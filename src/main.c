// PlutoVita - cliente no oficial de Pluto TV para PS Vita (homebrew)
//
// Version 2: reproductor HLS propio.
//   sceAvPlayer de la Vita solo abre MP4 y rechaza listas HLS (error 0x806A0002),
//   asi que la app hace todo el trabajo:
//     1. Baja la lista .m3u8 con libcurl y elige una calidad <= 576p.
//     2. Baja los segmentos .ts por adelantado (hilo "red").
//     3. Separa video y audio del MPEG-TS (hilo "demux").
//     4. H.264 con el decodificador de hardware (sceAvcdec) a texturas RGBA (hilo "video").
//     5. AAC con el decodificador de hardware (sceAudiodec) a sceAudioOut (hilo "audio").
//   El manejo de memoria del decodificador sigue lo aprendido en Vita IPTV
//   (github.com/emrhky/VitaIPTV, licencia MIT).
//
// Controles en reproduccion: O = volver, TRIANGULO = mostrar/ocultar datos de depuracion.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <malloc.h>
#include <psp2/kernel/processmgr.h>
#include <psp2/kernel/threadmgr.h>
#include <psp2/kernel/sysmem.h>
#include <psp2/sysmodule.h>
#include <psp2/net/net.h>
#include <psp2/net/netctl.h>
#include <psp2/ctrl.h>
#include <psp2/audioout.h>
#include <psp2/audiodec.h>
#include <psp2/videodec.h>
#include <psp2/gxm.h>
#include <curl/curl.h>
#include <openssl/evp.h>
#include <vita2d.h>

// ---- Endpoints (si Pluto los cambia, editalos aqui) ----
#define BOOT_URL \
  "https://boot.pluto.tv/v4/start?appName=web&appVersion=8.0.0&deviceVersion=122.0.0" \
  "&deviceModel=web&deviceMake=chrome&deviceType=web&clientID=%s&clientModelNumber=1.0.0" \
  "&serverSideAds=false&drmCapabilities=&blockingMode=&notificationVersion=1"
#define CHANNELS_URL "https://api.pluto.tv/v2/channels.json"
#define STITCH_URL \
  "https://service-stitcher.clusters.pluto.tv/v2/stitch/hls/channel/%s/master.m3u8" \
  "?advertisingId=&appName=web&appVersion=8.0.0&deviceDNT=0&deviceId=%s&deviceMake=chrome" \
  "&deviceModel=web&deviceType=web&deviceVersion=122.0.0&serverSideAds=false&sid=%s&jwt=%s" \
  "&masterJWTPassthrough=true"
// URL preferida (la que usa la web de Pluto): servidor y parametros que da el arranque
#define STITCH_URL2 "%s/v2/stitch/hls/channel/%s/master.m3u8?%s&jwt=%s&masterJWTPassthrough=true"

// ---- Ajustes del reproductor ----
#define MAX_HEIGHT  576          // calidad maxima a elegir (la pantalla es 544 de alto)
#define MAX_BW_NORES 2500000     // si la lista no dice la resolucion: tope de bits por segundo
#define SEG_AHEAD   3            // segmentos .ts bajados por adelantado
#define VQ_MAX      300          // unidades de video comprimidas en cola (~10 s)
#define PCM_SLOTS   192          // bloques de audio decodificado en cola (~4 s)
#define NSLOTS      5            // cuadros de video decodificados (texturas)
#define ES_CAP      (1024 * 1024)
#define NO_TS       0xFFFFFFFFu
#define ALIGN(x, a) (((x) + ((a) - 1)) & ~((a) - 1))
#define AVC         SCE_VIDEODEC_TYPE_HW_AVCDEC

// Memoria para el heap de newlib (curl + OpenSSL + segmentos)
int _newlib_heap_size_user = 64 * 1024 * 1024;

#define MAX_CH 800
typedef struct { char id[40]; char name[64]; } Channel;
static Channel chans[MAX_CH];
static int nchans = 0;
static char uuid[40], sid[40], jwt[2048];
static char stitcher[256], sparams[2048];   // del arranque de Pluto

static vita2d_pgf *pgf;
static SceCtrlData pad, oldpad;

static uint64_t now_us(void) { return (uint64_t)sceKernelGetProcessTimeWide(); }

static void make_uuid(char *o) {
  const char *h = "0123456789abcdef";
  srand((unsigned)sceKernelGetProcessTimeLow());
  for (int i = 0; i < 36; i++) o[i] = (i==8||i==13||i==18||i==23) ? '-' : h[rand() & 15];
  o[14] = '4'; o[36] = 0;
}

static void status(const char *msg) {
  vita2d_start_drawing(); vita2d_clear_screen();
  vita2d_pgf_draw_text(pgf, 40, 270, RGBA8(255,255,255,255), 1.2f, msg);
  vita2d_end_drawing(); vita2d_swap_buffers();
}

// ---------- HTTP (libcurl + OpenSSL) ----------
static int g_step = 0, g_err = 0, g_status = 0;
static volatile int g_abort = 0;          // corta descargas al salir del canal
struct mem { char *b; size_t n, cap; };

static size_t wcb(void *p, size_t sz, size_t nm, void *u) {
  struct mem *m = u; size_t t = sz * nm;
  if (m->n + t + 1 > m->cap) {
    size_t nc = m->cap ? m->cap : 256 * 1024;
    while (nc < m->n + t + 1) nc *= 2;
    if (nc > 16 * 1024 * 1024) return 0;
    char *nb = realloc(m->b, nc);
    if (!nb) return 0;
    m->b = nb; m->cap = nc;
  }
  memcpy(m->b + m->n, p, t); m->n += t; m->b[m->n] = 0;
  return t;
}

static int xferinfo(void *u, curl_off_t a, curl_off_t b, curl_off_t c, curl_off_t d) {
  return g_abort ? 1 : 0;
}

static char *http_get(const char *url, int *outlen) {
  g_step = 1; g_err = 0; g_status = 0;
  CURL *c = curl_easy_init();
  if (!c) { g_err = -1; return NULL; }
  struct mem m = {0, 0, 0};
  curl_easy_setopt(c, CURLOPT_URL, url);
  curl_easy_setopt(c, CURLOPT_WRITEFUNCTION, wcb);
  curl_easy_setopt(c, CURLOPT_WRITEDATA, &m);
  curl_easy_setopt(c, CURLOPT_SSL_VERIFYPEER, 0L);
  curl_easy_setopt(c, CURLOPT_SSL_VERIFYHOST, 0L);
  curl_easy_setopt(c, CURLOPT_FOLLOWLOCATION, 1L);
  curl_easy_setopt(c, CURLOPT_USERAGENT, "Mozilla/5.0 PlutoVita");
  curl_easy_setopt(c, CURLOPT_ACCEPT_ENCODING, "");
  curl_easy_setopt(c, CURLOPT_CONNECTTIMEOUT, 20L);
  curl_easy_setopt(c, CURLOPT_TIMEOUT, 60L);
  curl_easy_setopt(c, CURLOPT_NOSIGNAL, 1L);
  curl_easy_setopt(c, CURLOPT_NOPROGRESS, 0L);
  curl_easy_setopt(c, CURLOPT_XFERINFOFUNCTION, xferinfo);
  g_step = 4;
  CURLcode rc = curl_easy_perform(c);
  g_err = (int)rc;
  long st = 0; curl_easy_getinfo(c, CURLINFO_RESPONSE_CODE, &st); g_status = (int)st;
  curl_easy_cleanup(c);
  if (rc != CURLE_OK || st >= 400) { free(m.b); return NULL; }
  if (outlen) *outlen = (int)m.n;
  return m.b;
}

static int copy_str(const char *p, char *dst, int max) { // copia hasta la comilla
  int i = 0; while (*p && *p != '"' && i < max - 1) dst[i++] = *p++;
  dst[i] = 0; return i;
}

// Copia un texto JSON hasta la comilla final, resolviendo \u0026, \/ y \"
static void copy_json(const char *p, char *dst, int max) {
  int i = 0;
  while (*p && *p != '"' && i < max - 1) {
    if (*p == '\\' && p[1]) {
      if (p[1] == 'u' && p[2] && p[3] && p[4] && p[5]) {
        char hx[5] = { p[2], p[3], p[4], p[5], 0 };
        dst[i++] = (char)strtol(hx, NULL, 16); p += 6; continue;
      }
      dst[i++] = p[1]; p += 2; continue;
    }
    dst[i++] = *p++;
  }
  dst[i] = 0;
}

static int get_session(void) {
  char url[1024]; snprintf(url, sizeof url, BOOT_URL, uuid);
  char *r = http_get(url, NULL); if (!r) return -1;
  char *t = strstr(r, "\"sessionToken\":\"");
  int ok = -1;
  if (t) { copy_str(t + 16, jwt, sizeof jwt); ok = jwt[0] ? 0 : -1; }
  char *sp = strstr(r, "\"stitcherParams\":\"");
  if (sp) copy_json(sp + 18, sparams, sizeof sparams);
  char *sv = strstr(r, "\"stitcher\":\"");
  if (sv) copy_json(sv + 12, stitcher, sizeof stitcher);
  free(r); return ok;
}

// Parser basico: busca {"_id":"X","slug":"..","name":"Y"
static int get_channels(void) {
  char *r = http_get(CHANNELS_URL, NULL); if (!r) return -1;
  const char *p = r;
  while (nchans < MAX_CH && (p = strstr(p, "{\"_id\":\"")) != NULL) {
    p += 8;
    Channel *c = &chans[nchans];
    int n = copy_str(p, c->id, sizeof c->id);
    const char *q = p + n;
    if (strncmp(q, "\",\"slug\":\"", 10) != 0) continue;
    const char *nm = strstr(q, "\"name\":\"");
    if (!nm || nm - q > 300) continue;
    copy_str(nm + 8, c->name, sizeof c->name);
    if (c->id[0] && c->name[0]) nchans++;
  }
  free(r); return nchans > 0 ? 0 : -1;
}

// =====================================================================
//                          REPRODUCTOR HLS
// =====================================================================

static volatile int playing;
static SceUID mtx = -1;
static void lock(void)   { sceKernelLockMutex(mtx, 1, NULL); }
static void unlock(void) { sceKernelUnlockMutex(mtx, 1); }

// Interrumpible: duerme en pasos cortos mientras se reproduce
static void nap_ms(int ms) {
  while (ms > 0 && playing) { int s = ms > 50 ? 50 : ms; sceKernelDelayThread(s * 1000); ms -= s; }
}

// ---- Datos de depuracion (se muestran en pantalla) ----
static struct {
  char variant[80];
  int url2, jwt_added, alt_audio;
  char ts_types[48];
  int segs, seg_err, pl_err, pl_loads, http, curl;
  int enc_aes, enc_other, keys, key_err, dec_fail;
  char keymethod[24];
  int aus, frames, shown, dropped, dec_err, vopen, vw, vh, refs;
  unsigned last_dec_err, vinit_err;
  int arate, ach, aframes, aerr, alate;
  unsigned last_aerr;
  char msg[120];
} st;

// ---- URLs ----
static void url_resolve(const char *base, const char *ref, char *out, int cap) {
  if (!strncmp(ref, "http://", 7) || !strncmp(ref, "https://", 8)) { snprintf(out, cap, "%s", ref); return; }
  char b[4096]; snprintf(b, sizeof b, "%s", base);
  char *q = strchr(b, '?'); if (q) *q = 0;
  char *host = strstr(b, "://"); host = host ? host + 3 : b;
  if (ref[0] == '/') {
    char *sl = strchr(host, '/'); if (sl) *sl = 0;
    snprintf(out, cap, "%s%s", b, ref); return;
  }
  char *sl = strrchr(host, '/'); if (sl) sl[1] = 0; else strcat(b, "/");
  // quita "./" y resuelve "../"
  while (!strncmp(ref, "./", 2)) ref += 2;
  while (!strncmp(ref, "../", 3)) {
    ref += 3;
    int n = strlen(b);
    if (n > 0 && b[n - 1] == '/') b[n - 1] = 0;
    char *p = strrchr(host, '/');
    if (p) p[1] = 0; else strcat(b, "/");
  }
  snprintf(out, cap, "%s%s", b, ref);
}

// Lee la siguiente linea (sin \r\n). Devuelve puntero a la siguiente o NULL al final.
static const char *next_line(const char *p, char *line, int cap) {
  if (!p || !*p) return NULL;
  int i = 0;
  while (*p && *p != '\n' && *p != '\r') { if (i < cap - 1) line[i++] = *p; p++; }
  line[i] = 0;
  while (*p == '\r' || *p == '\n') p++;
  return p;
}

// Elige la variante de mayor calidad con alto <= MAX_HEIGHT (o la mas baja si ninguna cabe)
static int pick_variant(const char *m, const char *base, char *out, int cap) {
  static char line[4096];
  long best_bw = -1, low_bw = 0x7FFFFFFF; int best_h = 0, low_h = 0;
  static char best[4096], low[4096];
  best[0] = low[0] = 0;
  long bw = 0; int h = 0, pending = 0, skip = 0, any = 0;
  const char *p = m;
  while ((p = next_line(p, line, sizeof line)) != NULL) {
    if (!strncmp(line, "#EXT-X-MEDIA:", 13) && strstr(line, "TYPE=AUDIO") && strstr(line, "URI=")) st.alt_audio++;
    if (!strncmp(line, "#EXT-X-STREAM-INF:", 18)) {
      any = 1; pending = 1; skip = 0; bw = 0; h = 0;
      const char *b = strstr(line, "BANDWIDTH="); if (b) bw = atol(b + 10);
      const char *r = strstr(line, "RESOLUTION="); if (r) { const char *x = strchr(r, 'x'); if (x) h = atoi(x + 1); }
      const char *c = strstr(line, "CODECS=\""); if (c && !strstr(c, "avc1")) skip = 1;
    } else if (pending && line[0] && line[0] != '#') {
      pending = 0;
      if (skip) continue;
      int fits = h > 0 ? h <= MAX_HEIGHT : bw <= MAX_BW_NORES;
      if (fits && bw > best_bw) { best_bw = bw; best_h = h; snprintf(best, sizeof best, "%s", line); }
      if (bw < low_bw) { low_bw = bw; low_h = h; snprintf(low, sizeof low, "%s", line); }
    }
  }
  if (!any) { snprintf(out, cap, "%s", base); snprintf(st.variant, sizeof st.variant, "lista unica"); return 0; }
  const char *pick = best[0] ? best : low;
  if (!pick[0]) return -1;
  url_resolve(base, pick, out, cap);
  snprintf(st.variant, sizeof st.variant, "%dp  %ld kbps", best[0] ? best_h : low_h, (best[0] ? best_bw : low_bw) / 1000);
  return 0;
}

// ---- Cola de segmentos (red -> demux) ----
typedef struct Seg { struct Seg *next; uint8_t *data; int len; int disc; } Seg;
static Seg *sq_head, *sq_tail; static int sq_count;

static void seg_push(uint8_t *d, int len, int disc) {
  Seg *s = malloc(sizeof *s); if (!s) { free(d); return; }
  s->next = NULL; s->data = d; s->len = len; s->disc = disc;
  lock();
  if (sq_tail) sq_tail->next = s; else sq_head = s;
  sq_tail = s; sq_count++;
  unlock();
}
static Seg *seg_pop(void) {
  lock();
  Seg *s = sq_head;
  if (s) { sq_head = s->next; if (!sq_head) sq_tail = NULL; sq_count--; }
  unlock();
  return s;
}

// ---- Cifrado AES-128 de HLS (#EXT-X-KEY:METHOD=AES-128) ----
// Cada segmento va cifrado con AES-128-CBC. La llave (16 bytes) se baja de la URI de la etiqueta;
// el IV viene en la etiqueta o, si no, es el numero de secuencia del segmento.
static char key_uri[4096];
static uint8_t key_val[16];
static int key_ok;

static int hexval(int c) { return c >= '0' && c <= '9' ? c - '0' : c >= 'a' && c <= 'f' ? c - 'a' + 10 : c >= 'A' && c <= 'F' ? c - 'A' + 10 : -1; }

static int get_key(const char *uri) {
  if (key_ok && !strcmp(uri, key_uri)) return 0;
  int n = 0;
  char *k = http_get(uri, &n);
  st.http = g_status; st.curl = g_err;
  if (!k || n != 16) { free(k); st.key_err++; key_ok = 0; return -1; }
  memcpy(key_val, k, 16); free(k);
  snprintf(key_uri, sizeof key_uri, "%s", uri);
  key_ok = 1; st.keys++;
  return 0;
}

// Descifra en un bufer nuevo; devuelve el largo o -1
static int aes_decrypt(const uint8_t *in, int len, const uint8_t *iv, uint8_t **out) {
  *out = NULL;
  if (len <= 0 || len % 16) return -1;
  uint8_t *o = malloc(len + 16);
  if (!o) return -1;
  EVP_CIPHER_CTX *c = EVP_CIPHER_CTX_new();
  if (!c) { free(o); return -1; }
  int n1 = 0, n2 = 0, ok = EVP_DecryptInit_ex(c, EVP_aes_128_cbc(), NULL, key_val, iv) == 1 &&
                           EVP_DecryptUpdate(c, o, &n1, in, len) == 1;
  if (ok && EVP_DecryptFinal_ex(c, o + n1, &n2) != 1) n2 = 0;   // relleno raro: se queda con lo descifrado
  EVP_CIPHER_CTX_free(c);
  if (!ok) { free(o); return -1; }
  *out = o;
  return n1 + n2;
}

// ---- Hilo de red: recarga la lista y baja segmentos ----
static char g_media_url[4096];

#define MAX_SEGS 256
typedef struct { char *uri; char *key; int disc, method, has_iv; uint8_t iv[16]; } SegInfo;  // method: 0 nada, 1 AES-128, 2 otro

static int net_thread(SceSize a, void *u) {
  static char line[4096], cur_key[4096];
  static SegInfo segs[MAX_SEGS];
  int64_t next_seq = -1;
  int pending_disc = 0;
  while (playing) {
    int len = 0;
    char *pl = http_get(g_media_url, &len);
    st.http = g_status; st.curl = g_err;
    if (!pl) { st.pl_err++; nap_ms(2000); continue; }
    st.pl_loads++;
    int64_t mseq = 0; int tdur = 6, n = 0, ended = 0, disc = 0;
    int method = 0, has_iv = 0; uint8_t iv[16]; cur_key[0] = 0;
    const char *p = pl;
    while ((p = next_line(p, line, sizeof line)) != NULL) {
      if (!strncmp(line, "#EXT-X-MEDIA-SEQUENCE:", 22)) mseq = atoll(line + 22);
      else if (!strncmp(line, "#EXT-X-TARGETDURATION:", 22)) tdur = atoi(line + 22);
      else if (!strncmp(line, "#EXT-X-DISCONTINUITY", 20) && line[20] != '-') disc = 1;
      else if (!strncmp(line, "#EXT-X-ENDLIST", 14)) ended = 1;
      else if (!strncmp(line, "#EXT-X-KEY:", 11)) {
        method = strstr(line, "METHOD=NONE") ? 0 : strstr(line, "METHOD=AES-128") ? 1 : 2;
        if (method == 2) { const char *m = strstr(line, "METHOD="); snprintf(st.keymethod, sizeof st.keymethod, "%.20s", m ? m + 7 : "?"); }
        cur_key[0] = 0; has_iv = 0;
        const char *ur = strstr(line, "URI=\"");
        if (ur) {
          char raw[4096]; int i = 0; ur += 5;
          while (*ur && *ur != '"' && i < (int)sizeof raw - 1) raw[i++] = *ur++;
          raw[i] = 0;
          url_resolve(g_media_url, raw, cur_key, sizeof cur_key);
        }
        const char *ivp = strstr(line, "IV=0x"); if (!ivp) ivp = strstr(line, "IV=0X");
        if (ivp) {
          ivp += 5; memset(iv, 0, 16);
          int nd = 0; while (hexval(ivp[nd]) >= 0) nd++;
          for (int k = 0; k < nd && k < 32; k++) {        // alineado a la derecha
            int pos = 31 - (nd - 1 - k); if (pos < 0) continue;
            int v = hexval(ivp[k]);
            if (pos & 1) iv[pos / 2] |= v; else iv[pos / 2] |= v << 4;
          }
          has_iv = 1;
        }
      }
      else if (line[0] && line[0] != '#') {
        if (n < MAX_SEGS) {
          SegInfo *si = &segs[n];
          si->uri = malloc(4096);
          if (si->uri) {
            url_resolve(g_media_url, line, si->uri, 4096);
            si->disc = disc; si->method = method; si->has_iv = has_iv;
            memcpy(si->iv, iv, 16);
            si->key = method == 1 && cur_key[0] ? strdup(cur_key) : NULL;
            n++;
          }
        }
        disc = 0;
      }
    }
    free(pl);
    if (tdur < 1) tdur = 1;
    if (next_seq < 0 || next_seq > mseq + n + 10) next_seq = mseq + (n > 3 ? n - 3 : 0);
    if (next_seq < mseq) { next_seq = mseq; pending_disc = 1; }   // nos quedamos atras
    int got = 0;
    for (int i = 0; i < n && playing; i++) {
      int64_t seq = mseq + i;
      if (seq < next_seq) continue;
      while (playing && sq_count >= SEG_AHEAD) nap_ms(20);
      if (!playing) break;
      SegInfo *si = &segs[i];
      next_seq = seq + 1;
      if (si->method == 2) { st.enc_other++; pending_disc = 1; continue; }   // cifrado que no se puede abrir (DRM)
      int sl = 0;
      char *d = http_get(si->uri, &sl);
      st.http = g_status; st.curl = g_err;
      if (!d) { st.seg_err++; pending_disc = 1; continue; }
      if (si->method == 1) {
        st.enc_aes++;
        uint8_t ivb[16], *plain = NULL;
        if (si->has_iv) memcpy(ivb, si->iv, 16);
        else { memset(ivb, 0, 16); for (int k = 0; k < 8; k++) ivb[15 - k] = (uint8_t)((uint64_t)seq >> (8 * k)); }
        int pn = (si->key && get_key(si->key) == 0) ? aes_decrypt((uint8_t *)d, sl, ivb, &plain) : -1;
        free(d);
        if (pn < 0) { st.dec_fail++; pending_disc = 1; continue; }
        d = (char *)plain; sl = pn;
      }
      seg_push((uint8_t *)d, sl, si->disc || pending_disc);
      pending_disc = 0; got = 1; st.segs++;
    }
    for (int i = 0; i < n; i++) { free(segs[i].uri); free(segs[i].key); segs[i].uri = segs[i].key = NULL; }
    if (ended && !got) { snprintf(st.msg, sizeof st.msg, "Fin de la transmision"); break; }
    if (!got) nap_ms(tdur * 500);
  }
  return 0;
}

// ---- Cola de video comprimido (demux -> decodificador) ----
typedef struct VAu { struct VAu *next; uint8_t *data; int len; int64_t pts; int epoch; } VAu;
static VAu *vq_head, *vq_tail; static int vq_count;

static void vq_push(const uint8_t *d, int len, int64_t pts, int epoch) {
  while (playing && vq_count >= VQ_MAX) nap_ms(5);
  if (!playing) return;
  VAu *v = malloc(sizeof *v); if (!v) return;
  v->data = malloc(len); if (!v->data) { free(v); return; }
  memcpy(v->data, d, len); v->len = len; v->pts = pts; v->epoch = epoch; v->next = NULL;
  lock();
  if (vq_tail) vq_tail->next = v; else vq_head = v;
  vq_tail = v; vq_count++;
  unlock();
  st.aus++;
}
static VAu *vq_pop(void) {
  lock();
  VAu *v = vq_head;
  if (v) { vq_head = v->next; if (!vq_head) vq_tail = NULL; vq_count--; }
  unlock();
  return v;
}

// ---- Audio decodificado (demux -> hilo de audio) ----
typedef struct { int64_t pts; int epoch, samples, rate, ch; int16_t pcm[2048 * 2]; } Pcm;
static Pcm *pcm_ring; static int pcm_rd, pcm_wr, pcm_count;

// ---- Reloj comun (90 kHz, como los PTS) ----
static int clk_set, clk_epoch;
static int64_t clk_pts; static uint64_t clk_us;
static int64_t clock_now(void) { return clk_pts + (int64_t)(now_us() - clk_us) * 9 / 100; }
static void clock_set(int64_t pts, int epoch) { clk_pts = pts; clk_us = now_us(); clk_epoch = epoch; clk_set = 1; }

// ---- Memoria para el decodificador ----
enum { M_PHYCONT = 0, M_CDRAM, M_MAIN_NC, M_KINDS };
static void *mem_alloc(int kind, uint32_t size, SceUID *uid, int gpu) {
  int type; uint32_t al;
  if (kind == M_PHYCONT)    { type = SCE_KERNEL_MEMBLOCK_TYPE_USER_MAIN_PHYCONT_NC_RW; al = 1024 * 1024; }
  else if (kind == M_CDRAM) { type = SCE_KERNEL_MEMBLOCK_TYPE_USER_CDRAM_RW;           al = 256 * 1024; }
  else                      { type = SCE_KERNEL_MEMBLOCK_TYPE_USER_MAIN_NC_RW;         al = 4096; }
  size = ALIGN(size, al);
  *uid = sceKernelAllocMemBlock("pv_mem", type, size, NULL);
  if (*uid < 0) { *uid = -1; return NULL; }
  void *p = NULL; sceKernelGetMemBlockBase(*uid, &p);
  if (gpu && sceGxmMapMemory(p, size, SCE_GXM_MEMORY_ATTRIB_READ | SCE_GXM_MEMORY_ATTRIB_WRITE) < 0) {
    sceKernelFreeMemBlock(*uid); *uid = -1; return NULL;
  }
  return p;
}
static void mem_free(void *p, SceUID uid, int gpu) {
  if (uid < 0) return;
  if (gpu && p) sceGxmUnmapMemory(p);
  sceKernelFreeMemBlock(uid);
}

// ---- Cuadros decodificados (texturas) ----
enum { SL_FREE = 0, SL_READY, SL_SHOWN };
typedef struct {
  void *data; SceUID uid; vita2d_texture tex;
  int state, epoch; int64_t pts; uint32_t seq;
} Slot;
static Slot slots[NSLOTS];
static int shown = -1;
static uint32_t out_seq;

// ---- Decodificador H.264 de hardware ----
static SceAvcdecCtrl vctrl;
static int vlib = 0, vdec = 0, dw, dh, vis_w, vis_h;
static void *es_mem; static SceUID es_uid = -1, fb_uid = -1;
static int use_pts = 1, pts_tried = 0;
static volatile int vreset_req, vreset_ack;

static void vdec_close(void) {
  for (int i = 0; i < NSLOTS; i++) {
    mem_free(slots[i].data, slots[i].uid, 1);
    slots[i].data = NULL; slots[i].uid = -1; slots[i].state = SL_FREE;
  }
  shown = -1;
  if (vdec) sceAvcdecDeleteDecoder(&vctrl);
  vdec = 0;
  if (fb_uid >= 0) { mem_free(vctrl.frameBuf.pBuf, fb_uid, 0); fb_uid = -1; }
  if (vlib) sceVideodecTermLibrary(AVC);
  vlib = 0;
  if (es_uid >= 0) { mem_free(es_mem, es_uid, 0); es_uid = -1; es_mem = NULL; }
}

static int vdec_open(int cw, int ch, int vw, int vh) {
  static int mod_loaded = 0;
  if (!mod_loaded) { sceSysmoduleLoadModule(SCE_SYSMODULE_AVCDEC); mod_loaded = 1; } // en la Vita real puede fallar: no importa
  dw = ALIGN(cw, 16); dh = ALIGN(ch, 16);
  vis_w = vw > 0 && vw <= dw ? vw : dw;
  vis_h = vh > 0 && vh <= dh ? vh : dh;
  int mbs = (dw / 16) * (dh / 16);
  if (mbs > 3600) { snprintf(st.msg, sizeof st.msg, "Video %dx%d: mayor que 720p", dw, dh); return -1; }
  int refs = 18000 / mbs;          // el decodificador publico guarda 18000 macrobloques de referencia
  if (refs > 8) refs = 8;
  if (refs < 1) refs = 1;

  SceVideodecQueryInitInfoHwAvcdec init; memset(&init, 0, sizeof init);
  init.size = sizeof init; init.horizontal = dw; init.vertical = dh;
  init.numOfRefFrames = refs; init.numOfStreams = 1;
  int r = sceVideodecInitLibrary(AVC, &init);
  if (r < 0) { st.vinit_err = r; snprintf(st.msg, sizeof st.msg, "sceVideodecInitLibrary 0x%08X", (unsigned)r); return r; }
  vlib = 1;

  SceAvcdecQueryDecoderInfo q; SceAvcdecDecoderInfo di;
  memset(&q, 0, sizeof q); memset(&di, 0, sizeof di);
  q.horizontal = dw; q.vertical = dh; q.numOfRefFrames = refs;
  r = sceAvcdecQueryDecoderMemSize(AVC, &q, &di);
  if (r < 0) { st.vinit_err = r; snprintf(st.msg, sizeof st.msg, "QueryDecoderMemSize 0x%08X", (unsigned)r); return r; }

  r = -1;
  for (int k = 0; k < M_KINDS && r < 0; k++) {
    void *fb = mem_alloc(k, di.frameMemSize, &fb_uid, 0);
    if (!fb) continue;
    memset(&vctrl, 0, sizeof vctrl);
    vctrl.frameBuf.pBuf = fb;
    vctrl.frameBuf.size = ALIGN(di.frameMemSize, k == M_PHYCONT ? 1024 * 1024 : k == M_CDRAM ? 256 * 1024 : 4096);
    r = sceAvcdecCreateDecoder(AVC, &vctrl, &q);
    if (r < 0) { mem_free(fb, fb_uid, 0); fb_uid = -1; }
  }
  if (r < 0) { st.vinit_err = r; snprintf(st.msg, sizeof st.msg, "sceAvcdecCreateDecoder 0x%08X", (unsigned)r); return r; }
  vdec = 1;

  es_mem = mem_alloc(M_PHYCONT, ES_CAP, &es_uid, 0);
  if (!es_mem) es_mem = mem_alloc(M_CDRAM, ES_CAP, &es_uid, 0);
  if (!es_mem) es_mem = mem_alloc(M_MAIN_NC, ES_CAP, &es_uid, 0);
  if (!es_mem) { snprintf(st.msg, sizeof st.msg, "Sin memoria para el video"); return -1; }

  uint32_t psize = (uint32_t)dw * dh * 4;
  for (int i = 0; i < NSLOTS; i++) {
    Slot *s = &slots[i];
    s->data = mem_alloc(M_CDRAM, psize, &s->uid, 1);
    if (!s->data) s->data = mem_alloc(M_PHYCONT, psize, &s->uid, 1);
    if (!s->data) { snprintf(st.msg, sizeof st.msg, "Sin memoria para cuadros"); return -1; }
    memset(&s->tex, 0, sizeof s->tex);
    r = sceGxmTextureInitLinear(&s->tex.gxm_tex, s->data, SCE_GXM_TEXTURE_FORMAT_A8B8G8R8, dw, dh, 0);
    if (r < 0) { snprintf(st.msg, sizeof st.msg, "Textura 0x%08X", (unsigned)r); return r; }
    vita2d_texture_set_filters(&s->tex, SCE_GXM_TEXTURE_FILTER_LINEAR, SCE_GXM_TEXTURE_FILTER_LINEAR);
    s->state = SL_FREE;
  }
  st.vopen++; st.vw = vis_w; st.vh = vis_h; st.refs = refs;
  return 0;
}

// ---- Lector de bits para el SPS de H.264 ----
typedef struct { const uint8_t *d; int n, bit; } Bits;
static int rb1(Bits *b) { if (b->bit >= b->n * 8) return 0; int v = (b->d[b->bit >> 3] >> (7 - (b->bit & 7))) & 1; b->bit++; return v; }
static unsigned rbn(Bits *b, int k) { unsigned v = 0; while (k-- > 0) v = (v << 1) | rb1(b); return v; }
static unsigned ue(Bits *b) { int z = 0; while (!rb1(b) && z < 31) z++; return ((1u << z) - 1) + rbn(b, z); }
static int se(Bits *b) { unsigned v = ue(b); return (v & 1) ? (int)((v + 1) / 2) : -(int)(v / 2); }

// Devuelve tamano codificado (cw, ch) y visible (vw, vh)
static int parse_sps(const uint8_t *nal, int len, int *cw, int *ch, int *vw, int *vh) {
  uint8_t r[512]; int n = 0;
  for (int i = 1; i < len && n < (int)sizeof r; i++) {          // salta la cabecera NAL y quita 00 00 03
    if (i + 2 < len && nal[i] == 0 && nal[i + 1] == 0 && nal[i + 2] == 3) {
      r[n++] = 0; if (n < (int)sizeof r) r[n++] = 0; i += 2; continue;
    }
    r[n++] = nal[i];
  }
  Bits b = { r, n, 0 };
  int profile = rbn(&b, 8); rbn(&b, 16); ue(&b);
  int chroma = 1;
  if (profile == 100 || profile == 110 || profile == 122 || profile == 244 || profile == 44 ||
      profile == 83 || profile == 86 || profile == 118 || profile == 128 || profile == 138 ||
      profile == 139 || profile == 134 || profile == 135) {
    chroma = ue(&b); if (chroma == 3) rb1(&b);
    ue(&b); ue(&b); rb1(&b);
    if (rb1(&b)) {
      for (int i = 0; i < (chroma != 3 ? 8 : 12); i++) {
        if (!rb1(&b)) continue;
        int size = i < 6 ? 16 : 64, last = 8, next = 8;
        for (int j = 0; j < size; j++) {
          if (next) next = (last + se(&b) + 256) % 256;
          last = next ? next : last;
        }
      }
    }
  }
  ue(&b);
  int poc = ue(&b);
  if (poc == 0) ue(&b);
  else if (poc == 1) { rb1(&b); se(&b); se(&b); int k = ue(&b); for (int i = 0; i < k && i < 256; i++) se(&b); }
  ue(&b); rb1(&b);
  int wmbs = ue(&b) + 1, hmap = ue(&b) + 1, fmo = rb1(&b);
  if (!fmo) rb1(&b);
  rb1(&b);
  int cl = 0, cr = 0, ct = 0, cb = 0;
  if (rb1(&b)) { cl = ue(&b); cr = ue(&b); ct = ue(&b); cb = ue(&b); }
  *cw = wmbs * 16; *ch = (2 - fmo) * hmap * 16;
  int ux = chroma == 0 ? 1 : 2, uy = (chroma == 1 ? 2 : 1) * (2 - fmo);
  *vw = *cw - (cl + cr) * ux; *vh = *ch - (ct + cb) * uy;
  if (*cw < 16 || *ch < 16 || *cw > 4096 || *ch > 4096) return -1;
  return 0;
}

// Busca un SPS dentro de la unidad de video
static int find_sps(const uint8_t *d, int len, int *cw, int *ch, int *vw, int *vh) {
  for (int i = 0; i + 3 < len; i++) {
    if (d[i] == 0 && d[i + 1] == 0 && d[i + 2] == 1) {
      int s = i + 3;
      if ((d[s] & 0x1F) == 7) {
        int e = s;
        while (e + 2 < len && !(d[e] == 0 && d[e + 1] == 0 && (d[e + 2] == 1 || d[e + 2] == 0))) e++;
        if (e + 2 >= len) e = len;
        return parse_sps(d + s, e - s, cw, ch, vw, vh);
      }
      i = s - 1;
    }
  }
  return -1;
}

// ---- Hilo de video: decodifica a las texturas ----
static int free_slot(void) {
  int f = -1;
  lock();
  for (int i = 0; i < NSLOTS; i++) if (slots[i].data && slots[i].state == SL_FREE) { f = i; break; }
  unlock();
  return f;
}

static int vdec_thread(SceSize a, void *u) {
  int cur_cw = 0, cur_ch = 0, failed = 0;
  int64_t last_in = -1, frame_dur = 3003, last_out = -1;
  while (playing) {
    VAu *au = vq_pop();
    if (!au) { sceKernelDelayThread(2000); continue; }
    int cw, ch, vw, vh;
    int has_sps = find_sps(au->data, au->len, &cw, &ch, &vw, &vh) == 0;
    if (has_sps && vdec && (cw != cur_cw || ch != cur_ch)) {
      // cambio de resolucion (p. ej. un anuncio): reabrir con la pantalla soltando los cuadros
      vreset_ack = 0; vreset_req = 1;
      while (playing && !vreset_ack) sceKernelDelayThread(2000);
      vreset_req = 0;
      vdec_close();
    }
    if (!vdec) {
      if (!has_sps || failed >= 3) { free(au->data); free(au); continue; }  // espera un cuadro clave
      if (vdec_open(cw, ch, vw, vh) < 0) { vdec_close(); failed++; free(au->data); free(au); continue; }
      cur_cw = cw; cur_ch = ch; failed = 0;
    }
    if (au->pts >= 0 && last_in >= 0 && au->pts > last_in && au->pts - last_in < 9000 && au->pts - last_in < frame_dur)
      frame_dur = au->pts - last_in;
    if (au->pts >= 0) last_in = au->pts;

    int si;
    while (playing && (si = free_slot()) < 0) sceKernelDelayThread(2000);
    if (!playing) { free(au->data); free(au); break; }
    if (au->len > ES_CAP) { free(au->data); free(au); continue; }
    memcpy(es_mem, au->data, au->len);

    SceAvcdecPicture pic, *pp = &pic;
    SceAvcdecArrayPicture arr;
    SceAvcdecAu in;
    int r = -1;
    for (int attempt = 0; attempt < 2; attempt++) {
      memset(&in, 0, sizeof in);
      in.es.pBuf = es_mem; in.es.size = au->len;
      in.dts.upper = in.dts.lower = NO_TS;
      if (use_pts && au->pts >= 0) { in.pts.upper = (uint32_t)((uint64_t)au->pts >> 32); in.pts.lower = (uint32_t)au->pts; }
      else in.pts.upper = in.pts.lower = NO_TS;
      memset(&pic, 0, sizeof pic);
      pic.size = sizeof pic;
      pic.frame.pixelType = SCE_AVCDEC_PIXELFORMAT_RGBA8888;
      pic.frame.framePitch = dw; pic.frame.frameWidth = dw; pic.frame.frameHeight = dh;
      pic.frame.opt.rgba.alpha = 0xFF;
      pic.frame.pPicture[0] = slots[si].data;
      memset(&arr, 0, sizeof arr);
      arr.numOfElm = 1; arr.pPicture = &pp;
      r = sceAvcdecDecode(&vctrl, &in, &arr);
      if (r >= 0 || !use_pts || pts_tried) break;
      pts_tried = 1; use_pts = 0;      // algunos firmwares quieren los PTS en 0xFFFFFFFF: reintenta sin ellos
    }
    if (r >= 0) pts_tried = 1;
    int ep = au->epoch;
    free(au->data); free(au);
    if (r < 0) { st.dec_err++; st.last_dec_err = (unsigned)r; continue; }
    if (arr.numOfOutput == 0) continue;
    int64_t opts = -1;
    if (!(pic.info.pts.upper == NO_TS && pic.info.pts.lower == NO_TS))
      opts = (int64_t)(((uint64_t)pic.info.pts.upper << 32) | pic.info.pts.lower);
    if (opts < 0 && last_out >= 0) opts = last_out + frame_dur;
    if (opts >= 0) last_out = opts;
    lock();
    slots[si].pts = opts; slots[si].epoch = ep; slots[si].seq = out_seq++;
    slots[si].state = SL_READY;
    unlock();
    st.frames++;
  }
  return 0;
}

// ---- Decodificador AAC de hardware ----
static SceAudiodecCtrl actrl;
static SceAudiodecInfo ainfo;
static int alib = 0, adec = 0, a_rate = 0, a_ch = 0;
static uint8_t *aes, *apcm;
static const int ADTS_RATES[13] = { 96000, 88200, 64000, 48000, 44100, 32000, 24000, 22050, 16000, 12000, 11025, 8000, 7350 };

static void adec_close(void) {
  if (adec) sceAudiodecDeleteDecoder(&actrl);
  adec = 0; a_rate = a_ch = 0;
  free(aes); free(apcm); aes = apcm = NULL;
}

static int adec_open(int rate, int ch) {
  int r;
  if (!alib) {
    SceAudiodecInitParam ip; memset(&ip, 0, sizeof ip);
    ip.aac.size = sizeof ip.aac; ip.aac.totalStreams = 1;
    r = sceAudiodecInitLibrary(SCE_AUDIODEC_TYPE_AAC, &ip);
    if (r < 0 && (unsigned)r != 0x807F0003u) return r;    // "ya iniciada" esta bien
    alib = 1;
  }
  memset(&ainfo, 0, sizeof ainfo);
  ainfo.aac.size = sizeof ainfo.aac;
  ainfo.aac.isAdts = 1; ainfo.aac.ch = ch; ainfo.aac.samplingRate = rate; ainfo.aac.isSbr = 0;
  memset(&actrl, 0, sizeof actrl);
  actrl.size = sizeof actrl;
  actrl.wordLength = SCE_AUDIODEC_WORD_LENGTH_16BITS;
  actrl.pInfo = &ainfo;
  r = sceAudiodecCreateDecoder(&actrl, SCE_AUDIODEC_TYPE_AAC);
  if (r < 0) return r;
  adec = 1;
  aes  = memalign(SCE_AUDIODEC_ALIGNMENT_SIZE, SCE_AUDIODEC_ROUND_UP(SCE_AUDIODEC_AAC_MAX_ES_SIZE * 2));
  apcm = memalign(SCE_AUDIODEC_ALIGNMENT_SIZE, SCE_AUDIODEC_ROUND_UP(SCE_AUDIODEC_AAC_MAX_SAMPLES * 2 * 2));
  if (!aes || !apcm) return -1;
  a_rate = rate; a_ch = ch;
  st.arate = rate; st.ach = ch;
  return 0;
}

static int rate_ok(int r) {
  return r == 8000 || r == 11025 || r == 12000 || r == 16000 || r == 22050 ||
         r == 24000 || r == 32000 || r == 44100 || r == 48000;
}

// Un cuadro ADTS completo -> PCM a la cola
static void audio_frame(const uint8_t *d, int len, int64_t pts, int epoch) {
  int sfi = (d[2] >> 2) & 15, ch = ((d[2] & 1) << 2) | (d[3] >> 6);
  if (sfi >= 13) return;
  int rate = ADTS_RATES[sfi];
  if (ch < 1 || ch > 2 || !rate_ok(rate)) { st.aerr++; return; }
  if (!adec || rate != a_rate || ch != a_ch) {
    adec_close();
    int r = adec_open(rate, ch);
    if (r < 0) { st.aerr++; st.last_aerr = (unsigned)r; adec_close(); return; }
  }
  if (len > SCE_AUDIODEC_AAC_MAX_ES_SIZE * 2) { st.aerr++; return; }
  memcpy(aes, d, len);
  if (((aes[2] >> 6) & 3) == 0) aes[2] = (aes[2] & 0x3F) | 0x40;   // AAC Main -> LC (la Vita solo hace LC)
  actrl.pEs = aes; actrl.inputEsSize = len; actrl.pPcm = apcm;
  int r = sceAudiodecDecode(&actrl);
  if (r < 0) { st.aerr++; st.last_aerr = (unsigned)r; return; }
  int samples = (int)(actrl.outputPcmSize / (2u * ch));
  if (samples <= 0 || samples > 2048 || samples % 64) { st.aerr++; return; }
  while (playing && pcm_count >= PCM_SLOTS) nap_ms(5);
  if (!playing) return;
  Pcm *c = &pcm_ring[pcm_wr];
  c->pts = pts; c->epoch = epoch; c->samples = samples; c->rate = rate; c->ch = ch;
  memcpy(c->pcm, apcm, (size_t)samples * 2 * ch);
  lock(); pcm_wr = (pcm_wr + 1) % PCM_SLOTS; pcm_count++; unlock();
  st.aframes++;
}

// ---- Demultiplexor MPEG-TS ----
typedef struct { uint8_t *buf; int len, cap, want, started; int64_t pts; } Pes;
static int pmt_pid, vpid, apid, epoch;
static Pes vpes, apes;

static int64_t read_pts(const uint8_t *p) {
  return ((int64_t)((p[0] >> 1) & 7) << 30) | ((int64_t)p[1] << 22) | ((int64_t)(p[2] >> 1) << 15) |
         ((int64_t)p[3] << 7) | (p[4] >> 1);
}

static void pes_append(Pes *p, const uint8_t *d, int n) {
  if (p->len + n > p->cap) {
    int nc = p->cap ? p->cap : 256 * 1024;
    while (nc < p->len + n) nc *= 2;
    if (nc > 4 * 1024 * 1024) { p->started = 0; return; }
    uint8_t *nb = realloc(p->buf, nc);
    if (!nb) { p->started = 0; return; }
    p->buf = nb; p->cap = nc;
  }
  memcpy(p->buf + p->len, d, n); p->len += n;
}

static void pes_flush(Pes *p, int is_video) {
  if (p->started && p->len > 0) {
    if (is_video) vq_push(p->buf, p->len, p->pts, epoch);
    else {
      int i = 0, k = 0;
      while (i + 7 <= p->len && playing) {
        const uint8_t *d = p->buf + i;
        if (d[0] != 0xFF || (d[1] & 0xF6) != 0xF0) { i++; continue; }
        int fl = ((d[3] & 3) << 11) | (d[4] << 3) | (d[5] >> 5);
        if (fl < 7 || i + fl > p->len) break;
        int sfi = (d[2] >> 2) & 15;
        int rate = sfi < 13 ? ADTS_RATES[sfi] : 48000;
        int64_t pts = p->pts >= 0 ? p->pts + (int64_t)k * 1024 * 90000 / rate : -1;
        audio_frame(d, fl, pts, epoch);
        i += fl; k++;
      }
    }
  }
  p->len = 0; p->started = 0; p->want = 0; p->pts = -1;
}

static void pes_start(Pes *p, const uint8_t *d, int n) {
  if (n < 9 || d[0] != 0 || d[1] != 0 || d[2] != 1) return;
  int plen = (d[4] << 8) | d[5], flags = d[7], hl = d[8];
  if (9 + hl > n) return;
  p->pts = (flags & 0x80) && hl >= 5 ? read_pts(d + 9) : -1;
  p->want = plen ? plen - 3 - hl : 0;
  p->started = 1; p->len = 0;
  pes_append(p, d + 9 + hl, n - 9 - hl);
}

static void ts_reset(void) { pmt_pid = vpid = apid = -1; }

static void ts_packet(const uint8_t *p) {
  int pid = ((p[1] & 0x1F) << 8) | p[2], pusi = p[1] & 0x40, afc = (p[3] >> 4) & 3;
  int o = 4;
  if (afc & 2) o += 1 + p[4];
  if (!(afc & 1) || o >= 188) return;
  const uint8_t *d = p + o; int n = 188 - o;
  if (pid == 0 && pusi) {                                   // PAT
    int ptr = d[0]; d += 1 + ptr; n -= 1 + ptr;
    if (n < 12 || d[0] != 0) return;
    int sl = ((d[1] & 0x0F) << 8) | d[2];
    for (int i = 8; i + 4 <= 3 + sl - 4 && i + 4 <= n; i += 4) {
      int prog = (d[i] << 8) | d[i + 1];
      if (prog != 0) { pmt_pid = ((d[i + 2] & 0x1F) << 8) | d[i + 3]; break; }
    }
  } else if (pid == pmt_pid && pusi) {                      // PMT
    int ptr = d[0]; d += 1 + ptr; n -= 1 + ptr;
    if (n < 12 || d[0] != 2) return;
    int sl = ((d[1] & 0x0F) << 8) | d[2];
    int pil = ((d[10] & 0x0F) << 8) | d[11];
    int end = 3 + sl - 4; if (end > n) end = n;
    int nv = -1, na = -1, tl = 0;
    char types[48];
    for (int i = 12 + pil; i + 5 <= end; ) {
      int type = d[i], epid = ((d[i + 1] & 0x1F) << 8) | d[i + 2], il = ((d[i + 3] & 0x0F) << 8) | d[i + 4];
      if (type == 0x1B && nv < 0) nv = epid;
      if (type == 0x0F && na < 0) na = epid;
      if (tl < (int)sizeof types - 4) tl += snprintf(types + tl, sizeof types - tl, "%02X ", type);
      i += 5 + il;
    }
    vpid = nv; apid = na;
    types[tl] = 0;
    if (strcmp(types, st.ts_types)) snprintf(st.ts_types, sizeof st.ts_types, "%s", types);
  } else if (pid == vpid || pid == apid) {
    Pes *pe = pid == vpid ? &vpes : &apes;
    if (pusi) { pes_flush(pe, pid == vpid); pes_start(pe, d, n); }
    else if (pe->started) pes_append(pe, d, n);
    if (pe->started && pe->want > 0 && pe->len >= pe->want) pes_flush(pe, pid == vpid);
  }
}

static int demux_thread(SceSize a, void *u) {
  ts_reset(); epoch = 0;
  vpes.pts = apes.pts = -1;
  while (playing) {
    Seg *s = seg_pop();
    if (!s) { sceKernelDelayThread(5000); continue; }
    if (s->disc) { pes_flush(&vpes, 1); pes_flush(&apes, 0); ts_reset(); epoch++; }
    const uint8_t *d = s->data;
    int i = 0;
    while (i + 188 <= s->len && playing) {
      if (d[i] != 0x47) { i++; continue; }
      ts_packet(d + i); i += 188;
    }
    free(s->data); free(s);
  }
  return 0;
}

// ---- Hilo de audio: saca el PCM a tiempo con el reloj ----
static int audio_thread(SceSize a, void *u) {
  int port = -1, p_rate = 0, p_ch = 0, p_samples = 0, ob = 0;
  int16_t *obuf[2];
  obuf[0] = memalign(64, 2048 * 2 * 2); obuf[1] = memalign(64, 2048 * 2 * 2);
  uint64_t wait0 = 0;
  while (playing) {
    lock();
    if (pcm_count == 0) { unlock(); sceKernelDelayThread(5000); continue; }
    Pcm *c = &pcm_ring[pcm_rd];
    if (!clk_set || c->epoch > clk_epoch) {
      // espera a que el video ponga el reloj; si en 2 s no hay video, el audio lo pone
      if (!wait0) wait0 = now_us();
      if (now_us() - wait0 > 2000000) clock_set(c->pts >= 0 ? c->pts : 0, c->epoch);
      else { unlock(); sceKernelDelayThread(5000); continue; }
    }
    wait0 = 0;
    int drop = c->epoch < clk_epoch;
    if (!drop && c->pts >= 0) {
      int64_t diff = c->pts - clock_now();
      if (diff < -150 * 90) drop = 1;                                   // llego tarde
      else if (diff > 150 * 90) {                                       // aun es temprano
        unlock();
        int us = (int)(diff * 100 / 9); if (us > 20000) us = 20000;
        sceKernelDelayThread(us);
        continue;
      }
    }
    if (drop) { pcm_rd = (pcm_rd + 1) % PCM_SLOTS; pcm_count--; unlock(); st.alate++; continue; }
    int samples = c->samples, rate = c->rate, ch = c->ch;
    memcpy(obuf[ob], c->pcm, (size_t)samples * 2 * ch);
    pcm_rd = (pcm_rd + 1) % PCM_SLOTS; pcm_count--;
    unlock();
    if (port < 0 || samples != p_samples || rate != p_rate || ch != p_ch) {
      if (port >= 0) sceAudioOutReleasePort(port);
      // MAIN solo acepta 48000 Hz; BGM acepta las demas frecuencias
      port = sceAudioOutOpenPort(SCE_AUDIO_OUT_PORT_TYPE_BGM, samples, rate,
                                 ch == 1 ? SCE_AUDIO_OUT_MODE_MONO : SCE_AUDIO_OUT_MODE_STEREO);
      if (port < 0) { st.last_aerr = (unsigned)port; st.aerr++; port = -1; continue; }
      int vol[2] = { SCE_AUDIO_VOLUME_0DB, SCE_AUDIO_VOLUME_0DB };
      sceAudioOutSetVolume(port, SCE_AUDIO_VOLUME_FLAG_L_CH | SCE_AUDIO_VOLUME_FLAG_R_CH, vol);
      p_samples = samples; p_rate = rate; p_ch = ch;
    }
    sceAudioOutOutput(port, obuf[ob]);
    ob ^= 1;
  }
  if (port >= 0) { sceAudioOutOutput(port, NULL); sceAudioOutReleasePort(port); }
  free(obuf[0]); free(obuf[1]);
  return 0;
}

// ---- Pantalla: elige el cuadro que toca segun el reloj ----
static int oldest_ready(int after_seq_of) {
  int best = -1;
  for (int i = 0; i < NSLOTS; i++) {
    if (!slots[i].data || slots[i].state != SL_READY || i == after_seq_of) continue;
    if (after_seq_of >= 0 && (int32_t)(slots[i].seq - slots[after_seq_of].seq) <= 0) continue;
    if (best < 0 || (int32_t)(slots[i].seq - slots[best].seq) < 0) best = i;
  }
  return best;
}

static void take_frame(int f) {
  if (shown >= 0 && shown != f) slots[shown].state = SL_FREE;
  shown = f; slots[f].state = SL_SHOWN; st.shown++;
}

static void pick_frame(void) {
  lock();
  if (vreset_req && !vreset_ack) {          // el decodificador va a reabrirse: suelta todo
    for (int i = 0; i < NSLOTS; i++) slots[i].state = SL_FREE;
    shown = -1; vreset_ack = 1;
  }
  for (;;) {
    int f = oldest_ready(-1);
    if (f < 0) break;
    Slot *s = &slots[f];
    if (!clk_set || s->epoch != clk_epoch || s->pts < 0) {
      if (s->pts >= 0) clock_set(s->pts, s->epoch);
      take_frame(f); break;
    }
    int64_t d = s->pts - clock_now();
    if (d > 5 * 90000) { clock_set(s->pts, s->epoch); take_frame(f); break; }   // salto raro: re-ancla
    if (d > 0) break;                                                        // aun no toca
    if (d < -90000) { clock_set(s->pts, s->epoch); take_frame(f); break; }   // >1 s tarde: re-ancla
    int g = oldest_ready(f);
    if (g >= 0 && slots[g].epoch == clk_epoch && slots[g].pts >= 0 && slots[g].pts <= clock_now()) {
      s->state = SL_FREE; st.dropped++; continue;                           // ya toca el siguiente
    }
    take_frame(f); break;
  }
  unlock();
}

static void draw_debug(int y0) {
  char l[200]; uint32_t col = RGBA8(255,255,0,255);
  snprintf(l, sizeof l, "Calidad: %s   URL %s%s   audio aparte: %d", st.variant, st.url2 ? "nueva" : "vieja",
           st.jwt_added ? "  +jwt" : "", st.alt_audio);
  vita2d_pgf_draw_text(pgf, 20, y0, col, 0.9f, l);
  snprintf(l, sizeof l, "Red: segmentos %d  errores %d  lista %d/%d  http %d  curl %d  cola %d",
           st.segs, st.seg_err, st.pl_loads, st.pl_err, st.http, st.curl, sq_count);
  vita2d_pgf_draw_text(pgf, 20, y0 + 26, col, 0.9f, l);
  if (st.enc_aes || st.enc_other) {
    snprintf(l, sizeof l, "Cifrado: AES-128 %d  llaves %d  err llave %d  err descifrar %d  otro %d %s",
             st.enc_aes, st.keys, st.key_err, st.dec_fail, st.enc_other, st.keymethod);
    vita2d_pgf_draw_text(pgf, 20, y0 + 156, RGBA8(120,220,255,255), 0.9f, l);
  }
  snprintf(l, sizeof l, "Video: %dx%d refs %d  AUs %d  cuadros %d  mostrados %d  saltados %d",
           st.vw, st.vh, st.refs, st.aus, st.frames, st.shown, st.dropped);
  vita2d_pgf_draw_text(pgf, 20, y0 + 52, col, 0.9f, l);
  snprintf(l, sizeof l, "Video errores: %d (0x%08X)  init 0x%08X  pts %s  cola %d",
           st.dec_err, st.last_dec_err, st.vinit_err, use_pts ? "si" : "no", vq_count);
  vita2d_pgf_draw_text(pgf, 20, y0 + 78, col, 0.9f, l);
  snprintf(l, sizeof l, "Audio: %d Hz %d ch  cuadros %d  tarde %d  err %d (0x%08X)  cola %d  TS: %s",
           st.arate, st.ach, st.aframes, st.alate, st.aerr, st.last_aerr, pcm_count, st.ts_types);
  vita2d_pgf_draw_text(pgf, 20, y0 + 104, col, 0.9f, l);
  if (st.msg[0]) vita2d_pgf_draw_text(pgf, 20, y0 + 130, RGBA8(255,120,120,255), 0.9f, st.msg);
}

static void play_channel(const Channel *c) {
  static char url[4096];
  memset(&st, 0, sizeof st);
  key_ok = 0; key_uri[0] = 0;
  int use2 = stitcher[0] && sparams[0];
  if (use2) snprintf(url, sizeof url, STITCH_URL2, stitcher, c->id, sparams, jwt);
  else snprintf(url, sizeof url, STITCH_URL, c->id, uuid, sid, jwt);
  status("Cargando canal...");
  char *master = http_get(url, NULL);
  if (!master) {
    char m[200]; snprintf(m, sizeof m, "No se pudo abrir el canal: curl %d  http %d", g_err, g_status);
    status(m); sceKernelDelayThread(4000000); return;
  }
  int pv = pick_variant(master, url, g_media_url, sizeof g_media_url);
  free(master);
  if (pv == 0 && !strstr(g_media_url, "jwt=")) {   // la lista de calidad tambien pide el token
    int n = strlen(g_media_url);
    snprintf(g_media_url + n, sizeof g_media_url - n, "%cjwt=%s", strchr(g_media_url, '?') ? '&' : '?', jwt);
    st.jwt_added = 1;
  }
  st.url2 = use2;
  if (pv < 0) { status("La lista del canal no tiene video H.264"); sceKernelDelayThread(4000000); return; }

  // estado inicial
  mtx = sceKernelCreateMutex("pv_mtx", 0, 0, NULL);
  sq_head = sq_tail = NULL; sq_count = 0;
  vq_head = vq_tail = NULL; vq_count = 0;
  pcm_ring = malloc(sizeof(Pcm) * PCM_SLOTS);
  pcm_rd = pcm_wr = pcm_count = 0;
  clk_set = 0; clk_epoch = 0;
  memset(slots, 0, sizeof slots);
  for (int i = 0; i < NSLOTS; i++) slots[i].uid = -1;
  shown = -1; out_seq = 0; vreset_req = vreset_ack = 0;
  memset(&vpes, 0, sizeof vpes); memset(&apes, 0, sizeof apes);
  if (!pcm_ring) { status("Sin memoria"); sceKernelDelayThread(3000000); sceKernelDeleteMutex(mtx); return; }

  playing = 1; g_abort = 0;
  SceUID th_net = sceKernelCreateThread("pv_net",   net_thread,   0x10000100, 512 * 1024, 0, 0, NULL);
  SceUID th_dmx = sceKernelCreateThread("pv_demux", demux_thread, 0x10000100, 128 * 1024, 0, 0, NULL);
  SceUID th_vid = sceKernelCreateThread("pv_video", vdec_thread,  0x10000100, 64 * 1024,  0, 0, NULL);
  SceUID th_aud = sceKernelCreateThread("pv_audio", audio_thread, 0x10000100, 64 * 1024,  0, 0, NULL);
  sceKernelStartThread(th_net, 0, NULL);
  sceKernelStartThread(th_dmx, 0, NULL);
  sceKernelStartThread(th_vid, 0, NULL);
  sceKernelStartThread(th_aud, 0, NULL);

  int show_dbg = 0;
  while (playing) {
    sceCtrlPeekBufferPositive(0, &pad, 1);
    unsigned pr = pad.buttons & ~oldpad.buttons; oldpad = pad;
    if (pr & SCE_CTRL_CIRCLE) break;
    if (pr & SCE_CTRL_TRIANGLE) show_dbg = !show_dbg;

    pick_frame();
    vita2d_start_drawing(); vita2d_clear_screen();
    int sh = shown;
    if (sh >= 0) {
      float sx = 960.0f / vis_w, sy = 544.0f / vis_h, sc = sx < sy ? sx : sy;
      float x = (960.0f - vis_w * sc) / 2, y = (544.0f - vis_h * sc) / 2;
      vita2d_draw_texture_part_scale(&slots[sh].tex, x, y, 0, 0, vis_w, vis_h, sc, sc);
    } else {
      vita2d_pgf_draw_text(pgf, 20, 60, RGBA8(255,255,255,255), 1.2f, "Buffering...  (O = volver)");
    }
    if (show_dbg || sh < 0) {
      if (sh >= 0) vita2d_draw_rectangle(0, 330, 960, 214, RGBA8(0,0,0,170));
      draw_debug(sh >= 0 ? 360 : 110);
    }
    vita2d_end_drawing();
    vita2d_wait_rendering_done();       // la GPU termino: ya se pueden reciclar los cuadros
    vita2d_swap_buffers();
  }

  status("Cerrando...");
  playing = 0; g_abort = 1;
  sceKernelWaitThreadEnd(th_net, NULL, NULL);
  sceKernelWaitThreadEnd(th_dmx, NULL, NULL);
  sceKernelWaitThreadEnd(th_vid, NULL, NULL);
  sceKernelWaitThreadEnd(th_aud, NULL, NULL);
  sceKernelDeleteThread(th_net); sceKernelDeleteThread(th_dmx);
  sceKernelDeleteThread(th_vid); sceKernelDeleteThread(th_aud);
  g_abort = 0;

  vita2d_wait_rendering_done();
  vdec_close();
  adec_close();
  Seg *s; while ((s = seg_pop()) != NULL) { free(s->data); free(s); }
  VAu *v; while ((v = vq_pop()) != NULL) { free(v->data); free(v); }
  free(vpes.buf); free(apes.buf); memset(&vpes, 0, sizeof vpes); memset(&apes, 0, sizeof apes);
  free(pcm_ring); pcm_ring = NULL;
  sceKernelDeleteMutex(mtx); mtx = -1;
  use_pts = 1; pts_tried = 0;
}

// ---------- Main ----------
int main(void) {
  sceSysmoduleLoadModule(SCE_SYSMODULE_NET);
  static char netmem[1024 * 1024];
  SceNetInitParam np = { netmem, sizeof netmem, 0 };
  sceNetInit(&np); sceNetCtlInit();
  curl_global_init(CURL_GLOBAL_DEFAULT);

  vita2d_init(); pgf = vita2d_load_default_pgf();
  sceCtrlSetSamplingMode(SCE_CTRL_MODE_ANALOG);
  make_uuid(uuid); make_uuid(sid);

  status("Conectando con Pluto TV...");
  if (get_session() < 0) {
    char m[200]; snprintf(m, sizeof m, "Error sesion: paso %d  codigo 0x%08X  http %d", g_step, (unsigned)g_err, g_status);
    status(m); sceKernelDelayThread(15000000); goto out; }
  status("Descargando canales...");
  if (get_channels() < 0) {
    char m[200]; snprintf(m, sizeof m, "Error canales: paso %d  codigo 0x%08X  http %d", g_step, (unsigned)g_err, g_status);
    status(m); sceKernelDelayThread(15000000); goto out; }

  int sel = 0, top = 0; const int rows = 15;
  for (;;) {
    sceCtrlPeekBufferPositive(0, &pad, 1);
    unsigned p = pad.buttons & ~oldpad.buttons; oldpad = pad;
    if ((p & SCE_CTRL_DOWN) && sel < nchans - 1) sel++;
    if ((p & SCE_CTRL_UP) && sel > 0) sel--;
    if (p & SCE_CTRL_RTRIGGER) sel = sel + rows < nchans ? sel + rows : nchans - 1;
    if (p & SCE_CTRL_LTRIGGER) sel = sel - rows > 0 ? sel - rows : 0;
    if (sel < top) top = sel;
    if (sel >= top + rows) top = sel - rows + 1;
    if (p & SCE_CTRL_CROSS) { play_channel(&chans[sel]); continue; }
    if (p & SCE_CTRL_START) break;

    vita2d_start_drawing(); vita2d_clear_screen();
    vita2d_draw_rectangle(0, 0, 960, 50, RGBA8(30,30,120,255));
    vita2d_pgf_draw_text(pgf, 20, 34, RGBA8(255,255,255,255), 1.3f, "Pluto TV para Vita");
    for (int i = 0; i < rows && top + i < nchans; i++) {
      int y = 70 + i * 31, idx = top + i;
      if (idx == sel) vita2d_draw_rectangle(10, y - 4, 940, 30, RGBA8(70,70,200,255));
      vita2d_pgf_draw_text(pgf, 24, y + 18, RGBA8(255,255,255,255), 1.0f, chans[idx].name);
    }
    vita2d_pgf_draw_text(pgf, 20, 535, RGBA8(180,180,180,255), 0.9f,
                         "X: ver   O: volver   L/R: pagina   START: salir");
    vita2d_end_drawing(); vita2d_swap_buffers();
  }
out:
  vita2d_fini();
  curl_global_cleanup(); sceNetCtlTerm(); sceNetTerm();
  sceKernelExitProcess(0);
  return 0;
}
