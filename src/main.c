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
#include <psp2/ime_dialog.h>
#include <psp2/apputil.h>
#include <curl/curl.h>
#include <openssl/evp.h>
#include <vita2d.h>

// ---- Endpoints (si Pluto los cambia, editalos aqui) ----
#define BOOT_URL \
  "https://boot.pluto.tv/v4/start?appName=web&appVersion=8.0.0&deviceVersion=122.0.0" \
  "&deviceModel=web&deviceMake=chrome&deviceType=web&clientID=%s&clientModelNumber=1.0.0" \
  "&serverSideAds=false&drmCapabilities=&blockingMode=&notificationVersion=1"
#define CHANNELS_URL "https://api.pluto.tv/v2/channels.json"
// %s = "channel" (en vivo) o "episode" (peliculas y episodios a la carta)
#define STITCH_URL \
  "https://service-stitcher.clusters.pluto.tv/v2/stitch/hls/%s/%s/master.m3u8" \
  "?advertisingId=&appName=web&appVersion=8.0.0&deviceDNT=0&deviceId=%s&deviceMake=chrome" \
  "&deviceModel=web&deviceType=web&deviceVersion=122.0.0&serverSideAds=false&sid=%s&jwt=%s" \
  "&masterJWTPassthrough=true"
// URL preferida (la que usa la web de Pluto): servidor y parametros que da el arranque
#define STITCH_URL2 "%s/v2/stitch/hls/%s/%s/master.m3u8?%s&jwt=%s&masterJWTPassthrough=true"
// Catalogo a la carta (peliculas y series). v4 pide el token en "Authorization: Bearer"; v3 es el respaldo.
#define VOD_CATS_V4    "https://service-vod.clusters.pluto.tv/v4/vod/categories?includeItems=false&offset=1000&page=1"
#define VOD_ITEMS_V4   "https://service-vod.clusters.pluto.tv/v4/vod/categories/%s/items?offset=1000&page=1"
#define VOD_SEASONS_V4 "https://service-vod.clusters.pluto.tv/v4/vod/series/%s/seasons?offset=1000&page=1"
#define VOD_CATS_V3    "https://api.pluto.tv/v3/vod/categories?includeItems=true&deviceType=web"
#define VOD_SEASONS_V3 "https://api.pluto.tv/v3/vod/series/%s/seasons?deviceType=web"

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
typedef struct { char id[40]; char name[64]; char logo[224]; } Channel;
static Channel chans[MAX_CH];
static int nchans = 0;
static char uuid[40], sid[40];
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
static volatile int seek_gen = 0;         // sube con cada salto (adelantar/retroceder): lo viejo se descarta
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
  return (g_abort || (int)(intptr_t)u != seek_gen) ? 1 : 0;   // tambien corta si el usuario salto a otro punto
}

static char jwt[2048];
static char *http_req_ex(const char *url, int *outlen, int bearer, int quiet) {
  if (!quiet) { g_step = 1; g_err = 0; g_status = 0; }
  CURL *c = curl_easy_init();
  if (!c) { g_err = -1; return NULL; }
  struct curl_slist *hdr = NULL;
  if (bearer && jwt[0]) {
    static char auth[2200];
    snprintf(auth, sizeof auth, "Authorization: Bearer %s", jwt);
    hdr = curl_slist_append(hdr, auth);
    curl_easy_setopt(c, CURLOPT_HTTPHEADER, hdr);
  }
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
  curl_easy_setopt(c, CURLOPT_XFERINFODATA, (void *)(intptr_t)seek_gen);
  if (!quiet) g_step = 4;
  CURLcode rc = curl_easy_perform(c);
  long st = 0; curl_easy_getinfo(c, CURLINFO_RESPONSE_CODE, &st);
  if (!quiet) { g_err = (int)rc; g_status = (int)st; }
  curl_easy_cleanup(c);
  if (hdr) curl_slist_free_all(hdr);
  if (rc != CURLE_OK || st >= 400) { free(m.b); return NULL; }
  if (outlen) *outlen = (int)m.n;
  return m.b;
}
static char *http_req(const char *url, int *outlen, int bearer) { return http_req_ex(url, outlen, bearer, 0); }
static char *http_get(const char *url, int *outlen) { return http_req_ex(url, outlen, 0, 0); }

// JSON minimo (definido mas abajo)
static const char *jws(const char *p);
static const char *jget(const char *p, const char *key);
static void jstr(const char *v, char *dst, int cap);

static int copy_str(const char *p, char *dst, int max) { // copia hasta la comilla
  int i = 0; while (*p && *p != '"' && i < max - 1) dst[i++] = *p++;
  dst[i] = 0; return i;
}

// Escribe un caracter Unicode en UTF-8
static int put_utf8(char *d, int room, unsigned cp) {
  if (cp < 0x80)    { if (room < 1) return 0; d[0] = cp; return 1; }
  if (cp < 0x800)   { if (room < 2) return 0; d[0] = 0xC0 | (cp >> 6); d[1] = 0x80 | (cp & 0x3F); return 2; }
  if (cp < 0x10000) { if (room < 3) return 0; d[0] = 0xE0 | (cp >> 12); d[1] = 0x80 | ((cp >> 6) & 0x3F); d[2] = 0x80 | (cp & 0x3F); return 3; }
  if (room < 4) return 0;
  d[0] = 0xF0 | (cp >> 18); d[1] = 0x80 | ((cp >> 12) & 0x3F); d[2] = 0x80 | ((cp >> 6) & 0x3F); d[3] = 0x80 | (cp & 0x3F);
  return 4;
}

// Copia un texto JSON hasta la comilla final, resolviendo los escapes (á, \/, \", ...)
static void copy_json(const char *p, char *dst, int max) {
  int i = 0;
  while (*p && *p != '"' && i < max - 1) {
    if (*p == '\\' && p[1]) {
      if (p[1] == 'u' && p[2] && p[3] && p[4] && p[5]) {
        char hx[5] = { p[2], p[3], p[4], p[5], 0 };
        unsigned cp = (unsigned)strtol(hx, NULL, 16);
        p += 6;
        if (cp >= 0xD800 && cp < 0xDC00 && p[0] == '\\' && p[1] == 'u') {     // par sustituto
          char h2[5] = { p[2], p[3], p[4], p[5], 0 };
          unsigned lo = (unsigned)strtol(h2, NULL, 16);
          if (lo >= 0xDC00 && lo < 0xE000) { cp = 0x10000 + ((cp - 0xD800) << 10) + (lo - 0xDC00); p += 6; }
        }
        int w = put_utf8(dst + i, max - 1 - i, cp);
        if (!w) break;
        i += w; continue;
      }
      char e = p[1];
      dst[i++] = e == 'n' ? ' ' : e == 't' ? ' ' : e;
      p += 2; continue;
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
    copy_json(nm + 8, c->name, sizeof c->name);
    c->logo[0] = 0;
    const char *lg = jget(p - 8, "colorLogoPNG");             // p-8 = la "{" del canal
    if (!lg) lg = jget(p - 8, "logo");
    if (lg && *jws(lg) == '{') { const char *pa = jget(lg, "path"); if (pa) jstr(pa, c->logo, sizeof c->logo); }
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
  char ts_types[48], ats_types[48], alang[16];
  int asegs, aseg_err, apl_loads, apl_err, packed, amode, ahttp;
  char auri[80];
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

// Lee un atributo de una etiqueta HLS (NOMBRE=valor o NOMBRE="valor")
static int get_attr(const char *line, const char *name, char *out, int cap) {
  int nl = strlen(name);
  const char *p = line;
  while ((p = strstr(p, name)) != NULL) {
    if ((p == line || p[-1] == ',' || p[-1] == ':') && p[nl] == '=') {
      p += nl + 1; int i = 0;
      if (*p == '"') { p++; while (*p && *p != '"' && i < cap - 1) out[i++] = *p++; }
      else while (*p && *p != ',' && i < cap - 1) out[i++] = *p++;
      out[i] = 0; return 1;
    }
    p += nl;
  }
  if (cap > 0) out[0] = 0;
  return 0;
}

// Elige la variante de mayor calidad con alto <= MAX_HEIGHT (o la mas baja si ninguna cabe).
// Si el audio viene en una lista aparte (#EXT-X-MEDIA:TYPE=AUDIO), deja su URL en aout (prefiere espanol).
#define MAX_MEDIA 16
static int pick_variant(const char *m, const char *base, char *out, int cap, char *aout, int acap) {
  static char line[4096], best[4096], low[4096], tmp[64];
  static struct { char group[64], lang[16], uri[2048]; int def; } media[MAX_MEDIA];
  int nmedia = 0;
  char best_grp[64] = "", low_grp[64] = "", grp[64] = "";
  long best_bw = -1, low_bw = 0x7FFFFFFF; int best_h = 0, low_h = 0;
  best[0] = low[0] = 0; aout[0] = 0;
  long bw = 0; int h = 0, pending = 0, skip = 0, any = 0;
  const char *p = m;
  while ((p = next_line(p, line, sizeof line)) != NULL) {
    if (!strncmp(line, "#EXT-X-MEDIA:", 13)) {
      get_attr(line, "TYPE", tmp, sizeof tmp);
      if (!strcmp(tmp, "AUDIO") && nmedia < MAX_MEDIA && get_attr(line, "URI", media[nmedia].uri, sizeof media[0].uri)) {
        get_attr(line, "GROUP-ID", media[nmedia].group, sizeof media[0].group);
        get_attr(line, "LANGUAGE", media[nmedia].lang, sizeof media[0].lang);
        get_attr(line, "DEFAULT", tmp, sizeof tmp);
        media[nmedia].def = !strcmp(tmp, "YES");
        nmedia++; st.alt_audio++;
      }
    } else if (!strncmp(line, "#EXT-X-STREAM-INF:", 18)) {
      any = 1; pending = 1; skip = 0; bw = 0; h = 0;
      if (get_attr(line, "BANDWIDTH", tmp, sizeof tmp)) bw = atol(tmp);
      if (get_attr(line, "RESOLUTION", tmp, sizeof tmp)) { const char *x = strchr(tmp, 'x'); if (x) h = atoi(x + 1); }
      if (get_attr(line, "CODECS", tmp, sizeof tmp) && !strstr(tmp, "avc1")) skip = 1;
      get_attr(line, "AUDIO", grp, sizeof grp);
    } else if (pending && line[0] && line[0] != '#') {
      pending = 0;
      if (skip) continue;
      int fits = h > 0 ? h <= MAX_HEIGHT : bw <= MAX_BW_NORES;
      if (fits && bw > best_bw) { best_bw = bw; best_h = h; snprintf(best, sizeof best, "%s", line); snprintf(best_grp, sizeof best_grp, "%s", grp); }
      if (bw < low_bw) { low_bw = bw; low_h = h; snprintf(low, sizeof low, "%s", line); snprintf(low_grp, sizeof low_grp, "%s", grp); }
    }
  }
  if (!any) { snprintf(out, cap, "%s", base); snprintf(st.variant, sizeof st.variant, "lista unica"); return 0; }
  const char *pick = best[0] ? best : low;
  const char *g = best[0] ? best_grp : low_grp;
  if (!pick[0]) return -1;
  url_resolve(base, pick, out, cap);
  snprintf(st.variant, sizeof st.variant, "%dp  %ld kbps", best[0] ? best_h : low_h, (best[0] ? best_bw : low_bw) / 1000);
  // audio aparte: del grupo de la variante; espanol > por defecto > el primero
  int bi = -1, bs = -1;
  for (int i = 0; i < nmedia; i++) {
    if (g[0] && strcmp(media[i].group, g)) continue;
    int sc = (!strncmp(media[i].lang, "es", 2) || !strncmp(media[i].lang, "spa", 3)) ? 3 : media[i].def ? 2 : 1;
    if (sc > bs) { bs = sc; bi = i; }
  }
  if (bi >= 0) {
    url_resolve(base, media[bi].uri, aout, acap);
    snprintf(st.auri, sizeof st.auri, "%.70s", media[bi].uri);
    snprintf(st.alang, sizeof st.alang, "%s", media[bi].lang[0] ? media[bi].lang : "?");
  }
  return 0;
}

// ---- Colas de segmentos (red -> demux) ----
typedef struct Seg { struct Seg *next; uint8_t *data; int len, epoch, reset, gen; } Seg;
typedef struct { Seg *head, *tail; int count; } SegQ;
static SegQ vsq, asq;            // video (y audio si va junto) / audio aparte

static void seg_push(SegQ *q, uint8_t *d, int len, int epoch, int reset, int gen) {
  Seg *s = malloc(sizeof *s); if (!s) { free(d); return; }
  s->next = NULL; s->data = d; s->len = len; s->epoch = epoch; s->reset = reset; s->gen = gen;
  lock();
  if (gen != seek_gen) { unlock(); free(d); free(s); return; }   // llego tarde: ya se salto a otro punto
  if (q->tail) q->tail->next = s; else q->head = s;
  q->tail = s; q->count++;
  unlock();
}
static Seg *seg_pop(SegQ *q) {
  lock();
  Seg *s = q->head;
  if (s) { q->head = s->next; if (!q->head) q->tail = NULL; q->count--; }
  unlock();
  return s;
}

// ---- Cifrado AES-128 de HLS (#EXT-X-KEY:METHOD=AES-128) ----
// Cada segmento va cifrado con AES-128-CBC. La llave (16 bytes) se baja de la URI de la etiqueta;
// el IV viene en la etiqueta o, si no, es el numero de secuencia del segmento.
static int hexval(int c) { return c >= '0' && c <= '9' ? c - '0' : c >= 'a' && c <= 'f' ? c - 'a' + 10 : c >= 'A' && c <= 'F' ? c - 'A' + 10 : -1; }

// Descifra en un bufer nuevo; devuelve el largo o -1
static int aes_decrypt(const uint8_t *key, const uint8_t *in, int len, const uint8_t *iv, uint8_t **out) {
  *out = NULL;
  if (len <= 0 || len % 16) return -1;
  uint8_t *o = malloc(len + 16);
  if (!o) return -1;
  EVP_CIPHER_CTX *c = EVP_CIPHER_CTX_new();
  if (!c) { free(o); return -1; }
  int n1 = 0, n2 = 0, ok = EVP_DecryptInit_ex(c, EVP_aes_128_cbc(), NULL, key, iv) == 1 &&
                           EVP_DecryptUpdate(c, o, &n1, in, len) == 1;
  if (ok && EVP_DecryptFinal_ex(c, o + n1, &n2) != 1) n2 = 0;   // relleno raro: se queda con lo descifrado
  EVP_CIPHER_CTX_free(c);
  if (!ok) { free(o); return -1; }
  *out = o;
  return n1 + n2;
}

// ---- Hilos de red: recargan su lista y bajan segmentos ----
// Hay uno para el video y, si el canal trae el audio en otra lista, otro para el audio.
#define MAX_SEGS 4096          // una pelicula de 2 h tiene ~1200 segmentos
typedef struct { char *uri; char *key; int epoch, method, has_iv; uint8_t iv[16]; float dur; } SegInfo;  // method: 0 nada, 1 AES-128, 2 otro
typedef struct {
  char url[4096], orig[4096];
  int mode;                      // audio: 0 URL original, 1 ruta + parametros del video, 2 original + parametros del video
  SegQ *q;
  int is_audio;
  char key_uri[4096]; uint8_t key_val[16]; int key_ok;
  char line[4096], cur_key[4096], raw[4096];
  SegInfo segs[MAX_SEGS];
} NetCtx;
static NetCtx *vnet, *anet;

// A la carta: duracion total y a donde saltar (en segundos)
static volatile int is_vod;
static volatile double vod_total, seek_target, seek_landed;

// La lista de audio aparte rechazada (401): prueba con los parametros de la lista de video, que si funciona
static void audio_alt_url(NetCtx *c) {
  const char *vq = vnet ? strchr(vnet->url, '?') : NULL;
  if (c->mode == 0 || !vq) { snprintf(c->url, sizeof c->url, "%s", c->orig); return; }
  char path[4096]; snprintf(path, sizeof path, "%s", c->orig);
  char *q = strchr(path, '?');
  if (c->mode == 1) { if (q) *q = 0; snprintf(c->url, sizeof c->url, "%s%s", path, vq); }
  else snprintf(c->url, sizeof c->url, "%s%c%s", c->orig, q ? '&' : '?', vq + 1);
}

static int get_key(NetCtx *c, const char *uri) {
  if (c->key_ok && !strcmp(uri, c->key_uri)) return 0;
  int n = 0;
  char *k = http_get(uri, &n);
  st.http = g_status; st.curl = g_err;
  if (!k || n != 16) { free(k); st.key_err++; c->key_ok = 0; return -1; }
  memcpy(c->key_val, k, 16); free(k);
  snprintf(c->key_uri, sizeof c->key_uri, "%s", uri);
  c->key_ok = 1; st.keys++;
  return 0;
}

static int net_thread(SceSize a, void *argp) {
  NetCtx *c = *(NetCtx **)argp;
  int64_t next_seq = -1;
  int pending_reset = 0, gen = seek_gen;
  while (playing) {
    int len = 0;
    char *pl = http_get(c->url, &len);
    st.http = g_status; st.curl = g_err;
    if (c->is_audio) st.ahttp = g_status;
    if (!pl && gen != seek_gen) continue;            // se corto por un salto: no es un error
    if (!pl) {
      if (c->is_audio) {
        st.apl_err++;
        if (g_status == 401 || g_status == 403) { c->mode = (c->mode + 1) % 3; audio_alt_url(c); st.amode = c->mode; nap_ms(300); continue; }
      } else st.pl_err++;
      nap_ms(2000); continue;
    }
    if (c->is_audio) st.apl_loads++; else st.pl_loads++;
    int64_t mseq = 0, dseq = 0; int tdur = 6, n = 0, ended = 0, dcount = 0;
    int method = 0, has_iv = 0; uint8_t iv[16]; c->cur_key[0] = 0;
    float dur = 0;
    memset(iv, 0, 16);
    const char *p = pl;
    while ((p = next_line(p, c->line, sizeof c->line)) != NULL) {
      const char *line = c->line;
      if (!strncmp(line, "#EXT-X-MEDIA-SEQUENCE:", 22)) mseq = atoll(line + 22);
      else if (!strncmp(line, "#EXT-X-DISCONTINUITY-SEQUENCE:", 30)) dseq = atoll(line + 30);
      else if (!strncmp(line, "#EXT-X-TARGETDURATION:", 22)) tdur = atoi(line + 22);
      else if (!strncmp(line, "#EXT-X-DISCONTINUITY", 20) && line[20] != '-') dcount++;
      else if (!strncmp(line, "#EXT-X-ENDLIST", 14)) ended = 1;
      else if (!strncmp(line, "#EXTINF:", 8)) dur = (float)atof(line + 8);
      else if (!strncmp(line, "#EXT-X-KEY:", 11)) {
        method = strstr(line, "METHOD=NONE") ? 0 : strstr(line, "METHOD=AES-128") ? 1 : 2;
        if (method == 2) { const char *m = strstr(line, "METHOD="); snprintf(st.keymethod, sizeof st.keymethod, "%.20s", m ? m + 7 : "?"); }
        c->cur_key[0] = 0; has_iv = 0;
        if (get_attr(line, "URI", c->raw, sizeof c->raw)) url_resolve(c->url, c->raw, c->cur_key, sizeof c->cur_key);
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
          SegInfo *si = &c->segs[n];
          url_resolve(c->url, line, c->raw, sizeof c->raw);
          si->uri = strdup(c->raw);
          if (si->uri) {
            si->epoch = (int)(dseq + dcount);   // igual en la lista de video y la de audio
            si->method = method; si->has_iv = has_iv;
            memcpy(si->iv, iv, 16);
            si->key = method == 1 && c->cur_key[0] ? strdup(c->cur_key) : NULL;
            si->dur = dur > 0 ? dur : (float)tdur;
            n++;
          }
        }
      }
    }
    free(pl);
    if (tdur < 1) tdur = 1;
    if (next_seq < 0) next_seq = ended ? mseq : mseq + (n > 3 ? n - 3 : 0);   // a la carta: desde el inicio; en vivo: cerca del final
    else if (next_seq > mseq + n + 10) next_seq = mseq + (n > 3 ? n - 3 : 0);
    if (next_seq < mseq) { next_seq = mseq; pending_reset = 1; }   // nos quedamos atras
    if (ended && !c->is_audio) {                       // a la carta: duracion total para la barra
      double tot = 0; for (int i = 0; i < n; i++) tot += c->segs[i].dur;
      vod_total = tot; is_vod = 1;
    }
    if (gen != seek_gen) {                             // el usuario salto: busca el segmento de ese momento
      gen = seek_gen;
      double t = 0, target = seek_target; int idx = 0;
      for (idx = 0; idx < n - 1 && t + c->segs[idx].dur <= target; idx++) t += c->segs[idx].dur;
      next_seq = mseq + idx; pending_reset = 1;
      if (!c->is_audio) seek_landed = t;
    }
    int got = 0;
    for (int i = 0; i < n && playing && gen == seek_gen; i++) {
      int64_t seq = mseq + i;
      if (seq < next_seq) continue;
      while (playing && gen == seek_gen && c->q->count >= SEG_AHEAD) nap_ms(20);
      if (!playing || gen != seek_gen) break;
      SegInfo *si = &c->segs[i];
      next_seq = seq + 1;
      if (si->method == 2) { st.enc_other++; pending_reset = 1; continue; }   // cifrado que no se puede abrir (DRM)
      int sl = 0;
      char *d = http_get(si->uri, &sl);
      st.http = g_status; st.curl = g_err;
      if (!d && gen != seek_gen) break;
      if (!d) { if (c->is_audio) st.aseg_err++; else st.seg_err++; pending_reset = 1; continue; }
      if (si->method == 1) {
        st.enc_aes++;
        uint8_t ivb[16], *plain = NULL;
        if (si->has_iv) memcpy(ivb, si->iv, 16);
        else { memset(ivb, 0, 16); for (int k = 0; k < 8; k++) ivb[15 - k] = (uint8_t)((uint64_t)seq >> (8 * k)); }
        int pn = (si->key && get_key(c, si->key) == 0) ? aes_decrypt(c->key_val, (uint8_t *)d, sl, ivb, &plain) : -1;
        free(d);
        if (pn < 0) { st.dec_fail++; pending_reset = 1; continue; }
        d = (char *)plain; sl = pn;
      }
      seg_push(c->q, (uint8_t *)d, sl, si->epoch, pending_reset, gen);
      pending_reset = 0; got = 1;
      if (c->is_audio) st.asegs++; else st.segs++;
    }
    for (int i = 0; i < n; i++) { free(c->segs[i].uri); free(c->segs[i].key); c->segs[i].uri = c->segs[i].key = NULL; }
    if (gen != seek_gen) continue;
    if (ended && !got) {                               // termino: espera por si el usuario retrocede
      if (!c->is_audio) snprintf(st.msg, sizeof st.msg, "Fin");
      while (playing && gen == seek_gen) nap_ms(100);
      st.msg[0] = 0;
      continue;
    }
    if (!got) nap_ms(tdur * 500);
  }
  return 0;
}

// ---- Cola de video comprimido (demux -> decodificador) ----
typedef struct VAu { struct VAu *next; uint8_t *data; int len; int64_t pts; int epoch, gen; } VAu;
static VAu *vq_head, *vq_tail; static int vq_count;

static void vq_push(const uint8_t *d, int len, int64_t pts, int epoch, int gen) {
  while (playing && gen == seek_gen && vq_count >= VQ_MAX) nap_ms(5);
  if (!playing || gen != seek_gen) return;
  VAu *v = malloc(sizeof *v); if (!v) return;
  v->data = malloc(len); if (!v->data) { free(v); return; }
  memcpy(v->data, d, len); v->len = len; v->pts = pts; v->epoch = epoch; v->gen = gen; v->next = NULL;
  lock();
  if (gen != seek_gen) { unlock(); free(v->data); free(v); return; }
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
typedef struct { int64_t pts; int epoch, samples, rate, ch, gen; int16_t pcm[2048 * 2]; } Pcm;
static Pcm *pcm_ring; static int pcm_rd, pcm_wr, pcm_count;

// ---- Reloj comun (90 kHz, como los PTS) ----
static int clk_set, clk_epoch;
static int64_t clk_pts; static uint64_t clk_us;
static volatile int paused;
static int64_t pause_pts;
static int64_t clock_now(void) { return paused ? pause_pts : clk_pts + (int64_t)(now_us() - clk_us) * 9 / 100; }
static void clock_set(int64_t pts, int epoch) { clk_pts = pts; clk_us = now_us(); clk_epoch = epoch; clk_set = 1; pause_pts = pts; }

// Posicion en segundos (a la carta): base + lo que avanzo el reloj desde el primer cuadro tras el salto
static int pos_valid; static double pos_base; static int64_t pos_pts;
static double cur_pos(void) { return pos_valid ? pos_base + (double)(clock_now() - pos_pts) / 90000.0 : pos_base; }

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
  int cur_cw = 0, cur_ch = 0, failed = 0, my_gen = seek_gen;
  int64_t last_in = -1, frame_dur = 3003, last_out = -1;
  while (playing) {
    VAu *au = vq_pop();
    if (!au) { sceKernelDelayThread(2000); continue; }
    if (au->gen != seek_gen) { free(au->data); free(au); continue; }
    if (au->gen != my_gen) {
      // salto: el decodificador guarda cuadros viejos; se cierra y se abre con el siguiente cuadro clave
      my_gen = au->gen; last_in = last_out = -1;
      if (vdec) {
        vreset_ack = 0; vreset_req = 1;
        while (playing && !vreset_ack) sceKernelDelayThread(2000);
        vreset_req = 0;
        vdec_close();
      }
    }
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
    int ep = au->epoch, ag = au->gen;
    free(au->data); free(au);
    if (r < 0) { st.dec_err++; st.last_dec_err = (unsigned)r; continue; }
    if (arr.numOfOutput == 0) continue;
    int64_t opts = -1;
    if (!(pic.info.pts.upper == NO_TS && pic.info.pts.lower == NO_TS))
      opts = (int64_t)(((uint64_t)pic.info.pts.upper << 32) | pic.info.pts.lower);
    if (opts < 0 && last_out >= 0) opts = last_out + frame_dur;
    if (opts >= 0) last_out = opts;
    lock();
    if (ag == seek_gen) {
      slots[si].pts = opts; slots[si].epoch = ep; slots[si].seq = out_seq++;
      slots[si].state = SL_READY;
    }
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
static void audio_frame(const uint8_t *d, int len, int64_t pts, int epoch, int gen) {
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
  while (playing && gen == seek_gen && pcm_count >= PCM_SLOTS) nap_ms(5);
  lock();
  if (!playing || gen != seek_gen || pcm_count >= PCM_SLOTS) { unlock(); return; }
  Pcm *c = &pcm_ring[pcm_wr];
  c->pts = pts; c->epoch = epoch; c->samples = samples; c->rate = rate; c->ch = ch; c->gen = gen;
  memcpy(c->pcm, apcm, (size_t)samples * 2 * ch);
  pcm_wr = (pcm_wr + 1) % PCM_SLOTS; pcm_count++;
  unlock();
  st.aframes++;
}

// ---- Demultiplexor MPEG-TS (uno por lista) ----
typedef struct { uint8_t *buf; int len, cap, want, started; int64_t pts; } Pes;
typedef struct {
  SegQ *q;
  int pmt_pid, vpid, apid, epoch, use_audio, gen;
  Pes vpes, apes;
  char *types;                   // tipos de pista vistos (para la pantalla de datos)
} Dmx;
static Dmx vdmx, admx;

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

// Recorre cuadros ADTS seguidos; el primero tiene pts0 y los demas avanzan 1024 muestras
static void adts_run(const uint8_t *buf, int len, int64_t pts0, int epoch, int gen) {
  int i = 0, k = 0;
  while (i + 7 <= len && playing) {
    const uint8_t *d = buf + i;
    if (d[0] != 0xFF || (d[1] & 0xF6) != 0xF0) { i++; continue; }
    int fl = ((d[3] & 3) << 11) | (d[4] << 3) | (d[5] >> 5);
    if (fl < 7 || i + fl > len) break;
    int sfi = (d[2] >> 2) & 15;
    int rate = sfi < 13 ? ADTS_RATES[sfi] : 48000;
    int64_t pts = pts0 >= 0 ? pts0 + (int64_t)k * 1024 * 90000 / rate : -1;
    audio_frame(d, fl, pts, epoch, gen);
    i += fl; k++;
  }
}

static void pes_flush(Dmx *x, Pes *p, int is_video) {
  if (p->started && p->len > 0) {
    if (is_video) vq_push(p->buf, p->len, p->pts, x->epoch, x->gen);
    else adts_run(p->buf, p->len, p->pts, x->epoch, x->gen);
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

static void ts_reset(Dmx *x) { x->pmt_pid = x->vpid = x->apid = -1; }

static void ts_packet(Dmx *x, const uint8_t *p) {
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
      if (prog != 0) { x->pmt_pid = ((d[i + 2] & 0x1F) << 8) | d[i + 3]; break; }
    }
  } else if (pid == x->pmt_pid && pusi) {                   // PMT
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
    x->vpid = nv; x->apid = x->use_audio ? na : -1;
    types[tl] = 0;
    if (x->types && strcmp(types, x->types)) snprintf(x->types, 48, "%s", types);
  } else if (pid == x->vpid || pid == x->apid) {
    int vid = pid == x->vpid;
    Pes *pe = vid ? &x->vpes : &x->apes;
    if (pusi) { pes_flush(x, pe, vid); pes_start(pe, d, n); }
    else if (pe->started) pes_append(pe, d, n);
    if (pe->started && pe->want > 0 && pe->len >= pe->want) pes_flush(x, pe, vid);
  }
}

// Audio empaquetado (.aac): etiqueta ID3 con la marca de tiempo y luego cuadros ADTS
static int64_t id3_pts(const uint8_t *d, int len, int *hdr) {
  static const char own[] = "com.apple.streaming.transportStreamTimestamp";   // incluye el 0 final
  int64_t pts = -1;
  *hdr = 0;
  while (len - *hdr >= 10 && !memcmp(d + *hdr, "ID3", 3)) {
    const uint8_t *t = d + *hdr;
    int sz = ((t[6] & 0x7F) << 21) | ((t[7] & 0x7F) << 14) | ((t[8] & 0x7F) << 7) | (t[9] & 0x7F);
    int total = 10 + sz + ((t[5] & 0x10) ? 10 : 0);
    for (int i = 10; i + (int)sizeof own + 8 <= total && *hdr + i + (int)sizeof own + 8 <= len; i++) {
      if (!memcmp(t + i, own, sizeof own)) {
        const uint8_t *b = t + i + sizeof own;
        pts = ((int64_t)(b[3] & 1) << 32) | ((int64_t)b[4] << 24) | ((int64_t)b[5] << 16) | ((int64_t)b[6] << 8) | b[7];
        break;
      }
    }
    *hdr += total;
  }
  if (*hdr > len) *hdr = len;
  return pts;
}

static void dmx_segment(Dmx *x, Seg *s) {
  if (s->gen != x->gen) {                        // salto: lo que quedaba a medias se tira
    x->vpes.len = x->apes.len = 0; x->vpes.started = x->apes.started = 0;
    ts_reset(x); x->gen = s->gen; x->epoch = s->epoch;
  }
  if (s->reset || s->epoch != x->epoch) {
    pes_flush(x, &x->vpes, 1); pes_flush(x, &x->apes, 0);
    ts_reset(x); x->epoch = s->epoch;
  }
  const uint8_t *d = s->data;
  if (s->len >= 3 && !memcmp(d, "ID3", 3)) {                  // audio empaquetado
    if (!x->use_audio) return;
    int h; int64_t pts = id3_pts(d, s->len, &h);
    st.packed++;
    adts_run(d + h, s->len - h, pts, x->epoch, x->gen);
    return;
  }
  int i = 0;
  while (i + 188 <= s->len && playing) {
    if (d[i] != 0x47) { i++; continue; }
    ts_packet(x, d + i); i += 188;
  }
}

static int demux_thread(SceSize a, void *argp) {
  Dmx *x = *(Dmx **)argp;
  ts_reset(x); x->epoch = -1;
  x->vpes.pts = x->apes.pts = -1;
  while (playing) {
    Seg *s = seg_pop(x->q);
    if (!s) { sceKernelDelayThread(5000); continue; }
    if (s->gen == seek_gen) dmx_segment(x, s);
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
    if (paused) { sceKernelDelayThread(10000); continue; }
    lock();
    if (pcm_count == 0) { unlock(); sceKernelDelayThread(5000); continue; }
    Pcm *c = &pcm_ring[pcm_rd];
    if (c->gen != seek_gen) { pcm_rd = (pcm_rd + 1) % PCM_SLOTS; pcm_count--; unlock(); continue; }
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
      if (s->pts >= 0) {
        if (!clk_set) { pos_base = seek_landed; }        // primer cuadro tras empezar o saltar
        else pos_base = cur_pos();                       // cambio de tramo (anuncio): la posicion sigue
        clock_set(s->pts, s->epoch);
        pos_pts = s->pts; pos_valid = 1;
      }
      take_frame(f); break;
    }
    int64_t d = s->pts - clock_now();
    if (d > 5 * 90000 || d < -90000) {                   // salto raro o >1 s tarde: re-ancla
      pos_base = cur_pos(); clock_set(s->pts, s->epoch); pos_pts = s->pts;
      take_frame(f); break;
    }
    if (d > 0) break;                                                        // aun no toca
    int g = oldest_ready(f);
    if (g >= 0 && slots[g].epoch == clk_epoch && slots[g].pts >= 0 && slots[g].pts <= clock_now()) {
      s->state = SL_FREE; st.dropped++; continue;                           // ya toca el siguiente
    }
    take_frame(f); break;
  }
  unlock();
}

// Salta a "target" segundos: vacia todo y la red vuelve a empezar desde ese segmento
static void do_seek(double target) {
  if (target < 0) target = 0;
  if (vod_total > 10 && target > vod_total - 5) target = vod_total - 5;
  lock();
  seek_target = target; seek_landed = target;
  seek_gen++;
  SegQ *qs[2] = { &vsq, &asq };
  for (int k = 0; k < 2; k++) {
    Seg *s = qs[k]->head;
    while (s) { Seg *nx = s->next; free(s->data); free(s); s = nx; }
    qs[k]->head = qs[k]->tail = NULL; qs[k]->count = 0;
  }
  VAu *v = vq_head;
  while (v) { VAu *nx = v->next; free(v->data); free(v); v = nx; }
  vq_head = vq_tail = NULL; vq_count = 0;
  pcm_rd = pcm_wr = pcm_count = 0;
  for (int i = 0; i < NSLOTS; i++) if (slots[i].state == SL_READY) slots[i].state = SL_FREE;
  clk_set = 0; paused = 0;
  pos_base = target; pos_valid = 0;
  unlock();
}

static void toggle_pause(void) {
  lock();
  if (!paused) { pause_pts = clock_now(); paused = 1; }
  else { clk_pts = pause_pts; clk_us = now_us(); paused = 0; }
  unlock();
}

static void fmt_time(double t, char *o, int cap) {
  if (t < 0) t = 0;
  int s = (int)t, h = s / 3600, m = (s / 60) % 60; s %= 60;
  if (h) snprintf(o, cap, "%d:%02d:%02d", h, m, s); else snprintf(o, cap, "%d:%02d", m, s);
}

// Barra de reproduccion (a la carta)
static void draw_osd(double pos, int pending, double target) {
  char a[16], b[16], c[16], l[96];
  double tot = vod_total > 0 ? vod_total : 1;
  vita2d_draw_rectangle(0, 470, 960, 74, RGBA8(0,0,0,190));
  vita2d_draw_rectangle(30, 486, 900, 8, RGBA8(90,90,90,255));
  double f = (pending ? target : pos) / tot; if (f < 0) f = 0; if (f > 1) f = 1;
  vita2d_draw_rectangle(30, 486, (float)(900 * f), 8, pending ? RGBA8(255,200,60,255) : RGBA8(90,140,255,255));
  fmt_time(pos, a, sizeof a); fmt_time(vod_total, b, sizeof b); fmt_time(target, c, sizeof c);
  if (pending) snprintf(l, sizeof l, "%s / %s   ->  %s", a, b, c);
  else snprintf(l, sizeof l, "%s / %s%s", a, b, paused ? "   PAUSA" : "");
  vita2d_pgf_draw_text(pgf, 30, 522, RGBA8(255,255,255,255), 1.0f, l);
  vita2d_pgf_draw_text(pgf, 520, 522, RGBA8(170,170,170,255), 0.8f, "</>: 10 s   L/R: 1 min   CUADRADO: pausa");
}

static void draw_debug(int y0) {
  char l[200]; uint32_t col = RGBA8(255,255,0,255);
  snprintf(l, sizeof l, "Calidad: %s   URL %s%s   audio aparte: %d", st.variant, st.url2 ? "nueva" : "vieja",
           st.jwt_added ? "  +jwt" : "", st.alt_audio);
  vita2d_pgf_draw_text(pgf, 20, y0, col, 0.9f, l);
  snprintf(l, sizeof l, "Red: segmentos %d  errores %d  lista %d/%d  http %d  curl %d  cola %d",
           st.segs, st.seg_err, st.pl_loads, st.pl_err, st.http, st.curl, vsq.count);
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
  if (anet) {
    snprintf(l, sizeof l, "Audio aparte (%s): segmentos %d  errores %d  lista %d/%d  http %d  modo %d  aac %d  TS: %s",
             st.alang, st.asegs, st.aseg_err, st.apl_loads, st.apl_err, st.ahttp, st.amode, st.packed, st.ats_types);
    vita2d_pgf_draw_text(pgf, 20, y0 + 182, RGBA8(120,255,160,255), 0.9f, l);
    snprintf(l, sizeof l, "URI audio: %s", st.auri);
    vita2d_pgf_draw_text(pgf, 20, y0 + 208, RGBA8(120,255,160,255), 0.8f, l);
  }
  if (st.msg[0]) vita2d_pgf_draw_text(pgf, 20, y0 + 130, RGBA8(255,120,120,255), 0.9f, st.msg);
}

static void play_stream(const char *kind, const char *id) {
  static char url[4096];
  memset(&st, 0, sizeof st);
  int use2 = stitcher[0] && sparams[0];
  if (use2) snprintf(url, sizeof url, STITCH_URL2, stitcher, kind, id, sparams, jwt);
  else snprintf(url, sizeof url, STITCH_URL, kind, id, uuid, sid, jwt);
  status("Cargando...");
  char *master = http_get(url, NULL);
  if (!master) {
    char m[200]; snprintf(m, sizeof m, "No se pudo abrir: curl %d  http %d%s", g_err, g_status,
                         g_status == 403 || g_status == 404 ? "  (puede ser solo con DRM)" : "");
    status(m); sceKernelDelayThread(4000000); return;
  }
  vnet = calloc(1, sizeof(NetCtx));
  anet = calloc(1, sizeof(NetCtx));
  if (!vnet || !anet) { free(master); free(vnet); free(anet); vnet = anet = NULL; status("Sin memoria"); sceKernelDelayThread(3000000); return; }
  int pv = pick_variant(master, url, vnet->url, sizeof vnet->url, anet->url, sizeof anet->url);
  free(master);
  st.url2 = use2;
  if (pv < 0) {
    free(vnet); free(anet); vnet = anet = NULL;
    status("La lista del canal no tiene video H.264"); sceKernelDelayThread(4000000); return;
  }
  // las listas de calidad y de audio tambien piden el token
  NetCtx *nc[2] = { vnet, anet };
  for (int k = 0; k < 2; k++) {
    char *u = nc[k]->url;
    if (!u[0] || strstr(u, "jwt=")) continue;
    int n = strlen(u);
    snprintf(u + n, sizeof nc[k]->url - n, "%cjwt=%s", strchr(u, '?') ? '&' : '?', jwt);
    st.jwt_added = 1;
  }
  if (!anet->url[0]) { free(anet); anet = NULL; }
  else snprintf(anet->orig, sizeof anet->orig, "%s", anet->url);
  vnet->q = &vsq; vnet->is_audio = 0;
  if (anet) { anet->q = &asq; anet->is_audio = 1; }

  // estado inicial
  mtx = sceKernelCreateMutex("pv_mtx", 0, 0, NULL);
  memset(&vsq, 0, sizeof vsq); memset(&asq, 0, sizeof asq);
  memset(&vdmx, 0, sizeof vdmx); memset(&admx, 0, sizeof admx);
  vdmx.q = &vsq; vdmx.types = st.ts_types; vdmx.use_audio = anet == NULL;
  admx.q = &asq; admx.types = st.ats_types; admx.use_audio = 1;
  vq_head = vq_tail = NULL; vq_count = 0;
  pcm_ring = malloc(sizeof(Pcm) * PCM_SLOTS);
  pcm_rd = pcm_wr = pcm_count = 0;
  clk_set = 0; clk_epoch = 0;
  memset(slots, 0, sizeof slots);
  for (int i = 0; i < NSLOTS; i++) slots[i].uid = -1;
  shown = -1; out_seq = 0; vreset_req = vreset_ack = 0;
  if (!pcm_ring) { status("Sin memoria"); sceKernelDelayThread(3000000); sceKernelDeleteMutex(mtx); free(vnet); free(anet); vnet = anet = NULL; return; }

  playing = 1; g_abort = 0;
  is_vod = 0; vod_total = 0; seek_target = seek_landed = 0; paused = 0;
  pos_valid = 0; pos_base = 0;
  SceUID th_net = sceKernelCreateThread("pv_net",   net_thread,   0x10000100, 256 * 1024, 0, 0, NULL);
  SceUID th_dmx = sceKernelCreateThread("pv_demux", demux_thread, 0x10000100, 128 * 1024, 0, 0, NULL);
  SceUID th_vid = sceKernelCreateThread("pv_video", vdec_thread,  0x10000100, 64 * 1024,  0, 0, NULL);
  SceUID th_aud = sceKernelCreateThread("pv_audio", audio_thread, 0x10000100, 64 * 1024,  0, 0, NULL);
  SceUID th_anet = -1, th_admx = -1;
  void *arg;
  arg = vnet;  sceKernelStartThread(th_net, sizeof arg, &arg);
  arg = &vdmx; sceKernelStartThread(th_dmx, sizeof arg, &arg);
  sceKernelStartThread(th_vid, 0, NULL);
  sceKernelStartThread(th_aud, 0, NULL);
  if (anet) {                        // audio en lista aparte: su propia red y su propio demux
    th_anet = sceKernelCreateThread("pv_anet", net_thread,   0x10000100, 256 * 1024, 0, 0, NULL);
    th_admx = sceKernelCreateThread("pv_admx", demux_thread, 0x10000100, 128 * 1024, 0, 0, NULL);
    arg = anet;  sceKernelStartThread(th_anet, sizeof arg, &arg);
    arg = &admx; sceKernelStartThread(th_admx, sizeof arg, &arg);
  }

  int show_dbg = 0, seek_pend = 0;
  double seek_to = 0;
  uint64_t seek_t = 0, osd_until = 0;
  while (playing) {
    sceCtrlPeekBufferPositive(0, &pad, 1);
    unsigned pr = pad.buttons & ~oldpad.buttons; oldpad = pad;
    if (pr & SCE_CTRL_CIRCLE) break;
    if (pr & SCE_CTRL_TRIANGLE) show_dbg = !show_dbg;
    if (is_vod) {
      int step = 0;
      if (pr & SCE_CTRL_LEFT) step = -10;
      if (pr & SCE_CTRL_RIGHT) step = 10;
      if (pr & SCE_CTRL_LTRIGGER) step = -60;
      if (pr & SCE_CTRL_RTRIGGER) step = 60;
      if (step) {                                    // junta varios toques antes de saltar
        if (!seek_pend) { lock(); seek_to = cur_pos(); unlock(); seek_pend = 1; }
        seek_to += step;
        if (seek_to < 0) seek_to = 0;
        if (vod_total > 0 && seek_to > vod_total) seek_to = vod_total;
        seek_t = now_us(); osd_until = seek_t + 3000000;
      }
      if (seek_pend && now_us() - seek_t > 700000) { do_seek(seek_to); seek_pend = 0; osd_until = now_us() + 3000000; }
      if (pr & SCE_CTRL_SQUARE) { toggle_pause(); osd_until = now_us() + 3000000; }
      if (pr & (SCE_CTRL_UP | SCE_CTRL_DOWN | SCE_CTRL_CROSS)) osd_until = now_us() + 3000000;
    }

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
      if (sh >= 0) vita2d_draw_rectangle(0, 286, 960, 258, RGBA8(0,0,0,170));
      draw_debug(sh >= 0 ? 310 : 110);
    }
    if (is_vod && !show_dbg && (paused || seek_pend || now_us() < osd_until)) {
      lock(); double pos = cur_pos(); unlock();
      draw_osd(pos, seek_pend, seek_to);
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
  if (th_anet >= 0) { sceKernelWaitThreadEnd(th_anet, NULL, NULL); sceKernelDeleteThread(th_anet); }
  if (th_admx >= 0) { sceKernelWaitThreadEnd(th_admx, NULL, NULL); sceKernelDeleteThread(th_admx); }
  g_abort = 0;

  vita2d_wait_rendering_done();
  vdec_close();
  adec_close();
  Seg *s;
  while ((s = seg_pop(&vsq)) != NULL) { free(s->data); free(s); }
  while ((s = seg_pop(&asq)) != NULL) { free(s->data); free(s); }
  VAu *v; while ((v = vq_pop()) != NULL) { free(v->data); free(v); }
  free(vdmx.vpes.buf); free(vdmx.apes.buf); free(admx.vpes.buf); free(admx.apes.buf);
  memset(&vdmx, 0, sizeof vdmx); memset(&admx, 0, sizeof admx);
  free(vnet); free(anet); vnet = anet = NULL;
  free(pcm_ring); pcm_ring = NULL;
  sceKernelDeleteMutex(mtx); mtx = -1;
  use_pts = 1; pts_tried = 0;
}

// ---------- Buscador ----------
// minusculas y sin acentos, para comparar ("Accion" encuentra "Acción")
static void fold(const char *s, char *o, int cap) {
  int i = 0;
  const unsigned char *u = (const unsigned char *)s;
  while (*u && i < cap - 1) {
    unsigned c = *u;
    if (c == 0xC3 && u[1]) {
      unsigned d = u[1] | 0x20;                 // 0x80-0x9F mayusculas -> 0xA0-0xBF
      char r = 0;
      if (d >= 0xA0 && d <= 0xA5) r = 'a'; else if (d == 0xA7) r = 'c';
      else if (d >= 0xA8 && d <= 0xAB) r = 'e'; else if (d >= 0xAC && d <= 0xAF) r = 'i';
      else if (d == 0xB1) r = 'n'; else if (d >= 0xB2 && d <= 0xB6) r = 'o';
      else if (d >= 0xB9 && d <= 0xBC) r = 'u';
      if (r) { o[i++] = r; u += 2; continue; }
    }
    o[i++] = (c >= 'A' && c <= 'Z') ? c + 32 : c;
    u++;
  }
  o[i] = 0;
}

static void utf8_to_utf16(const char *s, SceWChar16 *o, int cap) {
  int i = 0;
  const unsigned char *u = (const unsigned char *)s;
  while (*u && i < cap - 1) {
    unsigned cp;
    if (*u < 0x80) cp = *u++;
    else if ((*u & 0xE0) == 0xC0 && u[1]) { cp = ((u[0] & 0x1F) << 6) | (u[1] & 0x3F); u += 2; }
    else if ((*u & 0xF0) == 0xE0 && u[1] && u[2]) { cp = ((u[0] & 0x0F) << 12) | ((u[1] & 0x3F) << 6) | (u[2] & 0x3F); u += 3; }
    else { u++; continue; }
    o[i++] = (SceWChar16)cp;
  }
  o[i] = 0;
}

static void utf16_to_utf8(const SceWChar16 *s, char *o, int cap) {
  int i = 0;
  for (; *s; s++) { int w = put_utf8(o + i, cap - 1 - i, *s); if (!w) break; i += w; }
  o[i] = 0;
}

// Abre el teclado de la Vita; devuelve 1 si el usuario confirmo
static int ime_search(char *query, int cap) {
  static SceWChar16 title[32], init[128], buf[128];
  utf8_to_utf16("Buscar", title, 32);
  utf8_to_utf16(query, init, 128);
  memset(buf, 0, sizeof buf);
  SceImeDialogParam ip;
  sceImeDialogParamInit(&ip);
  ip.supportedLanguages = SCE_IME_LANGUAGE_SPANISH | SCE_IME_LANGUAGE_ENGLISH;
  ip.languagesForced = SCE_FALSE;
  ip.type = SCE_IME_TYPE_DEFAULT;
  ip.option = 0;
  ip.textBoxMode = SCE_IME_DIALOG_TEXTBOX_MODE_WITH_CLEAR;
  ip.title = title;
  ip.maxTextLength = 60;
  ip.initialText = init;
  ip.inputTextBuffer = buf;
  if (sceImeDialogInit(&ip) < 0) return 0;
  int ok = 0;
  for (;;) {
    vita2d_start_drawing(); vita2d_clear_screen(); vita2d_end_drawing();
    vita2d_common_dialog_update();
    vita2d_swap_buffers();
    if (sceImeDialogGetStatus() == SCE_COMMON_DIALOG_STATUS_FINISHED) {
      SceImeDialogResult r; memset(&r, 0, sizeof r);
      sceImeDialogGetResult(&r);
      ok = r.button == SCE_IME_DIALOG_BUTTON_ENTER;
      sceImeDialogTerm();
      break;
    }
  }
  if (ok) utf16_to_utf8(buf, query, cap);
  sceCtrlPeekBufferPositive(0, &pad, 1); oldpad = pad;   // que la X del teclado no abra nada
  return ok;
}

// ---------- Imagenes (logos y portadas) ----------
// Un hilo baja las imagenes que pide la pantalla (la seleccionada primero) y las guarda como texturas.
enum { IM_REQ = 1, IM_LOADING, IM_READY, IM_FAIL };
typedef struct { char url[240]; vita2d_texture *tex; int state; uint32_t want, used; } Img;
#define IMG_MAX 96
static Img img_tab[IMG_MAX];
static SceUID img_mtx = -1;
static uint32_t img_tick, img_frame;
static volatile int img_run;

static void img_lock(void)   { sceKernelLockMutex(img_mtx, 1, NULL); }
static void img_unlock(void) { sceKernelUnlockMutex(img_mtx, 1); }

// Pide (si hace falta) y devuelve la textura si ya esta lista. Solo desde el hilo principal.
static vita2d_texture *img_get(const char *url) {
  if (!url || !url[0] || img_mtx < 0) return NULL;
  vita2d_texture *t = NULL;
  int freei = -1;
  img_lock();
  for (int i = 0; i < IMG_MAX; i++) {
    Img *m = &img_tab[i];
    if (!m->state) { if (freei < 0) freei = i; continue; }
    if (!strcmp(m->url, url)) {
      m->used = img_frame;
      if (m->state == IM_READY) t = m->tex;
      else if (m->state == IM_REQ) m->want = ++img_tick;
      img_unlock();
      return t;
    }
  }
  if (freei >= 0) {
    Img *m = &img_tab[freei];
    snprintf(m->url, sizeof m->url, "%s", url);
    m->tex = NULL; m->state = IM_REQ; m->want = ++img_tick; m->used = img_frame;
  }
  img_unlock();
  return NULL;
}

// Libera las que no se ven hace rato. Llamar con la GPU detenida (despues de vita2d_wait_rendering_done).
static void img_gc(void) {
  if (img_mtx < 0) return;
  img_frame++;
  img_lock();
  int used = 0;
  for (int i = 0; i < IMG_MAX; i++) if (img_tab[i].state) used++;
  while (used > IMG_MAX - 12) {
    int v = -1;
    for (int i = 0; i < IMG_MAX; i++) {
      Img *m = &img_tab[i];
      if (!m->state || m->state == IM_LOADING || img_frame - m->used < 30) continue;
      if (v < 0 || (int32_t)(m->used - img_tab[v].used) < 0) v = i;
    }
    if (v < 0) break;
    if (img_tab[v].tex) vita2d_free_texture(img_tab[v].tex);
    memset(&img_tab[v], 0, sizeof img_tab[v]);
    used--;
  }
  img_unlock();
}

static int img_thread(SceSize a, void *u) {
  static char url[300];
  while (img_run) {
    if (playing) { sceKernelDelayThread(100000); continue; }      // durante el video no baja imagenes
    int pick = -1;
    img_lock();
    for (int i = 0; i < IMG_MAX; i++) {
      Img *m = &img_tab[i];
      if (m->state != IM_REQ || img_frame - m->used > 2) continue;  // solo lo que se esta viendo
      if (pick < 0 || m->want > img_tab[pick].want) pick = i;
    }
    if (pick >= 0) {
      img_tab[pick].state = IM_LOADING;
      // version chica (el servidor de imagenes de Pluto acepta w/h)
      snprintf(url, sizeof url, "%s%cw=240&h=240&fit=max", img_tab[pick].url, strchr(img_tab[pick].url, '?') ? '&' : '?');
    }
    img_unlock();
    if (pick < 0) { sceKernelDelayThread(30000); continue; }
    vita2d_texture *t = NULL;
    for (int attempt = 0; attempt < 2 && !t && img_run; attempt++) {
      if (attempt == 1) {                    // sin la version chica, por si el servidor no la acepta
        img_lock(); snprintf(url, sizeof url, "%s", img_tab[pick].url); img_unlock();
      }
      int n = 0;
      uint8_t *d = (uint8_t *)http_req_ex(url, &n, 0, 1);
      if (d && n > 8) {
        if (d[0] == 0x89 && d[1] == 'P' && d[2] == 'N' && d[3] == 'G') t = vita2d_load_PNG_buffer(d);
        else if (d[0] == 0xFF && d[1] == 0xD8) t = vita2d_load_JPEG_buffer(d, n);
      }
      free(d);
    }
    if (t) vita2d_texture_set_filters(t, SCE_GXM_TEXTURE_FILTER_LINEAR, SCE_GXM_TEXTURE_FILTER_LINEAR);
    img_lock();
    img_tab[pick].tex = t;
    img_tab[pick].state = t ? IM_READY : IM_FAIL;
    img_unlock();
  }
  return 0;
}

// Dibuja la textura dentro de la caja (x, y, w, h) sin deformarla
static void draw_fit(vita2d_texture *t, float x, float y, float w, float h) {
  float tw = vita2d_texture_get_width(t), th = vita2d_texture_get_height(t);
  if (tw < 1 || th < 1) return;
  float sc = w / tw < h / th ? w / tw : h / th;
  vita2d_draw_texture_scale(t, x + (w - tw * sc) / 2, y + (h - th * sc) / 2, sc, sc);
}

// Recorta el texto para que quepa en "maxw" pixeles
static const char *fit_text(const char *s, float scale, float maxw, char *buf, int cap) {
  if (vita2d_pgf_text_width(pgf, scale, s) <= maxw) return s;
  snprintf(buf, cap, "%s", s);
  int n = strlen(buf);
  while (n > 0) {
    n--; while (n > 0 && ((unsigned char)buf[n] & 0xC0) == 0x80) n--;   // no partir letras con acento
    buf[n] = 0;
    char t[200]; snprintf(t, sizeof t, "%s...", buf);
    if (vita2d_pgf_text_width(pgf, scale, t) <= maxw) { snprintf(buf, cap, "%s", t); break; }
  }
  return buf;
}

// ---------- Pantalla de lista generica (con buscador) ----------
// Devuelve el indice elegido, o LS_BACK (O), LS_MODE (SELECT), LS_EXIT (START)
enum { LS_BACK = -1, LS_MODE = -2, LS_EXIT = -3, LS_SEARCH = -4 };
typedef struct { int sel, top; char query[128]; } ListState;

// global_search: TRIANGULO no filtra esta lista, devuelve LS_SEARCH para que el llamador busque en todo
// imgs: URL de imagen por elemento (o NULL). logos: 1 = logos de canal (tambien en cada fila), 0 = portadas
static int list_screen_img(const char *title, const char *const *names, const char *const *keys, const char *const *imgs, int logos,
                           int n, ListState *ls, const char *hint, int global_search) {
  int *view = malloc(sizeof(int) * (n > 0 ? n : 1));
  if (!view) return LS_BACK;
  int nview = 0, rebuild = 1, ret = LS_BACK;
  const int rows = 14;
  for (;;) {
    if (rebuild) {
      char q[128], nm[160];
      fold(ls->query, q, sizeof q);
      nview = 0;
      for (int i = 0; i < n; i++) {
        if (q[0]) { fold(keys ? keys[i] : names[i], nm, sizeof nm); if (!strstr(nm, q)) continue; }
        view[nview++] = i;
      }
      if (ls->sel >= nview) ls->sel = nview > 0 ? nview - 1 : 0;
      rebuild = 0;
    }
    sceCtrlPeekBufferPositive(0, &pad, 1);
    unsigned p = pad.buttons & ~oldpad.buttons; oldpad = pad;
    if ((p & SCE_CTRL_DOWN) && ls->sel < nview - 1) ls->sel++;
    if ((p & SCE_CTRL_UP) && ls->sel > 0) ls->sel--;
    if (p & SCE_CTRL_RTRIGGER) ls->sel = ls->sel + rows < nview ? ls->sel + rows : nview - 1;
    if (p & SCE_CTRL_LTRIGGER) ls->sel = ls->sel - rows > 0 ? ls->sel - rows : 0;
    if (ls->sel < 0) ls->sel = 0;
    if (ls->sel < ls->top) ls->top = ls->sel;
    if (ls->sel >= ls->top + rows) ls->top = ls->sel - rows + 1;
    if ((p & SCE_CTRL_CROSS) && nview > 0) { ret = view[ls->sel]; break; }
    if (p & SCE_CTRL_CIRCLE) { ret = LS_BACK; break; }
    if (p & SCE_CTRL_SELECT) { ret = LS_MODE; break; }
    if (p & SCE_CTRL_START) { ret = LS_EXIT; break; }
    if ((p & SCE_CTRL_TRIANGLE) && global_search) { ret = LS_SEARCH; break; }
    if (p & SCE_CTRL_TRIANGLE) { if (ime_search(ls->query, sizeof ls->query)) { ls->sel = ls->top = 0; rebuild = 1; } continue; }
    if ((p & SCE_CTRL_SQUARE) && ls->query[0]) { ls->query[0] = 0; ls->sel = ls->top = 0; rebuild = 1; }

    vita2d_wait_rendering_done();       // la GPU termino el cuadro anterior: ya se pueden liberar imagenes
    img_gc();
    vita2d_start_drawing(); vita2d_clear_screen();
    vita2d_draw_rectangle(0, 0, 960, 50, RGBA8(30,30,120,255));
    vita2d_pgf_draw_text(pgf, 20, 34, RGBA8(255,255,255,255), 1.2f, title);
    char hdr[200];
    if (ls->query[0]) snprintf(hdr, sizeof hdr, "Buscar: %s  (%d)", ls->query, nview);
    else snprintf(hdr, sizeof hdr, "%d", n);
    vita2d_pgf_draw_text(pgf, 960 - 20 - vita2d_pgf_text_width(pgf, 1.0f, hdr), 34, RGBA8(255,230,120,255), 1.0f, hdr);
    float listw = imgs ? 600 : 940, tx = (imgs && logos) ? 78 : 24;
    char cut[200];
    for (int i = 0; i < rows && ls->top + i < nview; i++) {
      int y = 66 + i * 31, idx = ls->top + i;
      if (idx == ls->sel) vita2d_draw_rectangle(10, y - 4, listw, 30, RGBA8(70,70,200,255));
      if (imgs && logos) {                                   // logo chico en cada fila
        vita2d_texture *t = img_get(imgs[view[idx]]);
        if (t) draw_fit(t, 16, y - 3, 54, 28);
      }
      vita2d_pgf_draw_text(pgf, tx, y + 18, RGBA8(255,255,255,255), 1.0f,
                           fit_text(names[view[idx]], 1.0f, listw - tx, cut, sizeof cut));
    }
    if (imgs && nview > 0) {                                 // imagen grande del seleccionado
      vita2d_draw_rectangle(625, 62, 320, 432, RGBA8(25,25,45,255));
      vita2d_texture *t = img_get(imgs[view[ls->sel]]);
      if (t) draw_fit(t, 635, 72, 300, logos ? 220 : 412);
      else vita2d_pgf_draw_text(pgf, 700, 270, RGBA8(120,120,150,255), 1.0f,
                                imgs[view[ls->sel]] && imgs[view[ls->sel]][0] ? "Cargando imagen..." : "Sin imagen");
      if (logos) vita2d_pgf_draw_text(pgf, 640, 330, RGBA8(255,255,255,255), 1.0f,
                                      fit_text(names[view[ls->sel]], 1.0f, 295, cut, sizeof cut));
    }
    if (nview == 0) vita2d_pgf_draw_text(pgf, 24, 100, RGBA8(255,200,200,255), 1.0f,
                                         ls->query[0] ? "Sin resultados. CUADRADO: ver todos" : "Lista vacia");
    vita2d_pgf_draw_text(pgf, 20, 512, RGBA8(180,180,180,255), 0.85f, hint);
    vita2d_pgf_draw_text(pgf, 20, 536, RGBA8(180,180,180,255), 0.85f,
                         ls->query[0] ? "TRIANGULO: buscar   CUADRADO: ver todos   L/R: pagina   START: salir"
                                      : "TRIANGULO: buscar   L/R: pagina   START: salir");
    vita2d_end_drawing(); vita2d_swap_buffers();
  }
  free(view);
  return ret;
}
static int list_screen_ex(const char *title, const char *const *names, const char *const *keys, int n, ListState *ls, const char *hint, int global_search) {
  return list_screen_img(title, names, keys, NULL, 0, n, ls, hint, global_search);
}
static int list_screen(const char *title, const char *const *names, int n, ListState *ls, const char *hint) {
  return list_screen_ex(title, names, NULL, n, ls, hint, 0);
}

static void show_error(const char *what) {
  char m[220];
  snprintf(m, sizeof m, "%s: http %d  curl %d  (O = volver)", what, g_status, g_err);
  for (;;) {
    sceCtrlPeekBufferPositive(0, &pad, 1);
    unsigned p = pad.buttons & ~oldpad.buttons; oldpad = pad;
    if (p & (SCE_CTRL_CIRCLE | SCE_CTRL_CROSS)) break;
    status(m);
  }
}

// ---------- JSON minimo (recorre el texto sin copiarlo) ----------
static const char *jws(const char *p) { while (p && (*p == ' ' || *p == '\n' || *p == '\r' || *p == '\t')) p++; return p; }

static const char *jskip(const char *p) {          // salta un valor completo
  p = jws(p);
  if (!p || !*p) return NULL;
  if (*p == '"') { p++; while (*p && *p != '"') { if (*p == '\\' && p[1]) p++; p++; } return *p ? p + 1 : NULL; }
  if (*p == '{' || *p == '[') {
    int depth = 0;
    while (*p) {
      if (*p == '"') { p++; while (*p && *p != '"') { if (*p == '\\' && p[1]) p++; p++; } if (!*p) return NULL; }
      else if (*p == '{' || *p == '[') depth++;
      else if (*p == '}' || *p == ']') { if (--depth == 0) return p + 1; }
      p++;
    }
    return NULL;
  }
  while (*p && *p != ',' && *p != '}' && *p != ']' && *p != ' ' && *p != '\n' && *p != '\r' && *p != '\t') p++;
  return p;
}

// valor de "key" dentro del objeto que empieza en p (solo hijos directos)
static const char *jget(const char *p, const char *key) {
  p = jws(p);
  if (!p || *p != '{') return NULL;
  int kl = strlen(key);
  p++;
  for (;;) {
    p = jws(p);
    if (!p || *p != '"') return NULL;
    const char *k = p + 1;
    const char *ke = jskip(p);
    if (!ke) return NULL;
    int match = (ke - 1 - k) == kl && !strncmp(k, key, kl);
    p = jws(ke);
    if (!p || *p != ':') return NULL;
    p = jws(p + 1);
    if (match) return p;
    p = jws(jskip(p));
    if (!p || *p != ',') return NULL;
    p++;
  }
}

// busca "key" a cualquier profundidad (primer resultado cuyo valor sea del tipo pedido: '[' '{' o 0 = cualquiera)
static const char *jfind(const char *p, const char *key, char want, int depth) {
  p = jws(p);
  if (!p || depth > 8) return NULL;
  if (*p == '{') {
    const char *v = jget(p, key);
    if (v && (!want || *v == want)) return v;
    p++;
    for (;;) {
      p = jws(p);
      if (!p || *p != '"') return NULL;
      p = jws(jskip(p)); if (!p || *p != ':') return NULL;
      p = jws(p + 1);
      const char *r = jfind(p, key, want, depth + 1);
      if (r) return r;
      p = jws(jskip(p));
      if (!p || *p != ',') return NULL;
      p++;
    }
  }
  if (*p == '[') {
    p = jws(p + 1);
    while (p && *p && *p != ']') {
      const char *r = jfind(p, key, want, depth + 1);
      if (r) return r;
      p = jws(jskip(p));
      if (!p || *p != ',') break;
      p = jws(p + 1);
    }
  }
  return NULL;
}

static const char *jarr_first(const char *p) { p = jws(p); if (!p || *p != '[') return NULL; p = jws(p + 1); return (p && *p && *p != ']') ? p : NULL; }
static const char *jarr_next(const char *p) { p = jws(jskip(p)); if (!p || *p != ',') return NULL; p = jws(p + 1); return (p && *p && *p != ']') ? p : NULL; }

// copia el texto (o numero) de un valor
static void jstr(const char *v, char *dst, int cap) {
  dst[0] = 0;
  v = jws(v);
  if (!v) return;
  if (*v == '"') { copy_json(v + 1, dst, cap); return; }
  int i = 0;
  while (*v && *v != ',' && *v != '}' && *v != ']' && i < cap - 1) dst[i++] = *v++;
  dst[i] = 0;
}
static void jfield(const char *obj, const char *k1, const char *k2, char *dst, int cap) {
  const char *v = jget(obj, k1);
  if (!v && k2) v = jget(obj, k2);
  if (v) jstr(v, dst, cap); else dst[0] = 0;
}

// ---------- Catalogo a la carta ----------
typedef struct { char id[40]; char name[104]; char title[96]; char img[224]; int kind; } Entry;   // kind: 0 categoria, 1 pelicula, 2 serie, 3 episodio
// name = lo que se muestra ("[Serie] X"); title = solo el titulo (con eso se busca)
typedef struct { Entry *e; const char **names, **keys, **imgs; int n, cap; } EntryList;

static void el_free(EntryList *l) { free(l->e); free(l->names); free(l->keys); free(l->imgs); memset(l, 0, sizeof *l); }
static Entry *el_add(EntryList *l) {
  if (l->n == l->cap) {
    int nc = l->cap ? l->cap * 2 : 64;
    Entry *ne = realloc(l->e, sizeof(Entry) * nc);
    if (!ne) return NULL;
    l->e = ne; l->cap = nc;
  }
  memset(&l->e[l->n], 0, sizeof(Entry));
  return &l->e[l->n++];
}
static void el_names(EntryList *l) {
  free(l->names); free(l->keys); free(l->imgs);
  l->names = malloc(sizeof(char *) * (l->n > 0 ? l->n : 1));
  l->keys  = malloc(sizeof(char *) * (l->n > 0 ? l->n : 1));
  l->imgs  = malloc(sizeof(char *) * (l->n > 0 ? l->n : 1));
  if (l->imgs)  for (int i = 0; i < l->n; i++) l->imgs[i] = l->e[i].img;
  if (l->names) for (int i = 0; i < l->n; i++) l->names[i] = l->e[i].name;
  if (l->keys)  for (int i = 0; i < l->n; i++) l->keys[i] = l->e[i].title[0] ? l->e[i].title : l->e[i].name;
}

// arreglo de objetos: el de la clave pedida, o el documento si ya es un arreglo
static const char *find_list(const char *doc, const char *key) {
  const char *p = jws(doc);
  if (p && *p == '[') return p;
  return jfind(doc, key, '[', 0);
}

// Portada de un titulo: covers (prefiere la vertical 347:500), luego poster/featuredImage/tile, luego images
static void find_cover(const char *obj, char *out, int cap) {
  out[0] = 0;
  if (!obj) return;
  const char *cv = jget(obj, "covers");
  if (cv && *jws(cv) == '[') {
    for (const char *c = jarr_first(cv); c; c = jarr_next(c)) {
      if (*jws(c) != '{') continue;
      char ar[24], u[224];
      jfield(c, "aspectRatio", NULL, ar, sizeof ar);
      jfield(c, "url", "path", u, sizeof u);
      if (!u[0]) continue;
      if (!out[0] || !strcmp(ar, "347:500")) snprintf(out, cap, "%s", u);
      if (!strcmp(ar, "347:500")) return;
    }
    if (out[0]) return;
  }
  const char *keys[] = { "poster", "featuredImage", "tile", "featuredImageMobile" };
  for (int k = 0; k < 4; k++) {
    const char *o = jget(obj, keys[k]);
    if (o && *jws(o) == '{') { jfield(o, "path", "url", out, cap); if (out[0]) return; }
    if (o && *jws(o) == '"') { jstr(o, out, cap); if (out[0]) return; }
  }
  const char *im = jget(obj, "images");
  if (im && *jws(im) == '[') {
    for (const char *c = jarr_first(im); c; c = jarr_next(c)) {
      if (*jws(c) != '{') continue;
      char u[224]; jfield(c, "url", "path", u, sizeof u);
      if (u[0]) { snprintf(out, cap, "%s", u); return; }
    }
  }
}

static int el_has(const EntryList *l, const char *id) {
  for (int i = 0; i < l->n; i++) if (!strcmp(l->e[i].id, id)) return 1;
  return 0;
}

// Solo peliculas y series (por titulo). Si la categoria trae un capitulo suelto, se agrega su serie.
static void add_items(EntryList *l, const char *arr) {
  for (const char *it = jarr_first(arr); it; it = jarr_next(it)) {
    if (*jws(it) != '{') continue;
    char type[24], id[40], title[96], img[224];
    jfield(it, "type", NULL, type, sizeof type);
    int kind;
    const char *src = it;                                         // de donde sale la portada
    if (!strcmp(type, "series")) {
      kind = 2;
      jfield(it, "_id", "id", id, sizeof id);
      jfield(it, "name", "title", title, sizeof title);
    } else if (!strcmp(type, "movie") || !type[0]) {
      kind = 1;
      jfield(it, "_id", "id", id, sizeof id);
      jfield(it, "name", "title", title, sizeof title);
    } else if (!strcmp(type, "episode")) {
      const char *ser = jget(it, "series");                       // datos de su serie, si vienen
      if (!ser || *jws(ser) != '{') continue;
      kind = 2; src = ser;
      jfield(ser, "_id", "id", id, sizeof id);
      jfield(ser, "name", "title", title, sizeof title);
    } else continue;                                              // clips, avances, etc.
    if (!id[0] || !title[0] || el_has(l, id)) continue;
    find_cover(src, img, sizeof img);
    Entry *e = el_add(l); if (!e) break;
    snprintf(e->img, sizeof e->img, "%s", img);
    snprintf(e->id, sizeof e->id, "%s", id);
    snprintf(e->title, sizeof e->title, "%s", title);
    if (kind == 2) snprintf(e->name, sizeof e->name, "[Serie] %s", title);
    else snprintf(e->name, sizeof e->name, "%s", title);
    e->kind = kind;
  }
}

static char *vod_doc;            // respuesta de categorias (se guarda: en v3 trae las peliculas dentro)
static EntryList vod_cats;
static int vod_v3;

static int load_categories(void) {
  if (vod_cats.n) return 0;
  status("Descargando catalogo...");
  vod_v3 = 0;
  vod_doc = http_req(VOD_CATS_V4, NULL, 1);
  const char *arr = vod_doc ? find_list(vod_doc, "categories") : NULL;
  if (!arr) {                                     // respaldo: API v3
    free(vod_doc);
    vod_doc = http_req(VOD_CATS_V3, NULL, 0);
    arr = vod_doc ? find_list(vod_doc, "categories") : NULL;
    vod_v3 = 1;
  }
  if (!arr) { free(vod_doc); vod_doc = NULL; return -1; }
  for (const char *c = jarr_first(arr); c; c = jarr_next(c)) {
    if (*jws(c) != '{') continue;
    Entry *e = el_add(&vod_cats); if (!e) break;
    jfield(c, "_id", "id", e->id, sizeof e->id);
    jfield(c, "name", "title", e->name, sizeof e->name);
    e->kind = 0;
    if (!e->id[0] || !e->name[0]) vod_cats.n--;
  }
  el_names(&vod_cats);
  return vod_cats.n ? 0 : -1;
}

// Peliculas y series de una categoria
static int load_items(int ci, EntryList *out, int quiet) {
  memset(out, 0, sizeof *out);
  const char *arr = NULL;
  // en v3 las peliculas vienen dentro de la categoria
  if (vod_doc) {
    const char *cats = find_list(vod_doc, "categories");
    for (const char *c = jarr_first(cats); c; c = jarr_next(c)) {
      if (*jws(c) != '{') continue;
      char id[40]; jfield(c, "_id", "id", id, sizeof id);
      if (!strcmp(id, vod_cats.e[ci].id)) { const char *it = jget(c, "items"); if (it && *jws(it) == '[') arr = it; break; }
    }
  }
  if (arr) { add_items(out, arr); el_names(out); return out->n ? 0 : -1; }
  if (!quiet) status("Descargando titulos...");
  char url[512]; snprintf(url, sizeof url, VOD_ITEMS_V4, vod_cats.e[ci].id);
  char *doc = http_req(url, NULL, 1);
  if (!doc) return -1;
  arr = find_list(doc, "items");
  if (arr) add_items(out, arr);
  free(doc);
  el_names(out);
  return out->n ? 0 : -1;
}

// Episodios de una serie (todas las temporadas, "T1 E3 - Nombre")
static int load_episodes(const char *series_id, EntryList *out) {
  memset(out, 0, sizeof *out);
  status("Descargando episodios...");
  char url[512]; snprintf(url, sizeof url, VOD_SEASONS_V4, series_id);
  char *doc = http_req(url, NULL, 1);
  const char *seasons = doc ? find_list(doc, "seasons") : NULL;
  if (!seasons) {
    free(doc);
    snprintf(url, sizeof url, VOD_SEASONS_V3, series_id);
    doc = http_req(url, NULL, 0);
    seasons = doc ? find_list(doc, "seasons") : NULL;
  }
  if (!seasons) { free(doc); return -1; }
  for (const char *se = jarr_first(seasons); se; se = jarr_next(se)) {
    if (*jws(se) != '{') continue;
    char snum[16]; jfield(se, "number", NULL, snum, sizeof snum);
    const char *eps = jget(se, "episodes");
    for (const char *ep = jarr_first(eps); ep; ep = jarr_next(ep)) {
      if (*jws(ep) != '{') continue;
      Entry *e = el_add(out); if (!e) break;
      char nm[96], en[16];
      jfield(ep, "_id", "id", e->id, sizeof e->id);
      jfield(ep, "name", "title", nm, sizeof nm);
      jfield(ep, "number", NULL, en, sizeof en);
      snprintf(e->name, sizeof e->name, "T%s E%s - %s", snum[0] ? snum : "?", en[0] ? en : "?", nm);
      e->kind = 3;
      if (!e->id[0]) out->n--;
    }
  }
  free(doc);
  el_names(out);
  return out->n ? 0 : -1;
}

// Abre un titulo: pelicula -> reproduce; serie -> lista de episodios. Devuelve 0, LS_MODE o LS_EXIT.
static int open_item(const Entry *it) {
  if (it->kind == 1) { play_stream("episode", it->id); return 0; }   // las peliculas tambien van por "episode"
  EntryList eps; ListState ep_ls; memset(&ep_ls, 0, sizeof ep_ls);
  char sid_copy[40], t2[160];
  snprintf(sid_copy, sizeof sid_copy, "%s", it->id);
  snprintf(t2, sizeof t2, "%s", it->name);
  if (load_episodes(sid_copy, &eps) < 0) { el_free(&eps); show_error("No se pudieron bajar los episodios"); return 0; }
  int r = 0;
  for (;;) {
    int ei = list_screen(t2, eps.names, eps.n, &ep_ls, "X: ver   O: volver   SELECT: en vivo");
    if (ei == LS_MODE || ei == LS_EXIT) { r = ei; break; }
    if (ei == LS_BACK) break;
    play_stream("episode", eps.e[ei].id);
  }
  el_free(&eps);
  return r;
}

// ---- Indice de todos los titulos (para buscar desde las categorias) ----
static EntryList all_items;
static int all_done;             // ya se recorrieron todas las categorias
static int all_next;             // siguiente categoria por recorrer (si se cancelo a medias)
#define IDX_HASH 16384
static int *all_hash;            // ids ya vistos (sin repetir titulos que estan en varias categorias)

static unsigned str_hash(const char *s) { unsigned h = 2166136261u; while (*s) h = (h ^ (unsigned char)*s++) * 16777619u; return h; }
static int seen_or_add(const char *id, int idx) {
  if (!all_hash) { all_hash = malloc(sizeof(int) * IDX_HASH); if (!all_hash) return 0; for (int i = 0; i < IDX_HASH; i++) all_hash[i] = -1; }
  unsigned h = str_hash(id) & (IDX_HASH - 1);
  for (int k = 0; k < IDX_HASH; k++, h = (h + 1) & (IDX_HASH - 1)) {
    if (all_hash[h] < 0) { all_hash[h] = idx; return 0; }
    if (!strcmp(all_items.e[all_hash[h]].id, id)) return 1;
  }
  return 1;                      // tabla llena: lo trata como repetido
}

// Recorre las categorias que falten. Devuelve 0 si termino, 1 si el usuario cancelo con O.
static int build_index(void) {
  while (!all_done) {
    if (all_next >= vod_cats.n) { all_done = 1; break; }
    sceCtrlPeekBufferPositive(0, &pad, 1);
    if (pad.buttons & SCE_CTRL_CIRCLE) { oldpad = pad; el_names(&all_items); return 1; }
    char m[200];
    snprintf(m, sizeof m, "Buscando en el catalogo... %d/%d  (O = cancelar)", all_next + 1, vod_cats.n);
    status(m);
    EntryList tmp;
    if (load_items(all_next, &tmp, 1) == 0) {
      for (int i = 0; i < tmp.n; i++) {
        int idx = all_items.n;
        Entry *e = el_add(&all_items); if (!e) break;
        *e = tmp.e[i];
        if (seen_or_add(e->id, idx)) all_items.n--;
      }
    }
    el_free(&tmp);
    all_next++;
  }
  el_names(&all_items);
  return 0;
}

// Busca peliculas y series en todo el catalogo. Devuelve 0, LS_MODE o LS_EXIT.
static int global_search(void) {
  static ListState res_ls;
  char q[128]; snprintf(q, sizeof q, "%s", res_ls.query);
  if (!ime_search(q, sizeof q) || !q[0]) return 0;
  int cancelled = build_index();
  snprintf(res_ls.query, sizeof res_ls.query, "%s", q);
  res_ls.sel = res_ls.top = 0;
  for (;;) {
    int r = list_screen_img("Buscar pelicula o serie", all_items.names, all_items.keys, all_items.imgs, 0, all_items.n, &res_ls,
                           cancelled ? "Busqueda parcial (se cancelo el recorrido)   X: ver / abrir   O: categorias"
                                     : "X: ver / abrir serie   O: categorias   SELECT: en vivo", 0);
    if (r == LS_MODE || r == LS_EXIT) return r;
    if (r == LS_BACK) return 0;
    Entry it = all_items.e[r];          // copia: el indice no cambia mientras tanto, pero por si acaso
    int o = open_item(&it);
    if (o) return o;
  }
}

// Navegador: categorias -> titulos -> (serie) episodios. Devuelve LS_MODE o LS_EXIT.
static int vod_browse(void) {
  static ListState cat_ls;
  if (load_categories() < 0) { show_error("No se pudo bajar el catalogo"); return LS_MODE; }
  for (;;) {
    int ci = list_screen_ex("A la carta: categorias", vod_cats.names, NULL, vod_cats.n, &cat_ls,
                            "X: abrir   TRIANGULO: buscar pelicula o serie   SELECT: en vivo", 1);
    if (ci == LS_MODE || ci == LS_EXIT) return ci;
    if (ci == LS_BACK) return LS_MODE;
    if (ci == LS_SEARCH) { int g = global_search(); if (g) return g; continue; }
    EntryList items; ListState item_ls; memset(&item_ls, 0, sizeof item_ls);
    if (load_items(ci, &items, 0) < 0) { el_free(&items); show_error("Categoria vacia o sin acceso"); continue; }
    char title[160]; snprintf(title, sizeof title, "A la carta: %s", vod_cats.e[ci].name);
    for (;;) {
      int ii = list_screen_img(title, items.names, items.keys, items.imgs, 0, items.n, &item_ls, "X: ver / abrir serie   O: categorias   SELECT: en vivo", 0);
      if (ii == LS_MODE || ii == LS_EXIT) { el_free(&items); return ii; }
      if (ii == LS_BACK) break;
      Entry it = items.e[ii];
      int o = open_item(&it);
      if (o) { el_free(&items); return o; }
    }
    el_free(&items);
  }
}

// ---------- Main ----------
int main(void) {
  sceSysmoduleLoadModule(SCE_SYSMODULE_NET);
  static char netmem[1024 * 1024];
  SceNetInitParam np = { netmem, sizeof netmem, 0 };
  sceNetInit(&np); sceNetCtlInit();
  curl_global_init(CURL_GLOBAL_DEFAULT);
  {
    SceAppUtilInitParam aip; SceAppUtilBootParam abp;
    memset(&aip, 0, sizeof aip); memset(&abp, 0, sizeof abp);
    sceAppUtilInit(&aip, &abp);                 // necesario para el teclado (dialogo comun)
  }

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

  static const char *chan_names[MAX_CH], *chan_logos[MAX_CH];
  for (int i = 0; i < nchans; i++) { chan_names[i] = chans[i].name; chan_logos[i] = chans[i].logo; }
  img_mtx = sceKernelCreateMutex("pv_img", 0, 0, NULL);
  img_run = 1;
  SceUID th_img = sceKernelCreateThread("pv_img", img_thread, 0x10000100, 256 * 1024, 0, 0, NULL);
  sceKernelStartThread(th_img, 0, NULL);
  static ListState live_ls;
  int mode = 0;                                  // 0 en vivo, 1 a la carta
  for (;;) {
    int r;
    if (mode == 0) {
      r = list_screen_img("Pluto TV: en vivo", chan_names, NULL, chan_logos, 1, nchans, &live_ls, "X: ver   SELECT: peliculas y series", 0);
      if (r >= 0) { play_stream("channel", chans[r].id); continue; }
      if (r == LS_MODE) mode = 1;
    } else {
      r = vod_browse();
      if (r == LS_MODE) mode = 0;
    }
    if (r == LS_EXIT) break;
  }
  img_run = 0;
  sceKernelWaitThreadEnd(th_img, NULL, NULL);
out:
  vita2d_fini();
  curl_global_cleanup(); sceNetCtlTerm(); sceNetTerm();
  sceKernelExitProcess(0);
  return 0;
}
