// PlutoVita - cliente no oficial de Pluto TV para PS Vita (homebrew)
// Sin dependencias externas: sceHttp + sceAvPlayer + vita2d.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <malloc.h>
#include <psp2/kernel/processmgr.h>
#include <psp2/kernel/threadmgr.h>
#include <psp2/sysmodule.h>
#include <psp2/net/net.h>
#include <psp2/net/netctl.h>
#include <psp2/net/http.h>
#include <psp2/ctrl.h>
#include <psp2/audioout.h>
#include <psp2/avplayer.h>
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
  "&deviceModel=web&deviceType=web&deviceVersion=122.0.0&serverSideAds=false&sid=%s&jwt=%s"

#define MAX_CH 800
typedef struct { char id[40]; char name[64]; } Channel;
static Channel chans[MAX_CH];
static int nchans = 0;
static char uuid[40], sid[40], jwt[2048];

static vita2d_pgf *pgf;
static SceCtrlData pad, oldpad;

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

// ---------- HTTP ----------
static int g_step = 0, g_err = 0, g_status = 0;

static char *http_get(const char *url, int *outlen) {
  g_step = 1; g_err = 0; g_status = 0;
  int tpl = sceHttpCreateTemplate("Mozilla/5.0 PlutoVita", SCE_HTTP_VERSION_1_1, 1);
  if (tpl < 0) { g_err = tpl; return NULL; }
  sceHttpsDisableOption(SCE_HTTPS_FLAG_SERVER_VERIFY); // sin CA certs en Vita
  g_step = 2;
  int conn = sceHttpCreateConnectionWithURL(tpl, url, 0);
  if (conn < 0) g_err = conn;
  g_step = 3;
  int req  = conn >= 0 ? sceHttpCreateRequestWithURL(conn, SCE_HTTP_METHOD_GET, url, 0) : -1;
  if (req < 0 && conn >= 0) g_err = req;
  char *buf = NULL; int len = 0;
  if (req >= 0) {
    g_step = 4;
    int sr = sceHttpSendRequest(req, NULL, 0);
    if (sr < 0) g_err = sr;
    else {
      g_step = 5;
      sceHttpGetStatusCode(req, &g_status);
      int cap = 256 * 1024; buf = malloc(cap);
      int n;
      while (buf && (n = sceHttpReadData(req, buf + len, cap - len - 1)) > 0) {
        len += n;
        if (cap - len < 16 * 1024) {
          if (cap >= 8 * 1024 * 1024) break;
          cap *= 2; char *nb = realloc(buf, cap);
          if (!nb) { free(buf); buf = NULL; len = 0; break; }
          buf = nb;
        }
      }
      if (buf) buf[len] = 0;
    }
  }
  if (req >= 0) sceHttpDeleteRequest(req);
  if (conn >= 0) sceHttpDeleteConnection(conn);
  sceHttpDeleteTemplate(tpl);
  if (outlen) *outlen = len;
  return buf;
}

static int copy_str(const char *p, char *dst, int max) { // copia hasta la comilla
  int i = 0; while (*p && *p != '"' && i < max - 1) dst[i++] = *p++;
  dst[i] = 0; return i;
}

static int get_session(void) {
  char url[1024]; snprintf(url, sizeof url, BOOT_URL, uuid);
  char *r = http_get(url, NULL); if (!r) return -1;
  char *t = strstr(r, "\"sessionToken\":\"");
  int ok = -1;
  if (t) { copy_str(t + 16, jwt, sizeof jwt); ok = jwt[0] ? 0 : -1; }
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

// ---------- Reproductor ----------
static void *a_alloc(void *o, uint32_t al, uint32_t sz) { return memalign(al, sz); }
static void  a_free (void *o, void *p) { free(p); }

static volatile int playing;
static SceAvPlayerHandle player;
static int audio_port = -1;

static int audio_thread(SceSize a, void *u) {
  SceAvPlayerFrameInfo f;
  while (playing) {
    if (sceAvPlayerIsActive(player) && sceAvPlayerGetAudioData(player, &f)) {
      if (audio_port < 0) {
        int mode = f.details.audio.channelCount == 1 ? SCE_AUDIO_OUT_MODE_MONO : SCE_AUDIO_OUT_MODE_STEREO;
        audio_port = sceAudioOutOpenPort(SCE_AUDIO_OUT_PORT_TYPE_MAIN, 1024, f.details.audio.sampleRate, mode);
      }
      if (audio_port >= 0) sceAudioOutOutput(audio_port, f.pData);
    } else sceKernelDelayThread(5000);
  }
  if (audio_port >= 0) { sceAudioOutReleasePort(audio_port); audio_port = -1; }
  return 0;
}

static void play_channel(const Channel *c) {
  char url[4096];
  snprintf(url, sizeof url, STITCH_URL, c->id, uuid, sid, jwt);
  status("Cargando canal...");

  SceAvPlayerInitData init; memset(&init, 0, sizeof init);
  init.memoryReplacement.allocate = a_alloc;
  init.memoryReplacement.deallocate = a_free;
  init.memoryReplacement.allocateTexture = a_alloc;
  init.memoryReplacement.deallocateTexture = a_free;
  init.basePriority = 0xA0;
  init.numOutputVideoFrameBuffers = 5;
  init.autoStart = 1;
  player = sceAvPlayerInit(&init);
  sceAvPlayerAddSource(player, url);

  playing = 1;
  SceUID th = sceKernelCreateThread("pluto_audio", audio_thread, 0x10000100, 0x10000, 0, 0, NULL);
  sceKernelStartThread(th, 0, NULL);

  vita2d_texture *tex = NULL; int tw = 0, thh = 0;
  SceAvPlayerFrameInfo f;
  while (playing) {
    sceCtrlPeekBufferPositive(0, &pad, 1);
    if ((pad.buttons & SCE_CTRL_CIRCLE) && !(oldpad.buttons & SCE_CTRL_CIRCLE)) playing = 0;
    oldpad = pad;

    if (sceAvPlayerIsActive(player) && sceAvPlayerGetVideoData(player, &f)) {
      int w = f.details.video.width, h = f.details.video.height;
      if (!tex || w != tw || h != thh) {
        if (tex) vita2d_free_texture(tex);
        tex = vita2d_create_empty_texture_format(w, h, SCE_GXM_TEXTURE_FORMAT_YVU420P2_CSC1);
        tw = w; thh = h;
      }
      memcpy(vita2d_texture_get_datap(tex), f.pData, (size_t)w * h * 3 / 2);
    }
    vita2d_start_drawing(); vita2d_clear_screen();
    if (tex) vita2d_draw_texture_scale(tex, 0, 0, 960.0f / tw, 544.0f / thh);
    else vita2d_pgf_draw_text(pgf, 40, 270, RGBA8(255,255,255,255), 1.2f, "Buffering...  (O = volver)");
    vita2d_end_drawing(); vita2d_swap_buffers();
  }
  sceKernelWaitThreadEnd(th, NULL, NULL);
  sceKernelDeleteThread(th);
  sceAvPlayerStop(player); sceAvPlayerClose(player);
  if (tex) { vita2d_wait_rendering_done(); vita2d_free_texture(tex); }
}

// ---------- Main ----------
int main(void) {
  sceSysmoduleLoadModule(SCE_SYSMODULE_NET);
  sceSysmoduleLoadModule(SCE_SYSMODULE_HTTPS);
  static char netmem[1024 * 1024];
  SceNetInitParam np = { netmem, sizeof netmem, 0 };
  sceNetInit(&np); sceNetCtlInit();
  sceHttpInit(1024 * 1024);

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
  sceHttpTerm(); sceNetCtlTerm(); sceNetTerm();
  sceKernelExitProcess(0);
  return 0;
}
