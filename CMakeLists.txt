cmake_minimum_required(VERSION 3.5)
if(NOT DEFINED CMAKE_TOOLCHAIN_FILE)
  if(DEFINED ENV{VITASDK})
    set(CMAKE_TOOLCHAIN_FILE "$ENV{VITASDK}/share/vita.toolchain.cmake" CACHE PATH "toolchain file")
  else()
    message(FATAL_ERROR "Define la variable VITASDK")
  endif()
endif()

project(PlutoVita C)
include("$ENV{VITASDK}/share/vita.cmake" REQUIRED)

set(VITA_APP_NAME "Pluto TV")
set(VITA_TITLEID  "PLUT00001")
set(VITA_VERSION  "01.00")

set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wl,-q -Wall -O2 -std=gnu99")

add_executable(${PROJECT_NAME} src/main.c)

target_link_libraries(${PROJECT_NAME}
  vita2d freetype png jpeg z m c
  SceDisplay_stub SceGxm_stub SceCtrl_stub SceSysmodule_stub
  ScePgf_stub ScePvf_stub SceCommonDialog_stub
  SceNet_stub SceNetCtl_stub SceHttp_stub SceSsl_stub
  SceAvPlayer_stub SceAudio_stub SceAppUtil_stub
  SceAppMgr_stub SceLibKernel_stub
)

vita_create_self(${PROJECT_NAME}.self ${PROJECT_NAME} UNSAFE)
vita_create_vpk(${PROJECT_NAME}.vpk ${VITA_TITLEID} ${PROJECT_NAME}.self
  VERSION ${VITA_VERSION}
  NAME ${VITA_APP_NAME}
)
