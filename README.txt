PlutoVita - Pluto TV no oficial para PS Vita liberada (HENkaku/Enso)

Compilar (necesitas VitaSDK):
  mkdir build && cd build
  cmake .. && make
Resultado: build/PlutoVita.vpk -> instalalo con VitaShell (usa "Unsafe homebrew" activado).

Controles: Arriba/Abajo elegir, X ver canal, O volver, L/R pagina, START salir.

Si algo falla, los endpoints estan arriba en src/main.c (BOOT_URL, CHANNELS_URL, STITCH_URL).
