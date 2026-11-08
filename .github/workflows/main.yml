name: build
on: [push, workflow_dispatch]
jobs:
  build:
    runs-on: ubuntu-latest
    container: vitasdk/vitasdk:latest
    steps:
      - uses: actions/checkout@v4
      - run: mkdir build && cd build && cmake .. && make
      - uses: actions/upload-artifact@v4
        with:
          name: PlutoVita
          path: build/PlutoVita.vpk
