#!/usr/bin/env bash
set -Eeuxo pipefail

DATE=$(date "+%Y-%m-%d")
[[ "$RUNNER_OS" == 'Windows' ]] && IS_WIN=true || IS_WIN=false
BIN=bin
EXT=""
$IS_WIN && EXT=".exe"
mkdir -p "$BIN"

is_exe() { [[ -x "$1/$2$EXT" ]] || command -v "$2" > /dev/null 2>&1; }

install_solvers() {
  (cd $BIN && curl -o bins.zip -sL "https://github.com/GaloisInc/what4-solvers/releases/download/$SOLVER_PKG_VERSION/$BUILD_TARGET_OS-$BUILD_TARGET_ARCH-bin.zip" && unzip -o bins.zip && rm bins.zip)
  cp $BIN/yices_smt2$EXT $BIN/yices-smt2$EXT
  chmod +x $BIN/*
}

install_system_deps() {
  install_solvers
  export PATH=$PWD/$BIN:$PATH
  echo "$PWD/$BIN" >> $GITHUB_PATH
  is_exe "$BIN" boolector && \
    is_exe "$BIN" bitwuzla && \
    is_exe "$BIN" cvc4 && \
    is_exe "$BIN" cvc5 && \
    is_exe "$BIN" yices && \
    is_exe "$BIN" z3
}

COMMAND="$1"
shift

"$COMMAND" "$@"
