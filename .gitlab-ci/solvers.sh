#!/usr/bin/env bash
set -Eeuxo pipefail

DATE=$(date "+%Y-%m-%d")
[[ "$RUNNER_OS" == 'Windows' ]] && IS_WIN=true || IS_WIN=false
BIN=bin
EXT=""
$IS_WIN && EXT=".exe"
mkdir -p "$BIN"

is_exe() { [[ -x "$1/$2$EXT" ]] || command -v "$2" > /dev/null 2>&1; }

extract_exe() {
    exe="$(cabal v2-exec which "$1$EXT" | tail -1)"
    name="$(basename "$exe")"
    echo "Copying $name to $2"
    mkdir -p "$2"
    cp -f "$exe" "$2/$name"
    $IS_WIN || chmod +x "$2/$name"
}

retry() {
    echo "Attempting with retry:" "$@"
    local n=1
    while true; do
        if "$@"; then
            break
        else
            if [[ $n -lt 3 ]]; then
                sleep $n # don't retry immediately
                ((n++))
                echo "Command failed. Attempt $n/3:"
            else
                echo "The command has failed after $n attempts."
                return 1
            fi
        fi
    done
}

install_system_deps() {
  (cd $BIN && curl -o bins.zip -sL "https://github.com/GaloisInc/what4-solvers/releases/download/$SOLVER_PKG_VERSION/$BUILD_TARGET_OS-bin.zip" && unzip -o bins.zip && rm bins.zip)
  chmod +x $BIN/*
  cp $BIN/yices_smt2$EXT $BIN/yices-smt2$EXT
  export PATH="$BIN:$PATH"
  is_exe "$BIN" z3 && is_exe "$BIN" cvc4 && is_exe "$BIN" yices
}


COMMAND="$1"
shift

"$COMMAND" "$@"
