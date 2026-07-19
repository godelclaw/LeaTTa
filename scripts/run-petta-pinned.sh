#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0

set -euo pipefail

if [[ $# -lt 1 ]]; then
  echo "usage: run-petta-pinned.sh PROGRAM.metta [PeTTa arguments...]" >&2
  exit 2
fi

PETTA_DIR="${PETTA_DIR:-$HOME/repos/PeTTa}"
PETTA_ORACLE_REV="${PETTA_ORACLE_REV:-6b7f52f064bdbc82fabd0a0998404121fb01d52e}"
CACHE_ROOT="${PLEATTA_CACHE_DIR:-${XDG_CACHE_HOME:-$HOME/.cache}/pleatta}"
CLEAN_ROOT="$CACHE_ROOT/petta-$PETTA_ORACLE_REV"
PROGRAM="$(readlink -f "$1")"
shift

PETTA_OWNER_HOME="$(dirname "$(dirname "$PETTA_DIR")")"
PETTA_PYTHONHOME="${PETTA_PYTHONHOME:-$PETTA_OWNER_HOME/miniforge3/envs/petta}"
if [[ -d "$PETTA_PYTHONHOME" ]]; then
  export PYTHONHOME="$PETTA_PYTHONHOME"
  export LD_LIBRARY_PATH="$PETTA_PYTHONHOME/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
fi

git -C "$PETTA_DIR" cat-file -e "$PETTA_ORACLE_REV^{commit}"
mkdir -p "$CACHE_ROOT"

exec 9>"$CLEAN_ROOT.lock"
flock 9
if [[ ! -f "$CLEAN_ROOT/.pleatta-oracle-revision" ]] ||
   [[ "$(<"$CLEAN_ROOT/.pleatta-oracle-revision")" != "$PETTA_ORACLE_REV" ]]; then
  if [[ -e "$CLEAN_ROOT" ]]; then
    echo "oracle cache exists but does not match $PETTA_ORACLE_REV: $CLEAN_ROOT" >&2
    exit 2
  fi
  BUILD_ROOT="$(mktemp -d "$CACHE_ROOT/.petta-$PETTA_ORACLE_REV.XXXXXX")"
  git -C "$PETTA_DIR" archive "$PETTA_ORACLE_REV" | tar -x -C "$BUILD_ROOT"
  printf '%s\n' "$PETTA_ORACLE_REV" > "$BUILD_ROOT/.pleatta-oracle-revision"
  mv "$BUILD_ROOT" "$CLEAN_ROOT"
fi
flock -u 9

case "$PROGRAM" in
  "$PETTA_DIR"/*)
    REL="${PROGRAM#"$PETTA_DIR"/}"
    REL_DIR="$(dirname "$REL")"
    SUFFIX="${PROGRAM##*.}"
    RUN_FILE="$CLEAN_ROOT/$REL_DIR/.pleatta-oracle-$$.$SUFFIX"
    cp "$PROGRAM" "$RUN_FILE"
    trap 'rm -f "$RUN_FILE"' EXIT
    ;;
  *)
    echo "program must be inside PETTA_DIR so relative imports remain pinned" >&2
    exit 2
    ;;
esac

# PeTTa resolves relative library imports (lib/*) against the process CWD, so
# run the pinned program from the checkout root exactly as PeTTa expects.
cd "$CLEAN_ROOT"
bash "$CLEAN_ROOT/run.sh" "$RUN_FILE" "$@"
