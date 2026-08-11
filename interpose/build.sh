#!/usr/bin/env bash
# Build the level-interposition shared object.
#
# No Lean headers and no Lean libraries are needed: the library resolves
# everything it uses out of the host process at load time (`dlsym`) or by
# reading the host's own symbol table.  See the header comment of interpose.c.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
out="${1:-$here/levelhack.so}"
${CC:-cc} -O2 -g -fPIC -shared -Wall -Wextra \
  -o "$out" "$here/interpose.c" "$here/level_algebra.c" -ldl
echo "built $out"
