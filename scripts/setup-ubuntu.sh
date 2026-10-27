#!/usr/bin/env bash
# Ubuntu 22.04/24.04 x86_64; run as a regular user with sudo.
set -euo pipefail
DELIVERY_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
DELIVERY_SWITCH="$DELIVERY_ROOT/.tools/coq"
[[ "$EUID" -ne 0 ]] || { echo '请使用有 sudo 权限的普通用户运行。'; exit 1; }
source /etc/os-release
[[ "$ID" == ubuntu && "$(uname -m)" == x86_64 ]] || { echo '安装入口面向 Ubuntu x86_64。'; exit 1; }
sudo apt-get update
sudo apt-get install -y build-essential python3 ca-certificates opam m4 pkg-config libgmp-dev bubblewrap
opam init --bare --no-setup -y
mkdir -p "$DELIVERY_ROOT/.tools"
if [[ ! -d "$DELIVERY_SWITCH/_opam" ]]; then
  opam switch create "$DELIVERY_SWITCH" ocaml-base-compiler.4.14.2 -y
fi
eval "$(opam env --switch="$DELIVERY_SWITCH" --set-switch)"
[[ "$(ocamlc -version)" == 4.14.2 ]] || { echo '需要 OCaml 4.14.2。'; exit 1; }
opam install --switch="$DELIVERY_SWITCH" coq.8.20.1 -y
coqc --version
python3 -B "$DELIVERY_ROOT/scripts/fetch-qcp.py"
echo '环境已准备；运行 python3 -B scripts/reproduce.py full --jobs 2。'
