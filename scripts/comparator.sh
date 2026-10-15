#!/usr/bin/env bash
# comparator.sh: the comparator check of this repository, in one command (`make comparator`).
#
# Run it in a fresh clone (Linux only). It
#   1. installs the pinned checking tools into .comparator/ (gitignored), checking every pinned revision:
#        Go 1.27.1    the official tarball, SHA-256 checked; used only to build landrun
#        landrun      github.com/Zouuup/landrun at 5e9a0d1, the sandbox comparator builds the proof in
#        lean4export  github.com/leanprover/lean4export, tag v4.32.0
#        comparator   github.com/leanprover/comparator, tag v4.32.0
#      A second run finds them in place, checks them again, and reuses them;
#   2. downloads the prebuilt Mathlib (`lake exe cache get`);
#   3. checks that landrun's sandbox works on this kernel, then runs
#        bash -c 'ulimit -s unlimited && lake env <comparator> comparator.json'
#      as comparator's README prescribes: in a transient systemd user unit with RestrictAddressFamilies=~AF_UNIX
#      (no Unix-domain sockets; landrun's own rules block every write outside .lake/ and, on Linux 6.7 or later,
#      TCP connections);
#   4. prints the elapsed time and the verdict. The exit status is 0 only if comparator succeeds and its last
#      line is "Your solution is okay!".
#
# Prerequisites: elan (https://github.com/leanprover/elan), git, curl, tar, sha256sum, which.
# Nothing is written outside this repository except what elan and lake write for any Lean project (the Lean
# toolchain under ~/.elan, the Mathlib cache under ~/.cache).
#
# Options:
#   --install-only                 step 1 only.
# Environment:
#   COMPARATOR_LAUNCH=auto|pty|unit|direct
#       how comparator is started. auto (default): `systemd-run --user --pty` if it works (it needs a user D-Bus
#       session, as on desktop Linux); else a detached `systemd-run --user` unit whose output is streamed here and
#       whose exit status is read back. If neither works, auto stops: running without the systemd Unix-socket guard
#       (comparator's README asks for it) needs an explicit COMPARATOR_LAUNCH=direct, and the verdict then says so.
#   COMPARATOR_SKIP_CACHE_GET=1
#       skip `lake exe cache get` (for testing this script on a small project that does not use Mathlib).
# The log of each run is kept in .comparator/logs/.
set -euo pipefail

GO_VERSION=1.27.1
GO_SHA256_amd64=63d339f0da5ab53635a56f2490a7984dfe12dfcff22ad749f63edaf590168445
GO_SHA256_arm64=3450b45a3f9ee8568792736a5c5e70a1f2e9b36c35a8f74958c03e51d7d92bec
LANDRUN_URL=https://github.com/Zouuup/landrun
LANDRUN_REV=5e9a0d15d6009cdaf27133bf2d59d29e7018cc47
LEAN4EXPORT_URL=https://github.com/leanprover/lean4export
LEAN4EXPORT_TAG=v4.32.0
LEAN4EXPORT_REV=4e7915201d3f9f04470d9eae002fa695f7cdc589
COMPARATOR_URL=https://github.com/leanprover/comparator
COMPARATOR_TAG=v4.32.0
COMPARATOR_REV=07bc4ea40f2266dcb861820a2ec1fa3244ed307f
OKAY='Your solution is okay!'
MEM_GB_MEASURED=32   # peak memory of one measured run of this check

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
TOOLS=$ROOT/.comparator
LANDRUN=$TOOLS/bin/landrun
LEAN4EXPORT=$TOOLS/lean4export/.lake/build/bin/lean4export
COMPARATOR=$TOOLS/comparator/.lake/build/bin/comparator

say() { printf '==> %s\n' "$*"; }
warn() { printf '==> WARNING: %s\n' "$*" >&2; }
die() { printf '==> ERROR: %s\n' "$*" >&2; exit 1; }
hms() { printf '%dh %02dm %02ds' $(($1 / 3600)) $(($1 % 3600 / 60)) $(($1 % 60)); }

# ---- inside the sandboxing unit: raise the limits, run comparator, record the exit status ----------------------
if [ "${1:-}" = --inner ]; then
  status=${2:-}
  cd "$ROOT"
  rc=0
  if ulimit -s unlimited 2>/dev/null; then
    ulimit -n "$(ulimit -Hn)" 2>/dev/null || true   # systemd user units start with a soft limit of 1024 open files
    echo "stack limit: $(ulimit -s); open files: $(ulimit -n)"
    lake env "$COMPARATOR" comparator.json || rc=$?
  else
    echo "cannot raise the stack limit to unlimited (hard limit: $(ulimit -Hs)); comparator needs it"
    rc=2
  fi
  if [ -n "$status" ]; then echo "$rc" > "$status.part" && mv "$status.part" "$status"; fi
  exit "$rc"
fi

case "${1:-}" in
  "") MODE=run ;;
  --install-only) MODE=install ;;
  *) die "unknown option '$1' (usage: scripts/comparator.sh [--install-only])" ;;
esac
cd "$ROOT"
T0=$(date +%s)

# ---- prerequisites ------------------------------------------------------------------------------------------
[ "$(uname -s)" = Linux ] || die "comparator runs on Linux only: its sandbox, landrun, uses the Linux Landlock LSM."
[ "$(id -u)" != 0 ] || die "do not run comparator as root (comparator's README, assumption 6); use an ordinary user."
if ! command -v lake >/dev/null 2>&1 && [ -x "$HOME/.elan/bin/lake" ]; then PATH=$HOME/.elan/bin:$PATH; fi
missing=()
for c in elan lake git curl tar sha256sum which; do command -v "$c" >/dev/null 2>&1 || missing+=("$c"); done
if ((${#missing[@]})); then
  printf '==> ERROR: missing prerequisites: %s\n' "${missing[*]}" >&2
  case " ${missing[*]} " in *" elan "* | *" lake "*)
    cat >&2 <<'EOF'
    elan installs Lean and lake (in your home directory, no root needed):
      curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
    then open a new shell (or run: source ~/.elan/env) and run `make comparator` again.
EOF
  esac
  case " ${missing[*]} " in *" git "* | *" curl "* | *" tar "* | *" sha256sum "* | *" which "*)
    echo "    git, curl, tar, sha256sum (coreutils) and which come with your distribution's package manager," \
      "e.g. sudo apt install git curl tar coreutils debianutils" >&2
  esac
  exit 1
fi
[ -f comparator.json ] || die "no comparator.json in $ROOT"

# The proof must be compiled only inside comparator's sandbox (comparator's README, assumption 2).
# Any compiled module of this repository counts (an interrupted `make` leaves thousands); Mathlib's prebuilt
# binaries live under .lake/packages and are not affected.
built_outside() {
  local f
  f=$(find .lake/build/lib/lean -name '*.olean' -print -quit 2>/dev/null)
  [ -n "$f" ] && { echo "$f"; return 0; }
  return 1
}
if [ "$MODE" = run ] && f=$(built_outside); then
  die "$f (and possibly more) already exists: this repository has been compiled before, outside comparator's sandbox.
    Compiling the proof outside the sandbox runs its code with your rights, which voids comparator's guarantee:
    run the check in a fresh clone, on an account (or container) where \`make\` has never built this repository."
fi

# ---- 1. pinned tools in .comparator/ ------------------------------------------------------------------------
mkdir -p "$TOOLS/bin" "$TOOLS/downloads" "$TOOLS/logs"

install_go() {
  local arch sha
  case "$(uname -m)" in
    x86_64 | amd64) arch=amd64 sha=$GO_SHA256_amd64 ;;
    aarch64 | arm64) arch=arm64 sha=$GO_SHA256_arm64 ;;
    *) die "no pinned Go build for $(uname -m) (pinned: linux-amd64, linux-arm64)" ;;
  esac
  local name=go$GO_VERSION.linux-$arch.tar.gz
  if [ -d "$TOOLS/go" ]; then
    [ "$(cat "$TOOLS/go.done" 2>/dev/null)" = "$name $sha" ] && [ -x "$TOOLS/go/bin/go" ] ||
      die "$TOOLS/go is not the pinned $name; remove it and run again"
    say "Go $GO_VERSION: present, from $name (SHA-256 $sha)"
    return
  fi
  say "Go $GO_VERSION: downloading https://go.dev/dl/$name"
  curl -fsSL --retry 3 -o "$TOOLS/downloads/$name.part" "https://go.dev/dl/$name" || die "download of $name failed"
  echo "$sha  $TOOLS/downloads/$name.part" | sha256sum -c --quiet - ||
    die "$name does not have the pinned SHA-256 $sha"
  mv "$TOOLS/downloads/$name.part" "$TOOLS/downloads/$name"
  rm -rf "$TOOLS/go.partial"
  mkdir "$TOOLS/go.partial"
  tar -xzf "$TOOLS/downloads/$name" -C "$TOOLS/go.partial"
  mv "$TOOLS/go.partial/go" "$TOOLS/go" && rmdir "$TOOLS/go.partial"
  "$TOOLS/go/bin/go" version | grep -q "go$GO_VERSION " || die "$TOOLS/go/bin/go is not Go $GO_VERSION"
  echo "$name $sha" > "$TOOLS/go.done"
  say "Go $GO_VERSION: installed (SHA-256 $sha verified)"
}

# clone_pinned NAME URL TAG REV: clone into .comparator/NAME (once) and check that HEAD is REV, unmodified.
clone_pinned() {
  local name=$1 url=$2 tag=$3 rev=$4 dir=$TOOLS/$1
  if [ ! -d "$dir" ]; then
    rm -rf "$dir.partial"
    if [ -n "$tag" ]; then
      git -c advice.detachedHead=false clone --quiet --depth 1 --branch "$tag" "$url" "$dir.partial" ||
        die "git clone of $url failed"
    else
      git clone --quiet "$url" "$dir.partial" || die "git clone of $url failed"
      git -c advice.detachedHead=false -C "$dir.partial" checkout --quiet --detach "$rev" ||
        die "$url has no commit $rev"
    fi
    mv "$dir.partial" "$dir"
  fi
  local head
  head=$(git -C "$dir" rev-parse HEAD)
  [ "$head" = "$rev" ] || die "$dir is at $head, not the pinned $rev; remove $dir and run again"
  [ -z "$(git -C "$dir" status --porcelain --untracked-files=all)" ] ||
    die "$dir has local changes or untracked files; remove $dir and run again"
}

install_landrun() {
  clone_pinned landrun "$LANDRUN_URL" "" "$LANDRUN_REV"
  if [ "$(cat "$TOOLS/landrun.done" 2>/dev/null)" != "$LANDRUN_REV" ] || [ ! -x "$LANDRUN" ]; then
    say "landrun: building ${LANDRUN_REV:0:7} with Go $GO_VERSION"
    # Go's caches and settings stay in .comparator/ (no module cache, telemetry or go env in your home).
    (cd "$TOOLS/landrun" && env GOTOOLCHAIN=local GOENV=off GOFLAGS=-modcacherw CGO_ENABLED=0 \
      GOPATH="$TOOLS/gopath" GOMODCACHE="$TOOLS/gopath/pkg/mod" GOCACHE="$TOOLS/gocache" \
      XDG_CONFIG_HOME="$TOOLS/config" "$TOOLS/go/bin/go" build -o "$LANDRUN" ./cmd/landrun) ||
      die "building landrun failed"
  fi
  # Go stamps the commit it built from into the binary.
  local info
  info=$("$TOOLS/go/bin/go" version -m "$LANDRUN")
  grep -q "vcs.revision=$LANDRUN_REV" <<< "$info" && grep -q 'vcs.modified=false' <<< "$info" ||
    die "$LANDRUN was not built from an unmodified $LANDRUN_REV; remove $TOOLS/landrun.done and run again"
  echo "$LANDRUN_REV" > "$TOOLS/landrun.done"
  say "landrun: $LANDRUN_REV (verified in the binary)"
}

# install_lake_tool NAME URL TAG REV BINARY
install_lake_tool() {
  local name=$1 url=$2 tag=$3 rev=$4 bin=$5 dir=$TOOLS/$1
  clone_pinned "$name" "$url" "$tag" "$rev"
  if [ "$(cat "$TOOLS/$name.done" 2>/dev/null)" != "$rev" ] || [ ! -x "$bin" ]; then
    say "$name: building $tag (${rev:0:7}) with lake"
    (cd "$dir" && lake build) || die "building $name failed"
    [ -x "$bin" ] || die "building $name did not produce $bin"
  fi
  # The Lean dependencies lake fetched must be the revisions pinned in the tool's lake-manifest.json.
  local p head
  for p in "$dir"/.lake/packages/*/; do
    [ -d "$p" ] || continue
    head=$(git -C "$p" rev-parse HEAD)
    grep -q "\"rev\": \"$head\"" "$dir/lake-manifest.json" ||
      die "$p is at $head, which $dir/lake-manifest.json does not pin; remove $dir and run again"
  done
  echo "$rev" > "$TOOLS/$name.done"
  say "$name: $tag = $rev (verified)"
}

install_go
install_landrun
install_lake_tool lean4export "$LEAN4EXPORT_URL" "$LEAN4EXPORT_TAG" "$LEAN4EXPORT_REV" "$LEAN4EXPORT"
install_lake_tool comparator "$COMPARATOR_URL" "$COMPARATOR_TAG" "$COMPARATOR_REV" "$COMPARATOR"
say "tools ready in $TOOLS ($(hms $(($(date +%s) - T0))))"
[ "$MODE" = install ] && exit 0

# ---- 2. prebuilt Mathlib ------------------------------------------------------------------------------------
if [ "${COMPARATOR_SKIP_CACHE_GET:-0}" = 1 ]; then
  say "skipping \`lake exe cache get\` (COMPARATOR_SKIP_CACHE_GET=1)"
else
  say "downloading the prebuilt Mathlib: lake exe cache get"
  lake exe cache get || die "lake exe cache get failed"
fi
if f=$(built_outside); then die "$f exists before comparator ran; use a fresh clone"; fi

# ---- 3. sandbox self-test and launch ------------------------------------------------------------------------
# landrun runs with --best-effort under comparator, so a kernel without Landlock would leave the build unconfined.
# Check that a write outside the allowed paths is refused, and one inside them is not.
probe=$TOOLS/sandbox-probe
rm -rf "$probe"
mkdir -p "$probe/allowed"
sh_bin=$(type -P sh)
"$LANDRUN" --best-effort --ro / --rw /dev --rwx "$probe/allowed" --ldd --add-exec "$sh_bin" \
  -c ": > '$probe/allowed/ok'" > /dev/null 2>&1 && [ -e "$probe/allowed/ok" ] ||
  die "landrun does not run on this system (Landlock: Linux 5.13 or later with the landlock LSM enabled)"
if "$LANDRUN" --best-effort --ro / --rw /dev --ldd --add-exec "$sh_bin" -c ": > '$probe/denied'" \
  > /dev/null 2>&1 || [ -e "$probe/denied" ]; then
  die "landrun did not block a write outside its sandbox: this kernel does not enforce Landlock (see
    /sys/kernel/security/lsm), so comparator's sandbox would not hold. Enable the landlock LSM and run again."
fi
rm -rf "$probe"
say "sandbox self-test passed: landrun refuses writes outside the paths it allows"

mem_kb=$(awk '/^MemTotal:/ {print $2}' /proc/meminfo 2>/dev/null || echo 0)
if [ "${mem_kb:-0}" -lt $((MEM_GB_MEASURED * 1000 * 1000)) ]; then
  warn "this machine has $((mem_kb / 1000 / 1000)) GB of memory; a measured run of this check peaked at about" \
    "$MEM_GB_MEASURED GB, so it may run out of memory."
fi

export PATH="$TOOLS/bin:$(dirname "$LEAN4EXPORT"):$PATH"
export COMPARATOR_LANDRUN=$LANDRUN COMPARATOR_LEAN4EXPORT=$LEAN4EXPORT
stamp=$(date -u +%Y%m%dT%H%M%SZ)
LOG=$TOOLS/logs/comparator-$stamp.log
{
  echo "comparator run of $ROOT, started $(date -u '+%Y-%m-%d %H:%M:%S UTC')"
  echo "  lean        $(lake env lean --version 2>/dev/null | head -1)"
  echo "  comparator  $COMPARATOR_TAG = $COMPARATOR_REV"
  echo "  lean4export $LEAN4EXPORT_TAG = $LEAN4EXPORT_REV"
  echo "  landrun     $LANDRUN_REV"
  echo "  config      comparator.json: $(tr -s ' \n' ' ' < comparator.json)"
} | tee "$LOG"

systemd_ok() { command -v systemd-run >/dev/null 2>&1; }
pty_ok() {
  systemd_ok && timeout 60 systemd-run --user --pty --quiet --collect --property=RestrictAddressFamilies=~AF_UNIX \
    -- "$(type -P true)" > /dev/null 2>&1
}
unit_ok() {
  systemd_ok && command -v systemctl >/dev/null 2>&1 && timeout 60 systemd-run --user --quiet --collect \
    --unit="comparator-probe-$stamp-$$" --property=RestrictAddressFamilies=~AF_UNIX -- "$(type -P true)" > /dev/null 2>&1
}
launch=${COMPARATOR_LAUNCH:-auto}
if [ "$launch" = auto ]; then
  if pty_ok; then launch=pty; elif unit_ok; then launch=unit; else
    die "systemd-run --user is not available here, so comparator cannot run under the RestrictAddressFamilies=~AF_UNIX
    guard that comparator's README asks for. To run it anyway without that guard (landrun's sandbox still applies),
    run: COMPARATOR_LAUNCH=direct make comparator"
  fi
fi
envs=(-E "PATH=$PATH" -E "HOME=$HOME" -E "COMPARATOR_LANDRUN=$LANDRUN" -E "COMPARATOR_LEAN4EXPORT=$LEAN4EXPORT")
[ -n "${ELAN_HOME:-}" ] && envs+=(-E "ELAN_HOME=$ELAN_HOME")
inner=("$(type -P bash)" "$ROOT/scripts/comparator.sh" --inner)

say "running comparator (the proof is compiled inside the sandbox first; this takes hours); log: $LOG"
T1=$(date +%s)
rc=0
case "$launch" in
  pty)
    say "launch: systemd-run --user --pty, RestrictAddressFamilies=~AF_UNIX"
    systemd-run --user --pty --quiet --collect --property=RestrictAddressFamilies=~AF_UNIX "${envs[@]}" \
      --working-directory "$ROOT" -- "${inner[@]}" 2>&1 | tee -a "$LOG" || rc=${PIPESTATUS[0]}
    ;;
  unit)
    unit=comparator-$stamp-$$
    status=$TOOLS/logs/comparator-$stamp.status
    say "launch: detached systemd user unit $unit, RestrictAddressFamilies=~AF_UNIX (no user D-Bus session for" \
      "--pty); its output follows. Ctrl-C stops the unit."
    tail -n 0 -F "$LOG" 2> /dev/null &
    tail_pid=$!
    trap 'kill "$tail_pid" 2>/dev/null || true' EXIT
    trap 'echo; warn "interrupted: stopping unit $unit"; systemctl --user stop "$unit" 2>/dev/null || true; exit 130' \
      INT TERM HUP
    systemd-run --user --quiet --collect --unit="$unit" --property=RestrictAddressFamilies=~AF_UNIX \
      -p StandardOutput="append:$LOG" -p StandardError=inherit "${envs[@]}" --working-directory "$ROOT" \
      -- "${inner[@]}" "$status" || die "systemd-run could not start the unit"
    while [ ! -s "$status" ]; do
      if ! systemctl --user is-active --quiet "$unit" 2>/dev/null; then
        sleep 3
        [ -s "$status" ] || break
      fi
      sleep 5
    done
    sleep 1
    kill "$tail_pid" 2>/dev/null || true
    trap - INT TERM HUP
    if [ -s "$status" ]; then rc=$(cat "$status"); else
      rc=1
      warn "unit $unit ended without reporting an exit status (killed, e.g. out of memory?)"
    fi
    ;;
  direct)
    warn "running comparator directly (systemd-run --user unavailable, or COMPARATOR_LAUNCH=direct), WITHOUT" \
      "RestrictAddressFamilies=~AF_UNIX. landrun's sandbox still confines the build, but comparator's README" \
      "adds this systemd guard against a known landrun weakness (Unix-domain sockets)."
    "${inner[@]}" 2>&1 | tee -a "$LOG" || rc=${PIPESTATUS[0]}
    ;;
  *) die "COMPARATOR_LAUNCH must be auto, pty, unit or direct (got '$launch')" ;;
esac

# ---- 4. verdict ---------------------------------------------------------------------------------------------
T2=$(date +%s)
last=$(tr -d '\r' < "$LOG" | awk 'NF {l = $0} END {print l}')
echo
say "comparator exit status: $rc"
say "elapsed: comparator $(hms $((T2 - T1))); total including setup $(hms $((T2 - T0)))"
say "log: $LOG"
guard="launch $launch, RestrictAddressFamilies=~AF_UNIX"
[ "$launch" = direct ] && guard="launch direct, WITHOUT the systemd Unix-socket guard"
VERDICT=$TOOLS/logs/comparator-$stamp.verdict
if [ "$rc" = 0 ] && [ "$last" = "$OKAY" ]; then
  echo "PASS ($guard): $OKAY" > "$VERDICT"
  say "VERDICT: PASS ($guard). comparator: $OKAY"
  say "the verdict is also in $VERDICT, and this command exits with status 0"
  exit 0
fi
echo "FAIL ($guard): ${last:-<none>}" > "$VERDICT"
say "VERDICT: FAIL ($guard). comparator did not accept the solution (last line: ${last:-<none>})"
[ "$rc" != 0 ] && exit "$rc"
exit 1
