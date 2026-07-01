#!/usr/bin/env bash
# setup-locked-vm.sh
#
# Create an OrbStack Debian VM, install HOL4 build deps + Claude Code,
# and lock outbound network to "DNS + HTTPS to api.anthropic.com /
# claude.ai".  Everything else is blocked at egress, including GitHub.
#
# The companion document `developers/claude/LOCKED-VM.md` (next to this
# script) describes the overall design, base assumptions, daily workflow,
# and security model.  Read it first if you haven't.
#
# Run on a macOS host.  Pre-reqs:
#   - OrbStack installed (`brew install orbstack`).
#   - A local HOL4 checkout (the directory containing this script must
#     be `<HOL>/developers/claude/`).  Override by setting REPO_HOST_PATH.
#   - A Claude Code account ready to log in via the device-flow.
#
# Phases:
#   1.  Create the OrbStack machine (skipped if it already exists).
#   2.  Bootstrap: apt install build deps + Claude Code.  Network is open
#       during this phase; nothing is locked down yet.
#   3.  Lockdown: configure nftables + dnsmasq so that the only allowed
#       outbound is to IPs that dnsmasq has resolved for the allowed
#       hostnames.  Verify with curl probes.
#   4.  Print invocation hints.
#
# To re-run a single phase manually, see the heredocs below -- they're
# standalone bash scripts intended to be cat'd into the VM.

set -euo pipefail

# Default REPO_HOST_PATH to the HOL checkout that contains this script.
# (Script is at <HOL>/developers/claude/setup-locked-vm.sh, so the repo
# root is two levels up.)  Override with REPO_HOST_PATH=<path> if you
# want the VM to point at a different checkout (e.g. the two-checkout
# pattern in LOCKED-VM.md).
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
REPO_DEFAULT="$( cd "$SCRIPT_DIR/../.." && pwd )"
REPO_HOST_PATH="${REPO_HOST_PATH:-$REPO_DEFAULT}"
REPO_GUEST_PATH="${REPO_GUEST_PATH:-/repo}"
VM_NAME="${VM_NAME:-hol4}"
VM_DISTRO="${VM_DISTRO:-debian}"

# ---------------------------------------------------------------------------
# Phase 1: ensure the VM exists.  OrbStack's `orb create` is idempotent if
# the machine already exists, but we still gate on `orb list` for a tidier
# log.

if [[ ! -d "$REPO_HOST_PATH" ]]; then
  echo "Repo not found at $REPO_HOST_PATH; set REPO_HOST_PATH." >&2
  exit 1
fi

if ! command -v orb >/dev/null; then
  echo "OrbStack not installed.  brew install orbstack." >&2
  exit 1
fi

if ! orbctl list 2>/dev/null | awk '{print $1}' | grep -qx "${VM_NAME}"; then
  echo "==> Creating isolated VM ${VM_NAME} (${VM_DISTRO})..."
  # --isolated         : do NOT mount /mnt/mac (the entire macOS home)
  # --isolate-network  : block lateral access to host IPs and other VMs
  #                      (does NOT block external internet; egress filter
  #                       inside the VM does that)
  # --mount A:B        : expose only the repo, nothing else from macOS
  orbctl create \
    --isolated \
    --isolate-network \
    --mount "${REPO_HOST_PATH}:${REPO_GUEST_PATH}" \
    "${VM_DISTRO}" "${VM_NAME}"
else
  echo "==> VM ${VM_NAME} already exists; skipping create."
fi

# ---------------------------------------------------------------------------
# Phase 2: bootstrap (apt + npm).  Network is wide open at this point.

# Write the bootstrap script to a host temp file and push it into the VM,
# rather than capturing it via $(cat <<'EOF' ... EOF) -- bash's outer parser
# still tracks $(...) nesting even through single-quoted heredocs, so the
# $(uname -m) etc. inside trips a syntax error.
cat > /tmp/setup-locked-vm.bootstrap.sh <<'INSIDE'
#!/usr/bin/env bash
set -euo pipefail
echo "[bootstrap 0/6] open network (stop firewall if active; re-applied by lockdown)"
# bootstrap needs unrestricted network: apt fetches deb.debian.org, npm
# fetches registry.npmjs.org, and mdbook is curl'd from github.com.
# If we're re-running on an already-bootstrapped VM, the lockdown
# firewall is up and would block all of those.  Stop it for the
# duration of bootstrap; lockdown re-enables it at the end.
sudo systemctl stop nftables 2>/dev/null || true

echo "[bootstrap 1/6] apt install build deps + sandbox tools + Claude prereqs"
# Notes on what's NOT in this list:
#  - mlton: unavailable on Debian/arm64.  Not needed for the manual
#    build pipeline; Poly/ML alone suffices.
#  - mdbook: not packaged in Bookworm.  Fetched as a static binary below.
#  - pandoc: Bookworm ships 2.17, too old for our pipeline.  Fetched as
#    an upstream-built .deb below.
# The texlive packages installed here are what HOL4's Manual/Description
# and Manual/Tutorial need for PDF builds (including stmaryrd from
# texlive-science and STIX fonts from texlive-fonts-extra).
export DEBIAN_FRONTEND=noninteractive
sudo apt-get update -qq
sudo apt-get install -y --no-install-recommends \
  build-essential ca-certificates curl git \
  polyml libpolyml-dev \
  latexmk \
  texlive-latex-recommended texlive-latex-extra texlive-science \
  texlive-fonts-recommended texlive-fonts-extra \
  nodejs npm \
  bubblewrap socat \
  nftables dnsmasq

echo "[bootstrap 2/6] install Claude Code globally"
sudo npm install -g @anthropic-ai/claude-code

echo "[bootstrap 3/6] install pandoc .deb (Bookworm's apt pandoc is too old)"
# To bump: visit https://github.com/jgm/pandoc/releases and pick a tag.
PANDOC_VER=3.9.0.2
ARCH=$(uname -m)
case "$ARCH" in
  aarch64|arm64)   PANDOC_ARCH=arm64 ;;
  x86_64|amd64)    PANDOC_ARCH=amd64 ;;
  *) echo "unknown arch $ARCH; install pandoc manually" >&2; exit 1 ;;
esac
PANDOC_DEB="pandoc-${PANDOC_VER}-1-${PANDOC_ARCH}.deb"
PANDOC_URL="https://github.com/jgm/pandoc/releases/download/${PANDOC_VER}/${PANDOC_DEB}"
curl -sSL -o "/tmp/${PANDOC_DEB}" "$PANDOC_URL"
sudo apt-get remove --purge -y pandoc pandoc-data 2>/dev/null || true
sudo dpkg -i "/tmp/${PANDOC_DEB}"
rm -f "/tmp/${PANDOC_DEB}"

echo "[bootstrap 4/6] install mdbook static binary (Debian has no package)"
# To bump: visit https://github.com/rust-lang/mdBook/releases and pick a tag.
MDBOOK_VER=v0.5.2
case "$ARCH" in
  aarch64|arm64)   MDBOOK_TARGET=aarch64-unknown-linux-musl ;;
  x86_64|amd64)    MDBOOK_TARGET=x86_64-unknown-linux-musl  ;;
  *) echo "unknown arch $ARCH; install mdbook manually" >&2; exit 1 ;;
esac
MDBOOK_URL="https://github.com/rust-lang/mdBook/releases/download/${MDBOOK_VER}/mdbook-${MDBOOK_VER}-${MDBOOK_TARGET}.tar.gz"
curl -sSL "$MDBOOK_URL" | sudo tar -xz -C /usr/local/bin mdbook
sudo chmod +x /usr/local/bin/mdbook

echo "[bootstrap 5/6] create unprivileged 'claude' user (no sudo)"
# Running Claude as a dedicated non-sudo user prevents it from disabling
# the egress firewall (sudo systemctl stop nftables would now fail).
# See developers/claude/LOCKED-VM.md ("Security model") for the full
# rationale.  virtio-fs is permissive about in-guest uids on /repo, so
# no group-membership setup is needed for write access.
if ! id claude >/dev/null 2>&1; then
  sudo useradd -m -s /bin/bash claude
fi
# Lock the default user's home so claude can't read its credentials etc.
sudo chmod 0750 "/home/$(whoami)"

echo "[bootstrap 6/6] sanity checks"
which poly claude pandoc mdbook
poly -v 2>&1 | head -1 || true
claude --version 2>&1 | head -1 || true
pandoc --version | head -1
mdbook --version
id claude
INSIDE

echo "==> Running bootstrap inside ${VM_NAME}..."
# orbctl push doesn't work for --isolated machines (it relies on the
# default /mnt/mac mapping that --isolated removes).  Pipe via stdin
# instead, which works regardless of the file-sharing config.
orb -m "${VM_NAME}" bash < /tmp/setup-locked-vm.bootstrap.sh

# ---------------------------------------------------------------------------
# Phase 3: lockdown.  nftables + dnsmasq with a DNS-driven allowlist set.
#
# Allowed outbound:
#   - loopback (lo)
#   - established/related (so return packets always come back)
#   - DNS to 127.0.0.1 (dnsmasq itself, which talks 1.1.1.1 upstream)
#   - HTTPS (tcp/443) to IPs in the anthropic_ips_v{4,6} nftables set
#
# Blocked: everything else.  github.com, raw IPs, port 22, SMTP, etc.
#
# dnsmasq populates the nftables sets on each A/AAAA lookup of an allowed
# hostname (api.anthropic.com, claude.ai).  Each entry has a TTL so stale
# IPs age out; new lookups refresh.

cat > /tmp/setup-locked-vm.lockdown.sh <<'INSIDE'
#!/usr/bin/env bash
set -euo pipefail

echo "[lockdown 1/5] writing /etc/nftables.conf"
sudo tee /etc/nftables.conf > /dev/null <<'NFT'
#!/usr/sbin/nft -f
flush ruleset

table inet filter {
  # Populated by dnsmasq on each A/AAAA lookup of an allowed hostname.
  set anthropic_ips_v4 { type ipv4_addr; flags timeout; }
  set anthropic_ips_v6 { type ipv6_addr; flags timeout; }

  chain output {
    type filter hook output priority 0; policy drop;
    oifname "lo"                                            accept
    ct state established,related                            accept
    # DNS from applications to the local dnsmasq stub
    udp dport 53  ip  daddr 127.0.0.1                       accept
    # Upstream DNS to Cloudflare.  dns-tcp-proxy uses the tcp/53 rules
    # (it forwards over TCP, which survives networks that drop outbound
    # UDP/53 -- see LOCKED-VM.md); the udp/53 rules stay so a plain UDP
    # upstream still works on networks that permit it.
    udp dport 53  ip  daddr 1.1.1.1                         accept
    udp dport 53  ip  daddr 1.0.0.1                         accept
    tcp dport 53  ip  daddr 1.1.1.1                         accept
    tcp dport 53  ip  daddr 1.0.0.1                         accept
    # HTTPS to allowlisted IPs (populated by dnsmasq)
    tcp dport 443 ip  daddr @anthropic_ips_v4               accept
    tcp dport 443 ip6 daddr @anthropic_ips_v6               accept
  }

  chain input  { type filter hook input  priority 0; policy accept; }
  chain forward{ type filter hook forward priority 0; policy drop;   }
}
NFT

echo "[lockdown 2/5] writing /etc/dnsmasq.d/anthropic.conf"
sudo tee /etc/dnsmasq.d/anthropic.conf > /dev/null <<'DNSMASQ'
listen-address=127.0.0.1
bind-interfaces
no-resolv
no-poll
# Forward upstream through the local UDP->TCP proxy (dns-tcp-proxy.service)
# instead of straight to 1.1.1.1:53.  Many Wi-Fi networks silently drop
# outbound UDP/53 to public resolvers while still permitting TCP/53, so a
# UDP upstream breaks the moment the host switches from wired to such a
# network.  The proxy speaks TCP, so DNS keeps working across the switch.
# See developers/claude/LOCKED-VM.md ("DNS breaks after switching networks").
server=127.0.0.1#5335
# OrbStack gives the guest a link-local IPv6 default route but no working
# global IPv6 egress, so AAAA answers send clients (node/Claude Code) down
# an IPv6 path whose SYNs the firewall silently drops -> connect timeouts
# and retries.  Strip AAAA so everything uses the working IPv4 allow-set.
filter-AAAA
# Add the resolved IPs of these hostnames to the nftables sets above.
nftset=/api.anthropic.com/4#inet#filter#anthropic_ips_v4
nftset=/api.anthropic.com/6#inet#filter#anthropic_ips_v6
nftset=/claude.ai/4#inet#filter#anthropic_ips_v4
nftset=/claude.ai/6#inet#filter#anthropic_ips_v6
DNSMASQ

echo "[lockdown 3/5] installing dns-tcp-proxy (UDP->TCP DNS forwarder)"
# dnsmasq has no "force TCP upstream" option and cannot re-frame UDP<->TCP
# DNS itself (TCP frames each message with a 2-byte length prefix that UDP
# lacks), so a small stdlib-only Python daemon does the forwarding.  No
# extra packages: python3 is already installed by bootstrap.
sudo tee /usr/local/sbin/dns-tcp-proxy.py > /dev/null <<'PYPROXY'
#!/usr/bin/env python3
"""dns-tcp-proxy: accept DNS queries over UDP on a local port and forward
them upstream over TCP/53, returning the answers back over UDP.

Rationale: some networks (notably UDP-53-filtering Wi-Fi, common on campus
and corporate access points) silently drop dnsmasq's UDP queries to public
resolvers while still permitting TCP/53.  dnsmasq has no "force TCP upstream"
option and cannot itself re-frame UDP<->TCP DNS, so it points its `server=`
at this proxy, which speaks TCP to Cloudflare.  See developers/claude/
LOCKED-VM.md for the full story."""
import socket, struct, sys, threading

LISTEN = ("127.0.0.1", 5335)
UPSTREAMS = [("1.1.1.1", 53), ("1.0.0.1", 53)]
TIMEOUT = 5

def _recvn(sock, n):
    buf = b""
    while len(buf) < n:
        chunk = sock.recv(n - len(buf))
        if not chunk:
            raise EOFError("upstream closed early")
        buf += chunk
    return buf

def resolve_tcp(query):
    framed = struct.pack("!H", len(query)) + query
    last = None
    for host, port in UPSTREAMS:
        try:
            with socket.create_connection((host, port), timeout=TIMEOUT) as t:
                t.settimeout(TIMEOUT)
                t.sendall(framed)
                (n,) = struct.unpack("!H", _recvn(t, 2))
                return _recvn(t, n)
        except Exception as exc:              # try the next upstream
            last = exc
    raise last

def handle(sock, data, addr):
    try:
        sock.sendto(resolve_tcp(data), addr)
    except Exception as exc:
        sys.stderr.write("dns-tcp-proxy: %s\n" % exc)

def main():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    s.bind(LISTEN)
    sys.stderr.write("dns-tcp-proxy: listening on %s:%d\n" % LISTEN)
    while True:
        data, addr = s.recvfrom(65535)
        threading.Thread(target=handle, args=(s, data, addr),
                         daemon=True).start()

if __name__ == "__main__":
    main()
PYPROXY
sudo chmod 0755 /usr/local/sbin/dns-tcp-proxy.py

sudo tee /etc/systemd/system/dns-tcp-proxy.service > /dev/null <<'UNITFILE'
[Unit]
Description=DNS UDP->TCP forwarder (for UDP/53-filtering networks)
Documentation=file:///repo/developers/claude/LOCKED-VM.md
Before=dnsmasq.service
After=network-online.target
Wants=network-online.target

[Service]
ExecStart=/usr/local/sbin/dns-tcp-proxy.py
DynamicUser=yes
Restart=on-failure
RestartSec=2
NoNewPrivileges=yes
ProtectSystem=strict
ProtectHome=yes
PrivateTmp=yes

[Install]
WantedBy=multi-user.target
UNITFILE
sudo systemctl daemon-reload

echo "[lockdown 4/5] disabling systemd-resolved stub, pointing resolv.conf at dnsmasq"
sudo systemctl disable --now systemd-resolved 2>/dev/null || true
# /etc/resolv.conf may be a symlink to a stub-resolv file managed by
# systemd-resolved; replace it with a static file pointing at dnsmasq.
sudo rm -f /etc/resolv.conf
sudo tee /etc/resolv.conf > /dev/null <<'RESOLV'
nameserver 127.0.0.1
options edns0 trust-ad
RESOLV

echo "[lockdown 5/5] enabling firewall + DNS proxy + dnsmasq services"
sudo systemctl enable --now nftables.service
sudo systemctl enable --now dns-tcp-proxy.service
sudo systemctl enable      dnsmasq.service
sudo systemctl restart     dnsmasq.service

echo
echo "==> Verifying lockdown..."

probe () {
  local label="$1" url="$2" want_pass="$3"
  if curl --max-time 5 --silent --head --output /dev/null "$url" 2>/dev/null; then
    if [[ "$want_pass" == yes ]]; then
      printf "  ok       %s reachable (expected)\n" "$label"
    else
      printf "  LEAK !!  %s reachable (should be blocked)\n" "$label"
    fi
  else
    if [[ "$want_pass" == yes ]]; then
      printf "  FAIL !!  %s unreachable (should work; investigate)\n" "$label"
    else
      printf "  ok       %s blocked (expected)\n" "$label"
    fi
  fi
}

probe "api.anthropic.com (HTTPS)" "https://api.anthropic.com/v1/messages" yes
probe "github.com (HTTPS)"        "https://github.com/"                  no
probe "raw IP 8.8.8.8 (HTTPS)"    "https://8.8.8.8/"                     no
probe "deb.debian.org (HTTPS)"    "https://deb.debian.org/"              no

echo
echo "==> Lockdown active."
INSIDE

echo "==> Applying lockdown inside ${VM_NAME}..."
orb -m "${VM_NAME}" bash < /tmp/setup-locked-vm.lockdown.sh

# ---------------------------------------------------------------------------
# Phase 4: usage hints.

cat <<EOF

==============================================================================
VM ${VM_NAME} ready.  Only the repo is visible inside the VM; the rest of
your macOS home is NOT mounted.

  host:   ${REPO_HOST_PATH}
  guest:  ${REPO_GUEST_PATH}     (read-write)

To enter the VM:
    orb -m ${VM_NAME}

Recommended: run Claude as the unprivileged 'claude' user rather than as
your sudo-capable default user.  Claude then cannot disable the egress
firewall (no sudo entry).  The default user's NOPASSWD sudo lets you
drop privileges without a password prompt.

One-time device-flow login as claude (lands credentials in
/home/claude/.claude/.credentials.json):
    orb -m ${VM_NAME} sudo -u claude -H bash -c \\
      'cd ${REPO_GUEST_PATH} && claude --dangerously-skip-permissions'
    # paste the printed URL into a macOS browser, enter code,
    # Ctrl+D when done

Daily invocation (same command; re-uses persisted credentials):
    orb -m ${VM_NAME} sudo -u claude -H bash -c \\
      'cd ${REPO_GUEST_PATH} && claude --dangerously-skip-permissions'

If you ever want to bypass that and run as the default sudo-capable user
(e.g. for maintenance), drop the 'sudo -u claude -H' prefix.

To inspect the firewall:
    orb -m ${VM_NAME} sudo nft list table inet filter

To unlock the network temporarily (e.g. apt install more deps):
    orb -m ${VM_NAME} sudo systemctl stop nftables
    # re-lock with:
    orb -m ${VM_NAME} sudo systemctl start nftables

To wipe the VM (the macOS repo is untouched):
    orbctl delete ${VM_NAME}

Notes:
  * Commits inside the VM operate on the macOS-mounted git repo, so
    they appear on macOS too.  Pushes must come from macOS
    (github is firewalled inside the VM).
  * The default in-VM user has the same name as your macOS user, with
    passwordless sudo.  The 'claude' user has no sudo and runs Claude.
  * If a new Anthropic endpoint becomes necessary, add it to
    /etc/dnsmasq.d/anthropic.conf and restart dnsmasq.
  * --isolate-network blocks lateral access to other OrbStack VMs and to
    macOS-host loopback IPs.  It does NOT block external internet; the
    nftables egress rules handle that.
  * See developers/claude/LOCKED-VM.md for the full design, security
    model, and troubleshooting guide.
==============================================================================
EOF
