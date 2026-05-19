# Locked-down OrbStack VM for Claude Code on HOL4

This describes one way of running [Claude Code](https://www.anthropic.com/claude-code)
against this repo from inside a sandboxed Linux VM, so that you can
let Claude work with `--dangerously-skip-permissions` (no per-command
prompts) inside a bounded blast radius.

It's optional — Claude Code runs fine directly on macOS or Linux —
but if you're handing Claude tasks that involve a lot of shell
commands, the prompt fatigue can be real, and "permit all" without
a sandbox is uncomfortable.  The setup here trades a bit of one-time
configuration for the ability to say "yes to everything" inside a
container that genuinely can't reach much.

## Base assumptions

- **macOS host (Apple Silicon or Intel).**  This depends on
  [OrbStack](https://orbstack.dev), which is macOS-only.  The setup
  script auto-detects arm64 vs amd64 for the Debian guest packages,
  so both host architectures should work.
- **A local clone of this repo.**  The setup script defaults to
  pointing the VM at the checkout containing the script (i.e.,
  `<HOL>/developers/claude/setup-locked-vm.sh` → repo root two
  levels up).  Override `REPO_HOST_PATH=…` for a different checkout
  (e.g. the two-checkout pattern below).
- **A Claude Code account.**  You'll do a one-time device-flow login
  from inside the VM, pasting a URL into a macOS browser.
- **Comfort with the command line.**  Setting environment variables,
  editing shell config, running `orb`/`orbctl`.
- **Awareness that this is one approach.**  Anthropic publishes their
  own
  [reference devcontainer](https://github.com/anthropics/claude-code/tree/main/.devcontainer)
  (Docker-based, Linux-host friendly) and there's an upstream
  ["safe YOLO mode" guide](https://docs.claude.com/en/docs/claude-code/devcontainer).
  The setup here is a deliberately small, OrbStack-shaped variant of
  the same idea, tuned for HOL4's build prerequisites.

## What the VM gives you

  - The VM mounts **only this repo** from the macOS host
    (e.g. `~/HOL → /repo`), not your home directory.  `~/.ssh`,
    `~/.aws`, `~/.gnupg`, Documents, etc. are unreachable from inside.
  - The VM's outbound network is firewalled to **only `api.anthropic.com`
    and `claude.ai`** (the endpoints Claude Code needs).  GitHub, raw
    public IPs, generic HTTP — all blocked at egress.
  - The VM cannot reach other OrbStack machines or the macOS host's
    loopback addresses (`--isolate-network`).
  - **Two user accounts inside the VM:** the default account
    (matching your macOS username) has passwordless sudo, used for
    maintenance.  A dedicated `claude` account has **no sudo**, used
    for running Claude Code.  Claude cannot disable the egress
    firewall because it cannot sudo.

Inside that envelope Claude has full freedom: any Bash command, any
file operation, no permission prompts.  What it cannot do is escape
the firewall, the mount restriction, or the user separation.

## One-time setup

The setup script is `developers/claude/setup-locked-vm.sh` in this
repo.  You can run it in place, or copy/symlink it to a directory on
your `$PATH` for convenience:

    # Run in place:
    ./developers/claude/setup-locked-vm.sh

    # Or install once, then re-run on demand:
    cp developers/claude/setup-locked-vm.sh ~/bin/
    chmod +x ~/bin/setup-locked-vm.sh
    ~/bin/setup-locked-vm.sh

The script creates the OrbStack VM, installs the build deps + Claude
Code, creates the `claude` user (no sudo), and applies the egress
firewall.  Idempotent — re-running it on an existing `hol4` VM is
harmless.  Bootstrap re-uses already-installed apt packages (fast);
lockdown re-writes the firewall config with the same content.

Environment variables (rarely need to override):

  - `REPO_HOST_PATH` — host path of this repo (default: the repo
    containing the script).
  - `REPO_GUEST_PATH` — guest mount point (default: `/repo`).
  - `VM_NAME`        — OrbStack machine name (default: `hol4`).
  - `VM_DISTRO`      — base distro (default: `debian`).

After the script finishes it prints a verification block.  All four
probes should report `ok`:

    ok       api.anthropic.com (HTTPS) reachable (expected)
    ok       github.com (HTTPS) blocked (expected)
    ok       raw IP 8.8.8.8 (HTTPS) blocked (expected)
    ok       deb.debian.org (HTTPS) blocked (expected)

If `api.anthropic.com` reports `FAIL`, see the troubleshooting section.

### Two-checkout pattern (optional)

By default the script points the VM at the same checkout you're
working on from macOS.  That works, but means Claude and your
macOS-side tools share `bin/Holmake`, `sigobj/`, and `.HOLMK/`
(Linux ELF and Mach-O collide; you'd have to `smart-configure` per
side every time you switch).

A cleaner pattern is to give the VM its own dedicated checkout:

    git clone ~/HOL ~/HOL-vm

    # Copy the per-repo Claude config across.  Anchored exclude keeps
    # any host-side git worktrees from coming along (they wouldn't
    # function from the new clone anyway).
    rsync -a --exclude='/worktrees/' ~/HOL/.claude/ ~/HOL-vm/.claude/

    # CRITICAL: delete the copied settings.local.json if you have one.
    # Its `sandbox` block is for macOS sandbox-exec; inside Linux +
    # bwrap it makes Claude unable to write to `.git/config` and
    # `.git/hooks` (see "Don't ship a sandbox stanza" below).
    rm -f ~/HOL-vm/.claude/settings.local.json

    # Then point the VM script at the new checkout:
    REPO_HOST_PATH=~/HOL-vm ./developers/claude/setup-locked-vm.sh

Now:

  - macOS side (`~/HOL`) is your normal workspace — editor, macOS
    builds, `gh`/`git push`, etc.  Nothing the VM does touches it.
  - Linux side (`~/HOL-vm`) is the VM's playground.  `bin/Holmake`
    is Linux ELF, `sigobj/` is full of Linux-built `.uo`s, Claude's
    writes land here only.

Syncing the two checkouts:

    # peek at what Claude did on the Linux side from your macOS shell
    git -C ~/HOL remote add locked ~/HOL-vm
    git -C ~/HOL fetch locked
    git -C ~/HOL log --oneline locked/<branch>

Pushing:

  - The VM cannot `git push` (github is firewalled), so push from
    macOS.  Either directly from the VM-side checkout (`git -C
    ~/HOL-vm push origin <branch>` — the firewall only constrains the
    VM, not macOS-side git running against the same directory), or
    merge the locked branch into your primary checkout via the
    `locked` remote above and push from there.

### First Claude login (as the `claude` user)

The VM has no browser, so use Claude Code's device-flow login.  The
auth runs *as the `claude` user* so credentials land in
`/home/claude/.claude/.credentials.json`, which only `claude` can
read:

    orb -m hol4 sudo -u claude -H bash -c \
      'cd /repo && claude --dangerously-skip-permissions'

It prints a URL + short code.  Open the URL on macOS, paste the code,
Ctrl+D when done.  Subsequent runs re-use the persisted credentials.

`sudo -u claude` works without a password prompt because your default
account has NOPASSWD sudo — you're using your privileges to drop
*down* to `claude`.  Claude itself cannot sudo back up.

### Git identity for in-VM commits

If you make commits inside the VM, set an identity once.  System-wide
is easiest (both users read it):

    orb -m hol4 sudo git config --system user.name  "Your Name"
    orb -m hol4 sudo git config --system user.email "you@example.com"

`--global` works too if you want different identities per role; it
goes in each user's `~/.gitconfig`.

## Daily workflow

### Starting fresh work on a new branch

When the next thing is "create a worktree, then launch Claude in it",
drop into a shell rather than chaining one-liners:

    orb -m hol4                                       # shell as default user
    $ cd /repo
    $ git worktree add .claude/worktrees/<name> <base>
    $ cd .claude/worktrees/<name>
    $ sudo -u claude -H claude --dangerously-skip-permissions

`sudo -u claude -H` preserves the current working directory and sets
`HOME=/home/claude` (so Claude finds its own `~/.claude/`).  When
Claude exits you're back at the original shell at the worktree dir,
ready to `git log`, `git push` from macOS, etc.

Stay as your default user for `git worktree add`; the worktree-
creation writes into `/repo/.git/worktrees/<name>/`, and keeping
infrastructure ops on the sudo-capable account matches the role
split.

### Resuming work on an existing worktree

Once a worktree exists, a single one-liner is enough:

    orb -m hol4 sudo -u claude -H bash -c \
      'cd /repo/.claude/worktrees/<name> && claude --dangerously-skip-permissions'

### Cwd-aware macOS alias

Add to your `~/.zshrc` (adjust the prefix path to match your
checkout location):

    function claude-vm() {
      local rel="${PWD#$HOME/HOL-vm}"
      orb -m hol4 sudo -u claude -H bash -c \
        "cd /repo${rel} && claude --dangerously-skip-permissions"
    }

Then `cd ~/HOL-vm/.claude/worktrees/foo && claude-vm` lands at
`/repo/.claude/worktrees/foo` inside the VM as `claude`.

## What you can / can't do inside the VM

  - **`/repo` is read+write from both sides.**  Edit in your macOS editor
    as usual.  Claude sees the changes immediately; your macOS editor
    sees Claude's writes immediately.  virtio-fs is permissive about
    in-guest user perms on `/repo` — any in-VM user (including `claude`
    with no shared group) can read/write/delete anywhere, and all
    writes appear on macOS as the default user.  (See "Security model"
    for why this is fine.)
  - **HOL4 builds are Linux-native.**  `bin/Holmake` and friends get
    rebuilt as Linux ELF by `poly < tools/smart-configure.sml` inside
    the VM.  Don't try to use those binaries from macOS afterwards —
    pick one side per worktree, or run smart-configure on each side
    as you switch.  The two-checkout pattern avoids the issue
    entirely.
  - **Worktrees** at `.claude/worktrees/<name>/` are visible as
    `/repo/.claude/worktrees/<name>/`.  Create them from inside the
    VM as your default user (creating from macOS is fine in principle
    but Spotlight indexing on virtio-fs has occasionally surfaced
    `Device or resource busy` errors on `.git/` writes).  Each new
    worktree needs its own smart-configure inside the VM if you
    intend to build there.
  - **`git commit` works inside the VM** (operates on the mounted git
    tree, which propagates to macOS).
  - **`git push` does NOT work inside the VM** — GitHub is firewalled.
    Push from a macOS terminal instead.
  - **`gh` CLI does not work inside the VM** for the same reason.  PRs
    and issue triage stay on macOS.
  - **Project-level skills at `/repo/.claude/skills/`** apply
    regardless of which in-guest user runs Claude.  User-level skills
    would need to be installed under both `/home/<your-user>/.claude/`
    and `/home/claude/.claude/` separately — project-level is easier.

## Don't ship a `sandbox` stanza in `.claude/settings.local.json`

Claude Code's macOS-side `.claude/settings.local.json` may have a
`sandbox` block that uses `sandbox-exec` to limit Bash file writes.
**Inside the VM that same block is interpreted via `bwrap` and breaks
git.**  Symptoms: `Device or resource busy` when git tries to write
`.git/config`, branch tracking info, hook config, etc.

The reason: `bwrap` `--ro-bind`s specific protected paths (e.g.
`.git/config`, `.git/hooks/`) over an otherwise-writable workspace.
On macOS sandbox-exec returns EACCES for the same protection; on
Linux you get EROFS / EBUSY instead, and git surfaces these as
"Device or resource busy".

`--dangerously-skip-permissions` only suppresses permission prompts;
the `bwrap` filesystem-protection layer runs independently.

Fix: delete `.claude/settings.local.json` in the VM-side checkout
(the `permissions.allow` list inside is moot under
`--dangerously-skip-permissions` anyway).  Exit + re-launch any
running VM Claude session to pick up the change.

To confirm whether bwrap is the culprit in a running session, run
inside the Claude shell (prefix with `!` to run as a shell command):

    !cat /proc/$$/mountinfo | grep ' /repo'

If you see per-file `ro virtiofs` entries under `/repo/.git/*`, that's
the bwrap sandbox.  Worktree isolation (a different mode, below)
would put the *whole* `/repo` on a single ro mount.

## Don't use Claude Code's Agent worktree isolation inside the VM

Claude Code's `Agent` tool accepts an `isolation: "worktree"` mode
that bind-mounts `/repo` read-only and overlays the agent's working
directory as rw.  Inside this VM that mode is broken: git's per-
worktree state lives at `/repo/.git/worktrees/<name>/`, which sits
on the read-only side of the bind mount.  Any git operation that
needs to write a lockfile or update config there fails with
`Read-only file system` (EROFS).  The tell: the failing path
contains `.git/worktrees/`.

Use plain git worktrees instead (see "Daily workflow" above for the
`git worktree add` recipe).  Sub-agents launched inside a Claude
session are fine **as long as you don't pass `isolation: "worktree"`**
— default isolation (no overlay) works.

## Maintenance

All maintenance happens as the default user from a macOS terminal.
The `claude` user has no sudo, so attempts to do these from inside
a Claude session would fail.

### Add a new apt package

Either:

  - Edit the setup script, add the package to the `apt-get install`
    list, and re-run.  (Recommended; captures the change for next
    time.)
  - Or one-shot: stop the firewall, install, restart the firewall:

        orb -m hol4 sudo systemctl stop nftables
        orb -m hol4 sudo apt-get install -y <package>
        orb -m hol4 sudo systemctl start nftables
        orb -m hol4 python3 -c "import socket; print(socket.gethostbyname('api.anthropic.com'))"

(The final `gethostbyname` warms the dnsmasq cache so the post-restart
firewall has IPs in the allowlist.)

### Allow a new outbound hostname

Edit the setup script, add to the dnsmasq section:

    nftset=/<hostname>/4#inet#filter#anthropic_ips_v4
    nftset=/<hostname>/6#inet#filter#anthropic_ips_v6

(Re-using the existing set names is fine even though they're named
`anthropic_ips_*`.)  Re-run the script.

### Update Claude Code

    orb -m hol4 sudo systemctl stop nftables
    orb -m hol4 sudo npm install -g @anthropic-ai/claude-code
    orb -m hol4 sudo systemctl start nftables

### Wipe the VM and start fresh

    orbctl delete hol4
    ./developers/claude/setup-locked-vm.sh

The macOS-side repo is untouched.  You will need to log in to Claude
again (device-flow as the `claude` user).

## Observing what's happening in the VM

  - **OrbStack.app GUI:** the Machines pane shows state, file
    browser, resource usage.
  - **`orbctl top`** — live activity monitor (CPU/RAM per VM).
  - **`orbctl info hol4`** — VM details.
  - **`orb -m hol4 htop`** — process view inside the VM (or `top`).
  - **A second shell while Claude is running:** `orb -m hol4` again
    from another terminal.  It's a separate process, doesn't disturb
    the Claude session.  You'll land as your default user; switch to
    `claude` with `sudo -u claude -H -s` if you need claude's
    perspective on something.

## Security model

### Trust layers

  - **macOS host:** trusts (a) git pushes you initiate, (b) editor
    file writes inside your macOS-side checkout, (c) anything you
    explicitly run in a macOS terminal.
  - **VM, as the default user:** trusted for maintenance.  Full sudo,
    NOPASSWD.  Use this for `git worktree add`, apt installs,
    stopping the firewall, etc.
  - **VM, as `claude`:** untrusted for privilege.  Can read/write
    `/repo`, can't sudo, can't disable the firewall, can't read
    other users' home directories.  This is where Claude Code runs.

### Enforced outside the guest (sudo cannot bypass)

  - **Mount restriction:** virtio-fs only exposes `/repo`.  No other
    macOS paths are visible, regardless of in-guest privilege.  Even
    in-VM root can't see `~/.ssh`, `~/.aws`, etc.
  - **`--isolate-network`:** VM cannot reach other OrbStack VMs or
    macOS loopback IPs.  Enforced at the OrbStack network-namespace
    layer.

### Enforced inside the guest

  - **Egress firewall (`nftables` + `dnsmasq`):** HTTPS to
    `api.anthropic.com` + `claude.ai` only, plus loopback and DNS to
    1.1.1.1.  Bypassable by `sudo systemctl stop nftables` — so we
    keep that out of Claude's reach by running Claude as the no-sudo
    `claude` user.
  - **VM ext4 filesystem perms:** `/etc/`, `/home/<default-user>/`,
    `/etc/sudoers.d/` etc. follow normal Linux semantics.  Claude
    can't write `/etc/nftables.conf`, can't read `/etc/sudoers`,
    can't read the default user's home.

### Empirical confirmation

Running as `claude` against the VM's ext4 and the `/repo` mount, the
following holds:

| target                                | claude can read?  | claude can write?               |
|---------------------------------------|-------------------|---------------------------------|
| `/etc/passwd` (0644 root:root)        | yes (world-read)  | no — EACCES                     |
| `/etc/nftables.conf` (0755 root:root) | yes (world-read)  | no — EACCES                     |
| `/etc/sudoers` (0440 root:root)       | no — EACCES       | no — EACCES                     |
| new file in `/etc/`                   | n/a               | no — EACCES                     |
| `sudo -n …`                           | n/a               | "password required" (claude not |
|                                       |                   | in sudoers, can't escalate)     |
| `nft list ruleset` (no sudo)          | n/a               | EPERM — needs CAP_NET_ADMIN     |
| anywhere under `/repo`                | yes (permissive)  | yes (permissive)                |

### Why `/repo` is permissive

OrbStack's virtio-fs ignores in-guest permissions on host-mounted
directories: any in-VM user can read/write/delete anywhere on
`/repo`, regardless of displayed perms or group membership.  All
writes appear on macOS as the default (mount-owning) user.

This is **not an OrbStack-specific surprise** — virtio-fs's design
assumption is that the entire guest VM is a single trust domain.
See OrbStack issue
[#1587](https://github.com/orbstack/orbstack/issues/1587) and
docker/for-mac
[#6243](https://github.com/docker/for-mac/issues/6243) for the
upstream-acknowledged versions.  In practice it means we rely on
the sudo boundary (not in-guest fs perms) as the real isolation.

Corollary worth knowing: the perm boundary on `/repo` is "what does
virtiofsd-as-host-user see on the host", not "what does the in-guest
user see".  A root-owned macOS file inside the host mount would be
inaccessible to *any* in-guest user including in-VM root, because
virtiofsd has no access on the host side.  The VM's own ext4 disk
(`/etc`, `/home`, `/usr`) follows normal Linux semantics — that's
where our actual security-relevant files live.

### What this does NOT defend against

  - Claude reading anything currently in `/repo`.  If sensitive data
    leaks into the tree (embedded tokens in `.git/config`, stray
    `.env`, etc.), Claude has access.  Mitigation: keep `/repo`
    clean.
  - Claude spawning long-running processes that survive its session.
    Not a security issue per se, but worth knowing.
  - Bugs in OrbStack's `--isolate-network` / virtio-fs isolation.
    Those are the trust roots — if they break, everything breaks.

## Troubleshooting

### Probe says `api.anthropic.com FAIL`

The firewall may have been written without the upstream-DNS allow
rule.  Verify:

    orb -m hol4 sudo nft list chain inet filter output

You should see allow rules for `udp dport 53 ip daddr 1.1.1.1` and
`udp dport 53 ip daddr 1.0.0.1`.  If missing, re-run the setup
script.

### Apt install during setup fails with `Temporary failure resolving`

The bootstrap phase runs **before** the lockdown, so it needs full
network.  Check `orb -m hol4 cat /etc/resolv.conf` — if it points at
`127.0.0.1` already, the lockdown applied prematurely.  Reset:

    orb -m hol4 sudo systemctl stop nftables dnsmasq
    orb -m hol4 sudo bash -c 'echo "nameserver 1.1.1.1" > /etc/resolv.conf'
    # then re-run the setup script

### Claude says "Network error" or hangs

Confirm dnsmasq is up and the nftables set has IPs for
`api.anthropic.com`:

    orb -m hol4 sudo systemctl status dnsmasq nftables
    orb -m hol4 sudo nft list set inet filter anthropic_ips_v4

If the set is empty, force a lookup to populate it:

    orb -m hol4 python3 -c "import socket; print(socket.gethostbyname('api.anthropic.com'))"

### Git fails with `Device or resource busy` on `.git/config`

The `bwrap` sandbox is protecting `.git/config` and `.git/hooks/` —
see "Don't ship a `sandbox` stanza" above.  Fix: delete
`.claude/settings.local.json` in the VM-side checkout, then exit +
re-launch the VM Claude session.

### Git fails with `Read-only file system` on `.git/worktrees/<name>/`

Claude Code's Agent tool was invoked with `isolation: "worktree"` —
see "Don't use Claude Code's Agent worktree isolation" above.  Fix:
in the current session, don't pass that isolation mode; use plain
git worktrees instead.
