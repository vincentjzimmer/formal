#!/usr/bin/env bash
# Extract rust/aeneas/capsule.rs to a Lean model via Charon + Aeneas, both
# built from the Aeneas flake (version-matched). Produces Capsule.lean, which
# refine_capsule.lean's hand-written `advance` is meant to match.
#
# Charon/Aeneas are NOT in nixpkgs; build them from the Aeneas flake (use
# git+https to avoid GitHub API rate limits):
#   nix build "git+https://github.com/AeneasVerif/aeneas#charon"         --no-link --print-out-paths
#   nix build "git+https://github.com/AeneasVerif/aeneas#aeneas-release" --no-link --print-out-paths
# then point CHARON / AENEAS at the resulting bin/ directories (or `nix run`).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
cd "$HERE"

CHARON="${CHARON:-charon}"
AENEAS="${AENEAS:-aeneas}"
DEST="${DEST:-$HERE/lean}"
mkdir -p "$DEST"

# Charon needs a cargo crate; create a throwaway one around capsule.rs.
if [ ! -f Cargo.toml ]; then
  cat > Cargo.toml <<'TOML'
[package]
name = "capsule"
version = "0.1.0"
edition = "2021"

[lib]
path = "capsule.rs"
TOML
fi

echo "== Charon: Rust -> LLBC =="
# `charon` drives cargo; emits capsule.llbc
$CHARON cargo -- --lib

echo "== Aeneas: LLBC -> Lean =="
# -backend lean : emit a Lean model; -dest : output directory
$AENEAS -backend lean capsule.llbc -dest "$DEST"

echo
echo "Generated Lean model in $DEST. Compare its extracted state machine to the"
echo "hand-written 'advance' in ../../refine_capsule.lean; once they agree, the"
echo "refinement theorems (step_advance, detRun_isRun, responsiveness_det,"
echo "safety_authentic_det) witness liveness+safety on the EXTRACTED code."
