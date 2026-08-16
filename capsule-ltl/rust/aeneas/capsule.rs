// capsule.rs — idiomatic, safe, sequential Rust for the Aeneas pipeline.
//
// Aeneas verifies Rust *indirectly*: Charon extracts this crate to LLBC, and
// Aeneas translates the safe/unsafe-free subset into a PURE FUNCTIONAL model in
// Lean (also Coq/F*). We then prove the capsule-update properties about that
// generated model — and, uniquely for this project, can reuse the EXISTING LTL
// embedding from ltl_capsule.lean to state the temporal properties on the
// extracted `step` function. That makes the Rust code, the abstract model, and
// the proofs one connected artifact in a single prover (refinement-to-Lean).
//
// Constraints to keep Aeneas happy: no `unsafe`, no raw pointers, no
// concurrency, no trait-object dynamism. Hardware I/O (flash write, signature
// check) is OUT — it stays behind a trusted boundary, exactly the sigOK-oracle
// decomposition of the foundational proof. So this models the DECISION LOGIC.
//
// TOOLCHAIN (neither is in nixpkgs):
//   # Charon (frontend):  https://github.com/AeneasVerif/charon
//   charon --dest llbc cargo
//   # Aeneas (extractor): https://github.com/AeneasVerif/aeneas
//   aeneas -backend lean capsule.llbc -dest ../../ltl_capsule_extracted

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Phase {
    Idle,
    CapsuleStaged,
    PostReset,
    Authenticating,
    Applied,
    Rejected,
}

#[derive(Clone, Copy)]
pub struct St {
    pub phase: Phase,
    pub fw_version: u64,
    pub capsule_present: bool,
    pub capsule_version: u64,
    pub capsule_sig_valid: bool,
    pub reset_occurred: bool,
}

// The decision the firmware makes at authentication time. This is the function
// Aeneas will extract; the proof obligation is that its `Applied` outcome
// implies the guard, and that it never lowers fw_version.
pub fn authenticate(s: St) -> St {
    if s.phase == Phase::Authenticating {
        if s.capsule_sig_valid && s.fw_version < s.capsule_version {
            // apply: bump the running version (the only version-changing path)
            St { phase: Phase::Applied, fw_version: s.capsule_version, ..s }
        } else {
            // reject: anti-rollback or bad signature
            St { phase: Phase::Rejected, capsule_present: false, ..s }
        }
    } else {
        s
    }
}

// The forced good-path steps (reset, beginAuth) as pure functions. Composing
// reset ; begin_auth ; authenticate on a good staged state reaches Applied in
// three steps — the executable witness behind liveness property L. Aeneas
// extracts these; the *liveness* statement itself is proved in the Lean layer
// over the run built from these functions (see README).
pub fn reset(s: St) -> St {
    if s.phase == Phase::CapsuleStaged {
        St { phase: Phase::PostReset, reset_occurred: true, ..s }
    } else {
        s
    }
}

pub fn begin_auth(s: St) -> St {
    if s.phase == Phase::PostReset {
        St { phase: Phase::Authenticating, ..s }
    } else {
        s
    }
}

// A single deterministic good-path advance: one function whose iteration is the
// run. Determinism is the key difference from the TLA+ model and is what makes
// the bounded liveness witness expressible as plain recursion in the backend.
pub fn advance(s: St) -> St {
    match s.phase {
        Phase::CapsuleStaged => reset(s),
        Phase::PostReset => begin_auth(s),
        Phase::Authenticating => authenticate(s),
        _ => s,
    }
}
