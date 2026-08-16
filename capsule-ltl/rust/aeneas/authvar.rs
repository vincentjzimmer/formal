// authvar.rs — idiomatic, safe, sequential Rust for the Aeneas pipeline,
// instance #2: UEFI time-based authenticated variables.
//
// Same shape as capsule.rs: a deterministic good-path `advance` whose Aeneas
// extraction to Lean is proved to refine the abstract auth-var `advance`
// (UefiAuthVar.advance). Hardware I/O and the signature check stay a trusted
// oracle; this models the DECISION LOGIC (timestamp anti-replay + authority).
//
// TOOLCHAIN: see extract.sh (charon rustc --preset=aeneas; aeneas -backend lean)

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Phase {
    Idle,
    Received,
    Verifying,
    Written,
    Refused,
}

#[derive(Clone, Copy)]
pub struct St {
    pub phase: Phase,
    pub stored_time: u64,      // timestamp of the stored value (monotone observable)
    pub req_present: bool,
    pub req_time: u64,         // adversary-chosen request timestamp
    pub req_authorized: bool,  // signer authorized (trusted oracle)
}

// The verification decision: written iff authorized AND strictly newer.
pub fn verify(s: St) -> St {
    if s.phase == Phase::Verifying {
        if s.req_authorized && s.stored_time < s.req_time {
            // write: advance the stored timestamp (only time-changing path)
            St { phase: Phase::Written, stored_time: s.req_time, ..s }
        } else {
            // refuse: replay (not newer) or unauthorized
            St { phase: Phase::Refused, req_present: false, ..s }
        }
    } else {
        s
    }
}

// The forced good-path step before verification.
pub fn begin_verify(s: St) -> St {
    if s.phase == Phase::Received {
        St { phase: Phase::Verifying, ..s }
    } else {
        s
    }
}

// Deterministic good-path advance: Received -> Verifying -> Written.
pub fn advance(s: St) -> St {
    match s.phase {
        Phase::Received => begin_verify(s),
        Phase::Verifying => verify(s),
        _ => s,
    }
}
