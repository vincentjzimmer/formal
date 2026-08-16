// secureboot.rs — idiomatic, safe, sequential Rust for the Aeneas pipeline,
// instance #3: UEFI Secure Boot dbx update.
//
// Aeneas faithfully translates user-defined recursive types and pure recursive
// functions, but axiomatizes std collection methods like `Vec::append` (no
// semantic model). To keep the refinement axiom-clean, we model dbx as a
// hand-rolled cons-list `Revs` and `append` as a pure recursive function —
// Aeneas extracts both exactly, and the extracted `append` matches the abstract
// `List.append` used by UefiSecureBoot. This is the executable, non-strict,
// set-valued instance: `update` APPENDS (append-only policy).
//
// TOOLCHAIN: see extract.sh (charon rustc --preset=aeneas; aeneas -backend lean)

#[derive(Clone, PartialEq, Eq)]
pub enum Revs {
    Nil,
    Cons(u64, Box<Revs>),
}

// Pure recursive append (Aeneas extracts this faithfully, no std axiom).
pub fn append(a: Revs, b: Revs) -> Revs {
    match a {
        Revs::Nil => b,
        Revs::Cons(h, t) => Revs::Cons(h, Box::new(append(*t, b))),
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum Phase {
    Idle,
    Received,
    Verifying,
    Updated,
    Refused,
}

pub struct St {
    pub phase: Phase,
    pub dbx: Revs,              // revoked image hashes (append-only cons-list)
    pub req_present: bool,
    pub req_revs: Revs,         // revocations the staged request would add
    pub req_authorized: bool,   // KEK-signed (trusted oracle)
}

// Policy-update decision: append the requested revocations iff authorized.
pub fn update(s: St) -> St {
    if s.phase == Phase::Verifying {
        if s.req_authorized {
            // append-only: extend dbx (the only dbx-changing path; never removes)
            St {
                phase: Phase::Updated,
                dbx: append(s.dbx, s.req_revs.clone()),
                req_revs: s.req_revs,
                req_present: s.req_present,
                req_authorized: s.req_authorized,
            }
        } else {
            St { phase: Phase::Refused, req_present: false, ..s }
        }
    } else {
        s
    }
}

pub fn begin_verify(s: St) -> St {
    if s.phase == Phase::Received {
        St { phase: Phase::Verifying, ..s }
    } else {
        s
    }
}

// Deterministic good-path advance: Received -> Verifying -> Updated.
pub fn advance(s: St) -> St {
    match s.phase {
        Phase::Received => begin_verify(s),
        Phase::Verifying => update(s),
        _ => s,
    }
}
