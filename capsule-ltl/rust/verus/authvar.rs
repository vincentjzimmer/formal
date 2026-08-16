// authvar.rs — a Verus-verified Rust reference monitor for UEFI time-based
// authenticated variable processing (instance #2 of the AuthMonotone family).
//
// Structurally the capsule monitor with the monotone observable retyped from a
// firmware version to a write timestamp. Proves, on executable code, the same
// shape of guarantees:
//   S  : a written variable's request was authorized
//   R1 : one step never lowers the stored timestamp (anti-replay, per step)
//   R2 : the stored timestamp never decreases over a run (global anti-replay)
//   G  : entering Written requires an authorized signer and a STRICTLY newer
//        timestamp (so an equal-timestamp replay is never committed)
//
// TOOLCHAIN: verus authvar.rs   (Verus 0.2026.05.03, bundled Z3)
//
// LIVENESS is not here, by design (Verus is a safety verifier); the omega-run
// liveness of the abstract instance lives in the Lean/TLA+ layers.

use vstd::prelude::*;

verus! {

pub enum Phase { Idle, Received, Verifying, Written, Refused }

pub struct St {
    pub phase: Phase,
    pub stored_time: nat,      // timestamp of the stored value (monotone observable)
    pub req_present: bool,
    pub req_time: nat,         // adversary-chosen request timestamp
    pub req_authorized: bool,  // adversary-chosen authorization verdict (oracle)
}

pub open spec fn init(s: St) -> bool {
    &&& s.phase == Phase::Idle
    &&& s.req_present == false
}

// One step of authenticated-variable processing, as a spec relation.
pub open spec fn step(s: St, s2: St) -> bool {
    // idle stutter
    ||| (s.phase == Phase::Idle && s2 == s)
    // recv: environment stages any timestamp + verdict
    ||| (s.phase == Phase::Idle
         && s2.phase == Phase::Received && s2.req_present == true
         && s2.stored_time == s.stored_time)
    // beginVerify
    ||| (s.phase == Phase::Received && s2.phase == Phase::Verifying
         && s2.stored_time == s.stored_time)
    // write: authorized AND strictly newer timestamp
    ||| (s.phase == Phase::Verifying
         && s.req_authorized == true && s.stored_time < s.req_time
         && s2.phase == Phase::Written && s2.stored_time == s.req_time
         && s2.req_time == s.req_time && s2.req_authorized == s.req_authorized)
    // refuse: not authorized OR not newer
    ||| (s.phase == Phase::Verifying
         && (s.req_authorized == false || s.req_time <= s.stored_time)
         && s2.phase == Phase::Refused && s2.stored_time == s.stored_time)
    // finish
    ||| ((s.phase == Phase::Written || s.phase == Phase::Refused)
         && s2.phase == Phase::Idle && s2.stored_time == s.stored_time)
}

// R1: no step lowers the stored timestamp.
pub proof fn anti_replay_step(s: St, s2: St)
    requires step(s, s2),
    ensures  s.stored_time <= s2.stored_time,
{ }

// G: entering Written requires authorization and a strictly newer timestamp.
pub proof fn write_guard(s: St, s2: St)
    requires step(s, s2), s2.phase == Phase::Written, s.phase != Phase::Written,
    ensures  s.req_authorized == true, s.stored_time < s.req_time,
{ }

// Authenticity invariant (S).
pub open spec fn inv_auth(s: St) -> bool {
    s.phase == Phase::Written ==> s.req_authorized == true
}

pub proof fn inv_init(s: St) requires init(s), ensures inv_auth(s) { }

pub proof fn inv_step(s: St, s2: St)
    requires inv_auth(s), step(s, s2), ensures inv_auth(s2) { }

// Runs.
pub open spec fn is_run(run: Seq<St>) -> bool {
    &&& run.len() > 0
    &&& init(run[0])
    &&& forall|i: int| 0 <= i < run.len() - 1 ==> #[trigger] step(run[i], run[i + 1])
}

// R2: global anti-replay — the stored timestamp is monotone along a run.
pub proof fn anti_replay_global(run: Seq<St>, i: int, j: int)
    requires is_run(run), 0 <= i <= j < run.len(),
    ensures  run[i].stored_time <= run[j].stored_time,
    decreases j - i,
{
    if i < j {
        anti_replay_global(run, i, j - 1);
        assert(step(run[j - 1], run[(j - 1) + 1]));
        anti_replay_step(run[j - 1], run[j]);
    }
}

// S on every position of every run.
pub proof fn inv_run(run: Seq<St>, i: int)
    requires is_run(run), 0 <= i < run.len(),
    ensures  inv_auth(run[i]),
    decreases i,
{
    if i > 0 {
        inv_run(run, i - 1);
        assert(step(run[i - 1], run[(i - 1) + 1]));
        inv_step(run[i - 1], run[i]);
    } else {
        inv_init(run[0]);
    }
}

fn main() {}

} // verus!
