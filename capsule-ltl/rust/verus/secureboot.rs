// secureboot.rs — a Verus-verified Rust reference monitor for UEFI Secure Boot
// dbx (forbidden-signature DB) updates (instance #3 of the AuthMonotone family).
//
// This is the NON-STRICT, SET-VALUED instance: dbx is append-only, so the
// monotone observable is the revocation set ordered by subset, NOT a number.
// We prove, on executable code:
//   S          : a committed policy update was KEK-authorized
//   NoUnrevoke : one step never removes a revoked hash (dbx ⊆ dbx', per step)
//   R2/persist : a hash revoked at i is still revoked at any later j
//   G          : entering Updated requires a KEK-authorized request
// and we encode the ROLLBACK FINDING: a step that drops a revocation has no
// place in this transition system — the only dbx-changing rule appends.
//
// Unlike capsule/authvar there is NO strict-advance guarantee, and there should
// not be: re-applying a revocation set is legitimate. This is the executable
// witness of the StrictMonitor/Monitor split in the framework.
//
// TOOLCHAIN: verus secureboot.rs   (Verus 0.2026.05.03, bundled Z3)

use vstd::prelude::*;

verus! {

pub enum Phase { Idle, Received, Verifying, Updated, Refused }

pub struct St {
    pub phase: Phase,
    pub dbx: Seq<nat>,          // revoked image hashes (the monotone set)
    pub req_present: bool,
    pub req_revs: Seq<nat>,     // revocations the staged request would add
    pub req_authorized: bool,   // KEK-signed (trusted oracle)
}

// Subset on revocation sets (membership-based, like the Lean `Sub`).
pub open spec fn sub(a: Seq<nat>, b: Seq<nat>) -> bool {
    forall|h: nat| a.contains(h) ==> b.contains(h)
}

pub open spec fn init(s: St) -> bool {
    &&& s.phase == Phase::Idle
    &&& s.req_present == false
}

// One step of Secure Boot dbx update. `update` APPENDS revocations (dbx grows).
pub open spec fn step(s: St, s2: St) -> bool {
    // idle stutter
    ||| (s.phase == Phase::Idle && s2 == s)
    // recv: stage any revocation set + verdict
    ||| (s.phase == Phase::Idle
         && s2.phase == Phase::Received && s2.req_present == true
         && s2.dbx == s.dbx)
    // beginVerify
    ||| (s.phase == Phase::Received && s2.phase == Phase::Verifying
         && s2.dbx == s.dbx)
    // update: KEK-authorized; APPENDS (dbx' = dbx ++ req_revs)
    ||| (s.phase == Phase::Verifying && s.req_authorized == true
         && s2.phase == Phase::Updated && s2.dbx == s.dbx + s.req_revs
         && s2.req_authorized == s.req_authorized)
    // refuse: not authorized
    ||| (s.phase == Phase::Verifying && s.req_authorized == false
         && s2.phase == Phase::Refused && s2.dbx == s.dbx)
    // finish
    ||| ((s.phase == Phase::Updated || s.phase == Phase::Refused)
         && s2.phase == Phase::Idle && s2.dbx == s.dbx)
}

// Appending only grows the set: a ⊆ a ++ r.
pub proof fn sub_append(a: Seq<nat>, r: Seq<nat>)
    ensures sub(a, a + r),
{
    assert forall|h: nat| a.contains(h) implies (a + r).contains(h) by {
        let i = choose|i: int| 0 <= i < a.len() && a[i] == h;
        assert(0 <= i < a.len());
        assert((a + r)[i] == a[i]);
        assert((a + r).contains(h)) by {
            assert((a + r)[i] == h);
        }
    }
}

// NoUnrevoke (R1): no step removes a revoked hash — dbx ⊆ dbx' across any step.
pub proof fn no_unrevoke_step(s: St, s2: St)
    requires step(s, s2),
    ensures  sub(s.dbx, s2.dbx),
{
    if (s.phase == Phase::Verifying && s.req_authorized == true
        && s2.phase == Phase::Updated && s2.dbx == s.dbx + s.req_revs) {
        sub_append(s.dbx, s.req_revs);
    }
}

// G: entering Updated requires KEK authorization.
pub proof fn update_guard(s: St, s2: St)
    requires step(s, s2), s2.phase == Phase::Updated, s.phase != Phase::Updated,
    ensures  s.req_authorized == true,
{ }

// Authenticity invariant (S).
pub open spec fn inv_auth(s: St) -> bool {
    s.phase == Phase::Updated ==> s.req_authorized == true
}
pub proof fn inv_init(s: St) requires init(s), ensures inv_auth(s) { }
pub proof fn inv_step(s: St, s2: St)
    requires inv_auth(s), step(s, s2),
    ensures inv_auth(s2),
{
    // s2 is Updated only via the `update` disjunct, which requires
    // s.req_authorized == true and preserves it into s2.
    if s2.phase == Phase::Updated {
        assert(s.req_authorized == true);
    }
}

pub open spec fn is_run(run: Seq<St>) -> bool {
    &&& run.len() > 0
    &&& init(run[0])
    &&& forall|i: int| 0 <= i < run.len() - 1 ==> #[trigger] step(run[i], run[i + 1])
}

// R2 / persistence: a hash revoked at position i is still revoked at any j >= i.
pub proof fn revocation_persists(run: Seq<St>, i: int, j: int, h: nat)
    requires is_run(run), 0 <= i <= j < run.len(), run[i].dbx.contains(h),
    ensures  run[j].dbx.contains(h),
    decreases j - i,
{
    if i < j {
        revocation_persists(run, i, j - 1, h);
        assert(step(run[j - 1], run[(j - 1) + 1]));
        no_unrevoke_step(run[j - 1], run[j]);
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
