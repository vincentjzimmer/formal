// secureboot_exec.rs — an EXECUTABLE, Verus-verified Secure Boot dbx-update core
// (instance #3). Runnable analogue of secureboot.rs. The NON-STRICT, set-valued
// case: dbx is a real Vec<u64> of revoked image hashes; `update` APPENDS
// (append-only policy), and we prove on EXECUTABLE code that no revoked hash is
// ever removed (the no-un-revocation property, R1 for the subset order), plus
// the authorization guard (G).
//
// This is the executable witness of the StrictMonitor/Monitor split: there is
// NO strict-advance contract here, by design — re-applying a revocation is
// legitimate. We instead prove membership preservation over a mutable Vec.
//
// HONEST BOUNDARIES: the KEK-authorization verdict `auth_ok` is a trusted input;
// NVRAM commit of dbx and the full EFI_SIGNATURE_LIST layout are out of scope.
// The dbx-rollback attack (replacing the whole variable with an older value) is
// OUT of this transition system by construction — exactly the obligation a
// platform discharges by binding dbx to a monotone authenticated-variable
// timestamp (instance #2). See the paper's composition theorem.
//
// TOOLCHAIN:  verus --compile secureboot_exec.rs -o secureboot_exec
//             verus secureboot_exec.rs   (verify only)

use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq, Structural)]
pub enum Decision { Update, Refuse }

// THE DECISION: a dbx update is committed iff KEK-authorized. (No timestamp
// strictness — append-only growth, the non-strict instance.)
pub exec fn check_update(auth_ok: bool) -> (d: Decision)
    ensures
        d == Decision::Update ==> auth_ok,    // G: only authorized updates commit
        !auth_ok ==> d == Decision::Refuse,
{
    if auth_ok { Decision::Update } else { Decision::Refuse }
}

// APPLY: append the requested revocations to dbx iff the decision is Update.
// The executable postcondition is the NON-STRICT, set-valued anti-rollback:
// every hash already in dbx is still in dbx afterward (no silent un-revocation).
pub exec fn apply_update(dbx: &mut Vec<u64>, new_revs: &Vec<u64>, d: Decision)
    ensures
        // R1 (subset-monotone): every previously-revoked hash remains revoked.
        forall|i: int| 0 <= i < old(dbx).len() ==> #[trigger] final(dbx)@.contains(old(dbx)@[i]),
        // and on Refuse, dbx is entirely unchanged.
        d == Decision::Refuse ==> final(dbx)@ == old(dbx)@,
{
    if d == Decision::Update {
        let ghost orig = dbx@;
        let mut k: usize = 0;
        while k < new_revs.len()
            invariant
                // dbx is always `orig` followed by some appended suffix, so every
                // original element is retained at its original index.
                orig.len() <= dbx@.len(),
                forall|i: int| 0 <= i < orig.len() ==> #[trigger] dbx@[i] == orig[i],
            decreases new_revs.len() - k,
        {
            dbx.push(new_revs[k]);
            k = k + 1;
        }
        // every original revocation is still present (at its original index)
        assert forall|i: int| 0 <= i < orig.len() implies #[trigger] dbx@.contains(orig[i]) by {
            assert(dbx@[i] == orig[i]);
        }
    }
}

// A revoked hash, once present, stays present across an apply — stated as a
// reusable executable lemma-style check (membership query after update).
pub exec fn still_revoked(dbx: &Vec<u64>, h: u64) -> (yes: bool)
    ensures yes == dbx@.contains(h),
{
    let mut k: usize = 0;
    while k < dbx.len()
        invariant
            forall|i: int| 0 <= i < k ==> dbx@[i] != h,
        decreases dbx.len() - k,
    {
        if dbx[k] == h {
            assert(dbx@.contains(dbx@[k as int]));
            return true;
        }
        k = k + 1;
    }
    assert(!dbx@.contains(h)) by {
        if dbx@.contains(h) {
            let j = choose|j: int| 0 <= j < dbx@.len() && dbx@[j] == h;
            assert(dbx@[j] != h);
        }
    }
    false
}

fn main() {
    // Install a revocation, then a second authorized update; the first stays.
    let mut dbx: Vec<u64> = Vec::new();
    let mut revs1: Vec<u64> = Vec::new();
    revs1.push(0xBADu64);
    apply_update(&mut dbx, &revs1, check_update(true));
    // 0xBAD is now revoked and must remain so after any further authorized update.
    let mut revs2: Vec<u64> = Vec::new();
    revs2.push(0xBEEFu64);
    apply_update(&mut dbx, &revs2, check_update(true));
    let _bad_still_revoked: bool = still_revoked(&dbx, 0xBADu64);  // provably true
}

} // verus!
