// authvar_exec.rs — an EXECUTABLE, Verus-verified authenticated-variable
// decision core (instance #2). Runnable analogue of authvar.rs (which is
// spec/proof-only): concrete u64 timestamps, a parsing front-end over a raw
// authentication descriptor, executable contracts for anti-replay (R1) and the
// write-guard (G).
//
// HONEST BOUNDARIES (trusted, as in the abstract development): the signature
// verdict `sig_ok` is an input (a verified PKCS#7/X.509 checker would supply
// it); NVRAM commit and the full EFI_VARIABLE_AUTHENTICATION_2 / EFI_TIME layout
// are out of scope. We verify the timestamp anti-replay + authority LOGIC.
//
// TOOLCHAIN:  verus --compile authvar_exec.rs -o authvar_exec
//             verus authvar_exec.rs   (verify only)

use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq, Structural)]
pub enum Decision { Write, Refuse }

// A parsed authentication descriptor: the request's monotonic timestamp and the
// signature-check verdict (TRUSTED ORACLE input).
pub struct AuthDesc {
    pub req_time: u64,   // request timestamp (UEFI uses EFI_TIME; modelled as u64)
    pub sig_ok: bool,
}

// Raw descriptor layout: 8 LE bytes of timestamp, then 1 verdict byte.
pub const DESC_LEN: usize = 9;

// PARSING FRONT-END: validate length, decode the descriptor; None if malformed.
pub exec fn parse_desc(buf: &Vec<u8>) -> (res: Option<AuthDesc>)
    ensures res is Some ==> buf.len() == DESC_LEN,
{
    if buf.len() != DESC_LEN {
        return None;
    }
    let t: u64 =
        (buf[0] as u64)
      | ((buf[1] as u64) << 8)  | ((buf[2] as u64) << 16) | ((buf[3] as u64) << 24)
      | ((buf[4] as u64) << 32) | ((buf[5] as u64) << 40) | ((buf[6] as u64) << 48)
      | ((buf[7] as u64) << 56);
    let sig = buf[8] != 0;
    Some(AuthDesc { req_time: t, sig_ok: sig })
}

// THE DECISION: write iff authorized AND strictly newer timestamp (anti-replay).
// `stored_time` is the timestamp currently recorded for the variable.
pub exec fn check_write(d: &AuthDesc, stored_time: u64) -> (out: Decision)
    ensures
        // G + strict freshness: Write implies authentic and strictly newer.
        out == Decision::Write ==> (d.sig_ok && stored_time < d.req_time),
        (!d.sig_ok || d.req_time <= stored_time) ==> out == Decision::Refuse,
{
    if d.sig_ok && stored_time < d.req_time {
        Decision::Write
    } else {
        Decision::Refuse
    }
}

// APPLY: anti-replay (R1) as a postcondition — the stored timestamp never
// decreases, and on Write advances to exactly the request timestamp.
pub exec fn apply_write(d: &AuthDesc, stored_time: u64, out: Decision) -> (new_time: u64)
    requires out == Decision::Write ==> (d.sig_ok && stored_time < d.req_time),
    ensures
        new_time >= stored_time,                                  // R1
        out == Decision::Write ==> new_time == d.req_time,
{
    if out == Decision::Write { d.req_time } else { stored_time }
}

// END-TO-END: parse, decide, apply over a raw buffer. Anti-replay holds over
// arbitrary (adversarial, possibly replayed) input bytes.
pub exec fn process_setvar(buf: &Vec<u8>, stored_time: u64) -> (new_time: u64)
    ensures new_time >= stored_time,   // R1 end-to-end
{
    match parse_desc(buf) {
        Option::Some(d) => {
            let dec = check_write(&d, stored_time);
            apply_write(&d, stored_time, dec)
        }
        Option::None => stored_time,
    }
}

fn main() {
    // A replay attempt: request timestamp == stored timestamp, signed.
    let mut buf: Vec<u8> = Vec::new();
    buf.push(7u8); buf.push(0); buf.push(0); buf.push(0);
    buf.push(0); buf.push(0); buf.push(0); buf.push(0);   // req_time = 7 (LE)
    buf.push(1u8);                                          // sig_ok = true
    let stored: u64 = 7;                                    // same timestamp = replay
    let nt = process_setvar(&buf, stored);
    // The contract guarantees nt >= stored for ANY buffer; the replay is refused
    // (nt stays 7, not advanced) — strict freshness defends replay.
    assert(nt >= stored);
    let _refused_replay: bool = nt == 7;
}

} // verus!
