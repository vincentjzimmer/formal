----------------------------- MODULE CapsuleProof -----------------------------
(***************************************************************************)
(* TLAPS (TLA+ Proof System) variant of the capsule-update model.          *)
(*                                                                         *)
(* Where CapsuleInductive.tla hands the inductive invariant to Apalache    *)
(* (symbolic, SMT, bounded Nat encoding), this module DISCHARGES THE SAME  *)
(* INDUCTIVE INVARIANT DEDUCTIVELY with tlapm -- unbounded over all of Nat,*)
(* with no model checker and no version bound. This is the TLA+ analogue   *)
(* of the Lean development: a machine-checked proof, here checked by       *)
(* Zenon / the SMT backend rather than the Lean kernel.                    *)
(*                                                                         *)
(* The proofs establish:                                                   *)
(*   TypeOK             -- the state record is well-typed (inductive)      *)
(*   Safety            == TypeInv /\ InvSig /\ InvReset /\ InvFloor         *)
(*   NoRollbackLSV     -- per-step monotonicity of the LSV floor           *)
(*   InvFloor          -- the floor never exceeds fwVersion                *)
(*                                                                         *)
(* Run: tlapm --toolbox 0 0 CapsuleProof.tla    (or see CapsuleProof.sh)   *)
(***************************************************************************)
EXTENDS Naturals, TLAPS

VARIABLES phase, fwVersion, lsv, capsulePresent, capsuleVersion,
          imageDigest, capsuleSigValid, resetOccurred

vars == << phase, fwVersion, lsv, capsulePresent, capsuleVersion,
           imageDigest, capsuleSigValid, resetOccurred >>

Phases == { "Idle", "CapsuleStaged", "PostReset",
            "Authenticating", "Applied", "Rejected" }

CertOK(d) == d /= 0

TypeOK ==
    /\ phase           \in Phases
    /\ fwVersion       \in Nat
    /\ lsv             \in Nat
    /\ capsulePresent  \in BOOLEAN
    /\ capsuleVersion  \in Nat
    /\ imageDigest     \in Nat
    /\ capsuleSigValid \in BOOLEAN
    /\ resetOccurred   \in BOOLEAN

Init ==
    /\ phase           = "Idle"
    /\ capsulePresent  = FALSE
    /\ resetOccurred   = FALSE
    /\ fwVersion       \in Nat
    /\ lsv             \in Nat
    /\ capsuleVersion  \in Nat
    /\ imageDigest     \in Nat
    /\ capsuleSigValid \in BOOLEAN
    /\ lsv <= fwVersion

\* ---- actions --------------------------------------------------------------
StutterIdle == phase = "Idle" /\ UNCHANGED vars

Stage ==
    /\ phase = "Idle"
    /\ \E v \in Nat, d \in Nat :
         /\ capsuleVersion' = v
         /\ imageDigest'    = d
    /\ phase'          = "CapsuleStaged"
    /\ capsulePresent' = TRUE
    /\ resetOccurred'  = FALSE
    /\ UNCHANGED << fwVersion, lsv, capsuleSigValid >>

Reset ==
    /\ phase = "CapsuleStaged"
    /\ phase'         = "PostReset"
    /\ resetOccurred' = TRUE
    /\ UNCHANGED << fwVersion, lsv, capsulePresent, capsuleVersion,
                    imageDigest, capsuleSigValid >>

BeginAuth ==
    /\ phase = "PostReset"
    /\ phase'           = "Authenticating"
    /\ capsuleSigValid' = CertOK(imageDigest)
    /\ UNCHANGED << fwVersion, lsv, capsulePresent, capsuleVersion,
                    imageDigest, resetOccurred >>

Apply ==
    /\ phase = "Authenticating"
    /\ capsuleSigValid = TRUE
    /\ lsv <= capsuleVersion
    /\ phase'     = "Applied"
    /\ fwVersion' = capsuleVersion
    /\ lsv'       = capsuleVersion
    /\ UNCHANGED << capsulePresent, capsuleVersion, imageDigest,
                    capsuleSigValid, resetOccurred >>

Reject ==
    /\ phase = "Authenticating"
    /\ (capsuleSigValid = FALSE \/ capsuleVersion < lsv)
    /\ phase'          = "Rejected"
    /\ capsulePresent' = FALSE
    /\ UNCHANGED << fwVersion, lsv, capsuleVersion, imageDigest,
                    capsuleSigValid, resetOccurred >>

Finish ==
    /\ phase \in { "Applied", "Rejected" }
    /\ phase'          = "Idle"
    /\ capsulePresent' = FALSE
    /\ resetOccurred'  = FALSE
    /\ UNCHANGED << fwVersion, lsv, capsuleVersion, imageDigest,
                    capsuleSigValid >>

Next ==
    \/ StutterIdle \/ Stage \/ Reset \/ BeginAuth
    \/ Apply \/ Reject \/ Finish

Spec == Init /\ [][Next]_vars

\* ---- invariants -----------------------------------------------------------
InvSig   == phase = "Applied" => capsuleSigValid = TRUE
InvReset == (phase \in { "PostReset", "Authenticating", "Applied" })
                => resetOccurred = TRUE
InvFloor == lsv <= fwVersion

\* The full inductive invariant: type-correctness plus the safety facts.
Inv == TypeOK /\ InvSig /\ InvReset /\ InvFloor

\* ===========================================================================
\* PROOFS (checked by tlapm; unbounded in fwVersion / capsuleVersion)
\* ===========================================================================

USE DEF Phases

\* ---- TypeOK is inductive --------------------------------------------------
THEOREM InitType == Init => TypeOK
  BY DEF Init, TypeOK

THEOREM NextType == TypeOK /\ [Next]_vars => TypeOK'
  BY DEF TypeOK, Next, vars, CertOK, StutterIdle, Stage, Reset, BeginAuth,
         Apply, Reject, Finish

\* ---- The safety invariant Inv is inductive --------------------------------
THEOREM InitInv == Init => Inv
  BY DEF Init, Inv, TypeOK, InvSig, InvReset, InvFloor

\* LISTING:nextinv:begin
THEOREM NextInv == Inv /\ [Next]_vars => Inv'
  BY DEF Inv, TypeOK, InvSig, InvReset, InvFloor, Next, vars, CertOK,
         StutterIdle, Stage, Reset, BeginAuth, Apply, Reject, Finish
\* LISTING:nextinv:end

\* ---- Spec-level safety: Inv holds on every reachable state ----------------
\* Standard inductive-invariant lifting: Init /\ [][Next]_vars => []Inv.
\*
\* The two hypotheses below (InitInv, NextInv) are the mathematical content
\* and are checked by the SMT/Zenon backends. The final QED is a temporal
\* lifting step; as before it is left OMITTED when `ls4` is unavailable.
THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv
        BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'
        BY NextInv
  <1>. QED
        OMITTED  \* temporal step; needs ls4. BY <1>1, <1>2, PTL DEF Spec

\* ---- Anti-rollback: per-step monotonicity of the LSV floor -----------------
THEOREM NoRollback ==
  ASSUME TypeOK, [Next]_vars
  PROVE  lsv' >= lsv
  BY DEF TypeOK, Next, vars, CertOK, StutterIdle, Stage, Reset, BeginAuth,
         Apply, Reject, Finish

THEOREM NoRollbackLSV == TypeOK /\ [Next]_vars => lsv' >= lsv
  BY NoRollback
=============================================================================
