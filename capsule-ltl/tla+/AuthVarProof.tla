---------------------------- MODULE AuthVarProof ----------------------------
(***************************************************************************)
(* TLAPS unbounded re-proof for the authenticated-variable instance        *)
(* (Lean instance #2). Like CapsuleProof.tla, this discharges the safety    *)
(* inductive invariant and the anti-replay monotonicity DEDUCTIVELY, over   *)
(* all timestamps in Nat (no MaxTime bound), via the SMT/Zenon backends.    *)
(*                                                                         *)
(*   InitInv  : Init => Inv                                                 *)
(*   NextInv  : Inv /\ [Next]_vars => Inv'    (S inductive step)            *)
(*   NoReplay : TypeOK /\ [Next]_vars => storedTime' >= storedTime  (R1)    *)
(***************************************************************************)
EXTENDS Naturals, TLAPS

VARIABLES phase, storedTime, reqPresent, reqTime, reqAuthorized
vars == << phase, storedTime, reqPresent, reqTime, reqAuthorized >>

Phases == { "Idle", "Received", "Verifying", "Written", "Refused" }

TypeOK ==
    /\ phase         \in Phases
    /\ storedTime    \in Nat
    /\ reqPresent    \in BOOLEAN
    /\ reqTime       \in Nat
    /\ reqAuthorized \in BOOLEAN

Init ==
    /\ phase         = "Idle"
    /\ reqPresent    = FALSE
    /\ storedTime    \in Nat
    /\ reqTime       \in Nat
    /\ reqAuthorized \in BOOLEAN

Idle == phase = "Idle" /\ UNCHANGED vars

Recv ==
    /\ phase = "Idle"
    /\ \E t \in Nat, a \in BOOLEAN : reqTime' = t /\ reqAuthorized' = a
    /\ phase'      = "Received"
    /\ reqPresent' = TRUE
    /\ UNCHANGED storedTime

BeginVerify ==
    /\ phase = "Received"
    /\ phase' = "Verifying"
    /\ UNCHANGED << storedTime, reqPresent, reqTime, reqAuthorized >>

Write ==
    /\ phase = "Verifying"
    /\ reqAuthorized = TRUE
    /\ storedTime < reqTime
    /\ phase'      = "Written"
    /\ storedTime' = reqTime
    /\ UNCHANGED << reqPresent, reqTime, reqAuthorized >>

Refuse ==
    /\ phase = "Verifying"
    /\ (reqAuthorized = FALSE \/ reqTime <= storedTime)
    /\ phase'      = "Refused"
    /\ reqPresent' = FALSE
    /\ UNCHANGED << storedTime, reqTime, reqAuthorized >>

Finish ==
    /\ phase \in { "Written", "Refused" }
    /\ phase'      = "Idle"
    /\ reqPresent' = FALSE
    /\ UNCHANGED << storedTime, reqTime, reqAuthorized >>

Next == Idle \/ Recv \/ BeginVerify \/ Write \/ Refuse \/ Finish

\* ---- invariants -----------------------------------------------------------
\* S (authenticity): a written variable's request was authorized.
InvAuth == phase = "Written" => reqAuthorized = TRUE
Inv == TypeOK /\ InvAuth

USE DEF Phases

THEOREM InitType == Init => TypeOK
  BY DEF Init, TypeOK

THEOREM NextType == TypeOK /\ [Next]_vars => TypeOK'
  BY DEF TypeOK, Next, vars, Idle, Recv, BeginVerify, Write, Refuse, Finish

THEOREM InitInv == Init => Inv
  BY DEF Init, Inv, TypeOK, InvAuth

\* The inductive step for the authenticity invariant, over all of Nat.
\* LISTING:avnextinv:begin
THEOREM NextInv == Inv /\ [Next]_vars => Inv'
  BY DEF Inv, TypeOK, InvAuth, Next, vars,
         Idle, Recv, BeginVerify, Write, Refuse, Finish
\* LISTING:avnextinv:end

\* R1: anti-replay monotonicity. Only Write changes storedTime, under
\* storedTime < reqTime, so the timestamp never decreases -- for ALL Nat.
THEOREM NoReplay ==
  ASSUME TypeOK, [Next]_vars
  PROVE  storedTime' >= storedTime
  BY DEF TypeOK, Next, vars, Idle, Recv, BeginVerify, Write, Refuse, Finish

=============================================================================
