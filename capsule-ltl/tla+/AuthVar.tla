------------------------------- MODULE AuthVar -------------------------------
(***************************************************************************)
(* TLA+ model of UEFI time-based authenticated-variable processing, the    *)
(* TLC cross-validation layer for the Lean instance #2 (AuthVarInstance).  *)
(* One action per Lean `Step` constructor over a state vector identical to *)
(* the Lean `St`. The \E in Recv is the threat model: the environment picks *)
(* any timestamp and any authorization verdict (forged / replayed writes).  *)
(*                                                                         *)
(* REPLAY toggles a perturbation the Lean model abstracts away: a stale     *)
(* request whose timestamp equals the stored one (a replay). The anti-replay*)
(* guard (storedTime < reqTime) must reject it; with REPLAY the environment  *)
(* is additionally allowed to re-stage the last committed timestamp.         *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS MaxTime, REPLAY

Phases == { "Idle", "Received", "Verifying", "Written", "Refused" }
Times  == 0 .. MaxTime

VARIABLES phase, storedTime, reqPresent, reqTime, reqAuthorized
vars == << phase, storedTime, reqPresent, reqTime, reqAuthorized >>

TypeOK ==
    /\ phase         \in Phases
    /\ storedTime    \in Times
    /\ reqPresent    \in BOOLEAN
    /\ reqTime       \in Times
    /\ reqAuthorized \in BOOLEAN

Init ==
    /\ phase         = "Idle"
    /\ reqPresent    = FALSE
    /\ storedTime    \in Times
    /\ reqTime       \in Times
    /\ reqAuthorized \in BOOLEAN

Idle == phase = "Idle" /\ UNCHANGED vars

\* recv: environment stages any timestamp and any authorization verdict.
Recv ==
    /\ phase = "Idle"
    /\ \E t \in Times, a \in BOOLEAN :
         /\ reqTime'       = t
         /\ reqAuthorized' = a
    /\ phase'      = "Received"
    /\ reqPresent' = TRUE
    /\ UNCHANGED storedTime

BeginVerify ==
    /\ phase = "Received"
    /\ phase' = "Verifying"
    /\ UNCHANGED << storedTime, reqPresent, reqTime, reqAuthorized >>

\* write: authorized AND strictly newer timestamp (anti-replay).
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

\* PERTURBATION: an authorized replay -- re-stage the CURRENT stored timestamp
\* with a valid signature. The anti-replay guard must still refuse it
\* (reqTime = storedTime is not strictly newer), so S/R1 must survive.
Replay ==
    /\ REPLAY
    /\ phase = "Idle"
    /\ reqTime'       = storedTime
    /\ reqAuthorized' = TRUE
    /\ phase'      = "Received"
    /\ reqPresent' = TRUE
    /\ UNCHANGED storedTime

Next == Idle \/ Recv \/ BeginVerify \/ Write \/ Refuse \/ Finish \/ Replay

Spec == Init /\ [][Next]_vars /\ WF_vars(BeginVerify) /\ WF_vars(Write)
                              /\ WF_vars(Refuse)

\* ---- Properties (mirror the Lean theorems) --------------------------------
\* S (authenticity): a committed write was authorized.
Authentic == (phase = "Written" => reqAuthorized = TRUE)

\* R1 (anti-replay/anti-rollback): stored timestamp never decreases.
AntiReplay == [][ storedTime' >= storedTime ]_vars

\* G + strict freshness: entering Written strictly advances the timestamp,
\* so a replay (equal timestamp) is never committed.
WriteGuard ==
    [][ (phase # "Written" /\ phase' = "Written")
          => (reqAuthorized = TRUE /\ storedTime < reqTime) ]_vars

=============================================================================
