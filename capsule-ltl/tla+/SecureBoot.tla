----------------------------- MODULE SecureBoot -----------------------------
(***************************************************************************)
(* TLA+ model of UEFI Secure Boot dbx (forbidden-signature DB) update, the  *)
(* TLC cross-validation for Lean instance #3 (SecureBootInstance) and the   *)
(* composition theorem (Composition.lean). dbx is modelled as a SUBSET of a *)
(* finite universe of revocable image hashes. The \E in Recv is the threat  *)
(* model: the environment proposes any revocation set with any KEK-auth      *)
(* verdict. The append-only `update` only ever grows dbx.                    *)
(*                                                                         *)
(* ROLLBACK toggles the classic Secure Boot bypass the Lean append-only      *)
(* model abstracts away: replacing the whole dbx variable with an EARLIER    *)
(* (smaller) value, dropping revocations. This is expected to break          *)
(* policy non-weakening -- it is the obligation a real platform discharges   *)
(* with the authenticated-variable timestamp on dbx itself.                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Hashes,   \* finite universe of revocable image hashes
          ROLLBACK

Phases == { "Idle", "Received", "Verifying", "Updated", "Refused" }

VARIABLES phase, dbx, reqPresent, reqRevs, reqAuthorized
vars == << phase, dbx, reqPresent, reqRevs, reqAuthorized >>

TypeOK ==
    /\ phase         \in Phases
    /\ dbx           \subseteq Hashes
    /\ reqPresent    \in BOOLEAN
    /\ reqRevs       \subseteq Hashes
    /\ reqAuthorized \in BOOLEAN

Init ==
    /\ phase         = "Idle"
    /\ dbx           = {}
    /\ reqPresent    = FALSE
    /\ reqRevs       = {}
    /\ reqAuthorized \in BOOLEAN

Idle == phase = "Idle" /\ UNCHANGED vars

Recv ==
    /\ phase = "Idle"
    /\ \E r \in SUBSET Hashes, a \in BOOLEAN :
         /\ reqRevs'       = r
         /\ reqAuthorized' = a
    /\ phase'      = "Received"
    /\ reqPresent' = TRUE
    /\ UNCHANGED dbx

BeginVerify ==
    /\ phase = "Received"
    /\ phase' = "Verifying"
    /\ UNCHANGED << dbx, reqPresent, reqRevs, reqAuthorized >>

\* update: KEK-authorized; APPENDS revocations (dbx only grows).
Update ==
    /\ phase = "Verifying"
    /\ reqAuthorized = TRUE
    /\ phase' = "Updated"
    /\ dbx'   = dbx \cup reqRevs
    /\ UNCHANGED << reqPresent, reqRevs, reqAuthorized >>

Refuse ==
    /\ phase = "Verifying"
    /\ reqAuthorized = FALSE
    /\ phase'      = "Refused"
    /\ reqPresent' = FALSE
    /\ UNCHANGED << dbx, reqRevs, reqAuthorized >>

Finish ==
    /\ phase \in { "Updated", "Refused" }
    /\ phase'      = "Idle"
    /\ reqPresent' = FALSE
    /\ UNCHANGED << dbx, reqRevs, reqAuthorized >>

\* PERTURBATION: variable rollback. Replace dbx with any SUBSET of itself --
\* a stale-variable-image attack that drops revocations. Expected to FALSIFY
\* policy non-weakening; the defense is binding the dbx variable to a
\* monotone authenticated-variable timestamp (instance #2 on dbx).
Rollback ==
    /\ ROLLBACK
    /\ \E d \in SUBSET dbx : dbx' = d
    /\ UNCHANGED << phase, reqPresent, reqRevs, reqAuthorized >>

Next == Idle \/ Recv \/ BeginVerify \/ Update \/ Refuse \/ Finish \/ Rollback

Spec == Init /\ [][Next]_vars

\* ---- Properties -----------------------------------------------------------
\* S (authenticity): a committed policy update was KEK-authorized.
Authentic == (phase = "Updated" => reqAuthorized = TRUE)

\* R1/R2 (no silent un-revocation): dbx never shrinks across a step.
NoUnrevoke == [][ dbx \subseteq dbx' ]_vars

\* Composition / policy non-weakening (action form): a revoked hash is never
\* dropped by any single step.
NonWeakening == [][ \A h \in dbx : h \in dbx' ]_vars

=============================================================================
