---------------------------- MODULE CapsuleUpdate ----------------------------
(***************************************************************************)
(* A TLA+ rendering of the UEFI capsule-update LTS from the Lean           *)
(* development (ltl_capsule.lean). Phase 1 is a deliberate ONE-TO-ONE      *)
(* mirror of the Lean `St` record and `Step` relation, so the two models   *)
(* can be eyeballed against each other. Phase 2 (CRASH) adds the           *)
(* power-fail / interrupted-SetImage behaviour the Lean model abstracts    *)
(* away -- this is where TLC is expected to break the fairness-free        *)
(* liveness property (L) and force explicit recovery assumptions.          *)
(*                                                                         *)
(* Toggle CRASH in the .cfg constants to compare the two regimes.          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    MaxVersion,      \* version numbers range over 0 .. MaxVersion (bounds TLC)
    CRASH            \* TRUE => enable the power-fail action (Phase 2)

\* ---- Phase enumeration: mirrors Lean `inductive Phase` --------------------
Phases == { "Idle", "CapsuleStaged", "PostReset",
            "Authenticating", "Applied", "Rejected" }

Versions == 0 .. MaxVersion

\* ---- State: mirrors Lean `structure St` ----------------------------------
\* phase           : Phase
\* fwVersion       : Nat       (running firmware version)
\* lsv             : Nat       (lowest supported version floor)
\* capsulePresent  : Bool
\* capsuleVersion  : Nat       (adversary-chosen, like Lean's `stage` input)
\* imageDigest     : Nat       (authenticated input staged with the capsule)
\* capsuleSigValid : Bool      (computed by BeginAuth from imageDigest)
\* resetOccurred   : Bool
VARIABLES
    phase, fwVersion, lsv, capsulePresent, capsuleVersion, imageDigest,
    capsuleSigValid, resetOccurred

vars == << phase, fwVersion, lsv, capsulePresent, capsuleVersion,
           imageDigest, capsuleSigValid, resetOccurred >>

CertOK(d) == d /= 0

TypeOK ==
    /\ phase           \in Phases
    /\ fwVersion       \in Versions
    /\ lsv             \in Versions
    /\ capsulePresent  \in BOOLEAN
    /\ capsuleVersion  \in Versions
    /\ imageDigest     \in Versions
    /\ capsuleSigValid \in BOOLEAN
    /\ resetOccurred   \in BOOLEAN

\* ---- Init: mirrors Lean `Init` --------------------------------------------
\* Lean fixes only phase/capsulePresent/resetOccurred plus the floor relation;
\* fwVersion, lsv, and the otherwise-unused capsule fields are unconstrained
\* beyond typing.
Init ==
    /\ phase           = "Idle"
    /\ capsulePresent  = FALSE
    /\ resetOccurred   = FALSE
    /\ fwVersion       \in Versions
    /\ lsv             \in Versions
    /\ capsuleVersion  \in Versions
    /\ imageDigest     \in Versions
    /\ capsuleSigValid \in BOOLEAN
    /\ lsv <= fwVersion

\* ===========================================================================
\* Phase 1: the Lean `Step` rules, one TLA+ action each.
\* ===========================================================================

\* stutterIdle (s) : phase = Idle -> Step s s
StutterIdle ==
    /\ phase = "Idle"
    /\ UNCHANGED vars

\* stage (s) v digest : phase = Idle -> staged with adversary-chosen v, digest
\* Signature validity is no longer chosen here; BeginAuth derives it later.
Stage ==
    /\ phase = "Idle"
    /\ \E v \in Versions, d \in Versions :
         /\ capsuleVersion' = v
         /\ imageDigest'    = d
    /\ phase'          = "CapsuleStaged"
    /\ capsulePresent' = TRUE
    /\ resetOccurred'  = FALSE
    /\ UNCHANGED << fwVersion, lsv, capsuleSigValid >>

\* reset (s) : phase = CapsuleStaged -> PostReset, resetOccurred := true
Reset ==
    /\ phase = "CapsuleStaged"
    /\ phase'         = "PostReset"
    /\ resetOccurred' = TRUE
    /\ UNCHANGED << fwVersion, lsv, capsulePresent, capsuleVersion,
                    imageDigest, capsuleSigValid >>

\* beginAuth (s) : phase = PostReset -> Authenticating,
\*                 capsuleSigValid := CertOK(imageDigest)
BeginAuth ==
    /\ phase = "PostReset"
    /\ phase'            = "Authenticating"
    /\ capsuleSigValid'  = CertOK(imageDigest)
    /\ UNCHANGED << fwVersion, lsv, capsulePresent, capsuleVersion,
                    imageDigest, resetOccurred >>

\* apply (s) : authentic + at-or-above-floor -> Applied,
\*             fwVersion := capsuleVersion, lsv := capsuleVersion
Apply ==
    /\ phase = "Authenticating"
    /\ capsuleSigValid = TRUE
    /\ lsv <= capsuleVersion
    /\ phase'     = "Applied"
    /\ fwVersion' = capsuleVersion
    /\ lsv'       = capsuleVersion
    /\ UNCHANGED << capsulePresent, capsuleVersion, imageDigest,
                    capsuleSigValid, resetOccurred >>

\* reject (s) : NOT(sig) \/ capsuleVersion < lsv -> Rejected
Reject ==
    /\ phase = "Authenticating"
    /\ (capsuleSigValid = FALSE \/ capsuleVersion < lsv)
    /\ phase'          = "Rejected"
    /\ capsulePresent' = FALSE
    /\ UNCHANGED << fwVersion, lsv, capsuleVersion, imageDigest,
                    capsuleSigValid, resetOccurred >>

\* finishApplied / finishRejected : phase \in {Applied,Rejected} -> Idle
Finish ==
    /\ phase \in { "Applied", "Rejected" }
    /\ phase'          = "Idle"
    /\ capsulePresent' = FALSE
    /\ resetOccurred'  = FALSE
    /\ UNCHANGED << fwVersion, lsv, capsuleVersion, imageDigest,
                    capsuleSigValid >>

\* ===========================================================================
\* Phase 2: power-fail. THIS HAS NO COUNTERPART IN THE LEAN MODEL.
\* A reset can fire from any non-Idle phase, dropping back to PostReset-style
\* recovery. The subtle choice is what happens to fwVersion if the crash
\* interrupts `Apply` mid-write: model it as nondeterministically the OLD or
\* the NEW version. The LSV floor and staged digest survive the crash.
\* ===========================================================================
\* LISTING:crash:begin
PartialWrite ==
    IF /\ phase = "Authenticating"
       /\ capsuleSigValid = TRUE
       /\ lsv <= capsuleVersion
    THEN { fwVersion, capsuleVersion }   \* mid-apply: old or new
    ELSE { fwVersion }                   \* no write in flight: unchanged

Crash ==
    /\ CRASH
    /\ phase \notin { "Idle" }
    /\ fwVersion' \in PartialWrite
    /\ phase'         = "PostReset"
    /\ resetOccurred' = TRUE
    /\ UNCHANGED << lsv, capsulePresent, capsuleVersion, imageDigest,
                    capsuleSigValid >>
\* LISTING:crash:end

\* Opt-in, more-adversarial variant: a crash can corrupt fwVersion to ANY
\* value (e.g. a torn write of the version metadata itself). The LSV floor is
\* still preserved; what breaks is the relation between fwVersion and the floor.
CrashAdversarial ==
    /\ CRASH
    /\ phase \notin { "Idle" }
    /\ fwVersion' \in Versions
    /\ phase'         = "PostReset"
    /\ resetOccurred' = TRUE
    /\ UNCHANGED << lsv, capsulePresent, capsuleVersion, imageDigest,
                    capsuleSigValid >>

Next ==
    \/ StutterIdle \/ Stage \/ Reset \/ BeginAuth
    \/ Apply \/ Reject \/ Finish
    \/ Crash

\* Weak fairness on the "good path" actions only -- mirrors the Lean claim
\* that progress is forced. Under CRASH this fairness is NOT enough, which
\* is exactly the finding the second paper is after.
Spec == Init /\ [][Next]_vars /\ WF_vars(Reset) /\ WF_vars(BeginAuth)
                              /\ WF_vars(Apply)

\* ===========================================================================
\* Properties: the Lean theorems, restated as TLA+ temporal formulas.
\* ===========================================================================

\* S  -- safety_authentic : G (Applied -> sig valid)
\* State-predicate form (used with INVARIANT); [] is supplied by TLC.
SafetyAuthentic == (phase = "Applied" => capsuleSigValid = TRUE)

\* R1 -- antirollback_lsv : G (lsv <= lsv')
AntiRollbackLSV == [][ lsv <= lsv' ]_vars

\* Legacy alias kept for callers that still mention the old property name.
AntiRollbackStep == AntiRollbackLSV

\* FLOOR invariant: the LSV floor never exceeds the running firmware version.
InvFloor == lsv <= fwVersion

\* O  -- reset_first : G (Applied -> resetOccurred)
\* State-predicate form (used with INVARIANT).
ResetFirst == (phase = "Applied" => resetOccurred = TRUE)

\* G  -- apply_guarded : entry into Applied is guarded on the PRE-state.
\* Expressed as an action formula over the primed/unprimed pair.
ApplyGuarded ==
    [][ (phase # "Applied" /\ phase' = "Applied")
          => (capsuleSigValid = TRUE /\ lsv <= capsuleVersion) ]_vars

\* L  -- responsiveness (liveness, fairness-free in Lean).
\* Once a good capsule is staged, Applied is eventually reached.
GoodStaged ==
    /\ phase = "CapsuleStaged"
    /\ CertOK(imageDigest)
    /\ lsv <= capsuleVersion

Responsiveness == [] (GoodStaged => <> (phase = "Applied"))

=============================================================================
