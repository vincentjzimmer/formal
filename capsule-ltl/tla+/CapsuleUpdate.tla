---------------------------- MODULE CapsuleUpdate ----------------------------
(***************************************************************************)
(* A TLA+ rendering of the UEFI capsule-update LTS from the Lean           *)
(* development (ltl_capsule.lean).  Phase 1 is a deliberate ONE-TO-ONE     *)
(* mirror of the Lean `St` record and `Step` relation, so the two models   *)
(* can be eyeballed against each other.  Phase 2 (CRASH) adds the          *)
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
\* capsulePresent  : Bool
\* capsuleVersion  : Nat       (adversary-chosen, like Lean's `stage` input)
\* capsuleSigValid : Bool      (adversary-chosen signature verdict)
\* resetOccurred   : Bool
VARIABLES
    phase, fwVersion, capsulePresent, capsuleVersion, capsuleSigValid,
    resetOccurred

vars == << phase, fwVersion, capsulePresent, capsuleVersion,
           capsuleSigValid, resetOccurred >>

TypeOK ==
    /\ phase           \in Phases
    /\ fwVersion       \in Versions
    /\ capsulePresent  \in BOOLEAN
    /\ capsuleVersion  \in Versions
    /\ capsuleSigValid \in BOOLEAN
    /\ resetOccurred   \in BOOLEAN

\* ---- Init: mirrors Lean `Init` --------------------------------------------
\* Lean fixes only phase/capsulePresent/resetOccurred; fwVersion and the
\* (unused-at-init) capsule fields are otherwise unconstrained.  We let
\* fwVersion start anywhere in range so monotonicity is proved generally.
Init ==
    /\ phase           = "Idle"
    /\ capsulePresent  = FALSE
    /\ resetOccurred   = FALSE
    /\ fwVersion       \in Versions
    /\ capsuleVersion  \in Versions
    /\ capsuleSigValid \in BOOLEAN

\* ===========================================================================
\* Phase 1: the eight Lean `Step` rules, one TLA+ action each.
\* ===========================================================================

\* stutterIdle (s) : phase = Idle -> Step s s
StutterIdle ==
    /\ phase = "Idle"
    /\ UNCHANGED vars

\* stage (s) v sig : phase = Idle -> staged with adversary-chosen v, sig
\* The \E here IS the Lean threat model: environment picks any version and
\* any signature verdict (forged / downgraded capsules included).
Stage ==
    /\ phase = "Idle"
    /\ \E v \in Versions, sig \in BOOLEAN :
         /\ capsuleVersion'  = v
         /\ capsuleSigValid' = sig
    /\ phase'          = "CapsuleStaged"
    /\ capsulePresent' = TRUE
    /\ resetOccurred'  = FALSE
    /\ UNCHANGED fwVersion

\* reset (s) : phase = CapsuleStaged -> PostReset, resetOccurred := true
Reset ==
    /\ phase = "CapsuleStaged"
    /\ phase'         = "PostReset"
    /\ resetOccurred' = TRUE
    /\ UNCHANGED << fwVersion, capsulePresent, capsuleVersion, capsuleSigValid >>

\* beginAuth (s) : phase = PostReset -> Authenticating
BeginAuth ==
    /\ phase = "PostReset"
    /\ phase' = "Authenticating"
    /\ UNCHANGED << fwVersion, capsulePresent, capsuleVersion,
                    capsuleSigValid, resetOccurred >>

\* apply (s) : authentic + strictly-newer -> Applied, fwVersion := capsuleVersion
Apply ==
    /\ phase = "Authenticating"
    /\ capsuleSigValid = TRUE
    /\ fwVersion < capsuleVersion
    /\ phase'     = "Applied"
    /\ fwVersion' = capsuleVersion
    /\ UNCHANGED << capsulePresent, capsuleVersion, capsuleSigValid,
                    resetOccurred >>

\* reject (s) : NOT(sig) \/ capsuleVersion <= fwVersion -> Rejected
Reject ==
    /\ phase = "Authenticating"
    /\ (capsuleSigValid = FALSE \/ capsuleVersion <= fwVersion)
    /\ phase'          = "Rejected"
    /\ capsulePresent' = FALSE
    /\ UNCHANGED << fwVersion, capsuleVersion, capsuleSigValid, resetOccurred >>

\* finishApplied / finishRejected : phase \in {Applied,Rejected} -> Idle
Finish ==
    /\ phase \in { "Applied", "Rejected" }
    /\ phase'          = "Idle"
    /\ capsulePresent' = FALSE
    /\ resetOccurred'  = FALSE
    /\ UNCHANGED << fwVersion, capsuleVersion, capsuleSigValid >>

\* ===========================================================================
\* Phase 2: power-fail.  THIS HAS NO COUNTERPART IN THE LEAN MODEL.
\* A reset can fire from any non-Idle phase, dropping back to PostReset-style
\* recovery.  The subtle, security-relevant choice is what happens to
\* fwVersion if the crash interrupts `Apply` mid-write: model it as
\* nondeterministically the OLD or the NEW version (a partial flash write).
\* This is the action expected to falsify fairness-free liveness (L) and to
\* stress the monotonicity invariant.
\* ===========================================================================
\* A partial SetImage can only land a version that was legitimately being
\* written -- i.e. the new version, and only when an apply was in progress
\* (fwVersion < capsuleVersion).  Otherwise the crash leaves fwVersion
\* untouched.  This keeps the crash from spuriously rolling the version back,
\* so any R1 violation TLC reports is a *real* hazard, not a modelling artefact.
\* LISTING:crash:begin
PartialWrite ==
    IF /\ phase = "Authenticating"
       /\ capsuleSigValid = TRUE
       /\ fwVersion < capsuleVersion
    THEN { fwVersion, capsuleVersion }   \* mid-apply: old or new
    ELSE { fwVersion }                   \* no write in flight: unchanged

Crash ==
    /\ CRASH
    /\ phase \notin { "Idle" }
    /\ fwVersion' \in PartialWrite
    /\ phase'         = "PostReset"
    /\ resetOccurred' = TRUE
    /\ UNCHANGED << capsulePresent, capsuleVersion, capsuleSigValid >>
\* LISTING:crash:end

\* Opt-in, more-adversarial variant: a crash can corrupt fwVersion to ANY
\* value (e.g. a torn write of the version metadata itself).  Swapping this
\* in for Crash in Next breaks AntiRollbackStep -- the second paper's finding
\* that crash-consistency of the version record is its own proof obligation.
CrashAdversarial ==
    /\ CRASH
    /\ phase \notin { "Idle" }
    /\ fwVersion' \in Versions
    /\ phase'         = "PostReset"
    /\ resetOccurred' = TRUE
    /\ UNCHANGED << capsulePresent, capsuleVersion, capsuleSigValid >>

Next ==
    \/ StutterIdle \/ Stage \/ Reset \/ BeginAuth
    \/ Apply \/ Reject \/ Finish
    \/ Crash

\* Weak fairness on the "good path" actions only -- mirrors the Lean claim
\* that progress is forced.  Under CRASH this fairness is NOT enough, which
\* is exactly the finding the second paper is after.
Spec == Init /\ [][Next]_vars /\ WF_vars(Reset) /\ WF_vars(BeginAuth)
                              /\ WF_vars(Apply)

\* ===========================================================================
\* Properties: the five Lean theorems, restated as TLA+ temporal formulas.
\* ===========================================================================

\* S  -- safety_authentic : G (Applied -> sig valid)
\* State-predicate form (used with INVARIANT); [] is supplied by TLC.
SafetyAuthentic == (phase = "Applied" => capsuleSigValid = TRUE)

\* R1 -- antirollback_step : G (fwVersion <= fwVersion')
\* (an action property; under CRASH with partial-write this can FAIL)
AntiRollbackStep == [][ fwVersion' >= fwVersion ]_vars

\* R2 -- antirollback_global is the inductive consequence of R1; TLC checks
\* the step form and we trust transitivity (or use Apalache for the closure).

\* O  -- reset_first : G (Applied -> resetOccurred)
\* State-predicate form (used with INVARIANT).
ResetFirst == (phase = "Applied" => resetOccurred = TRUE)

\* G  -- apply_guarded : entry into Applied is guarded on the PRE-state.
\* Expressed as an action formula over the primed/unprimed pair.
ApplyGuarded ==
    [][ (phase # "Applied" /\ phase' = "Applied")
          => (capsuleSigValid = TRUE /\ fwVersion < capsuleVersion) ]_vars

\* L  -- responsiveness (liveness, fairness-free in Lean).
\* Once a good capsule is staged, Applied is eventually reached.
GoodStaged ==
    /\ phase = "CapsuleStaged"
    /\ capsuleSigValid = TRUE
    /\ fwVersion < capsuleVersion

Responsiveness == [] (GoodStaged => <> (phase = "Applied"))

=============================================================================
