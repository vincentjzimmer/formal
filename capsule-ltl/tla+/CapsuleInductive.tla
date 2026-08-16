------------------------- MODULE CapsuleInductive -------------------------
(***************************************************************************)
(* Apalache (symbolic / SMT-backed TLA+) harness that discharges the      *)
(* global anti-rollback property R2 -- monotonicity of fwVersion over an  *)
(* UNBOUNDED number of steps -- as an INDUCTIVE INVARIANT, without the     *)
(* version bound TLC requires.  This closes the bounded/unbounded gap      *)
(* between the TLC model-checking story and the Lean deductive proof:      *)
(* TLC explores `MaxVersion = 3`; Apalache proves the invariant for all    *)
(* versions in `Nat` by two finite SMT queries.                            *)
(*                                                                         *)
(* Apalache type annotations are in the `\* @type:` comments.              *)
(*                                                                         *)
(* Two checks (see CapsuleInductive.sh):                                   *)
(*   (1) Init => IndInv                 -- base case                       *)
(*   (2) IndInv /\ Next => IndInv'      -- inductive step (length 1)       *)
(* Together they imply [] IndInv on the unbounded system.  IndInv          *)
(* conjoins the safety invariants the Lean proof establishes; the          *)
(* anti-rollback content is the action-level fact fwVersion' >= fwVersion, *)
(* which Apalache checks symbolically in the step query.                   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

\* CRASH stays a constant so the SAME inductive invariant can be checked in
\* both regimes; set it in the .cfg / CLI.
CONSTANT
    \* @type: Bool;
    CRASH

VARIABLES
    \* @type: Str;
    phase,
    \* @type: Int;
    fwVersion,
    \* @type: Bool;
    capsulePresent,
    \* @type: Int;
    capsuleVersion,
    \* @type: Bool;
    capsuleSigValid,
    \* @type: Bool;
    resetOccurred

vars == << phase, fwVersion, capsulePresent, capsuleVersion,
           capsuleSigValid, resetOccurred >>

Phases == { "Idle", "CapsuleStaged", "PostReset",
            "Authenticating", "Applied", "Rejected" }

\* No MaxVersion: versions range over all of Nat, as in the Lean model.
TypeOK ==
    /\ phase           \in Phases
    /\ fwVersion       \in Nat
    /\ capsulePresent  \in BOOLEAN
    /\ capsuleVersion  \in Nat
    /\ capsuleSigValid \in BOOLEAN
    /\ resetOccurred   \in BOOLEAN

Init ==
    /\ phase           = "Idle"
    /\ capsulePresent  = FALSE
    /\ resetOccurred   = FALSE
    /\ fwVersion       \in Nat
    /\ capsuleVersion  \in Nat
    /\ capsuleSigValid \in BOOLEAN

\* ---- actions (identical to CapsuleUpdate.tla, MaxVersion removed) --------
StutterIdle == phase = "Idle" /\ UNCHANGED vars

Stage ==
    /\ phase = "Idle"
    /\ \E v \in Nat, sig \in BOOLEAN :
         /\ capsuleVersion'  = v
         /\ capsuleSigValid' = sig
    /\ phase'          = "CapsuleStaged"
    /\ capsulePresent' = TRUE
    /\ resetOccurred'  = FALSE
    /\ UNCHANGED fwVersion

Reset ==
    /\ phase = "CapsuleStaged"
    /\ phase'         = "PostReset"
    /\ resetOccurred' = TRUE
    /\ UNCHANGED << fwVersion, capsulePresent, capsuleVersion, capsuleSigValid >>

BeginAuth ==
    /\ phase = "PostReset"
    /\ phase' = "Authenticating"
    /\ UNCHANGED << fwVersion, capsulePresent, capsuleVersion,
                    capsuleSigValid, resetOccurred >>

Apply ==
    /\ phase = "Authenticating"
    /\ capsuleSigValid = TRUE
    /\ fwVersion < capsuleVersion
    /\ phase'     = "Applied"
    /\ fwVersion' = capsuleVersion
    /\ UNCHANGED << capsulePresent, capsuleVersion, capsuleSigValid,
                    resetOccurred >>

Reject ==
    /\ phase = "Authenticating"
    /\ (capsuleSigValid = FALSE \/ capsuleVersion <= fwVersion)
    /\ phase'          = "Rejected"
    /\ capsulePresent' = FALSE
    /\ UNCHANGED << fwVersion, capsuleVersion, capsuleSigValid, resetOccurred >>

Finish ==
    /\ phase \in { "Applied", "Rejected" }
    /\ phase'          = "Idle"
    /\ capsulePresent' = FALSE
    /\ resetOccurred'  = FALSE
    /\ UNCHANGED << fwVersion, capsuleVersion, capsuleSigValid >>

PartialWrite ==
    IF /\ phase = "Authenticating"
       /\ capsuleSigValid = TRUE
       /\ fwVersion < capsuleVersion
    THEN { fwVersion, capsuleVersion }
    ELSE { fwVersion }

Crash ==
    /\ CRASH
    /\ phase \notin { "Idle" }
    /\ fwVersion' \in PartialWrite
    /\ phase'         = "PostReset"
    /\ resetOccurred' = TRUE
    /\ UNCHANGED << capsulePresent, capsuleVersion, capsuleSigValid >>

Next ==
    \/ StutterIdle \/ Stage \/ Reset \/ BeginAuth
    \/ Apply \/ Reject \/ Finish \/ Crash

\* ===========================================================================
\* The inductive invariant.
\*
\* IndInv must (a) be implied by Init, (b) be preserved by Next, and
\* (c) be strong enough to entail the safety invariants S and O.  The
\* anti-rollback content R2 is the *action* fact fwVersion' >= fwVersion,
\* established by NoRollback below; R2's "i <= j => fw_i <= fw_j" closure is
\* the transitive consequence over the unbounded run, mirroring the Lean
\* `antirollback_global` induction.
\*
\* InvReset is the Lean `InvReset` strengthening: it is the part of the
\* invariant that is NOT obvious from S/O alone but is needed to make the
\* conjunction inductive (the singleton `Applied => reset` is not inductive).
\* ===========================================================================
InvSig   == phase = "Applied" => capsuleSigValid = TRUE
InvReset == (phase \in { "PostReset", "Authenticating", "Applied" })
                => resetOccurred = TRUE

IndInv ==
    /\ TypeOK
    /\ InvSig
    /\ InvReset

\* Action invariant: anti-rollback (R1), proved symbolically for all of Nat.
\* This is the unbounded analogue of the Lean `step_version_mono` lemma; the
\* global R2 is its transitive closure.
NoRollback == fwVersion' >= fwVersion
=============================================================================
