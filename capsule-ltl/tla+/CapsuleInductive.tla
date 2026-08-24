------------------------- MODULE CapsuleInductive -------------------------
(***************************************************************************)
(* Apalache (symbolic / SMT-backed TLA+) harness that discharges the      *)
(* global anti-rollback property -- monotonicity of the stored LSV floor  *)
(* over an UNBOUNDED number of steps -- as an INDUCTIVE INVARIANT, without*)
(* the version bound TLC requires. This closes the bounded/unbounded gap   *)
(* between the TLC model-checking story and the Lean deductive proof:      *)
(* TLC explores `MaxVersion = 3`; Apalache proves the invariant for all   *)
(* versions in `Nat` by two finite SMT queries.                            *)
(*                                                                         *)
(* Apalache type annotations are in the `\* @type:` comments.             *)
(*                                                                         *)
(* Two checks (see CapsuleInductive.sh):                                   *)
(*   (1) Init => IndInv                 -- base case                       *)
(*   (2) IndInv /\ Next => IndInv'      -- inductive step (length 1)       *)
(* Together they imply [] IndInv on the unbounded system. IndInv           *)
(* conjoins the safety invariants the Lean proof establishes; the          *)
(* anti-rollback content is the action-level fact lsv' >= lsv, which       *)
(* Apalache checks symbolically in the step query.                         *)
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
    \* @type: Int;
    lsv,
    \* @type: Bool;
    capsulePresent,
    \* @type: Int;
    capsuleVersion,
    \* @type: Int;
    imageDigest,
    \* @type: Bool;
    capsuleSigValid,
    \* @type: Bool;
    resetOccurred

vars == << phase, fwVersion, lsv, capsulePresent, capsuleVersion,
           imageDigest, capsuleSigValid, resetOccurred >>

Phases == { "Idle", "CapsuleStaged", "PostReset",
            "Authenticating", "Applied", "Rejected" }

CertOK(d) == d /= 0

\* No MaxVersion: versions range over all of Nat, as in the Lean model.
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

\* ---- actions (identical to CapsuleUpdate.tla, MaxVersion removed) --------
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

PartialWrite ==
    IF /\ phase = "Authenticating"
       /\ capsuleSigValid = TRUE
       /\ lsv <= capsuleVersion
    THEN { fwVersion, capsuleVersion }
    ELSE { fwVersion }

Crash ==
    /\ CRASH
    /\ phase \notin { "Idle" }
    /\ fwVersion' \in PartialWrite
    /\ phase'         = "PostReset"
    /\ resetOccurred' = TRUE
    /\ UNCHANGED << lsv, capsulePresent, capsuleVersion, imageDigest,
                    capsuleSigValid >>

Next ==
    \/ StutterIdle \/ Stage \/ Reset \/ BeginAuth
    \/ Apply \/ Reject \/ Finish \/ Crash

\* ===========================================================================
\* The inductive invariant.
\*
\* IndInv must (a) be implied by Init, (b) be preserved by Next, and
\* (c) be strong enough to entail the safety invariants. The anti-rollback
\* content is the action fact lsv' >= lsv; its global closure follows by
\* transitivity over the run.
\* ===========================================================================
InvSig   == phase = "Applied" => capsuleSigValid = TRUE
InvReset == (phase \in { "PostReset", "Authenticating", "Applied" })
                => resetOccurred = TRUE
InvFloor == lsv <= fwVersion

IndInv ==
    /\ TypeOK
    /\ InvSig
    /\ InvReset
    /\ lsv >= 0
    /\ InvFloor

\* Action invariant: anti-rollback of the stored floor, proved symbolically
\* for all of Nat.
NoRollback == lsv' >= lsv
NoRollbackLSV == lsv' >= lsv
=============================================================================
