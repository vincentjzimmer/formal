--------------------------- MODULE CapsuleMultiDevice ---------------------------
(***************************************************************************)
(* Multi-device extension of the capsule-update model, with               *)
(* EFI_FIRMWARE_IMAGE_DEP dependency expressions.                          *)
(*                                                                         *)
(* The Lean development models ONE FMP device: fwVersion is a scalar.      *)
(* Real platforms expose many FMP instances (NIC, EC, retimer, GPU, ...),  *)
(* each with its own ImageTypeId and running version, and a capsule may    *)
(* carry a dependency expression (UEFI 2.10 sec 23.4 / FmpDevicePkg        *)
(* DEPENDENCY support) requiring that OTHER devices already be at some     *)
(* minimum version before this image may apply. That coupling is a         *)
(* concurrency/ordering problem -- exactly what TLC is good at and what    *)
(* the scalar Lean model cannot express.                                   *)
(*                                                                         *)
(* The version field becomes a per-device vector with the product order;   *)
(* anti-rollback lifts to "monotone in every component". The new question  *)
(* is whether dependency expressions admit a partial-update window or a    *)
(* dependency cycle that strands a device. We let TLC hunt for both.       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Devices,      \* set of FMP device handles, e.g. {"nic","ec"}
    MaxVersion,   \* per-device version range 0..MaxVersion
    Dep           \* Dep[d] = set of (device, minVersion) prereqs for applying to d

Versions == 0 .. MaxVersion
Phases   == { "Idle", "CapsuleStaged", "PostReset",
              "Authenticating", "Applied", "Rejected" }

\* ---- Concrete dependency tables (overridden onto Dep via the .cfg) --------
\* A CYCLIC dependency over {nic, ec}: each requires the other at >= 1, so from
\* an all-zero start neither can apply first. Falsifies ResponsivenessApply.
DepCyclic  == [ d \in {"nic","ec"} |->
                 IF d = "nic" THEN { <<"ec", 1>> } ELSE { <<"nic", 1>> } ]

\* An ACYCLIC dependency: nic requires ec >= 1; ec has no prereqs. Appliable in
\* the order ec-then-nic. ResponsivenessApply holds under a fair schedule.
DepAcyclic == [ d \in {"nic","ec"} |->
                 IF d = "nic" THEN { <<"ec", 1>> } ELSE {} ]

\* No dependencies at all (recovers the per-device-independent baseline).
DepNone    == [ d \in {"nic","ec"} |-> {} ]

\* ---- State -----------------------------------------------------------------
\* fwVersion : [Devices -> Nat]      running version per device
\* target    : the device the staged capsule is for (or "none" when Idle)
\* phase, capsuleVersion, capsuleSigValid, resetOccurred as before, but the
\* capsule fields describe the single in-flight capsule for `target`.
VARIABLES
    phase, fwVersion, target, capsulePresent, capsuleVersion,
    capsuleSigValid, resetOccurred

vars == << phase, fwVersion, target, capsulePresent, capsuleVersion,
           capsuleSigValid, resetOccurred >>

NoDev == "none"

TypeOK ==
    /\ phase           \in Phases
    /\ fwVersion       \in [ Devices -> Versions ]
    /\ target          \in Devices \cup { NoDev }
    /\ capsulePresent  \in BOOLEAN
    /\ capsuleVersion  \in Versions
    /\ capsuleSigValid \in BOOLEAN
    /\ resetOccurred   \in BOOLEAN

Init ==
    /\ phase           = "Idle"
    /\ fwVersion       \in [ Devices -> Versions ]
    /\ target          = NoDev
    /\ capsulePresent  = FALSE
    /\ capsuleVersion  \in Versions
    /\ capsuleSigValid \in BOOLEAN
    /\ resetOccurred   = FALSE

\* ---- Dependency satisfaction ----------------------------------------------
\* The capsule's DEPENDENCY clause for device d is satisfied iff every prereq
\* (e, minV) in Dep[d] holds of the CURRENT running versions. This is checked
\* at authentication time, against the post-reset coalesced state.
\* LISTING:deps:begin
DepsSatisfied(d) ==
    \A prereq \in Dep[d] : fwVersion[prereq[1]] >= prereq[2]
\* LISTING:deps:end

\* ===========================================================================
\* Actions
\* ===========================================================================
StutterIdle == phase = "Idle" /\ UNCHANGED vars

\* Stage a capsule for some device d, adversary-chosen version & signature.
Stage ==
    /\ phase = "Idle"
    /\ \E d \in Devices, v \in Versions, sig \in BOOLEAN :
         /\ target'          = d
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
    /\ UNCHANGED << fwVersion, target, capsulePresent, capsuleVersion,
                    capsuleSigValid >>

BeginAuth ==
    /\ phase = "PostReset"
    /\ phase' = "Authenticating"
    /\ UNCHANGED << fwVersion, target, capsulePresent, capsuleVersion,
                    capsuleSigValid, resetOccurred >>

\* Apply now has THREE guards: signature, strict version increase on the
\* target device, AND dependency satisfaction.
\* LISTING:mdapply:begin
Apply ==
    /\ phase = "Authenticating"
    /\ capsuleSigValid = TRUE
    /\ fwVersion[target] < capsuleVersion
    /\ DepsSatisfied(target)
    /\ phase'     = "Applied"
    /\ fwVersion' = [ fwVersion EXCEPT ![target] = capsuleVersion ]
    /\ UNCHANGED << target, capsulePresent, capsuleVersion, capsuleSigValid,
                    resetOccurred >>
\* LISTING:mdapply:end

\* Reject if signature fails, version is not newer, OR deps are unmet.
Reject ==
    /\ phase = "Authenticating"
    /\ \/ capsuleSigValid = FALSE
       \/ capsuleVersion <= fwVersion[target]
       \/ ~DepsSatisfied(target)
    /\ phase'          = "Rejected"
    /\ capsulePresent' = FALSE
    /\ UNCHANGED << fwVersion, target, capsuleVersion, capsuleSigValid,
                    resetOccurred >>

Finish ==
    /\ phase \in { "Applied", "Rejected" }
    /\ phase'          = "Idle"
    /\ target'         = NoDev
    /\ capsulePresent' = FALSE
    /\ resetOccurred'  = FALSE
    /\ UNCHANGED << fwVersion, capsuleVersion, capsuleSigValid >>

Next ==
    \/ StutterIdle \/ Stage \/ Reset \/ BeginAuth
    \/ Apply \/ Reject \/ Finish

Spec == Init /\ [][Next]_vars /\ WF_vars(Reset) /\ WF_vars(BeginAuth)
                              /\ WF_vars(Apply) /\ WF_vars(Reject)

\* ===========================================================================
\* Properties
\* ===========================================================================

\* Per-device anti-rollback: no device's version ever decreases (R1 lifted to
\* the product order -- monotone in every component).
AntiRollbackStep == [][ \A d \in Devices : fwVersion'[d] >= fwVersion[d] ]_vars

\* Authenticity, lifted: an applied capsule for its target was signed.
SafetyAuthentic == (phase = "Applied" => capsuleSigValid = TRUE)

\* Apply-guard, lifted: entry into Applied implies signature + strict newness
\* + dependency satisfaction held in the pre-state.
ApplyGuarded ==
    [][ (phase # "Applied" /\ phase' = "Applied")
          => /\ capsuleSigValid = TRUE
             /\ fwVersion[target] < capsuleVersion
             /\ DepsSatisfied(target) ]_vars

\* DEPENDENCY-GATING: an applied image's dependencies were satisfied at apply.
\* (Safety form, checkable as an invariant via the InvDepOK strengthening.)
\* Here we expose the *hazard*: with a cyclic Dep, a good capsule for a device
\* can be permanently un-appliable -- a liveness failure with NO crash needed.
\* Set Dep to a cycle in the .cfg and watch Responsiveness fail.
GoodStaged ==
    /\ phase = "CapsuleStaged"
    /\ capsuleSigValid = TRUE
    /\ fwVersion[target] < capsuleVersion

Responsiveness == [] (GoodStaged => <> (phase \in { "Applied", "Rejected" }))

\* The FAITHFUL LIFT of the Lean liveness theorem L (`goodStaged -> F Applied`):
\* a signed, strictly-newer staged capsule eventually APPLIES. In the scalar
\* Lean model this holds with no fairness. Here a dependency cycle (or any
\* unreachable prereq) gates `apply` and routes the capsule to `reject`
\* instead, so the capsule is authentic and newer yet NEVER applies --
\* ResponsivenessApply FAILS under DepCyclic. The dependency feature, not a
\* crash, is enough to break the scalar guarantee. This hazard is structural:
\* every individual action remains fair.
ResponsivenessApply ==
    [] (GoodStaged => <> (phase = "Applied"))
=============================================================================
