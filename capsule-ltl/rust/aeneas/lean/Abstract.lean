/-
  LTL properties of the UEFI capsule update process.

  A self-contained Lean 4 development (no Mathlib).

  We model the UEFI Capsule Update flow as a labelled transition system:

      Idle ──UpdateCapsule()──▶ CapsuleStaged ──reset──▶ PostReset
        ▲                                                    │
        │                                              beginAuthenticate
        │                                                    ▼
        ├────────────── finish ──── Applied ◀── apply ── Authenticating
        │                                          │            │
        └────────────── finish ─── Rejected ◀──────┴── reject ──┘

  - UpdateCapsule() (a UEFI Runtime Service) stages a capsule image in a
    reserved memory region together with a requested system reset
    (EFI_OS_INDICATIONS_FILE_CAPSULE_DELIVERY_SUPPORTED semantics).
  - After the reset the firmware (capsule coalescing + the Firmware Management
    Protocol / FMP) authenticates the image: a signature check *and* a
    monotonic version check (anti-rollback, per EDK II `FmpDeviceCheckImage`
    / lowest-supported-version handling).
  - apply is only enabled for an authentic, strictly-newer image; otherwise the
    capsule is rejected. Applying bumps the running firmware version.

  We then prove, by machine-checked LTL theorems quantified over *all* runs:
    1. SAFETY (authenticity):  G (Applied → signature was valid)
    2. ANTI-ROLLBACK:          G (fwVersion non-decreasing), and the global
                               monotonicity corollary  i ≤ j → fw i ≤ fw j
    3. APPLY-GUARD:            you only *enter* Applied via an authentic,
                               strictly-newer image (no rollback is ever applied)
    4. RESET-FIRST:            G (Applied → a reset has occurred)
    5. RESPONSIVENESS (live):  G (good capsule staged → F Applied)
                               — fairness-free, because the good path is forced.
-/

namespace UefiCapsuleLTL

/-! ## System model -/

inductive Phase where
  | Idle           -- normal runtime; no update pending
  | CapsuleStaged  -- UpdateCapsule() called; image in memory; reset requested
  | PostReset      -- machine has reset; capsule awaiting authentication
  | Authenticating -- FMP authenticating signature + version
  | Applied        -- image authenticated and written
  | Rejected       -- authentication or anti-rollback check failed
  deriving DecidableEq, Repr

open Phase

structure St where
  phase           : Phase
  fwVersion       : Nat   -- currently running firmware version
  capsulePresent  : Bool  -- a capsule image is staged
  capsuleVersion  : Nat   -- version of the staged image
  capsuleSigValid : Bool  -- staged image carries a valid signature
  resetOccurred   : Bool  -- a reset has happened since staging
  deriving Repr

/-- Initial firmware state: idle, nothing staged. -/
def Init (s : St) : Prop :=
  s.phase = Idle ∧ s.capsulePresent = false ∧ s.resetOccurred = false

/-- One step of the capsule-update transition system. -/
inductive Step : St → St → Prop where
  | stutterIdle (s) :
      s.phase = Idle →
      Step s s
  | stage (s) (v : Nat) (sig : Bool) :
      s.phase = Idle →
      Step s { s with phase := CapsuleStaged, capsulePresent := true,
                      capsuleVersion := v, capsuleSigValid := sig,
                      resetOccurred := false }
  | reset (s) :
      s.phase = CapsuleStaged →
      Step s { s with phase := PostReset, resetOccurred := true }
  | beginAuth (s) :
      s.phase = PostReset →
      Step s { s with phase := Authenticating }
  | apply (s) :
      s.phase = Authenticating →
      s.capsuleSigValid = true →              -- signature valid
      s.fwVersion < s.capsuleVersion →        -- strictly newer (anti-rollback)
      Step s { s with phase := Applied, fwVersion := s.capsuleVersion }
  | reject (s) :
      s.phase = Authenticating →
      (s.capsuleSigValid = false ∨ s.capsuleVersion ≤ s.fwVersion) →
      Step s { s with phase := Rejected, capsulePresent := false }
  | finishApplied (s) :
      s.phase = Applied →
      Step s { s with phase := Idle, capsulePresent := false, resetOccurred := false }
  | finishRejected (s) :
      s.phase = Rejected →
      Step s { s with phase := Idle, capsulePresent := false, resetOccurred := false }

/-- An (ω-)run: an infinite trace beginning at an initial state and
    closed under the transition relation. -/
def IsRun (σ : Nat → St) : Prop :=
  Init (σ 0) ∧ ∀ i, Step (σ i) (σ (i + 1))


/-! ## Shallow-embedded LTL

    A temporal proposition is a predicate on a trace and a position. -/

--LISTING:ltl:begin
abbrev TProp := (Nat → St) → Nat → Prop

/-- Lift a state predicate to "holds now". -/
def now (p : St → Prop) : TProp := fun σ i => p (σ i)

/-- G φ : φ holds at every position from here on. -/
def G (P : TProp) : TProp := fun σ i => ∀ j, i ≤ j → P σ j

/-- F φ : φ holds at some position from here on. -/
def F (P : TProp) : TProp := fun σ i => ∃ j, i ≤ j ∧ P σ j

/-- X φ : φ holds at the next position. -/
def X (P : TProp) : TProp := fun σ i => P σ (i + 1)

def Imp (P Q : TProp) : TProp := fun σ i => P σ i → Q σ i
def And (P Q : TProp) : TProp := fun σ i => P σ i ∧ Q σ i

/-- A temporal property is *valid* if it holds at position 0 of every run. -/
def Sat (φ : TProp) : Prop := ∀ σ, IsRun σ → φ σ 0
--LISTING:ltl:end

/-- Convenience state predicates. -/
def appliedNow  : TProp := now (fun s => s.phase = Applied)
def sigValidNow : TProp := now (fun s => s.capsuleSigValid = true)
def resetNow    : TProp := now (fun s => s.resetOccurred = true)


/-! ## Transition-level lemmas -/

/-- Every transition leaves the firmware version non-decreasing: the only
    version-changing rule is `apply`, which requires a strictly-newer image. -/
theorem step_version_mono {s s'} (h : Step s s') :
    s.fwVersion ≤ s'.fwVersion := by
  cases h <;> simp_all <;> omega

/-- APPLY-GUARD: one only *enters* `Applied` (from a non-`Applied` state) via
    an authentic, strictly-newer image. No rollback is ever applied. -/
theorem apply_guard {s s'} (h : Step s s')
    (hnow : s'.phase = Applied) (hprev : s.phase ≠ Applied) :
    s.capsuleSigValid = true ∧ s.fwVersion < s.capsuleVersion := by
  cases h <;> simp_all

/-- From a `CapsuleStaged` state the only enabled transition is `reset`; it
    advances to `PostReset` and preserves the image fields. -/
theorem reset_forced {s s'} (hp : s.phase = CapsuleStaged) (h : Step s s') :
    s'.phase = PostReset
      ∧ s'.fwVersion = s.fwVersion
      ∧ s'.capsuleVersion = s.capsuleVersion
      ∧ s'.capsuleSigValid = s.capsuleSigValid := by
  cases h <;> simp_all

/-- From a `PostReset` state the only enabled transition is `beginAuth`; it
    advances to `Authenticating` and preserves the image fields. -/
theorem auth_forced {s s'} (hp : s.phase = PostReset) (h : Step s s') :
    s'.phase = Authenticating
      ∧ s'.fwVersion = s.fwVersion
      ∧ s'.capsuleVersion = s.capsuleVersion
      ∧ s'.capsuleSigValid = s.capsuleSigValid := by
  cases h <;> simp_all

/-- From an authentic, strictly-newer `Authenticating` state the `reject` guard
    is false, so the only enabled transition is `apply`: the next state is
    `Applied`. This is what makes the good path *forced* (no fairness needed). -/
theorem good_apply_forced {s s'}
    (hp : s.phase = Authenticating)
    (hsig : s.capsuleSigValid = true)
    (hver : s.fwVersion < s.capsuleVersion)
    (h : Step s s') :
    s'.phase = Applied := by
  cases h <;> simp_all <;> omega


/-! ## Inductive invariants -/

/-- SAFETY invariant: if `Applied`, the staged image's signature was valid. -/
def InvSig (s : St) : Prop := s.phase = Applied → s.capsuleSigValid = true

theorem invSig_init {s} (h : Init s) : InvSig s := by
  intro hap; rw [h.1] at hap; exact absurd hap (by decide)

theorem invSig_step {s s'} (h : Step s s') (_hs : InvSig s) : InvSig s' := by
  intro hap; cases h <;> simp_all

theorem invSig_run {σ} (hr : IsRun σ) : ∀ i, InvSig (σ i) := by
  intro i
  induction i with
  | zero      => exact invSig_init hr.1
  | succ n ih => exact invSig_step (hr.2 n) ih

/-- RESET-FIRST invariant: every phase reachable only after a reset records it.
    (Strengthened across PostReset/Authenticating/Applied to be inductive.) -/
def InvReset (s : St) : Prop :=
  (s.phase = PostReset ∨ s.phase = Authenticating ∨ s.phase = Applied) →
    s.resetOccurred = true

theorem invReset_init {s} (h : Init s) : InvReset s := by
  intro hmem; rw [h.1] at hmem
  rcases hmem with h | h | h <;> exact absurd h (by decide)

--LISTING:inv:begin
theorem invReset_step {s s'} (h : Step s s') (hs : InvReset s) : InvReset s' := by
  intro hmem
  cases h with
  | beginAuth hp => exact hs (Or.inl hp)
  | apply hp _ _ => exact hs (Or.inr (Or.inl hp))
  | _ => simp_all
--LISTING:inv:end

theorem invReset_run {σ} (hr : IsRun σ) : ∀ i, InvReset (σ i) := by
  intro i
  induction i with
  | zero      => exact invReset_init hr.1
  | succ n ih => exact invReset_step (hr.2 n) ih


/-! ## The LTL theorems (quantified over all runs) -/

/-- **1. SAFETY (authenticity).**
    `⊨ G (Applied → signature valid)`.
    The firmware never reports a capsule as applied unless its signature was
    valid — an unauthenticated image is never applied. -/
theorem safety_authentic : Sat (G (Imp appliedNow sigValidNow)) := by
  intro σ hr j _ hap
  exact invSig_run hr j hap

/-- **2a. ANTI-ROLLBACK (step monotonicity).**
    `⊨ G (fwVersion ≤ X fwVersion)`.
    The running firmware version never decreases across a step. -/
theorem antirollback_step :
    Sat (G (fun σ i => (σ i).fwVersion ≤ (σ (i + 1)).fwVersion)) := by
  intro σ hr j _
  exact step_version_mono (hr.2 j)

/-- **2b. ANTI-ROLLBACK (global monotonicity).**
    For any two positions `i ≤ j`, `fwVersion i ≤ fwVersion j`.
    No sequence of capsule updates can ever roll the version backwards. -/
theorem antirollback_global {σ} (hr : IsRun σ) :
    ∀ i j, i ≤ j → (σ i).fwVersion ≤ (σ j).fwVersion := by
  intro i j h
  induction h with
  | refl       => exact Nat.le_refl _
  | step _ ih  => exact Nat.le_trans ih (step_version_mono (hr.2 _))

/-- **3. APPLY-GUARD.**
    `⊨ G ((¬Applied ∧ X Applied) → (authentic ∧ strictly-newer)_now)`.
    Whenever a run *enters* `Applied`, the state it came from carried a valid
    signature and a strictly-newer version — a downgrade or forged image is
    never applied. (The guard is stated on the pre-state: `apply` bumps
    `fwVersion := capsuleVersion`, so strict newness holds *before* applying.) -/
theorem apply_guarded :
    Sat (G (Imp (fun σ i => (σ i).phase ≠ Applied ∧ (σ (i+1)).phase = Applied)
                (fun σ i => (σ i).capsuleSigValid = true
                            ∧ (σ i).fwVersion < (σ i).capsuleVersion))) := by
  intro σ hr j _ hpre
  exact apply_guard (hr.2 j) hpre.2 hpre.1

/-- **4. RESET-FIRST.**
    `⊨ G (Applied → reset occurred)`.
    A capsule is only ever applied after the system has actually reset
    (capsule coalescing runs in the post-reset boot, not in the runtime call). -/
theorem reset_first : Sat (G (Imp appliedNow resetNow)) := by
  intro σ hr j _ hap
  exact invReset_run hr j (Or.inr (Or.inr hap))

/-- **5. RESPONSIVENESS (liveness, fairness-free).**
    `⊨ G ((staged ∧ authentic ∧ strictly-newer) → F Applied)`.
    Once a properly-signed, strictly-newer capsule is staged, every run reaches
    `Applied`. No fairness hypothesis is required: from the good staged state the
    enabled transitions are forced (reset → beginAuth → apply), so `Applied` is
    reached within three steps. -/
def goodStaged : TProp := fun σ i =>
  (σ i).phase = CapsuleStaged
    ∧ (σ i).capsuleSigValid = true
    ∧ (σ i).fwVersion < (σ i).capsuleVersion

--LISTING:live:begin
theorem responsiveness : Sat (G (Imp goodStaged (F appliedNow))) := by
  intro σ hr j _ hgood
  obtain ⟨hStaged, hSig, hVer⟩ := hgood
  -- step 1: reset  (CapsuleStaged → PostReset), fields preserved
  obtain ⟨h1p, h1fw, h1ver, h1sig⟩ := reset_forced hStaged (hr.2 j)
  -- step 2: beginAuth (PostReset → Authenticating), fields preserved
  obtain ⟨h2p, h2fw, h2ver, h2sig⟩ := auth_forced h1p (hr.2 (j + 1))
  -- step 3: apply forced (authentic + newer ⇒ Applied)
  have h3 : (σ (j + 3)).phase = Applied := by
    apply good_apply_forced h2p
    · rw [h2sig, h1sig, hSig]
    · rw [h2fw, h1fw, h2ver, h1ver]; exact hVer
    · exact hr.2 (j + 2)
  exact ⟨j + 3, by omega, h3⟩
--LISTING:live:end

end UefiCapsuleLTL
/-
  refine_capsule.lean — Refinement-to-code liveness (Option 3).

  This is the Lean side of the Aeneas pipeline. The Rust function `advance`
  (rust/aeneas/capsule.rs) is a DETERMINISTIC good-path scheduler. Aeneas
  extracts it to a pure Lean function; here we reproduce that function and prove
  that the run it generates is a legal `IsRun`, so the EXISTING temporal
  liveness theorem `responsiveness` applies to it verbatim. That is the payoff:
  the full omega-run liveness property L, proved once abstractly, transfers to
  the code-derived deterministic implementation — liveness "lives" in Lean,
  where F/G and infinite runs exist, while the refinement guarantees the Lean
  run faithfully mirrors the Rust.

  We prove, with NO new axioms:
    1. step_advance     : ∀ s, Step s (advance s)        — advance refines Step
    2. detRun_isRun     : Init s0 → IsRun (detRun s0)     — its run is legal
    3. responsiveness_det: liveness L on the code-derived run (corollary of the
                           existing `responsiveness`)
    4. advance_three    : the bounded 3-step witness, directly on `advance`

  Compile together with the development, e.g.:
    cat ltl_capsule.lean refine_capsule.lean > /tmp/combined.lean
    lean /tmp/combined.lean
-/

namespace UefiCapsuleLTL
open Phase

/-- The deterministic good-path scheduler, mirroring the Rust `advance`
    (rust/aeneas/capsule.rs). Every branch corresponds to exactly one `Step`
    constructor, so `advance` is a legal deterministic refinement of `Step`. -/
--LISTING:advance:begin
def advance (s : St) : St :=
  match s.phase with
  | Idle           => s                                    -- stutterIdle
  | CapsuleStaged  => { s with phase := PostReset, resetOccurred := true }
  | PostReset      => { s with phase := Authenticating }
  | Authenticating =>
      if s.capsuleSigValid = true ∧ s.fwVersion < s.capsuleVersion then
        { s with phase := Applied, fwVersion := s.capsuleVersion }
      else
        { s with phase := Rejected, capsulePresent := false }
  | Applied        => { s with phase := Idle, capsulePresent := false, resetOccurred := false }
  | Rejected       => { s with phase := Idle, capsulePresent := false, resetOccurred := false }
--LISTING:advance:end

/-- **Refinement.** Every `advance` step is a real `Step`: the deterministic
    scheduler only ever takes legal transitions. -/
theorem step_advance (s : St) : Step s (advance s) := by
  unfold advance
  cases h : s.phase with
  | Idle           => exact Step.stutterIdle s h
  | CapsuleStaged  => exact Step.reset s h
  | PostReset      => exact Step.beginAuth s h
  | Authenticating =>
      by_cases hc : s.capsuleSigValid = true ∧ s.fwVersion < s.capsuleVersion
      · rw [if_pos hc]; exact Step.apply s h hc.1 hc.2
      · rw [if_neg hc]
        apply Step.reject s h
        -- ¬(sig=true ∧ fw<cap)  ⇒  sig=false ∨ cap≤fw, using only core tactics
        by_cases hs : s.capsuleSigValid = true
        · -- signature valid, so the version guard must have failed
          have hnlt : ¬ (s.fwVersion < s.capsuleVersion) := fun hlt => hc ⟨hs, hlt⟩
          exact Or.inr (Nat.le_of_not_lt hnlt)
        · -- signature not = true, hence = false (Bool)
          exact Or.inl (by cases hb : s.capsuleSigValid <;> simp_all)
  | Applied        => exact Step.finishApplied s h
  | Rejected       => exact Step.finishRejected s h

/-- The deterministic run generated by iterating `advance` from `s0`. This is
    the Lean image of running the Rust `advance` in a loop. -/
def detRun (s0 : St) : Nat → St
  | 0     => s0
  | n + 1 => advance (detRun s0 n)

/-- **The code-derived run is legal.** If `s0` is initial, the deterministic
    `advance`-run is an `IsRun`, so every theorem proved for all runs applies. -/
theorem detRun_isRun {s0 : St} (h : Init s0) : IsRun (detRun s0) := by
  refine ⟨h, ?_⟩
  intro i
  show Step (detRun s0 i) (advance (detRun s0 i))
  exact step_advance (detRun s0 i)

/-- **Refinement-to-code liveness (the payoff).** The existing temporal theorem
    `responsiveness`, proved once for all runs, transfers to the deterministic
    code-derived run: whenever a good capsule is staged at any position `j`, the
    implementation reaches `Applied`. Liveness L now holds of the Rust function,
    via the refinement, with no new proof. -/
theorem responsiveness_det {s0 : St} (h : Init s0) :
    ∀ j, goodStaged (detRun s0) j →
        ∃ k, j ≤ k ∧ (detRun s0 k).phase = Applied := by
  intro j hgood
  exact responsiveness (detRun s0) (detRun_isRun h) j (Nat.zero_le j) hgood

/-- **Safety transfers too.** Authenticity (S) on the code-derived run: the
    implementation never reports a capsule applied unless its signature was
    valid. A corollary of the existing `safety_authentic`, via `detRun_isRun` —
    the same one-line transfer works for R1, R2, G, O. -/
theorem safety_authentic_det {s0 : St} (h : Init s0) :
    ∀ j, (detRun s0 j).phase = Applied → (detRun s0 j).capsuleSigValid = true := by
  intro j
  exact safety_authentic (detRun s0) (detRun_isRun h) j (Nat.zero_le j)

/-- A staged, authentic, strictly-newer state at the state level. -/
def goodState (s : St) : Prop :=
  s.phase = CapsuleStaged ∧ s.capsuleSigValid = true ∧ s.fwVersion < s.capsuleVersion

/-- **Bounded witness, directly on `advance`.** Three deterministic steps from a
    good staged state reach `Applied` — the executable image of the forced
    3-step liveness argument, on the extracted function itself. -/
theorem advance_three {s : St} (hg : goodState s) :
    (advance (advance (advance s))).phase = Applied := by
  obtain ⟨hp, hsig, hver⟩ := hg
  simp only [advance, hp, hsig, hver, and_self, if_true]

end UefiCapsuleLTL
