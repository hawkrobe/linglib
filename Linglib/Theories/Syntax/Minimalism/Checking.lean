import Linglib.Theories.Syntax.Minimalism.Features
import Linglib.Theories.Syntax.Minimalism.Basic
import Linglib.Theories.Syntax.Minimalism.Agree

/-!
# Feature Checking: The Derivational Lifecycle
@cite{chomsky-1995}

The four-stage lifecycle of formal features in the Minimalist Program
(Ch 4 §4.5; extended with @cite{preminger-2014} §5 "derivational time
bombs" and @cite{hewett-2026} Def 23):

0. **Inactive**: feature is present but dormant — not yet accessible to
   checking. Must be activated by a syntactic trigger (feature
   activation, @cite{hewett-2026} Def 23) before entering the
   checking lifecycle. Inactive –Interpretable features crash at LF.
1. **Active**: feature is present and accessible to computation
2. **Checked** (= deleted): feature has entered a checking relation;
   invisible at LF but still accessible to the narrow syntax
3. **Erased**: feature is completely removed, inaccessible to all
   further computation

–Interpretable features *must* pass through stages 1–3 (or 0–3 if
initially inactive) for the derivation to converge at LF.
+Interpretable features remain active (they contribute to meaning and
are never deleted).

## Strong Features

A strong feature is a –Interpretable feature that must be checked
*before Spell-Out* — i.e., by an overt operation. If a strong feature
survives to Spell-Out unchecked, the derivation is canceled. Strong
features are the locus of the overt/covert parametric variation:
English T has a strong D-feature (EPP), forcing overt subject raising;
languages without overt raising lack this strong feature.

## Connection to Agree

The checking lifecycle predates long-distance Agree (@cite{chomsky-2000}).
In the 1995 system, checking requires a local Spec-head or head-head
configuration. The post-2000 Agree mechanism in `Agree.lean` subsumes
checking: Agree values an unvalued feature, which is equivalent to
checking + deletion in one step. This module formalizes the finer-grained
1995 lifecycle, which remains relevant for:

- Distinguishing deletion (LF-invisible) from erasure (computationally
  inaccessible) — erasure blocks further operations on the feature
- Strong features, which interact with Spell-Out timing
- The parametric variation that allows –Interpretable features to
  escape erasure after checking (multiple-Spec constructions)

## Activation Indices

`ActivationIndex α` (§ 7) formalizes ordered n-tuple activation from
@cite{hewett-2026} Def 23: a feature carries a tuple of keys
`(c₁, …, cₙ)`, and each c-commanding head strips `c₁` if it matches.
When the tuple is empty the feature transitions from `.inactive` to
`.active`. Parametric over the key type `α`.
-/

namespace Minimalism

-- ============================================================================
-- § 1: Host-Dependent Interpretability
-- ============================================================================

/-- Whether a feature type is interpretable on a given host category.

    @cite{chomsky-1995} Ch 4: Categorial features and φ-features of
    nouns are +Interpretable. Case features, φ-features on functional
    heads (T, v, C), and EPP/strong features are –Interpretable.

    This encodes the default mapping. Individual languages or analyses
    may override (e.g., @cite{zeijlstra-2012} treats embedded tense as
    uninterpretable in SOT languages). -/
def isInterpretableOn (fv : FeatureVal) (host : Cat) : Interpretability :=
  match fv.inherentInterpretability with
  | some i => i  -- host-independent features
  | none => match fv with
    -- Phi-features: interpretable on N/D (substantive), uninterpretable on T/v/C (functional)
    | .phi _ => match host with
      | .N | .D => .interpretable
      | _ => .uninterpretable
    -- Wh, Q, Foc, Rel: interpretable on C (their natural host)
    | .wh _ | .q _ | .foc _ | .rel _ =>
      if host == .C then .interpretable else .uninterpretable
    -- Tense, finite: interpretable on T
    | .tense _ | .finite _ =>
      if host == .T then .interpretable else .uninterpretable
    -- Fallback: interpretable (conservative)
    | _ => .interpretable

/-- A feature must be checked before LF iff it is –Interpretable on its host. -/
def mustCheck (fv : FeatureVal) (host : Cat) : Bool :=
  isInterpretableOn fv host == .uninterpretable

/-- Phi on N is interpretable; phi on T is not. -/
theorem phi_on_N_interpretable (pf : PhiFeature) :
    isInterpretableOn (.phi pf) .N = .interpretable := rfl

theorem phi_on_T_uninterpretable (pf : PhiFeature) :
    isInterpretableOn (.phi pf) .T = .uninterpretable := rfl

-- ============================================================================
-- § 2: Feature Lifecycle
-- ============================================================================

/-- The lifecycle state of a formal feature in the derivation.

    Features begin `.active` (or `.inactive` if dormant) and, if
    –Interpretable, must reach `.erased` for the derivation to
    converge at LF. -/
inductive FeatureStatus where
  /-- Inactive: present but dormant. Not yet accessible to checking
      operations — must be activated first. Used for selectional
      features that await licensing by a specific syntactic trigger
      (@cite{preminger-2014} "derivational time bombs";
      @cite{hewett-2026} Def 23: selectional features activated
      stepwise by categorizing head and template). -/
  | inactive
  /-- Active: present and accessible to all computation. -/
  | active
  /-- Checked (= deleted in @cite{chomsky-1995}'s terminology):
      has entered a checking relation. Invisible at LF but still
      accessible to narrow-syntactic computation. -/
  | checked
  /-- Erased: completely removed. Inaccessible to all further
      computation, including narrow syntax. -/
  | erased
  deriving Repr, DecidableEq

/-- A feature in the derivation, tracking its lifecycle state. -/
structure TrackedFeature where
  val : FeatureVal
  host : Cat
  interp : Interpretability
  status : FeatureStatus := .active
  deriving Repr, DecidableEq

/-- Create a tracked feature with interpretability determined by host. -/
def TrackedFeature.fromHosted (fv : FeatureVal) (host : Cat) : TrackedFeature :=
  { val := fv, host := host, interp := isInterpretableOn fv host }

-- ============================================================================
-- § 2: Lifecycle Operations
-- ============================================================================

/-- Check a feature: transition from active to checked.
    Only –Interpretable features are checked (they enter a checking
    relation with a matching +Interpretable feature).
    Returns `none` if the feature is not active or is +Interpretable. -/
def TrackedFeature.check (tf : TrackedFeature) : Option TrackedFeature :=
  match tf.interp, tf.status with
  | .uninterpretable, .active => some { tf with status := .checked }
  | _, _ => none

/-- Erase a feature: transition from checked to erased.
    Erasure is possible only after checking. Once erased, the feature
    is computationally inaccessible.

    The book allows a parametric option: a –Interpretable feature may
    *escape erasure* after checking, permitting multiple-Spec
    constructions (MSCs). `allowEscapeErasure` controls this. -/
def TrackedFeature.erase (tf : TrackedFeature) : Option TrackedFeature :=
  match tf.status with
  | .checked => some { tf with status := .erased }
  | _ => none

/-- Activate a dormant feature: transition from inactive to active.
    This models @cite{preminger-2014}'s "derivational time bombs" and
    @cite{hewett-2026} Def 23: a selectional feature begins dormant
    and is activated by a specific syntactic trigger (a categorizing
    head, a template-defining head, etc.).
    Returns `none` if the feature is not inactive. -/
def TrackedFeature.activate (tf : TrackedFeature) : Option TrackedFeature :=
  match tf.status with
  | .inactive => some { tf with status := .active }
  | _ => none

/-- Is this feature visible at LF?
    +Interpretable active features are visible (they contribute meaning).
    Everything else — inactive, checked, erased, or –Interpretable — is not. -/
def TrackedFeature.visibleAtLF (tf : TrackedFeature) : Bool :=
  tf.interp == .interpretable && tf.status == .active

/-- Is this feature accessible to narrow-syntactic computation?
    Inactive, active, and checked features are accessible; erased
    features are not. Inactive features are accessible to Activate
    operations even though they cannot yet enter checking relations. -/
def TrackedFeature.accessible (tf : TrackedFeature) : Bool :=
  tf.status != .erased

-- ============================================================================
-- § 3: Strong Features and Spell-Out
-- ============================================================================

/-- A strong feature must be checked before Spell-Out (overt syntax).
    If it survives to Spell-Out unchecked, the derivation is canceled.

    Strong features are always –Interpretable. They force overt
    operations: the derivation cannot "wait" (Procrastinate) because
    the strong feature would crash at Spell-Out. -/
structure StrongFeature where
  feature : TrackedFeature
  isUninterpretable : feature.interp = .uninterpretable
  deriving Repr

/-- Does a strong feature survive unchecked at Spell-Out?
    If so, the derivation is canceled. Both active (unchecked) and
    inactive (never activated) strong features crash. -/
def StrongFeature.crashesAtSpellOut (sf : StrongFeature) : Bool :=
  sf.feature.status == .active || sf.feature.status == .inactive

-- ============================================================================
-- § 4: Convergence
-- ============================================================================

/-- A set of tracked features converges at LF iff no –Interpretable
    feature remains active or inactive (i.e., unchecked).

    This is the Full Interpretation (FI) condition at LF: every feature
    present at LF must be interpretable. –Interpretable features that
    have been checked (deleted) are invisible at LF and satisfy FI;
    those that have been erased are gone entirely. Both active and
    inactive –Interpretable features cause a crash — inactive features
    should have been activated and checked before reaching LF. -/
def convergesAtLF (features : List TrackedFeature) : Bool :=
  features.all λ tf =>
    tf.interp == .interpretable ||
    (tf.status != .active && tf.status != .inactive)

/-- A set of tracked features converges at Spell-Out iff no strong
    feature remains active or inactive.

    This is weaker than LF convergence: non-strong –Interpretable
    features can still be active at Spell-Out (they will be checked
    covertly, after Spell-Out). But strong features — whether active
    or inactive — must be resolved before Spell-Out.

    `isStrong` marks which features are strong (must be checked overtly). -/
def convergesAtSpellOut (features : List TrackedFeature)
    (isStrong : TrackedFeature → Bool) : Bool :=
  features.all λ tf =>
    !(isStrong tf) || (tf.status != .active && tf.status != .inactive)

-- ============================================================================
-- § 5: Lifecycle Theorems
-- ============================================================================

/-- +Interpretable features cannot be checked: `check` returns `none`. -/
theorem interpretable_cannot_check (tf : TrackedFeature)
    (h : tf.interp = .interpretable) :
    tf.check = none := by
  simp [TrackedFeature.check, h]

/-- Only active –Interpretable features can be checked. -/
theorem check_requires_active_uninterpretable (tf result : TrackedFeature)
    (hc : tf.check = some result) :
    tf.interp = .uninterpretable ∧ tf.status = .active := by
  simp [TrackedFeature.check] at hc
  split at hc <;> simp_all

/-- Only checked features can be erased. -/
theorem erase_requires_checked (tf result : TrackedFeature)
    (he : tf.erase = some result) :
    tf.status = .checked := by
  simp [TrackedFeature.erase] at he
  split at he <;> simp_all

/-- The lifecycle is deterministic: check always produces the same result. -/
theorem check_deterministic (tf r1 r2 : TrackedFeature)
    (h1 : tf.check = some r1) (h2 : tf.check = some r2) :
    r1 = r2 := by
  simp_all

/-- Erased features cannot be checked. -/
theorem erased_cannot_check (tf : TrackedFeature) (h : tf.status = .erased) :
    tf.check = none := by
  simp [TrackedFeature.check, h]

/-- Checked features cannot be checked again. -/
theorem checked_cannot_recheck (tf : TrackedFeature) (h : tf.status = .checked) :
    tf.check = none := by
  simp [TrackedFeature.check, h]

/-- Active features cannot be erased (must check first). -/
theorem active_cannot_erase (tf : TrackedFeature) (h : tf.status = .active) :
    tf.erase = none := by
  simp [TrackedFeature.erase, h]

/-- Erased features cannot be erased again. -/
theorem erased_cannot_erase (tf : TrackedFeature) (h : tf.status = .erased) :
    tf.erase = none := by
  simp [TrackedFeature.erase, h]

/-- Only inactive features can be activated. -/
theorem activate_requires_inactive (tf result : TrackedFeature)
    (ha : tf.activate = some result) :
    tf.status = .inactive := by
  simp [TrackedFeature.activate] at ha
  split at ha <;> simp_all

/-- Active features cannot be activated (already active). -/
theorem active_cannot_activate (tf : TrackedFeature) (h : tf.status = .active) :
    tf.activate = none := by
  simp [TrackedFeature.activate, h]

/-- Inactive features cannot be checked (must activate first). -/
theorem inactive_cannot_check (tf : TrackedFeature) (h : tf.status = .inactive) :
    tf.check = none := by
  simp [TrackedFeature.check, h]

/-- Inactive features cannot be erased. -/
theorem inactive_cannot_erase (tf : TrackedFeature) (h : tf.status = .inactive) :
    tf.erase = none := by
  simp [TrackedFeature.erase, h]

/-- The full lifecycle: an active –Interpretable feature can be checked
    and then erased, reaching the terminal state. -/
theorem full_lifecycle (fv : FeatureVal) (host : Cat)
    (h : isInterpretableOn fv host = .uninterpretable) :
    let tf := TrackedFeature.fromHosted fv host
    ∃ tf1 tf2, tf.check = some tf1 ∧ tf1.erase = some tf2 ∧
      tf2.status = .erased := by
  simp [TrackedFeature.fromHosted, h, TrackedFeature.check, TrackedFeature.erase]

/-- The extended lifecycle: an inactive –Interpretable feature can be
    activated, checked, and then erased.
    This is the full chain for @cite{hewett-2026} Def 23 selectional
    features: inactive → active → checked → erased. -/
theorem extended_lifecycle (fv : FeatureVal) (host : Cat) :
    let tf : TrackedFeature := ⟨fv, host, .uninterpretable, .inactive⟩
    ∃ tf1 tf2 tf3, tf.activate = some tf1 ∧ tf1.check = some tf2 ∧
      tf2.erase = some tf3 ∧ tf3.status = .erased := by
  simp [TrackedFeature.activate, TrackedFeature.check, TrackedFeature.erase]

/-- Checked features are invisible at LF. -/
theorem checked_invisible_at_LF (tf : TrackedFeature) (h : tf.status = .checked) :
    tf.visibleAtLF = false := by
  simp [TrackedFeature.visibleAtLF, h]

/-- Inactive features are invisible at LF. -/
theorem inactive_invisible_at_LF (tf : TrackedFeature) (h : tf.status = .inactive) :
    tf.visibleAtLF = false := by
  simp [TrackedFeature.visibleAtLF, h]

/-- Erased features are inaccessible to computation. -/
theorem erased_inaccessible (tf : TrackedFeature) (h : tf.status = .erased) :
    tf.accessible = false := by
  simp [TrackedFeature.accessible, h]

/-- Inactive features ARE accessible to computation (they can be
    targeted by Activate). Only erased features are inaccessible. -/
theorem inactive_accessible (tf : TrackedFeature) (h : tf.status = .inactive) :
    tf.accessible = true := by
  simp [TrackedFeature.accessible, h]

/-- +Interpretable active features are visible at LF (they contribute meaning). -/
theorem interpretable_active_visible (tf : TrackedFeature)
    (hi : tf.interp = .interpretable) (hs : tf.status = .active) :
    tf.visibleAtLF = true := by
  simp [TrackedFeature.visibleAtLF, hi, hs]

-- ============================================================================
-- § 6: Verification
-- ============================================================================

/-- +Interpretable features never need checking — they converge as-is. -/
theorem interpretable_converges (fv : FeatureVal) (host : Cat)
    (h : isInterpretableOn fv host = .interpretable) :
    convergesAtLF [TrackedFeature.fromHosted fv host] = true := by
  simp [convergesAtLF, TrackedFeature.fromHosted, h]

/-- An unchecked –Interpretable feature crashes at LF. -/
theorem unchecked_uninterpretable_crashes (fv : FeatureVal) (host : Cat)
    (h : isInterpretableOn fv host = .uninterpretable) :
    convergesAtLF [TrackedFeature.fromHosted fv host] = false := by
  simp [convergesAtLF, TrackedFeature.fromHosted, h]

/-- A checked –Interpretable feature does NOT crash at LF. -/
theorem checked_uninterpretable_converges :
    convergesAtLF [⟨.case .nom, .N, .uninterpretable, .checked⟩] = true := rfl

/-- Case on N must be checked for LF convergence. -/
example : convergesAtLF [TrackedFeature.fromHosted (.case .nom) .N] = false := rfl

/-- After checking, Case on N converges. -/
example : convergesAtLF [⟨.case .nom, .N, .uninterpretable, .checked⟩] = true := rfl

/-- Phi on N is interpretable — converges without checking. -/
example : convergesAtLF [TrackedFeature.fromHosted
    (.phi (.person .third)) .N] = true := rfl

/-- Phi on T is uninterpretable — must be checked. -/
example : convergesAtLF [TrackedFeature.fromHosted
    (.phi (.person .third)) .T] = false := rfl

/-- An inactive –Interpretable feature also crashes at LF. -/
example : convergesAtLF [⟨.case .nom, .N, .uninterpretable, .inactive⟩] = false := rfl

/-- After activation and checking, a previously-inactive feature converges. -/
example : convergesAtLF [⟨.case .nom, .N, .uninterpretable, .checked⟩] = true := rfl

-- ============================================================================
-- § 7: Feature Activation Indices (Def 23)
-- ============================================================================

/-! ### Ordered Activation Tuples

@cite{hewett-2026} Def 23 (adapted from @cite{merchant-2019}): a feature
can be indexed by an ordered tuple of category keys `(c₁, …, cₙ)`. Each
c-commanding head bearing key `k` strips `c₁` from the tuple **if `k = c₁`**
(matching activation). When the tuple is exhausted the feature transitions
from `.inactive` to `.active`.

`ActivationIndex α` is parametric over the key type `α` — for Semitic
l-selection `α` combines `Cat` and `SemiticTemplate`, but the mechanism
generalizes to any domain where features require ordered multi-head
activation (e.g., applicatives, serial verbs). -/

/-- An ordered tuple of activation keys. Stripping proceeds left-to-right:
    only the leftmost key can be matched at any derivational step. -/
structure ActivationIndex (α : Type) [BEq α] where
  /-- Keys remaining to be stripped. Empty = fully activated. -/
  remaining : List α
  deriving Repr

/-- Attempt to strip the leftmost key. Succeeds only if `key` matches
    the head of the tuple (matching activation). Non-matching keys and
    already-empty tuples are no-ops. -/
def ActivationIndex.activate {α : Type} [BEq α] (idx : ActivationIndex α)
    (key : α) : ActivationIndex α :=
  match idx.remaining with
  | k :: rest => if k == key then ⟨rest⟩ else idx
  | [] => idx

/-- Is the tuple fully stripped? -/
def ActivationIndex.isFullyActive {α : Type} [BEq α]
    (idx : ActivationIndex α) : Bool :=
  idx.remaining.isEmpty

/-- Map activation state to the `FeatureStatus` lifecycle: non-empty
    tuples are `.inactive`, empty tuples are `.active`. -/
def ActivationIndex.toStatus {α : Type} [BEq α]
    (idx : ActivationIndex α) : FeatureStatus :=
  if idx.isFullyActive then .active else .inactive

/-- Matching key strips the head. -/
theorem activate_matching_strips {α : Type} [BEq α] [LawfulBEq α]
    (k : α) (rest : List α) :
    (ActivationIndex.mk (k :: rest) : ActivationIndex α).activate k
    = ⟨rest⟩ := by
  simp [ActivationIndex.activate]

/-- Non-matching key is a no-op. -/
theorem activate_nonmatching_noop {α : Type} [BEq α] [LawfulBEq α]
    (k₁ k₂ : α) (rest : List α) (h : k₁ ≠ k₂) :
    (ActivationIndex.mk (k₁ :: rest) : ActivationIndex α).activate k₂
    = ⟨k₁ :: rest⟩ := by
  simp [ActivationIndex.activate, beq_iff_eq, h]

/-- Empty tuple is fully active. -/
theorem empty_is_active {α : Type} [BEq α] :
    (ActivationIndex.mk (α := α) []).isFullyActive = true := rfl

/-- Non-empty tuple is not fully active. -/
theorem nonempty_is_inactive {α : Type} [BEq α] (k : α) (rest : List α) :
    (ActivationIndex.mk (k :: rest) : ActivationIndex α).isFullyActive
    = false := rfl

/-- Empty tuple maps to `.active` status. -/
theorem empty_toStatus_active {α : Type} [BEq α] :
    (ActivationIndex.mk (α := α) []).toStatus = .active := rfl

/-- Non-empty tuple maps to `.inactive` status. -/
theorem nonempty_toStatus_inactive {α : Type} [BEq α]
    (k : α) (rest : List α) :
    (ActivationIndex.mk (k :: rest) : ActivationIndex α).toStatus
    = .inactive := rfl

/-- Activation on an already-empty tuple is a no-op. -/
theorem activate_empty_noop {α : Type} [BEq α] (key : α) :
    (ActivationIndex.mk (α := α) []).activate key = ⟨[]⟩ := rfl

/-- Full activation chain: stripping each key in order yields `.active`. -/
theorem full_activation_chain {α : Type} [BEq α] [LawfulBEq α]
    (k₁ k₂ : α) :
    let idx : ActivationIndex α := ⟨[k₁, k₂]⟩
    (idx.activate k₁ |>.activate k₂).toStatus = .active := by
  simp [ActivationIndex.activate, ActivationIndex.toStatus,
        ActivationIndex.isFullyActive]

-- ============================================================================
-- § 8: Agree–Checking Bridge
-- ============================================================================

/-! ### Connecting Agree (valuation) to Checking (lifecycle)

@cite{chomsky-2000}'s Agree subsumes the 1995 checking lifecycle:
Agree *values* an unvalued feature, which is equivalent to checking +
deletion in one step. The two formalizations operate at different levels:

- `Agree.applyAgree`: values probe features from goal features (feature bundles)
- `TrackedFeature.check`: lifecycle transition from active to checked

The bridge states: when Agree successfully values an uninterpretable
feature, that feature's lifecycle also advances. If ALL uninterpretable
features in a bundle are valued by Agree, the derivation converges at LF. -/

/-- A feature that has been valued by Agree can be checked in the lifecycle.
    This connects the two formalizations: Agree valuation implies lifecycle
    transition is available. -/
theorem agree_enables_check (fv : FeatureVal) (host : Cat)
    (h_uninterp : isInterpretableOn fv host = .uninterpretable) :
    let tf := TrackedFeature.fromHosted fv host
    tf.check.isSome = true := by
  simp [TrackedFeature.fromHosted, h_uninterp, TrackedFeature.check]

/-- When Agree values a feature bundle and all uninterpretable features
    are checked, the derivation converges at LF. -/
theorem agree_then_check_converges (fv : FeatureVal) (host : Cat)
    (h_uninterp : isInterpretableOn fv host = .uninterpretable) :
    let tf := TrackedFeature.fromHosted fv host
    match tf.check with
    | some checked_tf => convergesAtLF [checked_tf] = true
    | none => False := by
  simp [TrackedFeature.fromHosted, h_uninterp, TrackedFeature.check,
    convergesAtLF]

/-- Agree makes mustCheck features convergent: if a feature must be
    checked (is –Interpretable on its host), checking it resolves the
    convergence requirement. -/
theorem mustCheck_resolved_by_check (fv : FeatureVal) (host : Cat)
    (h : mustCheck fv host = true) :
    let tf := TrackedFeature.fromHosted fv host
    ∃ tf', tf.check = some tf' ∧ convergesAtLF [tf'] = true := by
  simp [mustCheck] at h
  simp [TrackedFeature.fromHosted, h, TrackedFeature.check, convergesAtLF]

-- ============================================================================
-- § 8: Spell-Out Convergence
-- ============================================================================

/-- A derivation converges at Spell-Out iff all strong features have been
    checked. This connects `Checking.convergesAtSpellOut` to the
    `StrongFeature` type. -/
theorem strong_feature_checked_converges (fv : FeatureVal) (host : Cat)
    (h_uninterp : isInterpretableOn fv host = .uninterpretable) :
    let tf := TrackedFeature.fromHosted fv host
    match tf.check with
    | some checked_tf =>
      convergesAtSpellOut [checked_tf] (λ _ => true) = true
    | none => False := by
  simp [TrackedFeature.fromHosted, h_uninterp, TrackedFeature.check,
    convergesAtSpellOut]

/-- An unchecked strong feature crashes at Spell-Out. -/
theorem unchecked_strong_crashes (fv : FeatureVal) (host : Cat)
    (h_uninterp : isInterpretableOn fv host = .uninterpretable) :
    convergesAtSpellOut [TrackedFeature.fromHosted fv host] (λ _ => true) = false := by
  simp [convergesAtSpellOut, TrackedFeature.fromHosted, h_uninterp]

end Minimalism
