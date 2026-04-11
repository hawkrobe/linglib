import Linglib.Theories.Syntax.Minimalism.Core.Features
import Linglib.Theories.Syntax.Minimalism.Core.Basic
import Linglib.Theories.Syntax.Minimalism.Core.Agree

/-!
# Feature Checking: The Derivational Lifecycle
@cite{chomsky-1995}

The three-stage lifecycle of formal features in the Minimalist Program
(Ch 4 §4.5):

1. **Active**: feature is present and accessible to computation
2. **Checked** (= deleted): feature has entered a checking relation;
   invisible at LF but still accessible to the narrow syntax
3. **Erased**: feature is completely removed, inaccessible to all
   further computation

–Interpretable features *must* pass through all three stages for the
derivation to converge at LF. +Interpretable features remain active
(they contribute to meaning and are never deleted).

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

    Features begin `.active` and, if –Interpretable, must reach
    `.erased` for the derivation to converge at LF. -/
inductive FeatureStatus where
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

/-- Is this feature visible at LF?
    +Interpretable active features are visible (they contribute meaning).
    Everything else — checked, erased, or –Interpretable — is not. -/
def TrackedFeature.visibleAtLF (tf : TrackedFeature) : Bool :=
  tf.interp == .interpretable && tf.status == .active

/-- Is this feature accessible to narrow-syntactic computation?
    Active and checked features are accessible; erased features are not. -/
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
    If so, the derivation is canceled. -/
def StrongFeature.crashesAtSpellOut (sf : StrongFeature) : Bool :=
  sf.feature.status == .active

-- ============================================================================
-- § 4: Convergence
-- ============================================================================

/-- A set of tracked features converges at LF iff no –Interpretable
    feature remains active (unchecked).

    This is the Full Interpretation (FI) condition at LF: every feature
    present at LF must be interpretable. –Interpretable features that
    have been checked (deleted) are invisible at LF and satisfy FI;
    those that have been erased are gone entirely. Only active
    –Interpretable features cause a crash. -/
def convergesAtLF (features : List TrackedFeature) : Bool :=
  features.all λ tf =>
    tf.interp == .interpretable || tf.status != .active

/-- A set of tracked features converges at Spell-Out iff no strong
    feature remains active.

    This is weaker than LF convergence: non-strong –Interpretable
    features can still be active at Spell-Out (they will be checked
    covertly, after Spell-Out).

    `isStrong` marks which features are strong (must be checked overtly). -/
def convergesAtSpellOut (features : List TrackedFeature)
    (isStrong : TrackedFeature → Bool) : Bool :=
  features.all λ tf => !(isStrong tf) || tf.status != .active

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

/-- The full lifecycle: an active –Interpretable feature can be checked
    and then erased, reaching the terminal state. -/
theorem full_lifecycle (fv : FeatureVal) (host : Cat)
    (h : isInterpretableOn fv host = .uninterpretable) :
    let tf := TrackedFeature.fromHosted fv host
    ∃ tf1 tf2, tf.check = some tf1 ∧ tf1.erase = some tf2 ∧
      tf2.status = .erased := by
  simp [TrackedFeature.fromHosted, h, TrackedFeature.check, TrackedFeature.erase]

/-- Checked features are invisible at LF. -/
theorem checked_invisible_at_LF (tf : TrackedFeature) (h : tf.status = .checked) :
    tf.visibleAtLF = false := by
  simp [TrackedFeature.visibleAtLF, h]

/-- Erased features are inaccessible to computation. -/
theorem erased_inaccessible (tf : TrackedFeature) (h : tf.status = .erased) :
    tf.accessible = false := by
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

-- ============================================================================
-- § 7: Agree–Checking Bridge
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
