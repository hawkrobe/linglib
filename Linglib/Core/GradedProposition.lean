import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Order.Basic

/-!
# Graded Propositions

Infrastructure for graded/continuous-valued propositions (W → ℚ) used in
probabilistic approaches to semantics.
-/

namespace Core.GradedProposition

/-- A graded proposition assigns a truth degree in ℚ to each world. -/
abbrev GProp (W : Type*) := W → ℚ

variable {W : Type*}

/-- Graded negation: P(¬A) = 1 - P(A). -/
def neg (p : GProp W) : GProp W := fun w => 1 - p w

/-- Graded conjunction: P(A ∧ B) = P(A) × P(B) under independence. -/
def conj (p q : GProp W) : GProp W := fun w => p w * q w

/-- Graded disjunction: P(A ∨ B) = P(A) + P(B) - P(A)P(B) under independence. -/
def disj (p q : GProp W) : GProp W := fun w => p w + q w - p w * q w

/-- Minimum-based conjunction (alternative to product). -/
def conjMin (p q : GProp W) : GProp W := fun w => min (p w) (q w)

/-- Maximum-based disjunction (alternative to probabilistic or). -/
def disjMax (p q : GProp W) : GProp W := fun w => max (p w) (q w)

/-- The always-true graded proposition (degree 1 everywhere). -/
def top : GProp W := fun _ => 1

/-- The always-false graded proposition (degree 0 everywhere). -/
def bot : GProp W := fun _ => 0

/-- Graded entailment: p entails q iff p(w) ≤ q(w) for all worlds. -/
def entails (p q : GProp W) : Prop := ∀ w, p w ≤ q w

/-- Graded equivalence: p and q have the same truth degree everywhere. -/
def equiv (p q : GProp W) : Prop := ∀ w, p w = q w

instance : LE (GProp W) where
  le := entails

instance : Preorder (GProp W) where
  le := entails
  le_refl := fun _ _ => le_refl _
  le_trans := fun _ _ _ hab hbc w => le_trans (hab w) (hbc w)

instance : Top (GProp W) where
  top := top

instance : Bot (GProp W) where
  bot := bot

/-- Partial order on graded propositions. -/
instance : PartialOrder (GProp W) where
  le := entails
  le_refl := fun _ _ => le_refl _
  le_trans := fun _ _ _ hab hbc w => le_trans (hab w) (hbc w)
  le_antisymm := fun p q hpq hqp => by
    funext w
    exact le_antisymm (hpq w) (hqp w)

/-- Convert a Boolean proposition to a graded proposition. -/
def ofBool (p : W → Bool) : GProp W := fun w => if p w then 1 else 0

/-- Alias matching the existing RSA function name. -/
def boolToGProp (p : W → Bool) : GProp W := ofBool p

/-- Graded negation is involutive: neg (neg p) = p. -/
theorem neg_involutive (p : GProp W) : neg (neg p) = p := by
  funext w
  simp only [neg]
  ring

/-- Graded negation is antitone: if p ≤ q then neg q ≤ neg p. -/
theorem neg_antitone (p q : GProp W) (h : entails p q) : entails (neg q) (neg p) := by
  intro w
  simp only [neg]
  linarith [h w]

/-- Negation swaps top and bot. -/
theorem neg_top : neg (top : GProp W) = bot := by
  funext w
  simp [neg, top, bot]

theorem neg_bot : neg (bot : GProp W) = top := by
  funext w
  simp [neg, top, bot]

/-- Product conjunction is commutative. -/
theorem conj_comm (p q : GProp W) : conj p q = conj q p := by
  funext w
  simp only [conj]
  ring

/-- Product conjunction is associative. -/
theorem conj_assoc (p q r : GProp W) : conj (conj p q) r = conj p (conj q r) := by
  funext w
  simp only [conj]
  ring

/-- Top is the identity for product conjunction. -/
theorem conj_top (p : GProp W) : conj p top = p := by
  funext w
  simp only [conj, top]
  ring

theorem top_conj (p : GProp W) : conj top p = p := by
  funext w
  simp only [conj, top]
  ring

/-- Bot is absorbing for product conjunction. -/
theorem conj_bot (p : GProp W) : conj p bot = bot := by
  funext w
  simp only [conj, bot]
  ring

/-- Probabilistic disjunction is commutative. -/
theorem disj_comm (p q : GProp W) : disj p q = disj q p := by
  funext w
  simp only [disj]
  ring

/-- Bot is the identity for disjunction. -/
theorem disj_bot (p : GProp W) : disj p bot = p := by
  funext w
  simp only [disj, bot]
  ring

/-- Top is absorbing for disjunction. -/
theorem disj_top (p : GProp W) : disj p top = top := by
  funext w
  simp only [disj, top]
  ring

/-- De Morgan's law for graded conjunction. -/
theorem deMorgan_conj (p q : GProp W) : neg (conj p q) = disj (neg p) (neg q) := by
  funext w
  simp only [neg, conj, disj]
  ring

/-- De Morgan's law for graded disjunction. -/
theorem deMorgan_disj (p q : GProp W) : neg (disj p q) = conj (neg p) (neg q) := by
  funext w
  simp only [neg, conj, disj]
  ring

/-- Negation preserves [0,1] bounds. -/
theorem neg_preserves_bounds (p : GProp W) (w : W)
    (h0 : 0 ≤ p w) (h1 : p w ≤ 1) : 0 ≤ neg p w ∧ neg p w ≤ 1 := by
  simp only [neg]
  constructor
  · linarith
  · linarith

/-- Conjunction preserves [0,1] bounds. -/
theorem conj_preserves_bounds (p q : GProp W) (w : W)
    (hp0 : 0 ≤ p w) (hp1 : p w ≤ 1) (hq0 : 0 ≤ q w) (hq1 : q w ≤ 1) :
    0 ≤ conj p q w ∧ conj p q w ≤ 1 := by
  simp only [conj]
  constructor
  · exact mul_nonneg hp0 hq0
  · calc p w * q w ≤ p w * 1 := by exact mul_le_mul_of_nonneg_left hq1 hp0
    _ = p w := by ring
    _ ≤ 1 := hp1

/-- Disjunction preserves [0,1] bounds. -/
theorem disj_preserves_bounds (p q : GProp W) (w : W)
    (hp0 : 0 ≤ p w) (hp1 : p w ≤ 1) (hq0 : 0 ≤ q w) (hq1 : q w ≤ 1) :
    0 ≤ disj p q w ∧ disj p q w ≤ 1 := by
  simp only [disj]
  constructor
  · -- p + q - pq ≥ 0 when p,q ∈ [0,1]
    have h : p w + q w - p w * q w = p w + q w * (1 - p w) := by ring
    rw [h]
    have hp1' : 0 ≤ 1 - p w := by linarith
    exact add_nonneg hp0 (mul_nonneg hq0 hp1')
  · -- p + q - pq ≤ 1 when p,q ∈ [0,1]
    have h : p w + q w - p w * q w = 1 - (1 - p w) * (1 - q w) := by ring
    rw [h]
    have hp1' : 0 ≤ 1 - p w := by linarith
    have hq1' : 0 ≤ 1 - q w := by linarith
    linarith [mul_nonneg hp1' hq1']

/-- Conjunction is monotone in both arguments. -/
theorem conj_monotone_left (p q r : GProp W)
    (hpq : entails p q) (hr : ∀ w, 0 ≤ r w) : entails (conj p r) (conj q r) := by
  intro w
  simp only [conj]
  exact mul_le_mul_of_nonneg_right (hpq w) (hr w)

/-- Disjunction is monotone in both arguments. -/
theorem disj_monotone_left (p q r : GProp W)
    (hpq : entails p q) (_hr : ∀ w, 0 ≤ r w) (hr1 : ∀ w, r w ≤ 1) :
    entails (disj p r) (disj q r) := by
  intro w
  simp only [disj]
  have h1 : p w + r w - p w * r w ≤ q w + r w - q w * r w := by
    have hdiff : q w - p w ≥ 0 := by linarith [hpq w]
    have hr1w := hr1 w
    calc p w + r w - p w * r w
        = p w * (1 - r w) + r w := by ring
      _ ≤ q w * (1 - r w) + r w := by linarith [mul_nonneg hdiff (by linarith : 0 ≤ 1 - r w)]
      _ = q w + r w - q w * r w := by ring
  exact h1

/-- When restricted to Boolean values, graded negation equals Boolean negation. -/
theorem neg_ofBool (p : W → Bool) :
    neg (ofBool p) = ofBool (fun w => !p w) := by
  funext w
  simp only [neg, ofBool]
  split <;> simp_all

/-- When restricted to Boolean values, graded conjunction equals Boolean conjunction. -/
theorem conj_ofBool (p q : W → Bool) :
    conj (ofBool p) (ofBool q) = ofBool (fun w => p w && q w) := by
  funext w
  simp only [conj, ofBool]
  split <;> split <;> simp_all

/-- When restricted to Boolean values, graded disjunction equals Boolean disjunction. -/
theorem disj_ofBool (p q : W → Bool) :
    disj (ofBool p) (ofBool q) = ofBool (fun w => p w || q w) := by
  funext w
  simp only [disj, ofBool]
  split <;> split <;> simp_all

scoped prefix:75 "∼" => neg
scoped infixl:65 " ⊗ " => conj      -- Product conjunction
scoped infixl:60 " ⊕ " => disj      -- Probabilistic disjunction
scoped infixl:65 " ⊓ᵍ " => conjMin  -- Min conjunction
scoped infixl:60 " ⊔ᵍ " => disjMax  -- Max disjunction

/-- A graded predicate is a function from entities to truth degrees. -/
abbrev GPred (E : Type*) := E → ℚ

/-- Lift a Boolean predicate to a graded predicate. -/
def GPred.ofBool {E : Type*} (p : E → Bool) : GPred E :=
  fun e => if p e then 1 else 0

/-- Semantic reliability parameters for a feature dimension. -/
structure FeatureReliability where
  /-- Truth degree when feature matches -/
  onMatch : ℚ := 1
  /-- Truth degree when feature doesn't match -/
  onMismatch : ℚ := 0
  /-- Match value should be higher than mismatch -/
  match_gt_mismatch : onMismatch ≤ onMatch := by native_decide
  deriving Repr

/-- Boolean (crisp) feature reliability. -/
def FeatureReliability.crisp : FeatureReliability :=
  { onMatch := 1, onMismatch := 0 }

/-- High reliability feature (like color). -/
def FeatureReliability.high : FeatureReliability :=
  { onMatch := 99/100, onMismatch := 1/100, match_gt_mismatch := by native_decide }

/-- Medium reliability feature (like size). -/
def FeatureReliability.medium : FeatureReliability :=
  { onMatch := 8/10, onMismatch := 2/10, match_gt_mismatch := by native_decide }

/-- Apply a feature reliability to a Boolean match result. -/
def FeatureReliability.apply (rel : FeatureReliability) (isMatch : Bool) : ℚ :=
  if isMatch then rel.onMatch else rel.onMismatch

/-- Entailment is preserved by `ofBool`. -/
theorem entails_ofBool_of_implies {W : Type*} (p q : W → Bool) (h : ∀ w, p w → q w) :
    entails (ofBool p) (ofBool q) := by
  intro w
  simp only [ofBool]
  cases hp : p w <;> cases hq : q w <;> simp_all

/-- Graded entailment reduces to Boolean entailment for {0,1} propositions. -/
theorem entails_iff_bool {W : Type*} (p q : W → Bool) :
    entails (ofBool p) (ofBool q) ↔ ∀ w, p w → q w := by
  constructor
  · intro h w hp
    have hle := h w
    simp only [ofBool] at hle
    cases hpw : p w <;> cases hqw : q w <;> simp_all
    -- The contradiction case: 1 ≤ 0
    exact absurd hle (by decide : ¬(1 : ℚ) ≤ 0)
  · exact entails_ofBool_of_implies p q

/-- Bot is the smallest graded proposition (for non-negative propositions). -/
theorem bot_entails (p : GProp W) (hp : ∀ w, 0 ≤ p w) : entails bot p := by
  intro w
  simp only [bot]
  exact hp w

end Core.GradedProposition
