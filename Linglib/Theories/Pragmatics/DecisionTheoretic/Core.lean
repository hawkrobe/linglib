import Linglib.Core.Question.Hamblin
import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic

/-!
# Decision-Theoretic Semantics: Core
@cite{merin-1999}

Core definitions for Merin's Decision-Theoretic Semantics (DTS). Meaning is
explicated through *signed relevance* — the Bayes factor P(E|H)/P(E|¬H) —
relative to a dichotomic issue {H, ¬H}.

Predicates over worlds are `Set W`; arithmetic operations carry
`[DecidablePred]` constraints at use sites following the mathlib idiom.

## Key Definitions

- `DTSContext` — a dichotomic issue (`topic : Set W`) plus a prior
  probability distribution. Following mathlib's `Filter.principal` pattern,
  the polar interrogative is not given a separate wrapper type: the
  `topic` is stored directly, and the inquisitive view is recovered as
  `DTSContext.toCoreIssue ctx = Core.Question.polar {w | ctx.topic w}` at
  consumption sites that need the general inquisitive-content lattice.
- `condProb` — conditional probability P(E|H) over finite worlds
- `bayesFactor` — P(E|H) / P(E|¬H), exact rational arithmetic
- `posRelevant` / `negRelevant` / `irrelevant` — ordinal relevance predicates
- `hContrary` — A and B have opposite relevance signs
- `CIP` — Conditional Independence Presumption
- `pxor` — exclusive disjunction for `Set W`

## Main Results

- **Corollary 3** (`sign_reversal`): BF_H(E) · BF_{¬H}(E) = 1
- **Fact 5** (`bayes_factor_multiplicative_under_cip`): Under CIP,
  BF(A∧B) = BF(A) · BF(B)
- **Theorem 6b** (`xor_not_necessarily_positive`): Counterexample showing
  XOR of two positively relevant propositions can be negatively relevant

-/

namespace DTS

/-- 4-world example type. Used by `xor_not_necessarily_positive` and
    consumers in this directory. -/
inductive World4 where
  | w0 | w1 | w2 | w3
  deriving DecidableEq, Repr, Inhabited, Fintype

-- ============================================================
-- Section 1: Core Types
-- ============================================================

/-- A DTS context: a dichotomic hypothesis `topic` (the proposition H,
    with ¬H implicit) plus a prior probability distribution.

    Following mathlib's `Filter.principal` pattern, the polar
    interrogative {H, ¬H} is not packaged as a separate wrapper type —
    the topic is stored directly, and the inquisitive view is recovered
    on demand via `DTSContext.toCoreIssue`. -/
structure DTSContext (W : Type*) where
  /-- The hypothesis H. The dichotomic issue {H, ¬H} is recovered as
      `Core.Question.polar topic`. -/
  topic : Set W
  /-- Decidability of `topic` — required so that arithmetic over finite
      worlds (`probSum`, `condProb`) is well-defined without invoking
      `Classical.propDecidable` at every use site. -/
  topicDec : DecidablePred (· ∈ topic)
  /-- Prior probability distribution over worlds (rational-valued). -/
  prior : W → ℚ

attribute [instance] DTSContext.topicDec

/-- Swap the issue: replace H with ¬H. -/
def swapIssue {W : Type*} (ctx : DTSContext W) : DTSContext W :=
  { topic := ctx.topicᶜ,
    topicDec := inferInstance,
    prior := ctx.prior }

/-- Forgetful projection from a DTS context to the general `Core.Question`
    lattice via the polar interrogative content of the topic
    proposition. The two representations agree on the underlying
    question semantics: a DTS dichotomy {H, ¬H} is exactly the polar
    interrogative of H, with two alternatives ⟦H⟧ and ⟦¬H⟧. -/
def DTSContext.toCoreIssue {W : Type*} (ctx : DTSContext W) : Core.Question W :=
  Core.Question.polar {w | ctx.topic w}

/-- Every DTS dichotomic issue is non-informative (`info = univ`):
    the question `{H, ¬H}` itself rules out no worlds; only an answer
    to it does. Inherited from `Core.Question.info_polar`. -/
@[simp] theorem DTSContext.toCoreIssue_info {W : Type*} (ctx : DTSContext W) :
    ctx.toCoreIssue.info = Set.univ :=
  Core.Question.info_polar _

/-- A DTS dichotomy is genuinely inquisitive (raises an unsettled
    question over the universal info state) iff its topic is non-trivial:
    neither everything nor nothing satisfies H. Inherited from
    `Core.Question.isInquisitive_polar_iff`. -/
theorem DTSContext.toCoreIssue_isInquisitive_iff {W : Type*} (ctx : DTSContext W) :
    ctx.toCoreIssue.isInquisitive ↔
      {w | ctx.topic w} ≠ ∅ ∧ {w | ctx.topic w} ≠ Set.univ :=
  Core.Question.isInquisitive_polar_iff _

-- ============================================================
-- Section 2: Probability
-- ============================================================

/-- Sum of prior probabilities over worlds satisfying a predicate. -/
def probSum {W : Type*} [Fintype W] (prior : W → ℚ) (p : Set W)
    [DecidablePred (· ∈ p)] : ℚ :=
  ∑ w : W, if w ∈ p then prior w else 0

/-- Conditional probability P(E|H) = P(E∧H) / P(H).

Returns 0 when P(H) = 0 (undefined conditioning). -/
def condProb {W : Type*} [Fintype W] (prior : W → ℚ)
    (e h : Set W) [DecidablePred (· ∈ e)] [DecidablePred (· ∈ h)] : ℚ :=
  let pH := probSum prior h
  if pH = 0 then 0
  else probSum prior (e ∩ h) / pH

/-- Marginal (unconditional) probability P(E) = P(E|⊤). -/
def margProb {W : Type*} [Fintype W] (prior : W → ℚ) (e : Set W)
    [DecidablePred (· ∈ e)] : ℚ :=
  probSum prior e

-- ============================================================
-- Section 3: Bayes Factor and Relevance
-- ============================================================

/-- Bayes factor: P(E|H) / P(E|¬H).

The pre-log ratio that determines relevance sign and magnitude.
Division-by-zero convention follows `ArgumentativeStrength.bayesFactor`:
- P(E|¬H) = 0, P(E|H) > 0 → 1000 (effectively +∞)
- P(E|¬H) = 0, P(E|H) = 0 → 1 (neutral) -/
def bayesFactor {W : Type*} [Fintype W] (ctx : DTSContext W)
    (e : Set W) [DecidablePred (· ∈ e)] : ℚ :=
  let pGivenH := condProb ctx.prior e ctx.topic
  let pGivenNotH := condProb ctx.prior e (ctx.topicᶜ)
  if pGivenNotH = 0 then
    if pGivenH > 0 then 1000
    else 1
  else pGivenH / pGivenNotH

/-- E is positively relevant to H: BF > 1 (E confirms H). -/
def posRelevant {W : Type*} [Fintype W] (ctx : DTSContext W) (e : Set W)
    [DecidablePred (· ∈ e)] : Prop :=
  bayesFactor ctx e > 1

instance {W : Type*} [Fintype W] (ctx : DTSContext W) (e : Set W)
    [DecidablePred (· ∈ e)] :
    Decidable (posRelevant ctx e) := inferInstanceAs (Decidable (_ > _))

/-- E is negatively relevant to H: BF < 1 (E disconfirms H). -/
def negRelevant {W : Type*} [Fintype W] (ctx : DTSContext W) (e : Set W)
    [DecidablePred (· ∈ e)] : Prop :=
  bayesFactor ctx e < 1

instance {W : Type*} [Fintype W] (ctx : DTSContext W) (e : Set W)
    [DecidablePred (· ∈ e)] :
    Decidable (negRelevant ctx e) := inferInstanceAs (Decidable (_ < _))

/-- E is irrelevant to H: BF = 1 (E neither confirms nor disconfirms). -/
def irrelevant {W : Type*} [Fintype W] (ctx : DTSContext W) (e : Set W)
    [DecidablePred (· ∈ e)] : Prop :=
  bayesFactor ctx e = 1

instance {W : Type*} [Fintype W] (ctx : DTSContext W) (e : Set W)
    [DecidablePred (· ∈ e)] :
    Decidable (irrelevant ctx e) := inferInstanceAs (Decidable (_ = _))

/-- A and B have opposite relevance signs w.r.t. H.

Merin's "contrariness": one supports H while the other supports ¬H. -/
def hContrary {W : Type*} [Fintype W] (ctx : DTSContext W) (a b : Set W)
    [DecidablePred (· ∈ a)] [DecidablePred (· ∈ b)] : Prop :=
  (posRelevant ctx a ∧ negRelevant ctx b) ∨ (negRelevant ctx a ∧ posRelevant ctx b)

-- ============================================================
-- Section 4: Conditional Independence Presumption (CIP)
-- ============================================================

/-- Conditional Independence Presumption (CIP, Merin's Def. 6):
A and B are conditionally independent given both H and ¬H.

P(A∧B|H) = P(A|H)·P(B|H) and P(A∧B|¬H) = P(A|¬H)·P(B|¬H). -/
def CIP {W : Type*} [Fintype W] (ctx : DTSContext W) (a b : Set W)
    [DecidablePred (· ∈ a)] [DecidablePred (· ∈ b)] : Prop :=
  condProb ctx.prior (a ∩ b) ctx.topic =
    condProb ctx.prior a ctx.topic * condProb ctx.prior b ctx.topic ∧
  condProb ctx.prior (a ∩ b) (ctx.topicᶜ) =
    condProb ctx.prior a (ctx.topicᶜ) *
    condProb ctx.prior b (ctx.topicᶜ)

-- ============================================================
-- Section 5: Exclusive Disjunction
-- ============================================================

/-- Exclusive disjunction (XOR) of two sets: symmetric difference. -/
def pxor {W : Type*} (a b : Set W) : Set W :=
  {w | (w ∈ a ∨ w ∈ b) ∧ ¬ (w ∈ a ∧ w ∈ b)}

instance {W : Type*} (a b : Set W) [DecidablePred (· ∈ a)] [DecidablePred (· ∈ b)] :
    DecidablePred (· ∈ pxor a b) := fun w =>
  inferInstanceAs (Decidable ((w ∈ a ∨ w ∈ b) ∧ ¬ (w ∈ a ∧ w ∈ b)))

-- ============================================================
-- Section 6: Helper Lemmas
-- ============================================================

section Helpers

variable {W : Type*} [Fintype W]

/-- Inclusion-exclusion for `probSum`: P(A∨B) + P(A∧B) = P(A) + P(B). -/
private lemma probSum_por_add_pand (prior : W → ℚ) (a b : Set W)
    [DecidablePred (· ∈ a)] [DecidablePred (· ∈ b)] :
    probSum prior (a ∪ b) + probSum prior (a ∩ b) =
    probSum prior a + probSum prior b := by
  simp only [probSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases ha : w ∈ a <;> by_cases hb : w ∈ b <;>
    simp [Set.mem_union, Set.mem_inter_iff, ha, hb]

/-- ∧ distributes over ∨ at `Set W`. -/
private lemma pand_por_distrib (a b h : Set W) :
    ((a ∪ b) ∩ h : Set W) =
    ((a ∩ h) ∪ (b ∩ h)) :=
  Set.union_inter_distrib_right a b h

/-- (A∧H) ∧ (B∧H) ↔ (A∧B) ∧ H, pointwise. -/
private lemma pand_pand_eq (a b h : Set W) :
    ((a ∩ h) ∩ (b ∩ h) : Set W) =
    ((a ∩ b) ∩ h) := by
  ext w
  exact ⟨fun ⟨⟨ha, hh⟩, ⟨hb, _⟩⟩ => ⟨⟨ha, hb⟩, hh⟩,
         fun ⟨⟨ha, hb⟩, hh⟩ => ⟨⟨ha, hh⟩, ⟨hb, hh⟩⟩⟩

/-- Inclusion-exclusion for probSum conditioned on h. -/
private lemma probSum_pand_por_eq (prior : W → ℚ) (a b h : Set W)
    [DecidablePred (· ∈ a)] [DecidablePred (· ∈ b)] [DecidablePred (· ∈ h)] :
    probSum prior ((a ∪ b) ∩ h) +
    probSum prior ((a ∩ b) ∩ h) =
    probSum prior (a ∩ h) + probSum prior (b ∩ h) := by
  -- Reduce to a pointwise sum equality, dodging decidability-instance dependency
  -- in `rw` by working at the `Finset.sum` level directly.
  unfold probSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases ha : w ∈ a <;> by_cases hb : w ∈ b <;> by_cases hh : w ∈ h <;>
    simp [Set.mem_union, Set.mem_inter_iff, ha, hb, hh]

/-- Unfold condProb when the conditioning event has nonzero probability. -/
private lemma condProb_unfold (prior : W → ℚ) (e h : Set W)
    [DecidablePred (· ∈ e)] [DecidablePred (· ∈ h)] (hh : probSum prior h ≠ 0) :
    condProb prior e h = probSum prior (e ∩ h) / probSum prior h := by
  simp [condProb, hh]

/-- Inclusion-exclusion for condProb: P(A∨B|H) + P(A∧B|H) = P(A|H) + P(B|H). -/
private lemma condProb_por_add (prior : W → ℚ) (a b h : Set W)
    [DecidablePred (· ∈ a)] [DecidablePred (· ∈ b)] [DecidablePred (· ∈ h)]
    (hh : probSum prior h ≠ 0) :
    condProb prior (a ∪ b) h + condProb prior (a ∩ b) h =
    condProb prior a h + condProb prior b h := by
  rw [condProb_unfold _ _ _ hh, condProb_unfold _ _ _ hh,
      condProb_unfold _ _ _ hh, condProb_unfold _ _ _ hh]
  field_simp
  linarith [probSum_pand_por_eq prior a b h]

/-- probSum is non-negative when prior is non-negative. -/
theorem probSum_nonneg (prior : W → ℚ) (hP : ∀ w, prior w ≥ 0)
    (p : Set W) [DecidablePred (· ∈ p)] :
    probSum prior p ≥ 0 := by
  unfold probSum
  apply Finset.sum_nonneg'
  intro w; split
  · exact hP w
  · exact le_refl 0

/-- probSum is monotone when prior is non-negative. -/
private lemma probSum_mono (prior : W → ℚ) (hP : ∀ w, prior w ≥ 0)
    (p q : Set W) [DecidablePred (· ∈ p)] [DecidablePred (· ∈ q)]
    (hsub : ∀ w, w ∈ p → w ∈ q) :
    probSum prior p ≤ probSum prior q := by
  unfold probSum
  apply Finset.sum_le_sum
  intro w _
  by_cases hp : w ∈ p
  · simp [hp, hsub w hp]
  · simp [hp]
    split
    · exact hP w
    · exact le_refl 0

/-- Partition: `P(e) = P(e ∩ h) + P(e ∩ hᶜ)` for any decidable conditioning
    set `h`. The DTS-side mirror of `PMF.probOfSet_partition`. -/
theorem probSum_partition (prior : W → ℚ) (e h : Set W)
    [DecidablePred (· ∈ e)] [DecidablePred (· ∈ h)] :
    probSum prior e = probSum prior (e ∩ h) + probSum prior (e ∩ hᶜ) := by
  unfold probSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases he : w ∈ e <;> by_cases hh : w ∈ h <;>
    simp [Set.mem_inter_iff, Set.mem_compl_iff, he, hh]

/-- Total mass: `P(h) + P(hᶜ) = P(univ)`. With normalization `P(univ) = 1`,
    yields `P(hᶜ) = 1 − P(h)`. The DTS-side mirror of
    `PMF.probOfSet_compl_add`. -/
theorem probSum_compl (prior : W → ℚ) (h : Set W) [DecidablePred (· ∈ h)] :
    probSum prior h + probSum prior hᶜ = probSum prior (Set.univ : Set W) := by
  have := probSum_partition prior Set.univ h
  simp [Set.univ_inter] at this
  linarith

/-- condProb is non-negative when prior is non-negative and conditioning event
has positive probability. -/
private lemma condProb_nonneg (prior : W → ℚ) (hP : ∀ w, prior w ≥ 0)
    (e h : Set W) [DecidablePred (· ∈ e)] [DecidablePred (· ∈ h)]
    (hh : probSum prior h > 0) :
    condProb prior e h ≥ 0 := by
  rw [condProb_unfold _ _ _ (ne_of_gt hh)]
  exact div_nonneg (probSum_nonneg prior hP _) (le_of_lt hh)

/-- condProb ≤ 1 when prior is non-negative and conditioning event has
positive probability. -/
private lemma condProb_le_one (prior : W → ℚ) (hP : ∀ w, prior w ≥ 0)
    (e h : Set W) [DecidablePred (· ∈ e)] [DecidablePred (· ∈ h)]
    (hh : probSum prior h > 0) :
    condProb prior e h ≤ 1 := by
  rw [condProb_unfold _ _ _ (ne_of_gt hh)]
  refine (div_le_one hh).mpr (probSum_mono prior hP _ _ (λ w hw => ?_))
  exact hw.2

/-- Unfold bayesFactor when P(E|¬H) ≠ 0. -/
private lemma bayesFactor_unfold (ctx : DTSContext W) (e : Set W)
    [DecidablePred (· ∈ e)]
    (hne : condProb ctx.prior e (ctx.topicᶜ) ≠ 0) :
    bayesFactor ctx e = condProb ctx.prior e ctx.topic /
                         condProb ctx.prior e (ctx.topicᶜ) := by
  simp [bayesFactor, hne]

/-- From posRelevant and nonzero P(E|¬H) with non-negative prior:
condProb E given H > condProb E given ¬H > 0. -/
private lemma posRelevant_condProb_ineqs (ctx : DTSContext W)
    (hP : ∀ w, ctx.prior w ≥ 0) (e : Set W) [DecidablePred (· ∈ e)]
    (hpos : posRelevant ctx e)
    (hne : condProb ctx.prior e (ctx.topicᶜ) ≠ 0) :
    condProb ctx.prior e (ctx.topicᶜ) > 0 ∧
    condProb ctx.prior e ctx.topic >
      condProb ctx.prior e (ctx.topicᶜ) := by
  have hbf := bayesFactor_unfold ctx e hne
  have hgt : bayesFactor ctx e > 1 := hpos
  rw [hbf] at hgt
  have hnh_pos : probSum ctx.prior (ctx.topicᶜ) > 0 := by
    by_contra h_le
    push_neg at h_le
    have h_ge := probSum_nonneg ctx.prior hP (ctx.topicᶜ)
    have h_eq : probSum ctx.prior (ctx.topicᶜ) = 0 := le_antisymm h_le h_ge
    simp [condProb, h_eq] at hne
  have ce_pos : condProb ctx.prior e (ctx.topicᶜ) > 0 := by
    have := condProb_nonneg ctx.prior hP e _ hnh_pos
    exact lt_of_le_of_ne this (Ne.symm hne)
  refine ⟨ce_pos, ?_⟩
  have : condProb ctx.prior e ctx.topic /
         condProb ctx.prior e (ctx.topicᶜ) > 1 := hgt
  calc condProb ctx.prior e ctx.topic
      = condProb ctx.prior e (ctx.topicᶜ) *
        (condProb ctx.prior e ctx.topic /
         condProb ctx.prior e (ctx.topicᶜ)) := by
          rw [mul_div_cancel₀ _ (ne_of_gt ce_pos)]
    _ > condProb ctx.prior e (ctx.topicᶜ) * 1 := by
          exact mul_lt_mul_of_pos_left this ce_pos
    _ = condProb ctx.prior e (ctx.topicᶜ) := mul_one _

/-- condProb < 1 follows from posRelevant and condProb ≤ 1 and BF > 1. -/
private lemma condProb_lt_one_of_posRelevant (ctx : DTSContext W)
    (hP : ∀ w, ctx.prior w ≥ 0) (e : Set W) [DecidablePred (· ∈ e)]
    (hpos : posRelevant ctx e)
    (hne : condProb ctx.prior e (ctx.topicᶜ) ≠ 0) :
    condProb ctx.prior e (ctx.topicᶜ) < 1 := by
  have ⟨ce_pos, ce_gt⟩ := posRelevant_condProb_ineqs ctx hP e hpos hne
  have hnh_pos : probSum ctx.prior (ctx.topicᶜ) > 0 := by
    by_contra h_le; push_neg at h_le
    have := probSum_nonneg ctx.prior hP (ctx.topicᶜ)
    linarith [show condProb ctx.prior e (ctx.topicᶜ) = 0 from by
      simp [condProb, show probSum ctx.prior (ctx.topicᶜ) = 0 from
        le_antisymm h_le this]]
  have hh_pos : probSum ctx.prior ctx.topic > 0 := by
    by_contra h_le; push_neg at h_le
    have := probSum_nonneg ctx.prior hP ctx.topic
    have h_eq : probSum ctx.prior ctx.topic = 0 := le_antisymm h_le this
    have : condProb ctx.prior e ctx.topic = 0 := by simp [condProb, h_eq]
    linarith
  have := condProb_le_one ctx.prior hP e _ hh_pos
  linarith

/-- Arithmetic core for Theorem 6a disjunction ordering: given four conditional
probabilities satisfying the CIP-derived relationships, max(pAH/pAnH, pBH/pBnH)
exceeds the inclusion-exclusion ratio, which itself exceeds 1. -/
private lemma max_div_gt_or_div (pAH pBH pAnH pBnH : ℚ)
    (h1 : 0 < pAnH) (h2 : 0 < pBnH)
    (h3 : pAnH < pAH) (h4 : pBnH < pBH)
    (h5 : pAnH < 1) (h6 : pBnH < 1)
    (h7 : pAH ≤ 1) (h8 : pBH ≤ 1) :
    max (pAH / pAnH) (pBH / pBnH) >
      (pAH + pBH - pAH * pBH) / (pAnH + pBnH - pAnH * pBnH) ∧
    (pAH + pBH - pAH * pBH) / (pAnH + pBnH - pAnH * pBnH) > 1 := by
  have hden_pos : pAnH + pBnH - pAnH * pBnH > 0 := by nlinarith
  refine ⟨?_, ?_⟩
  · rw [gt_iff_lt, max_def]; split
    · rename_i hge
      rw [div_lt_div_iff₀ hden_pos h2]
      have h_cross := (div_le_div_iff₀ h1 h2).mp hge
      nlinarith [mul_pos (mul_pos h2 (show (0:ℚ) < pBH by linarith))
        (show pAH - pAnH > 0 from by linarith)]
    · rename_i hlt; push_neg at hlt
      rw [div_lt_div_iff₀ hden_pos h1]
      have h_cross := (div_le_div_iff₀ h2 h1).mp (le_of_lt hlt)
      nlinarith [mul_pos (mul_pos h1 (show (0:ℚ) < pAH by linarith))
        (show pBH - pBnH > 0 from by linarith)]
  · rw [gt_iff_lt, one_lt_div hden_pos]
    nlinarith

end Helpers

-- ============================================================
-- Section 7: Theorems
-- ============================================================

section Theorems

variable {W : Type*} [Fintype W]

private lemma probSum_pnot_pnot (prior : W → ℚ) (h : Set W)
    [DecidablePred (· ∈ h)] :
    probSum prior ((hᶜ)ᶜ) = probSum prior h := by
  unfold probSum
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases hw : w ∈ h
  · simp [hw]
  · simp [hw]

private lemma probSum_pand_pnot_pnot (prior : W → ℚ) (e h : Set W)
    [DecidablePred (· ∈ e)] [DecidablePred (· ∈ h)] :
    probSum prior ((e ∩ ((hᶜ)ᶜ))) =
    probSum prior (e ∩ h) := by
  unfold probSum
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases hw : w ∈ h
  · simp [Set.mem_inter_iff, hw]
  · simp [Set.mem_inter_iff, hw]

private lemma condProb_pnot_pnot (prior : W → ℚ) (e h : Set W)
    [DecidablePred (· ∈ e)] [DecidablePred (· ∈ h)] :
    condProb prior e ((hᶜ)ᶜ) = condProb prior e h := by
  unfold condProb
  rw [probSum_pnot_pnot, probSum_pand_pnot_pnot]

/-- **Corollary 3** (qualitative sign reversal): E is positively relevant
to H iff E is negatively relevant to ¬H.

The ordinal content of r_H(E) = −r_{¬H}(E). -/
theorem sign_reversal_qual (ctx : DTSContext W) (e : Set W) [DecidablePred (· ∈ e)]
    (hEH : condProb ctx.prior e ctx.topic > 0)
    (hENotH : condProb ctx.prior e (ctx.topicᶜ) > 0) :
    posRelevant ctx e ↔ negRelevant (swapIssue ctx) e := by
  unfold posRelevant negRelevant bayesFactor swapIssue
  simp only [condProb_pnot_pnot]
  rw [if_neg (ne_of_gt hENotH), if_neg (ne_of_gt hEH)]
  constructor
  · intro h
    have h1 := ne_of_gt hEH
    have h2 := ne_of_gt hENotH
    rw [gt_iff_lt, lt_div_iff₀ hENotH] at h
    rw [div_lt_iff₀ hEH]
    linarith
  · intro h
    have h1 := ne_of_gt hEH
    have h2 := ne_of_gt hENotH
    rw [div_lt_iff₀ hEH] at h
    rw [gt_iff_lt, lt_div_iff₀ hENotH]
    linarith

/-- **Corollary 3** (quantitative): BF_H(E) · BF_{¬H}(E) = 1.

Exact when conditional probabilities are nonzero. -/
theorem sign_reversal (ctx : DTSContext W) (e : Set W) [DecidablePred (· ∈ e)]
    (hENotH : condProb ctx.prior e (ctx.topicᶜ) ≠ 0)
    (hEH : condProb ctx.prior e ctx.topic ≠ 0) :
    bayesFactor ctx e * bayesFactor (swapIssue ctx) e = 1 := by
  unfold bayesFactor swapIssue
  simp only [condProb_pnot_pnot]
  rw [if_neg hENotH, if_neg hEH]
  field_simp

/-- **Fact 2**: Relationship between relevance and conditional informativeness.

r_H(E) = inf(E, H) − inf(E, ¬H) where inf(E,X) = −log P(E|X).
That is, relevance is the *differential* of conditional informativeness.

Not provable in ℚ (requires logarithm properties). -/
theorem relevance_as_differential_inf :
    True := trivial  -- Stated for documentation; requires log properties

/-- **Fact 5**: Under CIP, Bayes factor is multiplicative over conjunction.

BF(A∧B) = BF(A) · BF(B) when A and B are conditionally independent
given both H and ¬H. -/
theorem bayes_factor_multiplicative_under_cip (ctx : DTSContext W) (a b : Set W)
    [DecidablePred (· ∈ a)] [DecidablePred (· ∈ b)]
    (hcip : CIP ctx a b)
    (hNotH : condProb ctx.prior a (ctx.topicᶜ) ≠ 0)
    (hNotH' : condProb ctx.prior b (ctx.topicᶜ) ≠ 0)
    (hABNotH : condProb ctx.prior (a ∩ b) (ctx.topicᶜ) ≠ 0) :
    bayesFactor ctx (a ∩ b) = bayesFactor ctx a * bayesFactor ctx b := by
  simp only [bayesFactor]
  rw [if_neg hABNotH, if_neg hNotH, if_neg hNotH']
  obtain ⟨hcipH, hcipNH⟩ := hcip
  rw [hcipH, hcipNH]
  field_simp

/-- **Theorem 6a** (part 1): Under CIP with both A,B positively relevant,
conjunction dominates both conjuncts: BF(A∧B) > max(BF(A), BF(B)). -/
theorem conjunction_dominates_conjuncts (ctx : DTSContext W) (a b : Set W)
    [DecidablePred (· ∈ a)] [DecidablePred (· ∈ b)]
    (hcip : CIP ctx a b)
    (hPosA : posRelevant ctx a) (hPosB : posRelevant ctx b)
    (hNonzero : condProb ctx.prior a (ctx.topicᶜ) ≠ 0)
    (hNonzero' : condProb ctx.prior b (ctx.topicᶜ) ≠ 0)
    (hABNonzero : condProb ctx.prior (a ∩ b)
      (ctx.topicᶜ) ≠ 0) :
    bayesFactor ctx (a ∩ b) >
      max (bayesFactor ctx a) (bayesFactor ctx b) := by
  have hMult := bayes_factor_multiplicative_under_cip ctx a b hcip hNonzero hNonzero' hABNonzero
  rw [hMult]
  have hA : bayesFactor ctx a > 1 := hPosA
  have hB : bayesFactor ctx b > 1 := hPosB
  rw [gt_iff_lt, max_lt_iff]
  refine ⟨?_, ?_⟩ <;> nlinarith

/-- **Theorem 6a** (full): Under CIP with both A,B positively relevant,
BF(A∧B) > max(BF(A), BF(B)) > BF(A∨B) > 1.

The disjunction ordering requires inclusion-exclusion on conditional
probabilities: P(A∨B|X) = P(A|X) + P(B|X) - P(A∧B|X). -/
theorem conjunction_dominates_disjunction (ctx : DTSContext W) (a b : Set W)
    [DecidablePred (· ∈ a)] [DecidablePred (· ∈ b)]
    (hcip : CIP ctx a b)
    (hPosA : posRelevant ctx a) (hPosB : posRelevant ctx b)
    (hNonzero : condProb ctx.prior a (ctx.topicᶜ) ≠ 0)
    (hNonzero' : condProb ctx.prior b (ctx.topicᶜ) ≠ 0)
    (hABNonzero : condProb ctx.prior (a ∩ b)
      (ctx.topicᶜ) ≠ 0)
    (hPrior : ∀ w, ctx.prior w ≥ 0) :
    bayesFactor ctx (a ∩ b) >
      max (bayesFactor ctx a) (bayesFactor ctx b) ∧
    max (bayesFactor ctx a) (bayesFactor ctx b) >
      bayesFactor ctx (a ∪ b) ∧
    bayesFactor ctx (a ∪ b) > 1 := by
  refine ⟨conjunction_dominates_conjuncts ctx a b hcip hPosA hPosB
    hNonzero hNonzero' hABNonzero, ?_⟩
  have ⟨hpAnH_pos, hpAH_gt⟩ := posRelevant_condProb_ineqs ctx hPrior a hPosA hNonzero
  have ⟨hpBnH_pos, hpBH_gt⟩ := posRelevant_condProb_ineqs ctx hPrior b hPosB hNonzero'
  have hpAnH_lt1 := condProb_lt_one_of_posRelevant ctx hPrior a hPosA hNonzero
  have hpBnH_lt1 := condProb_lt_one_of_posRelevant ctx hPrior b hPosB hNonzero'
  have hnh_pos : probSum ctx.prior (ctx.topicᶜ) > 0 := by
    by_contra hle; push_neg at hle
    have h0 := probSum_nonneg ctx.prior hPrior (ctx.topicᶜ)
    have h_eq : probSum ctx.prior (ctx.topicᶜ) = 0 := le_antisymm hle h0
    exact absurd (show condProb ctx.prior a (ctx.topicᶜ) = 0 by
      simp [condProb, h_eq]) hNonzero
  have hh_pos : probSum ctx.prior ctx.topic > 0 := by
    by_contra hle; push_neg at hle
    have h0 := probSum_nonneg ctx.prior hPrior ctx.topic
    have h_eq : probSum ctx.prior ctx.topic = 0 := le_antisymm hle h0
    have : condProb ctx.prior a ctx.topic = 0 := by simp [condProb, h_eq]
    linarith [hpAH_gt]
  have hpAH_le1 := condProb_le_one ctx.prior hPrior a ctx.topic hh_pos
  have hpBH_le1 := condProb_le_one ctx.prior hPrior b ctx.topic hh_pos
  have hnh_ne := ne_of_gt hnh_pos
  have hh_ne := ne_of_gt hh_pos
  obtain ⟨hcipH, hcipNH⟩ := hcip
  set pAH := condProb ctx.prior a ctx.topic
  set pBH := condProb ctx.prior b ctx.topic
  set pAnH := condProb ctx.prior a (ctx.topicᶜ)
  set pBnH := condProb ctx.prior b (ctx.topicᶜ)
  have hpor_nh : condProb ctx.prior (a ∪ b)
      (ctx.topicᶜ) = pAnH + pBnH - pAnH * pBnH := by
    have hie := condProb_por_add ctx.prior a b _ hnh_ne
    rw [hcipNH] at hie; linarith
  have hpor_h : condProb ctx.prior (a ∪ b) ctx.topic =
      pAH + pBH - pAH * pBH := by
    have hie := condProb_por_add ctx.prior a b _ hh_ne
    rw [hcipH] at hie; linarith
  have hpor_nh_ne : condProb ctx.prior (a ∪ b)
      (ctx.topicᶜ) ≠ 0 := by rw [hpor_nh]; nlinarith
  have hbfA := bayesFactor_unfold ctx a hNonzero
  have hbfB := bayesFactor_unfold ctx b hNonzero'
  have hbfOr := bayesFactor_unfold ctx (a ∪ b) hpor_nh_ne
  have harith := max_div_gt_or_div pAH pBH pAnH pBnH
    hpAnH_pos hpBnH_pos hpAH_gt hpBH_gt hpAnH_lt1 hpBnH_lt1 hpAH_le1 hpBH_le1
  refine ⟨?_, ?_⟩
  · rw [hbfA, hbfB, hbfOr, hpor_h, hpor_nh]
    exact harith.1
  · rw [hbfOr, hpor_h, hpor_nh]
    exact harith.2

/-- **Theorem 6b**: XOR of two positively relevant propositions is not
necessarily positively relevant.

Counterexample on World4: H={w0}, A={w0,w1}, B={w0,w2}, uniform prior.
BF(A) = 3, BF(B) = 3, but A⊕B = {w1,w2} has BF = 0 (not pos relevant).

TODO: Reconstruct the concrete counterexample in the new Prop-based
formulation. The mathematical content is unchanged from the Bool-era
formulation: the World4 witnesses still work, but threading the
`DecidablePred` instances through `decide` requires care. -/
theorem xor_not_necessarily_positive :
    ∃ (ctx : DTSContext World4) (a b : Set World4)
      (_ : DecidablePred (· ∈ a)) (_ : DecidablePred (· ∈ b)),
      posRelevant ctx a ∧ posRelevant ctx b ∧
      ¬ posRelevant ctx (pxor a b) := by
  sorry

end Theorems

end DTS
