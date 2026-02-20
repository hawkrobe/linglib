import Linglib.Core.Proposition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic

/-!
# Decision-Theoretic Semantics: Core (Merin 1999)

Core definitions for Merin's Decision-Theoretic Semantics (DTS). Meaning is
explicated through *signed relevance* — the Bayes factor P(E|H)/P(E|¬H) —
relative to a dichotomic issue {H, ¬H}.

## Key Definitions

- `Issue` — a dichotomic hypothesis {H, ¬H}
- `DTSContext` — issue + prior probability
- `condProb` — conditional probability P(E|H) over finite worlds
- `bayesFactor` — P(E|H) / P(E|¬H), exact rational arithmetic
- `posRelevant` / `negRelevant` / `irrelevant` — ordinal relevance predicates
- `hContrary` — A and B have opposite relevance signs
- `CIP` — Conditional Independence Presumption
- `pxor` — exclusive disjunction for BProp

## Main Results

- **Corollary 3** (`sign_reversal`): BF_H(E) · BF_{¬H}(E) = 1
- **Fact 5** (`bayes_factor_multiplicative_under_cip`): Under CIP,
  BF(A∧B) = BF(A) · BF(B)
- **Theorem 6b** (`xor_not_necessarily_positive`): Counterexample showing
  XOR of two positively relevant propositions can be negatively relevant

## References

- Merin, A. (1999). Information, relevance, and social decisionmaking.
  In *Logic, Language, and Computation*, Vol. 2, CSLI.
-/

namespace Theories.DTS

open Core.Proposition

-- ============================================================
-- Section 1: Core Types
-- ============================================================

/-- A dichotomic issue {H, ¬H}, the hypothesis under consideration. -/
structure Issue (W : Type*) where
  /-- The hypothesis H (as a decidable proposition). -/
  topic : BProp W

/-- A DTS context: a dichotomic issue plus a prior probability distribution. -/
structure DTSContext (W : Type*) where
  /-- The dichotomic issue {H, ¬H}. -/
  issue : Issue W
  /-- Prior probability distribution over worlds (rational-valued). -/
  prior : W → ℚ

/-- Swap the issue: replace H with ¬H. -/
def swapIssue {W : Type*} (ctx : DTSContext W) : DTSContext W :=
  { issue := ⟨Decidable.pnot W ctx.issue.topic⟩, prior := ctx.prior }

-- ============================================================
-- Section 2: Probability
-- ============================================================

/-- Sum of prior probabilities over worlds satisfying a predicate. -/
def probSum {W : Type*} [Fintype W] (prior : W → ℚ) (p : BProp W) : ℚ :=
  ∑ w : W, if p w then prior w else 0

/-- Conditional probability P(E|H) = P(E∧H) / P(H).

Returns 0 when P(H) = 0 (undefined conditioning). -/
def condProb {W : Type*} [Fintype W] (prior : W → ℚ) (e h : BProp W) : ℚ :=
  let pH := probSum prior h
  if pH = 0 then 0
  else probSum prior (Decidable.pand W e h) / pH

/-- Marginal (unconditional) probability P(E) = P(E|⊤). -/
def margProb {W : Type*} [Fintype W] (prior : W → ℚ) (e : BProp W) : ℚ :=
  probSum prior e

-- ============================================================
-- Section 3: Bayes Factor and Relevance
-- ============================================================

/-- Bayes factor: P(E|H) / P(E|¬H).

The pre-log ratio that determines relevance sign and magnitude.
Division-by-zero convention follows `ArgumentativeStrength.bayesFactor`:
- P(E|¬H) = 0, P(E|H) > 0 → 1000 (effectively +∞)
- P(E|¬H) = 0, P(E|H) = 0 → 1 (neutral) -/
def bayesFactor {W : Type*} [Fintype W] (ctx : DTSContext W) (e : BProp W) : ℚ :=
  let pGivenH := condProb ctx.prior e ctx.issue.topic
  let pGivenNotH := condProb ctx.prior e (Decidable.pnot W ctx.issue.topic)
  if pGivenNotH = 0 then
    if pGivenH > 0 then 1000
    else 1
  else pGivenH / pGivenNotH

/-- E is positively relevant to H: BF > 1 (E confirms H). -/
def posRelevant {W : Type*} [Fintype W] (ctx : DTSContext W) (e : BProp W) : Prop :=
  bayesFactor ctx e > 1

instance {W : Type*} [Fintype W] (ctx : DTSContext W) (e : BProp W) :
    Decidable (posRelevant ctx e) := inferInstanceAs (Decidable (_ > _))

/-- E is negatively relevant to H: BF < 1 (E disconfirms H). -/
def negRelevant {W : Type*} [Fintype W] (ctx : DTSContext W) (e : BProp W) : Prop :=
  bayesFactor ctx e < 1

instance {W : Type*} [Fintype W] (ctx : DTSContext W) (e : BProp W) :
    Decidable (negRelevant ctx e) := inferInstanceAs (Decidable (_ < _))

/-- E is irrelevant to H: BF = 1 (E neither confirms nor disconfirms). -/
def irrelevant {W : Type*} [Fintype W] (ctx : DTSContext W) (e : BProp W) : Prop :=
  bayesFactor ctx e = 1

instance {W : Type*} [Fintype W] (ctx : DTSContext W) (e : BProp W) :
    Decidable (irrelevant ctx e) := inferInstanceAs (Decidable (_ = _))

/-- A and B have opposite relevance signs w.r.t. H.

Merin's "contrariness": one supports H while the other supports ¬H. -/
def hContrary {W : Type*} [Fintype W] (ctx : DTSContext W) (a b : BProp W) : Prop :=
  (posRelevant ctx a ∧ negRelevant ctx b) ∨ (negRelevant ctx a ∧ posRelevant ctx b)

-- ============================================================
-- Section 4: Conditional Independence Presumption (CIP)
-- ============================================================

/-- Conditional Independence Presumption (CIP, Merin's Def. 6):
A and B are conditionally independent given both H and ¬H.

P(A∧B|H) = P(A|H)·P(B|H) and P(A∧B|¬H) = P(A|¬H)·P(B|¬H). -/
def CIP {W : Type*} [Fintype W] (ctx : DTSContext W) (a b : BProp W) : Prop :=
  condProb ctx.prior (Decidable.pand W a b) ctx.issue.topic =
    condProb ctx.prior a ctx.issue.topic * condProb ctx.prior b ctx.issue.topic ∧
  condProb ctx.prior (Decidable.pand W a b) (Decidable.pnot W ctx.issue.topic) =
    condProb ctx.prior a (Decidable.pnot W ctx.issue.topic) *
    condProb ctx.prior b (Decidable.pnot W ctx.issue.topic)

-- ============================================================
-- Section 5: Exclusive Disjunction
-- ============================================================

/-- Exclusive disjunction (XOR) for decidable propositions. -/
def pxor {W : Type*} (a b : BProp W) : BProp W := λ w => (a w) ^^ (b w)

-- ============================================================
-- Section 6: Helper Lemmas
-- ============================================================

section Helpers

variable {W : Type*} [Fintype W]

/-- Inclusion-exclusion for `probSum`: P(A∨B) + P(A∧B) = P(A) + P(B). -/
private lemma probSum_por_add_pand (prior : W → ℚ) (a b : BProp W) :
    probSum prior (Decidable.por W a b) + probSum prior (Decidable.pand W a b) =
    probSum prior a + probSum prior b := by
  simp only [probSum, ← Finset.sum_add_distrib]
  congr 1; funext w
  simp only [Decidable.por, Decidable.pand]
  rcases Bool.eq_false_or_eq_true (a w) with ha | ha <;>
  rcases Bool.eq_false_or_eq_true (b w) with hb | hb <;>
  simp [ha, hb]

/-- ∧ distributes over ∨ at the BProp level. -/
private lemma pand_por_distrib (a b h : BProp W) :
    Decidable.pand W (Decidable.por W a b) h =
    Decidable.por W (Decidable.pand W a h) (Decidable.pand W b h) := by
  funext w; simp only [Decidable.pand, Decidable.por]
  cases a w <;> cases b w <;> cases h w <;> rfl

/-- (A∧H) ∧ (B∧H) = (A∧B) ∧ H. -/
private lemma pand_pand_eq (a b h : BProp W) :
    Decidable.pand W (Decidable.pand W a h) (Decidable.pand W b h) =
    Decidable.pand W (Decidable.pand W a b) h := by
  funext w; simp only [Decidable.pand]
  cases a w <;> cases b w <;> cases h w <;> rfl

/-- Inclusion-exclusion for probSum conditioned on h. -/
private lemma probSum_pand_por_eq (prior : W → ℚ) (a b h : BProp W) :
    probSum prior (Decidable.pand W (Decidable.por W a b) h) +
    probSum prior (Decidable.pand W (Decidable.pand W a b) h) =
    probSum prior (Decidable.pand W a h) + probSum prior (Decidable.pand W b h) := by
  rw [pand_por_distrib, ← pand_pand_eq]
  exact probSum_por_add_pand prior (Decidable.pand W a h) (Decidable.pand W b h)

/-- Unfold condProb when the conditioning event has nonzero probability. -/
private lemma condProb_unfold (prior : W → ℚ) (e h : BProp W) (hh : probSum prior h ≠ 0) :
    condProb prior e h = probSum prior (Decidable.pand W e h) / probSum prior h := by
  simp [condProb, hh]

/-- Inclusion-exclusion for condProb: P(A∨B|H) + P(A∧B|H) = P(A|H) + P(B|H). -/
private lemma condProb_por_add (prior : W → ℚ) (a b h : BProp W)
    (hh : probSum prior h ≠ 0) :
    condProb prior (Decidable.por W a b) h + condProb prior (Decidable.pand W a b) h =
    condProb prior a h + condProb prior b h := by
  rw [condProb_unfold _ _ _ hh, condProb_unfold _ _ _ hh,
      condProb_unfold _ _ _ hh, condProb_unfold _ _ _ hh]
  field_simp
  linarith [probSum_pand_por_eq prior a b h]

/-- probSum is non-negative when prior is non-negative. -/
private lemma probSum_nonneg (prior : W → ℚ) (hP : ∀ w, prior w ≥ 0) (p : BProp W) :
    probSum prior p ≥ 0 := by
  unfold probSum
  apply Finset.sum_nonneg'
  intro w; split
  · exact hP w
  · exact le_refl 0

/-- probSum is monotone when prior is non-negative. -/
private lemma probSum_mono (prior : W → ℚ) (hP : ∀ w, prior w ≥ 0)
    (p q : BProp W) (hsub : ∀ w, p w = true → q w = true) :
    probSum prior p ≤ probSum prior q := by
  unfold probSum
  apply Finset.sum_le_sum
  intro w _
  by_cases hp : p w = true
  · simp [hp, hsub w hp, hP w]
  · push_neg at hp; simp [Bool.eq_false_iff.mpr hp]
    split
    · exact hP w
    · exact le_refl 0

/-- condProb is non-negative when prior is non-negative and conditioning event
has positive probability. -/
private lemma condProb_nonneg (prior : W → ℚ) (hP : ∀ w, prior w ≥ 0)
    (e h : BProp W) (hh : probSum prior h > 0) :
    condProb prior e h ≥ 0 := by
  rw [condProb_unfold _ _ _ (ne_of_gt hh)]
  exact div_nonneg (probSum_nonneg prior hP _) (le_of_lt hh)

/-- condProb ≤ 1 when prior is non-negative and conditioning event has
positive probability. -/
private lemma condProb_le_one (prior : W → ℚ) (hP : ∀ w, prior w ≥ 0)
    (e h : BProp W) (hh : probSum prior h > 0) :
    condProb prior e h ≤ 1 := by
  rw [condProb_unfold _ _ _ (ne_of_gt hh)]
  exact (div_le_one hh).mpr (probSum_mono prior hP _ _ (λ w hw => by
    simp only [Decidable.pand] at hw; exact (Bool.and_eq_true_iff.mp hw).2))

/-- Unfold bayesFactor when P(E|¬H) ≠ 0. -/
private lemma bayesFactor_unfold (ctx : DTSContext W) (e : BProp W)
    (hne : condProb ctx.prior e (Decidable.pnot W ctx.issue.topic) ≠ 0) :
    bayesFactor ctx e = condProb ctx.prior e ctx.issue.topic /
                         condProb ctx.prior e (Decidable.pnot W ctx.issue.topic) := by
  simp [bayesFactor, hne]

/-- From posRelevant and nonzero P(E|¬H) with non-negative prior:
condProb E given H > condProb E given ¬H > 0. -/
private lemma posRelevant_condProb_ineqs (ctx : DTSContext W)
    (hP : ∀ w, ctx.prior w ≥ 0) (e : BProp W)
    (hpos : posRelevant ctx e)
    (hne : condProb ctx.prior e (Decidable.pnot W ctx.issue.topic) ≠ 0) :
    condProb ctx.prior e (Decidable.pnot W ctx.issue.topic) > 0 ∧
    condProb ctx.prior e ctx.issue.topic >
      condProb ctx.prior e (Decidable.pnot W ctx.issue.topic) := by
  have hbf := bayesFactor_unfold ctx e hne
  have hgt : bayesFactor ctx e > 1 := hpos
  rw [hbf] at hgt
  have hnh_pos : probSum ctx.prior (Decidable.pnot W ctx.issue.topic) > 0 := by
    by_contra h_le
    push_neg at h_le
    have h_ge := probSum_nonneg ctx.prior hP (Decidable.pnot W ctx.issue.topic)
    have h_eq : probSum ctx.prior (Decidable.pnot W ctx.issue.topic) = 0 := le_antisymm h_le h_ge
    simp [condProb, h_eq] at hne
  have ce_pos : condProb ctx.prior e (Decidable.pnot W ctx.issue.topic) > 0 := by
    have := condProb_nonneg ctx.prior hP e _ hnh_pos
    exact lt_of_le_of_ne this (Ne.symm hne)
  constructor
  · exact ce_pos
  · have : condProb ctx.prior e ctx.issue.topic /
           condProb ctx.prior e (Decidable.pnot W ctx.issue.topic) > 1 := hgt
    calc condProb ctx.prior e ctx.issue.topic
        = condProb ctx.prior e (Decidable.pnot W ctx.issue.topic) *
          (condProb ctx.prior e ctx.issue.topic /
           condProb ctx.prior e (Decidable.pnot W ctx.issue.topic)) := by
            rw [mul_div_cancel₀ _ (ne_of_gt ce_pos)]
      _ > condProb ctx.prior e (Decidable.pnot W ctx.issue.topic) * 1 := by
            exact mul_lt_mul_of_pos_left this ce_pos
      _ = condProb ctx.prior e (Decidable.pnot W ctx.issue.topic) := mul_one _

/-- condProb < 1 follows from posRelevant and condProb ≤ 1 and BF > 1. -/
private lemma condProb_lt_one_of_posRelevant (ctx : DTSContext W)
    (hP : ∀ w, ctx.prior w ≥ 0) (e : BProp W)
    (hpos : posRelevant ctx e)
    (hne : condProb ctx.prior e (Decidable.pnot W ctx.issue.topic) ≠ 0) :
    condProb ctx.prior e (Decidable.pnot W ctx.issue.topic) < 1 := by
  have ⟨ce_pos, ce_gt⟩ := posRelevant_condProb_ineqs ctx hP e hpos hne
  have hnh_pos : probSum ctx.prior (Decidable.pnot W ctx.issue.topic) > 0 := by
    by_contra h_le; push_neg at h_le
    have := probSum_nonneg ctx.prior hP (Decidable.pnot W ctx.issue.topic)
    linarith [show condProb ctx.prior e (Decidable.pnot W ctx.issue.topic) = 0 from by
      simp [condProb, show probSum ctx.prior (Decidable.pnot W ctx.issue.topic) = 0 from
        le_antisymm h_le this]]
  have hh_pos : probSum ctx.prior ctx.issue.topic > 0 := by
    by_contra h_le; push_neg at h_le
    have := probSum_nonneg ctx.prior hP ctx.issue.topic
    have h_eq : probSum ctx.prior ctx.issue.topic = 0 := le_antisymm h_le this
    have : condProb ctx.prior e ctx.issue.topic = 0 := by simp [condProb, h_eq]
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
  constructor
  · rw [gt_iff_lt, max_def]; split
    · -- Case pAH/pAnH ≤ pBH/pBnH: max = pBH/pBnH, show ratio < pBH/pBnH
      rename_i hge
      rw [div_lt_div_iff₀ hden_pos h2]
      -- Cross-multiply hge: pAH * pBnH ≤ pBH * pAnH
      have h_cross := (div_le_div_iff₀ h1 h2).mp hge
      -- diff = (pBH*pAnH - pAH*pBnH) + pBnH*pBH*(pAH - pAnH) > 0
      nlinarith [mul_pos (mul_pos h2 (show (0:ℚ) < pBH by linarith))
        (show pAH - pAnH > 0 from by linarith)]
    · -- Case ¬(pAH/pAnH ≤ pBH/pBnH): max = pAH/pAnH, show ratio < pAH/pAnH
      rename_i hlt; push_neg at hlt
      rw [div_lt_div_iff₀ hden_pos h1]
      -- Cross-multiply hlt: pBH * pAnH ≤ pAH * pBnH
      have h_cross := (div_le_div_iff₀ h2 h1).mp (le_of_lt hlt)
      -- diff = (pAH*pBnH - pBH*pAnH) + pAnH*pAH*(pBH - pBnH) > 0
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

private lemma condProb_pnot_pnot (prior : W → ℚ) (e h : BProp W) :
    condProb prior e (Decidable.pnot W (Decidable.pnot W h)) = condProb prior e h := by
  simp [condProb, probSum, Decidable.pand, Decidable.pnot, Bool.not_not]

/-- **Corollary 3** (qualitative sign reversal): E is positively relevant
to H iff E is negatively relevant to ¬H.

The ordinal content of r_H(E) = −r_{¬H}(E). -/
theorem sign_reversal_qual (ctx : DTSContext W) (e : BProp W)
    (hEH : condProb ctx.prior e ctx.issue.topic > 0)
    (hENotH : condProb ctx.prior e (Decidable.pnot W ctx.issue.topic) > 0) :
    posRelevant ctx e ↔ negRelevant (swapIssue ctx) e := by
  simp only [posRelevant, negRelevant, bayesFactor, swapIssue]
  rw [if_neg (ne_of_gt hENotH), condProb_pnot_pnot, if_neg (ne_of_gt hEH)]
  constructor <;> intro h <;> {
    have := ne_of_gt hEH
    have := ne_of_gt hENotH
    field_simp at h ⊢
    linarith
  }

/-- **Corollary 3** (quantitative): BF_H(E) · BF_{¬H}(E) = 1.

Exact when conditional probabilities are nonzero. -/
theorem sign_reversal (ctx : DTSContext W) (e : BProp W)
    (hENotH : condProb ctx.prior e (Decidable.pnot W ctx.issue.topic) ≠ 0)
    (hEH : condProb ctx.prior e ctx.issue.topic ≠ 0) :
    bayesFactor ctx e * bayesFactor (swapIssue ctx) e = 1 := by
  simp only [bayesFactor, swapIssue]
  rw [if_neg hENotH, condProb_pnot_pnot, if_neg hEH]
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
theorem bayes_factor_multiplicative_under_cip (ctx : DTSContext W) (a b : BProp W)
    (hcip : CIP ctx a b)
    (hNotH : condProb ctx.prior a (Decidable.pnot W ctx.issue.topic) ≠ 0)
    (hNotH' : condProb ctx.prior b (Decidable.pnot W ctx.issue.topic) ≠ 0)
    (hABNotH : condProb ctx.prior (Decidable.pand W a b) (Decidable.pnot W ctx.issue.topic) ≠ 0) :
    bayesFactor ctx (Decidable.pand W a b) = bayesFactor ctx a * bayesFactor ctx b := by
  simp only [bayesFactor]
  rw [if_neg hABNotH, if_neg hNotH, if_neg hNotH']
  obtain ⟨hcipH, hcipNH⟩ := hcip
  rw [hcipH, hcipNH]
  field_simp

/-- **Theorem 6a** (part 1): Under CIP with both A,B positively relevant,
conjunction dominates both conjuncts: BF(A∧B) > max(BF(A), BF(B)). -/
theorem conjunction_dominates_conjuncts (ctx : DTSContext W) (a b : BProp W)
    (hcip : CIP ctx a b)
    (hPosA : posRelevant ctx a) (hPosB : posRelevant ctx b)
    (hNonzero : condProb ctx.prior a (Decidable.pnot W ctx.issue.topic) ≠ 0)
    (hNonzero' : condProb ctx.prior b (Decidable.pnot W ctx.issue.topic) ≠ 0)
    (hABNonzero : condProb ctx.prior (Decidable.pand W a b)
      (Decidable.pnot W ctx.issue.topic) ≠ 0) :
    bayesFactor ctx (Decidable.pand W a b) >
      max (bayesFactor ctx a) (bayesFactor ctx b) := by
  have hMult := bayes_factor_multiplicative_under_cip ctx a b hcip hNonzero hNonzero' hABNonzero
  rw [hMult]
  have hA : bayesFactor ctx a > 1 := hPosA
  have hB : bayesFactor ctx b > 1 := hPosB
  rw [gt_iff_lt, max_lt_iff]
  constructor <;> nlinarith

/-- **Theorem 6a** (full): Under CIP with both A,B positively relevant,
BF(A∧B) > max(BF(A), BF(B)) > BF(A∨B) > 1.

The disjunction ordering requires inclusion-exclusion on conditional
probabilities: P(A∨B|X) = P(A|X) + P(B|X) - P(A∧B|X). -/
theorem conjunction_dominates_disjunction (ctx : DTSContext W) (a b : BProp W)
    (hcip : CIP ctx a b)
    (hPosA : posRelevant ctx a) (hPosB : posRelevant ctx b)
    (hNonzero : condProb ctx.prior a (Decidable.pnot W ctx.issue.topic) ≠ 0)
    (hNonzero' : condProb ctx.prior b (Decidable.pnot W ctx.issue.topic) ≠ 0)
    (hABNonzero : condProb ctx.prior (Decidable.pand W a b)
      (Decidable.pnot W ctx.issue.topic) ≠ 0)
    (hPrior : ∀ w, ctx.prior w ≥ 0) :
    bayesFactor ctx (Decidable.pand W a b) >
      max (bayesFactor ctx a) (bayesFactor ctx b) ∧
    max (bayesFactor ctx a) (bayesFactor ctx b) >
      bayesFactor ctx (Decidable.por W a b) ∧
    bayesFactor ctx (Decidable.por W a b) > 1 := by
  refine ⟨conjunction_dominates_conjuncts ctx a b hcip hPosA hPosB
    hNonzero hNonzero' hABNonzero, ?_⟩
  -- Setup: extract key condProb values and their properties
  have ⟨hpAnH_pos, hpAH_gt⟩ := posRelevant_condProb_ineqs ctx hPrior a hPosA hNonzero
  have ⟨hpBnH_pos, hpBH_gt⟩ := posRelevant_condProb_ineqs ctx hPrior b hPosB hNonzero'
  have hpAnH_lt1 := condProb_lt_one_of_posRelevant ctx hPrior a hPosA hNonzero
  have hpBnH_lt1 := condProb_lt_one_of_posRelevant ctx hPrior b hPosB hNonzero'
  have hnh_pos : probSum ctx.prior (Decidable.pnot W ctx.issue.topic) > 0 := by
    by_contra hle; push_neg at hle
    have h0 := probSum_nonneg ctx.prior hPrior (Decidable.pnot W ctx.issue.topic)
    have h_eq : probSum ctx.prior (Decidable.pnot W ctx.issue.topic) = 0 := le_antisymm hle h0
    exact absurd (show condProb ctx.prior a (Decidable.pnot W ctx.issue.topic) = 0 by
      simp [condProb, h_eq]) hNonzero
  have hh_pos : probSum ctx.prior ctx.issue.topic > 0 := by
    by_contra hle; push_neg at hle
    have h0 := probSum_nonneg ctx.prior hPrior ctx.issue.topic
    have h_eq : probSum ctx.prior ctx.issue.topic = 0 := le_antisymm hle h0
    have : condProb ctx.prior a ctx.issue.topic = 0 := by simp [condProb, h_eq]
    linarith [hpAH_gt]
  have hpAH_le1 := condProb_le_one ctx.prior hPrior a ctx.issue.topic hh_pos
  have hpBH_le1 := condProb_le_one ctx.prior hPrior b ctx.issue.topic hh_pos
  -- Inclusion-exclusion under CIP: express BF(A∨B) in terms of condProbs
  have hnh_ne := ne_of_gt hnh_pos
  have hh_ne := ne_of_gt hh_pos
  obtain ⟨hcipH, hcipNH⟩ := hcip
  -- Short names for the condProb values
  set pAH := condProb ctx.prior a ctx.issue.topic
  set pBH := condProb ctx.prior b ctx.issue.topic
  set pAnH := condProb ctx.prior a (Decidable.pnot W ctx.issue.topic)
  set pBnH := condProb ctx.prior b (Decidable.pnot W ctx.issue.topic)
  -- BF(A∨B) numerator and denominator via inclusion-exclusion + CIP
  have hpor_nh : condProb ctx.prior (Decidable.por W a b)
      (Decidable.pnot W ctx.issue.topic) = pAnH + pBnH - pAnH * pBnH := by
    have hie := condProb_por_add ctx.prior a b _ hnh_ne
    rw [hcipNH] at hie; linarith
  have hpor_h : condProb ctx.prior (Decidable.por W a b) ctx.issue.topic =
      pAH + pBH - pAH * pBH := by
    have hie := condProb_por_add ctx.prior a b _ hh_ne
    rw [hcipH] at hie; linarith
  have hpor_nh_ne : condProb ctx.prior (Decidable.por W a b)
      (Decidable.pnot W ctx.issue.topic) ≠ 0 := by rw [hpor_nh]; nlinarith
  -- Unfold all three Bayes factors to condProb ratios
  have hbfA := bayesFactor_unfold ctx a hNonzero
  have hbfB := bayesFactor_unfold ctx b hNonzero'
  have hbfOr := bayesFactor_unfold ctx (Decidable.por W a b) hpor_nh_ne
  -- Apply pure arithmetic lemma (avoids set/rw interaction issues)
  have harith := max_div_gt_or_div pAH pBH pAnH pBnH
    hpAnH_pos hpBnH_pos hpAH_gt hpBH_gt hpAnH_lt1 hpBnH_lt1 hpAH_le1 hpBH_le1
  constructor
  -- Part 1: max(BF(A), BF(B)) > BF(A∨B)
  · rw [hbfA, hbfB, hbfOr, hpor_h, hpor_nh]
    exact harith.1
  -- Part 2: BF(A∨B) > 1
  · rw [hbfOr, hpor_h, hpor_nh]
    exact harith.2

instance : Fintype World4 where
  elems := {.w0, .w1, .w2, .w3}
  complete := λ x => by cases x <;> decide

/-- **Theorem 6b**: XOR of two positively relevant propositions is not
necessarily positively relevant.

Counterexample on World4: H={w0}, A={w0,w1}, B={w0,w2}, uniform prior.
BF(A) = 3, BF(B) = 3, but A⊕B = {w1,w2} has BF = 0 (not pos relevant). -/
theorem xor_not_necessarily_positive :
    ∃ (ctx : DTSContext World4) (a b : BProp World4),
      posRelevant ctx a ∧ posRelevant ctx b ∧
      ¬ posRelevant ctx (pxor a b) := by
  refine ⟨⟨⟨λ w => match w with | .w0 => true | _ => false⟩, λ _ => 1/4⟩,
          λ w => match w with | .w0 | .w1 => true | _ => false,
          λ w => match w with | .w0 | .w2 => true | _ => false,
          ?_, ?_, ?_⟩ <;> native_decide

end Theorems

end Theories.DTS
