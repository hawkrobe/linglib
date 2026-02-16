import Linglib.Core.Proposition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators

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
-- Section 6: Theorems
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
      (Decidable.pnot W ctx.issue.topic) ≠ 0) :
    bayesFactor ctx (Decidable.pand W a b) >
      max (bayesFactor ctx a) (bayesFactor ctx b) ∧
    max (bayesFactor ctx a) (bayesFactor ctx b) >
      bayesFactor ctx (Decidable.por W a b) ∧
    bayesFactor ctx (Decidable.por W a b) > 1 := by
  refine ⟨conjunction_dominates_conjuncts ctx a b hcip hPosA hPosB
    hNonzero hNonzero' hABNonzero, ?_, ?_⟩
  -- TODO: Requires inclusion-exclusion lemma for condProb:
  --   condProb prior (por a b) h = condProb prior a h + condProb prior b h
  --                                 - condProb prior (pand a b) h
  -- Then BF(A∨B) can be expressed in terms of conditional probabilities
  -- of A, B, A∧B, and the ordering follows from CIP + positive relevance.
  all_goals sorry

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
