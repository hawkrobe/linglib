import Linglib.Theories.Pragmatics.DTS.Core
import Linglib.Theories.Pragmatics.DTS.ScalarImplicature
import Linglib.Core.Presupposition
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Decision-Theoretic Semantics: "Also" (Merin 1999 §5.2–5.4)

Merin's DTS account of additive particles. Presupposition is modeled as
*i-irrelevance*: a presupposed proposition is one that doesn't change any
conditional probability. "Also" requires topic-anaphoric salience — the
antecedent D must have been relevant before becoming presupposed.

## Key Definitions

- `presupposedIrrelevant` (Def. 12): presupposition as informational inertness
- `topicAnaphoricSalience` (Def. 13): conditions for anaphoric antecedent
- `alsoFelicitous` (Hypothesis 8): felicity conditions for "and also"
- `properlyAccommodable` (partial Def. 14): accommodable propositions

## Main Results

- **Corollary 15** (`also_nonidentity`): "also" requires non-identity (a ≠ b)
- **Fact 17** (`presuppositional_independence_additivity`): presupposition
  implies multiplicativity of Bayes factor without CIP

## References

- Merin, A. (1999). Information, relevance, and social decisionmaking.
  §5.2–5.4: Also, presupposition, and accommodation.
-/

namespace Theories.DTS.Also

open Core.Proposition
open Core.Presupposition
open Theories.DTS
open Theories.DTS.ScalarImplicature (sgnRelevance RelevanceSign)

-- ============================================================
-- Section 1: Presupposition as Irrelevance (Def. 12)
-- ============================================================

/-- **Definition 12**: A proposition A is i-presupposed iff conditioning on A
doesn't change any conditional probability.

This is stronger than P(A)=1: it means A is informationally *inert*.
Formally: P(X|A) = P(X) for all X, which is equivalent to
P(X|A) = P(X|⊤) for all X. -/
def presupposedIrrelevant {W : Type*} [Fintype W]
    (prior : W → ℚ) (a : BProp W) : Prop :=
  ∀ (x : BProp W), condProb prior x a = condProb prior x (Decidable.top W)

-- ============================================================
-- Section 2: Topic-Anaphoric Salience (Def. 13)
-- ============================================================

/-- **Definition 13**: Topic-anaphoric salience.

D is topic-anaphorically salient for E in context iff:
(i) E is relevant to the current issue H,
(ii) D is presupposed (informationally inert),
(iii) D was recently relevant — before becoming presupposed, D bore
     on the issue.

This captures the discourse requirement of "also": the antecedent must
have been relevant before being taken for granted. -/
structure TopicAnaphoricSalience {W : Type*} [Fintype W]
    (ctx : DTSContext W) (d e : BProp W) where
  /-- E is relevant to the current issue. -/
  eRelevant : posRelevant ctx e ∨ negRelevant ctx e
  /-- D is currently presupposed (informationally inert). -/
  dPresupposed : presupposedIrrelevant ctx.prior d
  /-- D was previously relevant (before becoming presupposed). -/
  dWasRelevant : RelevanceSign

-- ============================================================
-- Section 3: "Also" Felicity (Hypothesis 8)
-- ============================================================

/-- **Hypothesis 8**: Felicity conditions for "and also(b, B)".

For "Q(a) and also Q(b)": Q(a) and Q(b) have the *same* relevance sign
(both support or both oppose H). This distinguishes "and also" from
"but also" (opposite signs).

The `previousSign` field records the relevance sign of Q(a) before it
was presupposed; `currentSign` is the relevance sign of Q(b) now. -/
structure AlsoFelicitous {W : Type*} [Fintype W]
    (ctx : DTSContext W) (qa qb : BProp W) where
  /-- Q(a) is presupposed. -/
  qaPresupposed : presupposedIrrelevant ctx.prior qa
  /-- Q(b) is relevant. -/
  qbRelevant : posRelevant ctx qb ∨ negRelevant ctx qb
  /-- Same relevance sign: Q(a) had the same sign as Q(b) before presupposition. -/
  sameSign : RelevanceSign
  /-- The sign matches Q(b)'s current relevance direction. -/
  signMatches : sgnRelevance ctx qb = sameSign

/-- "But also" variant: opposite relevance signs.

"Q(a) but also Q(b)": Q(a) had the opposite relevance sign from Q(b).
This combines adversativity ("but") with additivity ("also"). -/
structure ButAlsoFelicitous {W : Type*} [Fintype W]
    (ctx : DTSContext W) (qa qb : BProp W) where
  /-- Q(a) is presupposed. -/
  qaPresupposed : presupposedIrrelevant ctx.prior qa
  /-- Q(b) is relevant. -/
  qbRelevant : posRelevant ctx qb ∨ negRelevant ctx qb
  /-- Previous sign of Q(a). -/
  previousSign : RelevanceSign
  /-- Current sign of Q(b). -/
  currentSign : RelevanceSign
  /-- Signs are opposite. -/
  oppositeSigns : (previousSign = .pos ∧ currentSign = .neg) ∨
                  (previousSign = .neg ∧ currentSign = .pos)

-- ============================================================
-- Section 4: Accommodation (Partial Def. 14)
-- ============================================================

/-- **Partial Definition 14**: Properly accommodable propositions.

A proposition φ is properly accommodable iff:
(i) 0 < P(φ) (non-trivially satisfiable),
(ii) P(φ) < 1 (not already known),
(iii) φ is irrelevant to the current issue.

Accommodable propositions are those that can be "taken for granted"
without affecting the ongoing argumentation. -/
def properlyAccommodable {W : Type*} [Fintype W]
    (ctx : DTSContext W) (φ : BProp W) : Prop :=
  0 < margProb ctx.prior φ ∧
  margProb ctx.prior φ < 1 ∧
  irrelevant ctx φ

-- ============================================================
-- Section 5: Theorems
-- ============================================================

section Theorems

variable {W : Type*} [Fintype W]

-- Helper: condProb unfolds when denominator is nonzero
private lemma condProb_of_ne_zero (prior : W → ℚ) (e h : BProp W)
    (hne : probSum prior h ≠ 0) :
    condProb prior e h = probSum prior (Decidable.pand W e h) / probSum prior h := by
  simp [condProb, hne]

-- Helper: probSum of pand is commutative
private lemma probSum_pand_comm (prior : W → ℚ) (a b : BProp W) :
    probSum prior (Decidable.pand W a b) = probSum prior (Decidable.pand W b a) := by
  simp [probSum, Decidable.pand, Bool.and_comm]

-- Helper: probSum of pand with top is identity
private lemma probSum_pand_top (prior : W → ℚ) (a : BProp W) :
    probSum prior (Decidable.pand W a (Decidable.top W)) = probSum prior a := by
  simp [probSum, Decidable.pand, Decidable.top, Bool.and_true]

-- Helper: probSum is nonneg with nonneg prior
private lemma probSum_nonneg (prior : W → ℚ) (p : BProp W)
    (hNonneg : ∀ w, prior w ≥ 0) : probSum prior p ≥ 0 := by
  show 0 ≤ probSum prior p
  unfold probSum
  apply Finset.sum_nonneg
  intro w _
  split_ifs
  · linarith [hNonneg w]
  · linarith

-- Helper: P(a∧h) ≤ P(a) with nonneg prior
private lemma probSum_pand_le (prior : W → ℚ) (a h : BProp W)
    (hNonneg : ∀ w, prior w ≥ 0) :
    probSum prior (Decidable.pand W a h) ≤ probSum prior a := by
  unfold probSum Decidable.pand
  apply Finset.sum_le_sum
  intro w _
  split_ifs with h1 h2
  · linarith
  · simp only [Bool.and_eq_true] at h1; exact absurd h1.1 h2
  · linarith [hNonneg w]
  · linarith

-- Helper: P(a) = 0 + nonneg → P(a∧h) = 0
private lemma probSum_pand_zero_of_zero (prior : W → ℚ) (a h : BProp W)
    (hNonneg : ∀ w, prior w ≥ 0) (hZero : probSum prior a = 0) :
    probSum prior (Decidable.pand W a h) = 0 := by
  have hle := probSum_pand_le prior a h hNonneg
  have hge := probSum_nonneg prior (Decidable.pand W a h) hNonneg
  linarith

-- Helper: P(⊤) ≥ P(H) with nonneg prior
private lemma probSum_top_ge (prior : W → ℚ) (h : BProp W)
    (hNonneg : ∀ w, prior w ≥ 0) :
    probSum prior (Decidable.top W) ≥ probSum prior h := by
  show probSum prior h ≤ probSum prior (Decidable.top W)
  unfold probSum
  apply Finset.sum_le_sum
  intro w _
  simp only [Decidable.top]
  split_ifs <;> linarith [hNonneg w]

/-- Presupposition implies the Bayes factor equals 1.

If `presupposedIrrelevant prior a` (∀ x, P(x|a) = P(x|⊤)), then
BF_H(a) = 1 for any issue H, assuming nonneg prior and non-degenerate
issue (P(H) > 0 and P(¬H) > 0).

Proof: From presupposedIrrelevant with x := H, we get
P(H|a) = P(H|⊤) = P(H)/P(⊤). By a Bayes swap:
  P(a|H) = P(H∧a)/P(H) = P(a)·P(H)/(P(⊤)·P(H)) = P(a)/P(⊤).
This is independent of H, so P(a|H) = P(a|¬H), giving BF = 1. -/
private lemma presup_implies_bf_one (ctx : DTSContext W) (a : BProp W)
    (hPresup : presupposedIrrelevant ctx.prior a)
    (hNonneg : ∀ w, ctx.prior w ≥ 0)
    (hH : probSum ctx.prior ctx.issue.topic > 0)
    (hNH : probSum ctx.prior (Decidable.pnot W ctx.issue.topic) > 0) :
    bayesFactor ctx a = 1 := by
  set H := ctx.issue.topic
  set prior := ctx.prior
  -- Step 1: P(⊤) > 0
  have hTop : probSum prior (Decidable.top W) > 0 :=
    lt_of_lt_of_le hH (probSum_top_ge prior H hNonneg)
  -- Step 2: P(a) ≠ 0 (forced by presupposition + nonneg + P(H) > 0)
  -- If P(a) = 0, then condProb prior H a = 0, but
  -- condProb prior H (⊤) = P(H)/P(⊤) > 0, contradicting presupposition.
  have hPA : probSum prior a ≠ 0 := by
    intro hZero
    have hPres := hPresup H
    -- condProb prior H a = condProb prior H (top)
    -- With P(a) = 0: LHS = 0. RHS = P(H)/P(⊤) > 0. Contradiction.
    simp only [condProb, hZero, ↓reduceIte] at hPres
    rw [probSum_pand_top, if_neg (ne_of_gt hTop)] at hPres
    have : probSum prior H / probSum prior (Decidable.top W) > 0 :=
      div_pos hH hTop
    linarith
  -- Step 3: From presupposition, derive the joint probability equation
  -- presup with x gives: probSum(x∧a)/probSum(a) = probSum(x)/probSum(⊤)
  -- ↔ probSum(x∧a) = probSum(a) · probSum(x) / probSum(⊤)
  have hJoint : ∀ x, probSum prior (Decidable.pand W x a) =
      probSum prior a * probSum prior x / probSum prior (Decidable.top W) := by
    intro x
    have hPx := hPresup x
    simp only [condProb, hPA, ↓reduceIte] at hPx
    rw [probSum_pand_top, if_neg (ne_of_gt hTop)] at hPx
    -- hPx: probSum(x∧a)/probSum(a) = probSum(x)/probSum(⊤)
    have hPA_pos : (probSum prior a : ℚ) ≠ 0 := hPA
    have hTop_pos : (probSum prior (Decidable.top W) : ℚ) ≠ 0 := ne_of_gt hTop
    field_simp at hPx ⊢
    linarith
  -- Step 4: Derive P(a|H) = P(a|¬H) = P(a)/P(⊤)
  have hComm := probSum_pand_comm prior a H
  have hCommNH := probSum_pand_comm prior a (Decidable.pnot W H)
  -- P(a|H) = P(a∧H)/P(H) = P(H∧a)/P(H) = P(a)/P(⊤)
  have hcpH : condProb prior a H = probSum prior a /
      probSum prior (Decidable.top W) := by
    simp only [condProb, ne_of_gt hH, ↓reduceIte]
    rw [hComm, hJoint H]; field_simp
  have hcpNH : condProb prior a (Decidable.pnot W H) = probSum prior a /
      probSum prior (Decidable.top W) := by
    simp only [condProb, ne_of_gt hNH, ↓reduceIte]
    rw [hCommNH, hJoint (Decidable.pnot W H)]; field_simp
  -- Step 5: BF = P(a|H)/P(a|¬H) = 1
  simp only [bayesFactor]
  have hEq : condProb prior a H = condProb prior a (Decidable.pnot W H) := by
    rw [hcpH, hcpNH]
  by_cases hZ : condProb prior a (Decidable.pnot W H) = 0
  · rw [if_pos hZ]
    have : ¬ condProb prior a H > 0 := by rw [hEq, hZ]; linarith
    rw [if_neg this]
  · rw [if_neg hZ, hEq]; exact div_self hZ

/-- **Corollary 15**: "Also" requires non-identity.

If Q(a) is presupposed (informationally inert) and "Q(a) and also Q(b)"
is felicitous, then a ≠ b (assuming Q is injective on entities).

Proof: If a = b then Q(b) = Q(a) is presupposed, so BF(Q(b)) = 1 by
`presup_implies_bf_one`. But `AlsoFelicitous` requires Q(b) to be
relevant (BF > 1 or BF < 1) — contradiction.

Requires nonneg prior and non-degenerate issue (Merin assumes both). -/
theorem also_nonidentity {E : Type*} [DecidableEq E]
    (ctx : DTSContext W) (Q : E → BProp W) (a b : E)
    (hAlso : AlsoFelicitous ctx (Q a) (Q b))
    (_hInj : ∀ x y, Q x = Q y → x = y)
    (hNonneg : ∀ w, ctx.prior w ≥ 0)
    (hH : probSum ctx.prior ctx.issue.topic > 0)
    (hNH : probSum ctx.prior (Decidable.pnot W ctx.issue.topic) > 0) :
    a ≠ b := by
  intro hab
  subst hab
  have hBF := presup_implies_bf_one ctx (Q a) hAlso.qaPresupposed hNonneg hH hNH
  rcases hAlso.qbRelevant with hPos | hNeg
  · exact absurd hBF (ne_of_gt hPos)
  · exact absurd hBF (ne_of_lt hNeg)

/-- Presupposition implies CIP: a presupposed proposition is conditionally
independent of any other proposition given both H and ¬H.

From presupposedIrrelevant: P(x|a) = P(x) for all x. Instantiating
x = H and x = b∧H gives the joint factorization P(a∧b∧H) · P(H) =
P(a∧H) · P(b∧H), which is exactly CIP. -/
private lemma presup_implies_cip (ctx : DTSContext W) (a b : BProp W)
    (hPresup : presupposedIrrelevant ctx.prior a)
    (hNonneg : ∀ w, ctx.prior w ≥ 0)
    (hH : probSum ctx.prior ctx.issue.topic > 0)
    (hNH : probSum ctx.prior (Decidable.pnot W ctx.issue.topic) > 0) :
    CIP ctx a b := by
  set H := ctx.issue.topic
  set prior := ctx.prior
  have hTop : probSum prior (Decidable.top W) > 0 :=
    lt_of_lt_of_le hH (probSum_top_ge prior H hNonneg)
  have hPA : probSum prior a ≠ 0 := by
    intro hZero
    have hPres := hPresup H
    simp only [condProb, hZero, ↓reduceIte] at hPres
    rw [probSum_pand_top, if_neg (ne_of_gt hTop)] at hPres
    have : probSum prior H / probSum prior (Decidable.top W) > 0 := div_pos hH hTop
    linarith
  -- Key equation from presupposition: P(x∧a) = P(a)·P(x)/P(⊤)
  have hJoint : ∀ x, probSum prior (Decidable.pand W x a) =
      probSum prior a * probSum prior x / probSum prior (Decidable.top W) := by
    intro x
    have hPx := hPresup x
    simp only [condProb, hPA, ↓reduceIte] at hPx
    rw [probSum_pand_top, if_neg (ne_of_gt hTop)] at hPx
    field_simp at hPx ⊢
    linarith
  -- Helper equations
  have h_aH : probSum prior (Decidable.pand W a H) =
      probSum prior a * probSum prior H / probSum prior (Decidable.top W) := by
    rw [probSum_pand_comm]; exact hJoint H
  have h_aNH : probSum prior (Decidable.pand W a (Decidable.pnot W H)) =
      probSum prior a * probSum prior (Decidable.pnot W H) /
      probSum prior (Decidable.top W) := by
    rw [probSum_pand_comm]; exact hJoint (Decidable.pnot W H)
  have h_abH : probSum prior (Decidable.pand W (Decidable.pand W a b) H) =
      probSum prior a * probSum prior (Decidable.pand W b H) /
      probSum prior (Decidable.top W) := by
    have : probSum prior (Decidable.pand W (Decidable.pand W a b) H) =
        probSum prior (Decidable.pand W (Decidable.pand W b H) a) := by
      congr 1; funext w; simp [Decidable.pand]
      cases a w <;> cases b w <;> cases H w <;> rfl
    rw [this]; exact hJoint (Decidable.pand W b H)
  have h_abNH : probSum prior (Decidable.pand W (Decidable.pand W a b) (Decidable.pnot W H)) =
      probSum prior a * probSum prior (Decidable.pand W b (Decidable.pnot W H)) /
      probSum prior (Decidable.top W) := by
    have : probSum prior (Decidable.pand W (Decidable.pand W a b) (Decidable.pnot W H)) =
        probSum prior (Decidable.pand W (Decidable.pand W b (Decidable.pnot W H)) a) := by
      congr 1; funext w; simp [Decidable.pand, Decidable.pnot]
      cases a w <;> cases b w <;> cases H w <;> rfl
    rw [this]; exact hJoint (Decidable.pand W b (Decidable.pnot W H))
  have hHne := ne_of_gt hH
  have hNHne := ne_of_gt hNH
  constructor
  · -- CIP for H: P(a∧b|H) = P(a|H)·P(b|H)
    rw [condProb_of_ne_zero _ _ _ hHne, condProb_of_ne_zero _ _ _ hHne,
        condProb_of_ne_zero _ _ _ hHne]
    rw [h_aH, h_abH]; field_simp
  · -- CIP for ¬H: same argument with ¬H
    rw [condProb_of_ne_zero _ _ _ hNHne, condProb_of_ne_zero _ _ _ hNHne,
        condProb_of_ne_zero _ _ _ hNHne]
    rw [h_aNH, h_abNH]; field_simp

/-- **Fact 17**: Presupposition implies multiplicativity without CIP.

If A is presupposed (P(X|A) = P(X) for all X), then
BF(A∧B) = BF(A) · BF(B) holds without the CIP assumption.

Proof: Presupposition implies CIP (the joint factorizes trivially
when one factor is informationally inert), and multiplicativity
follows from CIP by `bayes_factor_multiplicative_under_cip`. -/
theorem presuppositional_independence_additivity
    (ctx : DTSContext W) (a b : BProp W)
    (hPresup : presupposedIrrelevant ctx.prior a)
    (hNonneg : ∀ w, ctx.prior w ≥ 0)
    (hH : probSum ctx.prior ctx.issue.topic > 0)
    (hNH : probSum ctx.prior (Decidable.pnot W ctx.issue.topic) > 0)
    (hNotH : condProb ctx.prior a (Decidable.pnot W ctx.issue.topic) ≠ 0)
    (hNotH' : condProb ctx.prior b (Decidable.pnot W ctx.issue.topic) ≠ 0)
    (hABNotH : condProb ctx.prior (Decidable.pand W a b)
      (Decidable.pnot W ctx.issue.topic) ≠ 0) :
    bayesFactor ctx (Decidable.pand W a b) =
      bayesFactor ctx a * bayesFactor ctx b :=
  bayes_factor_multiplicative_under_cip ctx a b
    (presup_implies_cip ctx a b hPresup hNonneg hH hNH) hNotH hNotH' hABNotH

/-! **Prediction 4** (not formalized): "Also" removes causal implicature.

In "Kim fell and she also broke her arm", the additive particle "also"
enforces presuppositional independence of the antecedent ("Kim fell"),
removing the default causal reading that plain "and" would carry
("Kim fell and [as a result] broke her arm").

This connects to `Core.Causation` — the causal reading arises from
non-independence of the conjuncts, and "also" explicitly marks the
antecedent as presupposed (hence independent).

-- TODO: Formalize using CausalDynamics from Core.Causation -/

end Theorems

end Theories.DTS.Also
