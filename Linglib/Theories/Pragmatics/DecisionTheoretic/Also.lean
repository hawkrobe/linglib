import Linglib.Theories.Pragmatics.DecisionTheoretic.Core
import Linglib.Theories.Pragmatics.DecisionTheoretic.ScalarImplicature
import Linglib.Core.Semantics.Presupposition
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Decision-Theoretic Semantics: "Also" (@cite{merin-1999} §5.2–5.4)
@cite{merin-1999}

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

-/

namespace DTS.Also

open Core.Presupposition
open DTS
open DTS.ScalarImplicature (sgnRelevance RelevanceSign)

-- ============================================================
-- Section 1: Presupposition as Irrelevance (Def. 12)
-- ============================================================

/-- **Definition 12**: A proposition A is i-presupposed iff conditioning on A
doesn't change any conditional probability.

This is stronger than P(A)=1: it means A is informationally *inert*.
Formally: P(X|A) = P(X) for all X, which is equivalent to
P(X|A) = P(X|⊤) for all X. -/
def presupposedIrrelevant {W : Type*} [Fintype W]
    (prior : W → ℚ) (a : Set W) [DecidablePred (· ∈ a)] : Prop :=
  ∀ (x : Set W) [DecidablePred (· ∈ x)],
    condProb prior x a = condProb prior x (Set.univ : Set W)

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
    (ctx : DTSContext W) (d e : Set W)
    [DecidablePred (· ∈ d)] [DecidablePred (· ∈ e)] where
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
    (ctx : DTSContext W) (qa qb : Set W)
    [DecidablePred (· ∈ qa)] [DecidablePred (· ∈ qb)] where
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
    (ctx : DTSContext W) (qa qb : Set W)
    [DecidablePred (· ∈ qa)] [DecidablePred (· ∈ qb)] where
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
    (ctx : DTSContext W) (φ : Set W) [DecidablePred (· ∈ φ)] : Prop :=
  0 < margProb ctx.prior φ ∧
  margProb ctx.prior φ < 1 ∧
  irrelevant ctx φ

-- ============================================================
-- Section 5: Theorems
-- ============================================================

section Theorems

variable {W : Type*} [Fintype W]

-- Helper: condProb unfolds when denominator is nonzero
private lemma condProb_of_ne_zero (prior : W → ℚ) (e h : Set W)
    [DecidablePred (· ∈ e)] [DecidablePred (· ∈ h)]
    (hne : probSum prior h ≠ 0) :
    condProb prior e h = probSum prior (e ∩ h) / probSum prior h := by
  unfold condProb
  dsimp only
  rw [if_neg hne]

-- Helper: probSum of pand is commutative
private lemma probSum_pand_comm (prior : W → ℚ) (a b : Set W)
    [DecidablePred (· ∈ a)] [DecidablePred (· ∈ b)] :
    probSum prior (a ∩ b) = probSum prior (b ∩ a) := by
  unfold probSum
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases ha : w ∈ a <;> by_cases hb : w ∈ b <;>
    simp [ha, hb]

-- Helper: probSum of pand with top is identity
private lemma probSum_pand_top (prior : W → ℚ) (a : Set W)
    [DecidablePred (· ∈ a)] :
    probSum prior (a ∩ (Set.univ : Set W)) = probSum prior a := by
  unfold probSum
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases ha : w ∈ a <;>
    simp [ha]

-- Helper: probSum is nonneg with nonneg prior
private lemma probSum_nonneg (prior : W → ℚ) (p : Set W) [DecidablePred (· ∈ p)]
    (hNonneg : ∀ w, prior w ≥ 0) : probSum prior p ≥ 0 := by
  show 0 ≤ probSum prior p
  unfold probSum
  apply Finset.sum_nonneg
  intro w _
  by_cases hp : w ∈ p
  · simp [hp]; exact hNonneg w
  · simp [hp]

-- Helper: P(a∧h) ≤ P(a) with nonneg prior
private lemma probSum_pand_le (prior : W → ℚ) (a h : Set W)
    [DecidablePred (· ∈ a)] [DecidablePred (· ∈ h)]
    (hNonneg : ∀ w, prior w ≥ 0) :
    probSum prior (a ∩ h) ≤ probSum prior a := by
  unfold probSum
  apply Finset.sum_le_sum
  intro w _
  by_cases ha : w ∈ a
  · by_cases hh : w ∈ h
    · simp [ha, hh]
    · simp [ha, hh]; exact hNonneg w
  · simp [ha]

-- Helper: P(a) = 0 + nonneg → P(a∧h) = 0
private lemma probSum_pand_zero_of_zero (prior : W → ℚ) (a h : Set W)
    [DecidablePred (· ∈ a)] [DecidablePred (· ∈ h)]
    (hNonneg : ∀ w, prior w ≥ 0) (hZero : probSum prior a = 0) :
    probSum prior (a ∩ h) = 0 := by
  have hle := probSum_pand_le prior a h hNonneg
  have hge := probSum_nonneg prior (a ∩ h) hNonneg
  linarith

-- Helper: P(⊤) ≥ P(H) with nonneg prior
private lemma probSum_top_ge (prior : W → ℚ) (h : Set W) [DecidablePred (· ∈ h)]
    (hNonneg : ∀ w, prior w ≥ 0) :
    probSum prior (Set.univ : Set W) ≥ probSum prior h := by
  show probSum prior h ≤ probSum prior (Set.univ : Set W)
  unfold probSum
  apply Finset.sum_le_sum
  intro w _
  by_cases hh : w ∈ h
  · simp [hh]
  · simp [hh]; exact hNonneg w

/-- Presupposition implies the Bayes factor equals 1.

If `presupposedIrrelevant prior a` (∀ x, P(x|a) = P(x|⊤)), then
BF_H(a) = 1 for any issue H, assuming nonneg prior and non-degenerate
issue (P(H) > 0 and P(¬H) > 0).

Proof: From presupposedIrrelevant with x := H, we get
P(H|a) = P(H|⊤) = P(H)/P(⊤). By a Bayes swap:
  P(a|H) = P(H∧a)/P(H) = P(a)·P(H)/(P(⊤)·P(H)) = P(a)/P(⊤).
This is independent of H, so P(a|H) = P(a|¬H), giving BF = 1. -/
private lemma presup_implies_bf_one (ctx : DTSContext W) (a : Set W)
    [DecidablePred (· ∈ a)]
    (hPresup : presupposedIrrelevant ctx.prior a)
    (hNonneg : ∀ w, ctx.prior w ≥ 0)
    (hH : probSum ctx.prior ctx.topic > 0)
    (hNH : probSum ctx.prior (ctx.topicᶜ) > 0) :
    bayesFactor ctx a = 1 := by
  -- Step 1: P(⊤) > 0
  have hTop : probSum ctx.prior (Set.univ : Set W) > 0 :=
    lt_of_lt_of_le hH (probSum_top_ge ctx.prior ctx.topic hNonneg)
  -- Step 2: P(a) ≠ 0 (forced by presupposition + nonneg + P(H) > 0)
  -- If P(a) = 0, then condProb prior H a = 0, but
  -- condProb prior H (⊤) = P(H)/P(⊤) > 0, contradicting presupposition.
  have hPA : probSum ctx.prior a ≠ 0 := by
    intro hZero
    have hPres := hPresup ctx.topic
    unfold condProb at hPres
    dsimp only at hPres
    rw [if_pos hZero] at hPres
    rw [probSum_pand_top, if_neg (ne_of_gt hTop)] at hPres
    have : probSum ctx.prior ctx.topic / probSum ctx.prior (Set.univ : Set W) > 0 :=
      div_pos hH hTop
    linarith
  -- Step 3: From presupposition, derive the joint probability equation
  -- presup with x gives: probSum(x∧a)/probSum(a) = probSum(x)/probSum(⊤)
  -- ↔ probSum(x∧a) = probSum(a) · probSum(x) / probSum(⊤)
  have hJoint : ∀ (x : Set W) [DecidablePred (· ∈ x)],
      probSum ctx.prior (x ∩ a) =
      probSum ctx.prior a * probSum ctx.prior x / probSum ctx.prior (Set.univ : Set W) := by
    intro x _
    have hPx := hPresup x
    unfold condProb at hPx
    dsimp only at hPx
    rw [if_neg hPA, if_neg (ne_of_gt hTop)] at hPx
    rw [probSum_pand_top] at hPx
    -- hPx: probSum(x∧a)/probSum(a) = probSum(x)/probSum(⊤)
    have hPA_pos : (probSum ctx.prior a : ℚ) ≠ 0 := hPA
    have hTop_pos : (probSum ctx.prior (Set.univ : Set W) : ℚ) ≠ 0 := ne_of_gt hTop
    field_simp at hPx ⊢
    linarith
  -- Step 4: Derive P(a|H) = P(a|¬H) = P(a)/P(⊤)
  have hComm := probSum_pand_comm ctx.prior a ctx.topic
  have hCommNH := probSum_pand_comm ctx.prior a (ctx.topicᶜ)
  -- P(a|H) = P(a∧H)/P(H) = P(H∧a)/P(H) = P(a)/P(⊤)
  have hcpH : condProb ctx.prior a ctx.topic = probSum ctx.prior a /
      probSum ctx.prior (Set.univ : Set W) := by
    unfold condProb
    dsimp only
    rw [if_neg (ne_of_gt hH)]
    rw [hComm, hJoint ctx.topic]
    field_simp
  have hcpNH : condProb ctx.prior a (ctx.topicᶜ) =
      probSum ctx.prior a / probSum ctx.prior (Set.univ : Set W) := by
    unfold condProb
    dsimp only
    rw [if_neg (ne_of_gt hNH)]
    rw [hCommNH, hJoint (ctx.topicᶜ)]
    field_simp
  -- Step 5: BF = P(a|H)/P(a|¬H) = 1
  unfold bayesFactor
  dsimp only
  have hEq : condProb ctx.prior a ctx.topic =
      condProb ctx.prior a (ctx.topicᶜ) := by
    rw [hcpH, hcpNH]
  by_cases hZ : condProb ctx.prior a (ctx.topicᶜ) = 0
  · rw [if_pos hZ]
    have hnpos : ¬ condProb ctx.prior a ctx.topic > 0 := by rw [hEq, hZ]; linarith
    rw [if_neg hnpos]
  · rw [if_neg hZ, hEq]; exact div_self hZ

/-- **Corollary 15**: "Also" requires non-identity.

If Q(a) is presupposed (informationally inert) and "Q(a) and also Q(b)"
is felicitous, then a ≠ b (assuming Q is injective on entities).

Proof: If a = b then Q(b) = Q(a) is presupposed, so BF(Q(b)) = 1 by
`presup_implies_bf_one`. But `AlsoFelicitous` requires Q(b) to be
relevant (BF > 1 or BF < 1) — contradiction.

Requires nonneg prior and non-degenerate issue (Merin assumes both). -/
theorem also_nonidentity {E : Type*} [DecidableEq E]
    (ctx : DTSContext W) (Q : E → Set W) [∀ e, DecidablePred (· ∈ Q e)]
    (a b : E)
    (hAlso : AlsoFelicitous ctx (Q a) (Q b))
    (_hInj : ∀ x y, Q x = Q y → x = y)
    (hNonneg : ∀ w, ctx.prior w ≥ 0)
    (hH : probSum ctx.prior ctx.topic > 0)
    (hNH : probSum ctx.prior (ctx.topicᶜ) > 0) :
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
private lemma presup_implies_cip (ctx : DTSContext W) (a b : Set W)
    [DecidablePred (· ∈ a)] [DecidablePred (· ∈ b)]
    (hPresup : presupposedIrrelevant ctx.prior a)
    (hNonneg : ∀ w, ctx.prior w ≥ 0)
    (hH : probSum ctx.prior ctx.topic > 0)
    (hNH : probSum ctx.prior (ctx.topicᶜ) > 0) :
    CIP ctx a b := by
  have hTop : probSum ctx.prior (Set.univ : Set W) > 0 :=
    lt_of_lt_of_le hH (probSum_top_ge ctx.prior ctx.topic hNonneg)
  have hPA : probSum ctx.prior a ≠ 0 := by
    intro hZero
    have hPres := hPresup ctx.topic
    unfold condProb at hPres
    dsimp only at hPres
    rw [if_pos hZero] at hPres
    rw [probSum_pand_top, if_neg (ne_of_gt hTop)] at hPres
    have : probSum ctx.prior ctx.topic / probSum ctx.prior (Set.univ : Set W) > 0 :=
      div_pos hH hTop
    linarith
  -- Key equation from presupposition: P(x∧a) = P(a)·P(x)/P(⊤)
  have hJoint : ∀ (x : Set W) [DecidablePred (· ∈ x)],
      probSum ctx.prior (x ∩ a) =
      probSum ctx.prior a * probSum ctx.prior x / probSum ctx.prior (Set.univ : Set W) := by
    intro x _
    have hPx := hPresup x
    unfold condProb at hPx
    dsimp only at hPx
    rw [if_neg hPA, if_neg (ne_of_gt hTop)] at hPx
    rw [probSum_pand_top] at hPx
    field_simp at hPx ⊢
    linarith
  -- Helper equations
  have h_aH : probSum ctx.prior (a ∩ ctx.topic) =
      probSum ctx.prior a * probSum ctx.prior ctx.topic /
      probSum ctx.prior (Set.univ : Set W) := by
    rw [probSum_pand_comm]; exact hJoint ctx.topic
  have h_aNH : probSum ctx.prior (a ∩ (ctx.topicᶜ)) =
      probSum ctx.prior a * probSum ctx.prior (ctx.topicᶜ) /
      probSum ctx.prior (Set.univ : Set W) := by
    rw [probSum_pand_comm]; exact hJoint (ctx.topicᶜ)
  have h_abH : probSum ctx.prior ((a ∩ b) ∩ ctx.topic) =
      probSum ctx.prior a * probSum ctx.prior (b ∩ ctx.topic) /
      probSum ctx.prior (Set.univ : Set W) := by
    have hperm :
        probSum ctx.prior ((a ∩ b) ∩ ctx.topic) =
        probSum ctx.prior ((b ∩ ctx.topic) ∩ a) := by
      unfold probSum
      refine Finset.sum_congr rfl (fun w _ => ?_)
      by_cases ha : w ∈ a <;> by_cases hb : w ∈ b <;> by_cases hh : ctx.topic w <;>
        simp [ha, hb, hh]
    rw [hperm]; exact hJoint (b ∩ ctx.topic)
  have h_abNH :
      probSum ctx.prior ((a ∩ b) ∩ (ctx.topicᶜ)) =
      probSum ctx.prior a *
        probSum ctx.prior (b ∩ (ctx.topicᶜ)) /
      probSum ctx.prior (Set.univ : Set W) := by
    have hperm :
        probSum ctx.prior ((a ∩ b) ∩ (ctx.topicᶜ)) =
        probSum ctx.prior (((b ∩ (ctx.topicᶜ)) ∩ a)) := by
      unfold probSum
      refine Finset.sum_congr rfl (fun w _ => ?_)
      by_cases ha : w ∈ a <;> by_cases hb : w ∈ b <;> by_cases hh : ctx.topic w <;>
        simp [ha, hb, hh]
    rw [hperm]; exact hJoint (b ∩ (ctx.topicᶜ))
  have hHne := ne_of_gt hH
  have hNHne := ne_of_gt hNH
  refine ⟨?_, ?_⟩
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
    (ctx : DTSContext W) (a b : Set W)
    [DecidablePred (· ∈ a)] [DecidablePred (· ∈ b)]
    (hPresup : presupposedIrrelevant ctx.prior a)
    (hNonneg : ∀ w, ctx.prior w ≥ 0)
    (hH : probSum ctx.prior ctx.topic > 0)
    (hNH : probSum ctx.prior (ctx.topicᶜ) > 0)
    (hNotH : condProb ctx.prior a (ctx.topicᶜ) ≠ 0)
    (hNotH' : condProb ctx.prior b (ctx.topicᶜ) ≠ 0)
    (hABNotH : condProb ctx.prior (a ∩ b)
      (ctx.topicᶜ) ≠ 0) :
    bayesFactor ctx (a ∩ b) =
      bayesFactor ctx a * bayesFactor ctx b :=
  bayes_factor_multiplicative_under_cip ctx a b
    (presup_implies_cip ctx a b hPresup hNonneg hH hNH) hNotH hNotH' hABNotH

/-! **Prediction 4** (not formalized): "Also" removes causal implicature.

In "Kim fell and she also broke her arm", the additive particle "also"
enforces presuppositional independence of the antecedent ("Kim fell"),
removing the default causal reading that plain "and" would carry
("Kim fell and [as a result] broke her arm").

This connects to `Core.StructuralEquationModel` — the causal reading arises from
non-independence of the conjuncts, and "also" explicitly marks the
antecedent as presupposed (hence independent).

-- TODO: Formalize using CausalDynamics from Core.StructuralEquationModel -/

end Theorems

end DTS.Also
