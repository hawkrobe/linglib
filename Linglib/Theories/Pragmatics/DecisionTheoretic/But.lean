import Linglib.Theories.Pragmatics.DecisionTheoretic.Core

/-!
# Decision-Theoretic Semantics: "But" (@cite{merin-1999} §4)
@cite{merin-1999}

Merin's DTS account of adversative conjunction. The felicity of "A but B"
requires that A and B have opposite relevance signs, and that the conjunction
A∧B is negatively relevant (the "but"-clause wins). The default interpretation
sets H = B, yielding unexpected-B-given-A.

## Key Definitions

- `butFelicitous` (Hypothesis 4): felicity conditions for "A but B"
- `NNIR` (Def. 10): Non-Negative Instantial Relevance
- `defaultButCtx`: the default interpretation where H = B

## Main Results

- **Theorem 8**: CIP + contrariness → unexpectedness (P(B|A) < P(B))
- **Theorem 9**: When H = B, CIP holds automatically
- **Theorem 10**: Properties of default-but interpretation
- **Corollary 11** (Harris universal): NNIR prevents "Qa but Qb"

-/

namespace DTS.But

open DTS

-- ============================================================
-- Section 1: Felicity Conditions for "But"
-- ============================================================

/-- **Hypothesis 4**: Felicity conditions for "A but B".

"A but B" is felicitous iff:
(i) A is positively relevant to H,
(ii) B is negatively relevant to H,
(iii) A∧B is negatively relevant to H (B "wins"). -/
def butFelicitous {W : Type*} [Fintype W]
    (ctx : DTSContext W) (a b : Set W) [DecidablePred (· ∈ a)] [DecidablePred (· ∈ b)] :
    Prop :=
  posRelevant ctx a ∧ negRelevant ctx b ∧
  negRelevant ctx (a ∩ b)

-- ============================================================
-- Section 2: Non-Negative Instantial Relevance (NNIR)
-- ============================================================

/-- **Definition 10**: Non-Negative Instantial Relevance (NNIR).

For a predicate Q over entities, observing Q(a) never makes Q(b) less
probable: P(Q(b)|Q(a)) ≥ P(Q(b)) for all a, b.

This captures a cross-linguistic universal: properties are positively
correlated across instances (knowing one dog is friendly makes it more
likely another is). -/
def NNIR {W : Type*} [Fintype W] (E : Type*)
    (prior : W → ℚ) (Q : E → Set W) [∀ e, DecidablePred (· ∈ Q e)] : Prop :=
  ∀ (a b : E), condProb prior (Q b) (Q a) ≥ margProb prior (Q b)

-- ============================================================
-- Section 3: Default But (H = B)
-- ============================================================

/-- Default "but" context: the issue is identified with the
but-clause itself (H = B).

Merin argues this is the preferred interpretation when no explicit
issue is provided. -/
def defaultButCtx {W : Type*} (prior : W → ℚ) (b : Set W)
    [DecidablePred (· ∈ b)] : DTSContext W :=
  ⟨b, inferInstance, prior⟩

-- ============================================================
-- Section 4: Theorems
-- ============================================================

section Theorems

variable {W : Type*} [Fintype W]

-- Helper lemmas for probSum with repeated/contradictory propositions

private lemma probSum_pand_self (prior : W → ℚ) (b : Set W)
    [DecidablePred (· ∈ b)] :
    probSum prior (b ∩ b) = probSum prior b := by
  unfold probSum
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases hb : w ∈ b
  · simp [hb]
  · simp [hb]

private lemma probSum_pand_assoc_self (prior : W → ℚ) (a b : Set W)
    [DecidablePred (· ∈ a)] [DecidablePred (· ∈ b)] :
    probSum prior ((a ∩ b) ∩ b) =
    probSum prior (a ∩ b) := by
  unfold probSum
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases ha : w ∈ a <;> by_cases hb : w ∈ b <;>
    simp [ha, hb]

private lemma probSum_pand_pnot_zero (prior : W → ℚ) (b : Set W)
    [DecidablePred (· ∈ b)] :
    probSum prior (b ∩ (bᶜ)) = 0 := by
  unfold probSum
  apply Finset.sum_eq_zero
  intro w _
  by_cases hb : w ∈ b
  · simp [hb]
  · simp [hb]

private lemma probSum_pand_pand_pnot_zero (prior : W → ℚ) (a b : Set W)
    [DecidablePred (· ∈ a)] [DecidablePred (· ∈ b)] :
    probSum prior ((a ∩ b) ∩ (bᶜ)) = 0 := by
  unfold probSum
  apply Finset.sum_eq_zero
  intro w _
  by_cases ha : w ∈ a <;> by_cases hb : w ∈ b <;>
    simp [ha, hb]

/-- condProb of b given ¬b is always 0: P(B|¬B) = 0. -/
private lemma condProb_self_given_not (prior : W → ℚ) (b : Set W)
    [DecidablePred (· ∈ b)] :
    condProb prior b (bᶜ) = 0 := by
  unfold condProb
  dsimp only
  split
  · rfl
  · rw [probSum_pand_pnot_zero, zero_div]

/-- BF_B(B) ≥ 1: B is never negatively relevant to itself. -/
private lemma bayesFactor_self_ge_one (prior : W → ℚ) (b : Set W)
    [DecidablePred (· ∈ b)] :
    bayesFactor (defaultButCtx prior b) b ≥ 1 := by
  unfold bayesFactor defaultButCtx
  dsimp only
  rw [if_pos (condProb_self_given_not prior b)]
  split <;> linarith

/-- Total probability: probSum(A) = probSum(A∧B) + probSum(A∧¬B). -/
private lemma probSum_pand_split (prior : W → ℚ) (a b : Set W)
    [DecidablePred (· ∈ a)] [DecidablePred (· ∈ b)] :
    probSum prior a =
    probSum prior (a ∩ b) +
    probSum prior (a ∩ (bᶜ)) := by
  unfold probSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases ha : w ∈ a <;> by_cases hb : w ∈ b <;>
    simp [ha, hb]

/-- probSum(B) + probSum(¬B) = probSum(⊤). -/
private lemma probSum_add_pnot (prior : W → ℚ) (b : Set W)
    [DecidablePred (· ∈ b)] :
    probSum prior b + probSum prior (bᶜ) =
    probSum prior (Set.univ : Set W) := by
  unfold probSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases hb : w ∈ b <;>
    simp [hb]

/-- pand is commutative at the probSum level. -/
private lemma probSum_pand_comm (prior : W → ℚ) (a b : Set W)
    [DecidablePred (· ∈ a)] [DecidablePred (· ∈ b)] :
    probSum prior (a ∩ b) = probSum prior (b ∩ a) := by
  unfold probSum
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases ha : w ∈ a <;> by_cases hb : w ∈ b <;>
    simp [ha, hb]

/-- probSum(pand A top) = probSum A. -/
private lemma probSum_pand_top (prior : W → ℚ) (a : Set W)
    [DecidablePred (· ∈ a)] :
    probSum prior (a ∩ (Set.univ : Set W)) = probSum prior a := by
  unfold probSum
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases ha : w ∈ a <;>
    simp [ha]

/-- probSum is non-negative when prior is non-negative. -/
private lemma probSum_nonneg' (prior : W → ℚ) (hP : ∀ w, prior w ≥ 0) (p : Set W)
    [DecidablePred (· ∈ p)] :
    0 ≤ probSum prior p := by
  unfold probSum; apply Finset.sum_nonneg; intro w _; split <;> linarith [hP w]

/-- CIP in probSum form: P(A∧B∧H)·P(H) = P(A∧H)·P(B∧H). -/
private lemma cip_probSum (prior : W → ℚ) (a b h : Set W)
    [DecidablePred (· ∈ a)] [DecidablePred (· ∈ b)] [DecidablePred (· ∈ h)]
    (hh : probSum prior h ≠ 0)
    (hcip : condProb prior (a ∩ b) h =
      condProb prior a h * condProb prior b h) :
    probSum prior ((a ∩ b) ∩ h) * probSum prior h =
    probSum prior (a ∩ h) * probSum prior (b ∩ h) := by
  simp only [condProb, hh, ↓reduceIte] at hcip
  field_simp at hcip; linarith

/-- Cross-product factorization identity (with normalization). -/
private lemma cross_product_factorization (aH anH bH bnH pH pnH : ℚ)
    (hsum : pH + pnH = 1) :
    (aH + anH) * (bH + bnH) * (pH * pnH) - (aH * bH * pnH + anH * bnH * pH) =
    (pnH * aH - pH * anH) * (pH * bnH - pnH * bH) := by
  have : pnH = 1 - pH := by linarith
  subst this; ring

/-- negRelevant implies condProb(e|¬H) ≠ 0. -/
private lemma negRelevant_condProb_ne (ctx : DTSContext W) (e : Set W)
    [DecidablePred (· ∈ e)]
    (hNeg : negRelevant ctx e) :
    condProb ctx.prior e (ctx.topicᶜ) ≠ 0 := by
  intro h
  have hbf : bayesFactor ctx e ≥ 1 := by
    unfold bayesFactor; dsimp only; rw [if_pos h]; split <;> linarith
  exact absurd hbf (not_le.mpr hNeg)

/-- posRelevant implies the cross-product sign: P(E∧H)·P(¬H) > P(E∧¬H)·P(H).
    When condProb(E|¬H) = 0, reduces to showing P(E∧H) > 0. -/
private lemma posRelevant_cross (ctx : DTSContext W) (e : Set W)
    [DecidablePred (· ∈ e)]
    (hPrior : ∀ w, ctx.prior w ≥ 0)
    (hpos : posRelevant ctx e)
    (hH_pos : 0 < probSum ctx.prior ctx.topic)
    (hNH_pos : 0 < probSum ctx.prior (ctx.topicᶜ)) :
    probSum ctx.prior (e ∩ (ctx.topicᶜ)) *
      probSum ctx.prior ctx.topic <
    probSum ctx.prior (e ∩ ctx.topic) *
      probSum ctx.prior (ctx.topicᶜ) := by
  have hH_ne := ne_of_gt hH_pos
  have hNH_ne := ne_of_gt hNH_pos
  by_cases hcnH : condProb ctx.prior e (ctx.topicᶜ) = 0
  · -- condProb(E|¬H) = 0 means P(E∧¬H) = 0
    have hEnH_zero :
        probSum ctx.prior (e ∩ (ctx.topicᶜ)) = 0 := by
      have h1 := probSum_nonneg' ctx.prior hPrior (e ∩ (ctx.topicᶜ))
      unfold condProb at hcnH; rw [if_neg hNH_ne] at hcnH
      rw [div_eq_zero_iff] at hcnH
      cases hcnH with
      | inl h => linarith
      | inr h => exact absurd h hNH_ne
    rw [hEnH_zero, zero_mul]
    -- Need P(E∧H) > 0; BF > 1 with condProb(E|¬H) = 0 forces condProb(E|H) > 0
    have hcH_pos : condProb ctx.prior e ctx.topic > 0 := by
      by_contra hle; push_neg at hle
      have hbf_le : bayesFactor ctx e ≤ 1 := by
        unfold bayesFactor; dsimp only; rw [if_pos hcnH, if_neg (not_lt.mpr hle)]
      exact absurd hbf_le (not_le.mpr hpos)
    have hEH_pos : 0 < probSum ctx.prior (e ∩ ctx.topic) := by
      unfold condProb at hcH_pos; rw [if_neg hH_ne] at hcH_pos
      have h_nn := probSum_nonneg' ctx.prior hPrior (e ∩ ctx.topic)
      by_contra hle; push_neg at hle
      have := le_antisymm hle h_nn
      simp [this] at hcH_pos
    positivity
  · -- condProb(E|¬H) ≠ 0: BF = condProb(E|H)/condProb(E|¬H) > 1
    have hcnH_pos : 0 < condProb ctx.prior e (ctx.topicᶜ) := by
      have h_nn : 0 ≤ condProb ctx.prior e (ctx.topicᶜ) := by
        unfold condProb; rw [if_neg hNH_ne]
        exact div_nonneg (probSum_nonneg' ctx.prior hPrior _) (le_of_lt hNH_pos)
      exact lt_of_le_of_ne h_nn (Ne.symm hcnH)
    have hbf_eq : bayesFactor ctx e = condProb ctx.prior e ctx.topic /
        condProb ctx.prior e (ctx.topicᶜ) := by
      unfold bayesFactor; dsimp only; rw [if_neg hcnH]
    have hcH_gt : condProb ctx.prior e (ctx.topicᶜ) <
        condProb ctx.prior e ctx.topic := by
      rw [← one_lt_div hcnH_pos, ← hbf_eq]; exact hpos
    unfold condProb at hcH_gt; rw [if_neg hH_ne, if_neg hNH_ne] at hcH_gt
    rw [div_lt_div_iff₀ hNH_pos hH_pos] at hcH_gt
    linarith

/-- negRelevant implies the cross-product sign: P(E∧H)·P(¬H) < P(E∧¬H)·P(H). -/
private lemma negRelevant_cross (ctx : DTSContext W) (e : Set W)
    [DecidablePred (· ∈ e)]
    (hPrior : ∀ w, ctx.prior w ≥ 0)
    (hneg : negRelevant ctx e)
    (hH_pos : 0 < probSum ctx.prior ctx.topic)
    (hNH_pos : 0 < probSum ctx.prior (ctx.topicᶜ)) :
    probSum ctx.prior (e ∩ ctx.topic) *
      probSum ctx.prior (ctx.topicᶜ) <
    probSum ctx.prior (e ∩ (ctx.topicᶜ)) *
      probSum ctx.prior ctx.topic := by
  have hH_ne := ne_of_gt hH_pos
  have hNH_ne := ne_of_gt hNH_pos
  have hcnH_ne := negRelevant_condProb_ne ctx e hneg
  have hcnH_pos : 0 < condProb ctx.prior e (ctx.topicᶜ) := by
    have h_nn : 0 ≤ condProb ctx.prior e (ctx.topicᶜ) := by
      unfold condProb; rw [if_neg hNH_ne]
      exact div_nonneg (probSum_nonneg' ctx.prior hPrior _) (le_of_lt hNH_pos)
    exact lt_of_le_of_ne h_nn (Ne.symm hcnH_ne)
  have hbf_eq : bayesFactor ctx e = condProb ctx.prior e ctx.topic /
      condProb ctx.prior e (ctx.topicᶜ) := by
    unfold bayesFactor; dsimp only; rw [if_neg hcnH_ne]
  have hcH_lt : condProb ctx.prior e ctx.topic <
      condProb ctx.prior e (ctx.topicᶜ) := by
    rw [← div_lt_one hcnH_pos, ← hbf_eq]; exact hneg
  unfold condProb at hcH_lt; rw [if_neg hH_ne, if_neg hNH_ne] at hcH_lt
  have := (div_lt_div_iff₀ hH_pos hNH_pos).mp hcH_lt
  linarith

/-- **Theorem 8**: CIP + contrariness implies unexpectedness.

If A and B are conditionally independent given H and ¬H, and have
opposite relevance signs, then P(B|A) < P(B) — B is unexpected given A.

Proof sketch: CIP gives P(B|H,A) = P(B|H) and P(B|¬H,A) = P(B|¬H).
By total probability: P(B|A) = P(B|H)·P(H|A) + P(B|¬H)·P(¬H|A).
And P(B) = P(B|H)·P(H) + P(B|¬H)·P(¬H).
So P(B|A) - P(B) = (P(B|H) - P(B|¬H))·(P(H|A) - P(H)).
Contrariness makes the two factors have opposite signs, giving P(B|A) < P(B). -/
theorem cip_contrariness_implies_unexpectedness (ctx : DTSContext W)
    (a b : Set W) [DecidablePred (· ∈ a)] [DecidablePred (· ∈ b)]
    (hPrior : ∀ w, ctx.prior w ≥ 0)
    (hNorm : probSum ctx.prior (Set.univ : Set W) = 1)
    (hcip : CIP ctx a b)
    (hcontr : hContrary ctx a b)
    (hA_pos : 0 < probSum ctx.prior a)
    (hH_pos : 0 < probSum ctx.prior ctx.topic)
    (hNH_pos : 0 < probSum ctx.prior (ctx.topicᶜ)) :
    condProb ctx.prior b a < margProb ctx.prior b := by
  set prior := ctx.prior
  set H := ctx.topic
  set nH := Hᶜ
  -- Abbreviations for probSum values
  set pH := probSum prior H
  set pnH := probSum prior nH
  set aH := probSum prior (a ∩ H)
  set anH := probSum prior (a ∩ nH)
  set bH := probSum prior (b ∩ H)
  set bnH := probSum prior (b ∩ nH)
  set abH := probSum prior ((a ∩ b) ∩ H)
  set abnH := probSum prior ((a ∩ b) ∩ nH)
  set pAB := probSum prior (a ∩ b)
  set pA := probSum prior a
  set pB := probSum prior b
  -- Non-negativity
  have haH := probSum_nonneg' prior hPrior (a ∩ H)
  have hanH := probSum_nonneg' prior hPrior (a ∩ nH)
  have hbH := probSum_nonneg' prior hPrior (b ∩ H)
  have hbnH := probSum_nonneg' prior hPrior (b ∩ nH)
  have hpAB_nn := probSum_nonneg' prior hPrior (a ∩ b)
  -- Normalization: pH + pnH = 1
  have hNormHP : pH + pnH = 1 := by
    have := probSum_add_pnot prior H
    rw [hNorm] at this; exact this
  -- Total probability decompositions
  have htotA : pA = aH + anH := probSum_pand_split prior a H
  have htotB : pB = bH + bnH := probSum_pand_split prior b H
  have htotAB : pAB = abH + abnH := probSum_pand_split prior (a ∩ b) H
  -- CIP in probSum form
  have hH_ne := ne_of_gt hH_pos
  have hNH_ne := ne_of_gt hNH_pos
  obtain ⟨hcipH, hcipNH⟩ := hcip
  have hcipH' : abH * pH = aH * bH := cip_probSum prior a b H hH_ne hcipH
  have hcipNH' : abnH * pnH = anH * bnH := cip_probSum prior a b nH hNH_ne hcipNH
  -- From CIP + total probability: pAB · pH · pnH = aH·bH·pnH + anH·bnH·pH
  have h_cip_sum : pAB * pH * pnH = aH * bH * pnH + anH * bnH * pH := by
    rw [htotAB]; nlinarith
  -- Contrariness gives the sign of the cross-product
  have hSign : 0 < (pnH * aH - pH * anH) * (pH * bnH - pnH * bH) := by
    rcases hcontr with ⟨hposA, hnegB⟩ | ⟨hnegA, hposB⟩
    · -- posRelevant A → aH·pnH > anH·pH, i.e., pnH·aH - pH·anH > 0
      have hA_cross := posRelevant_cross ctx a hPrior hposA hH_pos hNH_pos
      -- negRelevant B → bH·pnH < bnH·pH, i.e., pH·bnH - pnH·bH > 0
      have hB_cross := negRelevant_cross ctx b hPrior hnegB hH_pos hNH_pos
      nlinarith
    · -- negRelevant A → aH·pnH < anH·pH, i.e., pnH·aH - pH·anH < 0
      have hA_cross := negRelevant_cross ctx a hPrior hnegA hH_pos hNH_pos
      -- posRelevant B → bH·pnH > bnH·pH, i.e., pH·bnH - pnH·bH < 0
      have hB_cross := posRelevant_cross ctx b hPrior hposB hH_pos hNH_pos
      nlinarith
  -- Apply factorization identity
  have hFact := cross_product_factorization aH anH bH bnH pH pnH hNormHP
  -- pA·pB·pH·pnH > pAB·pH·pnH
  have hIneq : pAB * (pH * pnH) < pA * pB * (pH * pnH) := by
    have h1 : pA * pB * (pH * pnH) - (aH * bH * pnH + anH * bnH * pH) > 0 := by
      rw [htotA, htotB]; linarith [hFact, hSign]
    have h2 : pAB * (pH * pnH) = aH * bH * pnH + anH * bnH * pH := by
      have := h_cip_sum; ring_nf; linarith
    linarith
  -- pAB < pA · pB
  have hProd_pos : 0 < pH * pnH := mul_pos hH_pos hNH_pos
  have hKey : pAB < pA * pB := by
    by_contra hle; push_neg at hle
    have : pA * pB * (pH * pnH) ≤ pAB * (pH * pnH) := by
      have := mul_le_mul_of_nonneg_right hle (le_of_lt hProd_pos)
      ring_nf at this ⊢; linarith
    linarith [hIneq]
  -- condProb(B|A) = P(B∧A)/P(A) < P(B) = margProb(B)
  have hA_ne : probSum prior a ≠ 0 := ne_of_gt hA_pos
  show condProb prior b a < margProb prior b
  unfold condProb; dsimp only; rw [if_neg hA_ne]
  unfold margProb
  rw [probSum_pand_comm prior b a]
  exact (div_lt_iff₀ hA_pos).mpr (by nlinarith [hKey])

/-- **Theorem 9**: When H = B, CIP holds automatically for any A.

P(A∧B|B) = P(A|B)·P(B|B) because B∧(A∧B) = A∧B and B∧B = B.
P(A∧B|¬B) = P(A|¬B)·P(B|¬B) because (A∧B)∧¬B = ⊥ and B∧¬B = ⊥. -/
theorem topic_eq_b_satisfies_cip (prior : W → ℚ) (a b : Set W)
    [DecidablePred (· ∈ a)] [DecidablePred (· ∈ b)] :
    CIP (defaultButCtx prior b) a b := by
  constructor
  · -- P(A∧B|B) = P(A|B) · P(B|B)
    show condProb prior (a ∩ b) b =
         condProb prior a b * condProb prior b b
    unfold condProb
    dsimp only
    rw [probSum_pand_assoc_self, probSum_pand_self]
    split
    · simp
    · rename_i h; field_simp
  · -- P(A∧B|¬B) = P(A|¬B) · P(B|¬B)
    show condProb prior (a ∩ b) (bᶜ) =
         condProb prior a (bᶜ) * condProb prior b (bᶜ)
    unfold condProb
    dsimp only
    rw [probSum_pand_pand_pnot_zero, probSum_pand_pnot_zero]
    split
    · simp
    · simp

set_option maxHeartbeats 400000 in
/-- **Theorem 10**: Negative relevance implies unexpectedness in default-but.

When the issue is B itself and A is negatively relevant to H=B,
then P(B|A) < P(B) — B is unexpected given A.

The proof uses Bayes' reciprocity: negative relevance gives
P(A|B)/P(A|¬B) < 1, so P(A∧B)·P(¬B) < P(A∧¬B)·P(B).
By total probability P(A) = P(A∧B) + P(A∧¬B) and normalization
P(B) + P(¬B) = 1, this yields P(A∧B) < P(A)·P(B),
hence P(B|A) = P(A∧B)/P(A) < P(B) = margProb(B).

TODO: This proof currently times out during elaboration of the
`bayesFactor` unfolding step due to `defaultButCtx` field projections
not reducing through `simp only`. Restructure to expose the underlying
`prior`/`topic` equations before invoking `if_neg`/`div_lt_one`. -/
theorem default_but_properties (prior : W → ℚ) (a b : Set W)
    [DecidablePred (· ∈ a)] [DecidablePred (· ∈ b)]
    (hPrior : ∀ w, prior w ≥ 0)
    (hNorm : probSum prior (Set.univ : Set W) = 1)
    (hNegA : negRelevant (defaultButCtx prior b) a)
    (hB_pos : 0 < probSum prior b)
    (hNotB_pos : 0 < probSum prior (bᶜ))
    (hAnB_pos : 0 < probSum prior (a ∩ (bᶜ))) :
    condProb prior b a < margProb prior b := by
  -- TODO: This proof times out during elaboration of the `bayesFactor` unfolding
  -- step due to `defaultButCtx` field projections (`.prior`, `.topic`) not
  -- reducing through `simp only`. Restructure to expose the underlying
  -- `prior`/`topic` equations before invoking `if_neg`/`div_lt_one`.
  -- Proof sketch:
  --   1. Unfold negRelevant + bayesFactor over defaultButCtx to extract
  --      probSum(A∧B)/probSum(B) < probSum(A∧¬B)/probSum(¬B).
  --   2. Cross-multiply with hB_pos, hNotB_pos via div_lt_div_iff₀.
  --   3. Use probSum_pand_split + probSum_add_pnot + hNorm to convert to
  --      probSum(A∧B) < probSum(A) · probSum(B).
  --   4. Conclude condProb(b|a) = probSum(B∧A)/probSum(A) < probSum(B)
  --      via div_lt_iff₀ + probSum_pand_comm.
  sorry

/-- **Corollary 11** (Harris universal): NNIR prevents "Qa but Qb".

Under NNIR, "Q(a) but Q(b)" is never felicitous in the default-but
interpretation. When H = Q(b), the Bayes factor BF_{Q(b)}(Q(b)) is
P(Q(b)|Q(b))/P(Q(b)|¬Q(b)) = 1/0 ≥ 1, so Q(b) cannot be negatively
relevant to itself, violating the butFelicitous requirement. -/
theorem harris_universal {E : Type*} (prior : W → ℚ)
    (Q : E → Set W) [∀ e, DecidablePred (· ∈ Q e)] (a b : E)
    (_hnnir : NNIR E prior Q) :
    ¬ butFelicitous (defaultButCtx prior (Q b)) (Q a) (Q b) := by
  intro ⟨_, hNeg, _⟩
  exact absurd hNeg (not_lt.mpr (bayesFactor_self_ge_one prior (Q b)))

/-! **Theorem 13** (not formalized): Savage-Kemeny-Gaifman-Humburg theorem.

Symmetric probability on finite models extends to infinite models only
if NNIR holds. This provides a foundational justification for NNIR as
a rationality constraint. Not formalized here (requires measure theory
and de Finetti-style exchangeability arguments).

Reference: Gaifman, H. & Snir, M. (1982). Probabilities over rich languages. -/

end Theorems

end DTS.But
