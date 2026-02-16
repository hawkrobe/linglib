import Linglib.Theories.Pragmatics.DecisionTheoretic.Core

/-!
# Decision-Theoretic Semantics: "But" (Merin 1999 §4)

Merin's DTS account of adversative conjunction. The felicity of "A but B"
requires that A and B have opposite relevance signs, and that the conjunction
A∧B is negatively relevant (the "but"-clause wins). The default interpretation
sets H = B, yielding unexpected-B-given-A.

## Key Definitions

- `butFelicitous` (Hypothesis 4): felicity conditions for "A but B"
- `NNIR` (Def. 10): Non-Negative Instantial Relevance
- `defaultBut`: the default interpretation where H = B

## Main Results

- **Theorem 8**: CIP + contrariness → unexpectedness (P(B|A) < P(B))
- **Theorem 9**: When H = B, CIP holds automatically
- **Theorem 10**: Properties of default-but interpretation
- **Corollary 11** (Harris universal): NNIR prevents "Qa but Qb"

## References

- Merin, A. (1999). Information, relevance, and social decisionmaking.
  §4: The semantics of "but".
- Harris, Z. (1946). From morpheme to utterance. Language 22.
-/

namespace Theories.DTS.But

open Core.Proposition
open Theories.DTS

-- ============================================================
-- Section 1: Felicity Conditions for "But"
-- ============================================================

/-- **Hypothesis 4**: Felicity conditions for "A but B".

"A but B" is felicitous iff:
(i) A is positively relevant to H,
(ii) B is negatively relevant to H,
(iii) A∧B is negatively relevant to H (B "wins"). -/
def butFelicitous {W : Type*} [Fintype W]
    (ctx : DTSContext W) (a b : BProp W) : Prop :=
  posRelevant ctx a ∧ negRelevant ctx b ∧
  negRelevant ctx (Decidable.pand W a b)

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
    (prior : W → ℚ) (Q : E → BProp W) : Prop :=
  ∀ (a b : E), condProb prior (Q b) (Q a) ≥ margProb prior (Q b)

-- ============================================================
-- Section 3: Default But (H = B)
-- ============================================================

/-- Default "but" interpretation: the issue is identified with the
but-clause itself (H = B).

Merin argues this is the preferred interpretation when no explicit
issue is provided. -/
def defaultBut {W : Type*} (b : BProp W) : Issue W :=
  ⟨b⟩

/-- Context for default-but: issue is B itself. -/
def defaultButCtx {W : Type*} (prior : W → ℚ) (b : BProp W) : DTSContext W :=
  ⟨defaultBut b, prior⟩

-- ============================================================
-- Section 4: Theorems
-- ============================================================

section Theorems

variable {W : Type*} [Fintype W]

-- Helper lemmas for probSum with repeated/contradictory propositions

private lemma probSum_pand_self (prior : W → ℚ) (b : BProp W) :
    probSum prior (Decidable.pand W b b) = probSum prior b := by
  simp [probSum, Decidable.pand, Bool.and_self]

private lemma probSum_pand_assoc_self (prior : W → ℚ) (a b : BProp W) :
    probSum prior (Decidable.pand W (Decidable.pand W a b) b) =
    probSum prior (Decidable.pand W a b) := by
  congr 1; funext w; simp [Decidable.pand, Bool.and_self, Bool.and_assoc]

private lemma probSum_pand_pnot_zero (prior : W → ℚ) (b : BProp W) :
    probSum prior (Decidable.pand W b (Decidable.pnot W b)) = 0 := by
  simp [probSum, Decidable.pand, Decidable.pnot, Bool.and_not_self]

private lemma probSum_pand_pand_pnot_zero (prior : W → ℚ) (a b : BProp W) :
    probSum prior (Decidable.pand W (Decidable.pand W a b) (Decidable.pnot W b)) = 0 := by
  simp only [probSum, Decidable.pand, Decidable.pnot]
  apply Finset.sum_eq_zero
  intro w _
  have : ¬((a w = true ∧ b w = true) ∧ b w = false) := by
    intro ⟨⟨_, hb⟩, hb'⟩; rw [hb] at hb'; exact Bool.noConfusion hb'
  simp [this]

/-- condProb of b given ¬b is always 0: P(B|¬B) = 0. -/
private lemma condProb_self_given_not (prior : W → ℚ) (b : BProp W) :
    condProb prior b (Decidable.pnot W b) = 0 := by
  simp [condProb, probSum_pand_pnot_zero]

/-- BF_B(B) ≥ 1: B is never negatively relevant to itself. -/
private lemma bayesFactor_self_ge_one (prior : W → ℚ) (b : BProp W) :
    bayesFactor (defaultButCtx prior b) b ≥ 1 := by
  simp only [bayesFactor, defaultButCtx, defaultBut, condProb_self_given_not]
  simp; split <;> linarith

/-- **Theorem 8**: CIP + contrariness implies unexpectedness.

If A and B are conditionally independent given H and ¬H, and have
opposite relevance signs, then P(B|A) < P(B) — B is unexpected given A.

Proof sketch: CIP means BF(A∧B) = BF(A)·BF(B). Contrariness means
BF(A)>1 and BF(B)<1 (or vice versa). By Bayes' theorem, the shift in
conditional probability is determined by the Bayes factor product. -/
theorem cip_contrariness_implies_unexpectedness (ctx : DTSContext W)
    (a b : BProp W)
    (hcip : CIP ctx a b)
    (hcontr : hContrary ctx a b) :
    condProb ctx.prior b a < margProb ctx.prior b := by
  -- TODO: Requires Bayes' theorem relating condProb to margProb
  -- through the Bayes factor, then using CIP multiplicativity
  -- and contrariness to establish the direction of the inequality.
  sorry

/-- **Theorem 9**: When H = B, CIP holds automatically for any A.

P(A∧B|B) = P(A|B)·P(B|B) because B∧(A∧B) = A∧B and B∧B = B.
P(A∧B|¬B) = P(A|¬B)·P(B|¬B) because (A∧B)∧¬B = ⊥ and B∧¬B = ⊥. -/
theorem topic_eq_b_satisfies_cip (prior : W → ℚ) (a b : BProp W) :
    CIP (defaultButCtx prior b) a b := by
  constructor
  · -- P(A∧B|B) = P(A|B) · P(B|B)
    simp only [defaultButCtx, defaultBut, condProb]
    rw [probSum_pand_assoc_self, probSum_pand_self]
    split
    · simp
    · rename_i h; field_simp
  · -- P(A∧B|¬B) = P(A|¬B) · P(B|¬B)
    simp only [defaultButCtx, defaultBut, condProb]
    rw [probSum_pand_pand_pnot_zero, probSum_pand_pnot_zero]
    split
    · simp
    · simp

/-- **Theorem 10**: Negative relevance implies unexpectedness in default-but.

When the issue is B itself and A is negatively relevant to H=B,
then P(B|A) < P(B) — B is unexpected given A. By Bayes' rule:
  P(B|A) < P(B) ↔ P(A|B) < P(A) ↔ P(A|B) < P(A|¬B)
and negative relevance gives exactly P(A|B) < P(A|¬B).

Note: the original version used `posRelevant`, but positive relevance
(P(A|B) > P(A|¬B)) implies P(B|A) > P(B) — the opposite of
unexpectedness. In "A but B", A must make B *less* likely. -/
theorem default_but_properties (prior : W → ℚ) (a b : BProp W)
    (hNegA : negRelevant (defaultButCtx prior b) a)
    (hNondegen : 0 < condProb prior (Decidable.pand W a b) (Decidable.top W)) :
    condProb prior b a < margProb prior b := by
  -- negRelevant means P(A|B)/P(A|¬B) < 1, i.e., P(A|B) < P(A|¬B).
  -- By Bayes: P(B|A) = P(A|B)·P(B)/P(A), and P(B|A) < P(B) ↔ P(A|B) < P(A).
  sorry

/-- **Corollary 11** (Harris universal): NNIR prevents "Qa but Qb".

Under NNIR, "Q(a) but Q(b)" is never felicitous in the default-but
interpretation. When H = Q(b), the Bayes factor BF_{Q(b)}(Q(b)) is
P(Q(b)|Q(b))/P(Q(b)|¬Q(b)) = 1/0 ≥ 1, so Q(b) cannot be negatively
relevant to itself, violating the butFelicitous requirement. -/
theorem harris_universal {E : Type*} (prior : W → ℚ)
    (Q : E → BProp W) (a b : E)
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

end Theories.DTS.But
