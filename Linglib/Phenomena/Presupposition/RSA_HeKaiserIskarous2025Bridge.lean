import Linglib.Phenomena.Presupposition.Studies.HeKaiserIskarous2025
import Linglib.Core.Proposition
import Linglib.Theories.Semantics.Montague.Basic
import Linglib.Theories.Semantics.Entailment.Polarity

/-!
# Bridge: RSA Polarity Asymmetry Models → Phenomena Data

Connects the RSA polarity asymmetry models for He, Kaiser & Iskarous (2025)
to empirical data in `Phenomena.Presupposition.Studies.HeKaiserIskarous2025`.

The RSA model code that was here (standardL1, fuzzyRSA, wonkyRSA, funkyRSA)
has been removed pending migration to the new RSA infrastructure.

## Compositional Grounding (Preserved)

The compositional grounding section is retained: it derives sentence
meanings, polarity, and cost from Montague semantics and structural
complexity, independent of the RSA evaluation machinery.

## Reference

He, M., Kaiser, E., & Iskarous, K. (2025). "Modeling sentence polarity asymmetries:
Fuzzy interpretations in a possibly wonky world". SCiL 2025.
-/


namespace Phenomena.Presupposition.HeKaiserIskarous2025Bridge

open Phenomena.Presupposition.Studies.HeKaiserIskarous2025


/-- Simple sigmoid approximation using rational arithmetic.

    sigmoid(x; L, k, x0, c) = L / (1 + exp(-k(x - x0))) + c

    Since we can't easily compute exp with rationals, we use a
    piecewise linear approximation:
    - For x < x0 - 1/k: returns c (low plateau)
    - For x > x0 + 1/k: returns L + c (high plateau)
    - Otherwise: linear interpolation

    This captures the key sigmoid behavior for our purposes. -/
def sigmoidApprox (x : ℚ) (L k x0 c : ℚ) : ℚ :=
  let threshold := if k > 0 then 1 / k else 1/10
  if x < x0 - threshold then
    c
  else if x > x0 + threshold then
    L + c
  else
    -- Linear interpolation in the middle region
    let slope := L / (2 * threshold)
    let midpoint := c + L / 2
    midpoint + slope * (x - x0)


/-- Fuzzy interpretation for negative utterances.

    [[u_neg]](s_neg) = n (constant)
    [[u_neg]](s_pos) = 1 - n

    This reflects that negation "inherently" presupposes its positive
    counterpart, regardless of the specific state prior. -/
def fuzzyNegInterpretation (n : ℚ) : HKIState → ℚ
  | .neg => n
  | .pos => 1 - n

/-- Fuzzy interpretation for positive utterances.

    [[u_pos]](s_pos) = sigmoid(P(s_pos); L, k, x0, c)
    [[u_pos]](s_neg) = 1 - [[u_pos]](s_pos)

    The sigmoid captures that positive utterances about low-prior states
    are less likely to be interpreted as intended. -/
def fuzzyPosInterpretation (p_pos : ℚ) (params : FuzzyParams) : HKIState → ℚ :=
  let sig := sigmoidApprox p_pos params.L params.k params.x0 params.c
  λ s => match s with
    | .pos => sig
    | .neg => 1 - sig

/-- Fuzzy interpretation for null utterance (no information). -/
def fuzzyNullInterpretation : HKIState → ℚ
  | _ => 1  -- Uniform / no constraint

/-- Combined fuzzy meaning function for fuzzyRSA.

    Maps (utterance, state) → [0, 1] based on polarity-specific functions. -/
def fuzzyMeaning (cfg : HKIConfig) (u : HKIUtterance) (s : HKIState) : ℚ :=
  match u with
  | .uNeg => fuzzyNegInterpretation cfg.fuzzyParams.n s
  | .uPos => fuzzyPosInterpretation cfg.prior.p_pos cfg.fuzzyParams s
  | .uNull => fuzzyNullInterpretation s


/-- World-conditioned prior for wonkyRSA.

    In wonky world: uniform prior (all states equally likely)
    In normal world: empirical prior -/
def worldConditionedPrior (cfg : HKIConfig) : WorldType → HKIState → ℚ
  | .wonky, _ => 1/2  -- Uniform in wonky world
  | .normal, s => cfg.prior.prob s

/-- Goal projection for wonkyRSA.

    In normal world: full partition (distinguish states)
    In wonky world: states are still distinguished -/
def wonkyGoalProject : WorldType → HKIState → HKIState → Bool
  | _, s1, s2 => s1 == s2


/-- Standard scenario has correct dimensions -/
theorem standard_dimensions :
    allUtterances.length = 3 ∧
    allStates.length = 2 :=
  ⟨rfl, rfl⟩

/-- wonkyRSA has 2 goals (normal, wonky) -/
theorem wonky_dimensions :
    allWorldTypes.length = 2 :=
  rfl

/-- Negative utterances have higher cost in our model -/
theorem neg_higher_cost :
    utteranceCost .uNeg > utteranceCost .uPos := by
  native_decide

/-- fuzzyRSA with low prior: positive utterance becomes less reliable.

    The sigmoid interpretation means that for low-prior positive states,
    the positive utterance is less likely to be interpreted as intended. -/
theorem fuzzy_low_prior_effect :
    fuzzyMeaning lowPriorConfig .uPos .pos <
    fuzzyMeaning highPriorConfig .uPos .pos := by
  native_decide

/-- Negative interpretation is constant regardless of prior.

    This reflects the "inherent" presupposition trigger of negation. -/
theorem neg_interpretation_constant :
    fuzzyMeaning lowPriorConfig .uNeg .neg =
    fuzzyMeaning highPriorConfig .uNeg .neg :=
  rfl

/--
Map He et al.'s sentence polarity to compositional context polarity.

This bridges the two notions:
- Sentence polarity: positive vs negative utterances
- Context polarity: upward vs downward entailing

Negative sentences contain negation → DE context.
-/
def toContextPolarity : Polarity → Semantics.Entailment.Polarity.ContextPolarity
  | .positive => .upward
  | .negative => .downward
  | .null => .upward

/-- Cost aligns with UE/DE distinction: DE costs more -/
theorem cost_reflects_polarity :
    utteranceCost .uPos < utteranceCost .uNeg := by
  native_decide


/-
## Compositional Analysis of He et al. Sentences

The He et al. sentences have the form:
- Positive: "A has B" (e.g., "The house has a bathroom")
- Negative: "A doesn't have B" (e.g., "The house doesn't have a bathroom")

Compositionally:
- ⟦uPos⟧ = has(A, B)
- ⟦uNeg⟧ = neg(has(A, B))

where `neg` is Montague's sentence-level negation operator.
-/

section CompositionalGrounding

open Semantics.Montague

/--
A simple model for part-whole relations.

Entities: containers (houses, classrooms) and parts (bathrooms, stoves)
-/
inductive PWEntity where
  | house | classroom | bathroom | stove
  deriving DecidableEq, BEq, Repr

/-- Part-whole model -/
def pwModel : Model where
  Entity := PWEntity
  decEq := inferInstance

/--
The "has" relation: which containers have which parts.

Typical: house-bathroom (most houses have bathrooms)
Atypical: classroom-stove (most classrooms don't have stoves)
-/
def has_sem : pwModel.interpTy (.e ⇒ .e ⇒ .t) :=
  λ part container => match container, part with
    | .house, .bathroom => true   -- Houses typically have bathrooms
    | .classroom, .stove => false -- Classrooms typically don't have stoves
    | _, _ => false

/-- Positive sentence meaning: "A has B" -/
def posMeaning (container part : PWEntity) : pwModel.interpTy .t :=
  interpSVO pwModel container has_sem part

/-- Negative sentence meaning: "A doesn't have B" = neg(has(A, B)) -/
def negMeaning (container part : PWEntity) : pwModel.interpTy .t :=
  neg (posMeaning container part)

/-- Key theorem: negative meaning is compositionally derived via `neg` -/
theorem neg_is_compositional (container part : PWEntity) :
    negMeaning container part = neg (posMeaning container part) := rfl

/-- "The house has a bathroom" is true -/
theorem house_has_bathroom : posMeaning .house .bathroom = true := rfl

/-- "The house doesn't have a bathroom" is false -/
theorem house_doesnt_have_bathroom : negMeaning .house .bathroom = false := rfl

/-- "The classroom doesn't have a stove" is true -/
theorem classroom_doesnt_have_stove : negMeaning .classroom .stove = true := rfl

-- Connecting to Polarity Machinery (with proven DE property)

open Semantics.Entailment.Polarity
open Core.Proposition

/--
Lift He et al. sentences to world-indexed propositions.

Uses `Core.Proposition.BProp HKIState = HKIState → Bool`.
-/
def liftToWorlds (s : HKIState) : BProp HKIState :=
  λ w => w == s

/--
Negative sentence meaning as world-indexed proposition.

⟦"A doesn't have B"⟧ = pnot(⟦"A has B"⟧)

Uses `Core.Proposition.Decidable.pnot` for the negation.
-/
def negMeaningW : BProp HKIState :=
  Decidable.pnot HKIState (liftToWorlds .pos)

/--
Key theorem: Negation reverses entailment (DE property).

Inherited from `Core.Proposition.Decidable.pnot_reverses_entailment`.
This is the centralized proof that negation is Downward Entailing.
-/
theorem pnot_reverses_entailment_HKI (p q : BProp HKIState)
    (h : ∀ w, p w = true → q w = true) :
    ∀ w, Decidable.pnot HKIState q w = true → Decidable.pnot HKIState p w = true :=
  Decidable.pnot_reverses_entailment p q h

/--
The grounded polarity from Entailment.Polarity (uses `pnot`)
-/
def negSentencePolarity : GroundedPolarity := negationPolarity

/-- Negative sentences have DE polarity (from Montague's proof) -/
theorem neg_sentence_is_de :
    negSentencePolarity.toContextPolarity = .downward := rfl

/-- Positive sentences have UE polarity (identity = no negation) -/
theorem pos_sentence_is_ue :
    identityPolarity.toContextPolarity = .upward := rfl

-- Deriving Cost from Structural Complexity

/--
Structural complexity: count of functional heads in the derivation.

- Positive "A has B": just the predication (complexity 1)
- Negative "A doesn't have B": predication + negation head (complexity 2)
-/
def structuralComplexity : HKIUtterance → ℕ
  | .uNull => 0  -- Silence: no structure
  | .uPos => 1   -- Positive: just predication
  | .uNeg => 2   -- Negative: predication + Neg head

/--
Key theorem: utterance cost equals structural complexity.

This derives the stipulated cost function from compositional structure.
-/
theorem cost_from_structure :
    ∀ u : HKIUtterance, utteranceCost u = structuralComplexity u := by
  intro u
  cases u <;> rfl

/--
Negation adds exactly one unit of complexity (the Neg functional head).
-/
theorem negation_adds_one_head :
    structuralComplexity .uNeg = structuralComplexity .uPos + 1 := rfl

end CompositionalGrounding

/-
## Summary: Compositional Grounding

The He et al. model is now grounded in Montague semantics:

1. **Sentence meanings** are compositionally derived:
   - ⟦uPos⟧ = has(A, B)
   - ⟦uNeg⟧ = neg(has(A, B))

2. **Polarity** comes from Montague's proven machinery:
   - `negationPolarity` proves `neg` is DE
   - `identityPolarity` proves positive is UE

3. **Cost** is derived from structural complexity:
   - Negation adds a functional head (Neg)
   - Each head adds 1 to cost

This connects the RSA pragmatic model to compositional formal semantics.
-/

end Phenomena.Presupposition.HeKaiserIskarous2025Bridge
