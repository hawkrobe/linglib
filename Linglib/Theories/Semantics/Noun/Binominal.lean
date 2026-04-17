import Linglib.Core.Lexical.Binominal
import Linglib.Theories.Semantics.Noun.GradableNouns
import Linglib.Theories.Semantics.Probabilistic.Measurement.Basic
import Linglib.Theories.Semantics.Gradability.Intensification

/-!
# Binominal Noun Phrase Semantics

Cross-linguistic semantic composition rules for binominal (N₁-of-N₂)
constructions, connecting the taxonomy in `Core.Lexical.Binominal` to
the semantic theories for gradable nouns and quantizing nouns.

## Evaluative BNP Semantics (Stage 4)

Evaluative BNPs (*that idiot of a doctor*) compose N₁ as a gradable
predicate with N₂ as a restricting predicate (@cite{ten-wolde-2023},
@cite{morzycki-2009}). The denotation is conjunctive: x must satisfy
both N₂ (be a doctor) and POS(N₁) (be d-idiotic for d ≥ θ).

## Evaluative Modifier Semantics (Stage 5)

EMs (*a hell of a game*) bleach N₁ to an evaluative modifier:
N₁ no longer contributes its own lexical predicate but applies an
evaluative measure function (@cite{nouwen-2024}) to a contextually-
determined property of N₂.

## Binominal Intensifier Semantics (Stage 6)

BIs (*a hell of a good time*) bleach N₁ further to a degree word:
[N₁ of a] intensifies a following adjective, composing via
`intensifiedMeaning` from @cite{nouwen-2024}.

## Quantizing ↔ Pseudo-partitive Bridge

All quantizing noun classes (@cite{scontras-2014}) — container nouns,
atomizers, and measure terms — instantiate pseudo-partitive binominals
in @cite{ten-wolde-2023}'s taxonomy.
-/

namespace Semantics.Noun.Binominal

open Core.Lexical.Binominal
open Semantics.Noun.GradableNouns (GradableNoun)
open Semantics.Probabilistic.Measurement (QuantizingNounClass)

-- ═══════════════════════════════════════════════════════════════
-- § 1: Evaluative BNP Semantics
-- ═══════════════════════════════════════════════════════════════

/-- Evaluative BNP semantics: N₁ ascribes a gradable property to N₂.

"that idiot of a doctor" = the doctor x such that idiot(x) ≥ θ_idiot.
This is precisely `GradableNoun.pos` applied to N₂, where N₁ provides
the measure function and contextual standard.

This composition rule applies cross-linguistically: English *of*,
French *de*, Italian *di*, Dutch *van* evaluative BNPs all have the
same truth conditions. -/
def ebnpSemantics {Entity : Type} (n₁ : GradableNoun Entity) (n₂ : Entity → Bool)
    : Entity → Bool :=
  λ x => n₂ x && n₁.pos x

/-- Evaluative BNPs are conjunctive: the referent must satisfy both
    N₂ (doctor) and N₁'s positive form (idiot above threshold). -/
theorem ebnp_requires_n₂ {Entity : Type} (n₁ : GradableNoun Entity)
    (n₂ : Entity → Bool) (x : Entity) :
    ebnpSemantics n₁ n₂ x = true → n₂ x = true := by
  simp only [ebnpSemantics]
  exact (Bool.and_eq_true_iff.mp · |>.1)

/-- Evaluative BNPs entail N₁'s positive form. -/
theorem ebnp_requires_n₁_pos {Entity : Type} (n₁ : GradableNoun Entity)
    (n₂ : Entity → Bool) (x : Entity) :
    ebnpSemantics n₁ n₂ x = true → n₁.pos x = true := by
  simp only [ebnpSemantics]
  exact (Bool.and_eq_true_iff.mp · |>.2)

-- ═══════════════════════════════════════════════════════════════
-- § 2: Quantizing → Pseudo-partitive Bridge
-- ═══════════════════════════════════════════════════════════════

/-- Map a `QuantizingNounClass` to the `OfBinominalType` it instantiates.

All quantizing nouns (@cite{scontras-2014}) are pseudo-partitive
in @cite{ten-wolde-2023}'s taxonomy: N₁ quantizes, N₂ is the
semantic head. -/
def quantizingToOfBinominal : QuantizingNounClass → OfBinominalType
  | .containerNoun => .pseudoPartitive
  | .atomizer      => .pseudoPartitive
  | .measureTerm   => .pseudoPartitive

/-- Every quantizing noun class maps to pseudo-partitive. -/
theorem all_quantizing_are_pseudopartitive (c : QuantizingNounClass) :
    quantizingToOfBinominal c = .pseudoPartitive := by
  cases c <;> rfl

/-- Pseudo-partitive is N₂-headed, consistent with the quantizing
    noun semantics where N₂ denotes the measured stuff. -/
theorem quantizing_n₂_headed (c : QuantizingNounClass) :
    (quantizingToOfBinominal c).head = .n₂ := by
  cases c <;> rfl

-- ═══════════════════════════════════════════════════════════════
-- § 3: End-to-End Worked Example
-- ═══════════════════════════════════════════════════════════════

/-! ### "That idiot of a doctor"

End-to-end chain: lexical entry → gradable noun theory → EBNP
composition → concrete truth conditions.

Using the `Person` type and `exampleIdiot` from `GradableNouns`:
- George: idiocy degree 8 (above standard 3 → idiot)
- Sarah: idiocy degree 4 (above standard 3 → idiot)
- Floyd: idiocy degree 1 (below standard 3 → not an idiot)
-/

open Semantics.Noun.GradableNouns (exampleIdiot)

/-- A doctor predicate for the worked example. -/
def isDoctor : GradableNouns.Person → Bool
  | .george => true
  | .sarah  => true
  | .floyd  => false

/-- George is "that idiot of a doctor": he is a doctor (true) and
    his idiocy degree (8) exceeds the standard (3). -/
theorem george_is_idiot_doctor :
    ebnpSemantics exampleIdiot isDoctor .george = true := by native_decide

/-- Sarah is also "an idiot of a doctor": doctor (true), idiocy 4 ≥ 3. -/
theorem sarah_is_idiot_doctor :
    ebnpSemantics exampleIdiot isDoctor .sarah = true := by native_decide

/-- Floyd is not "an idiot of a doctor": he is not a doctor. -/
theorem floyd_not_idiot_doctor :
    ebnpSemantics exampleIdiot isDoctor .floyd = false := by native_decide

/-- George would be an idiot even if he weren't a doctor — the
    gradable noun threshold is independent of the N₂ restriction.
    This confirms that ebnpSemantics is genuinely conjunctive. -/
theorem george_idiot_independent :
    exampleIdiot.pos .george = true := by native_decide

-- ═══════════════════════════════════════════════════════════════
-- § 4: Evaluative Modifier (EM) Semantics
-- ═══════════════════════════════════════════════════════════════

/-! ### Stage 5: Evaluative Modifier

At stage 5 on @cite{ten-wolde-2023}'s grammaticalization cline, N₁ has
bleached from a full gradable predicate (EBNP) to an evaluative modifier:
*a hell of a game* ≈ *an extremely good game*. N₁ no longer contributes
its own lexical predicate — instead, [N₁ of a] applies an evaluative
measure function (@cite{nouwen-2024}) to a contextually-determined
property of N₂. -/

section EM
open Semantics.Gradability.Intensification (EvaluativeMeasure intensifiedMeaning)
open Core.Scale (Degree Threshold Degree.toNat Threshold.toNat)

/-- EM semantics: N₁ as evaluative modifier of a contextual property of N₂.

"a hell of a game" = the game x such that the contextually-salient
property of x (e.g., quality) exceeds the evaluative threshold set by N₁.

Unlike EBNP, N₁ does not contribute its own lexical predicate — it has
bleached to a pure evaluative function. The `contextualDegree` parameter
represents the pragmatically-determined property being evaluated. -/
def emSemantics {Entity : Type} {max : Nat}
    (eval : EvaluativeMeasure max)
    (contextualDegree : Entity → Degree max)
    (θ_eval : Threshold max)
    (n₂ : Entity → Bool) : Entity → Bool :=
  λ x => n₂ x && (eval.mu (contextualDegree x).toNat > θ_eval.toNat)

/-- EM preserves the N₂ restriction. -/
theorem em_requires_n₂ {Entity : Type} {max : Nat}
    (eval : EvaluativeMeasure max) (cdeg : Entity → Degree max)
    (θ : Threshold max) (n₂ : Entity → Bool) (x : Entity) :
    emSemantics eval cdeg θ n₂ x = true → n₂ x = true := by
  simp only [emSemantics]
  exact (Bool.and_eq_true_iff.mp · |>.1)

-- ═══════════════════════════════════════════════════════════════
-- § 5: Binominal Intensifier (BI) Semantics
-- ═══════════════════════════════════════════════════════════════

/-! ### Stage 6: Binominal Intensifier

At stage 6, N₁ has fully grammaticalized to a degree word: *a hell of a
good time* ≈ *a very good time*. The [N₁ of a] unit modifies a following
adjective rather than N₂ directly. Semantics composes via
`intensifiedMeaning` from @cite{nouwen-2024}: the adjective's positive
form AND N₁'s evaluative threshold must both be exceeded. -/

/-- BI semantics: N₁ as degree intensifier of a following adjective.

"a hell of a good time" = the time x such that good(x) is intensified:
both the adjective threshold (good enough) and the evaluative threshold
(hell-level) are exceeded.

This directly instantiates @cite{nouwen-2024}'s `intensifiedMeaning`:
the adjective's positive form AND the evaluative measure must both hold. -/
def biSemantics {Entity : Type} {max : Nat}
    (eval : EvaluativeMeasure max)
    (adjDegree : Entity → Degree max)
    (θ_adj θ_eval : Threshold max)
    (n₂ : Entity → Bool) : Entity → Bool :=
  λ x => n₂ x && intensifiedMeaning eval (adjDegree x) θ_adj θ_eval

/-- BI preserves the N₂ restriction. -/
theorem bi_requires_n₂ {Entity : Type} {max : Nat}
    (eval : EvaluativeMeasure max) (adjDeg : Entity → Degree max)
    (θ_adj θ_eval : Threshold max) (n₂ : Entity → Bool) (x : Entity) :
    biSemantics eval adjDeg θ_adj θ_eval n₂ x = true → n₂ x = true := by
  simp only [biSemantics]
  exact (Bool.and_eq_true_iff.mp · |>.1)

/-- BI entails EM when the adjective degree is the contextual property.

This formalizes the grammaticalization claim: BI is a special case of EM
where the contextual property is fixed to a specific adjective, and an
additional threshold (the adjective's standard) is imposed. BI strengthens
EM by adding the adjective's positive form as a conjunct. -/
theorem bi_entails_em {Entity : Type} {max : Nat}
    (eval : EvaluativeMeasure max) (adjDeg : Entity → Degree max)
    (θ_adj θ_eval : Threshold max) (n₂ : Entity → Bool) (x : Entity) :
    biSemantics eval adjDeg θ_adj θ_eval n₂ x = true →
    emSemantics eval adjDeg θ_eval n₂ x = true := by
  simp only [biSemantics, emSemantics, intensifiedMeaning]
  intro h
  have ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp h
  have ⟨_, h₃⟩ := Bool.and_eq_true_iff.mp h₂
  exact Bool.and_eq_true_iff.mpr ⟨h₁, h₃⟩

end EM

-- ═══════════════════════════════════════════════════════════════
-- § 6: EM / BI Worked Example
-- ═══════════════════════════════════════════════════════════════

/-! ### "A hell of a doctor" / "A hell of a good doctor"

Extends the §3 worked example (Person, isDoctor) with EM and BI:
- George: quality 9 → extreme enough for "hell" → EM and BI ✓
- Sarah: quality 6 → good but not extreme → EM and BI ✗
- Floyd: not a doctor → EM and BI ✗

Uses `muHorrible 10` as the evaluative measure for *hell*:
μ_hell(d) = |d − 5|, peaking at extreme degrees. -/

section EMBIExample
open Semantics.Gradability.Intensification (muHorrible EvaluativeMeasure)
open Core.Scale (Degree deg thr)

/-- Quality measure for EM: contextually-determined goodness as a doctor.
George (9) is an outstanding doctor; Sarah (6) is decent; Floyd (3) is poor. -/
def doctorQuality : GradableNouns.Person → Degree 10
  | .george => deg 9
  | .sarah  => deg 6
  | .floyd  => deg 3

/-- Evaluative measure for *hell*: peaks at extreme degrees.
μ_hell(d) = |d − 5| — uses @cite{nouwen-2024}'s extreme-peaking profile.
*hell* is valence-neutral (positive in *a hell of a good time*, negative in
*the hell of war*); the extreme-peaking shape captures its intensity
regardless of polarity. -/
def hellEval : EvaluativeMeasure 10 := muHorrible 10

/-- George is "a hell of a doctor": doctor ✓, quality (9) yields
μ_hell(9) = |9−5| = 4 > 3 = θ_eval ✓. -/
theorem george_hell_of_doctor :
    emSemantics hellEval doctorQuality (thr 3) isDoctor .george = true := by
  native_decide

/-- Sarah is not "a hell of a doctor": quality (6) yields
μ_hell(6) = |6−5| = 1, not > 3. -/
theorem sarah_not_hell_of_doctor :
    emSemantics hellEval doctorQuality (thr 3) isDoctor .sarah = false := by
  native_decide

/-- George is "a hell of a good doctor": good(9 > 5) ✓ AND
μ_hell(9) = 4 > 3 ✓. BI compounds both thresholds. -/
theorem george_hell_of_good_doctor :
    biSemantics hellEval doctorQuality (thr 5) (thr 3) isDoctor .george = true := by
  native_decide

/-- Sarah is not "a hell of a good doctor": good(6 > 5) ✓ but
μ_hell(6) = 1, not > 3. She's good, but not hell-level good. -/
theorem sarah_not_hell_of_good_doctor :
    biSemantics hellEval doctorQuality (thr 5) (thr 3) isDoctor .sarah = false := by
  native_decide

/-- BI → EM entailment holds in the worked example:
George's BI truth entails his EM truth (by `bi_entails_em`). -/
theorem george_bi_entails_em :
    emSemantics hellEval doctorQuality (thr 3) isDoctor .george = true :=
  bi_entails_em hellEval doctorQuality (thr 5) (thr 3) isDoctor .george
    (by native_decide)

end EMBIExample

-- ═══════════════════════════════════════════════════════════════
-- § 7: EBNP ≠ EM — Categorical Independence
-- ═══════════════════════════════════════════════════════════════

/-! ### EBNP and EM are categorically independent

EBNP uses N₁'s own gradable predicate (`GradableNoun.pos`); EM uses
a bleached evaluative measure function (`EvaluativeMeasure`). These are
different semantic types, so neither entails the other in general.

The worked example witnesses both directions of independence:
- Sarah is an EBNP idiot-doctor (idiocy 4 ≥ 3) but NOT an EM hell-of-a-doctor
  (μ_hell(6) = 1, not > 3).
- A non-idiot who happens to be extreme on a contextual quality dimension
  would be EM but not EBNP (not witnessed in the small example, but the
  Sarah case already shows ¬(EBNP → EM)). -/

/-- EBNP does not entail EM: Sarah satisfies `ebnpSemantics` (she is an
    idiot-doctor) but fails `emSemantics` (she is not a hell-of-a-doctor). -/
theorem ebnp_not_entails_em :
    ebnpSemantics exampleIdiot isDoctor .sarah = true ∧
    emSemantics hellEval doctorQuality (Core.Scale.thr 3) isDoctor .sarah = false := by
  constructor <;> native_decide

end Semantics.Noun.Binominal
