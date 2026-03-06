import Linglib.Core.Lexical.Binominal
import Linglib.Theories.Semantics.Lexical.Noun.GradableNouns
import Linglib.Theories.Semantics.Probabilistic.Measurement.Basic

/-!
# Binominal Noun Phrase Semantics

Cross-linguistic semantic composition rules for binominal (N₁-of-N₂)
constructions, connecting the taxonomy in `Core.Lexical.Binominal` to
the semantic theories for gradable nouns and quantizing nouns.

## Evaluative BNP Semantics

Evaluative BNPs (*that idiot of a doctor*) compose N₁ as a gradable
predicate with N₂ as a restricting predicate (@cite{ten-wolde-2023},
@cite{morzycki-2009}). The denotation is conjunctive: x must satisfy
both N₂ (be a doctor) and POS(N₁) (be d-idiotic for d ≥ θ).

## Quantizing ↔ Pseudo-partitive Bridge

All quantizing noun classes (@cite{scontras-2014}) — container nouns,
atomizers, and measure terms — instantiate pseudo-partitive binominals
in @cite{ten-wolde-2023}'s taxonomy.
-/

namespace Semantics.Lexical.Noun.Binominal

open Core.Lexical.Binominal
open Semantics.Lexical.Noun.GradableNouns (GradableNoun)
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

open Semantics.Lexical.Noun.GradableNouns (exampleIdiot Person)

/-- A doctor predicate for the worked example. -/
def isDoctor : Person → Bool
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

end Semantics.Lexical.Noun.Binominal
