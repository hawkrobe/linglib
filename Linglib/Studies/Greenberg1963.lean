import Linglib.Data.OrderTypology.Greenberg1963

/-!
# Greenberg (1963): Some Universals of Grammar

This file formalizes the implicational universals of order of [greenberg-1963], "Some universals
of grammar with particular reference to the order of meaningful elements", over the paper's own
data: the 30-language sample of Appendix I, extended by the per-language properties the text and
its footnotes record, and the 24 basic order types of Appendix II with the languages listed as
attesting each (`Data.OrderTypology.Greenberg1963`). A universal is a statement that every
language of the sample with one property has another (`Universal`), and the paper's "almost
always" and "with overwhelmingly more than chance frequency" are universals with the exceptions
the paper names (`UniversalExcept`). Over the sample, verb-initial languages are prepositional
and verb-final ones postpositional (`universal_3`, `universal_4`), postpositions go with a
preposed genitive and prepositions with a postposed one (`universal_2`), and the same holds of
the sentence-level question particles, the inflected auxiliaries, the adjective, the
demonstrative and numeral, the adverb and adjective, the comparative construction, apposition,
the relative expression, and affixing (`universal_9` through `universal_27`). Over the attested
order types, the postpositional verb-initial types are empty (`universal_3_types`), the
prepositional verb-final types are Persian's and Amharic's (`universal_4_types`), and no
verb-final type with a postposed genitive has a preposed adjective (`universal_5_types`).

## Implementation notes

The genitive column of the sample follows the text's count, every postpositional language
preposing it and every prepositional one postposing it but Norwegian, which the paper's
additional note then records with both orders. Zapotec and Songhai, whose question particles
follow more than one rule, carry none, as in the paper's Table 2. Universal 23 as printed pairs
proper-noun-first apposition with a postposed genitive; the paper's footnote 19 and its Table 9
totals pair it with a preposed one, as does the text's assimilation of apposition to the
genitive, and `universal_23` states the version the data support.

## References

* [greenberg-1963]

## TODO

Universals 6 to 8, 11, 13 to 15, 19, 20, 25, and 26 and the morphological universals 28 to 45
concern properties the appendices and footnotes do not record per language.
-/

namespace Greenberg1963

open Data.OrderTypology Data.OrderTypology.Greenberg1963

/-! ### Universals over the sample -/

/-- A Greenbergian implicational universal over the sample: every language with `P` has `Q`. -/
def Universal (P Q : SampleRow → Prop) : Prop := ∀ r ∈ sample, P r → Q r

instance (P Q : SampleRow → Prop) [DecidablePred P] [DecidablePred Q] :
    Decidable (Universal P Q) :=
  inferInstanceAs (Decidable (∀ r ∈ sample, P r → Q r))

/-- A universal holding but for the named languages, the paper's "almost always". -/
def UniversalExcept (P Q : SampleRow → Prop) (exceptions : List String) : Prop :=
  ∀ r ∈ sample, P r → Q r ∨ r.language ∈ exceptions

instance (P Q : SampleRow → Prop) (exceptions : List String) [DecidablePred P]
    [DecidablePred Q] : Decidable (UniversalExcept P Q exceptions) :=
  inferInstanceAs (Decidable (∀ r ∈ sample, P r → Q r ∨ r.language ∈ exceptions))

/-- Universal 2: postpositions go with a preposed genitive throughout the sample; no
prepositional language has the genitive preposed alone, Norwegian having both orders. -/
theorem universal_2 :
    Universal (·.adposition = .postpositions) (·.genitive = .dependentFirst) ∧
      Universal (·.adposition = .prepositions) (·.genitive ≠ .dependentFirst) := by
  decide

/-- Universal 3: the verb-initial languages of the sample are prepositional. -/
theorem universal_3 : Universal (·.verbPosition = .initial) (·.adposition = .prepositions) := by
  decide

/-- Universal 4: the verb-final languages of the sample are postpositional. -/
theorem universal_4 : Universal (·.verbPosition = .final) (·.adposition = .postpositions) := by
  decide

/-- Universal 9: a question particle placed at the start of the sentence occurs in a
prepositional language; one placed at its end in a postpositional language, Thai and Yoruba
excepted (Table 2). -/
theorem universal_9 :
    Universal (·.questionParticleSentence = some .initial) (·.adposition = .prepositions) ∧
      UniversalExcept (·.questionParticleSentence = some .final)
        (·.adposition = .postpositions) ["Thai", "Yoruba"] := by
  decide

/-- Universal 10: a question particle placed by reference to a word follows it, Yoruba
excepted, and no verb-initial language has one. -/
theorem universal_10 :
    UniversalExcept (·.questionParticleWord ≠ none) (·.questionParticleWord = some .follows)
        ["Yoruba"] ∧
      Universal (·.questionParticleWord ≠ none) (·.verbPosition ≠ .initial) := by
  decide

/-- Universal 12: verb-initial languages put the interrogative word first, verb-final ones never
do (Table 3). -/
theorem universal_12 :
    Universal (·.verbPosition = .initial) (·.questionWordFirst = true) ∧
      Universal (·.verbPosition = .final) (·.questionWordFirst = false) := by
  decide

/-- Universal 16: an inflected auxiliary precedes the verb in a verb-initial language and
follows it in a verb-final one (Table 4). -/
theorem universal_16 :
    Universal (·.verbPosition = .initial) (·.auxiliary ≠ some .follows) ∧
      Universal (·.verbPosition = .final) (·.auxiliary ≠ some .precedes) := by
  decide

/-- Universal 17: the verb-initial languages of the sample have the adjective after the noun
(Table 5). -/
theorem universal_17 : Universal (·.verbPosition = .initial) (·.adjective = .nounFirst) := by
  decide

/-- Universal 18: when the adjective precedes the noun, so do the demonstrative and the numeral
(Table 6). -/
theorem universal_18 :
    Universal (·.adjective = .dependentFirst)
      (λ r => r.demonstrative = .dependentFirst ∧ r.numeral = .dependentFirst) := by
  decide

/-- Universal 21: where some or all adverbs follow the adjective, the adjective follows the noun
and the verb precedes its object (Table 7). -/
theorem universal_21 :
    Universal (λ r => r.adverbAdjective = some .adjectiveAdverb ∨ r.adverbAdjective = some .both)
      (λ r => r.adjective = .nounFirst ∧ r.verbPosition ≠ .final) := by
  decide

/-- Universal 22: standard-marker-adjective, alone or as an alternative, goes with
postpositions; adjective-marker-standard alone goes with prepositions, Songhai excepted
(Table 8). -/
theorem universal_22 :
    Universal (λ r => r.comparison = some .standardMarkerAdjective ∨ r.comparison = some .both)
        (·.adposition = .postpositions) ∧
      UniversalExcept (·.comparison = some .adjectiveMarkerStandard)
        (·.adposition = .prepositions) ["Songhai"] := by
  decide

/-- Universal 23 as the data have it (footnote 19, Table 9): the proper noun first in
apposition goes with a preposed genitive; the common noun first with a postposed genitive,
Guarani excepted. -/
theorem universal_23 :
    Universal (·.apposition = some .properCommon) (·.genitive ≠ .nounFirst) ∧
      UniversalExcept (·.apposition = some .commonProper) (·.genitive = .nounFirst)
        ["Guarani"] := by
  decide

/-- Universal 24: a relative expression preceding the noun, alone or as an alternative, goes
with postpositions or a preposed adjective (Table 10). -/
theorem universal_24 :
    Universal (λ r => r.relative = some .dependentFirst ∨ r.relative = some .both)
      (λ r => r.adposition = .postpositions ∨ r.adjective = .dependentFirst) := by
  decide

/-- Universal 27: an exclusively suffixing language is postpositional, an exclusively prefixing
one prepositional (Table 11). -/
theorem universal_27 :
    Universal (·.affixing = some .suffixingOnly) (·.adposition = .postpositions) ∧
      Universal (·.affixing = some .prefixingOnly) (·.adposition = .prepositions) := by
  decide

/-! ### Universals over the attested order types of Appendix II -/

/-- The order types the paper lists a language for. -/
def attested : List OrderType := types.filter (·.attested ≠ [])

/-- A universal over the attested types. -/
def TypeUniversal (P Q : OrderType → Prop) : Prop := ∀ t ∈ attested, P t → Q t

instance (P Q : OrderType → Prop) [DecidablePred P] [DecidablePred Q] :
    Decidable (TypeUniversal P Q) :=
  inferInstanceAs (Decidable (∀ t ∈ attested, P t → Q t))

/-- Universal 2 over the types: a prepositional type with a preposed genitive is one of the
paper's 3, 11, 12, and 19; a postpositional type with a postposed genitive is its 14 or 21. -/
theorem universal_2_types :
    TypeUniversal (λ t => t.adposition = .prepositions ∧ t.genitive = .dependentFirst)
        (·.index ∈ [3, 11, 12, 19]) ∧
      TypeUniversal (λ t => t.adposition = .postpositions ∧ t.genitive = .nounFirst)
        (·.index ∈ [14, 21]) := by
  decide

/-- Universal 3 over the types: no postpositional verb-initial type is attested; the paper's
additional note records Papago as the one exception it learned of. -/
theorem universal_3_types :
    TypeUniversal (·.verbPosition = .initial) (·.adposition = .prepositions) := by
  decide

/-- Universal 4 over the types: the prepositional verb-final types are 17, Persian's, and 19,
Amharic's. -/
theorem universal_4_types :
    TypeUniversal (λ t => t.verbPosition = .final ∧ t.adposition = .prepositions)
      (·.index ∈ [17, 19]) := by
  decide

/-- Universal 5: a verb-final type with a postposed genitive has the adjective after the noun,
the types 18 and 22 being empty. -/
theorem universal_5_types :
    TypeUniversal (λ t => t.verbPosition = .final ∧ t.genitive = .nounFirst)
      (·.adjective = .nounFirst) := by
  decide

/-- Universal 17 over the types: the verb-initial types with the adjective before the noun are
2 and 3. -/
theorem universal_17_types :
    TypeUniversal (λ t => t.verbPosition = .initial ∧ t.adjective = .dependentFirst)
      (·.index ∈ [2, 3]) := by
  decide

end Greenberg1963
