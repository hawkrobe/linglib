import Linglib.Phenomena.AuxiliaryVerbs.Typology

/-!
# Negative Auxiliaries (Anderson 2006 §1.7.2)

Some languages express sentential negation through a **negative auxiliary verb**
that hosts inflection (tense, agreement) while the lexical verb appears in a
nonfinite form. This is a special case of the aux-headed AVC pattern.

## Cross-linguistic strategies

| Strategy | Structure | Example |
|----------|-----------|---------|
| NegVerb | Inflected neg aux + nonfinite LV | Finnish *ei mene* 'NEG.3SG go' |
| NegAffix | Bound negative morpheme | Kwerba *or-* prefix |
| NegParticle | Free negative particle | English *not*, Tswana *ga/se* |

The neg-verb strategy is particularly interesting because the negative element
is itself an auxiliary verb, creating an AVC with the negative verb as
inflectional head.

## References

- Anderson, G. D. S. (2006). Auxiliary Verb Constructions. OUP. §1.7.2.
- Miestamo, M. (2005). Standard Negation: The Negation of Declarative Verbal
  Main Clauses in a Typological Perspective. Mouton de Gruyter.
-/

namespace Phenomena.AuxiliaryVerbs.NegativeAuxiliaries

open Phenomena.AuxiliaryVerbs.Typology (InflPattern)

/-! ## Types -/

/-- Strategy for expressing sentential negation. -/
inductive NegStrategy where
  /-- Negative auxiliary verb that inflects (Finnish *ei*, Komi *oz*). -/
  | negVerb
  /-- Bound negative morpheme (Kwerba *or-* prefix). -/
  | negAffix
  /-- Free negative particle (English *not*, Tswana *ga*). -/
  | negParticle
  deriving DecidableEq, Repr, BEq

/-! ## Functions -/

/-- A negative verb creates an AVC and therefore has an expected inflectional
    pattern: aux-headed (the neg verb hosts inflection). Affixes and particles
    do not create AVCs. -/
def NegStrategy.expectedInflPattern : NegStrategy → Option InflPattern
  | .negVerb    => some .auxHeaded
  | .negAffix   => none
  | .negParticle => none

/-- Is this strategy verbal (i.e., does it create an AVC)? -/
def NegStrategy.isVerbal : NegStrategy → Bool
  | .negVerb  => true
  | _         => false

/-! ## Data -/

/-- A negative auxiliary datum. -/
structure NegAuxDatum where
  language : String
  strategy : NegStrategy
  form : String
  gloss : String := ""
  deriving Repr, BEq

/-- Finnish *ei* — negative auxiliary verb (inflects for person/number). -/
def finnish : NegAuxDatum :=
  { language := "Finnish"
  , strategy := .negVerb
  , form := "ei"
  , gloss := "e-n mene 'NEG-1SG go' (I don't go)" }

/-- Komi *oz* — negative auxiliary verb. -/
def komi : NegAuxDatum :=
  { language := "Komi"
  , strategy := .negVerb
  , form := "oz"
  , gloss := "oz mun 'NEG go'" }

/-- Udihe *e-si* — negative auxiliary verb (past tense on neg aux). -/
def udihe : NegAuxDatum :=
  { language := "Udihe"
  , strategy := .negVerb
  , form := "e-si"
  , gloss := "e-si ŋene 'NEG-PST go' (didn't go)" }

/-- Kwerba *or-* — negative affix (prefix on verb). -/
def kwerba : NegAuxDatum :=
  { language := "Kwerba"
  , strategy := .negAffix
  , form := "or-"
  , gloss := "or-war 'NEG-go'" }

/-- Tswana *ga/se* — negative affixes (preverbal bound morphemes). -/
def tswana : NegAuxDatum :=
  { language := "Tswana"
  , strategy := .negAffix
  , form := "ga/se"
  , gloss := "ga ke tsamae 'NEG 1SG go'" }

/-- English *not* — negative particle (does not create an AVC). -/
def englishNot : NegAuxDatum :=
  { language := "English"
  , strategy := .negParticle
  , form := "not"
  , gloss := "does not go" }

def allData : List NegAuxDatum :=
  [finnish, komi, udihe, kwerba, tswana, englishNot]

/-! ## Theorems -/

/-- Negative verbs create aux-headed AVCs. -/
theorem negVerb_implies_auxHeaded :
    NegStrategy.negVerb.expectedInflPattern = some .auxHeaded := rfl

/-- Negative affixes do not create AVCs. -/
theorem negAffix_no_avc :
    NegStrategy.negAffix.expectedInflPattern = none := rfl

/-- Negative particles do not create AVCs. -/
theorem negParticle_no_avc :
    NegStrategy.negParticle.expectedInflPattern = none := rfl

/-! ## Per-datum verification -/

theorem finnish_is_negVerb : finnish.strategy = .negVerb := rfl
theorem komi_is_negVerb : komi.strategy = .negVerb := rfl
theorem udihe_is_negVerb : udihe.strategy = .negVerb := rfl
theorem kwerba_is_negAffix : kwerba.strategy = .negAffix := rfl
theorem tswana_is_negAffix : tswana.strategy = .negAffix := rfl
theorem english_is_negParticle : englishNot.strategy = .negParticle := rfl

end Phenomena.AuxiliaryVerbs.NegativeAuxiliaries
