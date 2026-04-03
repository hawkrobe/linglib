import Linglib.Phenomena.AuxiliaryVerbs.Typology
import Linglib.Phenomena.Negation.Typology
import Linglib.Fragments.Finnish.Negation
import Linglib.Fragments.Italian.Negation

/-!
# Negative Auxiliaries
@cite{anderson-2006} @cite{miestamo-2005}

Some languages express sentential negation through a **negative auxiliary verb**
that hosts inflection (tense, agreement) while the lexical verb appears in a
nonfinite form. This is a special case of the aux-headed AVC pattern.

## Cross-linguistic strategies

| Strategy | Structure | Example |
|----------|-----------|---------|
| NegVerb | Inflected neg aux + nonfinite LV | Finnish *ei mene* 'NEG.3SG go' |
| NegAffix | Bound negative morpheme | Kwerba *or-*, Tswana *ga/se* |
| NegParticle | Free negative particle | English *not*, Italian *non* |

The neg-verb strategy is particularly interesting because the negative element
is itself an auxiliary verb, creating an AVC with the negative verb as
inflectional head.

-/

namespace Phenomena.AuxiliaryVerbs.NegativeAuxiliaries

open Phenomena.AuxiliaryVerbs.Typology (InflPattern)

/-! ## Types -/

/-- Strategy for expressing sentential negation. -/
inductive NegStrategy where
  /-- Negative auxiliary verb that inflects (Finnish *ei*, Komi *oz*). -/
  | negVerb
  /-- Bound negative morpheme (Kwerba *or-* prefix, Tswana *ga/se*). -/
  | negAffix
  /-- Free negative particle (English *not*). -/
  | negParticle
  deriving DecidableEq, Repr

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

/-- Finnish *ei* — negative auxiliary verb (inflects for person/number).
    The 3sg citation form derives from `Fragments.Finnish.Negation.negParadigm`. -/
def finnish : NegAuxDatum :=
  { language := "Finnish"
  , strategy := .negVerb
  , form := match Fragments.Finnish.Negation.negParadigm.find?
      (fun f => f.person == 3 && f.number == "sg") with
    | some f => f.form
    | none => "ei"
  , gloss := "e-n mene 'NEG-1SG go' (I don't go)" }

/-- Komi *oz* — negative auxiliary verb (@cite{anderson-2006}). -/
def komi : NegAuxDatum :=
  { language := "Komi"
  , strategy := .negVerb
  , form := "oz"
  , gloss := "oz mun 'NEG go'" }

/-- Udihe *e-si* — negative auxiliary verb (past tense on neg aux)
    (@cite{anderson-2006}). -/
def udihe : NegAuxDatum :=
  { language := "Udihe"
  , strategy := .negVerb
  , form := "e-si"
  , gloss := "e-si ŋene 'NEG-PST go' (didn't go)" }

/-- Kwerba *or-* — negative affix (prefix on verb) (@cite{anderson-2006}). -/
def kwerba : NegAuxDatum :=
  { language := "Kwerba"
  , strategy := .negAffix
  , form := "or-"
  , gloss := "or-war 'NEG-go'" }

/-- Tswana *ga/se* — negative affixes (preverbal bound morphemes in the Bantu
    verbal complex; *ga* in indicative, *se* in subjunctive/hortative). -/
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

/-- Italian *non* — preverbal negative particle (symmetric negation).
    Form derived from `Fragments.Italian.Negation.negMarker`. -/
def italianNon : NegAuxDatum :=
  { language := "Italian"
  , strategy := .negParticle
  , form := Fragments.Italian.Negation.negMarker
  , gloss := "non mangia 'NEG eats' (he doesn't eat)" }

def allData : List NegAuxDatum :=
  [finnish, komi, udihe, kwerba, tswana, englishNot, italianNon]

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
theorem italian_is_negParticle : italianNon.strategy = .negParticle := rfl

/-! ## Bridge to Finnish Fragment -/

/-- The Finnish negative auxiliary form derives from the Fragment paradigm. -/
theorem finnish_form_from_fragment :
    finnish.form = "ei" := rfl

/-! ## Bridge to Italian Fragment -/

/-- The Italian negative particle form derives from the Fragment negation marker. -/
theorem italian_form_from_fragment :
    italianNon.form = Fragments.Italian.Negation.negMarker := rfl

/-! ## Bridge to Negation Typology (WALS Ch 112)

`NegStrategy` in this file and `NegMorphemeType` in `Phenomena.Negation.Typology`
classify the same dimension — the morphological status of the negative marker.
This bridge maps between them. -/

open Phenomena.Negation.Typology (NegMorphemeType)

/-- Map from AVC-oriented `NegStrategy` to WALS-oriented `NegMorphemeType`. -/
def NegStrategy.toNegMorphemeType : NegStrategy → NegMorphemeType
  | .negVerb    => .auxVerb
  | .negAffix   => .affix
  | .negParticle => .particle

theorem negVerb_maps_to_auxVerb :
    NegStrategy.negVerb.toNegMorphemeType = .auxVerb := rfl
theorem negAffix_maps_to_affix :
    NegStrategy.negAffix.toNegMorphemeType = .affix := rfl
theorem negParticle_maps_to_particle :
    NegStrategy.negParticle.toNegMorphemeType = .particle := rfl

end Phenomena.AuxiliaryVerbs.NegativeAuxiliaries
