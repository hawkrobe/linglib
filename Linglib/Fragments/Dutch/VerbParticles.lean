import Mathlib.Tactic.FinCases

/-!
# Dutch Verbal Prefix and Particle Verbs
@cite{dendikken-1995}

Lexical entries for Dutch verbs with prefixes (separable particles
*scheidbaar samengestelde werkwoorden*; inseparable prefixes
*onscheidbaar samengestelde werkwoorden*) — the distinction central
to Germanic VPC syntax and cited extensively by @cite{dendikken-1995}
in the SC analysis. The two classes share concatenated citation form
but diverge on the diagnostic morphology: separable verbs show *ge-*
insertion in the past participle (*opbellen* → *op-ge-beld*); inseparable
verbs lack *ge-* entirely (*verstaan* → *verstaan*, not *\*ge-verstaan*).

## Main definitions

* `DutchAffixClass` — separable vs inseparable.
* `DutchVerbalAffixEntry` — a single entry.
* `inventory` — eight canonical entries (5 separable, 3 inseparable).

## Main results

* `inventory_citation_concat` — every entry's `citationForm` is the
  concatenation `affix ++ stem`.
* `IsSeparable` predicate with decidable instance.

-/

namespace Fragments.Dutch.VerbParticles

/-- Dutch affix class: separable particles (*op-*, *aan-*) split off the
    verb under V2 and trigger *ge-* insertion in the past participle;
    inseparable prefixes (*ver-*, *be-*, *ont-*) are derivational and
    never split. -/
inductive DutchAffixClass
  | separable
  | inseparable
  deriving DecidableEq

/-- A Dutch prefixed-verb entry: separable particle verb or inseparable
    prefix verb. -/
structure DutchVerbalAffixEntry where
  /-- Citation infinitive (affix + stem concatenated). -/
  citationForm   : String
  /-- Bare verb stem. -/
  stem           : String
  /-- The affix (separable particle or inseparable prefix). -/
  affix          : String
  /-- Affix class. -/
  affixClass     : DutchAffixClass
  /-- Past participle. Separable verbs show *ge-* insertion
      (*opbellen* → *opgebeld*); inseparable verbs lack *ge-*
      (*verstaan* → *verstaan*). -/
  pastParticiple : String
  /-- English gloss. -/
  gloss          : String

/-- An entry's affix is *separable*. -/
def IsSeparable (e : DutchVerbalAffixEntry) : Prop :=
  e.affixClass = .separable

instance : DecidablePred IsSeparable :=
  fun e => decEq e.affixClass .separable

/-! ### Separable particle verbs -/

/-- *opbellen* 'phone, call up'. Separable *op-*; pp *opgebeld*. -/
def opbellen : DutchVerbalAffixEntry where
  citationForm   := "opbellen"
  stem           := "bellen"
  affix          := "op"
  affixClass     := .separable
  pastParticiple := "opgebeld"
  gloss          := "phone, call up"

/-- *aankomen* 'arrive'. Separable *aan-*; pp *aangekomen*. -/
def aankomen : DutchVerbalAffixEntry where
  citationForm   := "aankomen"
  stem           := "komen"
  affix          := "aan"
  affixClass     := .separable
  pastParticiple := "aangekomen"
  gloss          := "arrive"

/-- *uitgaan* 'go out'. Separable *uit-*; pp *uitgegaan*. -/
def uitgaan : DutchVerbalAffixEntry where
  citationForm   := "uitgaan"
  stem           := "gaan"
  affix          := "uit"
  affixClass     := .separable
  pastParticiple := "uitgegaan"
  gloss          := "go out"

/-- *meedoen* 'participate, take part'. Separable *mee-*; pp *meegedaan*. -/
def meedoen : DutchVerbalAffixEntry where
  citationForm   := "meedoen"
  stem           := "doen"
  affix          := "mee"
  affixClass     := .separable
  pastParticiple := "meegedaan"
  gloss          := "participate"

/-- *doorwerken* 'work through'. Separable *door-*; pp *doorgewerkt*. -/
def doorwerken : DutchVerbalAffixEntry where
  citationForm   := "doorwerken"
  stem           := "werken"
  affix          := "door"
  affixClass     := .separable
  pastParticiple := "doorgewerkt"
  gloss          := "work through"

/-! ### Inseparable prefix verbs -/

/-- *verstaan* 'understand'. Inseparable *ver-*; pp *verstaan* (no *ge-*). -/
def verstaan : DutchVerbalAffixEntry where
  citationForm   := "verstaan"
  stem           := "staan"
  affix          := "ver"
  affixClass     := .inseparable
  pastParticiple := "verstaan"
  gloss          := "understand"

/-- *bezoeken* 'visit'. Inseparable *be-*; pp *bezocht* (no *ge-*). -/
def bezoeken : DutchVerbalAffixEntry where
  citationForm   := "bezoeken"
  stem           := "zoeken"
  affix          := "be"
  affixClass     := .inseparable
  pastParticiple := "bezocht"
  gloss          := "visit"

/-- *ontkomen* 'escape'. Inseparable *ont-*; pp *ontkomen* (no *ge-*). -/
def ontkomen : DutchVerbalAffixEntry where
  citationForm   := "ontkomen"
  stem           := "komen"
  affix          := "ont"
  affixClass     := .inseparable
  pastParticiple := "ontkomen"
  gloss          := "escape"

/-- The canonical inventory: 5 separable + 3 inseparable. -/
def inventory : List DutchVerbalAffixEntry :=
  [opbellen, aankomen, uitgaan, meedoen, doorwerken,
   verstaan, bezoeken, ontkomen]

/-! ### Properties -/

/-- An entry's `citationForm` is the literal concatenation of its
    `affix` and `stem`. Holds for both separable and inseparable
    entries — the morphological split lives in the past participle,
    not in the citation form. -/
def IsCitationConcat (e : DutchVerbalAffixEntry) : Prop :=
  e.citationForm = e.affix ++ e.stem

instance : DecidablePred IsCitationConcat :=
  fun e => decEq e.citationForm (e.affix ++ e.stem)

/-- Every inventory entry's citation form is the literal concatenation
    of its affix and stem. -/
theorem inventory_citation_concat
    (e : DutchVerbalAffixEntry) (he : e ∈ inventory) :
    IsCitationConcat e := by
  fin_cases he <;> rfl

end Fragments.Dutch.VerbParticles
