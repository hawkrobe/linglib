import Mathlib.Tactic.FinCases

/-!
# German Verbal Prefix and Particle Verbs
@cite{ludeling-2001} @cite{dendikken-1995}

Lexical entries for German verbs with prefixes — both separable
particle verbs (*scheidbar zusammengesetzte Verben*, e.g. *anrufen*)
and inseparable prefix verbs (*ver-*, *be-*, *ent-*, *zer-*). The
distinction is the major morphosyntactic split in the German verbal
system: separable verbs split under V2 (*er ruft Maria an*) and
trigger *ge-* insertion in the past participle (*angerufen*) and *zu*
insertion in the *zu*-infinitive (*anzurufen*); inseparable prefix
verbs never split, lack *ge-* in the participle (*verstanden*, not
*\*geverstanden*), and place *zu* before the whole word in the
*zu*-infinitive (*zu verstehen*).

@cite{dendikken-1995}'s SC analysis (book ch. 2) takes German
particle verbs as one of the major Germanic test cases for the
ergative-particle / SC-head proposal.

## Main definitions

* `GermanAffixClass` — separable vs inseparable.
* `GermanVerbalAffixEntry` — a single entry.
* `inventory` — eight canonical entries (5 separable, 3 inseparable).

## Main results

* `inventory_citation_concat` — every entry's `citationForm` is
  `affix ++ stem` (holds for both classes).
* `IsSeparable` predicate with decidable instance.

-/

namespace Fragments.German.VerbParticles

/-- German affix class: separable particles split under V2 and trigger
    *ge-*/*-zu-* insertion; inseparable prefixes never split. -/
inductive GermanAffixClass
  | separable
  | inseparable
  deriving DecidableEq

/-- A German prefixed-verb entry: separable particle verb or
    inseparable prefix verb. Records both the past participle (with
    or without *ge-* insertion) and the *zu*-infinitive (concatenated
    or space-separated) for the morphological diagnostics. -/
structure GermanVerbalAffixEntry where
  /-- Citation infinitive (affix + stem concatenated). -/
  citationForm   : String
  /-- Bare verb stem. -/
  stem           : String
  /-- The affix (separable particle or inseparable prefix). -/
  affix          : String
  /-- Affix class. -/
  affixClass     : GermanAffixClass
  /-- Past participle. Separable: *ge-* between affix and stem
      (*angerufen*). Inseparable: bare verb participle, no *ge-*
      (*verstanden*). -/
  pastParticiple : String
  /-- *zu*-infinitive. Separable: *zu* concatenated between affix and
      stem (*anzurufen*, one word). Inseparable: *zu* as separate word
      before the citation form (*zu verstehen*). -/
  zuInfinitive   : String
  /-- English gloss. -/
  gloss          : String

/-- An entry's affix is *separable*. -/
def IsSeparable (e : GermanVerbalAffixEntry) : Prop :=
  e.affixClass = .separable

instance : DecidablePred IsSeparable :=
  fun e => decEq e.affixClass .separable

/-! ### Separable particle verbs -/

/-- *anrufen* 'phone, call up'. Separable *an-*; pp *angerufen*;
    zu-inf *anzurufen*. -/
def anrufen : GermanVerbalAffixEntry where
  citationForm   := "anrufen"
  stem           := "rufen"
  affix          := "an"
  affixClass     := .separable
  pastParticiple := "angerufen"
  zuInfinitive   := "anzurufen"
  gloss          := "phone, call up"

/-- *aufmachen* 'open'. Separable *auf-*; pp *aufgemacht*;
    zu-inf *aufzumachen*. -/
def aufmachen : GermanVerbalAffixEntry where
  citationForm   := "aufmachen"
  stem           := "machen"
  affix          := "auf"
  affixClass     := .separable
  pastParticiple := "aufgemacht"
  zuInfinitive   := "aufzumachen"
  gloss          := "open"

/-- *einschalten* 'switch on'. Separable *ein-*; pp *eingeschaltet*;
    zu-inf *einzuschalten*. -/
def einschalten : GermanVerbalAffixEntry where
  citationForm   := "einschalten"
  stem           := "schalten"
  affix          := "ein"
  affixClass     := .separable
  pastParticiple := "eingeschaltet"
  zuInfinitive   := "einzuschalten"
  gloss          := "switch on"

/-- *abfahren* 'depart'. Separable *ab-*; pp *abgefahren*;
    zu-inf *abzufahren*. -/
def abfahren : GermanVerbalAffixEntry where
  citationForm   := "abfahren"
  stem           := "fahren"
  affix          := "ab"
  affixClass     := .separable
  pastParticiple := "abgefahren"
  zuInfinitive   := "abzufahren"
  gloss          := "depart"

/-- *mitkommen* 'come along'. Separable *mit-*; pp *mitgekommen*;
    zu-inf *mitzukommen*. -/
def mitkommen : GermanVerbalAffixEntry where
  citationForm   := "mitkommen"
  stem           := "kommen"
  affix          := "mit"
  affixClass     := .separable
  pastParticiple := "mitgekommen"
  zuInfinitive   := "mitzukommen"
  gloss          := "come along"

/-! ### Inseparable prefix verbs -/

/-- *verstehen* 'understand'. Inseparable *ver-*; pp *verstanden*
    (no *ge-*); zu-inf *zu verstehen* (separated). -/
def verstehen : GermanVerbalAffixEntry where
  citationForm   := "verstehen"
  stem           := "stehen"
  affix          := "ver"
  affixClass     := .inseparable
  pastParticiple := "verstanden"
  zuInfinitive   := "zu verstehen"
  gloss          := "understand"

/-- *bezahlen* 'pay'. Inseparable *be-*; pp *bezahlt* (no *ge-*);
    zu-inf *zu bezahlen* (separated). -/
def bezahlen : GermanVerbalAffixEntry where
  citationForm   := "bezahlen"
  stem           := "zahlen"
  affix          := "be"
  affixClass     := .inseparable
  pastParticiple := "bezahlt"
  zuInfinitive   := "zu bezahlen"
  gloss          := "pay"

/-- *entkommen* 'escape'. Inseparable *ent-*; pp *entkommen*
    (no *ge-*); zu-inf *zu entkommen* (separated). -/
def entkommen : GermanVerbalAffixEntry where
  citationForm   := "entkommen"
  stem           := "kommen"
  affix          := "ent"
  affixClass     := .inseparable
  pastParticiple := "entkommen"
  zuInfinitive   := "zu entkommen"
  gloss          := "escape"

/-- The canonical inventory: 5 separable + 3 inseparable. -/
def inventory : List GermanVerbalAffixEntry :=
  [anrufen, aufmachen, einschalten, abfahren, mitkommen,
   verstehen, bezahlen, entkommen]

/-! ### Properties -/

/-- An entry's `citationForm` is the literal concatenation of its
    `affix` and `stem`. Holds for both separable and inseparable
    classes; the morphological diagnostics live in the past participle
    and *zu*-infinitive shapes (separable inserts *ge-*/*-zu-* between
    affix and stem; inseparable does neither). -/
def IsCitationConcat (e : GermanVerbalAffixEntry) : Prop :=
  e.citationForm = e.affix ++ e.stem

instance : DecidablePred IsCitationConcat :=
  fun e => decEq e.citationForm (e.affix ++ e.stem)

/-- Every inventory entry's citation form is the concatenation of its
    affix and stem. -/
theorem inventory_citation_concat
    (e : GermanVerbalAffixEntry) (he : e ∈ inventory) :
    IsCitationConcat e := by
  fin_cases he <;> rfl

end Fragments.German.VerbParticles
