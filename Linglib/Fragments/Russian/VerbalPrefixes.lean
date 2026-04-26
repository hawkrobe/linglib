import Mathlib.Tactic.FinCases

/-!
# Russian Verbal Prefixes
@cite{svenonius-2004} @cite{dendikken-1995}

Lexical entries for Russian verbal prefixes encoding the
**lexical / superlexical** distinction of @cite{svenonius-2004}: lexical
prefixes are R-heads inside VP (resultative, particle-like); superlexical
prefixes are Asp-heads outside VP (aspectual operators). The same
prefix string can realise either class — paper §1 ex. 1a/1c uses *za-*
both ways. Diagnostic 56c (paper §4.1): superlexicals select imperfective
stems. Connects to @cite{dendikken-1995}'s "affixal particle" thesis
(book §5.2.5 fn. 10), which the lex class instantiates and the superlex
class doesn't subdivide.

## Main definitions

* `Aspect` — perfective vs imperfective.
* `SuperlexicalSubtype` — six aspectual subtypes from paper §3.
* `PrefixClass` — `lexical` or `superlexical _`, the Svenonius split.
* `RussianPrefixedVerbEntry` — a single lexical entry.
* `inventory` — six canonical entries.

## Main results

* `inventory_transparent_concat` — every entry's `prefixedForm` is the
  literal concatenation of `morpheme ++ bareStem`.
* `stemAspect_imperfective_of_isSuperlexical` — Svenonius's diagnostic
  56c verified across the inventory.

-/

namespace Fragments.Russian.VerbalPrefixes

/-- Russian grammatical aspect. -/
inductive Aspect
  | perfective
  | imperfective
  deriving DecidableEq

/-- Aspectual subtypes for the superlexical class
    (@cite{svenonius-2004} §3). The paper distinguishes ≈ 9 subtypes;
    six are encoded here (excessive, attenuative, and terminative
    are deferred). -/
inductive SuperlexicalSubtype
  | delimitative
  | cumulative
  | completive
  | repetitive
  | inceptive
  | distributive
  deriving DecidableEq

/-- @cite{svenonius-2004}'s lexical / superlexical split. The
    `superlexical` case carries its subtype, eliminating the need for
    a separate `Option`-typed companion field plus a consistency lemma. -/
inductive PrefixClass
  | lexical
  | superlexical (subtype : SuperlexicalSubtype)
  deriving DecidableEq

namespace PrefixClass

/-- A `PrefixClass` is *superlexical* iff it is the `superlexical _` case. -/
def IsSuperlexical : PrefixClass → Prop
  | .lexical          => False
  | .superlexical _   => True

instance : DecidablePred IsSuperlexical
  | .lexical        => isFalse id
  | .superlexical _ => isTrue trivial

end PrefixClass

/-- A Russian prefixed-verb entry. Latin transliteration with `'` for
    the soft-sign infinitive ending. -/
structure RussianPrefixedVerbEntry where
  /-- Bare verb stem (infinitive). -/
  bareStem      : String
  /-- Aspect of the bare stem. -/
  stemAspect    : Aspect
  /-- The prefix morpheme. -/
  morpheme      : String
  /-- The prefixed perfective infinitive. -/
  prefixedForm  : String
  /-- @cite{svenonius-2004} class. -/
  prefixClass   : PrefixClass
  /-- Gloss of the bare stem. -/
  baseGloss     : String
  /-- Gloss of the prefixed perfective. -/
  prefixedGloss : String

/-! ### Lexical entries -/

/-- *za-brosit'* 'kick into / throw into' — lexical *za-*
    (@cite{svenonius-2004} §1 ex. 1a, transparently resultative
    spatial). Built on the perfective stem *brosit'*. -/
def zabrosit : RussianPrefixedVerbEntry where
  bareStem      := "brosit'"
  stemAspect    := .perfective
  morpheme      := "za"
  prefixedForm  := "zabrosit'"
  prefixClass   := .lexical
  baseGloss     := "throw"
  prefixedGloss := "throw into, kick into"

/-- *vy-brosit'* 'throw out' — lexical *vy-* (English *out* analogue;
    @cite{svenonius-2004} ex. 4a uses the secondary imperfective
    *vy-brasyvatj*). Built on the perfective stem *brosit'*. -/
def vybrosit : RussianPrefixedVerbEntry where
  bareStem      := "brosit'"
  stemAspect    := .perfective
  morpheme      := "vy"
  prefixedForm  := "vybrosit'"
  prefixClass   := .lexical
  baseGloss     := "throw"
  prefixedGloss := "throw out"

/-- *pri-nesti* 'bring (carry to)' — lexical *pri-* (allative). The
    lex classification of *pri-* is from broader Slavicist literature
    (Romanova 2004; Babko-Malaya 2003) — @cite{svenonius-2004}
    §1-§5 does not work *pri-* as an example. Built on the
    imperfective determinate-motion stem *nesti*. -/
def prinesti : RussianPrefixedVerbEntry where
  bareStem      := "nesti"
  stemAspect    := .imperfective
  morpheme      := "pri"
  prefixedForm  := "prinesti"
  prefixClass   := .lexical
  baseGloss     := "carry"
  prefixedGloss := "bring (carry to)"

/-! ### Superlexical entries -/

/-- *za-brosat'* 'start throwing' — superlexical *za-* INCP
    (@cite{svenonius-2004} §1 ex. 1c). Minimal pair with `zabrosit`
    on the same morpheme but different `prefixClass`. Built on the
    imperfective stem *brosat'* (per Svenonius's diagnostic 56c). -/
def zabrosatInceptive : RussianPrefixedVerbEntry where
  bareStem      := "brosat'"
  stemAspect    := .imperfective
  morpheme      := "za"
  prefixedForm  := "zabrosat'"
  prefixClass   := .superlexical .inceptive
  baseGloss     := "throw"
  prefixedGloss := "start throwing"

/-- *po-sidet'* 'sit for a while' — superlexical *po-* DLMT
    (canonical delimitative). Built on the imperfective stem *sidet'*. -/
def posidet : RussianPrefixedVerbEntry where
  bareStem      := "sidet'"
  stemAspect    := .imperfective
  morpheme      := "po"
  prefixedForm  := "posidet'"
  prefixClass   := .superlexical .delimitative
  baseGloss     := "sit"
  prefixedGloss := "sit for a while"

/-- *do-pisat'* 'finish writing' — superlexical *do-* CMPL. Note:
    *do-* is the standard Russian completive in broader Slavicist
    literature; @cite{svenonius-2004} §3 takes Bulgarian *iz-* as the
    canonical completive instead. Built on the imperfective stem *pisat'*. -/
def dopisat : RussianPrefixedVerbEntry where
  bareStem      := "pisat'"
  stemAspect    := .imperfective
  morpheme      := "do"
  prefixedForm  := "dopisat'"
  prefixClass   := .superlexical .completive
  baseGloss     := "write"
  prefixedGloss := "finish writing"

/-- The canonical inventory: three lexical entries plus three
    superlexical entries (with the `zabrosit` / `zabrosatInceptive`
    minimal pair on *za-*). -/
def inventory : List RussianPrefixedVerbEntry :=
  [zabrosit, vybrosit, prinesti, zabrosatInceptive, posidet, dopisat]

/-! ### Properties -/

/-- An entry's `prefixedForm` is the literal concatenation of its
    `morpheme` and `bareStem`. The inventory deliberately avoids
    voicing-assimilation prefixes (*iz-*, *raz-*, *voz-*, *bez-*)
    where this would fail. -/
def IsTransparentConcat (e : RussianPrefixedVerbEntry) : Prop :=
  e.prefixedForm = e.morpheme ++ e.bareStem

instance : DecidablePred IsTransparentConcat :=
  fun e => decEq e.prefixedForm (e.morpheme ++ e.bareStem)

/-- Every entry in `inventory` is a transparent concatenation. -/
theorem inventory_transparent_concat
    (e : RussianPrefixedVerbEntry) (he : e ∈ inventory) :
    IsTransparentConcat e := by
  fin_cases he <;> rfl

/-- @cite{svenonius-2004}'s diagnostic 56c (paper §4.1): a superlexical
    entry has an imperfective bare stem. Lexical entries are
    unconstrained. -/
theorem stemAspect_imperfective_of_isSuperlexical
    (e : RussianPrefixedVerbEntry) (he : e ∈ inventory)
    (hs : e.prefixClass.IsSuperlexical) :
    e.stemAspect = Aspect.imperfective := by
  fin_cases he <;> first | rfl | exact absurd hs (by decide)

end Fragments.Russian.VerbalPrefixes
