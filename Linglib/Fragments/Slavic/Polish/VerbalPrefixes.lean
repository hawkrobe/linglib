import Mathlib.Tactic.FinCases
import Linglib.Fragments.Slavic.Params

/-!
# Polish Verbal Prefixes
@cite{jablonska-2004} @cite{svenonius-2004} @cite{dendikken-1995}

Lexical entries for Polish verbal prefixes encoding the
**lexical / superlexical** distinction of @cite{svenonius-2004},
specialised to Polish per @cite{jablonska-2004}. The main typological
parallels with Russian: lexical prefixes are R-heads inside VP
(resultative, particle-like); superlexical prefixes are Asp-heads
outside VP (aspectual operators); the same prefix can realise either
class depending on context. Polish-specific feature
(@cite{jablonska-2004}): the prefix *po-* shows verbalizer-class
sensitivity — its interpretation (delimitative vs distributive vs
inchoative Degree Achievement) depends on the embedded verbalizer
suffix.

## Main definitions

* `Aspect` — perfective vs imperfective.
* `SuperlexicalSubtype` — six aspectual subtypes (parallel to Russian).
* `PrefixClass` — `lexical` or `superlexical _`.
* `PolishPrefixedVerbEntry` — a single entry.
* `inventory` — six canonical entries covering the lex/superlex split.

## Main results

* `inventory_transparent_concat` — every entry's `prefixedForm` is the
  literal concatenation `morpheme ++ bareStem`.
* `stemAspect_imperfective_of_isSuperlexical` — diagnostic 56c
  (@cite{svenonius-2004} §4.1) verified across the inventory.

-/

namespace Fragments.Slavic.Polish.VerbalPrefixes

open Fragments.Slavic (Aspect SuperlexicalSubtype PrefixClass)

/-- A Polish prefixed-verb entry. Polish orthography (with diacritics:
    *ć*, *ż*, *ó*, *ł*, *ę*, *ą*) used directly. -/
structure PolishPrefixedVerbEntry where
  /-- Bare verb stem (infinitive, ending in *-ć* or *-c*). -/
  bareStem      : String
  /-- Aspect of the bare stem. -/
  stemAspect    : Aspect
  /-- The prefix morpheme (without dash). -/
  morpheme      : String
  /-- The prefixed perfective infinitive (transparently
      `morpheme ++ bareStem` for the entries here; voicing-assimilation
      prefixes — *z-* alternating with *s-*, *roz-* with *ros-* —
      deliberately avoided). -/
  prefixedForm  : String
  /-- @cite{svenonius-2004} class. -/
  prefixClass   : PrefixClass
  /-- Gloss of the bare stem. -/
  baseGloss     : String
  /-- Gloss of the prefixed perfective. -/
  prefixedGloss : String

/-! ### Lexical entries -/

/-- *na-pisać* 'write down' — lexical *na-* (spatial 'on, onto').
    @cite{jablonska-2004} treats Polish *na-* with concrete-spatial
    meaning as lexical; the homophonous "pure perfectivising" *na-*
    (the standard PF counterpart of *pisać*) is also typically
    classified as lexical in the Svenonius framework. Built on the
    imperfective stem *pisać*. -/
def napisac : PolishPrefixedVerbEntry where
  bareStem      := "pisać"
  stemAspect    := .imperfective
  morpheme      := "na"
  prefixedForm  := "napisać"
  prefixClass   := .lexical
  baseGloss     := "write"
  prefixedGloss := "write down"

/-- *wy-pisać* 'write out, copy out' — lexical *wy-* (spatial 'out',
    Polish counterpart of Russian *vy-*). Built on the imperfective
    stem *pisać*. -/
def wypisac : PolishPrefixedVerbEntry where
  bareStem      := "pisać"
  stemAspect    := .imperfective
  morpheme      := "wy"
  prefixedForm  := "wypisać"
  prefixClass   := .lexical
  baseGloss     := "write"
  prefixedGloss := "write out, copy out"

/-- *przy-nieść* 'bring (carry to)' — lexical *przy-* (allative,
    Polish counterpart of Russian *pri-*). Built on the imperfective
    determinate-motion stem *nieść*. -/
def przyniesc : PolishPrefixedVerbEntry where
  bareStem      := "nieść"
  stemAspect    := .imperfective
  morpheme      := "przy"
  prefixedForm  := "przynieść"
  prefixClass   := .lexical
  baseGloss     := "carry"
  prefixedGloss := "bring (carry to)"

/-! ### Superlexical entries -/

/-- *za-śpiewać* 'start singing' — superlexical *za-* INCP (Polish
    counterpart of Russian *za-* on the inceptive reading). Built on
    the imperfective stem *śpiewać*. -/
def zaspiewacInceptive : PolishPrefixedVerbEntry where
  bareStem      := "śpiewać"
  stemAspect    := .imperfective
  morpheme      := "za"
  prefixedForm  := "zaśpiewać"
  prefixClass   := .superlexical .inceptive
  baseGloss     := "sing"
  prefixedGloss := "start singing"

/-- *po-siedzieć* 'sit for a while' — superlexical *po-* DLMT.
    @cite{jablonska-2004}'s central topic: Polish *po-* shows
    verbalizer-sensitive interpretations; with imperfective high
    verbalizers it gives the delimitative reading shown here. Built
    on the imperfective stem *siedzieć*. -/
def posiedziec : PolishPrefixedVerbEntry where
  bareStem      := "siedzieć"
  stemAspect    := .imperfective
  morpheme      := "po"
  prefixedForm  := "posiedzieć"
  prefixClass   := .superlexical .delimitative
  baseGloss     := "sit"
  prefixedGloss := "sit for a while"

/-- *prze-czytać* 'read through, read completely' — superlexical
    *prze-* CMPL (completive 'through, all the way'). Polish *prze-*
    is the canonical completive (cf. Russian *iz-* / *do-*). Built on
    the imperfective stem *czytać*. -/
def przeczytac : PolishPrefixedVerbEntry where
  bareStem      := "czytać"
  stemAspect    := .imperfective
  morpheme      := "prze"
  prefixedForm  := "przeczytać"
  prefixClass   := .superlexical .completive
  baseGloss     := "read"
  prefixedGloss := "read through, read completely"

/-- The canonical inventory: 3 lexical, 3 superlexical. -/
def inventory : List PolishPrefixedVerbEntry :=
  [napisac, wypisac, przyniesc, zaspiewacInceptive, posiedziec, przeczytac]

/-! ### Properties -/

/-- An entry's `prefixedForm` is the literal concatenation of
    `morpheme ++ bareStem`. -/
def IsTransparentConcat (e : PolishPrefixedVerbEntry) : Prop :=
  e.prefixedForm = e.morpheme ++ e.bareStem

instance : DecidablePred IsTransparentConcat :=
  fun e => decEq e.prefixedForm (e.morpheme ++ e.bareStem)

/-- Every inventory entry is a transparent concatenation. -/
theorem inventory_transparent_concat
    (e : PolishPrefixedVerbEntry) (he : e ∈ inventory) :
    IsTransparentConcat e := by
  fin_cases he <;> rfl

/-- @cite{svenonius-2004}'s diagnostic 56c (paper §4.1): superlexical
    entries select imperfective stems. -/
theorem stemAspect_imperfective_of_isSuperlexical
    (e : PolishPrefixedVerbEntry) (he : e ∈ inventory)
    (hs : e.prefixClass.IsSuperlexical) :
    e.stemAspect = Aspect.imperfective := by
  fin_cases he <;> first | rfl | exact absurd hs (by decide)

end Fragments.Slavic.Polish.VerbalPrefixes
