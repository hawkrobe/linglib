import Mathlib.Tactic.FinCases
import Linglib.Semantics.Aspect.Basic

/-!
# Svenonius (2004): Slavic Prefixes Inside and Outside VP

[svenonius-2004] splits Slavic verbal prefixes into two classes: **lexical**
prefixes are R-heads inside VP (resultative, particle-like, connecting to
[dendikken-1995]'s treatment of Germanic verb particles), while
**superlexical** prefixes are Asp-heads outside VP (aspectual operators).
The same prefix string can realise either class — his §1 exx. (1a)/(1c)
use Russian *za-* both ways. The classification is contested rather than
consensus: [romanova-2004] documents diagnostic mismatches, and Tatevosov's
later work posits an intermediate class.

The syntactic height cut named here is the same one
`Minimalist.AspFlavor` (outer vs inner aspect, Travis/Cinque) carries for
Sinitic split-aspect; the types are kept separate because the commitments
differ (lexical = resultative R-head, not merely inner-Asp host).

Stem aspect reuses `Semantics.Aspect.ViewpointAspectB`.

## Main definitions

* `SuperlexicalSubtype` — a selection of the superlexical Aktionsart
  subtypes recurring in the paper's §4 and in [istratkova-2004]; not a
  closed inventory (the Bulgarian ordering in his (57) also lists
  excessive *raz-*).
* `PrefixClass` — `lexical` or `superlexical _`, with the
  `IsSuperlexical` predicate.
* `PrefixedVerbEntry` — a single-prefix prefixed-verb lexical entry
  (shared with `Studies/Jablonska2004.lean` for Polish).
* `Russian.inventory` — six canonical Russian entries.

## Main results

* `Russian.inventory_transparent_concat` — every entry's `prefixedForm`
  is the literal concatenation `morpheme ++ bareStem`.
* `Russian.stemAspect_imperfective_of_isSuperlexical` — the paper's
  diagnostic (56c) (§4.1): superlexical prefixes select imperfective
  stems.
-/

namespace Svenonius2004

open Semantics.Aspect (ViewpointAspectB)

/-- Aspectual subtypes of the superlexical class — the labels recurring
    in [svenonius-2004] §4 (his Bulgarian ordering (57)) and in
    [istratkova-2004]'s prefix-by-prefix taxonomy. A selection, not a
    closed set: excessive, terminative, and perdurative also occur in
    the literature. -/
inductive SuperlexicalSubtype
  | delimitative
  | cumulative
  | completive
  | repetitive
  | inceptive
  | distributive
  | attenuative
  deriving DecidableEq

/-- [svenonius-2004]'s lexical / superlexical split as a single ADT —
    the superlexical case carries its subtype. -/
inductive PrefixClass
  | lexical
  | superlexical (subtype : SuperlexicalSubtype)
  deriving DecidableEq

namespace PrefixClass

/-- A `PrefixClass` is *superlexical* iff it is the `superlexical _` case. -/
def IsSuperlexical : PrefixClass → Prop
  | .lexical        => False
  | .superlexical _ => True

instance : DecidablePred IsSuperlexical
  | .lexical        => isFalse id
  | .superlexical _ => isTrue trivial

end PrefixClass

/-- A single-prefix prefixed-verb lexical entry. -/
structure PrefixedVerbEntry where
  /-- Bare verb stem (citation form). -/
  bareStem      : String
  /-- Viewpoint aspect of the bare stem. -/
  stemAspect    : ViewpointAspectB
  /-- The prefix morpheme. -/
  morpheme      : String
  /-- The prefixed perfective citation form. -/
  prefixedForm  : String
  /-- [svenonius-2004] class. -/
  prefixClass   : PrefixClass
  /-- Gloss of the bare stem. -/
  baseGloss     : String
  /-- Gloss of the prefixed perfective. -/
  prefixedGloss : String

/-- An entry's `prefixedForm` is the literal concatenation of its
    `morpheme` and `bareStem`. Inventories deliberately avoid
    voicing-assimilation prefixes (*iz-*, *raz-*, *voz-*, *bez-*)
    where this would fail. -/
def IsTransparentConcat (e : PrefixedVerbEntry) : Prop :=
  e.prefixedForm = e.morpheme ++ e.bareStem

instance : DecidablePred IsTransparentConcat :=
  fun e => decEq e.prefixedForm (e.morpheme ++ e.bareStem)

/-! ### Russian inventory

Latin transliteration with `'` for the soft-sign infinitive ending. -/

namespace Russian

/-- *za-brosit'* 'kick into / throw into' — lexical *za-*
    ([svenonius-2004] §1 ex. (1a), transparently resultative spatial).
    Built on the perfective stem *brosit'*. -/
def zabrosit : PrefixedVerbEntry where
  bareStem      := "brosit'"
  stemAspect    := .perfective
  morpheme      := "za"
  prefixedForm  := "zabrosit'"
  prefixClass   := .lexical
  baseGloss     := "throw"
  prefixedGloss := "throw into, kick into"

/-- *vy-brosit'* 'throw out' — lexical *vy-* (English *out* analogue;
    [svenonius-2004] ex. (4a) uses the secondary imperfective
    *vy-brasyvatj*). Built on the perfective stem *brosit'*. -/
def vybrosit : PrefixedVerbEntry where
  bareStem      := "brosit'"
  stemAspect    := .perfective
  morpheme      := "vy"
  prefixedForm  := "vybrosit'"
  prefixClass   := .lexical
  baseGloss     := "throw"
  prefixedGloss := "throw out"

/-- *pri-nesti* 'bring (carry to)' — lexical *pri-* (allative). The
    lex classification of *pri-* is from the broader Slavicist
    literature ([romanova-2004]; [babko-malaya-2003]) — [svenonius-2004]
    does not work *pri-* as an example. Built on the imperfective
    determinate-motion stem *nesti*. -/
def prinesti : PrefixedVerbEntry where
  bareStem      := "nesti"
  stemAspect    := .imperfective
  morpheme      := "pri"
  prefixedForm  := "prinesti"
  prefixClass   := .lexical
  baseGloss     := "carry"
  prefixedGloss := "bring (carry to)"

/-- *za-brosat'* 'start throwing' — superlexical *za-* INCP
    ([svenonius-2004] §1 ex. (1c)). Minimal pair with `zabrosit` on the
    same morpheme but different `prefixClass`. Built on the imperfective
    stem *brosat'*. Stress distinguishes it from the homographic
    *zabrosát'* 'pelt (with)'. -/
def zabrosatInceptive : PrefixedVerbEntry where
  bareStem      := "brosat'"
  stemAspect    := .imperfective
  morpheme      := "za"
  prefixedForm  := "zabrosat'"
  prefixClass   := .superlexical .inceptive
  baseGloss     := "throw"
  prefixedGloss := "start throwing"

/-- *po-sidet'* 'sit for a while' — superlexical *po-* DLMT (canonical
    delimitative; [svenonius-2004] (57c) labels Bulgarian *po-* DLMT).
    Built on the imperfective stem *sidet'*. -/
def posidet : PrefixedVerbEntry where
  bareStem      := "sidet'"
  stemAspect    := .imperfective
  morpheme      := "po"
  prefixedForm  := "posidet'"
  prefixClass   := .superlexical .delimitative
  baseGloss     := "sit"
  prefixedGloss := "sit for a while"

/-- *do-pisat'* 'finish writing' — superlexical *do-* CMPL. Note:
    *do-* is the standard Russian completive in the broader Slavicist
    literature; [svenonius-2004] §4 takes Bulgarian *iz-* as the
    canonical completive instead. Built on the imperfective stem
    *pisat'*. -/
def dopisat : PrefixedVerbEntry where
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
def inventory : List PrefixedVerbEntry :=
  [zabrosit, vybrosit, prinesti, zabrosatInceptive, posidet, dopisat]

/-- Every entry in `inventory` is a transparent concatenation. -/
theorem inventory_transparent_concat
    (e : PrefixedVerbEntry) (he : e ∈ inventory) :
    IsTransparentConcat e := by
  fin_cases he <;> rfl

/-- [svenonius-2004]'s diagnostic (56c) (§4.1): a superlexical entry
    has an imperfective bare stem. Lexical entries are unconstrained. -/
theorem stemAspect_imperfective_of_isSuperlexical
    (e : PrefixedVerbEntry) (he : e ∈ inventory)
    (hs : e.prefixClass.IsSuperlexical) :
    e.stemAspect = ViewpointAspectB.imperfective := by
  fin_cases he <;> first | rfl | exact absurd hs (by decide)

end Russian

end Svenonius2004
