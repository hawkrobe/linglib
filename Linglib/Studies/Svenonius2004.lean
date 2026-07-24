import Mathlib.Tactic.FinCases
import Linglib.Morphology.Word.Tree
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

A prefixed verb is carried as a stem plus a surface-ordered list of
classified prefixes; its word-formation tree (`Morphology.Word.Tree`) and
orthographic form are **derived**, so concatenative and kind-coherent
structure holds by construction. Stem aspect reuses
`Semantics.Aspect.ViewpointAspectB` (`none` = aspectless stems, cf.
[istratkova-2004]'s homogeneous simplex class).

## Main definitions

* `SuperlexicalSubtype` — a selection of the superlexical Aktionsart
  subtypes recurring in the paper's §4 and in [istratkova-2004]; not a
  closed inventory (the Bulgarian ordering in his (57) also lists
  excessive *raz-*).
* `PrefixClass` — `lexical` or `superlexical _`, with the
  `IsSuperlexical` predicate.
* `PrefixedVerb` — the shared carrier (also used by
  `Studies/Istratkova2004.lean` and `Studies/Jablonska2004.lean`), with
  derived `tree` and `form`.
* `WellStacked` — no lexical prefix outside a superlexical one (§1:
  "the superlexical prefix always appears outside the lexical prefix").
* `Russian.inventory` — six canonical Russian entries.

## Main results

* `tree_isConcatenative`, `tree_isKindCoherent` — every derived tree is
  concatenative and kind-coherent, by construction.
* `Russian.stemAspect_imperfective_of_isSuperlexical` — the paper's
  diagnostic (56c) (§4.1): superlexical prefixes select imperfective
  stems.
-/

namespace Svenonius2004

open Morphology (Morph)
open Morphology.Word (Tree)
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

/-- A prefixed-verb lexical entry: a stem plus a surface-ordered
    (outermost-first) list of classified prefixes. The word-formation
    tree and orthographic form are derived (`tree`, `form`), not
    stipulated. -/
structure PrefixedVerb where
  /-- Bare verb stem (citation form). -/
  stem          : String
  /-- Viewpoint aspect of the bare stem; `none` for aspectless stems
      ([istratkova-2004]'s homogeneous simplex class). -/
  stemAspect    : Option ViewpointAspectB
  /-- Classified prefixes in surface order, outermost first. -/
  prefixes      : List (String × PrefixClass)
  /-- Gloss of the bare stem. -/
  baseGloss     : String
  /-- Gloss of the prefixed verb. -/
  prefixedGloss : String

namespace PrefixedVerb

/-- The word-formation tree: the prefixes folded, innermost-last, over
    the root. -/
def tree (e : PrefixedVerb) : Tree Morph :=
  e.prefixes.foldr (fun p t => .prefixed (Morph.pref p.1) t)
    (.root (Morph.root e.stem))

/-- The orthographic form: the concatenation of the prefix morphs and
    the stem. Inventories deliberately avoid voicing-assimilation
    prefixes (*iz-*, *raz-*, *voz-*, *bez-*) whose surface form is not
    the plain concatenation. -/
def form (e : PrefixedVerb) : String :=
  String.join (e.tree.toList.map Morph.form)

/-- Every derived tree is concatenative: prefixation only. -/
theorem tree_isConcatenative (e : PrefixedVerb) :
    e.tree.IsConcatenative := by
  unfold tree
  induction e.prefixes with
  | nil => trivial
  | cons p ps ih => exact ih

/-- Every derived tree is kind-coherent: prefix morphs on `prefixed`
    nodes, a root morph at the leaf. -/
theorem tree_isKindCoherent (e : PrefixedVerb) :
    e.tree.IsKindCoherent := by
  unfold tree
  induction e.prefixes with
  | nil => exact Or.inl rfl
  | cons p ps ih => exact ⟨rfl, ih⟩

end PrefixedVerb

/-- A prefix sequence (surface order, outermost first) is well-stacked
    when no lexical prefix appears outside a superlexical one —
    [svenonius-2004] §1: "the superlexical prefix always appears
    outside the lexical prefix". -/
def WellStacked (prefixes : List (String × PrefixClass)) : Prop :=
  prefixes.Pairwise fun outer inner =>
    inner.2.IsSuperlexical → outer.2.IsSuperlexical

instance : DecidablePred WellStacked := fun prefixes =>
  inferInstanceAs (Decidable (prefixes.Pairwise fun outer inner =>
    inner.2.IsSuperlexical → outer.2.IsSuperlexical))

/-! ### Russian inventory

Latin transliteration with `'` for the soft-sign infinitive ending. -/

namespace Russian

/-- *za-brosit'* 'kick into / throw into' — lexical *za-*
    ([svenonius-2004] §1 ex. (1a), transparently resultative spatial).
    Built on the perfective stem *brosit'*. -/
def zabrosit : PrefixedVerb where
  stem          := "brosit'"
  stemAspect    := some .perfective
  prefixes      := [("za", .lexical)]
  baseGloss     := "throw"
  prefixedGloss := "throw into, kick into"

/-- *vy-brosit'* 'throw out' — lexical *vy-* (English *out* analogue;
    [svenonius-2004] ex. (4a) uses the secondary imperfective
    *vy-brasyvatj*). Built on the perfective stem *brosit'*. -/
def vybrosit : PrefixedVerb where
  stem          := "brosit'"
  stemAspect    := some .perfective
  prefixes      := [("vy", .lexical)]
  baseGloss     := "throw"
  prefixedGloss := "throw out"

/-- *pri-nesti* 'bring (carry to)' — lexical *pri-* (allative). The
    lex classification of *pri-* is from the broader Slavicist
    literature ([romanova-2004]; [babko-malaya-2003]) — [svenonius-2004]
    does not work *pri-* as an example. Built on the imperfective
    determinate-motion stem *nesti*. -/
def prinesti : PrefixedVerb where
  stem          := "nesti"
  stemAspect    := some .imperfective
  prefixes      := [("pri", .lexical)]
  baseGloss     := "carry"
  prefixedGloss := "bring (carry to)"

/-- *za-brosat'* 'start throwing' — superlexical *za-* INCP
    ([svenonius-2004] §1 ex. (1c)). Minimal pair with `zabrosit` on the
    same morpheme but different class. Built on the imperfective stem
    *brosat'*. Stress distinguishes it from the homographic
    *zabrosát'* 'pelt (with)'. -/
def zabrosatInceptive : PrefixedVerb where
  stem          := "brosat'"
  stemAspect    := some .imperfective
  prefixes      := [("za", .superlexical .inceptive)]
  baseGloss     := "throw"
  prefixedGloss := "start throwing"

/-- *po-sidet'* 'sit for a while' — superlexical *po-* DLMT (canonical
    delimitative; [svenonius-2004] (57c) labels Bulgarian *po-* DLMT).
    Built on the imperfective stem *sidet'*. -/
def posidet : PrefixedVerb where
  stem          := "sidet'"
  stemAspect    := some .imperfective
  prefixes      := [("po", .superlexical .delimitative)]
  baseGloss     := "sit"
  prefixedGloss := "sit for a while"

/-- *do-pisat'* 'finish writing' — superlexical *do-* CMPL. Note:
    *do-* is the standard Russian completive in the broader Slavicist
    literature; [svenonius-2004] §4 takes Bulgarian *iz-* as the
    canonical completive instead. Built on the imperfective stem
    *pisat'*. -/
def dopisat : PrefixedVerb where
  stem          := "pisat'"
  stemAspect    := some .imperfective
  prefixes      := [("do", .superlexical .completive)]
  baseGloss     := "write"
  prefixedGloss := "finish writing"

/-- The canonical inventory: three lexical entries plus three
    superlexical entries (with the `zabrosit` / `zabrosatInceptive`
    minimal pair on *za-*). -/
def inventory : List PrefixedVerb :=
  [zabrosit, vybrosit, prinesti, zabrosatInceptive, posidet, dopisat]

-- The derived form matches the attested orthographic word.
example : zabrosit.form = "zabrosit'" := rfl

/-- [svenonius-2004]'s diagnostic (56c) (§4.1): a superlexical entry
    has an imperfective bare stem. Lexical entries are unconstrained. -/
theorem stemAspect_imperfective_of_isSuperlexical
    (e : PrefixedVerb) (he : e ∈ inventory)
    (hs : ∃ p ∈ e.prefixes, p.2.IsSuperlexical) :
    e.stemAspect = some ViewpointAspectB.imperfective := by
  fin_cases he <;> first | rfl | exact absurd hs (by decide)

end Russian

end Svenonius2004
