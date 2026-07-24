import Linglib.Studies.Svenonius2004

/-!
# Istratkova (2004): On Multiple Prefixation in Bulgarian

[istratkova-2004] documents the Bulgarian-distinctive feature of
**multiple prefixation**: up to seven prefixes can stack on a single
verbal root, with superlexical prefixes systematically appearing outside
lexical ones and outer prefixes taking scope over inner ones. Prefixes
attach to both perfective and imperfective stems — they don't uniformly
mark perfectivity — and the large class of simplex *homogeneous* verbs
(her ex. (2): *misl'a* 'think', *piša* 'write', *četa* 'read', ...) has
no perfective counterparts and "remains aspectless", behaving as
imperfective only by default; `stemAspect` is accordingly
`Option`-typed, with `none` for these.

Her *po-* taxonomy distinguishes three superlexical *po-*'s:
delimitative ('for a while', which does not stack), distributive
(occurring only after *iz-*), and attenuative ('to a low degree', the
one that stacks over other superlexicals). [svenonius-2004]'s §1 ex. (3)
glosses the *po-* of *po-na-razkaža* as DLMT; on her own taxonomy it is
the attenuative *po-* (her (23c) *po-na-prodam* 'sell a few things'),
and the entries below follow her labels.

## Main definitions

* `PrefixedVerbEntry` — carries `prefixChain : List (String × PrefixClass)`
  in surface (outermost-first) order to support multi-prefixation, and an
  `Option`-typed `stemAspect` (`none` = aspectless homogeneous simplex).
* `inventory` — eight entries: four single-prefix lexical, two
  single-prefix superlexical, two multi-prefix.

## Main results

* `inventory_transparent_concat` — every entry's `prefixedForm` is the
  literal concatenation of its prefix chain followed by `bareStem`.
* `inventory_wellStacked` — no lexical prefix appears outside a
  superlexical one, the structural invariant of her stacking data
  (echoed by [svenonius-2004] §1: "the superlexical prefix always
  appears outside the lexical prefix").
-/

namespace Istratkova2004

open Semantics.Aspect (ViewpointAspectB)
open Svenonius2004 (PrefixClass)

/-- A Bulgarian prefixed-verb entry. The `prefixChain` lists
    `(morpheme, class)` pairs in **surface order** (outermost /
    leftmost first), supporting multi-prefixation. Citation forms are
    first-person singular present, as in the paper (Bulgarian has no
    infinitive). -/
structure PrefixedVerbEntry where
  /-- Bare verb stem (1sg present citation form). -/
  bareStem      : String
  /-- Viewpoint aspect of the bare stem; `none` for the aspectless
      homogeneous simplex verbs of [istratkova-2004] ex. (2). -/
  stemAspect    : Option ViewpointAspectB
  /-- Surface-order list of `(morpheme, class)` pairs. -/
  prefixChain   : List (String × PrefixClass)
  /-- The fully prefixed form (concatenation of all prefixes followed
      by `bareStem`). -/
  prefixedForm  : String
  /-- Gloss of the bare stem. -/
  baseGloss     : String
  /-- Gloss of the prefixed form. -/
  prefixedGloss : String

/-! ### Single-prefix lexical entries -/

/-- *za-piša* 'write down, note' — lexical *za-* on the homogeneous
    simplex *piša* 'write' ([istratkova-2004] exx. (1a), (2f)). -/
def zapisa : PrefixedVerbEntry where
  bareStem      := "piša"
  stemAspect    := none
  prefixChain   := [("za", .lexical)]
  prefixedForm  := "zapiša"
  baseGloss     := "write"
  prefixedGloss := "write down"

/-- *iz-misl'a* 'make up (a story)' — lexical *iz-* with idiosyncratic
    meaning shift on the homogeneous simplex *misl'a* 'think'
    ([istratkova-2004] exx. (3a), (2a)). -/
def izmisla : PrefixedVerbEntry where
  bareStem      := "misl'a"
  stemAspect    := none
  prefixChain   := [("iz", .lexical)]
  prefixedForm  := "izmisl'a"
  baseGloss     := "think"
  prefixedGloss := "make up (a story)"

/-- *po-znam* 'guess' — lexical *po-* on the homogeneous simplex *znam*
    'know' ([istratkova-2004] exx. (3c), (2c)). The fully idiosyncratic
    meaning is [svenonius-2004]'s own lexicality diagnostic; her ex. (3)
    lists the perfective-imperfective pair without a superlexical
    label. -/
def poznam : PrefixedVerbEntry where
  bareStem      := "znam"
  stemAspect    := none
  prefixChain   := [("po", .lexical)]
  prefixedForm  := "poznam"
  baseGloss     := "know"
  prefixedGloss := "guess"

/-- *pro-četa* 'read completely' — lexical (quantizing) *pro-* on the
    homogeneous simplex *četa* 'read' ([istratkova-2004] exx. (3i),
    (2h)). *pro-* is not in her superlexical inventory; the prefixed
    form is the default perfectivization of *četa*. -/
def procheta : PrefixedVerbEntry where
  bareStem      := "četa"
  stemAspect    := none
  prefixChain   := [("pro", .lexical)]
  prefixedForm  := "pročeta"
  baseGloss     := "read"
  prefixedGloss := "read completely"

/-! ### Single-prefix superlexical entries -/

/-- *za-blest'a* 'start to glitter' — superlexical *za-* INCP ('to
    begin' in her prefix taxonomy) on the homogeneous simplex *blest'a*
    'glitter' ([istratkova-2004] exx. (3d), (2d)). -/
def zablesta : PrefixedVerbEntry where
  bareStem      := "blest'a"
  stemAspect    := none
  prefixChain   := [("za", .superlexical .inceptive)]
  prefixedForm  := "zablest'a"
  baseGloss     := "glitter"
  prefixedGloss := "start to glitter"

/-- *za-običam* 'start to love' — superlexical *za-* INCP on the
    homogeneous simplex *običam* 'love' ([istratkova-2004] exx. (3b),
    (2b)). -/
def zaobicham : PrefixedVerbEntry where
  bareStem      := "običam"
  stemAspect    := none
  prefixChain   := [("za", .superlexical .inceptive)]
  prefixedForm  := "zaobičam"
  baseGloss     := "love"
  prefixedGloss := "start to love"

/-! ### Multi-prefix entries

The distinctive Bulgarian feature: superlexical prefixes stack outside
each other (and outside any lexical prefix), outermost taking widest
scope. The stem *razkaža* 'narrate' (etymologically *raz-kaža*
'around-say') is itself quantized and perfective. -/

/-- *po-na-razkaža* 'tell a little of many' — attenuative *po-* over
    cumulative *na-* ([istratkova-2004] §4; cited as ex. (3a) by
    [svenonius-2004] p. 206, who glosses the *po-* DLMT — on her
    taxonomy the stacking *po-* is attenuative, cf. her (23c)). -/
def ponarazkaza : PrefixedVerbEntry where
  bareStem      := "razkaža"
  stemAspect    := some .perfective
  prefixChain   :=
    [("po", .superlexical .attenuative),
     ("na", .superlexical .cumulative)]
  prefixedForm  := "ponarazkaža"
  baseGloss     := "narrate"
  prefixedGloss := "tell a little of many"

/-- *iz-po-na-pre-razkaža* 'renarrate completely one by one, of many' —
    a four-superlexical stack: completive *iz-*, distributive *po-*
    (the *po-* occurring after *iz-* in her taxonomy), cumulative
    *na-*, repetitive *pre-* ([svenonius-2004] §1 ex. (3e), from her
    data). -/
def izponaprerazkaza : PrefixedVerbEntry where
  bareStem      := "razkaža"
  stemAspect    := some .perfective
  prefixChain   :=
    [("iz", .superlexical .completive),
     ("po", .superlexical .distributive),
     ("na", .superlexical .cumulative),
     ("pre", .superlexical .repetitive)]
  prefixedForm  := "izponaprerazkaža"
  baseGloss     := "narrate"
  prefixedGloss := "renarrate completely one by one, of many"

/-- The canonical inventory: 4 single-lex + 2 single-superlex + 2
    multi-prefix. -/
def inventory : List PrefixedVerbEntry :=
  [zapisa, izmisla, poznam, procheta, zablesta, zaobicham,
   ponarazkaza, izponaprerazkaza]

/-! ### Properties -/

/-- The concatenation of all prefix morphemes in the chain (surface
    order: leftmost first). -/
def PrefixedVerbEntry.prefixString (e : PrefixedVerbEntry) : String :=
  e.prefixChain.foldl (fun acc p => acc ++ p.1) ""

/-- An entry's `prefixedForm` is the literal concatenation of its
    prefix chain (in surface order) followed by `bareStem`. -/
def IsTransparentConcat (e : PrefixedVerbEntry) : Prop :=
  e.prefixedForm = e.prefixString ++ e.bareStem

instance : DecidablePred IsTransparentConcat :=
  fun e => decEq e.prefixedForm (e.prefixString ++ e.bareStem)

/-- A prefix chain (surface order, outermost first) is well-stacked
    when no lexical prefix appears outside a superlexical one —
    [istratkova-2004]'s structural stacking invariant. -/
def WellStacked (chain : List (String × PrefixClass)) : Prop :=
  chain.Pairwise fun outer inner =>
    inner.2.IsSuperlexical → outer.2.IsSuperlexical

instance : DecidablePred WellStacked := fun chain =>
  inferInstanceAs (Decidable (chain.Pairwise fun outer inner =>
    inner.2.IsSuperlexical → outer.2.IsSuperlexical))

/-- Every inventory entry is a transparent concatenation. -/
theorem inventory_transparent_concat
    (e : PrefixedVerbEntry) (he : e ∈ inventory) :
    IsTransparentConcat e := by
  fin_cases he <;> rfl

/-- Every inventory entry is well-stacked: superlexical prefixes sit
    outside lexical ones, never the reverse. -/
theorem inventory_wellStacked
    (e : PrefixedVerbEntry) (he : e ∈ inventory) :
    WellStacked e.prefixChain := by
  fin_cases he <;> decide

end Istratkova2004
