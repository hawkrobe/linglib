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
imperfective only by default; such stems carry `stemAspect := none`.

Her *po-* taxonomy distinguishes three superlexical *po-*'s:
delimitative ('for a while', which does not stack), distributive
(occurring only after *iz-*), and attenuative ('to a low degree', the
one that stacks over other superlexicals). [svenonius-2004]'s §1 ex. (3)
glosses the *po-* of *po-na-razkaža* as DLMT; on her own taxonomy it is
the attenuative *po-* (her (23c) *po-na-prodam* 'sell a few things'),
and the entries below follow her labels.

Entries use the shared carrier `Svenonius2004.PrefixedVerb`; multi-prefix
verbs are entries whose `prefixes` list has more than one element, and
their word-formation trees and forms are derived.

## Main definitions

* `inventory` — eight entries: four single-prefix lexical, two
  single-prefix superlexical, two multi-prefix.

## Main results

* `inventory_wellStacked` — every entry satisfies
  `Svenonius2004.WellStacked`: no lexical prefix appears outside a
  superlexical one, the structural invariant of her stacking data.
-/

namespace Istratkova2004

open Svenonius2004 (PrefixedVerb WellStacked)

/-! ### Single-prefix lexical entries

Citation forms are first-person singular present, as in the paper
(Bulgarian has no infinitive). -/

/-- *za-piša* 'write down, note' — lexical *za-* on the homogeneous
    simplex *piša* 'write' ([istratkova-2004] exx. (1a), (2f)). -/
def zapisa : PrefixedVerb where
  stem          := "piša"
  stemAspect    := none
  prefixes      := [("za", .lexical)]
  baseGloss     := "write"
  prefixedGloss := "write down"

/-- *iz-misl'a* 'make up (a story)' — lexical *iz-* with idiosyncratic
    meaning shift on the homogeneous simplex *misl'a* 'think'
    ([istratkova-2004] exx. (3a), (2a)). -/
def izmisla : PrefixedVerb where
  stem          := "misl'a"
  stemAspect    := none
  prefixes      := [("iz", .lexical)]
  baseGloss     := "think"
  prefixedGloss := "make up (a story)"

/-- *po-znam* 'guess' — lexical *po-* on the homogeneous simplex *znam*
    'know' ([istratkova-2004] exx. (3c), (2c)). The fully idiosyncratic
    meaning is [svenonius-2004]'s own lexicality diagnostic; her ex. (3)
    lists the perfective-imperfective pair without a superlexical
    label. -/
def poznam : PrefixedVerb where
  stem          := "znam"
  stemAspect    := none
  prefixes      := [("po", .lexical)]
  baseGloss     := "know"
  prefixedGloss := "guess"

/-- *pro-četa* 'read completely' — lexical (quantizing) *pro-* on the
    homogeneous simplex *četa* 'read' ([istratkova-2004] exx. (3i),
    (2h)). *pro-* is not in her superlexical inventory; the prefixed
    form is the default perfectivization of *četa*. -/
def procheta : PrefixedVerb where
  stem          := "četa"
  stemAspect    := none
  prefixes      := [("pro", .lexical)]
  baseGloss     := "read"
  prefixedGloss := "read completely"

/-! ### Single-prefix superlexical entries -/

/-- *za-blest'a* 'start to glitter' — superlexical *za-* INCP ('to
    begin' in her prefix taxonomy) on the homogeneous simplex *blest'a*
    'glitter' ([istratkova-2004] exx. (3d), (2d)). -/
def zablesta : PrefixedVerb where
  stem          := "blest'a"
  stemAspect    := none
  prefixes      := [("za", .superlexical .inceptive)]
  baseGloss     := "glitter"
  prefixedGloss := "start to glitter"

/-- *za-običam* 'start to love' — superlexical *za-* INCP on the
    homogeneous simplex *običam* 'love' ([istratkova-2004] exx. (3b),
    (2b)). -/
def zaobicham : PrefixedVerb where
  stem          := "običam"
  stemAspect    := none
  prefixes      := [("za", .superlexical .inceptive)]
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
def ponarazkaza : PrefixedVerb where
  stem          := "razkaža"
  stemAspect    := some .perfective
  prefixes      :=
    [("po", .superlexical .attenuative),
     ("na", .superlexical .cumulative)]
  baseGloss     := "narrate"
  prefixedGloss := "tell a little of many"

/-- *iz-po-na-pre-razkaža* 'renarrate completely one by one, of many' —
    a four-superlexical stack: completive *iz-*, distributive *po-*
    (the *po-* occurring after *iz-* in her taxonomy), cumulative
    *na-*, repetitive *pre-* ([svenonius-2004] §1 ex. (3e), from her
    data). -/
def izponaprerazkaza : PrefixedVerb where
  stem          := "razkaža"
  stemAspect    := some .perfective
  prefixes      :=
    [("iz", .superlexical .completive),
     ("po", .superlexical .distributive),
     ("na", .superlexical .cumulative),
     ("pre", .superlexical .repetitive)]
  baseGloss     := "narrate"
  prefixedGloss := "renarrate completely one by one, of many"

/-- The canonical inventory: 4 single-lex + 2 single-superlex + 2
    multi-prefix. -/
def inventory : List PrefixedVerb :=
  [zapisa, izmisla, poznam, procheta, zablesta, zaobicham,
   ponarazkaza, izponaprerazkaza]

/-! ### Properties -/

-- The derived form matches the attested orthographic word.
example : izponaprerazkaza.form = "izponaprerazkaža" := rfl

/-- Every inventory entry is well-stacked: superlexical prefixes sit
    outside lexical ones, never the reverse. -/
theorem inventory_wellStacked
    (e : PrefixedVerb) (he : e ∈ inventory) :
    WellStacked e.prefixes := by
  fin_cases he <;> decide

end Istratkova2004
