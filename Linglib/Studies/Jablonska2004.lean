import Linglib.Studies.Svenonius2004

/-!
# Jabłońska (2004): When the Prefixes Meet the Suffixes

[jablonska-2004] specialises the lexical / superlexical distinction of
[svenonius-2004] to Polish. Her central claim: the interpretation of
superlexical *po-* (delimitative vs distributive vs inchoative Degree
Achievement) is **verbalizer-sensitive** — it depends on the embedded
verbalizer suffix, with a common semantic denominator across the
readings. Her fn. 2 notes that *na-* patterns with *po-* in its ability
to stack (to occur in Asp3), the zone above the Secondary Imperfective.

Entries use the shared carrier `Svenonius2004.PrefixedVerb`.

## Main definitions

* `inventory` — six canonical Polish entries covering the
  lexical / superlexical split (Polish orthography with diacritics).

## Main results

* `stemAspect_imperfective_of_isSuperlexical` — [svenonius-2004]'s
  diagnostic (56c) (§4.1) verified across the inventory.
-/

namespace Jablonska2004

open Semantics.Aspect (ViewpointAspectB)
open Svenonius2004 (PrefixedVerb)

/-! ### Lexical entries -/

/-- *na-pisać* 'write (to completion)' — *na-* as the standard
    perfectivizer of *pisać*, classified lexical in the
    [svenonius-2004] framework (pure perfectivizers pattern with
    low, R-head prefixes). [jablonska-2004]'s own fn. 2 diverges,
    grouping *na-* with *po-* as Asp3-stackable. Built on the
    imperfective stem *pisać*. -/
def napisac : PrefixedVerb where
  stem          := "pisać"
  stemAspect    := some .imperfective
  prefixes      := [("na", .lexical)]
  baseGloss     := "write"
  prefixedGloss := "write (to completion)"

/-- *wy-pisać* 'write out, copy out' — lexical *wy-* (spatial 'out',
    Polish counterpart of Russian *vy-*). Built on the imperfective
    stem *pisać*. -/
def wypisac : PrefixedVerb where
  stem          := "pisać"
  stemAspect    := some .imperfective
  prefixes      := [("wy", .lexical)]
  baseGloss     := "write"
  prefixedGloss := "write out, copy out"

/-- *przy-nieść* 'bring (carry to)' — lexical *przy-* (allative,
    Polish counterpart of Russian *pri-*). Built on the imperfective
    determinate-motion stem *nieść*. -/
def przyniesc : PrefixedVerb where
  stem          := "nieść"
  stemAspect    := some .imperfective
  prefixes      := [("przy", .lexical)]
  baseGloss     := "carry"
  prefixedGloss := "bring (carry to)"

/-! ### Superlexical entries -/

/-- *za-śpiewać* 'start singing' — superlexical *za-* INCP (Polish
    counterpart of Russian *za-* on the inceptive reading). Built on
    the imperfective stem *śpiewać*. -/
def zaspiewacInceptive : PrefixedVerb where
  stem          := "śpiewać"
  stemAspect    := some .imperfective
  prefixes      := [("za", .superlexical .inceptive)]
  baseGloss     := "sing"
  prefixedGloss := "start singing"

/-- *po-siedzieć* 'sit for a while' — superlexical *po-* DLMT.
    [jablonska-2004]'s central topic: with imperfective high
    verbalizers *po-* gives the delimitative reading shown here.
    Built on the imperfective stem *siedzieć*. -/
def posiedziec : PrefixedVerb where
  stem          := "siedzieć"
  stemAspect    := some .imperfective
  prefixes      := [("po", .superlexical .delimitative)]
  baseGloss     := "sit"
  prefixedGloss := "sit for a while"

/-- *prze-czytać* 'read through, read completely' — superlexical
    *prze-* CMPL (completive 'through, all the way'; cf. Bulgarian
    *iz-*, [svenonius-2004]'s canonical completive). Built on the
    imperfective stem *czytać*. -/
def przeczytac : PrefixedVerb where
  stem          := "czytać"
  stemAspect    := some .imperfective
  prefixes      := [("prze", .superlexical .completive)]
  baseGloss     := "read"
  prefixedGloss := "read through, read completely"

/-- The canonical inventory: 3 lexical, 3 superlexical. -/
def inventory : List PrefixedVerb :=
  [napisac, wypisac, przyniesc, zaspiewacInceptive, posiedziec, przeczytac]

/-! ### Properties -/

-- The derived form matches the attested orthographic word.
example : przeczytac.form = "przeczytać" := rfl

/-- [svenonius-2004]'s diagnostic (56c) (§4.1): superlexical entries
    select imperfective stems. (Every Polish entry here, lexical
    included, has an imperfective stem, so the hypothesis is unused.) -/
theorem stemAspect_imperfective_of_isSuperlexical
    (e : PrefixedVerb) (he : e ∈ inventory)
    (_hs : ∃ p ∈ e.prefixes, p.2.IsSuperlexical) :
    e.stemAspect = some ViewpointAspectB.imperfective := by
  fin_cases he <;> rfl

end Jablonska2004
