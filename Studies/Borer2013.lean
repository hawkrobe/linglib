module

public import Linglib.Data.Examples.Borer2013
public import Linglib.Syntax.Minimalist.Category.FunctionalSequence

/-!
# Borer (2013): Structuring Sense: Volume III: Taking Form

A category-less root takes its category from the extended projection above it, so *dance* is a noun
under a determiner and a verb under infinitival *to*, with nothing added to it. Such roots never
occur as adjectives (*too dance*), and the words that occur as adjectives occur neither as nouns nor
as verbs (*a green*, *to green*). Distributed Morphology categorizes a root by a head *n*, *v* or
*a* that may be null, so it has to rule each pairing of a root with a head in or out. Borer's
resolution is that adjectives are not roots. Like derivatives they are born categorized, and a
categorized core fits only the extended projection of its own category, while the adjectival
extended projection cannot categorize a root. This file formalizes the resolution and derives from
it every judgment of the paradigm that poses the puzzle.

## Main statements

* `licenses_nominal_and_verbal_iff`: roots, and roots alone, occur both as nouns and as verbs.
* `Licenses.eq_adjectival`: a core that occurs as an adjective occurs in no other extended
  projection.
* `acceptable_iff_licensed`: the lexicon and the licensing condition derive every judgment of the
  paradigm.
* `exists_ne_of_verbal_of_adjectival`: a word that is both a verb and an adjective is listed
  twice, as *thin* and *yellow* are.

## Implementation notes

* The category of a core is an `Option CatFamily`, `none` for a root, and an example's frame is
  the family of the extended projection it builds: nominal under *a* and *the*, verbal under *to*,
  adjectival under *too*. The adpositional extended projection is taken not to categorize roots,
  which the paradigm does not test.
* The verbal *thin* and *yellow* are listed as categorized verbs, since as roots they would be
  nouns as well.

## TODO

The chapter supports the resolution with inflection and affixation: adjectives show none of the
stem allomorphy or root-selected affixes that roots allow, taking only the regular *-er* and
*-est* and the default nominalizers *-ness* and *-ity*. The verbs *clarify* and *enlarge*, built
on underived adjectives, are left as a problem for it. Neither is formalized.

## References

* [borer-2013]
-/

@[expose] public section

namespace Borer2013

open Minimalist

/-! ### Categorization by the extended projection -/

/-- `Licenses e κ` says that the extended projection of family `e` takes a core of category `κ`,
where `none` is a category-less root. A categorized core fits only the extended projection of its
own category, and a root becomes a noun or a verb in its extended projection, but the adjectival
one cannot make it an adjective. -/
def Licenses (e : CatFamily) : Option CatFamily → Prop
  | some c => c = e
  | none => e = .nominal ∨ e = .verbal

instance (e : CatFamily) : DecidablePred (Licenses e)
  | some c => inferInstanceAs (Decidable (c = e))
  | none => inferInstanceAs (Decidable (e = .nominal ∨ e = .verbal))

variable {e : CatFamily} {κ : Option CatFamily}

@[simp] theorem licenses_some {c : CatFamily} : Licenses e (some c) ↔ c = e := Iff.rfl

@[simp] theorem licenses_none : Licenses e none ↔ e = .nominal ∨ e = .verbal := Iff.rfl

/-- Roots, and roots alone, occur both as nouns and as verbs. -/
theorem licenses_nominal_and_verbal_iff :
    Licenses .nominal κ ∧ Licenses .verbal κ ↔ κ = none := by
  cases κ <;> grind [Licenses]

/-- A core that occurs as an adjective occurs in no other extended projection, since the
adjectival extended projection takes no root and an adjective is categorized. -/
theorem Licenses.eq_adjectival (hA : Licenses .adjectival κ) (h : Licenses e κ) :
    e = .adjectival := by
  cases κ <;> simp_all

/-- A word that is both a verb and an adjective is listed under two categories, since no core is
licensed in both extended projections. The verbal uses of *thin* and *yellow* cannot be predicted
from their adjectival ones and must be listed (fn. 39). -/
theorem exists_ne_of_verbal_of_adjectival {l : List (Option CatFamily)}
    (hV : ∃ κ ∈ l, Licenses .verbal κ) (hA : ∃ κ ∈ l, Licenses .adjectival κ) :
    ∃ κ ∈ l, ∃ κ' ∈ l, κ ≠ κ' := by
  obtain ⟨κ, hκ, hV⟩ := hV
  obtain ⟨κ', hκ', hA⟩ := hA
  exact ⟨κ, hκ, κ', hκ', by rintro rfl; cases hA.eq_adjectival hV⟩

/-! ### The paradigm -/

/-- The words of the paradigm, each with the category of a core it is listed as. The roots are
category-less, the adjectives are born categorized, and *thin* and *yellow* are listed again as
verbs. -/
def lexicon : List (String × Option CatFamily) :=
  [("dance", none), ("jump", none), ("walk", none), ("table", none), ("chair", none),
    ("wardrobe", none), ("question", none), ("mean", some .adjectival),
    ("green", some .adjectival), ("fat", some .adjectival), ("tall", some .adjectival),
    ("smart", some .adjectival), ("wide", some .adjectival), ("big", some .adjectival),
    ("thin", some .adjectival), ("thin", some .verbal), ("yellow", some .adjectival),
    ("yellow", some .verbal)]

/-- The categories a word is listed under. -/
def categories (w : String) : List (Option CatFamily) :=
  lexicon.filterMap fun p ↦ if p.1 = w then some p.2 else none

/-- A row records the extended projection an example puts its word in, the categories of the
cores the word is listed as, and the judgment. -/
structure Row where
  frame : CatFamily
  cores : List (Option CatFamily)
  judgment : Judgment

/-- The row of an example whose word is listed. -/
def Row.ofDatum (d : Datum) : Option Row := do
  let frame ← d.parse? "frame"
    [("nominal", CatFamily.nominal), ("verbal", .verbal), ("adjectival", .adjectival)]
  let cats := categories (← d.feature? "item")
  guard (cats ≠ [])
  pure ⟨frame, cats, d.judgment⟩

/-- The examples. -/
def data : List Row := Examples.all.filterMap Row.ofDatum

/-- Every example has its row, so every word of the paradigm is listed. -/
theorem data_length : data.length = Examples.all.length := by decide +kernel

/-- An example is acceptable exactly when its word is listed as a core that fits the extended
projection the example puts it in: *a dance*, *to dance* and *too green* are acceptable, and
*too dance*, *a green* and *to green* are not. -/
theorem acceptable_iff_licensed :
    ∀ d ∈ data, d.judgment = .acceptable ↔ ∃ κ ∈ d.cores, Licenses d.frame κ := by
  decide +kernel

end Borer2013
