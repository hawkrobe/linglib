module

public import Linglib.Syntax.Case.Alignment
public import Linglib.Morphology.Morph

/-!
# Tanti Dargwa case

This file defines the grammatical cases of Tanti Dargwa as Sumbatova describes them. A noun has
a direct stem, its absolutive singular, and an oblique stem, the direct stem with *-li*, which
is its ergative singular and the base of most other forms. The dative and the comitative add
their suffix to the oblique stem, as do the locative forms of `Locatives.lean`, while the
absolutive and the adverbial are built on the direct stem. Tanti has the absolutive, ergative,
genitive, dative and comitative of most Dargwa varieties and an adverbial case of nominal and
secondary predicates besides, which goes under the comparative label of the essive. The
alignment is ergative without a split, A ergative and S and P absolutive.

## Main definitions

* `Dargwa.Case.obliqueStem`: the oblique stem suffix *-li*
* `Dargwa.Case.exponent`: the suffixes of a case after the direct stem, `none` for a case
  Tanti lacks
* `Dargwa.Case.inventory`: the cases, those with an exponent
* `Dargwa.Case.marking`: the ergative marking of the core arguments

## Main results

* `Dargwa.Case.builtOnOblique_iff`: the ergative, dative and comitative are the cases built
  on the oblique stem

## Implementation notes

* The genitive is *-la*, or *-lla* for some nouns, and for some nouns is built on the oblique
  stem; the exponent records the *-la* of *dubur-la* 'mountain's'. The plural builds its
  oblique forms on an oblique plural stem, the absolutive plural with *-a*, which is not
  treated.

## References

* [N. Sumbatova, *Dargwa* (2021)][sumbatova-2021]
-/

@[expose] public section

namespace Dargwa.Case

open Morphology

/-- The oblique stem suffix *-li*. The oblique singular stem is the direct stem with it, and
is the ergative singular. -/
def obliqueStem : Morph := .suff "li"

/-- The suffixes of a case after the direct singular stem. The absolutive is unmarked, the
ergative is the oblique stem, the genitive takes *-la*, the dative *-ž* and the comitative
*-cːele* on the oblique stem, and the adverbial, the essive under its comparative label,
*-le*. -/
def exponent : Case → Option (List Morph)
  | .abs => some []
  | .erg => some [obliqueStem]
  | .gen => some [.suff "la"]
  | .dat => some [obliqueStem, .suff "ž"]
  | .com => some [obliqueStem, .suff "cːele"]
  | .ess => some [.suff "le"]
  | _ => none

/-- The cases of Tanti, those with an exponent. -/
def inventory : Finset Case := Finset.univ.filter fun c ↦ (exponent c).isSome

/-- A case is built on the oblique stem when its exponent begins with the stem suffix. -/
def BuiltOnOblique (c : Case) : Prop := (exponent c).bind List.head? = some obliqueStem

instance : DecidablePred BuiltOnOblique := fun c ↦ by unfold BuiltOnOblique; infer_instance

/-- The ergative, dative and comitative are the cases built on the oblique stem. -/
theorem builtOnOblique_iff (c : Case) :
    BuiltOnOblique c ↔ c = .erg ∨ c = .dat ∨ c = .com := by
  cases c <;> decide

/-- The marking of the core arguments is ergative, A ergative and S and P absolutive, with no
split by tense or aspect. -/
abbrev marking : ArgumentRole → Case := Alignment.ergative

end Dargwa.Case
