import Linglib.Data.UD.Basic
import Linglib.Syntax.Minimalist.ExtendedProjection.Basic
import Linglib.Syntax.Minimalist.ExtendedProjection.Properties

/-!
# Panagiotidis (2015): Categorial Features

This file formalizes the theory of word class in [panagiotidis-2015]: lexical category is
not a property of roots but of the categorizer heads *n*, *v*, and *a* that category-neutral
roots merge with ([marantz-1997]), and the categorial features those heads bear are
substantive and interpretable rather than diacritic, [N] imposing a sortal perspective and
[V] a perspective extending into time on the root's concept. Nouns bear [N] only, verbs [V]
only, adjectives both, and adpositions neither, the adposition being the default categorizer
(`categorizer_features`, `isCategorizer_iff`). The functional heads of an extended projection
carry uninterpretable copies of their categorizer's features, so a category's features are
fixed by its family (`categorialFeatures_eq_iff`), and the diacritic features of
[chomsky-1970] cut the categories into the same four classes, the substrate's
`Minimalist.chomsky_panagiotidis_agree`. Category change is change of categorizer: an English
root surfaces in all three categorized classes (`RootFamily`, `all_families_tricategorial`).

## Implementation notes

`categorialFeatures` and `catFeatures` live in the extended-projection substrate, which does
not represent the difference between a categorizer's interpretable features and the copies on
its functional heads, so the two feature systems are compared on the partitions they induce.
The root families are the standard English illustrations of category-neutral roots from the
Distributed Morphology literature rather than data from the book.

## References

* [panagiotidis-2015]
* [chomsky-1970]
* [marantz-1997]
-/

namespace Panagiotidis2015

open Minimalist

/-- The features of the lexical categorizers: *n* bears [N], *v* bears [V], *a* both, and the
adposition, the default categorizer, neither. -/
theorem categorizer_features :
    categorialFeatures .n = ⟨true, false⟩ ∧ categorialFeatures .v = ⟨false, true⟩ ∧
      categorialFeatures .a = ⟨true, true⟩ ∧ categorialFeatures .P = ⟨false, false⟩ := by
  decide

/-- The categorizers are exactly *v*, *n*, and *a*; the categorized lexical heads are not
categorizers but root-plus-categorizer complexes. -/
theorem isCategorizer_iff (c : Cat) : isCategorizer c = true ↔ c = .v ∨ c = .n ∨ c = .a := by
  cases c <;> decide

/-- Features are fixed by the extended-projection family: every head of a projection carries
its categorizer's [N] and [V] specification. -/
theorem categorialFeatures_eq_iff (c₁ c₂ : Cat) :
    categorialFeatures c₁ = categorialFeatures c₂ ↔ catFamily c₁ = catFamily c₂ := by
  cases c₁ <;> cases c₂ <;> decide

/-- A category-neutral root with the surface words it projects across the lexical categories,
each stamped with its Universal Dependencies category ([marantz-1997]). -/
structure RootFamily where
  /-- A label for the root; roots themselves are sub-morphemic. -/
  rootLabel : String
  /-- The surface forms with their categories. -/
  forms : List (String × UD.UPOS)

/-- The family has a surface form in category `c`. -/
def RootFamily.HasCategory (rf : RootFamily) (c : UD.UPOS) : Prop :=
  ∃ f ∈ rf.forms, f.2 = c

instance (rf : RootFamily) (c : UD.UPOS) : Decidable (rf.HasCategory c) :=
  List.decidableBEx _ rf.forms

/-- √DESTROY: destroy, destruction, destructive. -/
def destroy : RootFamily :=
  ⟨"DESTROY", [("destroy", .VERB), ("destruction", .NOUN), ("destructive", .ADJ)]⟩

/-- √BEAUTY: beautify, beauty, beautiful. -/
def beauty : RootFamily :=
  ⟨"BEAUTY", [("beautify", .VERB), ("beauty", .NOUN), ("beautiful", .ADJ)]⟩

/-- √CLEAR: clear, clarity, clear. -/
def clear : RootFamily := ⟨"CLEAR", [("clear", .VERB), ("clarity", .NOUN), ("clear", .ADJ)]⟩

/-- √PRODUCE: produce, production, productive. -/
def produce : RootFamily :=
  ⟨"PRODUCE", [("produce", .VERB), ("production", .NOUN), ("productive", .ADJ)]⟩

/-- √CREATE: create, creation, creative. -/
def create : RootFamily :=
  ⟨"CREATE", [("create", .VERB), ("creation", .NOUN), ("creative", .ADJ)]⟩

/-- √ACT: act, action, active. -/
def act : RootFamily := ⟨"ACT", [("act", .VERB), ("action", .NOUN), ("active", .ADJ)]⟩

/-- The sample root families. -/
def allFamilies : List RootFamily := [destroy, beauty, clear, produce, create, act]

/-- Every root in the sample surfaces under each of the three categorizers. -/
theorem all_families_tricategorial :
    ∀ rf ∈ allFamilies, rf.HasCategory .VERB ∧ rf.HasCategory .NOUN ∧ rf.HasCategory .ADJ := by
  decide

end Panagiotidis2015
