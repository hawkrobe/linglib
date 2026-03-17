import Linglib.Core.Lexical.MorphRule

/-!
# Swahili Reciprocal Fragment
@cite{nordlinger-2023}

Swahili marks reciprocity with the verbal suffix "-an-" (sometimes
"-ana" in final position). This is a verbal affix strategy (monovalent):
it reduces valency by removing the object argument. The reciprocal
participants are encoded as a plural subject.

Example: "pend-" (love) → "pend-an-a" (love each other)
@cite{nordlinger-2023} ex. 40 (citing Dimitriadis 2004).

The reciprocal affix is distinct from the reflexive prefix "ji-".
-/

namespace Fragments.Swahili.Reciprocals

open Core.Morphology

/-- Swahili reciprocal suffix "-an-" as a morphological rule. -/
def reciprocalAffix : MorphRule Bool :=
  { category := .valence
  , value := "reciprocal"
  , formRule := fun stem => stem ++ "an"
  , featureRule := fun f => { f with valence := some .intransitive }
  , semEffect := id
  }

/-- Swahili reflexive prefix "ji-" (for contrast). -/
def reflexivePrefix : MorphRule Bool :=
  { category := .valence
  , value := "reflexive"
  , formRule := fun stem => "ji" ++ stem
  , featureRule := fun f => { f with valence := some .intransitive }
  , semEffect := id
  }

/-- Reciprocal and reflexive are formally distinct in Swahili. -/
theorem recip_distinct_from_reflexive :
    reciprocalAffix.value ≠ reflexivePrefix.value := by decide

/-- Both are valence-changing operations. -/
theorem both_valence_changing :
    reciprocalAffix.category = .valence ∧
    reflexivePrefix.category = .valence := ⟨rfl, rfl⟩

end Fragments.Swahili.Reciprocals
