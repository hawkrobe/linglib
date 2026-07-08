import Linglib.Morphology.MorphRule
import Linglib.Syntax.Reciprocal
import Linglib.Fragments.Swahili.Predicates

/-!
# Swahili Reciprocal Fragment
[nordlinger-2023]

Swahili marks reciprocity with the verbal suffix "-an-" (sometimes
"-ana" in final position). This is a verbal affix strategy (monovalent):
it reduces valency by removing the object argument. The reciprocal
participants are encoded as a plural subject.

Example: "pend-" (love) → "pend-an-a" (love each other)
[nordlinger-2023] ex. 40 (citing Dimitriadis 2004).

The reciprocal affix is distinct from the reflexive prefix "ji-".
-/

namespace Swahili.Reciprocals

open Morphology

/-- Swahili reciprocal suffix "-an-" as a morphological rule. -/
def reciprocalAffix : MorphRule Bool :=
  { category := .valence
  , value := "reciprocal"
  , formRule := fun stem => stem ++ "an"
  , featureRule := id
  , valenceRule := fun _ => some ComplementType.none
  , semEffect := id
  }

/-- Swahili reflexive prefix "ji-" (for contrast). -/
def reflexivePrefix : MorphRule Bool :=
  { category := .valence
  , value := "reflexive"
  , formRule := fun stem => "ji" ++ stem
  , featureRule := id
  , valenceRule := fun _ => some ComplementType.none
  , semEffect := id
  }

/-- Reciprocal and reflexive are formally distinct in Swahili. -/
theorem recip_distinct_from_reflexive :
    reciprocalAffix.value ≠ reflexivePrefix.value := by decide

/-- Both are valence-changing operations. -/
theorem both_valence_changing :
    reciprocalAffix.category = .valence ∧
    reflexivePrefix.category = .valence := ⟨rfl, rfl⟩

open Reciprocal

/-- The reciprocal suffix as a typological marker (distinct from the
    reflexive *-ji-*). -/
def anSuffix : Marker :=
  { form := "-an-", strategy := .verbalAffix }

/-- Marker inventory. -/
def markers : List Marker := [anSuffix]

/-- The *-an-* verbs with lexicalized reciprocal entries ([palmieri-2024],
    Appendix C), referenced as ordinary verb entries. -/
def lexicalReciprocals : List Verb :=
  [Predicates.achana, Predicates.gawana, Predicates.gombana,
   Predicates.gongana, Predicates.jibizana, Predicates.pambana,
   Predicates.patana, Predicates.pigana, Predicates.shindana]

/-- Derivational pairing of each lexical reciprocal with its binary base
    ([palmieri-2024], Appendix C). *jibizana* is absent: it has no
    binary base (\**jibiza*). -/
def derivedFrom : List (Verb × Verb) :=
  [(Predicates.achana, Predicates.acha), (Predicates.gawana, Predicates.gawa),
   (Predicates.gombana, Predicates.gomba), (Predicates.gongana, Predicates.gonga),
   (Predicates.pambana, Predicates.pamba), (Predicates.patana, Predicates.pata),
   (Predicates.pigana, Predicates.piga), (Predicates.shindana, Predicates.shinda)]

end Swahili.Reciprocals
