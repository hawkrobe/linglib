import Linglib.Morphology.MorphRule
import Linglib.Syntax.Reciprocal

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

/-- Lexical reciprocal verbs ([palmieri-2024], Appendix C): *-an-*-formed
    verbs with lexicalized reciprocal entries, diagnosed by singular
    predication (modal embedding, habituality) and affix ordering. The
    binary base is morphologically distinct, sometimes with semantic
    drift (*pambana* 'fight' < *pamba* 'decorate'); *jibizana* lacks a
    binary base altogether (\**jibiza*). -/
def lexicalReciprocals : List LexicalVerb :=
  [ { form := "achana", gloss := "break up, divorce", transitiveAlternate := some "acha" }
  , { form := "gawana", gloss := "share", transitiveAlternate := some "gawa" }
  , { form := "gombana", gloss := "quarrel", transitiveAlternate := some "gomba" }
  , { form := "gongana", gloss := "collide", transitiveAlternate := some "gonga" }
  , { form := "jibizana", gloss := "discuss, talk, dialogue" }
  , { form := "pambana", gloss := "fight, be in conflict", transitiveAlternate := some "pamba" }
  , { form := "patana", gloss := "agree", transitiveAlternate := some "pata" }
  , { form := "pigana", gloss := "fight", transitiveAlternate := some "piga" }
  , { form := "shindana", gloss := "compete", transitiveAlternate := some "shinda" } ]

end Swahili.Reciprocals
