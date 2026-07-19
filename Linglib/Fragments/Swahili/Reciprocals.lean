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

open Reciprocal

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
