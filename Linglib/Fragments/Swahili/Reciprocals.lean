import Linglib.Syntax.Reciprocal
import Linglib.Fragments.Swahili.Verbs

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
  [Verbs.achana, Verbs.gawana, Verbs.gombana,
   Verbs.gongana, Verbs.jibizana, Verbs.pambana,
   Verbs.patana, Verbs.pigana, Verbs.shindana]

/-- Derivational pairing of each lexical reciprocal with its binary base
    ([palmieri-2024], Appendix C). *jibizana* is absent: it has no
    binary base (\**jibiza*). -/
def derivedFrom : List (Verb × Verb) :=
  [(Verbs.achana, Verbs.acha), (Verbs.gawana, Verbs.gawa),
   (Verbs.gombana, Verbs.gomba), (Verbs.gongana, Verbs.gonga),
   (Verbs.pambana, Verbs.pamba), (Verbs.patana, Verbs.pata),
   (Verbs.pigana, Verbs.piga), (Verbs.shindana, Verbs.shinda)]

end Swahili.Reciprocals
