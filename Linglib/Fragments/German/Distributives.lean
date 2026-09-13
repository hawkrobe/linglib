import Linglib.Semantics.Plurality.Distributivity

/-!
# German distributive expressions

The German distributive items *jeder*, *jeweils* and *alle*, with their denotations as the
theory-layer operators and their syntactic uses ([haslinger-etal-2025]). *jeder* and *jeweils*
are both obligatorily distributive; *jeder* is maximal, while *jeweils* distributes over a
contextually tolerated subplurality and has no determiner use.

## References

* [haslinger-etal-2025]
-/

namespace German.Distributives

open Plurality Plurality.Distributivity

variable {Atom W : Type*}

/-- ⟦jeder⟧: maximal distribution. -/
def jederSem (P : Atom → W → Prop) : Finset Atom → W → Prop := distMaximal P

/-- ⟦jeweils⟧: tolerant distribution with a contextually supplied tolerance. -/
def jeweilsSem (P : Atom → W → Prop) (tol : Tolerance Atom) : Finset Atom → W → Prop :=
  distTolerant P tol

/-- ⟦alle⟧: maximal, without distributive inferences of its own. -/
def alleSem (P : Atom → W → Prop) : Finset Atom → W → Prop := distMaximal P

/-- A German distributive item. -/
structure DistributiveEntry where
  form : String
  gloss : String
  /-- Has a determiner use. -/
  hasDPUse : Bool
  /-- Has a distance-distributive, adverbial use. -/
  hasDistanceUse : Bool
  distMaxClass : DistMaxClass
  deriving Repr

def jederEntry : DistributiveEntry :=
  { form := "jeder", gloss := "every/each", hasDPUse := true, hasDistanceUse := true,
    distMaxClass := .distMax }

def jeweilsEntry : DistributiveEntry :=
  { form := "jeweils", gloss := "each/respectively", hasDPUse := false, hasDistanceUse := true,
    distMaxClass := .distNonMax }

def alleEntry : DistributiveEntry :=
  { form := "alle", gloss := "all", hasDPUse := true, hasDistanceUse := false,
    distMaxClass := .nonDistMax }

end German.Distributives
