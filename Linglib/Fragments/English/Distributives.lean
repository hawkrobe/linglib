import Linglib.Semantics.Plurality.Distributivity

/-!
# English universal determiners

The English determiners *each*, *every* and *all*, with their denotations as the theory-layer
operators and their classification by distributivity and maximality
([haslinger-etal-2025-nllt]). *each* and *every* share a class; they differ in the atomicity
presupposition *each* carries, which blocks *each ten minutes* while allowing *every ten minutes*.

## References

* [haslinger-etal-2025-nllt]
-/

namespace English.Distributives

open Plurality Plurality.Distributivity

variable {Atom W : Type*}

/-- ⟦each⟧: maximal distribution; the atomicity presupposition is a felicity condition. -/
def eachSem (P : Atom → W → Prop) : Finset Atom → W → Prop := distMaximal P

/-- ⟦every⟧: maximal distribution, with only the non-overlap presupposition. -/
def everySem (P : Atom → W → Prop) : Finset Atom → W → Prop := distMaximal P

/-- ⟦all⟧: maximal, without distributive inferences of its own. -/
def allSem (P : Atom → W → Prop) : Finset Atom → W → Prop := distMaximal P

/-- An English universal determiner. -/
structure DistributiveEntry where
  form : String
  gloss : String
  /-- Carries the atomicity presupposition. -/
  atomicityPresup : Bool
  distMaxClass : DistMaxClass
  deriving Repr

def eachEntry : DistributiveEntry :=
  { form := "each", gloss := "each", atomicityPresup := true, distMaxClass := .distMax }

def everyEntry : DistributiveEntry :=
  { form := "every", gloss := "every", atomicityPresup := false, distMaxClass := .distMax }

def allEntry : DistributiveEntry :=
  { form := "all", gloss := "all", atomicityPresup := false, distMaxClass := .nonDistMax }

end English.Distributives
