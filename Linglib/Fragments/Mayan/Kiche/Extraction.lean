module

public import Linglib.Syntax.Reflex
public import Linglib.Fragments.Mayan.Extraction
public import Linglib.Fragments.Mayan.Kiche.Voice

/-!
# K'iche' extraction marking

K'iche' (K'ichean Mayan) puts the verb in the Agent Focus voice when a transitive subject is
extracted, and adds the fronting particle *wi* to the verbal complex when a locative,
instrument, dative or benefactive phrase is extracted, comitatives too; the particle is
obligatory in the varieties Mendes and Ranero describe and absent or optional in others, and
reasons, purposes, manners and temporals never license it. Absolutive extraction is unmarked.
The benefactive cell records the K'ichean pattern as Elkins, Brown and Torrence summarize it,
which they note varies by variety between datives and benefactives.

## Main declarations

* `Kiche.Extraction.wi`: the fronting particle.
* `Kiche.Extraction.realize`: the reflexes extraction from each `Mayan.ExtractionSite` licenses
  on a verb of each class, the Agent Focus marker taken from `Kiche.agentFocus`.

## References

* [coon-mateo-pedro-preminger-2014]
* [elkins-torrence-brown-2026]
* [mendes-ranero-2021]
* [mondloch-2017]
-/

@[expose] public section

namespace Kiche.Extraction

/-- A K'iche' extraction reflex is hosted by the verb stem or by the verbal complex the
particle *wi* attaches to. -/
inductive Host where
  | verb
  | verbalComplex
  deriving DecidableEq, Repr

/-- The fronting particle *wi*. -/
def wi : Morphology.Morph := .free "wi"

/-- Transitive-subject extraction takes the Agent Focus marker of the verb's class on the verb;
low-adjunct extraction adds *wi* to the verbal complex; everything else is unmarked. -/
def realize (c : Mayan.VerbClass) : Mayan.ExtractionSite → Finset (Reflex Host)
  | .core .A => {.morpheme .verb (agentFocus c).marker}
  | .adjunct .instrument | .adjunct .benefactive | .adjunct .dative | .adjunct .locative =>
      {.morpheme .verbalComplex [wi]}
  | _ => ∅

/-- *wi* is licensed by exactly the low adjunct classes. -/
theorem realize_adjunct_nonempty_iff (c : Mayan.VerbClass) (a : Mayan.Adjunct) :
    (realize c (.adjunct a)).Nonempty ↔
      a = .instrument ∨ a = .benefactive ∨ a = .dative ∨ a = .locative := by
  decide +revert

end Kiche.Extraction
