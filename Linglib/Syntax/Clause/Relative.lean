import Mathlib.Tactic.DeriveFintype
import Mathlib.Order.Interval.Finset.Defs
import Linglib.Core.Order.OrdConnected
import Linglib.Semantics.Reference.Definiteness
import Linglib.Syntax.GrammaticalRelation

/-!
# Relative clauses: structural core

Theory-neutral types for cross-linguistic relative-clause data: the placement of the clause
relative to its head, what occupies the relativized position (NP_rel), and the `Marker` schema
the fragments instantiate for a language's relative-clause markers. The relativizable positions
are the grammatical relations of `Syntax.GrammaticalRelation`, whose order is
[keenan-comrie-1977]'s Accessibility Hierarchy.

## Main declarations

* `RelativeClause.Placement` — the clause's placement relative to the head noun.
* `RelativeClause.NPRel` — what occupies the relativized position.
* `RelativeClause.Marker` — a relative-clause marker with the positions it relativizes, its
  contiguity `IsContinuous` and the primary-strategy predicate `IsPrimary`.

## Implementation notes

The accessibility order is that of `Syntax.GrammaticalRelation`, so a strategy's contiguity
(Keenan and Comrie's second Hierarchy Constraint) is order-connectedness of the set it covers,
and the Primary Relativization Constraint is `Finset.eq_Icc_top_of_ordConnected_coe` on that
set. The positions a marker covers are a `Finset`, since only membership matters.

## References

* [keenan-comrie-1977]
* [scott-2021]
* [sichel-2014]
-/

namespace RelativeClause

open Syntax

/-! ### Placement of the clause -/

/-- The placement of the relative clause relative to its head noun. -/
inductive Placement where
  /-- The clause follows the head, English "the man [who left]". -/
  | postNominal
  /-- The clause precedes the head, Japanese "[ _ kaetta] hito". -/
  | preNominal
  /-- The head sits inside the clause, as in Bambara. -/
  | internallyHeaded
  /-- The head appears both inside and outside the clause, Hindi-Urdu *jo … vo*. -/
  | correlative
  deriving DecidableEq, Repr

/-! ### What occupies the relativized position -/

/-- What occupies the relativized position NP_rel inside the clause, the core of
[keenan-comrie-1977]'s ±case distinction: a −case strategy deletes NP_rel, a +case strategy
retains a case-bearing element. -/
inductive NPRel where
  /-- Nothing overt at the relativized position, English "the man [that _ left]". -/
  | gap
  /-- A personal pronoun, Arabic "al-madina [illi saafartu ila-ha]" 'the city that I travelled
  to it'. -/
  | resumptive
  /-- A resumptive that is a partially pronounced lower copy of an Ā-movement chain, diagnosed
  by parasitic gaps ([scott-2021]). -/
  | resumptiveMovement
  /-- A base-generated resumptive bound by the head, obligatory inside adjunct islands
  ([scott-2021]). -/
  | resumptiveBound
  /-- A dedicated relative pronoun, typically fronted and case-bearing, German "der Mann [der
  ging]". -/
  | relPronoun
  /-- The head noun repeated in full inside the clause, as in Bambara. -/
  | nonReduction
  deriving DecidableEq, Repr

/-! ### Relative-clause markers -/

/-- A relative-clause marker or construction of a language, the linguistic object a fragment
records: a particle, pronoun or verbal suffix with the positions it relativizes. The typological
strategy classification is derived from these properties in the studies. -/
structure Marker where
  /-- The surface form, "a", "joka", "that/∅", "-(n)ɨn". -/
  form : String
  /-- What occupies the relativized position. -/
  npRel : NPRel
  /-- Whether the relative element bears case marking, [keenan-comrie-1977]'s ±case. -/
  bearsCaseMarking : Bool
  /-- The clause's placement relative to the head. -/
  placement : Placement
  /-- The positions the marker relativizes. -/
  positions : Finset GrammaticalRelation
  /-- The head-noun definiteness the marker is attested with, when the language distinguishes
  markers by it: Modern Standard Arabic *alladhī* with definite heads against the asyndetic
  relative with indefinite heads ([ryding-2005]). A marker attested with both is recorded as two
  entries. -/
  headDefiniteness : Option Reference.Definiteness := none
  deriving DecidableEq

namespace Marker

variable (m : Marker)

/-- The positions the marker covers form a contiguous segment of the hierarchy,
[keenan-comrie-1977]'s second Hierarchy Constraint: the covered set is order-connected. -/
def IsContinuous : Prop := (m.positions : Set GrammaticalRelation).OrdConnected

instance : Decidable m.IsContinuous :=
  inferInstanceAs (Decidable (m.positions : Set GrammaticalRelation).OrdConnected)

/-- The marker is primary in [keenan-comrie-1977]'s sense: it relativizes subjects. -/
def IsPrimary : Prop := ⊤ ∈ m.positions

instance : Decidable m.IsPrimary := inferInstanceAs (Decidable (_ ∈ _))

end Marker

end RelativeClause
