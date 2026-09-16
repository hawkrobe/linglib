import Mathlib.Order.Interval.Set.Defs
import Linglib.Semantics.Mereology
import Linglib.Semantics.Reference.Context.Basic
import Linglib.Syntax.Agreement.ContainmentPair
import Linglib.Semantics.Plurality.NumberFeatures
import Linglib.Syntax.Person.Decomposition
import Linglib.Syntax.Gender.Decomposition

/-!
# The domains of φ-features

A φ-feature is a presuppositional partial identity function on the entity domain
[sauerland-2003]: it asserts nothing and is defined on a domain, so a feature denotes as that
domain, a `Set` of entities. The cell of a containment pair denotes through two sets
(`ContainmentPair.dom`): the maximal cell is the inner set, the intermediate cell the outer one
and the minimal cell everything. When the inner set is contained in the outer, the domains nest
by specification level (`ContainmentPair.dom_subset_of_specLevel_le`), the Feature-Subset
Principle as a consequence of the privative geometry rather than a stipulation. The person,
number and gender values denote through their bundles (`Person.dom`, `Number.dom`,
`Gender.dom`), person at parthood of the agent and the addressee of the context of utterance
(`Reference.Context`), number at atomicity, gender at the female and the inanimate sorts the
entity domain comes equipped with (`Gender.Sorts`), the three columns of one skeleton
[harbour-2016]; an absent feature, and a value without a bundle, the impersonal person, the
numbers beyond the dual and the non-sex-based genders, denote the whole domain. The semantically
unmarked values, third person, plural and masculine, are the minimal cells, and their
unrestricted domain is what honorification recruits [wang-r-2023].

## Implementation notes

The dual's minimality domain needs a mereological predicate the entity domain's order does not
supply, so the number outer set is the whole domain and the dual restricts nothing. The
neuter ↦ inanimate cell and the gender containment are less established than the person and
number columns (German *das Mädchen* 'the girl' is neuter and animate); the established core is
feminine presupposing female with masculine unmarked [sauerland-2008].

## References

* [sauerland-2003]
* [sauerland-2008]
* [harbour-2016]
* [wang-r-2023]
-/

open Mereology

namespace Agreement.ContainmentPair

variable {E : Type*} (inner outer : Set E)

/-- The domain of a cell through two sets: the maximal cell is `inner`, the intermediate cell
`outer` and the minimal cell everything. -/
def dom : ContainmentPair → Set E
  | ⟨true, true⟩ => inner
  | ⟨true, false⟩ => outer
  | ⟨false, _⟩ => Set.univ

@[simp] theorem dom_maximal : maximal.dom inner outer = inner := rfl

@[simp] theorem dom_intermediate : intermediate.dom inner outer = outer := rfl

@[simp] theorem dom_minimal : minimal.dom inner outer = Set.univ := rfl

/-- The specification level of a pair is at most its two features. -/
theorem specLevel_le_two (c : ContainmentPair) : c.specLevel ≤ 2 := by
  obtain ⟨_ | _, _ | _⟩ := c <;> decide

/-- The Feature-Subset Principle: with `inner ⊆ outer`, a more specified well-formed cell's
domain is contained in a less specified one's. -/
theorem dom_subset_of_specLevel_le (h : inner ⊆ outer) {c₁ c₂ : ContainmentPair}
    (hw₁ : c₁.WellFormed) (hw₂ : c₂.WellFormed) (hs : c₂.specLevel ≤ c₁.specLevel) :
    c₁.dom inner outer ⊆ c₂.dom inner outer := by
  rcases classification c₁ hw₁ with rfl | rfl | rfl <;>
    rcases classification c₂ hw₂ with rfl | rfl | rfl <;>
      simp_all [maximal, intermediate, minimal, specLevel, dom, Set.subset_univ]

end Agreement.ContainmentPair

namespace Agreement.ContainmentPairLike

variable {E F : Type*} [ContainmentPairLike F] (inner outer : Set E)

/-- The domain of a bundle: that of its cell. -/
def dom (f : F) : Set E := (toPair f).dom inner outer

end Agreement.ContainmentPairLike

open Agreement

/-! ### Person -/

namespace Person

variable {W E P T : Type*} [PartialOrder E] (c : Reference.Context W E P T) (x : E)

/-- The domain of an optional person value at a context of utterance: first person the
referents including the agent, second those including the agent or the addressee, third
everything; an absent feature and the impersonal restrict nothing. -/
def dom (p : Option Person) : Set E :=
  (p.bind toFeatures).elim Set.univ
    (ContainmentPairLike.dom (Set.Ici c.agent) (Set.Ici c.agent ∪ Set.Ici c.addressee))

@[simp] theorem dom_none : dom c none = Set.univ := rfl

@[simp] theorem mem_dom_first : x ∈ dom c (some .first) ↔ c.agent ≤ x := Iff.rfl

@[simp] theorem mem_dom_firstInclusive :
    x ∈ dom c (some .firstInclusive) ↔ c.agent ≤ x := Iff.rfl

@[simp] theorem mem_dom_firstExclusive :
    x ∈ dom c (some .firstExclusive) ↔ c.agent ≤ x := Iff.rfl

@[simp] theorem mem_dom_second :
    x ∈ dom c (some .second) ↔ c.agent ≤ x ∨ c.addressee ≤ x := Iff.rfl

@[simp] theorem dom_third : dom c (some .third) = Set.univ := rfl

@[simp] theorem dom_zero : dom c (some .zero) = Set.univ := rfl

end Person

/-! ### Number -/

namespace Number

variable {E : Type*} [PartialOrder E] (x : E)

/-- The domain of an optional number value: singular the atoms, plural everything, the dual
everything pending a minimality predicate; an absent feature and a value without a bundle
restrict nothing. -/
def dom (n : Option Number) : Set E :=
  (n.bind Features.ofNumber).elim Set.univ (ContainmentPairLike.dom {x | Atom x} Set.univ)

@[simp] theorem dom_none : dom (E := E) none = Set.univ := rfl

@[simp] theorem mem_dom_singular : x ∈ dom (E := E) (some .singular) ↔ Atom x := Iff.rfl

@[simp] theorem dom_dual : dom (E := E) (some .dual) = Set.univ := rfl

@[simp] theorem dom_plural : dom (E := E) (some .plural) = Set.univ := rfl

end Number

/-! ### Gender -/

namespace Gender

/-- The sorts of an entity domain that the gender features presuppose: the female and the
inanimate referents. -/
class Sorts (E : Type*) where
  /-- The female referents, presupposed by the feminine. -/
  female : Set E
  /-- The inanimate referents, presupposed by the neuter. -/
  inanimate : Set E

variable {E : Type*} [Sorts E] (x : E)

/-- The domain of an optional gender value over a sorted entity domain: neuter the inanimate
referents, feminine the female ones, masculine everything; an absent feature and the
non-sex-based genders restrict nothing. -/
def dom (g : Option Gender) : Set E :=
  (g.bind Features.fromGender).elim Set.univ (ContainmentPairLike.dom Sorts.inanimate Sorts.female)

@[simp] theorem dom_none : dom (E := E) none = Set.univ := rfl

@[simp] theorem mem_dom_neuter : x ∈ dom (some .neuter) ↔ x ∈ Sorts.inanimate := Iff.rfl

@[simp] theorem mem_dom_feminine : x ∈ dom (some .feminine) ↔ x ∈ Sorts.female := Iff.rfl

@[simp] theorem dom_masculine : dom (E := E) (some .masculine) = Set.univ := rfl

end Gender
