import Mathlib.Order.Interval.Set.Defs
import Linglib.Semantics.Mereology
import Linglib.Semantics.Reference.Context.Basic
import Linglib.Core.Order.UpperLower.Finset
import Linglib.Semantics.Plurality.NumberFeatures
import Linglib.Syntax.Person.Features
import Linglib.Syntax.Gender.Decomposition

/-!
# The domains of φ-features

A φ-feature is a presuppositional partial identity function on the entity domain
[sauerland-2003]: it asserts nothing and is defined on a domain, so a feature denotes as that
domain, a `Set` of entities. A bundle of features denotes as the intersection of its features'
domains, `Finset.inf`, the empty bundle as everything, so a bigger bundle denotes a smaller
domain, and over well-formed bundles the domains nest by specification
(`IsLowerSet.inf_le_inf_of_card_le`): the Feature-Subset Principle as a consequence of the
privative geometry rather than a stipulation. The person, number and gender values denote
through their bundles (`Person.dom`, `Number.dom`, `Gender.dom`): person at parthood of the
agent and the addressee of the context of utterance (`Reference.Context`), number at
atomicity, and gender at the gender of the referent, the referents gendered masculine and
feminine that the entity domain comes equipped with (`Gendered`): the feminine feature
presupposes a referent not gendered masculine and the neuter one a referent not gendered
feminine, so the neuter domain lies inside the feminine one
(`Gender.dom_neuter_subset_dom_feminine`), the markedness ordering of [sauerland-2008b]. The
three columns are one skeleton, the containment pair of [harley-ritter-2002] and
[adger-harbour-2008]. An absent feature, and a value without a bundle, the impersonal person,
the numbers beyond the dual and the non-sex-based genders, denote the whole domain. The
semantically unmarked values, third person, plural and masculine, are the empty bundles, and
their unrestricted domain is what honorification recruits [wang-r-2023].

## Implementation notes

The gender of a referent is a social category, not an anatomical one: a referent may be
gendered neither way, and then only a form without a gender feature is defined of it, the
account of singular *they* in [bjorkman-2017] and [konnelly-cowper-2020]. The person entries
take the agent and the addressee as parts of the referent where [sauerland-2003] has them
overlap it; the two coincide for an atomic agent and addressee. The two-feature decomposition
does not see clusivity, so the inclusive is refined to referents including the addressee and
the exclusive leaves the addressee's exclusion to Maximize Presupposition. The dual's minimality
domain needs a mereological predicate the entity domain's order does not supply, so the number
outer set is the whole domain and the dual restricts nothing.

## References

* [sauerland-2003]
* [sauerland-2008b]
* [harley-ritter-2002]
* [adger-harbour-2008]
* [bjorkman-2017]
* [konnelly-cowper-2020]
* [wang-r-2023]
-/

open Mereology

/-! ### Person -/

namespace Person

variable {W E P T : Type*} [PartialOrder E] (c : Reference.Context W E P T) (x : E)

/-- The domain of a person feature at a context of utterance: [author] the referents including
the agent, [participant] those including the agent or the addressee. -/
def Feature.dom : Feature → Set E
  | .author => Set.Ici c.agent
  | .participant => Set.Ici c.agent ∪ Set.Ici c.addressee

/-- The domain of an optional person value at a context of utterance: first person the
referents including the agent, the inclusive those including the agent and the addressee,
second those including the agent or the addressee, third everything; an absent feature and the
impersonal restrict nothing. -/
def dom : Option Person → Set E
  | some .firstInclusive => Set.Ici c.agent ∩ Set.Ici c.addressee
  | p => (p.bind toFeatures).elim Set.univ (·.inf (Feature.dom c))

@[simp] theorem dom_none : dom c none = Set.univ := rfl

@[simp] theorem mem_dom_first : x ∈ dom c (some .first) ↔ c.agent ≤ x := by
  simp [dom, toFeatures, firstF, Feature.dom, or_and_right]

@[simp] theorem mem_dom_firstInclusive :
    x ∈ dom c (some .firstInclusive) ↔ c.agent ≤ x ∧ c.addressee ≤ x := Iff.rfl

@[simp] theorem mem_dom_firstExclusive :
    x ∈ dom c (some .firstExclusive) ↔ c.agent ≤ x := by
  simp [dom, toFeatures, firstF, Feature.dom, or_and_right]

@[simp] theorem mem_dom_second :
    x ∈ dom c (some .second) ↔ c.agent ≤ x ∨ c.addressee ≤ x := by
  simp [dom, toFeatures, secondF, Feature.dom]

@[simp] theorem dom_third : dom c (some .third) = Set.univ := by
  simp [dom, toFeatures, thirdF]

@[simp] theorem dom_zero : dom c (some .zero) = Set.univ := rfl

/-- The inclusive lies inside the first person. -/
theorem dom_firstInclusive_subset_dom_first :
    dom c (some .firstInclusive) ⊆ dom c (some .first) :=
  fun _ hx ↦ (mem_dom_first c _).2 hx.1

end Person

/-! ### Number -/

namespace Number

variable {E : Type*} [PartialOrder E] (x : E)

/-- The domain of a number feature: [atomic] the atoms, [minimal] everything pending a
minimality predicate. -/
def Feature.dom : Feature → Set E
  | .atomic => {x | Atom x}
  | .minimal => Set.univ

/-- The domain of an optional number value: singular the atoms, plural everything, the dual
everything pending a minimality predicate; an absent feature and a value without a bundle
restrict nothing. -/
def dom (n : Option Number) : Set E :=
  (n.bind Features.ofNumber).elim Set.univ (·.inf Feature.dom)

@[simp] theorem dom_none : dom (E := E) none = Set.univ := rfl

@[simp] theorem mem_dom_singular : x ∈ dom (E := E) (some .singular) ↔ Atom x := by
  simp [dom, Features.ofNumber, singularF, Feature.dom]

@[simp] theorem dom_dual : dom (E := E) (some .dual) = Set.univ := by
  simp [dom, Features.ofNumber, dualF, Feature.dom]

@[simp] theorem dom_plural : dom (E := E) (some .plural) = Set.univ := by
  simp [dom, Features.ofNumber, pluralF]

end Number

/-! ### Gender -/

/-- The gender of referents, as socially constituted: the referents gendered masculine and those
gendered feminine, disjoint. Grammatical gender presupposes it, and a referent may be gendered
neither way. -/
class Gendered (E : Type*) where
  /-- The referents gendered masculine. -/
  masculine : Set E
  /-- The referents gendered feminine. -/
  feminine : Set E
  /-- No referent is gendered both ways. -/
  disjoint : Disjoint masculine feminine

namespace Gender

variable {E : Type*} [Gendered E] (x : E)

/-- The domain of a gender feature over a gendered entity domain: [feminine] the referents not
gendered masculine, [neuter] those not gendered feminine. -/
def Feature.dom : Feature → Set E
  | .feminine => Gendered.masculineᶜ
  | .neuter => Gendered.feminineᶜ

/-- The domain of an optional gender value over a gendered entity domain: the feminine the
referents not gendered masculine, the neuter those gendered neither way, the masculine
everything; an absent feature and the non-sex-based genders restrict nothing. -/
def dom (g : Option Gender) : Set E :=
  (g.bind Features.fromGender).elim Set.univ (·.inf Feature.dom)

@[simp] theorem dom_none : dom (E := E) none = Set.univ := rfl

@[simp] theorem mem_dom_neuter :
    x ∈ dom (some .neuter) ↔ x ∉ Gendered.masculine ∧ x ∉ Gendered.feminine := by
  simp [dom, Features.fromGender, Features.neuter, Feature.dom]

@[simp] theorem mem_dom_feminine : x ∈ dom (some .feminine) ↔ x ∉ Gendered.masculine := by
  simp [dom, Features.fromGender, Features.feminine, Feature.dom]

@[simp] theorem dom_masculine : dom (E := E) (some .masculine) = Set.univ := by
  simp [dom, Features.fromGender, Features.masculine]

/-- The neuter domain lies inside the feminine one: the containment `[+neuter] → [+feminine]`
of the decomposition, as a fact about referents. -/
theorem dom_neuter_subset_dom_feminine :
    dom (E := E) (some .neuter) ⊆ dom (some .feminine) :=
  Finset.inf_mono (by decide : Features.feminine ⊆ Features.neuter)

end Gender
