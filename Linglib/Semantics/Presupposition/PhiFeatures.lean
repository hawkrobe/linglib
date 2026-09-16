import Linglib.Semantics.Mereology
import Linglib.Syntax.Agreement.ContainmentPair
import Linglib.Semantics.Plurality.NumberFeatures
import Linglib.Syntax.Person.Decomposition
import Linglib.Syntax.Gender.Decomposition
import Linglib.Semantics.Presupposition.Basic

/-!
# Presuppositional semantics of φ-features

A φ-feature denotes a presuppositional partial identity function on the entity domain
[sauerland-2003]. The cell of a containment pair denotes through two predicates
(`ContainmentPair.presup`): the maximal cell presupposes the inner predicate, the intermediate
cell the outer one and the minimal cell nothing, and every cell asserts nothing
(`ContainmentPair.presup_assertion`). When the inner predicate entails the outer, the domains
nest by specification level (`ContainmentPair.presup_defined_of_specLevel_le`), the
Feature-Subset Principle as a consequence of the privative geometry rather than a stipulation.
The person, number and gender values denote through their bundles (`Person.presup`,
`Number.presup`, `Gender.presup`), person at the speaker's and the addressee's parthood, number
at atomicity, gender at femaleness and inanimacy, the three columns of one skeleton
[harbour-2016]; a value without a bundle, the impersonal person, the numbers beyond the dual and
the non-sex-based genders, presupposes nothing. The semantically unmarked values, third person,
plural and masculine, are the minimal cells, and their vacuous presupposition is what
honorification recruits [wang-r-2023].

## Implementation notes

The dual's minimality presupposition needs a mereological predicate the entity domain's order
does not supply, so the number outer predicate is trivial and the dual presupposes nothing. The
neuter ↦ inanimate cell and the gender containment are less established than the person and
number columns (German *das Mädchen* 'the girl' is neuter and animate); the established core is
feminine presupposing female with masculine unmarked [sauerland-2008].

## References

* [sauerland-2003]
* [sauerland-2008]
* [harbour-2016]
* [wang-r-2023]
-/

open Presupposition Mereology

namespace Agreement.ContainmentPair

variable {E : Type*} (innerP outerP : E → Prop)

/-- The presupposition of a cell through two predicates: the maximal cell presupposes `innerP`,
the intermediate cell `outerP` and the minimal cell nothing; every cell asserts nothing. -/
def presup : ContainmentPair → PartialProp E
  | ⟨true, true⟩ => ⟨innerP, fun _ ↦ True⟩
  | ⟨true, false⟩ => ⟨outerP, fun _ ↦ True⟩
  | ⟨false, _⟩ => PartialProp.top

@[simp] theorem presup_maximal_defined (x : E) :
    (maximal.presup innerP outerP).defined x ↔ innerP x := Iff.rfl

@[simp] theorem presup_intermediate_defined (x : E) :
    (intermediate.presup innerP outerP).defined x ↔ outerP x := Iff.rfl

@[simp] theorem presup_minimal_defined (x : E) : (minimal.presup innerP outerP).defined x :=
  trivial

@[simp] theorem presup_assertion (c : ContainmentPair) (x : E) :
    (c.presup innerP outerP).assertion x := by
  obtain ⟨_ | _, _ | _⟩ := c <;> trivial

/-- The specification level of a pair is at most its two features. -/
theorem specLevel_le_two (c : ContainmentPair) : c.specLevel ≤ 2 := by
  obtain ⟨_ | _, _ | _⟩ := c <;> decide

/-- The Feature-Subset Principle: with `innerP` entailing `outerP`, a more specified well-formed
cell's presupposition entails a less specified one's. -/
theorem presup_defined_of_specLevel_le (h : ∀ x, innerP x → outerP x)
    {c₁ c₂ : ContainmentPair} (hw₁ : c₁.WellFormed) (hw₂ : c₂.WellFormed)
    (hs : c₂.specLevel ≤ c₁.specLevel) {x : E} (hx : (c₁.presup innerP outerP).defined x) :
    (c₂.presup innerP outerP).defined x := by
  rcases classification c₁ hw₁ with rfl | rfl | rfl <;>
    rcases classification c₂ hw₂ with rfl | rfl | rfl <;>
      simp_all [maximal, intermediate, minimal, specLevel, presup, PartialProp.defined]

end Agreement.ContainmentPair

namespace Agreement.ContainmentPairLike

variable {E F : Type*} [ContainmentPairLike F] (innerP outerP : E → Prop)

/-- The presupposition of a bundle: that of its cell. -/
def presup (f : F) : PartialProp E := (toPair f).presup innerP outerP

@[simp] theorem presup_assertion (f : F) (x : E) : (presup innerP outerP f).assertion x :=
  ContainmentPair.presup_assertion innerP outerP _ x

end Agreement.ContainmentPairLike

open Agreement

/-! ### Person -/

namespace Person

variable {E : Type*} [PartialOrder E] (speaker addressee : E) (x : E)

/-- The presupposition of a person value at a speaker and an addressee: first person presupposes
a referent including the speaker, second one including the speaker or the addressee, third
nothing; the impersonal has no bundle and presupposes nothing. -/
def presup (p : Person) : PartialProp E :=
  p.toFeatures.elim PartialProp.top
    (ContainmentPairLike.presup (speaker ≤ ·) fun y ↦ speaker ≤ y ∨ addressee ≤ y)

@[simp] theorem presup_first_defined : (presup speaker addressee .first).defined x ↔ speaker ≤ x :=
  Iff.rfl

@[simp] theorem presup_firstInclusive_defined :
    (presup speaker addressee .firstInclusive).defined x ↔ speaker ≤ x := Iff.rfl

@[simp] theorem presup_firstExclusive_defined :
    (presup speaker addressee .firstExclusive).defined x ↔ speaker ≤ x := Iff.rfl

@[simp] theorem presup_second_defined :
    (presup speaker addressee .second).defined x ↔ speaker ≤ x ∨ addressee ≤ x := Iff.rfl

@[simp] theorem presup_third_defined : (presup speaker addressee .third).defined x := trivial

@[simp] theorem presup_zero_defined : (presup speaker addressee .zero).defined x := trivial

@[simp] theorem presup_assertion (p : Person) : (presup speaker addressee p).assertion x := by
  unfold presup; cases p.toFeatures <;> simp

end Person

/-! ### Number -/

namespace Number

variable {E : Type*} [PartialOrder E] (x : E)

/-- The presupposition of a number value: singular presupposes an atom, plural nothing, the dual
nothing pending a minimality predicate, and a value without a bundle nothing. -/
def presup (n : Number) : PartialProp E :=
  (Features.ofNumber n).elim PartialProp.top (ContainmentPairLike.presup Atom fun _ ↦ True)

@[simp] theorem presup_singular_defined : (presup (E := E) .singular).defined x ↔ Atom x :=
  Iff.rfl

@[simp] theorem presup_dual_defined : (presup (E := E) .dual).defined x := trivial

@[simp] theorem presup_plural_defined : (presup (E := E) .plural).defined x := trivial

@[simp] theorem presup_assertion (n : Number) : (presup (E := E) n).assertion x := by
  unfold presup; cases Features.ofNumber n <;> simp

end Number

/-! ### Gender -/

namespace Gender

variable {E : Type*} (isFemale isInanimate : E → Prop) (x : E)

/-- The presupposition of a gender value at a femaleness and an inanimacy predicate: neuter
presupposes an inanimate referent, feminine a female one, masculine nothing, and the
non-sex-based genders have no bundle and presuppose nothing. -/
def presup (g : Gender) : PartialProp E :=
  (Features.fromGender g).elim PartialProp.top (ContainmentPairLike.presup isInanimate isFemale)

@[simp] theorem presup_neuter_defined :
    (presup isFemale isInanimate .neuter).defined x ↔ isInanimate x := Iff.rfl

@[simp] theorem presup_feminine_defined :
    (presup isFemale isInanimate .feminine).defined x ↔ isFemale x := Iff.rfl

@[simp] theorem presup_masculine_defined : (presup isFemale isInanimate .masculine).defined x :=
  trivial

@[simp] theorem presup_assertion (g : Gender) : (presup isFemale isInanimate g).assertion x := by
  unfold presup; cases Features.fromGender g <;> simp

end Gender
