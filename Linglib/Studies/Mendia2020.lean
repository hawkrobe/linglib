module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Setoid.Partition
public import Linglib.Semantics.Degree.Hom
public import Linglib.Semantics.Reference.Iota

/-!
# Mendia (2020): Reference to ad hoc kinds

This file formalizes [mendia-2020]'s partition analysis of kind reference. The analysis starts
from the Disjointness Condition of [carlson-1977a], as Mendia states it in (16): a
kind-referring expression ranges over subkinds that share no realizations and jointly cover the
kind. Mendia recasts the condition as the requirement that kind reference go through a
partition of the kind's realizations into the cells of a contextually salient equivalence
relation, (17)–(20) and (28), a family in which every realization lies in exactly one cell
(`cover_and_noOverlap_iff`). Under any partition, finitely many individuals realize at most as
many subkinds as there are individuals (`ncard_realized_classes_le`). So *two kinds of dog are
sitting in the next room*, (14), is false when only Fido, a border collie and a watch-dog, is
there (`ncard_realized_fido_le`). The border collies and the watch-dogs would make it true, but
they overlap in Fido and form no partition (`ncard_realized_borderCollies_watchDogs`,
`not_partition_borderCollies_watchDogs`), while three bulldogs and two beagles realize two
subkinds of the breed partition (`ncard_realized_room14a`).

Subkinds are referred to through the ι of the cells. The demonstrative *that (kind of) dog* is
always defined and picks out the cell of the demonstrated dog, (31b) (`that_eq`), while *the
kind of dog* fails once there are two cells, (32b) (`the_kind_eq_none`). An ad hoc kind term
such as *the lions that eat people* is the ι of κ+, the cells that contain every instance of
the restrictor, (33)–(36) (`kappaPlus`). The definite refers when the restrictor's instances
share a cell (`the_kappaPlus_eq_some`) and fails when they do not, so no partition of lions by
subspecies serves it (`the_kappaPlus_eq_none`, `the_kappaPlus_subspecies`); under the partition
by what each lion eats, (37), it refers to exactly the people-eating lions, the second line of
(36) (`the_kappaPlus_ker`, `the_kappaPlus_diet`). Footnote 9's unification of the operators
holds: κ is κ+ with no restrictor, and the demonstrative is the definite over κ+ restricted to
the demonstrated individual (`kappaPlus_empty`, `kappaPlus_singleton`).

Mendia's (17) is the two-sided indistinguishability `Degree.cresswellSetoid`, which returns an
equivalence relation unchanged (`Degree.cresswellSetoid_setoid`) and divides a preorder into its
degrees (`Degree.cresswellSetoid_le_iff`): following [cresswell-1976], §4.3.1 takes degrees to
be equivalence classes. An amount reading of a relative clause is then the same definite under
the partition into degrees, and refers to the degree (59) of the restrictor's instances
(`amount_reading`).

## Implementation notes

* The model is extensional. The type `E` collects the realizations of the kind under
  discussion, a salient kind formation is a `Setoid E`, the partition Π of (28) is its
  `Setoid.classes`, and a subkind is identified with its cell, as the paper does for its tables
  (p. 616: the members of a partition "are always objects, not kinds").
* (28b) as printed binds `y_k` in the antecedent and uses it in the consequent; it is read with
  `y_k` bound outside the implication. (33) prints `Π(x_y)` for `Π(x_k)`.
* The ι of (31) and (36) is `Reference.russellIota?`, undefined when no cell or several qualify.
* Dogs come in every combination of breed and role and lions in every combination of subspecies
  and diet, so there are people-eating lions of both subspecies. The restrictor *lions that eat
  people* is read as footnote 11's *lions that eat only people*, a value of the diet.

## TODO

* The champagne partitions (64)–(66) of §4.3.2, the distribution of ad hoc kind terms (§3.3),
  the singular–plural contrast (§3.4), and the amount readings without degrees of §5.

## References

* [mendia-2020]
* [carlson-1977a]
* [cresswell-1976]
-/

@[expose] public section

namespace Mendia2020

open Reference

variable {E : Type*}

/-! ### Partitions and the Disjointness Condition (§3.1) -/

/-- (16), (28): a family of subkinds covers the kind and has no overlap iff every realization
lies in exactly one of them, the clause that makes a family a `Setoid.IsPartition`. -/
theorem cover_and_noOverlap_iff {c : Set (Set E)} :
    ((∀ x, ∃ y ∈ c, x ∈ y) ∧ ∀ x, ∀ y ∈ c, x ∈ y → ¬ ∃ z ∈ c, y ≠ z ∧ x ∈ z) ↔
      ∀ x, ∃! y ∈ c, x ∈ y := by
  refine ⟨fun ⟨hc, hn⟩ x ↦ ?_, fun h ↦ ⟨fun x ↦ (h x).exists, fun x y hy hx ⟨z, hz, hne, hxz⟩ ↦
    hne ((h x).unique ⟨hy, hx⟩ ⟨hz, hxz⟩)⟩⟩
  obtain ⟨y, hy, hx⟩ := hc x
  exact ⟨y, ⟨hy, hx⟩, fun z ⟨hz, hxz⟩ ↦ by_contra fun hne ↦ hn x y hy hx ⟨z, hz, Ne.symm hne, hxz⟩⟩

/-- The subkinds of a family realized among the individuals `X`, those that *n kinds of dog are
in the next room* counts. -/
def realized (c : Set (Set E)) (X : Set E) : Set (Set E) := {y ∈ c | (y ∩ X).Nonempty}

/-- The subkinds of a partition realized among `X` are the cells of the members of `X`. -/
theorem realized_classes (s : Setoid E) (X : Set E) :
    realized s.classes X = (fun x ↦ {z | s z x}) '' X := by
  ext y
  refine ⟨?_, fun ⟨x, hx, hy⟩ ↦ hy ▸ ⟨s.mem_classes x, x, s.refl' x, hx⟩⟩
  rintro ⟨⟨a, rfl⟩, x, hxa, hx⟩
  exact ⟨x, hx, Set.ext fun z ↦ ⟨(s.trans' · hxa), (s.trans' · (s.symm' hxa))⟩⟩

/-- (14): under any salient partition, finitely many individuals realize at most as many
subkinds as there are individuals. -/
theorem ncard_realized_classes_le (s : Setoid E) {X : Set E} (hX : X.Finite) :
    (realized s.classes X).ncard ≤ X.ncard := by
  rw [realized_classes]
  exact Set.ncard_image_le hX

/-! ### Fido, (14) -/

/-- Breeds of dog. -/
inductive Breed
  | borderCollie | bulldog | beagle

/-- Roles of dog. -/
inductive Role
  | watchDog | guideDog

/-- A dog: its breed, its role, and an index telling apart dogs alike in both. -/
structure Dog where
  breed : Breed
  role : Role
  idx : ℕ

/-- Fido, a border collie and a watch-dog, (14b). -/
def fido : Dog := ⟨.borderCollie, .watchDog, 0⟩

/-- (14b): with only Fido in the room, no partition of the dogs has two subkinds realized there,
so *two kinds of dog are sitting in the next room* is false. -/
theorem ncard_realized_fido_le (s : Setoid Dog) : (realized s.classes {fido}).ncard ≤ 1 :=
  (ncard_realized_classes_le s (Set.finite_singleton fido)).trans (Set.ncard_singleton fido).le

/-- The border collies. -/
def borderCollies : Set Dog := {d | d.breed = .borderCollie}

/-- The watch-dogs. -/
def watchDogs : Set Dog := {d | d.role = .watchDog}

private theorem borderCollies_ne_watchDogs : borderCollies ≠ watchDogs := fun h ↦ by
  have : (⟨.borderCollie, .guideDog, 0⟩ : Dog) ∈ watchDogs := h ▸ rfl
  simp [watchDogs] at this

/-- (14b): Fido alone realizes both the border collies and the watch-dogs, so counting these
two subkinds would make (14) true. -/
theorem ncard_realized_borderCollies_watchDogs :
    (realized {borderCollies, watchDogs} {fido}).ncard = 2 := by
  have : realized {borderCollies, watchDogs} {fido} = {borderCollies, watchDogs} := by
    refine Set.sep_eq_self_iff_mem_true.2 ?_
    rintro y (rfl | rfl) <;> exact ⟨fido, rfl, rfl⟩
  rw [this, Set.ncard_pair borderCollies_ne_watchDogs]

/-- (14b): the border collies and the watch-dogs overlap in Fido, so they form no partition and
the Disjointness Condition excludes them. -/
theorem not_partition_borderCollies_watchDogs :
    ¬ ∀ x, ∃! y ∈ ({borderCollies, watchDogs} : Set (Set Dog)), x ∈ y := fun h ↦
  borderCollies_ne_watchDogs ((h fido).unique ⟨by simp, rfl⟩ ⟨by simp, rfl⟩)

/-- The dogs of (14a): three bulldogs and two beagles. -/
def room14a : Set Dog :=
  {⟨.bulldog, .guideDog, 0⟩, ⟨.bulldog, .guideDog, 1⟩, ⟨.bulldog, .guideDog, 2⟩,
    ⟨.beagle, .guideDog, 0⟩, ⟨.beagle, .guideDog, 1⟩}

/-- (14a): the dogs of the room realize two subkinds of the breed partition, so (14) is
true. -/
theorem ncard_realized_room14a : (realized (Setoid.ker Dog.breed).classes room14a).ncard = 2 := by
  have hne : {z : Dog | z.breed = .bulldog} ≠ {z | z.breed = .beagle} := fun h ↦ by
    have : (⟨.bulldog, .guideDog, 0⟩ : Dog) ∈ {z : Dog | z.breed = .beagle} := h ▸ rfl
    simp at this
  rw [realized_classes]
  simp only [room14a, Set.image_insert_eq, Set.image_singleton, Setoid.ker_def]
  simp only [Set.insert_eq_of_mem, Set.mem_insert_iff, Set.mem_singleton_iff, true_or]
  exact Set.ncard_pair hne

/-! ### Subkind reference (§3.2.2) -/

/-- (31b): the demonstrative *that (kind of) dog*, the ι of the cells containing the
demonstrated dog, always refers, to that dog's cell. -/
theorem that_eq (s : Setoid E) (a : E) :
    russellIota? (fun y ↦ y ∈ s.classes ∧ a ∈ y) = some {x | s x a} :=
  (russellIota?_eq_some_iff _).2 ⟨⟨s.mem_classes a, s.refl' a⟩,
    fun _ hy ↦ (Setoid.classes_eqv_classes a).unique hy ⟨s.mem_classes a, s.refl' a⟩⟩

/-- (32b): *the kind of dog*, the ι of the cells alone, fails once the partition has two
cells. -/
theorem the_kind_eq_none (s : Setoid E) {a b : E} (h : ¬ s a b) :
    russellIota? (· ∈ s.classes) = none :=
  (russellIota?_eq_none_iff _).2 fun ⟨y, hy, hu⟩ ↦ h <| s.rel_iff_exists_classes.2
    ⟨y, hy, hu _ (s.mem_classes a) ▸ s.refl' a, hu _ (s.mem_classes b) ▸ s.refl' b⟩

/-- κ+, (33): the cells of the partition that contain every instance of the restrictor `P`. -/
def kappaPlus (s : Setoid E) (P : Set E) : Set (Set E) := {y ∈ s.classes | P ⊆ y}

/-- Footnote 9: κ+ with no restrictor is κ, the partition itself. -/
@[simp] theorem kappaPlus_empty (s : Setoid E) : kappaPlus s ∅ = s.classes := by
  simp [kappaPlus]

/-- Footnote 9: κ+ restricted to the demonstrated individual gives the cells whose ι (31b)
takes, so the demonstrative is the definite over κ+. -/
@[simp] theorem kappaPlus_singleton (s : Setoid E) (a : E) :
    kappaPlus s {a} = {y ∈ s.classes | a ∈ y} := by
  simp [kappaPlus]

/-- (36): when every instance of the restrictor shares the cell of `a ∈ P`, the definite over
κ+ refers to that cell. -/
theorem the_kappaPlus_eq_some (s : Setoid E) {P : Set E} {a : E} (ha : a ∈ P)
    (hP : ∀ x ∈ P, s x a) : russellIota? (· ∈ kappaPlus s P) = some {x | s x a} :=
  (russellIota?_eq_some_iff _).2 ⟨⟨s.mem_classes a, hP⟩, fun _ ⟨hy, hPy⟩ ↦
    Setoid.eq_of_mem_classes hy (hPy ha) (s.mem_classes a) (s.refl' a)⟩

/-- p. 604: when two instances of the restrictor lie in different cells, no cell contains them
both and the definite fails. -/
theorem the_kappaPlus_eq_none (s : Setoid E) {P : Set E} {a b : E} (ha : a ∈ P) (hb : b ∈ P)
    (h : ¬ s a b) : russellIota? (· ∈ kappaPlus s P) = none :=
  (russellIota?_eq_none_iff _).2 fun ⟨y, ⟨hy, hPy⟩, _⟩ ↦
    h (s.rel_iff_exists_classes.2 ⟨y, hy, hPy ha, hPy hb⟩)

/-- (36), (37) and footnote 11: under the partition by a function `f`, such as what each lion
eats, the individuals on which `f` takes a given value form a cell, and the definite with that
restrictor refers to exactly them, the second line of (36). -/
theorem the_kappaPlus_ker {β : Type*} (f : E → β) (a : E) :
    russellIota? (· ∈ kappaPlus (Setoid.ker f) (f ⁻¹' {f a})) = some (f ⁻¹' {f a}) :=
  the_kappaPlus_eq_some _ rfl fun _ h ↦ h

/-- Subspecies of lion. -/
inductive Subspecies
  | african | asiatic

/-- What a lion eats, read as footnote 11 requires: only people, only zebras, or only carrion. -/
inductive Diet
  | people | zebras | carrion

/-- A lion: its subspecies, its diet, and an index telling apart lions alike in both. -/
structure Lion where
  subspecies : Subspecies
  diet : Diet
  idx : ℕ

/-- *Lions that eat people*, (21b), sharpened as footnote 11 requires. -/
def eatPeople : Set Lion := Lion.diet ⁻¹' {.people}

/-- p. 604: the partition of lions by subspecies cannot serve *the lions that eat people*, since
there are people-eating lions of both subspecies. -/
theorem the_kappaPlus_subspecies :
    russellIota? (· ∈ kappaPlus (Setoid.ker Lion.subspecies) eatPeople) = none :=
  the_kappaPlus_eq_none _ (a := ⟨.african, .people, 0⟩) (b := ⟨.asiatic, .people, 0⟩) rfl rfl
    (by simp [Setoid.ker_def])

/-- (37): the partition by what lions eat serves it, and the definite refers to the
people-eating lions. -/
theorem the_kappaPlus_diet :
    russellIota? (· ∈ kappaPlus (Setoid.ker Lion.diet) eatPeople) = some eatPeople :=
  the_kappaPlus_ker Lion.diet ⟨.african, .people, 0⟩

/-! ### Amounts (§4.3) -/

/-- §4.3: an amount reading is ad hoc kind reference under the partition of a preorder into its
degrees, (57)–(59), and needs only that the restrictor lie in one cell (p. 617). When every
instance of the restrictor is as A as `a`, the definite over κ+ refers to the degree of `a`, the
individuals exactly as A as `a`, (59). -/
theorem amount_reading [Preorder E] {P : Set E} {a : E} (ha : a ∈ P)
    (hP : ∀ x ∈ P, AntisymmRel (· ≤ ·) x a) :
    russellIota? (· ∈ kappaPlus (Degree.cresswellSetoid (· ≤ ·)) P) =
      some {y | AntisymmRel (· ≤ ·) a y} := by
  simp_rw [← Degree.cresswellSetoid_le_iff] at hP
  rw [the_kappaPlus_eq_some _ ha hP]
  exact congrArg some (Set.ext fun y ↦ (Degree.cresswellSetoid_le_iff y a).trans antisymmRel_comm)

end Mendia2020
