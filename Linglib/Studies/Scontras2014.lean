import Linglib.Semantics.Degree.Measure.Dimensioned
import Linglib.Data.Examples.Scontras2014
import Mathlib.Order.Antichain
import Mathlib.Data.Set.Card

/-!
# Scontras (2014): The Semantics of Measurement

This file formalizes the dissertation's third chapter, on quantizing nouns, the words that
package a substance for counting or measuring. Diagnostics adapted from Rothstein separate three
readings of *n Q of S* and three classes of noun (`Data/Examples/Scontras2014`): a container noun
like *glass* is a plain predicate whose container reading arises from intersective modification
by the preposition *of*, contributing the filled-with relation ((38), `containerReading`); a
measure term like *liter* is a relation between a numeral and the instances of the substance that
measure it ((41), `measureReading`); an atomizer like *grain* partitions the substance into
countable units ((77), `atomizingReading`). The readings differ in what they refer to (Table 3.1):
a container reading refers to containers, the quantizing noun's own denotation, while measure
and atomizing readings refer to the substance (`containerReading_subset`,
`measureReading_subset`, `atomizingReading_subset`); the measure reading is moreover
quantity-uniform under the term's measure (`measureReading_isQuantityUniform`). Each of the
first two classes has uses as the other, the container noun by a shift on the model of the
measure suffix *-ful* ((47), `shiftCM`) and the measure term by lexical reinterpretation as the
class of containers of a unit quantity ((52), `shiftMC`); atomizers, being neither predicates of
containers nor measures, have no measure use.

Countable units are the maximally self-connected instances of a kind in a mereotopology,
parthood with a connectedness relation obeying the bridging axioms of [grimm-2012] ((69)–(75),
`Mereotopology`, `MSC`), and a partition returns such units ((76), `IsMSCPartition`); no-overlap
alone ((66), `IsNonOverlapping`) does not stop the water in a glass from counting as two. Either
way the members of a partition form an antichain, so each of them measures one relative atom
under the relative-atom measure of (68) (`pAtomMeasure_eq_one`), which is what lets cardinal
numerals count them.

## Implementation notes

* Kinds are represented by their instantiation predicates, the `∪k` of the chapter, and an
  atomizer's selectional presupposition ((79), (87)) by an added conjunct rather than a domain
  condition.
* The chapter's argument that the container-to-measure shift cannot be compositional, since a
  continuous measure cannot be built from a predicate, is respected by taking (47), which counts
  filled containers, as the shift; the measure-term-to-container shift is stated as (52) with
  the remark that world knowledge narrows its output.
* The number-marking system of the second chapter, the substrate's `applyNumeral` and
  `IsQuantityUniform`, is consumed rather than restated.

## References

* [scontras-2014]
* [chierchia-1998]
* [rothstein-2009]
* [grimm-2012]
-/

namespace Scontras2014

open Degree

variable {E : Type*} {D : Type}

/-! ### The three readings (§3.2, §3.3) -/

/-- (38b): the preposition *of* of a container reading, the property of being filled with an
instance of the substance `k`. -/
def ofFilled (filledWith : E → E → Prop) (k : E → Prop) (x : E) : Prop :=
  ∃ y, k y ∧ filledWith y x

/-- (38d): the container reading of a container noun `P` with substance `k`: a `P` filled with
the substance, by intersective modification. -/
def containerReading (P : E → Prop) (filledWith : E → E → Prop) (k : E → Prop) (x : E) : Prop :=
  P x ∧ ofFilled filledWith k x

/-- (41), (42): the measure reading of a measure term with measure `μ`, numeral `n` and
substance `k`: the instances of the substance that measure `n`. -/
def measureReading [Preorder D] (μ : DimensionedMeasure E D) (k : E → Prop) (n : D) (x : E) :
    Prop :=
  k x ∧ μ.applyNumeral n x

/-- (77): the atomizing reading of an atomizer with partitioning function `π` and substance
`k`. -/
def atomizingReading (π : (E → Prop) → E → Prop) (k : E → Prop) (x : E) : Prop := π k x

/-- (79), (87): an atomizer's selectional restriction, as the properties its units must have. -/
def atomizerReading (props : E → Prop) (π : (E → Prop) → E → Prop) (k : E → Prop) (x : E) :
    Prop :=
  props x ∧ atomizingReading π k x

/-- Table 3.1: a container reading refers to members of the quantizing noun's denotation. -/
theorem containerReading_subset (P : E → Prop) (filledWith : E → E → Prop) (k : E → Prop) :
    ∀ x, containerReading P filledWith k x → P x := λ _ h => h.1

/-- Table 3.1: a measure reading refers to instances of the substance. -/
theorem measureReading_subset [Preorder D] (μ : DimensionedMeasure E D) (k : E → Prop) (n : D) :
    ∀ x, measureReading μ k n x → k x := λ _ h => h.1

/-- The measure reading with numeral `n` is quantity-uniform under the term's measure, the
condition (44) that number marking checks. -/
theorem measureReading_isQuantityUniform [Preorder D] (μ : DimensionedMeasure E D) (k : E → Prop)
    (n : D) : IsQuantityUniform (measureReading μ k n) μ :=
  λ _ _ hx hy => hx.2.trans hy.2.symm

/-! ### Derived uses (§3.2.3) -/

/-- (47): the container-to-measure shift, on the model of *-ful*: the substance measured by the
number of containers it fills. -/
def shiftCM (P : E → Prop) (filledWith : E → E → Prop) (card : E → ℕ) (k : E → Prop) (n : ℕ)
    (x : E) : Prop :=
  k x ∧ ∃ y, P y ∧ filledWith x y ∧ card y = n

/-- A shifted container noun yields a measure reading: it refers to the substance. -/
theorem shiftCM_subset (P : E → Prop) (filledWith : E → E → Prop) (card : E → ℕ) (k : E → Prop)
    (n : ℕ) : ∀ x, shiftCM P filledWith card k n x → k x := λ _ h => h.1

/-- (52): the measure-term-to-container shift: the objects filled with a unit quantity of some
substance, which lexical reinterpretation narrows to a salient class of containers. -/
def shiftMC [Preorder D] [One D] (μ : DimensionedMeasure E D) (filledWith : E → E → Prop)
    (x : E) : Prop :=
  ∃ (k : E → Prop) (y : E), measureReading μ k 1 y ∧ filledWith y x

/-- A shifted measure term with an *of*-phrase yields a container reading. -/
theorem containerReading_shiftMC [Preorder D] [One D] (μ : DimensionedMeasure E D)
    (filledWith : E → E → Prop) (k : E → Prop) (x : E) :
    containerReading (shiftMC μ filledWith) filledWith k x ↔
      shiftMC μ filledWith x ∧ ∃ y, k y ∧ filledWith y x :=
  Iff.rfl

/-! ### Partitions and relative atoms (§3.3.1) -/

section Mereotopology

variable [PartialOrder E]

/-- (71): two individuals overlap when they share a part. -/
def Overlap (x y : E) : Prop := ∃ z, z ≤ x ∧ z ≤ y

/-- (72), (73): a mereotopology on the parthood order: a reflexive symmetric connectedness
relation, entailed by parthood (integrity) and by overlap (unity), and monotone along
parthood. -/
structure Mereotopology (E : Type*) [PartialOrder E] where
  /-- Connectedness. -/
  C : E → E → Prop
  refl : ∀ x, C x x
  symm : ∀ x y, C x y → C y x
  integrity : ∀ x y, x ≤ y → C x y
  unity : ∀ x y, Overlap x y → C x y
  mono : ∀ x y z, x ≤ y → C x z → C z y

variable (M : Mereotopology E)

/-- (74): an individual is self-connected when any two individuals that between them overlap
exactly what it overlaps are connected. -/
def SelfConnected (x : E) : Prop :=
  ∀ y z, (∀ v, Overlap v x ↔ Overlap v y ∨ Overlap v z) → M.C y z

/-- (75): a maximally self-connected instance of the kind `k`: self-connected and a proper part
of no self-connected instance. -/
def MSC (k : E → Prop) (x : E) : Prop :=
  SelfConnected M x ∧ k x ∧ ¬ ∃ y, x < y ∧ SelfConnected M y ∧ k y

/-- (76): a partition of the kind `k` returns maximally self-connected instances of it. -/
def IsMSCPartition (k : E → Prop) (Q : E → Prop) : Prop := ∀ y, Q y → k y ∧ MSC M k y

/-- (66): a set of individuals no two of which overlap. -/
def IsNonOverlapping (Q : E → Prop) : Prop := ∀ x y, Q x → Q y → x ≠ y → ¬ Overlap x y

/-- (68): the relative-atom measure of `Q`: the number of `Q`-atoms, members of `Q` with no
member of `Q` as a proper part, that are parts of `y`. -/
noncomputable def pAtomMeasure (Q : E → Prop) (y : E) : ℕ :=
  {x | Q x ∧ x ≤ y ∧ ¬ ∃ z, Q z ∧ z < x}.ncard

/-- The members of a maximally self-connected partition form an antichain: one cannot be a
proper part of another. -/
theorem isAntichain_of_isMSCPartition {k Q : E → Prop} (h : IsMSCPartition M k Q) :
    IsAntichain (· ≤ ·) {x | Q x} := λ x hx y hy hxy hle =>
  (h x hx).2.2.2 ⟨y, lt_of_le_of_ne hle hxy, (h y hy).2.1, (h y hy).1⟩

/-- The members of a non-overlapping partition form an antichain. -/
theorem isAntichain_of_isNonOverlapping {Q : E → Prop} (h : IsNonOverlapping Q) :
    IsAntichain (· ≤ ·) {x | Q x} := λ x hx y hy hxy hle =>
  h x y hx hy hxy ⟨x, le_rfl, hle⟩

/-- In an antichain every member is its only atom below itself. -/
theorem atoms_eq_singleton {Q : E → Prop} (h : IsAntichain (· ≤ ·) {x | Q x}) {y : E}
    (hy : Q y) : {x | Q x ∧ x ≤ y ∧ ¬ ∃ z, Q z ∧ z < x} = {y} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, hxy, -⟩
    by_contra hne
    exact h hx hy hne hxy
  · rintro rfl
    exact ⟨hy, le_rfl, λ ⟨z, hz, hzy⟩ => h hz hy hzy.ne hzy.le⟩

/-- Each member of a partition measures one relative atom, so cardinal numerals count them. -/
theorem pAtomMeasure_eq_one {Q : E → Prop} (h : IsAntichain (· ≤ ·) {x | Q x}) {y : E}
    (hy : Q y) : pAtomMeasure Q y = 1 := by
  rw [pAtomMeasure, atoms_eq_singleton h hy, Set.ncard_singleton]

/-- (77) with (76): the atomizing reading refers to maximally self-connected instances of the
substance, hence to the substance. -/
theorem atomizingReading_subset {π : (E → Prop) → E → Prop} {k : E → Prop}
    (hπ : IsMSCPartition M k (π k)) : ∀ x, atomizingReading π k x → k x :=
  λ _ hx => (hπ _ hx).1

end Mereotopology

end Scontras2014
