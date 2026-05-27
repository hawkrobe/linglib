import Linglib.Core.Logic.Intensional.Frame
import Linglib.Core.Logic.Quantification.Basic
import Linglib.Core.Logic.Quantification.Counting
import Linglib.Semantics.Composition.ToyDomain
import Linglib.Semantics.Composition.TypeShifting
import Linglib.Semantics.Quantification.Lexicon

/-!
# Generalized quantifiers: Frame bridge and toy-model examples
@cite{barwise-cooper-1981} @cite{keenan-stavi-1986} @cite{peters-westerstahl-2006}

The GQ substrate (concrete denotations like `every_sem`, `most_sem`, …
plus their properties: conservativity, monotonicity, smoothness, quantity,
proportionality, etc.) lives in `Core.Logic.Quantification.{Basic, Counting}`.

This file is the **Frame layer**: the `Ty.det` semantic type, the
Type-Shifting bridge `A_eq_some_sem`, the toy-model lexicon
(`student_sem`, `person_sem`, `thing_sem`), the worked examples, and the
`gqtMeaning` operator for quantity-implicature studies that plug
threshold parameters into a uniform GQT signature.

Toy-model counterexamples to non-properties (e.g. `every_not_symmetric`,
`m_not_conservative`) also live here because they need a concrete
witness type.
-/

namespace Semantics.Quantification.Quantifier

open Core.Logic.Intensional
open Semantics.Montague (toyModel ToyEntity)
open Core.Quantification

export Core.Quantification
  (every_sem some_sem no_sem
   most_sem few_sem half_sem both_sem neither_sem
   at_least_n_sem at_most_n_sem exactly_n_sem all_but_n_sem between_n_m_sem m_sem
   count Quantity Proportional SatisfiesUniversals
   every_conservative some_conservative no_conservative
   most_conservative few_conservative half_conservative both_conservative
   neither_conservative
   at_least_n_conservative at_most_n_conservative exactly_n_conservative
   all_but_n_conservative between_n_m_conservative
   every_scope_up some_scope_up no_scope_down few_scope_down most_scope_up
   at_least_n_scope_up at_most_n_scope_down
   every_restrictor_down some_restrictor_up no_restrictor_down
   at_least_n_restrictor_up at_most_n_restrictor_down
   some_symmetric no_symmetric
   some_intersective no_intersective
   every_laa no_laa no_raa laa_characterization
   innerNeg_every_eq_no dualQ_every_eq_some outerNeg_some_eq_no
   every_positive_strong no_negative_strong_nonempty
   some_existential no_existential
   every_transitive every_antisymmetric some_quasi_reflexive no_quasi_universal
   every_doubleMono some_doubleMono no_doubleMono notAll_doubleMono
   every_filtrating
   every_contradicts_notEvery no_contradicts_some
   a_e_contrary subalternation_a_i subalternation_e_o subcontrariety_i_o
   every_satisfies_isContradictory_pointwise
   some_upSE some_upSW every_downNW every_downNE no_downNW no_downNE
   some_downNE some_smooth every_upSE_direct every_smooth no_coSmooth_partial
   most_downNE most_upSE most_smooth at_least_n_downNE at_least_n_smooth
   at_most_n_coSmooth
   forall_bij_inv exists_bij_inv count_bij_inv
   quantity_outerNeg quantity_gqMeet
   at_least_n_quantity at_most_n_quantity exactly_n_quantity
   some_quantity no_quantity every_quantity
   most_quantity few_quantity half_quantity
   all_but_n_quantity between_n_m_quantity
   some_eq_at_least_1 at_most_eq_outerNeg_at_least_succ no_eq_at_most_0
   exactly_eq_meet_at_least_at_most all_but_0_eq_every
   some_satisfiesUniversals every_satisfiesUniversals no_satisfiesUniversals
   most_satisfiesUniversals few_satisfiesUniversals
   at_least_n_satisfiesUniversals at_most_n_satisfiesUniversals
   most_proportional few_proportional half_proportional
   quantityInvariant_of_quantity quantity_of_quantityInvariant)

/-! ### Semantic-type alias -/

/-- The determiner type ⟨⟨e,t⟩,⟨⟨e,t⟩,t⟩⟩. -/
def Ty.det : Ty := (.e ⇒ .t) ⇒ ((.e ⇒ .t) ⇒ .t)

/-! ### Frame bridge: `A` (Partee existential closure) = `some_sem`

`A` (type-shifting bridge in `Composition.TypeShifting`) is Frame-typed;
`some_sem` is `Type*`-polymorphic. The bridge is one direction. -/

/-- Partee's `A` (existential closure) equals B&C's ⟦some⟧ over a complete
    finite domain. Both compute `λR.λS. ∃x. R(x) ∧ S(x)`. -/
theorem A_eq_some_sem (F : Frame) (domain : List F.Entity)
    (hComplete : ∀ x : F.Entity, x ∈ domain) :
    Semantics.Composition.TypeShifting.A domain = (some_sem : GQ F.Entity) := by
  funext R S
  simp only [Semantics.Composition.TypeShifting.A, some_sem]
  exact propext ⟨fun ⟨x, _, hR, hS⟩ => ⟨x, hR, hS⟩,
                 fun ⟨x, hR, hS⟩ => ⟨x, hComplete x, hR, hS⟩⟩

/-! ### Toy-model `Fintype` instances -/

instance : Fintype ToyEntity where
  elems := {.john, .mary, .pizza, .book}
  complete := fun x => by cases x <;> simp

/-- Bridge: `toyModel.Entity = ToyEntity` is definitional but opaque to
    instance search. -/
instance : Fintype toyModel.Entity :=
  show Fintype ToyEntity by infer_instance

/-! ### Toy lexicon -/

section ToyLexicon

def student_sem : toyModel.Denot (.e ⇒ .t) :=
  λ x => match x with
    | .john => True
    | .mary => True
    | _ => False

def person_sem : toyModel.Denot (.e ⇒ .t) :=
  λ x => match x with
    | .john => True
    | .mary => True
    | _ => False

def thing_sem : toyModel.Denot (.e ⇒ .t) :=
  λ _ => True

instance : DecidablePred student_sem :=
  fun x => match x with
    | .john | .mary => .isTrue (by simp [student_sem])
    | .pizza | .book => .isFalse (by simp [student_sem])

instance : DecidablePred person_sem :=
  fun x => match x with
    | .john | .mary => .isTrue (by simp [person_sem])
    | .pizza | .book => .isFalse (by simp [person_sem])

instance : DecidablePred thing_sem := fun _ => .isTrue trivial

end ToyLexicon

/-! ### Worked examples -/

section Examples

open Semantics.Montague.ToyLexicon

/-- Not every student sleeps (John sleeps but Mary doesn't). -/
theorem not_everyStudentSleeps : ¬ every_sem student_sem sleeps_sem := by
  intro h
  have := h ToyEntity.mary (by simp [student_sem])
  simp [sleeps_sem] at this

/-- Some student sleeps (John does). -/
theorem someStudentSleeps : some_sem student_sem sleeps_sem :=
  ⟨ToyEntity.john, by simp [student_sem], by simp [sleeps_sem]⟩

/-- Not no student sleeps (John does). -/
theorem not_noStudentSleeps : ¬ no_sem student_sem sleeps_sem := by
  intro h
  have := h ToyEntity.john (by simp [student_sem])
  simp [sleeps_sem] at this

/-- Every student laughs (John and Mary both laugh). -/
theorem everyStudentLaughs : every_sem student_sem laughs_sem := by
  intro x hR
  match x with
  | .john => simp [laughs_sem]
  | .mary => simp [laughs_sem]
  | .pizza => simp [student_sem] at hR
  | .book => simp [student_sem] at hR

theorem someStudentLaughs : some_sem student_sem laughs_sem :=
  ⟨ToyEntity.john, by simp [student_sem], by simp [laughs_sem]⟩

theorem not_everyPersonSleeps : ¬ every_sem person_sem sleeps_sem := by
  intro h
  have := h ToyEntity.mary (by simp [person_sem])
  simp [sleeps_sem] at this

theorem somePersonSleeps : some_sem person_sem sleeps_sem :=
  ⟨ToyEntity.john, by simp [person_sem], by simp [sleeps_sem]⟩

end Examples

/-! ### Toy-witnessed non-properties

These counterexamples to non-properties of specific quantifiers require a
concrete witness type. The witness is `ToyEntity`. -/

/-- `m_sem` is not conservative: it inspects `B` outside `A`. -/
theorem m_not_conservative : ¬ Conservative (m_sem (α := ToyEntity)) := by
  sorry

/-- `⟦every⟧` is NOT symmetric. Witness: R=students, S=things; every(students,
    things)=true but every(things,students)=false. -/
theorem every_not_symmetric : ¬ QSymmetric (every_sem (α := ToyEntity)) := by
  intro h
  have := (h student_sem thing_sem).mp (fun x _ => trivial)
  exact absurd (this ToyEntity.pizza trivial) (by simp [student_sem])

/-- `⟦no⟧` is NOT positive strong: no(A,A) = false when A is non-empty. -/
theorem no_not_positive_strong : ¬ PositiveStrong (no_sem (α := ToyEntity)) := by
  intro h
  have := h student_sem
  exact this ToyEntity.john (by simp [student_sem]) (by simp [student_sem])

/-- `⟦every⟧` is NOT existential (K&S §3.3). -/
theorem every_not_existential : ¬ Existential (every_sem (α := ToyEntity)) := by
  intro h
  have hFwd := (h thing_sem student_sem).mpr
  have : every_sem (fun x => thing_sem x ∧ student_sem x) (fun _ => True) := by
    intro x _; trivial
  exact absurd (hFwd this ToyEntity.pizza trivial) (by simp [student_sem])

/-- `⟦most⟧` is NOT existential (K&S §3.3). -/
theorem most_not_existential : ¬ Existential (most_sem (α := ToyEntity)) := by
  sorry

/-! ## Generalized-Quantifier-Theoretic (GQT) meaning operator

A parametric truth-conditional GQT operator: given a monotonicity direction
and a numerical threshold, `gqtMeaning` returns the literal GQT denotation
as a `Bool` over a finite "intersection-count" world. Used by
quantity-implicature studies (e.g., van Tiel et al. 2021) that plug
per-paper threshold parameters into the same GQT machinery. -/

open Semantics.Quantification.Lexicon (Monotonicity) in
/-- GQT meaning: at threshold `θ`, with monotonicity `mono`, in a domain of
    size `n`, is the count `t` true? -/
def gqtMeaning (n : Nat) (mono : Monotonicity) (θ : Nat) (t : Fin (n + 1)) :
    Bool :=
  match mono with
  | .increasing  => t.val ≥ θ
  | .decreasing  => t.val ≤ θ
  | .nonMonotone => t.val == θ

open Semantics.Quantification.Lexicon (Monotonicity) in
/-- Rational version of `gqtMeaning` (1 if true, 0 if false). -/
def gqtMeaningRat (n : Nat) (mono : Monotonicity) (θ : Nat) (t : Fin (n + 1)) :
    ℚ :=
  if gqtMeaning n mono θ t then 1 else 0

open Semantics.Quantification.Lexicon (Monotonicity) in
theorem gqtMeaningRat_nonneg (n : Nat) (mono : Monotonicity) (θ : Nat)
    (t : Fin (n + 1)) : 0 ≤ gqtMeaningRat n mono θ t := by
  simp only [gqtMeaningRat]; split_ifs <;> norm_num

end Semantics.Quantification.Quantifier
