import Linglib.Core.Logic.Intensional.Defs
import Linglib.Core.Logic.Quantification.Basic
import Linglib.Core.Logic.Quantification.Counting
import Linglib.Semantics.Composition.TypeShifting
import Linglib.Semantics.Quantification.Lexicon

/-!
# Generalized quantifiers: typed bridge
[barwise-cooper-1981] [keenan-stavi-1986] [peters-westerstahl-2006]

The GQ substrate (concrete denotations like `every_sem`, `most_sem`, …
plus their properties: conservativity, monotonicity, smoothness, quantity,
proportionality, etc.) lives in `Core.Logic.Quantification.{Basic, Counting}`.

This file is the **typed layer**: the `Ty.det` semantic type, the
Type-Shifting bridge `A_eq_some_sem`, and the `gqtMeaning` operator for
quantity-implicature studies that plug threshold parameters into a uniform
GQT signature. Toy-witnessed examples and counterexamples live in
`Studies/BarwiseCooper1981.lean` and `Studies/KeenanStavi1986.lean`.
-/

namespace Semantics.Quantification.Quantifier

open Core.Logic.Intensional
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

/-! ### Existential-closure bridge: `A` (Partee existential closure) = `some_sem`

`A` (type-shifting bridge in `Composition.TypeShifting`) and `some_sem` are
both `Type*`-polymorphic over the entity domain. The bridge is one direction. -/

/-- Partee's `A` (existential closure) equals B&C's ⟦some⟧ over a complete
    finite domain. Both compute `λR.λS. ∃x. R(x) ∧ S(x)`. -/
theorem A_eq_some_sem (E : Type) (domain : List E)
    (hComplete : ∀ x : E, x ∈ domain) :
    Semantics.Composition.TypeShifting.A domain = (some_sem : GQ E) := by
  funext R S
  simp only [Semantics.Composition.TypeShifting.A, some_sem]
  exact propext ⟨fun ⟨x, _, hR, hS⟩ => ⟨x, hR, hS⟩,
                 fun ⟨x, hR, hS⟩ => ⟨x, hComplete x, hR, hS⟩⟩

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
