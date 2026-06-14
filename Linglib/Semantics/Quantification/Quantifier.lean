import Linglib.Core.Logic.Intensional.Defs
import Linglib.Semantics.Quantification.Basic
import Linglib.Semantics.Quantification.Counting
import Linglib.Semantics.Composition.TypeShifting
import Linglib.Semantics.Quantification.Lexicon

/-!
# Generalized quantifiers: typed bridge
[barwise-cooper-1981] [keenan-stavi-1986] [peters-westerstahl-2006]

The GQ substrate (concrete denotations like `every_sem`, `most_sem`, …
plus their properties: conservativity, monotonicity, smoothness, quantity,
proportionality, etc.) lives in `Quantification.{Basic, Counting}`.

This file is the **typed layer**: the `Ty.det` semantic type, the
Type-Shifting bridge `A_eq_some_sem`, and the `gqtMeaning` operator for
quantity-implicature studies that plug threshold parameters into a uniform
GQT signature. Toy-witnessed examples and counterexamples live in
`Studies/BarwiseCooper1981.lean` and `Studies/KeenanStavi1986.lean`.
-/

namespace Quantification.Quantifier

open Core.Logic.Intensional
open Quantification

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

open Quantification.Lexicon (Monotonicity) in
/-- GQT meaning: at threshold `θ`, with monotonicity `mono`, in a domain of
    size `n`, is the count `t` true? -/
def gqtMeaning (n : Nat) (mono : Monotonicity) (θ : Nat) (t : Fin (n + 1)) :
    Bool :=
  match mono with
  | .increasing  => t.val ≥ θ
  | .decreasing  => t.val ≤ θ
  | .nonMonotone => t.val == θ

open Quantification.Lexicon (Monotonicity) in
/-- Rational version of `gqtMeaning` (1 if true, 0 if false). -/
def gqtMeaningRat (n : Nat) (mono : Monotonicity) (θ : Nat) (t : Fin (n + 1)) :
    ℚ :=
  if gqtMeaning n mono θ t then 1 else 0

open Quantification.Lexicon (Monotonicity) in
theorem gqtMeaningRat_nonneg (n : Nat) (mono : Monotonicity) (θ : Nat)
    (t : Fin (n + 1)) : 0 ≤ gqtMeaningRat n mono θ t := by
  simp only [gqtMeaningRat]; split_ifs <;> norm_num

end Quantification.Quantifier
