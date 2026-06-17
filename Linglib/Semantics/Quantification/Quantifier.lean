import Linglib.Semantics.Intensional.Defs
import Linglib.Semantics.Quantification.Basic
import Linglib.Semantics.Quantification.Counting
import Linglib.Semantics.Composition.TypeShifting

/-!
# Generalized quantifiers: typed bridge
[barwise-cooper-1981] [keenan-stavi-1986] [peters-westerstahl-2006]

The GQ substrate (concrete denotations like `every_sem`, `most_sem`, …
plus their properties: conservativity, monotonicity, smoothness, quantity,
proportionality, etc.) lives in `Quantification.{Basic, Counting}`.

This file is the **typed layer**: the `Ty.det` semantic type and the
Type-Shifting bridge `A_eq_some_sem`. Toy-witnessed examples and
counterexamples live in `Studies/BarwiseCooper1981.lean` and
`Studies/KeenanStavi1986.lean`. The threshold-parametric GQT scale-model
(`gqtMeaning`) is van Tiel's foil and lives in `Studies/VanTielEtAl2021.lean`.
-/

namespace Quantification.Quantifier

open Intensional
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

end Quantification.Quantifier
