import Linglib.Semantics.Quantification.ChoiceFunction
import Linglib.Fragments.Farsi.Determiners

/-!
# Mirrazi (2024): Indefinites in Negated Intensional Contexts

This file formalizes the argument of [mirrazi-2024] from Farsi indefinites under negated
intensional operators. *Rodica does not think that Carl read some of the books* has a
reading on which the indefinite scopes above the negation but below *think*, de dicto: no
syntactic position is at once above the negation and below the attitude, so movement cannot
derive it, and neg-raising cannot either, since it leaves the indefinite below the negation
and the reading also arises under predicates that do not raise negation. The paper derives
the reading from in-situ choice functions whose existential closure sits above the negation
while the function carries a world variable bound by the attitude (`widePseudoDeDictoTC`,
against the de re construal `wideDeReTC`). The world variable is what separates the two:
when the noun's extension and the function are rigid across the belief worlds the truth
conditions coincide (`deRe_eq_pseudoDeDicto_when_rigid`), the fixed-set problem, and the
Farsi indefinites, choice-functional with a world variable, are predicted to have the
reading (`farsi_indefinites_pseudo`).

## Implementation notes

The choice-function apparatus, its world-skolemized variant, and the classification of
indefinites by type and world variable live in `Semantics/Quantification/ChoiceFunction`;
the Farsi determiners are the fragment's. Universal quantifiers, which lack the reading,
enter only through that classification.

## References

* [mirrazi-2024]
-/

namespace Mirrazi2024

open Quantification.ChoiceFunction
open Farsi.Determiners

section TruthConditions

variable (W E : Type*) (f : SkolemCF W E) (R : E → W → W → Prop) (agent : E) (worlds : List W)
  (nounProp : W → E → Prop) (vp : E → W → Prop) (w₀ : W)

/-- The wide pseudo-scope de dicto reading: in every belief world the individual the function
picks from that world's extension of the noun fails the predicate. -/
def widePseudoDeDictoTC : Prop :=
  ∀ w' ∈ worlds, R agent w₀ w' → ¬ vp (f.applyIntensionAt .bound w' w₀ nounProp) w'

/-- The wide-scope de re reading: the function's world argument is free, so the individual is
fixed across the belief worlds. -/
def wideDeReTC : Prop :=
  ∀ w' ∈ worlds, R agent w₀ w' → ¬ vp (f.applyIntensionAt .free w' w₀ nounProp) w'

/-- The two readings differ only in whether the function's world argument is bound, so with a
rigid noun extension and a rigid function they coincide: the fixed-set problem of plain
intensional choice functions. -/
theorem deRe_eq_pseudoDeDicto_when_rigid (hRigidNP : ∀ w, nounProp w = nounProp w₀)
    (hRigidCF : ∀ w, f w = f w₀) :
    widePseudoDeDictoTC W E f R agent worlds nounProp vp w₀ ↔
      wideDeReTC W E f R agent worlds nounProp vp w₀ := by
  unfold widePseudoDeDictoTC wideDeReTC SkolemCF.applyIntensionAt SkolemCF.applyIntension
  constructor <;> intro h w' hw' hR
  · rw [← hRigidNP w', ← hRigidCF w']; exact h w' hw' hR
  · rw [hRigidNP w', hRigidCF w']; exact h w' hw' hR

end TruthConditions

/-- The Farsi indefinites *ye*, *čand-ta*, and *do-ta* are choice-functional with a world
variable, so they support the wide pseudo-scope de dicto reading. -/
theorem farsi_indefinites_pseudo :
    ∀ e ∈ [ye, candTa, doTa], IndefType.canPseudoDeDicto e.indefType e.hasWorldVar = true := by
  decide

end Mirrazi2024
