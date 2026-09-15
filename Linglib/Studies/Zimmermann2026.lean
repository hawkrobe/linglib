import Linglib.Fragments.Akan.Determiners
import Linglib.Fragments.Hausa.Determiners
import Linglib.Studies.Owusu2022
import Linglib.Studies.Zimmermann2008
import Linglib.Logic.Modal.Extensional

/-!
# Zimmermann (2026): African Lambdas I, The Nominal Domain

This file formalizes the comparative claim about marked indefinites in §3.3 of
[zimmermann-2026]'s review of formal semantic work on African languages. Akan *bí* and Hausa
*wani* are near-identical in distribution, but under negation *wani* phrases scope freely, (13)
after [zimmermann-2014], while *bí* phrases must outscope negation, (15). The review takes the
contrast to require different analyses, (16): a skolemized choice function for *bí*, after
[owusu-2022], and an existential quantifier for *wani*, after [zimmermann-2008]. The two
classifications are recorded on the fragment inventories (`z2026IndefType`); the existential
analysis makes the two scopings of *wani* truth-conditionally distinct on the passenger model
of `Zimmermann2008` (`wani_scopings_diverge`); the choice-function analysis gives *bí* under
negation a reading distinct from the narrow-scope one on the model of `Owusu2022`
(`bi_reading_not_narrow`); and the review's explanation, that negation is not an intensional
operator and so cannot shift the situation argument of the choice function, is the collapse
of the bound and free construals of the situation pronoun under an extensional operator
(`bi_negation_construals_collapse`).

## Implementation notes

* Only the comparison the review itself draws is formalized; the per-language analyses are
  consumed from the studies of their primary sources.
* Bare noun phrases, which take obligatory narrow scope in both languages, are outside the
  classification of (16).

## TODO

* The Ga markers *ko* and *kome* of (17) and the co-occurrence of definite and indefinite
  markers of (18).

## References

* [zimmermann-2026]
* [zimmermann-2014]
* [zimmermann-2008]
* [owusu-2022]
-/

open Quantification.ChoiceFunction (IndefType)

namespace Akan.Determiners.Indefinite

/-- [zimmermann-2026] (16a)'s classification of the Akan inventory: *bí*
denotes a skolemized choice function ([owusu-2022]); bare NPs
(obligatory narrow scope) are outside the (16) classification. -/
def z2026IndefType : Indefinite → Option IndefType
  | .bi => some .choiceFunction
  | .bare => none

end Akan.Determiners.Indefinite

namespace Hausa.Determiners.Indefinite

/-- [zimmermann-2026] (16b)'s classification of the Hausa inventory:
*wani/wata* denotes an ∃-quantifier ([zimmermann-2008],
[zimmermann-2014]); bare NPs (obligatory narrow scope) are outside the
(16) classification. -/
def z2026IndefType : Indefinite → Option IndefType
  | .wani => some .existential
  | .bare => none

end Hausa.Determiners.Indefinite

namespace Zimmermann2026

open Quantification
open Quantification.ChoiceFunction

/-- (13): under the ∃-analysis (16b), the two scopings of *wani* under
negation are truth-conditionally distinct — on [zimmermann-2008]'s
passenger model the ∃ > ¬ reading holds while ¬ > ∃ fails, so the scopal
flexibility of *wani* is empirically detectable. -/
theorem wani_scopings_diverge :
    ¬ ((¬ ∃ x : Zimmermann2008.Faasinjee, Zimmermann2008.Daura x) ↔
      some_sem (λ _ : Zimmermann2008.Faasinjee => True)
        (¬ Zimmermann2008.Daura ·)) :=
  λ h =>
    Zimmermann2008.wani_narrow_scope_false (h.mpr Zimmermann2008.wani_wide_scope)

/-- (15): the CF analysis (16a) assigns *bí* under negation a reading
distinct from ¬ > ∃ — on [owusu-2022]'s two-person model the CF reading
is true while ¬ > ∃ is false. The interpretive gap that selects (16a)
over (16b) for *bí*. -/
theorem bi_reading_not_narrow :
    ∀ d ∈ Owusu2022.skolemDenot Owusu2022.preferAma () .bi,
      ¬ ((¬ ∃ x, Owusu2022.ToDwom x) ↔
        ¬ Owusu2022.ToDwom (d (λ _ _ => True))) :=
  λ d hd h =>
    h.mpr (Owusu2022.bi_wide_scope_witnessed d hd) Owusu2022.someone_sang

/-- The review's negation gloss, formalized: "as negation is not an
intensional operator, the situational skolem argument of the choice
function cannot be shifted away from the actual resource situation …
resulting in wide scope only". Pointwise negation is extensional
(`ModalLogic.IsExtensionalAt.neg`), so by the substrate's
`bound_free_collapse` the bound and free construals of *bí*'s situation
pronoun coincide under negation — for any CF and restrictor; the wide
(free) construal is the only reading. Situation quantifiers separate
the construals (`bound_free_diverge_box`), so the collapse is negation's
extensionality at work, not a triviality. -/
theorem bi_negation_construals_collapse {S E : Type*}
    (f : SkolemCF S E) (s₀ : S) (P : S → E → Prop)
    (VP : E → S → Prop) :
    ((λ p s => ¬ p s)
        (λ s => VP (f.applyIntensionAt .bound s s₀ P) s) s₀ ↔
     (λ p s => ¬ p s)
        (λ s => VP (f.applyIntensionAt .free s s₀ P) s) s₀) :=
  bound_free_collapse ModalLogic.IsExtensionalAt.neg f P VP

end Zimmermann2026
