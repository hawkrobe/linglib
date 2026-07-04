import Linglib.Fragments.Akan.Determiners
import Linglib.Fragments.Hausa.Determiners
import Linglib.Studies.Owusu2022
import Linglib.Studies.Zimmermann2008

/-!
# [zimmermann-2026]: African Lambdas I — The Nominal Domain

[zimmermann-2026] §3.3's comparative claim about marked indefinites: Akan
*bí* and Hausa *wani/wata* are near-identical in distribution but differ
in one decisive respect — under negation *wani*-NPs scope freely
(ex. (13), from [zimmermann-2014]) while *bí*-NPs must outscope negation
(ex. (15)). The review concludes the two markers need contrasting
analyses — (16a) skolemized choice function for *bí* ([owusu-2022],
after [kratzer-1998-pseudoscope] and [mirrazi-2024]) vs (16b)
∃-quantifier for *wani* ([zimmermann-2008]; cf. [schwarzschild-2002]) —
and that the two-way African comparison discriminates between CF- and
∃-analyses of indefinites where comparison with English alone cannot.

## Main declarations

* `Akan.Determiners.Indefinite.z2026IndefType`,
  `Hausa.Indefinite.z2026IndefType` — the review's (16)
  classification over the two Fragment inventories, discharging the
  substrate `IndefType` contrast.
* `Zimmermann2026.wani_scopings_diverge` — (13): the ∃-analysis' two
  scopings are truth-conditionally distinct on [zimmermann-2008]'s
  passenger model.
* `Zimmermann2026.bi_reading_not_narrow` — (15): the CF reading is not
  the ¬ > ∃ reading on [owusu-2022]'s two-person model.
* `Zimmermann2026.bi_negation_construals_collapse` — the review's
  "negation is not an intensional operator" gloss: extensionality of
  negation collapses the situation pronoun's bound/free construals.

## Implementation notes

Review-anchor discipline: only the comparison the review itself draws is
formalized here — the (16) classification and the (13)/(15) scope
divergence. The per-language analyses are consumed from their primary
sources' formalizations: `Studies/Zimmermann2008` (Hausa model,
`wani_wide_scope`, `wani_narrow_scope_false`) and `Studies/Owusu2022`
(Akan model, `skolemDenot`, `bi_wide_scope_witnessed`, `someone_sang`).

## Todo

* Ga *ko* (∃-bound CF) vs *kome* (contextually bound CF) and the
  no-student datum unattested with English indefinites (§3.3 ex. (17)).
* Bare NPs: obligatory narrow scope in both languages; covert-∃
  availability under [chierchia-1998]-style blocking by the overt
  markers (§3.3–§3.4).
* DEF–INDEF co-occurrence *bí nó* via [partee-1987] type-shift of the
  CF output (§3.4 ex. (18)).
* The DEF-marking landscape of §3.1 (uniqueness ι, familiar *nó*,
  demonstrative analyses) — the [schwarz-2013] / [bombi-2018] /
  [owusu-2022] rivalry on the shared Akan entries.
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

namespace Hausa.Indefinite

/-- [zimmermann-2026] (16b)'s classification of the Hausa inventory:
*wani/wata* denotes an ∃-quantifier ([zimmermann-2008],
[zimmermann-2014]); bare NPs (obligatory narrow scope) are outside the
(16) classification. -/
def z2026IndefType : Indefinite → Option IndefType
  | .wani => some .existential
  | .bare => none

end Hausa.Indefinite

namespace Zimmermann2026

open Quantification
open Quantification.ChoiceFunction

/-- (13): under the ∃-analysis (16b), the two scopings of *wani* under
negation are truth-conditionally distinct — on [zimmermann-2008]'s
passenger model the ∃ > ¬ reading holds while ¬ > ∃ fails, so the scopal
flexibility of *wani* is empirically detectable. -/
theorem wani_scopings_diverge :
    ¬ ((¬ ∃ x : Zimmermann2008.Faasinjee, Zimmermann2008.Daura x) ↔
      some_sem (fun _ : Zimmermann2008.Faasinjee => True)
        (¬ Zimmermann2008.Daura ·)) :=
  fun h =>
    Zimmermann2008.wani_narrow_scope_false (h.mpr Zimmermann2008.wani_wide_scope)

/-- (15): the CF analysis (16a) assigns *bí* under negation a reading
distinct from ¬ > ∃ — on [owusu-2022]'s two-person model the CF reading
is true while ¬ > ∃ is false. The interpretive gap that selects (16a)
over (16b) for *bí*. -/
theorem bi_reading_not_narrow :
    ∀ d ∈ Owusu2022.skolemDenot Owusu2022.preferAma () .bi,
      ¬ ((¬ ∃ x, Owusu2022.ToDwom x) ↔
        ¬ Owusu2022.ToDwom (d (Intensional.Intension.rigid (fun _ => True)))) :=
  fun d hd h =>
    h.mpr (Owusu2022.bi_wide_scope_witnessed d hd) Owusu2022.someone_sang

/-- The review's negation gloss, formalized: "as negation is not an
intensional operator, the situational skolem argument of the choice
function cannot be shifted away from the actual resource situation …
resulting in wide scope only". Pointwise negation is extensional
(`Intensional.IsExtensionalAt.neg`), so by the substrate's
`bound_free_collapse` the bound and free construals of *bí*'s situation
pronoun coincide under negation — for any CF and restrictor; the wide
(free) construal is the only reading. Situation quantifiers separate
the construals (`bound_free_diverge_box`), so the collapse is negation's
extensionality at work, not a triviality. -/
theorem bi_negation_construals_collapse {S E : Type*}
    (f : SkolemCF S E) (s₀ : S) (P : Intensional.Intension S (E → Prop))
    (VP : E → S → Prop) :
    ((fun p s => ¬ p s)
        (fun s => VP (f.applyIntensionAt .bound s s₀ P) s) s₀ ↔
     (fun p s => ¬ p s)
        (fun s => VP (f.applyIntensionAt .free s s₀ P) s) s₀) :=
  bound_free_collapse Intensional.IsExtensionalAt.neg f P VP

end Zimmermann2026
