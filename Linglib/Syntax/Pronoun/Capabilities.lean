import Linglib.Core.UD.Word
import Linglib.Features.CoreferenceStatus
import Linglib.Features.Register
import Linglib.Features.Prominence
import Linglib.Features.Clusivity
import Linglib.Syntax.Binding.Basic
import Linglib.Syntax.Pronoun.Basic

/-!
# Pronoun capabilities — a mixin tower over pronoun carriers

Pronoun *entries* (`Pronoun`, `PersonalPronoun`, `IndefinitePronoun`, …) are bundled `structure`
values — many per language, like mathlib's `MonoidHom`. This file gives the *capabilities* a
carrier `α` can have, as typeclass mixins abstracting over the representation — the
`MonoidHomClass`/`ContinuousMul`-over-`MonoidHom`/`Mul` relationship, applied to pronouns. A
consumer (binding engine, agreement module, …) then requires exactly the axes it touches:
`[Proform α]` for form/φ, `[Bound α]` for the Principle A/B/C role, and so on — composed by
instance parameters with no `extends`-diamond. The carrier may be a record (`Pronoun`), a syntactic
object (`Word`), or a future theory representation; each supplies its own instances.

## Main declarations

* `Proform` — the spine: a carrier exposes a surface `form` and agreement `phi`-features.
* `instance Bound Pronoun` / `Bound PersonalPronoun` — the pronoun carriers' binding-axis
  instances. The `Bound` *class* (with `Anaphoric`/`Pronominal`/`Referring` and the
  `Bound.Is*` element predicates) is theory-neutral and lives beside its partial companion
  `Features.BindingSource` in `Features/CoreferenceStatus.lean`.
* `bindingClassOf_toWord` — the faithfulness certificate: the binding engine's canonical
  morphology source (`Binding.bindingClassOf`) agrees with the `Bound` mixin on every
  projected pro-form, so the surface engine and the carrier capability never diverge.
* `Deictic`, `Clusive` — orthogonal data-mixins (register / referential person; clusivity).

## Implementation notes

Capabilities live near their domain (mathlib-style: `ContinuousMul` is in `Topology`, not
`Algebra`). The word-class-neutral `Indefinite` capability (`[Indefinite α]`, Haspelmath
function-coverage) therefore lives in `Features/Indefinite.lean`, and the binding axis `Bound`
lives in `Features/CoreferenceStatus.lean` — neither is pronoun-specific. Two further axes are deferred, each for a principled reason. *Deficiency*
([cardinaletti-starke-1999] `Pronoun.Strength`) is *per-series*, not per-element: every carrier's
strength is carrier-uniform (Italian clitics are all `.clitic`; the Mixtec clitic/nonclitic *fields*
have fixed strengths), so an `α → Strength` accessor would be constant on every carrier — a
per-*type* fact, not a per-element capability, and it is already served by per-series `def`s +
`Strength.rank`. The finer *lexical-kind* axis (personal vs relative vs interrogative vs
demonstrative) is `Pronoun.pronType` — real UD morphology on the carrier (no invented enum),
threaded onto the projected word by `toWord`.
-/

set_option autoImplicit false

/-! ### The spine: `Proform` -/

/-- A pronoun-like carrier exposes a surface `form` and agreement `phi`-features — everything true
of *every* pronoun, the base every other capability builds over (cf. `Mul`/`Semigroup` as the base
operation class). -/
class Proform (α : Type*) where
  /-- Surface form (romanization or orthographic). -/
  form : α → String
  /-- Agreement φ-features (person/number/gender). -/
  phi : α → UD.MorphFeatures

instance : Proform Word := ⟨Word.form, Word.phi⟩
instance : Proform Pronoun := ⟨Pronoun.form, fun p => p.toWord.phi⟩
instance : Proform PersonalPronoun :=
  ⟨fun p => p.toPronoun.form, fun p => p.toPronoun.toWord.phi⟩

/-! ### The pronoun carriers' `Bound` instances, and the faithfulness certificate -/

/-- A bare `Pronoun`'s declared class, defaulting an undeclared φ-shell to Principle-B `.pronoun`
([chomsky-1981]'s elsewhere case for a pro-form). -/
instance : Bound Pronoun := ⟨fun p => p.bindingClass.getD .pronoun⟩
instance : Bound PersonalPronoun := ⟨fun p => p.toPronoun.bindingClass.getD .pronoun⟩

/-- The canonical morphology source agrees with the mixin: a pro-form's projected word
classifies (`Binding.bindingClassOf`, reading `Reflex`/`PronType`/category) exactly as the
carrier's `Bound` class — `Pronoun.toWord` threads the binding morphology faithfully, so the
surface engine and the capability never diverge. Two coherence premises, both vacuous for
every actual entry: the pronoun is not lexically declared an R-expression (its surface
category `.PRON` would win), and it does not *store* `PronType=Rcp` (reciprocal is derived
by `toWord` from `bindingClass = .reciprocal`, never stored). -/
theorem bindingClassOf_toWord (p : Pronoun) (h : p.bindingClass ≠ some .rExpression)
    (hr : p.pronType = some .Rcp → p.bindingClass = some .reciprocal) :
    Binding.bindingClassOf p.toWord = Bound.source p := by
  show Binding.bindingClassOf p.toWord = some (p.bindingClass.getD .pronoun)
  rcases hb : p.bindingClass with _ | c
  · rcases hp : p.pronType with _ | pt
    · simp [Binding.bindingClassOf, Pronoun.toWord, hb, hp]
    · cases pt
      case Rcp => exact absurd ((hr hp).symm.trans hb) (by simp)
      all_goals (simp [Binding.bindingClassOf, Pronoun.toWord, hb, hp]; try decide)
  · cases c with
    | reflexive =>
      rcases hp : p.pronType with _ | pt
      · simp [Binding.bindingClassOf, Pronoun.toWord, hb, hp]; try decide
      · cases pt <;> (simp [Binding.bindingClassOf, Pronoun.toWord, hb, hp]; try decide)
    | reciprocal =>
      rcases hp : p.pronType with _ | pt
      · simp [Binding.bindingClassOf, Pronoun.toWord, hb, hp]; try decide
      · cases pt <;> (simp [Binding.bindingClassOf, Pronoun.toWord, hb, hp]; try decide)
    | pronoun =>
      rcases hp : p.pronType with _ | pt
      · simp [Binding.bindingClassOf, Pronoun.toWord, hb, hp]
        try decide
      · cases pt
        case Rcp => exact absurd ((hr hp).symm.trans hb) (by simp)
        all_goals (simp [Binding.bindingClassOf, Pronoun.toWord, hb, hp]; try decide)
    | rExpression => exact absurd hb h

/-! ### Orthogonal data-mixins: `Deictic`, `Clusive` -/

/-- A deictic carrier exposes register and — when it diverges from agreement person — referential
person, the features specific to personal/referential pronouns ([adamson-zompi-2025]). -/
class Deictic (α : Type*) [Proform α] where
  /-- Register level (T/V, honorific tiers). -/
  register : α → Features.Register.Level
  /-- Referential person when it diverges from formal/agreement person; `none` otherwise. -/
  referentialPerson : α → Option Features.Prominence.PersonLevel

instance : Deictic PersonalPronoun :=
  ⟨PersonalPronoun.register, PersonalPronoun.referentialPerson⟩

/-- A carrier that may mark clusivity (inclusive/exclusive on a 1st-person non-singular form;
[cysouw-2009]). -/
class Clusive (α : Type*) [Proform α] where
  /-- Clusivity value, `none` where unmarked or inapplicable. -/
  clusivity : α → Option Features.Clusivity.Value

instance : Clusive Pronoun := ⟨Pronoun.clusivity⟩
