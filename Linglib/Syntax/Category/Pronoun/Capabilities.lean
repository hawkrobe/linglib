import Linglib.Data.UD.Basic
import Linglib.Features.Case.Capabilities
import Linglib.Features.Number.Capabilities
import Linglib.Features.Person.Capabilities
import Linglib.Features.CoreferenceStatus
import Linglib.Features.Register
import Linglib.Features.Prominence
import Linglib.Features.Clusivity
import Linglib.Syntax.Binding.Basic
import Linglib.Syntax.Category.Pronoun.Basic
import Linglib.Morphology.Word.Basic

open Morphology (Word)


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
* `Deictic` — orthogonal data-mixin (register / referential person).

## Implementation notes

Capabilities live near their domain (mathlib-style: `ContinuousMul` is in `Topology`, not
`Algebra`). The word-class-neutral `Indefinite` capability (`[Indefinite α]`, Haspelmath
function-coverage) therefore lives in `Features/Indefinite.lean`, and the binding axis `Bound`
lives in `Features/CoreferenceStatus.lean` — neither is pronoun-specific. Two further axes are deferred, each for a principled reason. *Deficiency*
([cardinaletti-starke-1999] `Pronoun.Strength`) is *per-series*, not per-element: every carrier's
strength is carrier-uniform (Italian clitics are all `.clitic`; the Mixtec clitic/nonclitic *fields*
have fixed strengths), so an `α → Strength` accessor would be constant on every carrier — a
per-*type* fact, not a per-element capability. It is served by the `Pronoun.strength` field
(series-level, `none` when not homogeneous) and the `Strength` linear order, not by a class.
The finer *lexical-kind* axis (personal vs relative vs interrogative vs
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

/-! ### The number axis: `HasNumber` instances and faithfulness -/

/-- A pronoun bears its analytical number directly — the carrier field is
root-`Number`-typed. -/
instance : HasNumber Pronoun := ⟨fun p => p.number⟩
instance : HasNumber PersonalPronoun := ⟨fun p => HasNumber.numberOf p.toPronoun⟩

/-- Projecting a pronoun to a `Word` realizes its number through UD: the
round-trip is identity exactly on UD-expressible values — the
minimal/augmented values are lost to realization (`Number.toUD` is
partial), the number analogue of `personOf_toWord`'s coarsening. -/
theorem numberOf_toWord (p : Pronoun) :
    HasNumber.numberOf p.toWord =
      p.number.bind fun n => n.toUD.bind Number.fromUD := by
  show (p.number.bind Number.toUD).bind Number.fromUD = _
  cases p.number <;> rfl

/-! ### The person axis: `HasPerson` instances and faithfulness -/

/-- A pronoun bears its analytical person directly — the carrier field is
root-`Person`-typed, clusivity included (Tagalog *kami* =
`firstExclusive`). -/
instance : HasPerson Pronoun := ⟨fun p => p.person⟩

instance : HasPerson PersonalPronoun :=
  ⟨fun p => HasPerson.personOf p.toPronoun⟩

/-- Projecting a pronoun to a `Word` coarsens its person: `Word` carries
UD realization, which has no clusivity — the mixin makes the loss
explicit rather than silent. -/
theorem personOf_toWord (p : Pronoun) :
    HasPerson.personOf p.toWord =
      (HasPerson.personOf p).map Person.coarsen := by
  show (p.person.map Person.toUD).map Person.fromUD =
    p.person.map Person.coarsen
  cases p.person with
  | none => rfl
  | some per => exact congrArg some (Person.fromUD_toUD per)

/-! ### The case axis: `HasCase` instances and faithfulness -/

/-- A pronoun bears its analytical case directly — the carrier field is
root-`Case`-typed. -/
instance : HasCase Pronoun := ⟨fun p => p.case_⟩

instance : HasCase PersonalPronoun := ⟨fun p => HasCase.caseOf p.toPronoun⟩

/-- Projecting a pronoun to a `Word` realizes its case through UD
losslessly: `Case.toUD` is currently a bijection, so — unlike person
(clusivity lost) and number (minimal/augmented lost) — the round-trip is
the identity. This is the theorem that degrades when an analytical
refinement splits a UD cell (`Case.fromUD_toUD`). -/
theorem caseOf_toWord (p : Pronoun) :
    HasCase.caseOf p.toWord = HasCase.caseOf p := by
  show (p.case_.map Case.toUD).map Case.fromUD = p.case_
  cases p.case_ with
  | none => rfl
  | some c => exact congrArg some (Case.fromUD_toUD c)

/-! ### Orthogonal data-mixin: `Deictic` -/

/-- A deictic carrier exposes register and — when it diverges from agreement person — referential
person, the features specific to personal/referential pronouns ([adamson-zompi-2025]). -/
class Deictic (α : Type*) [Proform α] where
  /-- Register level (T/V, honorific tiers). -/
  register : α → Features.Register.Level
  /-- Referential person when it diverges from formal/agreement person; `none` otherwise. -/
  referentialPerson : α → Option Person

instance : Deictic PersonalPronoun :=
  ⟨PersonalPronoun.register, PersonalPronoun.referentialPerson⟩
