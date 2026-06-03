import Linglib.Core.Word
import Linglib.Features.CoreferenceStatus
import Linglib.Features.Register
import Linglib.Features.Prominence
import Linglib.Features.Clusivity
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
* `Bound` — the binding axis: a carrier's total `Features.BindingClass`, the typed companion to the
  partial `Features.BindingSource`.
* `Anaphoric`, `Pronominal`, `Referring` — the Principle A / B / C *type*-markers: a homogeneous
  carrier all of whose elements share one binding class. The typed-view generalization of the
  element-level `Pronoun.{IsAnaphor, IsPronominal, IsRExpression}`.
* `Bound.{IsAnaphor, IsPronominal, IsRExpression}` — the same A / B / C partition as *element*
  predicates, generic over any `[Bound α]` carrier.
* `Deictic`, `Clusive` — orthogonal data-mixins (register / referential person; clusivity).

## Implementation notes

Capabilities live near their domain (mathlib-style: `ContinuousMul` is in `Topology`, not
`Algebra`). The word-class-neutral `Indefinite` capability (`[Indefinite α]`, Haspelmath
function-coverage) therefore lives in `Features/Indefinite.lean`, not here — indefiniteness is not
pronoun-specific. Two further axes are deferred, each for a principled reason. *Deficiency*
([cardinaletti-starke-1999] `Pronoun.Strength`) is *per-series*, not per-element: every carrier's
strength is carrier-uniform (Italian clitics are all `.clitic`; the Mixtec clitic/nonclitic *fields*
have fixed strengths), so an `α → Strength` accessor would be constant on every carrier — a
per-*type* fact, not a per-element capability, and it is already served by per-series `def`s +
`Strength.rank`. A finer *lexical-kind* axis (personal vs relative vs interrogative) is not reducible
to the A/B/C role and needs a kind enum not worth inventing ahead of a consumer.
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

/-! ### The binding axis: `Bound` and the Principle A/B/C type-markers -/

/-- A carrier whose every element carries a (total) `Features.BindingClass` — its Principle A/B/C
role. The typed companion to `Features.BindingSource` (`α → Option BindingClass`, the *partial*
source the framework-neutral binding engine consumes): `Bound` is the case where the kind fixes the
class for the whole carrier. -/
class Bound (α : Type*) where
  /-- The Principle A anaphor / B pronominal / C R-expression class. -/
  bindingClass : α → Features.BindingClass

/-- A bare `Pronoun`'s declared class, defaulting an undeclared φ-shell to Principle-B `.pronoun`
([chomsky-1981]'s elsewhere case for a pro-form). -/
instance : Bound Pronoun := ⟨fun p => p.bindingClass.getD .pronoun⟩
instance : Bound PersonalPronoun := ⟨fun p => p.toPronoun.bindingClass.getD .pronoun⟩

/-- Principle-A carrier: every element is an anaphor (reflexive or reciprocal). -/
class Anaphoric (α : Type*) [Bound α] : Prop where
  isAnaphor : ∀ a : α, Bound.bindingClass a = .reflexive ∨ Bound.bindingClass a = .reciprocal

/-- Principle-B carrier: every element is a pronominal. -/
class Pronominal (α : Type*) [Bound α] : Prop where
  isPronominal : ∀ a : α, Bound.bindingClass a = .pronoun

/-- Principle-C carrier: every element is a referring expression (an R-expression — proper name,
full NP). Named for the adjectival parallel with `Anaphoric`/`Pronominal`. -/
class Referring (α : Type*) [Bound α] : Prop where
  isReferring : ∀ a : α, Bound.bindingClass a = .rExpression

/-! ### Binding-class element predicates (generic over `[Bound α]`) -/

/-- `a` is a Principle-A anaphor (reflexive or reciprocal) — the A/B/C partition as an *element*
predicate over any `[Bound α]` carrier (a `Pronoun`, an Italian clitic, a Turkish anaphor, …). The
generic companion to the per-`Pronoun` `Pronoun.IsAnaphor`. -/
def Bound.IsAnaphor {α : Type*} [Bound α] (a : α) : Prop :=
  Bound.bindingClass a = .reflexive ∨ Bound.bindingClass a = .reciprocal

/-- `a` is a Principle-B pronominal. -/
def Bound.IsPronominal {α : Type*} [Bound α] (a : α) : Prop :=
  Bound.bindingClass a = .pronoun

/-- `a` is a Principle-C R-expression. -/
def Bound.IsRExpression {α : Type*} [Bound α] (a : α) : Prop :=
  Bound.bindingClass a = .rExpression

instance {α : Type*} [Bound α] (a : α) : Decidable (Bound.IsAnaphor a) := by
  unfold Bound.IsAnaphor; infer_instance
instance {α : Type*} [Bound α] (a : α) : Decidable (Bound.IsPronominal a) := by
  unfold Bound.IsPronominal; infer_instance
instance {α : Type*} [Bound α] (a : α) : Decidable (Bound.IsRExpression a) := by
  unfold Bound.IsRExpression; infer_instance

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
