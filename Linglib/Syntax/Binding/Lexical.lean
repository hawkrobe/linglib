import Linglib.Syntax.Pronoun.Basic
import Linglib.Syntax.Pronoun.Mixin
import Linglib.Features.CoreferenceStatus

/-!
# The lexical interface to binding
[chomsky-1981]

The lexical half of binding theory, as a mixin. A carrier `α` is a `Binding.Lexicon`
when each of its pro-forms *declares* a `Features.BindingClass` — which binding
principle governs it. The framework-neutral binding engine
(`Syntax/Binding/Basic.lean`) reads a pro-form's declared class rather than recovering
it from surface form strings or lexicon-list membership: the lexical entry is the
source of truth for its own binding role.

The universal `Pronoun` record is the canonical instance (via its `bindingClass`
field). A syntactic theory's representation (`Word`, an HPSG synsem, …) can instance
it too — which is what lets the binding principles abstract over `[Binding.Lexicon α]`
instead of taking an explicit `classify : Word → Option BindingClass` parameter.

## Main declarations

* `Binding.Lexicon` — a carrier whose pro-forms declare a `BindingClass`.
* `Binding.Lexicon.{IsAnaphor, IsPronominal, IsRExpression}` — the Principle A / B / C
  partitions, read off the declaration.

## Implementation notes

The *per-kind* marker mixins (`Reflexive α`, `Personal α`, …) of the long-horizon design
attach to dedicated single-kind carriers, not to the universal `Pronoun` record (whose
`bindingClass` varies per entry, so no type-level "all of `α` is reflexive" holds). They
are deferred to the theory layer; the per-element `IsAnaphor`/… predicates here serve the
multi-kind record.
-/

namespace Binding

open Features (BindingClass)

/-- A carrier whose pro-forms declare a `Features.BindingClass` — the lexical interface
the binding engine reads. `none` is a bare φ-shell that declares no class. -/
class Lexicon (α : Type) where
  /-- The binding class `a` declares, if any. -/
  bindingClass : α → Option BindingClass

instance : Lexicon Pronoun := ⟨Pronoun.bindingClass⟩

namespace Lexicon

variable {α : Type} [Lexicon α]

/-- `a` declares a Principle-A anaphor (reflexive or reciprocal). -/
def IsAnaphor (a : α) : Prop :=
  bindingClass a = some .reflexive ∨ bindingClass a = some .reciprocal

/-- `a` declares a Principle-B pronominal. -/
def IsPronominal (a : α) : Prop := bindingClass a = some .pronoun

/-- `a` declares a Principle-C R-expression. -/
def IsRExpression (a : α) : Prop := bindingClass a = some .rExpression

instance (a : α) : Decidable (IsAnaphor a) := by unfold IsAnaphor; infer_instance
instance (a : α) : Decidable (IsPronominal a) := by unfold IsPronominal; infer_instance
instance (a : α) : Decidable (IsRExpression a) := by unfold IsRExpression; infer_instance

end Lexicon

/-! ### Single-kind marker mixins

A carrier all of whose pro-forms declare one binding kind — the `[Anaphoric α]`-style
markers. Prop-mixins over `[Lexicon α]`, instantiable on a *single-kind* carrier (a subtype
of a lexicon narrowed to one class) but NOT on the multi-kind `Pronoun` record (whose
`bindingClass` varies per entry; use the per-element `Lexicon.Is*` predicates there).
Stacking these is how a pronoun *kind* is composed and *derived*, never stipulated. -/

/-- All pro-forms of `α` are Principle-A anaphors. -/
class Anaphoric (α : Type) [Lexicon α] : Prop where
  isAnaphor : ∀ a : α, Lexicon.IsAnaphor a

/-- All pro-forms of `α` are Principle-B pronominals. -/
class Pronominal (α : Type) [Lexicon α] : Prop where
  isPronominal : ∀ a : α, Lexicon.IsPronominal a

/-- All pro-forms of `α` are Principle-C R-expressions. -/
class RExpression (α : Type) [Lexicon α] : Prop where
  isRExpression : ∀ a : α, Lexicon.IsRExpression a

/-- A **reflexive pronoun**, derived not stipulated: the sub-carrier of `Pronoun` whose
declaration is `.reflexive`. The dissolution of "should `ReflexivePronoun` be a `structure`?"
— it is the narrowed carrier, and it is `Anaphoric` by construction. -/
abbrev ReflexivePronoun := {p : Pronoun // p.bindingClass = some .reflexive}

instance : Lexicon ReflexivePronoun := ⟨fun r => r.val.bindingClass⟩
instance : Anaphoric ReflexivePronoun := ⟨fun r => Or.inl r.property⟩
instance : PronounLike ReflexivePronoun where
  form := fun r => r.val.form
  phi := fun r => r.val.toWord.phi

/-- `ReflexivePronoun` carries the full lexical stack — `PronounLike` (word-class: form + φ)
*and* the `Anaphoric` marker (Principle A) — composed with no diamond, since the word-class
and binding axes are orthogonal. -/
example (r : ReflexivePronoun) :
    PronounLike.form r = r.val.form ∧ Lexicon.IsAnaphor r :=
  ⟨rfl, Anaphoric.isAnaphor r⟩

/-! ### A validated consumer: Principle A driven by the declaration

A minimal slice of Principle A (`Binding.reflexiveLicensed`, `Syntax/Binding/Basic.lean`)
re-expressed over the lexical mixins: it reads the dependent's kind from `[Lexicon α]` and
the φ-agreement from `[PronounLike α]`, folding the structural command + locality facts into
`commandsLocally` — *no* `classify : Word → BindingClass` parameter. This validates the mixin
layer: the engine's Principle-A logic is driven by the lexical *declaration*. -/

/-- Principle A over the mixins: a declared reflexive `dep` is licensed by `ante` iff `ante`
locally commands it and they φ-agree. A non-reflexive `dep` is vacuously licensed (Principle
A is silent on it). -/
def licensesReflexive {α : Type} [Lexicon α] [PronounLike α]
    (commandsLocally : Prop) (ante dep : α) : Prop :=
  match Lexicon.bindingClass dep with
  | some .reflexive => commandsLocally ∧ (PronounLike.phi ante).compatible (PronounLike.phi dep)
  | _ => True

/-- The reflexive case reduces to *local command ∧ φ-agreement* — exactly the reflexive clause
of `Binding.reflexiveLicensed`, now driven by `[Lexicon α]` rather than a form-string
classifier. -/
theorem licensesReflexive_of_declared {α : Type} [Lexicon α] [PronounLike α]
    (commandsLocally : Prop) (ante dep : α)
    (h : Lexicon.bindingClass dep = some .reflexive) :
    licensesReflexive commandsLocally ante dep
      = (commandsLocally ∧ (PronounLike.phi ante).compatible (PronounLike.phi dep)) := by
  simp only [licensesReflexive, h]

private def exHe : Pronoun :=
  { form := "he", person := some .third, number := some .sg,
    gender := some .masculine, bindingClass := some .pronoun }
private def exHimself : Pronoun :=
  { form := "himself", person := some .third, number := some .sg,
    gender := some .masculine, bindingClass := some .reflexive }

/-- Validation: `himself` (declaring `.reflexive`), φ-agreeing with and locally commanded by
`he`, is licensed by Principle A — driven entirely by the declaration, no classifier. -/
example : licensesReflexive True exHe exHimself := by
  rw [licensesReflexive_of_declared True exHe exHimself rfl]
  exact ⟨trivial, by decide⟩

end Binding
