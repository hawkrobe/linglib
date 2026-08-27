/-!
# Features.CoreferenceStatus

Cross-framework coreference verdict enum. Syntactic frameworks (HPSG,
Dependency Grammar, Minimalism) each provide a
`computeCoreferenceStatus : ... → CoreferenceStatus` function — the shared
return type is what makes their predictions comparable rather than each
framework's verdict living in a private namespace.
-/

namespace Features

/-- The possible coreference relationships between two positions. -/
inductive CoreferenceStatus where
  /-- Coreference is obligatory (reflexives with local antecedent) -/
  | obligatory
  /-- Coreference is possible but not required -/
  | possible
  /-- Coreference is blocked (Principle B/C violations) -/
  | blocked
  /-- No prediction (positions not in relevant configuration) -/
  | unspecified
  deriving Repr, DecidableEq

/-- The binding-theoretic class of a nominal expression, shared across the
    syntactic frameworks (HPSG, Dependency Grammar, Minimalism) so their
    binding-class sources return the same type. The canonical source reads the
    class off a word's own UD morphology (`Binding.bindingClassOf`).

    The *binding-distribution* axis (anaphor/pronominal/r-expression, with the
    anaphor class split into reflexive/reciprocal) — orthogonal to a nominal's
    `Definiteness.Description` (definiteness/reference flavor) and to a
    pronoun's lexical kind. -/
inductive BindingClass where
  /-- Reflexive anaphor (*himself*, *herself*, *themselves*). -/
  | reflexive
  /-- Reciprocal anaphor (*each other*, *one another*). -/
  | reciprocal
  /-- Personal/other pronoun (*he*, *she*, *they*, …). -/
  | pronoun
  /-- Referring expression (proper name, full NP). -/
  | rExpression
  deriving Repr, BEq, DecidableEq

/-- A **binding-class source**: *where* an expression's `BindingClass` comes from. Theories
source it differently — a word's own UD morphology (`Binding.bindingClassOf`, the canonical
language-neutral source), a lexical declaration (`Pronoun.bindingClass`), a structural sort
(HPSG), or the syntactic context (minimal-pronoun / DM). The framework-neutral binding engine is polymorphic
over the source: it takes a `BindingSource` and stays agnostic to where the class came from. -/
abbrev BindingSource (α : Type _) := α → Option BindingClass

end Features

/-! ### The `Bound` capability: total binding class on a carrier

The typeclass face of the binding-class axis, beside its partial companion
`Features.BindingSource`. The *class* is theory-neutral and lives here; each carrier's
*instance* lives with the carrier (`Pronoun` in `Syntax/Category/Pronoun/Capabilities.lean`,
Italian clitics and Turkish anaphors in their Fragments). -/

/-- A carrier whose every element carries a (total) `Features.BindingClass` — its Principle A/B/C
role. The typed companion to `Features.BindingSource` (`α → Option BindingClass`, the *partial*
source the framework-neutral binding engine consumes): `Bound` is the case where the kind fixes the
class for the whole carrier. -/
class Bound (α : Type _) where
  /-- The Principle A anaphor / B pronominal / C R-expression class. -/
  bindingClass : α → Features.BindingClass

/-- A `[Bound α]` carrier's `Features.BindingSource` — the canonical mixin → source bridge:
every element classifies, so the source is total (`some` everywhere). -/
def Bound.source {α : Type _} [Bound α] : Features.BindingSource α :=
  fun a => some (Bound.bindingClass a)

/-- Principle-A carrier: every element is an anaphor (reflexive or reciprocal). -/
class Anaphoric (α : Type _) [Bound α] : Prop where
  isAnaphor : ∀ a : α, Bound.bindingClass a = .reflexive ∨ Bound.bindingClass a = .reciprocal

/-- Principle-B carrier: every element is a pronominal. -/
class Pronominal (α : Type _) [Bound α] : Prop where
  isPronominal : ∀ a : α, Bound.bindingClass a = .pronoun

/-- Principle-C carrier: every element is a referring expression (an R-expression — proper name,
full NP). Named for the adjectival parallel with `Anaphoric`/`Pronominal`. -/
class Referring (α : Type _) [Bound α] : Prop where
  isReferring : ∀ a : α, Bound.bindingClass a = .rExpression

/-- `a` is a Principle-A anaphor (reflexive or reciprocal) — the A/B/C partition as an *element*
predicate over any `[Bound α]` carrier (a `Pronoun`, an Italian clitic, a Turkish anaphor, …). The
element-level companion to the carrier-level `Anaphoric` type-marker. -/
def Bound.IsAnaphor {α : Type _} [Bound α] (a : α) : Prop :=
  Bound.bindingClass a = .reflexive ∨ Bound.bindingClass a = .reciprocal

/-- `a` is a Principle-B pronominal. -/
def Bound.IsPronominal {α : Type _} [Bound α] (a : α) : Prop :=
  Bound.bindingClass a = .pronoun

/-- `a` is a Principle-C R-expression. -/
def Bound.IsRExpression {α : Type _} [Bound α] (a : α) : Prop :=
  Bound.bindingClass a = .rExpression

instance {α : Type _} [Bound α] (a : α) : Decidable (Bound.IsAnaphor a) := by
  unfold Bound.IsAnaphor; infer_instance
instance {α : Type _} [Bound α] (a : α) : Decidable (Bound.IsPronominal a) := by
  unfold Bound.IsPronominal; infer_instance
instance {α : Type _} [Bound α] (a : α) : Decidable (Bound.IsRExpression a) := by
  unfold Bound.IsRExpression; infer_instance
