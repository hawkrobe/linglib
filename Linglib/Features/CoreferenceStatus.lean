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
    `Core.Nominal.Description` (definiteness/reference flavor) and to a
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
