import Linglib.Core.Logic.Intensional.Frame
import Linglib.Core.Logic.Intensional.Variables

/-!
# Predicate Abstraction
[heim-kratzer-1998]

Predicate Abstraction ([heim-kratzer-1998] Ch. 7) is the composition rule
that λ-binds a variable index, turning a proposition (type `t`) into a property
(type `e ⇒ t`):

  `⟦[XP Op_n YP]⟧^g = λx. ⟦YP⟧^{g[n ↦ x]}`

where `YP` contains a variable (a trace or pronoun) at index `n`. It is the
sibling of Predicate Modification (`Modifier.intersective`, in
`Semantics/Modification/Basic.lean`) — the two non-FA composition rules of
[heim-kratzer-1998] — and is
framework-neutral: any analysis that abstracts over a gap (a Minimalist trace, an
HPSG `SLASH` discharge, a CCG type-raised argument) realizes this rule.

## Main declarations

* `predicateAbstraction` — the rule at result type `t` (the common case).
* `predicateAbstractionGen` — the rule at an arbitrary result type `τ`.

The relative-clause denotation built from this rule (`RelativeClause.denote`) lives
in `Semantics/RelativeClause.lean`.
-/

namespace Semantics.Composition.Abstraction

open Core.Logic.Intensional Core.Logic.Intensional.Variables

/--
Predicate Abstraction ([heim-kratzer-1998] Ch. 7): λ-bind at index `n`,
turning a proposition into a property by abstracting over the variable left at `n`.

  `⟦[XP Op_n YP]⟧^g = λx. ⟦YP⟧^{g[n ↦ x]}`
-/
def predicateAbstraction {F : Frame} (n : ℕ) (body : DenotG F .t)
    : DenotG F (.e ⇒ .t) :=
  lambdaAbsG n body

/--
Generalized predicate abstraction for any result type — e.g. "the book that John
said Mary read _", where the trace is embedded and the result needs further
composition.
-/
def predicateAbstractionGen {F : Frame} {τ : Ty} (n : ℕ) (body : DenotG F τ)
    : DenotG F (.e ⇒ τ) :=
  lambdaAbsG n body

/-- Applying a predicate-abstracted meaning at index `n` to `x` is evaluation of
    the body under the assignment updated at `n` to `x`. -/
theorem predicateAbstraction_apply {F : Frame} (n : ℕ) (body : DenotG F .t)
    (x : F.Entity) (g : Core.Assignment F.Entity)
    : (predicateAbstraction n body g) x = body (g[n ↦ x]) := rfl

end Semantics.Composition.Abstraction
