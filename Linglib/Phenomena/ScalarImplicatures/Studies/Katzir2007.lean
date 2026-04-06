import Linglib.Theories.Semantics.Composition.QuantifierComposition

/-!
# Katzir 2007: Structurally-Defined Alternatives (End-to-End)
@cite{katzir-2007}

Katzir, R. (2007). Structurally-defined alternatives.
Linguistics and Philosophy, 30(6), 669–690.

## Unified Tree Demonstration

This file demonstrates that a single `Tree Cat String` supports both:
- **Structural operations** (PF-level): `leafSubst` generates scalar
  alternatives by same-category word substitution
- **Compositional interpretation** (LF-level): `evalTree` computes
  truth conditions via FA, PM, and Predicate Abstraction

One tree, two interfaces — the Y-model made concrete.

## The Argument

1. Build φ = "some student sleeps" as `Tree Cat String` with QR
2. Generate φ' = "every student sleeps" via `leafSubst` (Det substitution)
3. Interpret both: ⟦φ⟧ = true, ⟦φ'⟧ = false → asserting φ implicates ¬φ'
4. Show φ contains no `ConjP`/`NegP` → symmetric alternative
   "some but not all" cannot be generated structurally

This is Katzir's solution to the symmetry problem: structural
constraints on alternatives prevent the symmetric alternative
from being generated, licensing the scalar implicature.
-/

namespace Phenomena.ScalarImplicatures.Studies.Katzir2007

open Core.Tree
open Semantics.Composition.Tree
open Semantics.Composition.QuantifierComposition
open Semantics.Montague (toyModel ToyEntity)
open Semantics.Montague.ToyLexicon (sleeps_sem)
open Semantics.Lexical.Determiner.Quantifier (some_sem every_sem student_sem)

-- ════════════════════════════════════════════════════════════════════
-- § Source Tree
-- ════════════════════════════════════════════════════════════════════

/-- "Some student sleeps" after QR, with UD-grounded categories:
```
[S [DP [Det some] [N student]] [₁ [S [t₁:NP] [VP [V sleeps]]]]]
``` -/
def φ : Tree Cat String :=
  .node .S [
    .node .DP [.terminal .Det "some", .terminal .N "student"],
    .bind 1 .S
      (.node .S [.trace 1 .NP, .node .VP [.terminal .V "sleeps"]])]

-- ════════════════════════════════════════════════════════════════════
-- § Structural Alternative Generation
-- ════════════════════════════════════════════════════════════════════

/-- Scalar alternative: substitute "some" → "every" at Det position.
This is Katzir's core operation (def 19, substitution): replace a
terminal with a same-category item from the substitution source.
Both "some" and "every" are Det terminals in the lexicon. -/
def φ' : Tree Cat String := φ.leafSubst "some" "every" .Det

-- ════════════════════════════════════════════════════════════════════
-- § Compositional Interpretation (on the same trees)
-- ════════════════════════════════════════════════════════════════════

/-- "Some student sleeps" is true: John is a student and sleeps.

    With `interpTy .t = Prop`, we state the truth condition directly at
    the Prop level rather than via `evalTree` (which requires a blanket
    `Decidable` instance for all propositions). -/
theorem some_student_sleeps :
    some_sem toyModel student_sem sleeps_sem :=
  ⟨ToyEntity.john, trivial, trivial⟩

/-- The scalar alternative "every student sleeps" is false:
Mary is a student but doesn't sleep. -/
theorem every_student_sleeps :
    ¬ every_sem toyModel student_sem sleeps_sem := by
  intro h; exact h ToyEntity.mary trivial

/-- The two readings differ: genuine scalar inference.
Asserting "some" when "every" was available implicates ¬"every".
The asymmetry is witnessed: "some" is satisfiable (John), while
"every" is refuted (Mary is a student who doesn't sleep). -/
theorem readings_differ :
    some_sem toyModel student_sem sleeps_sem ∧
    ¬ every_sem toyModel student_sem sleeps_sem :=
  ⟨some_student_sleeps, every_student_sleeps⟩

-- ════════════════════════════════════════════════════════════════════
-- § Symmetry Breaking
-- ════════════════════════════════════════════════════════════════════

/-! The symmetry problem: for any stronger alternative φ' = "every",
there exists a symmetric alternative φ'' = "some but not all" which
is also stronger. Naïve exhaustivity would predict no implicature.

Katzir's solution: φ'' requires ConjP and NegP structure, which
cannot be generated from L(φ) = lexicon ∪ subtrees(φ) because
the source tree φ contains neither category. -/

/-- φ contains no ConjP anywhere in its structure. -/
theorem no_conjp : φ.containsCat Cat.ConjP = false := by native_decide

/-- φ contains no NegP anywhere in its structure. -/
theorem no_negp : φ.containsCat Cat.NegP = false := by native_decide

/-- None of φ's subtrees contain ConjP either. -/
theorem subtrees_lack_conjp :
    φ.subtrees.all (λ t => !t.containsCat Cat.ConjP) = true := by native_decide

-- Therefore: "some but not all students sleep" requires introducing
-- ConjP and NegP structure not available in L(φ), so it is not a
-- structural alternative. The scalar implicature ¬"every" is licensed.

end Phenomena.ScalarImplicatures.Studies.Katzir2007
