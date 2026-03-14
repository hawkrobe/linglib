import Linglib.Theories.Semantics.Composition.QuantifierComposition

/-!
# Katzir 2007: Structurally-Defined Alternatives (End-to-End)
@cite{katzir-2007}

Katzir, R. (2007). Structurally-defined alternatives.
Linguistics and Philosophy, 30(6), 669–690.

## Unified Tree Demonstration

This file demonstrates that a single `SynTree Cat String` supports both:
- **Structural operations** (PF-level): `leafSubst` generates scalar
  alternatives by same-category word substitution
- **Compositional interpretation** (LF-level): `evalSynTree` computes
  truth conditions via FA, PM, and Predicate Abstraction

One tree, two interfaces — the Y-model made concrete.

## The Argument

1. Build φ = "some student sleeps" as `SynTree Cat String` with QR
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

-- ════════════════════════════════════════════════════════════════════
-- § Source Tree
-- ════════════════════════════════════════════════════════════════════

/-- "Some student sleeps" after QR, with UD-grounded categories:
```
[S [DP [Det some] [N student]] [₁ [S [t₁:NP] [VP [V sleeps]]]]]
``` -/
def φ : SynTree Cat String :=
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
def φ' : SynTree Cat String := φ.leafSubst "some" "every" .Det

-- ════════════════════════════════════════════════════════════════════
-- § Compositional Interpretation (on the same trees)
-- ════════════════════════════════════════════════════════════════════

/-- "Some student sleeps" is true: John is a student and sleeps. -/
theorem some_student_sleeps : evalSynTree quantLex g₀ φ = some true := by
  native_decide

/-- The scalar alternative "every student sleeps" is false:
Mary is a student but doesn't sleep. -/
theorem every_student_sleeps : evalSynTree quantLex g₀ φ' = some false := by
  native_decide

/-- The two readings differ: genuine scalar inference.
Asserting "some" when "every" was available implicates ¬"every". -/
theorem readings_differ :
    evalSynTree quantLex g₀ φ ≠ evalSynTree quantLex g₀ φ' := by
  native_decide

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
