import Linglib.Syntax.Tree.Cat
import Linglib.Semantics.Composition.Tree
import Linglib.Fragments.English.Toy
import Linglib.Semantics.Quantification.Quantifier
import Linglib.Semantics.Alternatives.Structural

/-!
# Katzir 2007: Structurally-Defined Alternatives (End-to-End)
[katzir-2007]

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
2. Generate φ' = "every student sleeps" via `leafSubst` and prove it is a
   genuine structural alternative (`φ' ∈ structuralAlternatives`) through
   the `Alternatives.Structural` substrate
3. Interpret both: ⟦φ⟧ = true, ⟦φ'⟧ = false → asserting φ implicates ¬φ'
4. Prove the symmetric "some but not all" (a ConjP) is NOT a structural
   alternative via the substrate's `category_preservation`

This is Katzir's solution to the symmetry problem: structural
constraints on alternatives prevent the symmetric alternative
from being generated, licensing the scalar implicature. The
alternative-generation and exclusion claims are stated about the
canonical `Alternatives.Structural` operators, not re-derived locally.
-/

namespace Katzir2007

open Syntax
open Semantics.Composition.Tree
open Alternatives.Structural
open Semantics.Montague (ToyEntity)
open Semantics.Montague.ToyLexicon (sleeps_sem student_sem)
open Quantification (some_sem every_sem)

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

/-- The lexicon for this fragment: the Det scale-mates plus the content
words of φ, as `Tree Cat String` terminals. Feeds the substitution
source `L(φ) = katzirLex ∪ subtrees(φ)`. -/
def katzirLex : List (Tree Cat String) :=
  [.terminal .Det "some", .terminal .Det "every",
   .terminal .N "student", .terminal .V "sleeps"]

/-- φ' is a genuine **structural** alternative to φ, derived through the
[katzir-2007] substrate (`Alternatives.Structural`): leaf substitution of
the Det scale-mate "every" (in `katzirLex`) is a chain of `StructOp.subst`
steps, so `φ' ∈ A_str(φ)` by `horn_alternatives_are_structural`. This
states the study's alternative-generation claim about the canonical
`structuralAlternatives`, not a local re-encoding. -/
theorem φ'_is_structural_alternative :
    φ' ∈ structuralAlternatives katzirLex φ :=
  horn_alternatives_are_structural katzirLex φ "some" "every" .Det
    (by simp [katzirLex]) (by simp [katzirLex])

-- ════════════════════════════════════════════════════════════════════
-- § Compositional Interpretation (on the same trees)
-- ════════════════════════════════════════════════════════════════════

/-- "Some student sleeps" is true: John is a student and sleeps.

    With `interpTy .t = Prop`, we state the truth condition directly at
    the Prop level rather than via `evalTree` (which requires a blanket
    `Decidable` instance for all propositions). -/
theorem some_student_sleeps :
    some_sem student_sem sleeps_sem :=
  ⟨ToyEntity.john, trivial, trivial⟩

/-- The scalar alternative "every student sleeps" is false:
Mary is a student but doesn't sleep. -/
theorem every_student_sleeps :
    ¬ every_sem student_sem sleeps_sem := by
  intro h; exact h ToyEntity.mary trivial

/-- The two readings differ: genuine scalar inference.
Asserting "some" when "every" was available implicates ¬"every".
The asymmetry is witnessed: "some" is satisfiable (John), while
"every" is refuted (Mary is a student who doesn't sleep). -/
theorem readings_differ :
    some_sem student_sem sleeps_sem ∧
    ¬ every_sem student_sem sleeps_sem :=
  ⟨some_student_sleeps, every_student_sleeps⟩

-- ════════════════════════════════════════════════════════════════════
-- § Symmetry Breaking
-- ════════════════════════════════════════════════════════════════════

/-! The symmetry problem: for any stronger alternative φ' = "every",
there exists a symmetric alternative φ'' = "some but not all" which
is also stronger. Naïve exhaustivity would predict no implicature.

Katzir's solution: φ'' requires ConjP and NegP structure, which
cannot be generated from L(φ) = lexicon ∪ subtrees(φ) because
the source tree φ contains neither category. We discharge this through
the substrate's `category_preservation`, not by raw `containsCat`
assertions — the same mechanism that proves
`Alternatives.Structural.symmetry_problem_solved`, here on the
QR-structured `Tree Cat String`. -/

/-- The symmetric alternative φ'' = "some but not all student sleeps",
with the Det position filled by a ConjP. -/
def φ'' : Tree Cat String :=
  .node .S [
    .node .DP [
      .node .ConjP [
        .terminal .Det "some",
        .terminal .Conj "but",
        .node .NegP [.terminal .Neg "not", .terminal .Det "every"]],
      .terminal .N "student"],
    .bind 1 .S
      (.node .S [.trace 1 .NP, .node .VP [.terminal .V "sleeps"]])]

/-- φ contains no ConjP anywhere in its structure. -/
theorem no_conjp : φ.containsCat Cat.ConjP = false := by decide

/-- φ contains no NegP anywhere in its structure. -/
theorem no_negp : φ.containsCat Cat.NegP = false := by decide

/-- No item in `L(φ) = katzirLex ∪ subtrees(φ)` contains ConjP: the
lexicon is flat Det/N/V terminals and φ's subtrees are ConjP-free. -/
theorem source_lacks_conjp :
    (substitutionSource katzirLex φ).all
      (fun t => !t.containsCat Cat.ConjP) = true := by decide

/-- φ'' does contain ConjP. -/
theorem φ''_has_conjp : φ''.containsCat Cat.ConjP = true := by decide

/-- **The symmetry problem, solved through the substrate.** φ'' is NOT a
structural alternative to φ: by `category_preservation`, every tree in
`A_str(φ)` lacks ConjP (no source item introduces it), but φ'' contains
ConjP. So the scalar implicature ¬"every" is licensed — no symmetric
alternative blocks it. This consumes
`Alternatives.Structural.category_preservation` rather than re-deriving
the argument from `containsCat`. -/
theorem symmetric_not_structural :
    φ'' ∉ structuralAlternatives katzirLex φ := by
  intro h
  have h_pres := category_preservation
    (substitutionSource katzirLex φ) Cat.ConjP φ φ''
    (by intro s hs
        have := List.all_eq_true.mp source_lacks_conjp s hs
        simp at this; exact this)
    no_conjp
    h
  exact absurd φ''_has_conjp (by rw [h_pres]; decide)

end Katzir2007
