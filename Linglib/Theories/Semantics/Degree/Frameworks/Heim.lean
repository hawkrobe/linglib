import Linglib.Core.Scale
import Linglib.Theories.Semantics.Degree.Core
import Linglib.Theories.Semantics.Degree.Frameworks.Kennedy

/-!
# Heim's Sentential Operator Approach

Heim (2001) "Degree Operators and Scope": the comparative morpheme
`-er` is a sentential operator that introduces degree variables via
λ-abstraction, rather than being a degree quantifier as in Kennedy's
approach.

## Key Differences from Kennedy

| Feature         | Kennedy                  | Heim                     |
|-----------------|--------------------------|--------------------------|
| Type of -er     | degree quantifier        | sentential operator      |
| Degree binding  | -er binds degree var     | λ-abstraction            |
| Than-clause     | degree clause (type d)   | degree predicate (d → t) |
| Scope           | DP-internal scope        | clausal scope            |

## Denotation

    ⟦-er⟧ = λD₂.λD₁. max(D₁) > max(D₂)

where D₁ and D₂ are degree predicates (sets of degrees):
- D₁ = the matrix degree clause (abstracting over d)
- D₂ = the than-clause degree predicate

## Scope Predictions

The sentential operator approach predicts scope interactions with
other operators (negation, modals, quantifiers) that the degree
quantifier approach does not, because -er takes scope at the clause
level.

## References

- Heim, I. (2001). Degree operators and scope. In *Audiatur Vox
  Sapientiae*, ed. C. Féry & W. Sternefeld, 214-239.
- Heim, I. (2006). Little. In *Proceedings of SALT 16*.
-/

namespace Semantics.Degree.Frameworks.Heim

open Core.Scale

-- ════════════════════════════════════════════════════
-- § 1. Degree Abstraction
-- ════════════════════════════════════════════════════

/-- A degree predicate: a set of degrees.
    In Heim's framework, both the matrix clause and the than-clause
    denote degree predicates after degree abstraction.

    Example: "John is d-tall" = λd. height(John) ≥ d
    This is the same as Kennedy's adjective denotation, but Heim
    treats it as the result of degree abstraction rather than the
    lexical entry of the adjective. -/
def DegreePredicate (D : Type*) := D → Prop

/-- The matrix degree predicate: abstracting over the degree variable
    in "A is d-tall" yields λd. μ(A) ≥ d.
    This is the degree set of A. -/
def matrixPredicate {Entity D : Type*} [Preorder D]
    (μ : Entity → D) (a : Entity) : DegreePredicate D :=
  fun d => μ a ≥ d

/-- The than-clause degree predicate: abstracting over the degree
    variable in "B is d-tall" yields λd. μ(B) ≥ d.
    This is the degree set of B. -/
def thanClausePredicate {Entity D : Type*} [Preorder D]
    (μ : Entity → D) (b : Entity) : DegreePredicate D :=
  fun d => μ b ≥ d

-- ════════════════════════════════════════════════════
-- § 2. -er as Sentential Operator
-- ════════════════════════════════════════════════════

/-- Heim's `-er` as a sentential operator over degree predicates.

    ⟦-er⟧(D₂)(D₁) = max(D₁) > max(D₂)

    When D₁ and D₂ are degree sets of entities A and B, this
    yields: height(A) > height(B). -/
def heimComparative {D : Type*} [LinearOrder D]
    (d1Max d2Max : D) : Prop :=
  d1Max > d2Max

/-- Heim comparative with measure function: same truth conditions as
    Kennedy, but different compositional derivation.

    "A is taller than B" via Heim:
    ⟦-er⟧(λd. height(B) ≥ d)(λd. height(A) ≥ d) = height(A) > height(B) -/
def heimComparativeWithMeasure {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) : Prop :=
  μ a > μ b

-- ════════════════════════════════════════════════════
-- § 3. Scope Predictions
-- ════════════════════════════════════════════════════

/-- Heim's approach predicts scope ambiguities with modals.
    "The paper is required to be longer than that."
    - -er > required: there's a length d such that the paper must be at least d-long
    - required > -er: for each requirement, the paper meets the length threshold

    Kennedy's degree quantifier approach does not predict the wide-scope
    -er reading (because -er is DP-internal). -/
inductive ComparativeScopeReading where
  | wideScope   -- -er scopes above other operators
  | narrowScope -- -er scopes below other operators
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 4. Kennedy–Heim Equivalence
-- ════════════════════════════════════════════════════

/-- **Extensional equivalence**: Kennedy and Heim yield the same truth
    conditions for simple comparatives. They differ only in scope
    predictions with other operators. -/
theorem kennedy_heim_extensional_equivalence {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) :
    heimComparativeWithMeasure μ a b ↔
      Semantics.Degree.Frameworks.Kennedy.kennedyComparative μ a b :=
  Iff.rfl

end Semantics.Degree.Frameworks.Heim
