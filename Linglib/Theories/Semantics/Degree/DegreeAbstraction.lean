import Linglib.Core.Scales.Scale
import Linglib.Theories.Semantics.Degree.Core
import Linglib.Theories.Semantics.Degree.Comparative

/-!
# Heim's Degree Operator Approach
@cite{heim-2001}

@cite{heim-2001} "Degree Operators and Scope": degree morphemes (`-er`,
`less`, `-est`, `too`) are **generalized quantifiers over degrees** (type
⟨dt,t⟩) that take scope by QR, just like DP quantifiers. The key
theoretical content is twofold:

1. **Denotation**: ⟦-er than P⟧ = λQ. max(Q) > max(P), where max is
   the maximality operator over degree predicates.
2. **Scope**: because DegPs QR, they interact scopally with other
   operators (quantifiers, negation, modals). The paper probes which
   scope configurations are empirically available.

## Monotonicity and Scope Collapse

Adjective denotations are *monotone*: if `tall(x,d)` then `tall(x,d')`
for all `d' ≤ d`. This means max{d: tall(x,d)} = μ(x). And for
monotone increasing operators (∀, ∃), low-DegP and high-DegP yield
equivalent truth conditions — scope is undetectable.

## Comparison with Kennedy

Kennedy's `-er` is DP-internal (no QR needed), so it never takes wide
scope. The two frameworks agree extensionally on simple comparatives
but diverge on scope predictions with `exactly`-differentials, `less`,
and intensional verbs.

-/

namespace Semantics.Degree.DegreeAbstraction

open Core.Scale

-- ════════════════════════════════════════════════════
-- § 1. Degree Predicates and Maximality
-- ════════════════════════════════════════════════════

/-- A degree predicate: a set of degrees (type ⟨d,t⟩ in Heim's terms).
    Both the matrix clause and the than-clause denote degree predicates
    after degree abstraction. -/
def DegreePredicate (D : Type*) := D → Prop

/-- Heim's maximality operator (paper def. (6)):
    max(P) := ιd. P(d) ∧ ∀d', P(d') → d' ≤ d

    We define it relationally: `d` is the maximum of `P` when it
    satisfies `P` and is an upper bound. -/
def IsMaxDeg {D : Type*} [LE D] (P : DegreePredicate D) (d : D) : Prop :=
  P d ∧ ∀ d', P d' → d' ≤ d

/-- The matrix degree predicate for "A is d-tall": λd. μ(A) ≥ d. -/
def matrixPredicate {Entity D : Type*} [Preorder D]
    (μ : Entity → D) (a : Entity) : DegreePredicate D :=
  fun d => μ a ≥ d

/-- The than-clause degree predicate for "B is d-tall": λd. μ(B) ≥ d. -/
def thanClausePredicate {Entity D : Type*} [Preorder D]
    (μ : Entity → D) (b : Entity) : DegreePredicate D :=
  fun d => μ b ≥ d

/-- The maximum of a monotone predicate λd. μ(a) ≥ d is μ(a) itself.
    This grounds the Heim–Kennedy equivalence: max{d: tall(a,d)} = μ(a). -/
theorem isMaxDeg_matrixPredicate {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a : Entity) :
    IsMaxDeg (matrixPredicate μ a) (μ a) :=
  ⟨le_refl _, fun _ h => h⟩

-- ════════════════════════════════════════════════════
-- § 2. Monotonicity
-- ════════════════════════════════════════════════════

/-- An adjective denotation (type ⟨d,et⟩) is **monotone** iff
    tall(x,d) implies tall(x,d') for all d' ≤ d.

    Heim (p. 216, def. (3)): a function f of type ⟨d,et⟩ is monotone
    iff ∀x∀d∀d'[f(d)(x) = 1 & d' < d → f(d')(x) = 1]. -/
def Monotone {Entity D : Type*} [Preorder D]
    (adj : D → Entity → Prop) : Prop :=
  ∀ (x : Entity) (d d' : D), adj d x → d' ≤ d → adj d' x

/-- `matrixPredicate μ a` is always monotone (by construction). -/
theorem matrixPredicate_monotone {Entity D : Type*} [Preorder D]
    (μ : Entity → D) (a : Entity) :
    ∀ (d d' : D), matrixPredicate μ a d → d' ≤ d →
      matrixPredicate μ a d' := by
  intro d d' hd hle
  exact le_trans hle hd

-- ════════════════════════════════════════════════════
-- § 3. Degree Operators
-- ════════════════════════════════════════════════════

/-- Heim's `-er` operating on degree predicates (paper def. (6)):
    ⟦-er⟧(D₂)(D₁) = max(D₁) > max(D₂)

    Takes two degree predicates and compares their maxima. -/
def erOnPredicates {D : Type*} [LE D] [LT D]
    (_P₁ _P₂ : DegreePredicate D) (d₁ d₂ : D)
    (_h₁ : IsMaxDeg _P₁ d₁) (_h₂ : IsMaxDeg _P₂ d₂) : Prop :=
  d₁ > d₂

/-- Heim's `less` operator (paper (23)):
    ⟦less than P⟧ = λQ. max(Q) < max(P) -/
def lessOnPredicates {D : Type*} [LE D] [LT D]
    (_P₁ _P₂ : DegreePredicate D) (d₁ d₂ : D)
    (_h₁ : IsMaxDeg _P₁ d₁) (_h₂ : IsMaxDeg _P₂ d₂) : Prop :=
  d₁ < d₂

/-- Heim comparative with measure function: the result of composing
    `-er` with degree predicates derived from a monotone adjective.

    "A is taller than B" = ⟦-er⟧(λd. μ(B) ≥ d)(λd. μ(A) ≥ d)
                         = max{d: μ(A) ≥ d} > max{d: μ(B) ≥ d}
                         = μ(A) > μ(B) -/
def heimComparativeWithMeasure {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) : Prop :=
  μ a > μ b

-- ════════════════════════════════════════════════════
-- § 4. Scope Configurations
-- ════════════════════════════════════════════════════

/-- **Low-DegP** truth conditions for "every girl is taller than 4ft":
    ∀x[girl(x) → max{d: tall(x,d)} > 4']

    DegP scopes below the quantifier. Each girl's height exceeds 4'. -/
def lowDegP_forall {Entity D : Type*} [LinearOrder D]
    (restrictor : Entity → Prop) (μ : Entity → D) (threshold : D) : Prop :=
  ∀ x, restrictor x → μ x > threshold

/-- **High-DegP** truth conditions for "every girl is taller than 4ft":
    max{d: ∀x[girl(x) → tall(x,d)]} > 4'

    DegP scopes above the quantifier. The maximal degree to which
    *every* girl is tall exceeds 4'. This equals the height of the
    *shortest* girl (by monotonicity). -/
def highDegP_forall {Entity D : Type*} [LinearOrder D]
    (restrictor : Entity → Prop) (μ : Entity → D) (threshold : D) : Prop :=
  ∃ d, (∀ x, restrictor x → μ x ≥ d) ∧ d > threshold

/-- **Monotone collapse** (Heim §2.1): for ∀ + more-comparatives,
    high-DegP → low-DegP (the reverse direction).

    If there exists d > threshold s.t. every girl is d-tall, then
    every girl exceeds threshold (since μ(x) ≥ d > threshold). -/
theorem forall_more_high_to_low {Entity D : Type*} [LinearOrder D]
    (restrictor : Entity → Prop) (μ : Entity → D) (threshold : D) :
    highDegP_forall restrictor μ threshold →
    lowDegP_forall restrictor μ threshold := by
  rintro ⟨d, hall, hgt⟩ x hR
  exact lt_of_lt_of_le hgt (hall x hR)

/-- **Monotone collapse** (Heim §2.1): for ∀ + more-comparatives,
    low-DegP → high-DegP (given a witness).

    If every girl is taller than threshold, pick any girl `w` — her
    height witnesses d > threshold with ∀x.tall(x,d) being vacuously
    weak (every girl is at least threshold-tall, and w is one of them). -/
theorem forall_more_low_to_high {Entity D : Type*} [LinearOrder D]
    (restrictor : Entity → Prop) (μ : Entity → D) (threshold : D)
    (w : Entity) (hw : restrictor w)
    (hmin : ∀ x, restrictor x → μ x ≥ μ w) :
    lowDegP_forall restrictor μ threshold →
    highDegP_forall restrictor μ threshold := by
  intro hlow
  exact ⟨μ w, hmin, hlow w hw⟩

/-- Low-DegP for ∃: ∃x[girl(x) ∧ μ(x) > threshold]. -/
def lowDegP_exists {Entity D : Type*} [LinearOrder D]
    (restrictor : Entity → Prop) (μ : Entity → D) (threshold : D) : Prop :=
  ∃ x, restrictor x ∧ μ x > threshold

/-- High-DegP for ∃: max{d: ∃x[girl(x) ∧ tall(x,d)]} > threshold.
    This equals the tallest girl's height. -/
def highDegP_exists {Entity D : Type*} [LinearOrder D]
    (restrictor : Entity → Prop) (μ : Entity → D) (threshold : D) : Prop :=
  ∃ d, (∃ x, restrictor x ∧ μ x ≥ d) ∧ d > threshold

/-- Monotone collapse for ∃ + more: low ↔ high. -/
theorem exists_more_scope_collapse {Entity D : Type*} [LinearOrder D]
    (restrictor : Entity → Prop) (μ : Entity → D) (threshold : D) :
    lowDegP_exists restrictor μ threshold ↔
    highDegP_exists restrictor μ threshold := by
  constructor
  · rintro ⟨x, hR, hgt⟩
    exact ⟨μ x, ⟨x, hR, le_refl _⟩, hgt⟩
  · rintro ⟨d, ⟨x, hR, hge⟩, hgt⟩
    exact ⟨x, hR, lt_of_lt_of_le hgt hge⟩

-- ════════════════════════════════════════════════════
-- § 5. Presupposition Failure under Negation
-- ════════════════════════════════════════════════════

/-- The degree set {d : ¬(μ(x) ≥ d)} = {d : d > μ(x)}.
    This set has no maximum on an unbounded scale.
    Heim (p. 220): high-DegP over negation is ruled out because
    max{d: ¬tall(m,d)} is undefined. -/
def negatedDegreePredicate {Entity D : Type*} [Preorder D]
    (μ : Entity → D) (a : Entity) : DegreePredicate D :=
  fun d => ¬ (μ a ≥ d)

/-- The negated degree set is exactly {d : d > μ(a)}. -/
theorem negatedDegreePredicate_eq {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a : Entity) (d : D) :
    negatedDegreePredicate μ a d ↔ d > μ a := by
  simp [negatedDegreePredicate, not_le]

-- ════════════════════════════════════════════════════
-- § 6. Kennedy–Heim Equivalence
-- ════════════════════════════════════════════════════

/-- **Extensional equivalence**: Heim yields the same truth conditions
    as the consensus comparative semantics for simple comparatives.
    They differ only on scope predictions with `exactly`-differentials,
    `less`-comparatives, and intensional verbs (Heim §2.2–2.3). -/
theorem heim_extensional_equivalence {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) :
    heimComparativeWithMeasure μ a b ↔
      Semantics.Degree.Comparative.comparativeSem μ a b .positive :=
  Iff.rfl

end Semantics.Degree.DegreeAbstraction
