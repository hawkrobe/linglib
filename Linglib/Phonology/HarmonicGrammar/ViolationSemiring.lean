import Linglib.Core.Optimization.Evaluation
import Linglib.Phonology.Constraints.Profile
import Linglib.Phonology.HarmonicGrammar.OTLimit
import Mathlib.Algebra.Tropical.Basic

/-!
# Violation Semiring — OT/HG Unification
[riggle-2009]

OT and HG are instances of a single algebraic framework: evaluation over
a commutative semiring. Violation profiles form a commutative semiring V
(the **violation semiring**); real-valued costs form the standard tropical
semiring T. HG weights define a structure-preserving map from V to T.

## The two semirings (Example 2 of [riggle-2009])

**V** = `Tropical (WithTop (ViolationProfile n))` — the **violation semiring**:
- ⊕ (tropical addition) = `min` under harmonic inequality (choose winner)
- ⊗ (tropical multiplication) = componentwise `+` (merge violations)
- 0̃ = ⊤ (V^∞ — the infinitely bad candidate, additive identity for `min`)
- 1̃ = zero profile (∅ — the perfect candidate, multiplicative identity)

**T** = `Tropical (WithTop ℝ≥0)` — the **tropical semiring**:
- ⊕ = `min` of costs (choose winner)
- ⊗ = `+` of costs (merge costs)
- 0̃ = ∞ (infinitely bad, identity for `min`)
- 1̃ = 0 (no cost, identity for `+`)

OT evaluates in V; HG evaluates in T. The weight assignment
w : Fin n → ℝ induces a map V → T via the weighted sum v ↦ Σ wᵢ · vᵢ.
This map always preserves ⊗ (merge/tropical multiplication — linearity
of the dot product). It preserves ⊕ (min/tropical addition) when weights
are exponentially separated — which is exactly the content of the HG–OT
agreement theorem ([smolensky-legendre-2006], formalized in
`HarmonicGrammar.OTLimit`).

## Monotonicity (Dijkstra's Principle)

In both V and T, merging violations can only make things worse:
∀ a b, a ≤ a ⊎ b. This is the property that makes shortest-path
algorithms applicable to OT optimization. Riggle: "every subpath of
an optimal input–output mapping is itself an optimal mapping."
-/

namespace HarmonicGrammar.ViolationSemiring


open Core.Optimization.Evaluation Constraints

-- ============================================================================
-- § 1: The Violation Semiring V
-- ============================================================================

/-- The **violation semiring** ([riggle-2009] Definition 2, Example 2):
    `Tropical (WithTop (ViolationProfile n))` for n ranked constraints.

    Tropical addition (⊕) is `min` under harmonic inequality.
    Tropical multiplication (⊗) is componentwise violation addition.
    The semiring structure is derived, not stipulated:
    `ViolationProfile n` = `Lex (Fin n → Nat)` carries `LinearOrder`
    (from `Pi.Lex`), `AddCommMonoid` (componentwise), and
    `IsOrderedCancelAddMonoid`, and mathlib's `Tropical`/`WithTop`
    wrappers do the rest. -/
abbrev VS (n : Nat) := Tropical (WithTop (ViolationProfile n))

/-- The violation semiring is a commutative semiring. -/
noncomputable instance (n : Nat) : CommSemiring (VS n) := inferInstance

-- ============================================================================
-- § 2: Monotonicity — Dijkstra's Principle
-- ============================================================================

/-- **Dijkstra's principle** for violation profiles
    ([riggle-2009] §4, [dijkstra-1959]):
    merging violations can only make things worse (or keep them equal).

    In Riggle's terms: the ⊎ (merge) operator is **monotone** —
    A ⊎ B ≥ A for all violation profiles A, B. Equivalently, the
    ⊗ (min) operator is **idempotent** — A ⊗ A = A.

    This is the structural property that makes shortest-path algorithms
    applicable to OT optimization: "every piece of an optimal
    input–output mapping is itself an optimal mapping." -/
theorem merge_monotone (n : Nat) (a b : ViolationProfile n) :
    a ≤ a + b :=
  le_add_of_nonneg_right (ViolationProfile.zero_le b)

/-- The ⊗ (min) operation is idempotent: A ⊗ A = A. This is a direct
    consequence of `LinearOrder` and is the property Riggle identifies
    as guaranteeing reflexivity and antisymmetry of the harmonic ordering.
    Idempotency of ⊗ together with monotonicity of ⊎ make the violation
    semiring a **Kleene algebra** suitable for shortest-path computation. -/
noncomputable example (n : Nat) (a : ViolationProfile n) :
    min a a = a := min_self a

-- ============================================================================
-- § 3: Weight Map V → ℝ (AddMonoidHom)
-- ============================================================================

/-- The **weight map** ([riggle-2009] §4): an additive monoid
    homomorphism from the violation semiring's underlying monoid
    `(ViolationProfile n, +, 0)` to `(ℝ, +, 0)`.

    Given weights `w : Fin n → ℝ`, the weight map sends a violation
    profile `v` to the weighted sum `Σ wᵢ · vᵢ`. This is the function
    that maps V to T — the violation semiring to the tropical semiring.

    Bundling as `AddMonoidHom` makes the homomorphism property
    (`weight(a ⊎ b) = weight(a) + weight(b)`) structural rather than
    propositional, and unlocks mathlib's homomorphism lemmas (`map_sum`,
    `map_nsmul`, etc.).

    Equivalently, this says the weight map preserves **tropical
    multiplication** (⊗) from V to T — always true by linearity of
    the dot product, regardless of weight magnitudes. The interesting
    condition (exponential separation) is needed for preserving
    **tropical addition** (⊕ = min) — see `weightMap_strictMono`. -/
def weightMap {n : Nat} (w : Fin n → ℝ) : ViolationProfile n →+ ℝ where
  toFun v := Finset.univ.sum fun i => w i * (v i : ℝ)
  map_zero' := by simp
  map_add' a b := by
    simp only [← Finset.sum_add_distrib]
    congr 1; ext i
    show w i * ((a i + b i : Nat) : ℝ) = w i * (a i : ℝ) + w i * (b i : ℝ)
    push_cast; ring

-- ============================================================================
-- § 4: Bridge to Existing HG Code
-- ============================================================================

/-- `weightMap` is definitionally equal to `weightedViolations`
    from `HarmonicGrammar.OTLimit`.

    This bridges the semiring-theoretic framework (violation profiles as
    algebraic objects) to the existing HG–OT agreement machinery
    (violation vectors as functions). -/
theorem weightMap_eq_weightedViolations {n : Nat}
    (w : Fin n → ℝ) (v : ViolationProfile n) :
    weightMap w v = weightedViolations w v := rfl

-- ============================================================================
-- § 5: Order-Preservation (⊕-compatibility)
-- ============================================================================

/-- **The weight map is strictly order-preserving** when weights are
    exponentially separated ([riggle-2009] §4,
    [smolensky-legendre-2006] ch. 14):

    If `a < b` lexicographically and all violations are bounded by `M`,
    then `weight(a) < weight(b)`.

    In tropical semiring terms: the weight map preserves **tropical
    addition** (⊕ = min) — it maps the lex-minimum in V to the
    numerical minimum in T. This is the content that exponential
    separation buys: the weight map is not just a monoid homomorphism
    (preserves ⊗ always, § 3) but an **order-preserving** monoid
    homomorphism (preserves ⊕ conditionally).

    The proof delegates to `lex_imp_lower_violations` from `OTLimit.lean`,
    which is stated over `<` on `ViolationProfile` directly. -/
theorem weightMap_strictMono {n : Nat} (w : Fin n → ℝ) (M : Nat)
    (hw : ExponentiallySeparated w M)
    (a b : ViolationProfile n)
    (hM : ∀ i, a i ≤ M ∧ b i ≤ M)
    (hab : a < b) :
    weightMap w a < weightMap w b :=
  lex_imp_lower_violations w M a b hM hw hab

/-- Non-strict monotonicity: `a ≤ b` lexicographically implies
    `weight(a) ≤ weight(b)` under exponential separation. -/
theorem weightMap_mono {n : Nat} (w : Fin n → ℝ) (M : Nat)
    (hw : ExponentiallySeparated w M)
    (a b : ViolationProfile n)
    (hM : ∀ i, a i ≤ M ∧ b i ≤ M)
    (hab : a ≤ b) :
    weightMap w a ≤ weightMap w b := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_refl _
  · exact le_of_lt (weightMap_strictMono w M hw a b hM hlt)

/-- The lex-minimum of a candidate set maps to the weight-minimum:
    the OT winner and HG winner coincide under exponential separation.

    This is the semiring-theoretic restatement of HG–OT agreement:
    `argmin_V ↦ argmin_T` when the weight map preserves both ⊗ and ⊕. -/
theorem weightMap_preserves_minimum {n : Nat} (w : Fin n → ℝ) (M : Nat)
    (hw : ExponentiallySeparated w M)
    (a : ViolationProfile n)
    (S : Finset (ViolationProfile n))
    (ha : a ∈ S)
    (hmin : ∀ b ∈ S, a ≤ b)
    (hM : ∀ b ∈ S, ∀ i, b i ≤ M) :
    ∀ b ∈ S, weightMap w a ≤ weightMap w b :=
  fun b hb => weightMap_mono w M hw a b
    (fun i => ⟨hM a ha i, hM b hb i⟩) (hmin b hb)

end HarmonicGrammar.ViolationSemiring
