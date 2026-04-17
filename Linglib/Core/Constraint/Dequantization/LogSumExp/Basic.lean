import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Log-Sum-Exp: The Warped Semiring Bridging MaxEnt and Max-Plus
@cite{cohen-smith-zaidan-2008} @cite{eisner-2002}

The log-sum-exp operator at temperature `α > 0`,
    `lse α a b := (1/α) · log(exp(α·a) + exp(α·b))`,
is the additive operator of a commutative ("warped") semiring on ℝ
whose multiplicative operator is `+`. Three things to know:

1. **Algebra**: it satisfies commutativity, associativity, and the
   semiring distributivity `d + (a ⊕_α b) = (d + a) ⊕_α (d + b)` for
   all `α ≠ 0`. Identity is `-∞` (omitted here; see `WithBot ℝ` for
   the typeclass-level packaging).
2. **Limit** (in `LogSumExp/Limit.lean`): as `α → ∞`, `lse α a b → max a b`.
3. **Bridge to softmax** (in `Decoder.lean` extensions): the softmax
   probability admits the partition-function form
   `softmax α s c = exp(α · (s c - lseFinset α s f))`, which collapses
   the softmax → argmax limit to the lse → max limit.

## Important caveat

LSE is *not* idempotent at finite α — `lse α a a = a + log 2 / α`. So
while it is a commutative semiring, it is not a Kleene algebra.
Idempotency is exactly what is recovered in the `α → ∞` limit, and is
what makes max-plus suitable for shortest-path style computation. The
"warp" terminology emphasises this deviation from idempotence:
`lse α` only behaves like `max` up to a temperature-dependent slack.
-/

namespace Core.Constraint

open Real Finset

-- ============================================================================
-- § 1: Binary log-sum-exp
-- ============================================================================

/-- Log-sum-exp at temperature `α`:
    `lse α a b := (1/α) · log(exp(α·a) + exp(α·b))`. -/
noncomputable def lse (α a b : ℝ) : ℝ :=
  (1/α) * log (exp (α*a) + exp (α*b))

/-- Cancellation identity (`α ≠ 0`):
    `exp(α · lse α a b) = exp(α·a) + exp(α·b)`.

    This is the key building block — every algebraic identity for `lse`
    reduces to an identity inside the `log`, accessed by exponentiating
    both sides and using this lemma. -/
theorem exp_alpha_lse (α : ℝ) (hα : α ≠ 0) (a b : ℝ) :
    exp (α * lse α a b) = exp (α*a) + exp (α*b) := by
  unfold lse
  have hpos : 0 < exp (α*a) + exp (α*b) := by positivity
  rw [show α * (1/α * log (exp (α*a) + exp (α*b)))
        = log (exp (α*a) + exp (α*b)) by field_simp]
  exact Real.exp_log hpos

/-- LSE is commutative. -/
theorem lse_comm (α a b : ℝ) : lse α a b = lse α b a := by
  unfold lse; rw [add_comm]

/-- LSE is associative (for `α ≠ 0`).

    Proof: both sides equal `(1/α) · log(exp(α·a) + exp(α·b) + exp(α·c))`
    by the cancellation identity `exp_alpha_lse`. -/
theorem lse_assoc (α : ℝ) (hα : α ≠ 0) (a b c : ℝ) :
    lse α (lse α a b) c = lse α a (lse α b c) := by
  show (1/α) * log (exp (α * lse α a b) + exp (α*c))
       = (1/α) * log (exp (α*a) + exp (α * lse α b c))
  rw [exp_alpha_lse α hα a b, exp_alpha_lse α hα b c]
  congr 1
  ring_nf

/-- The semiring distributivity law: `+` distributes over `lse α` (for
    `α ≠ 0`).

    Equivalently, multiplication by `exp(α·d)` distributes over the
    sum inside the log. This is the "multiplicative" axiom of the warped
    semiring `(ℝ, lse α, +)` — the analogue of `d * (a + b) = d*a + d*b`. -/
theorem add_lse (α : ℝ) (hα : α ≠ 0) (d a b : ℝ) :
    d + lse α a b = lse α (d + a) (d + b) := by
  unfold lse
  have hpos : 0 < exp (α*a) + exp (α*b) := by positivity
  have hexpd : (0 : ℝ) < exp (α*d) := exp_pos _
  have key : exp (α*(d+a)) + exp (α*(d+b))
              = exp (α*d) * (exp (α*a) + exp (α*b)) := by
    rw [mul_add (exp (α*d)), ← exp_add, ← exp_add]
    congr 1 <;> ring_nf
  rw [key, Real.log_mul hexpd.ne' hpos.ne', Real.log_exp]
  field_simp

/-- The non-idempotency identity: `lse α a a = a + log 2 / α` for `α ≠ 0`.

    This is the precise statement that LSE is NOT a tropical/max-plus
    operation at finite α — there is a `log 2 / α` "slack" that vanishes
    only in the `α → ∞` limit. -/
theorem lse_self (α : ℝ) (hα : α ≠ 0) (a : ℝ) :
    lse α a a = a + log 2 / α := by
  unfold lse
  have h : exp (α*a) + exp (α*a) = 2 * exp (α*a) := by ring
  rw [h, Real.log_mul (by norm_num) (exp_pos _).ne', Real.log_exp]
  field_simp
  ring

-- ============================================================================
-- § 2: n-ary log-sum-exp over a Finset
-- ============================================================================

/-- The n-ary log-sum-exp over a Finset:
    `lseFinset α s f := (1/α) · log(∑ c ∈ s, exp(α · f c))`.

    Equals `(1/α) · log Z` where `Z = ∑ exp(α · f c)` is the MaxEnt
    partition function. The softmax probability of `c ∈ s` then has the
    clean form `exp(α · (f c - lseFinset α s f))`. -/
noncomputable def lseFinset {C : Type*} (α : ℝ) (s : Finset C) (f : C → ℝ) : ℝ :=
  (1/α) * log (∑ c ∈ s, exp (α * f c))

/-- Cancellation: `exp(α · lseFinset α s f) = ∑ c ∈ s, exp(α · f c)`
    when `α ≠ 0` and `s` is non-empty. -/
theorem exp_alpha_lseFinset {C : Type*} (α : ℝ) (hα : α ≠ 0) {s : Finset C}
    (hne : s.Nonempty) (f : C → ℝ) :
    exp (α * lseFinset α s f) = ∑ c ∈ s, exp (α * f c) := by
  unfold lseFinset
  have hpos : 0 < ∑ c ∈ s, exp (α * f c) :=
    Finset.sum_pos (fun c _ => exp_pos _) hne
  rw [show α * (1/α * log (∑ c ∈ s, exp (α * f c)))
        = log (∑ c ∈ s, exp (α * f c)) by field_simp]
  exact Real.exp_log hpos

/-- The singleton case: `lseFinset α {c} f = f c`.

    Witnesses that the n-ary lse degenerates to the underlying score
    on a single-candidate set — there is nothing to aggregate. -/
theorem lseFinset_singleton {C : Type*} (α : ℝ) (hα : α ≠ 0) (c : C) (f : C → ℝ) :
    lseFinset α ({c} : Finset C) f = f c := by
  unfold lseFinset
  rw [Finset.sum_singleton, Real.log_exp]
  field_simp

end Core.Constraint
