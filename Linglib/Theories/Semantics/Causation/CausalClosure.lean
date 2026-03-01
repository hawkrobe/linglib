import Mathlib.Order.Closure
import Linglib.Core.StructuralEquationModel
import Linglib.Theories.Semantics.Causation.Sufficiency

/-!
# Causal Closure Operator
@cite{davey-priestley-2002} @cite{nadathur-lauer-2020}

The algebraic root of causal reasoning: for positive dynamics,
`normalDevelopment` is a **closure operator** on `(Situation, trueLE)`.

## The Three Axioms

For positive dynamics `dyn` with fuel `f`:
1. **Extensive**: `s ≤ cl(s)` — development only adds truths
2. **Monotone**: `s₁ ≤ s₂ → cl(s₁) ≤ cl(s₂)` — more input, more output
3. **Idempotent**: `cl(cl(s)) = cl(s)` — fixpoint stability

## Why This Matters

Causal sufficiency IS closure membership: `causallySufficient dyn s t c`
iff `c = true ∈ cl(s + {t = true})`. This single observation unifies
ability modals (*be able*), implicative verbs (*manage*), and degree
constructions (*enough/too*) — all are membership tests in different
closures with different triggers.

## Levels of Abstraction

- **Level 1 (this file)**: `ClosureOperator Situation` for positive dynamics
- **Level 2 (future)**: Galois connection `(cl, ι)` decomposing cl = ι ∘ l
- **Level 3 (future)**: Scott Information System unifying all situation-like
  objects in linglib (causal, dynamic, modal, presuppositional)

-/

namespace Core.CausalClosure

open Core.StructuralEquationModel

-- ════════════════════════════════════════════════════
-- § 1. Preorder on Situation
-- ════════════════════════════════════════════════════

/-- The true-content preorder on `Situation`: `s₁ ≤ s₂` iff every variable
    that is `true` in `s₁` is also `true` in `s₂`.

    This is NOT antisymmetric: two situations can agree on all true values
    while differing on false/undetermined assignments. Hence `Preorder`,
    not `PartialOrder`. -/
instance : Preorder Situation where
  le := Situation.trueLE
  le_refl := Situation.trueLE_refl
  le_trans := fun _ _ _ => Situation.trueLE_trans

-- ════════════════════════════════════════════════════
-- § 2. Positive Dynamics Bundle
-- ════════════════════════════════════════════════════

/-- A `PositiveDynamics` bundles causal dynamics with:
    - A proof that all laws have positive preconditions and effects
      (no inhibitory connections)
    - A fuel budget for fixpoint iteration
    - A proof that fuel is sufficient to always reach a fixpoint

    Positive dynamics are the structural condition under which
    `normalDevelopment` forms a closure operator. The `reachesFP`
    field guarantees that `fuel` is enough for the dynamics to
    converge from any starting situation — without this, idempotency
    of the closure operator cannot be proved. -/
structure PositiveDynamics where
  /-- The underlying causal dynamics -/
  dynamics : CausalDynamics
  /-- Proof of positivity -/
  positive : isPositiveDynamics dynamics = true
  /-- Fuel for fixpoint iteration (default: 100) -/
  fuel : Nat := 100
  /-- Fuel is sufficient: normalDevelopment always reaches a fixpoint. -/
  reachesFP : ∀ s, isFixpoint dynamics (normalDevelopment dynamics s fuel) = true

-- ════════════════════════════════════════════════════
-- § 3. Monotone Closure Function
-- ════════════════════════════════════════════════════

/-- The closure function as a monotone map on `(Situation, trueLE)`.

    `pd.cl s = normalDevelopment pd.dynamics s pd.fuel`

    Monotonicity: if `s₁ ≤ s₂` then `cl(s₁) ≤ cl(s₂)`. This follows
    from the fact that positive dynamics only have positive preconditions,
    so more true values in the input means more law firings. -/
def PositiveDynamics.cl (pd : PositiveDynamics) : Situation →o Situation where
  toFun s := normalDevelopment pd.dynamics s pd.fuel
  monotone' := fun {_a} {_b} (h : Situation.trueLE _ _) =>
    normalDevelopment_trueLE_positive
      pd.dynamics _ _ pd.fuel pd.positive h

-- ════════════════════════════════════════════════════
-- § 4. ClosureOperator Instance
-- ════════════════════════════════════════════════════

/-- `normalDevelopment` for positive dynamics is a closure operator.

    - **Extensive** (proved): `s ≤ cl(s)` — causal development only adds truths.
    - **Monotone** (proved): more input → more output.
    - **Idempotent** (proved): `cl(cl(s)) = cl(s)` — the result of development
      is itself a fixpoint and further development is a no-op.

    Idempotency follows from the `reachesFP` field of `PositiveDynamics`:
    the first application reaches a fixpoint, and `normalDevelopment_of_fixpoint`
    shows that running from a fixpoint is a no-op. -/
def PositiveDynamics.closureOp (pd : PositiveDynamics) :
    ClosureOperator Situation where
  toOrderHom := pd.cl
  le_closure' s := positive_normalDevelopment_grows
    pd.dynamics s pd.fuel pd.positive
  idempotent' s := normalDevelopment_of_fixpoint (pd.reachesFP s) pd.fuel

-- ════════════════════════════════════════════════════
-- § 5. Sufficiency = Closure Membership
-- ════════════════════════════════════════════════════

/-- **Causal sufficiency is closure membership.**

    `causallySufficient dyn s trigger complement` holds iff
    `complement = true ∈ cl(s ⊕ {trigger = true})`.

    This is the deep structural reason that ability modals, implicative
    verbs, and degree constructions all work the same way: they all
    reduce to asking whether a complement variable is in the closure
    of a background situation extended with a trigger. -/
theorem sufficiency_as_closure_membership (dyn : CausalDynamics)
    (s : Situation) (trigger complement : Variable) :
    causallySufficient dyn s trigger complement =
      (normalDevelopment dyn (s.extend trigger true)).hasValue complement true := rfl

/-- Necessity is **complement of closure membership** under counterfactual
    removal: `causallyNecessary dyn s cause effect` holds iff
    `effect = true ∉ cl(s ⊕ {cause = false})`. -/
theorem necessity_as_closure_nonmembership (dyn : CausalDynamics)
    (s : Situation) (cause effect : Variable) :
    causallyNecessary dyn s cause effect =
      (!(normalDevelopment dyn (s.extend cause false)).hasValue effect true) := rfl

-- ════════════════════════════════════════════════════
-- § 6. Closed Elements = Causal Fixpoints
-- ════════════════════════════════════════════════════

/-- A situation is **causally closed** under `pd` if it is a fixed point
    of the closure operator: no further causal development changes it.

    These are the situations where all consequences of all present causes
    have already been computed. -/
def IsCausalFixpoint (pd : PositiveDynamics) (s : Situation) : Prop :=
  pd.closureOp s = s

-- ════════════════════════════════════════════════════
-- § 7. Standard Constructors
-- ════════════════════════════════════════════════════

/-- Helper: for a single positive law, one step of applyLawsOnce always
    reaches a fixpoint. Either preconditions are unmet (fixpoint trivially)
    or the effect is set (fixpoint because effect is now present). -/
private theorem single_positive_law_reaches_fp
    (law : CausalLaw) (s : Situation)
    (_hPosPrec : law.preconditions.all (·.2) = true)
    (hPosEff : law.effectValue = true) :
    isFixpoint ⟨[law]⟩ (applyLawsOnce ⟨[law]⟩ s) = true := by
  simp only [isFixpoint, applyLawsOnce, List.all_cons, List.all_nil,
             Bool.and_true, List.foldl_cons, List.foldl_nil]
  by_cases hMet : law.preconditionsMet s = true
  · rw [CausalLaw.apply_of_met hMet]
    simp only [Bool.or_eq_true, Bool.not_eq_true']
    right
    simp [Situation.hasValue, Situation.extend, hPosEff]
  · have : law.preconditionsMet s = false := by
      cases h : law.preconditionsMet s <;> simp_all
    rw [CausalLaw.apply_of_not_met this]
    simp only [Bool.or_eq_true, Bool.not_eq_true']
    left; exact this

-- TODO: General convergence theorem for N laws.
-- For positive dynamics with N laws, N steps of fuel suffice:
-- each non-fixpoint step sets at least one new effect (by foldl_sets_witness_effect),
-- effects never unset (monotonicity), and there are at most N effect variables.
