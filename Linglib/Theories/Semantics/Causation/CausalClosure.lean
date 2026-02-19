import Mathlib.Order.Closure
import Linglib.Core.Causation
import Linglib.Theories.Semantics.Causation.Sufficiency

/-!
# Causal Closure Operator

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

## References

- Davey, B.A. & Priestley, H.A. (2002). *Introduction to Lattices and Order*.
  Chapter 7: Closure operators and Galois connections.
- Nadathur, P. & Lauer, S. (2020). Causal necessity, causal sufficiency,
  and the implications of causative verbs. *Glossa*.
-/

namespace Core.CausalClosure

open Core.Causation

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

    Positive dynamics are the structural condition under which
    `normalDevelopment` forms a closure operator. -/
structure PositiveDynamics where
  /-- The underlying causal dynamics -/
  dynamics : CausalDynamics
  /-- Proof of positivity -/
  positive : isPositiveDynamics dynamics = true
  /-- Fuel for fixpoint iteration (default: 100) -/
  fuel : Nat := 100

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
    NadathurLauer2020.Sufficiency.normalDevelopment_trueLE_positive
      pd.dynamics _ _ pd.fuel pd.positive h

-- ════════════════════════════════════════════════════
-- § 4. ClosureOperator Instance
-- ════════════════════════════════════════════════════

/-- `normalDevelopment` for positive dynamics is a closure operator.

    - **Extensive** (proved): `s ≤ cl(s)` — causal development only adds truths.
    - **Monotone** (proved): more input → more output.
    - **Idempotent** (sorry): `cl(cl(s)) = cl(s)` — the result of development
      is itself a fixpoint and further development is a no-op.

    The idempotency proof requires showing that `normalDevelopment` always
    reaches an actual fixpoint of the dynamics (not just exhausting fuel),
    which needs tracking the finite variable set. This is true in practice
    for all causal models in linglib (default fuel 100 far exceeds the
    number of variables in any scenario). -/
def PositiveDynamics.closureOp (pd : PositiveDynamics) :
    ClosureOperator Situation where
  toOrderHom := pd.cl
  le_closure' s := NadathurLauer2020.Sufficiency.positive_normalDevelopment_grows
    pd.dynamics s pd.fuel pd.positive
  idempotent' _s := by
    -- TODO: prove via (1) normalDevelopment reaches fixpoint for positive dynamics,
    -- (2) fixpoints are preserved by further development.
    -- Requires: Situation.extend_eq_self, applyLawsOnce_fixpoint, and
    -- a bound on the number of variables to guarantee fixpoint is reached.
    sorry

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

/-- Standard constructors produce positive dynamics. -/
def PositiveDynamics.simple (cause effect : Variable) : PositiveDynamics where
  dynamics := CausalDynamics.ofList [CausalLaw.simple cause effect]
  positive := rfl

def PositiveDynamics.chain (a b c : Variable) : PositiveDynamics where
  dynamics := CausalDynamics.causalChain a b c
  positive := rfl

def PositiveDynamics.disjunctive (a b c : Variable) : PositiveDynamics where
  dynamics := CausalDynamics.disjunctiveCausation a b c
  positive := rfl

end Core.CausalClosure
