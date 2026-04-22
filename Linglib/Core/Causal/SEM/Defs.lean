import Mathlib.Logic.Function.Iterate

/-!
# Structural Equation Model: Definitions
@cite{nadathur-lauer-2020}

Core types and forward propagation for deterministic causal models.

- **Variable**: Named causal variables
- **Situation**: Partial valuations (Variable → Option Bool)
- **CausalLaw**: Structural equations (preconditions → effect)
- **CausalDynamics**: Collections of causal laws
- **normalDevelopment**: Forward propagation to fixpoint

The `trueLE` preorder, monotonicity proofs, and counterfactual queries
live in sibling files (`Monotonicity`, `Counterfactual`).
-/

namespace Core.Causal

-- ============================================================
-- § Variables and Situations
-- ============================================================

-- Variables

/-- A variable in a causal model.
    Variables are named entities whose values are determined by causal laws. -/
structure Variable where
  name : String
  deriving DecidableEq, Hashable, Repr, Inhabited

instance : BEq Variable where beq a b := decide (a = b)

instance : LawfulBEq Variable where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

instance : ToString Variable where
  toString v := v.name

/-- Create a variable from a string literal. -/
def mkVar (name : String) : Variable := ⟨name⟩

-- Situations (Def 22)

/-- **Situation** (Definition 22 from @cite{nadathur-lauer-2020})

    A partial valuation: some variables have known values, others are
    undetermined. Situations are *partial* functions — crucial for
    modeling what's "given" vs what's computed, and for counterfactual
    reasoning (removing a cause = setting it to false). -/
@[ext]
structure Situation where
  /-- The partial valuation: Variable → Option Bool -/
  valuation : Variable → Option Bool

namespace Situation

/-- The empty situation: nothing is determined. -/
def empty : Situation := ⟨λ _ => none⟩

/-- Get the value of a variable (if determined). -/
def get (s : Situation) (v : Variable) : Option Bool := s.valuation v

/-- Check if a variable has a specific value in the situation. -/
def hasValue (s : Situation) (v : Variable) (val : Bool) : Bool :=
  s.valuation v == some val

/-- **Extend** a situation with a new assignment: s ⊕ {v = val}.
    If the variable was already determined, the new value overwrites. -/
def extend (s : Situation) (v : Variable) (val : Bool) : Situation :=
  ⟨λ v' => if v' == v then some val else s.valuation v'⟩

/-- Remove a variable from the situation (set to undetermined). -/
def remove (s : Situation) (v : Variable) : Situation :=
  ⟨λ v' => if v' == v then none else s.valuation v'⟩

/-- Combine two situations (right takes precedence). -/
def merge (s1 s2 : Situation) : Situation :=
  ⟨λ v => s2.valuation v <|> s1.valuation v⟩

instance : Inhabited Situation := ⟨Situation.empty⟩

/-- Enumerate all extensions of a situation over a list of free variables.
    Each variable can be left undetermined, set true, or set false.
    Called only on variables NOT already determined in `s`.

    **Scalability**: produces 3^n situations for n free variables. This is
    acceptable for the small models in @cite{nadathur-lauer-2020} (typically
    2–4 variables) but would need pruning or symbolic reasoning for larger
    causal networks. -/
def allExtensions (s : Situation) : List Variable → List Situation
  | [] => [s]
  | v :: vs =>
    let rest := s.allExtensions vs
    rest ++ rest.map (·.extend v true) ++ rest.map (·.extend v false)

/-- Extending at `v` and querying `v` returns whether the values match. -/
@[simp] theorem extend_hasValue_same {s : Situation} {v : Variable} {val bval : Bool} :
    (s.extend v val).hasValue v bval = (val == bval) := by
  simp [hasValue, extend]

/-- Extending at `v` doesn't affect queries at a different variable `w`. -/
@[simp] theorem extend_hasValue_diff {s : Situation} {v w : Variable} {val bval : Bool}
    (h : w ≠ v) : (s.extend v val).hasValue w bval = s.hasValue w bval := by
  simp [hasValue, extend, h]

/-- Extending at a value already present is identity. -/
theorem extend_eq_self {s : Situation} {v : Variable} {val : Bool}
    (h : s.hasValue v val = true) : s.extend v val = s := by
  unfold hasValue at h; simp only [beq_iff_eq] at h
  apply Situation.ext; funext w
  simp only [extend]
  by_cases hw : w = v
  · subst hw; simp [h]
  · simp [hw]

end Situation

-- True-subset ordering on situations

/-- s₁ ⊑ s₂ in the true-content ordering: every variable `true` in s₁
    is also `true` in s₂. This is the natural preorder for reasoning about
    monotonicity of positive causal dynamics. -/
def Situation.trueLE (s₁ s₂ : Situation) : Prop :=
  ∀ v, s₁.hasValue v true = true → s₂.hasValue v true = true

theorem Situation.trueLE_refl (s : Situation) : s.trueLE s := fun _ hv => hv

theorem Situation.trueLE_trans {s₁ s₂ s₃ : Situation}
    (h₁₂ : s₁.trueLE s₂) (h₂₃ : s₂.trueLE s₃) : s₁.trueLE s₃ :=
  fun v hv => h₂₃ v (h₁₂ v hv)

-- ============================================================
-- § Causal Laws and Dynamics
-- ============================================================

-- Causal Laws (Def 10)

/-- **Causal Law** (Definition 10 from @cite{nadathur-lauer-2020})

    A causal law specifies: if all preconditions hold, the effect follows.
    In notation: ⟨{(v₁, val₁), …, (vₙ, valₙ)}, (vₑ, valₑ)⟩. -/
structure CausalLaw where
  /-- Preconditions that must all hold -/
  preconditions : List (Variable × Bool)
  /-- The variable affected by this law -/
  effect : Variable
  /-- The value the effect variable gets (default: true) -/
  effectValue : Bool := true
  deriving Repr, Inhabited

namespace CausalLaw

/-- Check if all preconditions of a law are satisfied in a situation. -/
def preconditionsMet (law : CausalLaw) (s : Situation) : Bool :=
  law.preconditions.all λ (v, val) => s.hasValue v val

/-- Apply a law to a situation (if preconditions met, set effect). -/
def apply (law : CausalLaw) (s : Situation) : Situation :=
  bif law.preconditionsMet s then
    s.extend law.effect law.effectValue
  else
    s

/-- Create a simple law: if cause = true, then effect = true. -/
def simple (cause effect : Variable) : CausalLaw :=
  { preconditions := [(cause, true)], effect := effect }

/-- Create a conjunctive law: if cause1 = true ∧ cause2 = true, then effect = true. -/
def conjunctive (cause1 cause2 effect : Variable) : CausalLaw :=
  { preconditions := [(cause1, true), (cause2, true)], effect := effect }

/-- Create an inhibitory law: if cause = false (absent), then effect = true.
    This is the structural equation B := ¬A from @cite{sloman-barbey-hotaling-2009}
    Figure 4 (eq. 4a). Inhibitory laws are the structural basis for prevention:
    the effect occurs precisely when the cause is absent. -/
def inhibitory (cause effect : Variable) : CausalLaw :=
  { preconditions := [(cause, false)], effect := effect }

/-- If preconditions are not met, applying the law is a no-op.
    Avoids leaving stuck `if false = true then …` terms in goals. -/
@[simp] theorem apply_of_not_met {law : CausalLaw} {s : Situation}
    (h : law.preconditionsMet s = false) : law.apply s = s := by
  unfold apply; rw [h]; rfl

/-- If preconditions are met, applying the law extends the situation. -/
@[simp] theorem apply_of_met {law : CausalLaw} {s : Situation}
    (h : law.preconditionsMet s = true) :
    law.apply s = s.extend law.effect law.effectValue := by
  unfold apply; rw [h]; rfl

/-- The effect variable of a simple law. -/
@[simp] theorem simple_effect (c e : Variable) :
    (simple c e).effect = e := rfl

/-- The effect value of a simple law (always `true`). -/
@[simp] theorem simple_effectValue (c e : Variable) :
    (simple c e).effectValue = true := rfl

end CausalLaw

-- Causal Dynamics

/-- **Causal Dynamics**: A collection of causal laws.
    Represents the structural equations of a causal model.
    Multiple laws can affect the same variable (disjunctive causation). -/
structure CausalDynamics where
  /-- The laws governing causal propagation -/
  laws : List CausalLaw
  deriving Repr, Inhabited

namespace CausalDynamics

/-- Empty dynamics (no causal laws). -/
def empty : CausalDynamics := ⟨[]⟩

/-- Create dynamics from a list of laws. -/
def ofList (laws : List CausalLaw) : CausalDynamics := ⟨laws⟩

/-- Disjunctive causation: A ∨ B → C. Either cause alone suffices. -/
def disjunctiveCausation (cause1 cause2 effect : Variable) : CausalDynamics :=
  ⟨[CausalLaw.simple cause1 effect, CausalLaw.simple cause2 effect]⟩

/-- Conjunctive causation: A ∧ B → C. Both causes required. -/
def conjunctiveCausation (cause1 cause2 effect : Variable) : CausalDynamics :=
  ⟨[CausalLaw.conjunctive cause1 cause2 effect]⟩

/-- Causal chain: A → B → C. -/
def causalChain (a b c : Variable) : CausalDynamics :=
  ⟨[CausalLaw.simple a b, CausalLaw.simple b c]⟩

/-- Prevention model: B := ¬A (@cite{sloman-barbey-hotaling-2009} eq. 4a).
    A single inhibitory law: if A is absent, B occurs. A's presence blocks B.
    This is the simplest dynamics for which `preventSem` returns true. -/
def prevention (preventer effect : Variable) : CausalDynamics :=
  ⟨[CausalLaw.inhibitory preventer effect]⟩

/-- Prevention with accessory: B := ¬A ∧ X (@cite{sloman-barbey-hotaling-2009} eq. 4b).
    The effect requires both the preventer's absence AND an accessory cause.
    Models "A prevents B when X is present" — e.g., "the vaccine prevents
    infection when the patient is exposed." -/
def preventionWithAccessory (preventer accessory effect : Variable) : CausalDynamics :=
  ⟨[{ preconditions := [(preventer, false), (accessory, true)], effect := effect }]⟩

end CausalDynamics

/-- A dynamics is **positive** if all preconditions require `true` and all
    effect values are `true`. Positive dynamics have no inhibitory connections:
    causes can only enable effects, never block them.

    This is the key structural condition for monotonicity results: in positive
    dynamics, adding `true` values to a situation can only enable more laws,
    never block them. -/
def isPositiveDynamics (dyn : CausalDynamics) : Bool :=
  dyn.laws.all (fun law => law.preconditions.all (·.2) && law.effectValue)

/-- All variables mentioned in a dynamics (preconditions and effects). -/
def allVariables (dyn : CausalDynamics) : List Variable :=
  (dyn.laws.flatMap fun law =>
    law.effect :: law.preconditions.map (·.1)).eraseDups

/-- Inner (endogenous) variables: those appearing as effects of laws. -/
def innerVariables (dyn : CausalDynamics) : List Variable :=
  (dyn.laws.map (·.effect)).eraseDups

/-- Every law's effect appears in `innerVariables`. -/
theorem effect_mem_innerVariables (dyn : CausalDynamics) (law : CausalLaw)
    (h : law ∈ dyn.laws) : law.effect ∈ innerVariables dyn := by
  unfold innerVariables
  exact List.mem_eraseDups.mpr (List.mem_map.mpr ⟨law, h, rfl⟩)

-- ============================================================
-- § Positivity Typeclass
-- ============================================================

/-- Typeclass marker: `dyn` is a positive dynamics (no inhibitory connections).

    The whole linguistic API in `Counterfactual.lean` (`causallySufficient`,
    `causallyNecessary`, etc.) requires this; for non-positive dynamics use
    the structural `preventSem` from `Theories/Semantics/Causation/Prevention.lean`. -/
class IsPositive (dyn : CausalDynamics) : Prop where
  positive : isPositiveDynamics dyn = true

namespace IsPositive

/-- Empty dynamics is trivially positive. -/
instance : IsPositive CausalDynamics.empty where positive := by decide

/-- A simple law `c → e` is positive. -/
instance (cause effect : Variable) :
    IsPositive ⟨[CausalLaw.simple cause effect]⟩ where
  positive := rfl

/-- Disjunctive causation `a → c, b → c` is positive. -/
instance (a b c : Variable) : IsPositive (CausalDynamics.disjunctiveCausation a b c) where
  positive := rfl

/-- Conjunctive causation `a ∧ b → c` is positive. -/
instance (a b c : Variable) : IsPositive (CausalDynamics.conjunctiveCausation a b c) where
  positive := rfl

/-- Causal chain `a → b → c` is positive. -/
instance (a b c : Variable) : IsPositive (CausalDynamics.causalChain a b c) where
  positive := rfl

end IsPositive

-- ============================================================
-- § Normal Causal Development (Def 15)
-- ============================================================

/-- Apply all laws once to a situation (one step of forward propagation). -/
def applyLawsOnce (dyn : CausalDynamics) (s : Situation) : Situation :=
  dyn.laws.foldl (λ s' law => law.apply s') s

/-- Check if a situation is a fixpoint (no law can change it). -/
def isFixpoint (dyn : CausalDynamics) (s : Situation) : Bool :=
  dyn.laws.all λ law =>
    !law.preconditionsMet s ||
    s.hasValue law.effect law.effectValue

/-- The default fuel level used by `normalDevelopment` when no explicit fuel
    is supplied. Large enough for all dynamics in the codebase; for positive
    dynamics, see `Monotonicity.lean` for a fuel-free `normalDevelopmentPositive`
    via well-founded recursion. -/
abbrev defaultFuel : Nat := 100

/-- **Normal Causal Development** (Definition 15)

    Iterate forward propagation until fixpoint. Uses bounded iteration
    (fuel) to ensure termination. -/
def normalDevelopment (dyn : CausalDynamics) (s : Situation)
    (fuel : Nat := defaultFuel) : Situation :=
  match fuel with
  | 0 => s
  | n + 1 =>
    let s' := applyLawsOnce dyn s
    bif isFixpoint dyn s' then s'
    else normalDevelopment dyn s' n

-- Fixpoint Theorems

/-- Unfold normalDevelopment one step. -/
@[simp] theorem normalDevelopment_succ (dyn : CausalDynamics) (s : Situation) (n : Nat) :
    normalDevelopment dyn s (n + 1) =
      let s' := applyLawsOnce dyn s
      bif isFixpoint dyn s' then s' else normalDevelopment dyn s' n := rfl

/-- If the first round reaches a fixpoint, normalDevelopment returns it. -/
theorem normalDevelopment_succ_fix {dyn : CausalDynamics} {s : Situation} {n : Nat}
    (h : isFixpoint dyn (applyLawsOnce dyn s) = true) :
    normalDevelopment dyn s (n + 1) = applyLawsOnce dyn s := by
  simp [h]

/-- If the first round is NOT a fixpoint, normalDevelopment recurses. -/
theorem normalDevelopment_succ_step {dyn : CausalDynamics} {s : Situation} {n : Nat}
    (h : isFixpoint dyn (applyLawsOnce dyn s) = false) :
    normalDevelopment dyn s (n + 1) = normalDevelopment dyn (applyLawsOnce dyn s) n := by
  simp [h]

/-- If the result of one round of law application is a fixpoint,
    normalDevelopment returns that result. -/
theorem normalDevelopment_fixpoint_after_one (dyn : CausalDynamics) (s : Situation) {fuel : Nat}
    (h : isFixpoint dyn (applyLawsOnce dyn s) = true) :
    normalDevelopment dyn s (fuel + 1) = applyLawsOnce dyn s := by
  simp [h]

/-- Fuel-agnostic version: any positive fuel is enough when one round suffices. -/
theorem normalDevelopment_eq_applyLawsOnce_of_fixpoint
    (dyn : CausalDynamics) (s : Situation) {fuel : Nat}
    (h : isFixpoint dyn (applyLawsOnce dyn s) = true) (hpos : 0 < fuel) :
    normalDevelopment dyn s fuel = applyLawsOnce dyn s := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  exact normalDevelopment_fixpoint_after_one dyn s h

/-- If the first round is not a fixpoint but the second is,
    normalDevelopment returns the second-round result. -/
theorem normalDevelopment_fixpoint_after_two (dyn : CausalDynamics) (s : Situation) {fuel : Nat}
    (h1 : isFixpoint dyn (applyLawsOnce dyn s) = false)
    (h2 : isFixpoint dyn (applyLawsOnce dyn (applyLawsOnce dyn s)) = true) :
    normalDevelopment dyn s (fuel + 2) =
      applyLawsOnce dyn (applyLawsOnce dyn s) := by
  simp [h1, h2]

/-- Fuel-agnostic version of `_after_two`: any fuel ≥ 2 suffices. -/
theorem normalDevelopment_eq_applyLawsTwice_of_fixpoint
    (dyn : CausalDynamics) (s : Situation) {fuel : Nat}
    (h1 : isFixpoint dyn (applyLawsOnce dyn s) = false)
    (h2 : isFixpoint dyn (applyLawsOnce dyn (applyLawsOnce dyn s)) = true)
    (hge : 2 ≤ fuel) :
    normalDevelopment dyn s fuel = applyLawsOnce dyn (applyLawsOnce dyn s) := by
  match fuel, hge with
  | n + 2, _ => exact normalDevelopment_fixpoint_after_two dyn s h1 h2

/-- General fixpoint theorem: if `applyLawsOnce` reaches a fixpoint after
    exactly `n + 1` rounds, then `normalDevelopment` with sufficient fuel
    returns `(applyLawsOnce dyn)^[n + 1] s`.

    `_after_one` and `_after_two` are special cases for `n = 0` and `n = 1`. -/
theorem normalDevelopment_fixpoint_at (dyn : CausalDynamics) (s : Situation)
    (n : Nat) {fuel : Nat}
    (hnfix : ∀ k, k < n → isFixpoint dyn ((applyLawsOnce dyn)^[k + 1] s) = false)
    (hfix : isFixpoint dyn ((applyLawsOnce dyn)^[n + 1] s) = true) :
    normalDevelopment dyn s (fuel + n + 1) = (applyLawsOnce dyn)^[n + 1] s := by
  induction n generalizing s with
  | zero => exact normalDevelopment_succ_fix hfix
  | succ m ih =>
    rw [show fuel + (m + 1) + 1 = (fuel + m + 1) + 1 from by omega,
        normalDevelopment_succ_step (hnfix 0 (Nat.zero_lt_succ m))]
    exact ih (applyLawsOnce dyn s)
      (fun k hk => hnfix (k + 1) (by omega))
      hfix

/-- If a law's fixpoint condition holds (preconditions unmet or effect present),
    applying the law is a no-op. -/
theorem CausalLaw.apply_of_fixpoint {law : CausalLaw} {s : Situation}
    (h : (!law.preconditionsMet s || s.hasValue law.effect law.effectValue) = true) :
    law.apply s = s := by
  by_cases hMet : law.preconditionsMet s = true
  · simp only [hMet, Bool.not_true, Bool.false_or] at h
    rw [apply_of_met hMet]
    exact Situation.extend_eq_self h
  · have : law.preconditionsMet s = false := by
      cases hb : law.preconditionsMet s <;> simp_all
    exact apply_of_not_met this

/-- Folding law application over a fixpoint is identity. -/
private theorem foldl_apply_fixpoint (laws : List CausalLaw) (s : Situation)
    (h : ∀ l, l ∈ laws →
      (!l.preconditionsMet s || s.hasValue l.effect l.effectValue) = true) :
    laws.foldl (fun s' l => l.apply s') s = s := by
  revert h
  induction laws with
  | nil => intro _; rfl
  | cons hd tl ih =>
    intro h
    simp only [List.forall_mem_cons] at h
    simp only [List.foldl_cons]
    rw [CausalLaw.apply_of_fixpoint h.1]
    exact ih h.2

/-- Applying all laws to a fixpoint situation is a no-op. -/
theorem applyLawsOnce_of_fixpoint {dyn : CausalDynamics} {s : Situation}
    (h : isFixpoint dyn s = true) : applyLawsOnce dyn s = s := by
  simp only [isFixpoint, List.all_eq_true] at h
  exact foldl_apply_fixpoint dyn.laws s h

/-- Normal development from a fixpoint is a no-op regardless of fuel. -/
theorem normalDevelopment_of_fixpoint {dyn : CausalDynamics} {s : Situation}
    (h : isFixpoint dyn s = true) (fuel : Nat) :
    normalDevelopment dyn s fuel = s := by
  induction fuel with
  | zero => rfl
  | succ n ih =>
    have hApp : applyLawsOnce dyn s = s := applyLawsOnce_of_fixpoint h
    have hFix : isFixpoint dyn (applyLawsOnce dyn s) = true := hApp.symm ▸ h
    rw [normalDevelopment_succ_fix hFix, hApp]

/-- Empty dynamics: any situation is a fixpoint. -/
theorem empty_dynamics_fixpoint (s : Situation) :
    isFixpoint CausalDynamics.empty s = true := by
  simp only [isFixpoint, CausalDynamics.empty, List.all_eq_true]
  intro x hx
  simp at hx

/-- Normal development of empty dynamics returns the input unchanged. -/
theorem empty_dynamics_unchanged (s : Situation) (fuel : Nat) :
    normalDevelopment CausalDynamics.empty s fuel = s := by
  induction fuel with
  | zero => rfl
  | succ n _ =>
    simp only [normalDevelopment, applyLawsOnce, CausalDynamics.empty, List.foldl_nil,
               isFixpoint]
    simp

end Core.Causal
