import Mathlib.Logic.Function.Iterate

/-!
# Structural Equation Model
@cite{nadathur-lauer-2020}

Theory-neutral infrastructure for deterministic causal and counterfactual
reasoning based on Pearl's structural causal model framework.

- **Variable**: Named causal variables
- **Situation**: Partial valuations (Variable → Option Bool)
- **CausalLaw**: Structural equations (preconditions → effect)
- **CausalDynamics**: Collections of causal laws
- **normalDevelopment**: Forward propagation to fixpoint
- **intervene**: Pearl's do-operator (set variable, cut incoming laws)
- **causallyNecessary / causallySufficient**: Counterfactual tests
- **manipulates**: Does intervening on X change Y?

For the probabilistic causal Bayes net layer (WorldState, CausalRelation,
NoisyOR), see `Core.CausalBayesNet`.

-/

namespace Core.StructuralEquationModel

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

-- Situations (Def 9)

/-- **Situation** (Definition 9 from @cite{nadathur-lauer-2020})

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

end CausalDynamics

/-- A dynamics is **positive** if all preconditions require `true` and all
    effect values are `true`. Positive dynamics have no inhibitory connections:
    causes can only enable effects, never block them.

    This is the key structural condition for monotonicity results: in positive
    dynamics, adding `true` values to a situation can only enable more laws,
    never block them. -/
def isPositiveDynamics (dyn : CausalDynamics) : Bool :=
  dyn.laws.all (fun law => law.preconditions.all (·.2) && law.effectValue)

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

/-- **Normal Causal Development** (Definition 15)

    Iterate forward propagation until fixpoint. Uses bounded iteration
    (fuel) to ensure termination. -/
def normalDevelopment (dyn : CausalDynamics) (s : Situation)
    (fuel : Nat := 100) : Situation :=
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

/-- If the first round is not a fixpoint but the second is,
    normalDevelopment returns the second-round result. -/
theorem normalDevelopment_fixpoint_after_two (dyn : CausalDynamics) (s : Situation) {fuel : Nat}
    (h1 : isFixpoint dyn (applyLawsOnce dyn s) = false)
    (h2 : isFixpoint dyn (applyLawsOnce dyn (applyLawsOnce dyn s)) = true) :
    normalDevelopment dyn s (fuel + 2) =
      applyLawsOnce dyn (applyLawsOnce dyn s) := by
  simp [h1, h2]

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

-- ============================================================
-- § Positive Dynamics: Monotonicity
-- ============================================================

private abbrev trueLE := Situation.trueLE

-- § Per-law monotonicity lemmas

private theorem positive_preconditions_monotone
    (law : CausalLaw) (s₁ s₂ : Situation)
    (hPosPrec : law.preconditions.all (·.2) = true)
    (hLE : trueLE s₁ s₂)
    (hMet : law.preconditionsMet s₁ = true) :
    law.preconditionsMet s₂ = true := by
  simp only [CausalLaw.preconditionsMet, List.all_eq_true] at *
  intro p hmem
  have hval : p.2 = true := hPosPrec p hmem
  exact hval ▸ hLE p.1 (hval ▸ hMet p hmem)

private theorem positive_law_apply_trueLE
    (law : CausalLaw) (s₁ s₂ : Situation)
    (hPosPrec : law.preconditions.all (·.2) = true)
    (hPosEff : law.effectValue = true)
    (hLE : trueLE s₁ s₂) :
    trueLE (law.apply s₁) (law.apply s₂) := by
  intro v hv
  by_cases hMet₁ : law.preconditionsMet s₁ = true
  · have hMet₂ := positive_preconditions_monotone law s₁ s₂ hPosPrec hLE hMet₁
    rw [CausalLaw.apply_of_met hMet₁] at hv; rw [CausalLaw.apply_of_met hMet₂]
    by_cases he : v = law.effect
    · subst he; rw [Situation.extend_hasValue_same]; simp [hPosEff]
    · rw [Situation.extend_hasValue_diff he] at hv ⊢
      exact hLE v hv
  · have h₁ : law.preconditionsMet s₁ = false := by
      cases h : law.preconditionsMet s₁ <;> simp_all
    rw [CausalLaw.apply_of_not_met h₁] at hv
    by_cases hMet₂ : law.preconditionsMet s₂ = true
    · rw [CausalLaw.apply_of_met hMet₂]
      by_cases he : v = law.effect
      · subst he; rw [Situation.extend_hasValue_same]; simp [hPosEff]
      · rw [Situation.extend_hasValue_diff he]; exact hLE v hv
    · have h₂ : law.preconditionsMet s₂ = false := by
        cases h : law.preconditionsMet s₂ <;> simp_all
      rw [CausalLaw.apply_of_not_met h₂]; exact hLE v hv

private theorem positive_law_apply_grows
    (law : CausalLaw) (s : Situation) (hPosEff : law.effectValue = true) :
    trueLE s (law.apply s) := by
  intro v hv
  by_cases hMet : law.preconditionsMet s = true
  · rw [CausalLaw.apply_of_met hMet]
    by_cases he : v = law.effect
    · subst he; rw [Situation.extend_hasValue_same]; simp [hPosEff]
    · rw [Situation.extend_hasValue_diff he]; exact hv
  · have : law.preconditionsMet s = false := by
      cases h : law.preconditionsMet s <;> simp_all
    rw [CausalLaw.apply_of_not_met this]; exact hv

private theorem positive_law_apply_absorbed
    (law : CausalLaw) (s₁ s₂ : Situation)
    (hPosPrec : law.preconditions.all (·.2) = true)
    (hPosEff : law.effectValue = true)
    (hLE : trueLE s₁ s₂)
    (hFixLaw : (!law.preconditionsMet s₂ || s₂.hasValue law.effect law.effectValue) = true) :
    trueLE (law.apply s₁) s₂ := by
  intro v hv
  by_cases hMet₁ : law.preconditionsMet s₁ = true
  · rw [CausalLaw.apply_of_met hMet₁] at hv
    by_cases he : v = law.effect
    · subst he
      have hMet₂ := positive_preconditions_monotone law s₁ s₂ hPosPrec hLE hMet₁
      simp only [hMet₂, Bool.not_true, Bool.false_or] at hFixLaw
      rw [hPosEff] at hFixLaw; exact hFixLaw
    · rw [Situation.extend_hasValue_diff he] at hv; exact hLE v hv
  · have : law.preconditionsMet s₁ = false := by
      cases h : law.preconditionsMet s₁ <;> simp_all
    rw [CausalLaw.apply_of_not_met this] at hv; exact hLE v hv

-- § Foldl (law-list) monotonicity

private theorem positive_foldl_trueLE
    (laws : List CausalLaw) (s₁ s₂ : Situation)
    (hPos : laws.all (fun law => law.preconditions.all (·.2) && law.effectValue) = true)
    (hLE : trueLE s₁ s₂) :
    trueLE (laws.foldl (fun s' law => law.apply s') s₁)
           (laws.foldl (fun s' law => law.apply s') s₂) := by
  induction laws generalizing s₁ s₂ with
  | nil => exact hLE
  | cons law rest ih =>
    simp only [List.foldl_cons, List.all_cons, Bool.and_eq_true] at *
    exact ih (law.apply s₁) (law.apply s₂) hPos.2
      (positive_law_apply_trueLE law s₁ s₂ hPos.1.1 hPos.1.2 hLE)

private theorem positive_foldl_grows
    (laws : List CausalLaw) (s : Situation)
    (hPos : laws.all (fun law => law.preconditions.all (·.2) && law.effectValue) = true) :
    trueLE s (laws.foldl (fun s' law => law.apply s') s) := by
  induction laws generalizing s with
  | nil => exact Situation.trueLE_refl s
  | cons law rest ih =>
    simp only [List.foldl_cons, List.all_cons, Bool.and_eq_true] at *
    exact Situation.trueLE_trans
      (positive_law_apply_grows law s hPos.1.2) (ih (law.apply s) hPos.2)

private theorem positive_foldl_absorbed
    (laws : List CausalLaw) (s₁ s₂ : Situation)
    (hPos : laws.all (fun law => law.preconditions.all (·.2) && law.effectValue) = true)
    (hLE : trueLE s₁ s₂)
    (hFix : laws.all (fun law => !law.preconditionsMet s₂ ||
            s₂.hasValue law.effect law.effectValue) = true) :
    trueLE (laws.foldl (fun s' law => law.apply s') s₁) s₂ := by
  induction laws generalizing s₁ with
  | nil => exact hLE
  | cons law rest ih =>
    simp only [List.foldl_cons, List.all_cons, Bool.and_eq_true] at *
    exact ih (law.apply s₁) hPos.2
      (positive_law_apply_absorbed law s₁ s₂ hPos.1.1 hPos.1.2 hLE hFix.1) hFix.2

-- § Foldl sets witness effect (for convergence)

/-- If a law `l` is in the list and its preconditions are met in `s`,
    then after folding all positive laws, `l`'s effect is set.
    Key helper for proving normalDevelopment convergence. -/
private theorem foldl_sets_witness_effect :
    ∀ (laws : List CausalLaw) (s : Situation) (l : CausalLaw),
    laws.all (fun law => law.preconditions.all (·.2) && law.effectValue) = true →
    l ∈ laws →
    l.effectValue = true →
    l.preconditionsMet s = true →
    (laws.foldl (fun s' law => law.apply s') s).hasValue l.effect true = true
  | [], _, _, _, hMem, _, _ => by simp at hMem
  | hd :: tl, s, l, hPos, hMem, hPosEff, hMet => by
    simp only [List.foldl_cons]
    have hPosAll := hPos
    simp only [List.all_cons, Bool.and_eq_true] at hPos
    cases List.mem_cons.mp hMem with
    | inl heq =>
      subst heq
      rw [CausalLaw.apply_of_met hMet]
      have hSet : (s.extend l.effect l.effectValue).hasValue l.effect true = true := by
        simp [Situation.hasValue, Situation.extend, hPosEff]
      exact positive_foldl_grows tl (s.extend l.effect l.effectValue) hPos.2
        l.effect hSet
    | inr hmem =>
      have hLE := positive_law_apply_grows hd s hPos.1.2
      have hLPos := List.all_eq_true.mp hPos.2 l hmem
      simp only [Bool.and_eq_true] at hLPos
      have hMet' := positive_preconditions_monotone l s (hd.apply s) hLPos.1 hLE hMet
      exact foldl_sets_witness_effect tl (hd.apply s) l hPos.2 hmem hPosEff hMet'

-- § applyLawsOnce / normalDevelopment monotonicity

private theorem positive_applyLawsOnce_trueLE
    (dyn : CausalDynamics) (s₁ s₂ : Situation)
    (hPos : isPositiveDynamics dyn = true) (hLE : trueLE s₁ s₂) :
    trueLE (applyLawsOnce dyn s₁) (applyLawsOnce dyn s₂) :=
  positive_foldl_trueLE dyn.laws s₁ s₂ hPos hLE

private theorem positive_applyLawsOnce_grows
    (dyn : CausalDynamics) (s : Situation)
    (hPos : isPositiveDynamics dyn = true) :
    trueLE s (applyLawsOnce dyn s) :=
  positive_foldl_grows dyn.laws s hPos

private theorem positive_applyLawsOnce_absorbed
    (dyn : CausalDynamics) (s₁ s₂ : Situation)
    (hPos : isPositiveDynamics dyn = true)
    (hLE : trueLE s₁ s₂) (hFix : isFixpoint dyn s₂ = true) :
    trueLE (applyLawsOnce dyn s₁) s₂ :=
  positive_foldl_absorbed dyn.laws s₁ s₂ hPos hLE hFix

/-- For positive dynamics, normal development is **inflationary** (extensive):
    every truth in `s` is preserved. This is one of the three closure-operator
    axioms. Used by `CausalClosure.lean` to build the `ClosureOperator` instance. -/
theorem positive_normalDevelopment_grows
    (dyn : CausalDynamics) (s : Situation) (fuel : Nat)
    (hPos : isPositiveDynamics dyn = true) :
    trueLE s (normalDevelopment dyn s fuel) := by
  induction fuel generalizing s with
  | zero => exact Situation.trueLE_refl s
  | succ n ih =>
    have hGrow := positive_applyLawsOnce_grows dyn s hPos
    by_cases hFix : isFixpoint dyn (applyLawsOnce dyn s) = true
    · rw [normalDevelopment_succ_fix hFix]; exact hGrow
    · have : isFixpoint dyn (applyLawsOnce dyn s) = false := by
        cases h : isFixpoint dyn (applyLawsOnce dyn s) <;> simp_all
      rw [normalDevelopment_succ_step this]
      exact Situation.trueLE_trans hGrow (ih (applyLawsOnce dyn s))

private theorem fixpoint_absorbs
    (dyn : CausalDynamics) (s₁ s₂ : Situation) (fuel : Nat)
    (hPos : isPositiveDynamics dyn = true)
    (hLE : trueLE s₁ s₂) (hFix : isFixpoint dyn s₂ = true) :
    trueLE (normalDevelopment dyn s₁ fuel) s₂ := by
  induction fuel generalizing s₁ with
  | zero => exact hLE
  | succ n ih =>
    have hLE' := positive_applyLawsOnce_absorbed dyn s₁ s₂ hPos hLE hFix
    by_cases hFixS₁ : isFixpoint dyn (applyLawsOnce dyn s₁) = true
    · rw [normalDevelopment_succ_fix hFixS₁]; exact hLE'
    · have : isFixpoint dyn (applyLawsOnce dyn s₁) = false := by
        cases h : isFixpoint dyn (applyLawsOnce dyn s₁) <;> simp_all
      rw [normalDevelopment_succ_step this]; exact ih (applyLawsOnce dyn s₁) hLE'

private theorem positive_normalDevelopment_trueLE
    (dyn : CausalDynamics) (s₁ s₂ : Situation) (fuel : Nat)
    (hPos : isPositiveDynamics dyn = true) (hLE : trueLE s₁ s₂) :
    trueLE (normalDevelopment dyn s₁ fuel) (normalDevelopment dyn s₂ fuel) := by
  induction fuel generalizing s₁ s₂ with
  | zero => exact hLE
  | succ n ih =>
    have hLE' := positive_applyLawsOnce_trueLE dyn s₁ s₂ hPos hLE
    by_cases hFix₁ : isFixpoint dyn (applyLawsOnce dyn s₁) = true <;>
    by_cases hFix₂ : isFixpoint dyn (applyLawsOnce dyn s₂) = true
    · rw [normalDevelopment_succ_fix hFix₁, normalDevelopment_succ_fix hFix₂]; exact hLE'
    · have h₂ : isFixpoint dyn (applyLawsOnce dyn s₂) = false := by
        cases h : isFixpoint dyn (applyLawsOnce dyn s₂) <;> simp_all
      rw [normalDevelopment_succ_fix hFix₁, normalDevelopment_succ_step h₂]
      exact Situation.trueLE_trans hLE'
        (positive_normalDevelopment_grows dyn (applyLawsOnce dyn s₂) n hPos)
    · have h₁ : isFixpoint dyn (applyLawsOnce dyn s₁) = false := by
        cases h : isFixpoint dyn (applyLawsOnce dyn s₁) <;> simp_all
      rw [normalDevelopment_succ_step h₁, normalDevelopment_succ_fix hFix₂]
      exact fixpoint_absorbs dyn (applyLawsOnce dyn s₁) (applyLawsOnce dyn s₂) n hPos
        hLE' hFix₂
    · have h₁ : isFixpoint dyn (applyLawsOnce dyn s₁) = false := by
        cases h : isFixpoint dyn (applyLawsOnce dyn s₁) <;> simp_all
      have h₂ : isFixpoint dyn (applyLawsOnce dyn s₂) = false := by
        cases h : isFixpoint dyn (applyLawsOnce dyn s₂) <;> simp_all
      rw [normalDevelopment_succ_step h₁, normalDevelopment_succ_step h₂]
      exact ih (applyLawsOnce dyn s₁) (applyLawsOnce dyn s₂) hLE'

-- § Main monotonicity theorem

/-- For positive dynamics, normalDevelopment is monotone in the trueLE ordering.
    If s₁ ⊑ s₂ (every true in s₁ is true in s₂), then
    normalDevelopment(s₁) ⊑ normalDevelopment(s₂). -/
theorem normalDevelopment_trueLE_positive (dyn : CausalDynamics) (s₁ s₂ : Situation) (fuel : Nat)
    (hPos : isPositiveDynamics dyn = true)
    (hLE : Situation.trueLE s₁ s₂) :
    Situation.trueLE (normalDevelopment dyn s₁ fuel) (normalDevelopment dyn s₂ fuel) :=
  positive_normalDevelopment_trueLE dyn s₁ s₂ fuel hPos hLE

-- ============================================================
-- § Convenience Functions
-- ============================================================

/-- Check if a variable develops to a specific value. -/
def developsToBe (dyn : CausalDynamics) (s : Situation) (v : Variable) (val : Bool) : Bool :=
  (normalDevelopment dyn s).hasValue v val

/-- Check if a variable becomes true after normal development. -/
def developsToTrue (dyn : CausalDynamics) (s : Situation) (v : Variable) : Bool :=
  developsToBe dyn s v true

/-- The cause is present and the effect holds after normal development.

    Shared primitive for `actuallyCaused` (Necessity.lean) and
    `complementActualized` (Ability.lean). -/
def factuallyDeveloped (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Bool :=
  s.hasValue cause true &&
  (normalDevelopment dyn s).hasValue effect true

/-- `factuallyDeveloped` unfolds to a conjunction of two `hasValue` checks. -/
theorem factuallyDeveloped_iff (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) :
    factuallyDeveloped dyn s cause effect =
      (s.hasValue cause true && (normalDevelopment dyn s).hasValue effect true) := rfl

-- ============================================================
-- § Structural Graph Queries
-- ============================================================

/-- Does any causal law directly connect `cause` to `effect`? -/
def hasDirectLaw (dyn : CausalDynamics) (cause effect : Variable) : Bool :=
  dyn.laws.any fun law =>
    law.preconditions.any (fun (v, _) => v == cause) && law.effect == effect

/-- Does the intermediate have a causal law not depending on `cause`? -/
def hasIndependentSource (dyn : CausalDynamics)
    (cause intermediate : Variable) : Bool :=
  dyn.laws.any fun law =>
    law.effect == intermediate &&
    !(law.preconditions.any (fun (v, _) => v == cause))

-- ============================================================
-- § Intervention (Pearl's do-operator)
-- ============================================================

/-- **Intervene**: Pearl's do(X = val).

    Sets variable `target` to `val` and removes all laws that would
    determine `target`, so the intervention overrides the structural
    equations rather than being overwritten by them. -/
def intervene (dyn : CausalDynamics) (s : Situation)
    (target : Variable) (val : Bool) : CausalDynamics × Situation :=
  let dyn' : CausalDynamics := ⟨dyn.laws.filter (·.effect != target)⟩
  let s' := s.extend target val
  (dyn', s')

/-- **Manipulates**: Does intervening on `cause` change the value of `effect`?

    Compares normal development under do(cause = true) vs do(cause = false).
    If the effect's value differs, then `cause` manipulates `effect`.

    This is the interventionist criterion for causation:
    X causes Y iff there exists an intervention on X that changes Y. -/
def manipulates (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Bool :=
  let (dynT, sT) := intervene dyn s cause true
  let (dynF, sF) := intervene dyn s cause false
  let valT := (normalDevelopment dynT sT).get effect
  let valF := (normalDevelopment dynF sF).get effect
  valT != valF

-- ============================================================
-- § Counterfactual Queries (@cite{nadathur-lauer-2020} Definitions 23-24)
-- ============================================================

/-- **Causal Sufficiency** (@cite{nadathur-lauer-2020}, Definition 23).
    C is causally sufficient for E in situation s iff adding C and
    developing normally produces E. -/
def causallySufficient (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Bool :=
  let sWithCause := s.extend cause true
  let developed := normalDevelopment dyn sWithCause
  developed.hasValue effect true

/-- **Causal Necessity** (@cite{nadathur-lauer-2020}, Definition 24).
    C is causally necessary for E in situation s iff removing C and
    developing normally does NOT produce E.

    **Precondition**: this but-for test assumes both `cause` and `effect`
    are NOT already determined by `s`. If they are, the result is
    vacuously true and not meaningful. @cite{nadathur-2024} Definition
    10b adds an achievability condition (the effect must be obtainable
    when the cause holds) that prevents vacuous necessity. This
    implementation does not include that check. -/
def causallyNecessary (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Bool :=
  let sWithoutCause := s.extend cause false
  let developed := normalDevelopment dyn sWithoutCause
  !developed.hasValue effect true

/-- Causal profile: packages the counterfactual properties of a
    cause-effect pair in a structural model. -/
structure CausalProfile where
  sufficient : Bool
  necessary : Bool
  direct : Bool
  deriving DecidableEq, Repr, BEq

/-- Extract the causal profile of a cause-effect pair. -/
def extractProfile (dyn : CausalDynamics) (bg : Situation)
    (cause effect : Variable) : CausalProfile :=
  { sufficient := causallySufficient dyn bg cause effect
  , necessary := causallyNecessary dyn bg cause effect
  , direct := hasDirectLaw dyn cause effect }

-- ============================================================
-- § Causal Ancestors (@cite{nadathur-2024} Definition 11)
-- ============================================================

/-- **Immediate causal ancestors** of variable X: variables that appear
    as preconditions of any law whose effect is X. -/
def immediateAncestors (dyn : CausalDynamics) (x : Variable) : List Variable :=
  (dyn.laws.filter (fun law => law.effect == x)).flatMap
    (fun law => law.preconditions.map (·.1))
  |>.eraseDups

/-- **Causal ancestors** (@cite{nadathur-2024} Definition 11).
    Transitive closure of immediate causal ancestors. Bounded to
    avoid nontermination on cyclic models (which are ill-formed
    but representable). -/
def causalAncestors (dyn : CausalDynamics) (x : Variable)
    (fuel : Nat := 20) : List Variable :=
  match fuel with
  | 0 => []
  | n + 1 =>
    let imm := immediateAncestors dyn x
    let deeper := imm.flatMap (fun v => causalAncestors dyn v n)
    (imm ++ deeper).eraseDups

-- ============================================================
-- § Causal Consistency (@cite{nadathur-2024} Definition 9)
-- ============================================================

/-- **Causal consistency** (@cite{nadathur-2024} Definition 9).

    A situation s is causally consistent iff, for every inner variable
    X ∈ dom(s), the dynamics do not causally entail the negation of
    s's determination for X. That is: if s(X) = 1, then s does not
    causally entail ⟨X, 0⟩, and vice versa. -/
def causallyConsistent (dyn : CausalDynamics) (s : Situation)
    (innerVars : List Variable) : Bool :=
  innerVars.all fun x =>
    match s.get x with
    | some true  => !(normalDevelopment dyn s).hasValue x false
    | some false => !(normalDevelopment dyn s).hasValue x true
    | none       => true

-- ============================================================
-- § Situation-Based Necessity/Sufficiency (@cite{nadathur-2024} Def 12)
-- ============================================================

/-- **Situation-based causal sufficiency** (@cite{nadathur-2024} Definition 12a).

    Situation s is causally sufficient for ⟨X, x⟩ iff the fixed point s*
    of T_D relative to s assigns X = x. Equivalent to `causallySufficient`
    when s directly sets the cause variable; this version works with
    arbitrary situations as potential causes. -/
def situationSufficient (dyn : CausalDynamics) (s : Situation)
    (x : Variable) (val : Bool) : Bool :=
  (normalDevelopment dyn s).hasValue x val

/-- **Situation-based causal necessity** (@cite{nadathur-2024} Definition 12b).

    Situation s is causally necessary for ⟨X, x⟩ iff for every situation s'
    that:
    (i) dom(s') ⊇ dom(s) ∩ Anc(X)
    (ii) ∃ Y ∈ dom(s) ∩ Anc(X) with s'(Y) ≠ s(Y)
    (iii) s'(X) ≠ x
    we have s' ⊭_D ⟨X, x⟩.

    Approximated here by a counterfactual test over each individual ancestor:
    for each ancestor Y of X in dom(s), flipping Y's value blocks X = val. -/
def situationNecessary (dyn : CausalDynamics) (s : Situation)
    (x : Variable) (val : Bool) : Bool :=
  let ancs := causalAncestors dyn x
  let relevantAncs := ancs.filter (fun y => (s.get y).isSome)
  -- If no relevant ancestors in s, s is vacuously necessary
  relevantAncs.isEmpty ||
  -- Every relevant ancestor in s: flipping it blocks x = val
  relevantAncs.all fun y =>
    match s.get y with
    | some yval =>
      let s' := s.extend y (!yval)
      !(normalDevelopment dyn s').hasValue x val
    | none => true

end Core.StructuralEquationModel
