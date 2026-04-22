import Mathlib.Logic.Function.Iterate

/-!
# Structural Equation Model: Definitions
@cite{fitting-1985} @cite{schulz-2011} @cite{nadathur-2024} @cite{nadathur-lauer-2020} @cite{kleene-1952}

Core types and forward propagation for deterministic causal models.

- **Variable**: Named causal variables
- **Situation**: Partial valuations (Variable → Option Bool)
- **CausalLaw**: Structural equations (preconditions → effect)
- **CausalDynamics**: Collections of causal laws

## Three-valued substrate

`Situation` interprets `none` as @cite{kleene-1952}'s `u` (undetermined),
the third truth value alongside `false` (`some false`) and `true`
(`some true`). The information ordering `u ⊑ false`, `u ⊑ true`
(@cite{fitting-1985} §2-3) makes negative preconditions like `¬BRK`
genuinely partial: a precondition `(v, false)` is met iff
`s.get v = some false` (definite absence), not iff
`s.get v ≠ some true` (default-to-false).

This is the substrate @cite{schulz-2011} adopts for causal counterfactuals
(§3.1, three-valued truth tables in Fig. 1) and that @cite{nadathur-2024}
inherits for implicative-verb semantics (§4, Definitions 4 & 9):
variables with `u`-status block law firing, modeling Nadathur's
"potential obstacle" reading.

## Information monotonicity (Schulz's T_D)

`CausalLaw.apply` is the per-law version of @cite{schulz-2011}'s operator
`T_D` (Definition 3): a law fires only when its effect is undetermined
(`s.get q = u`); once determined, the value is preserved even if the
dynamics would predict otherwise. As Schulz notes (footnote 7,
p. 246): "T cannot change the truth value of propositional variable
already set to 1 or 0, even if this contradicts the predictions made
by causal regularities described in the dynamics D."

This information-monotonicity gives well-founded fixpoint iteration via
the `Option.isNone` measure (in `Monotonicity.lean`) — an explicit Lean
realization of Schulz's footnoted claim that the fixpoint "can be
reached in finitely many steps." No polarity restriction on
preconditions is needed; @cite{fitting-1985}'s Kripke-Kleene framework
admits negation natively.

## Generalization beyond Schulz

@cite{schulz-2011} associates each inner variable with a single truth
function `f_q : {0,1}^n → {0,1}`. We allow multiple `CausalLaw`s per
effect variable (disjunctive causation, conjunctive paths). With
information-monotone `apply`, the foldl over laws produces a "first
firing wins" semantics: if multiple compatible laws would fire, the
first sets the value; subsequent laws are blocked by the determined
effect. For well-formed dynamics (laws agree on effect values), this
matches Schulz's single-`f_q` model.
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

/-- The variable has a specific value in the situation. -/
def hasValue (s : Situation) (v : Variable) (val : Bool) : Prop :=
  s.valuation v = some val

instance (s : Situation) (v : Variable) (val : Bool) : Decidable (s.hasValue v val) :=
  inferInstanceAs (Decidable (_ = _))

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

/-- Extending at `v` and querying `v` returns true iff the values match. -/
@[simp] theorem extend_hasValue_same {s : Situation} {v : Variable} {val bval : Bool} :
    (s.extend v val).hasValue v bval ↔ val = bval := by
  simp [hasValue, extend]

/-- Extending at `v` doesn't affect queries at a different variable `w`. -/
@[simp] theorem extend_hasValue_diff {s : Situation} {v w : Variable} {val bval : Bool}
    (h : w ≠ v) : (s.extend v val).hasValue w bval ↔ s.hasValue w bval := by
  simp [hasValue, extend, h]

/-- Extending at a value already present is identity. -/
theorem extend_eq_self {s : Situation} {v : Variable} {val : Bool}
    (h : s.hasValue v val) : s.extend v val = s := by
  apply Situation.ext; funext w
  simp only [extend]
  by_cases hw : w = v
  · subst hw; simp; exact h.symm
  · simp [hw]

/-- Extending at `w ≠ v` doesn't affect the value of `v`. -/
theorem extend_get_ne {s : Situation} {v w : Variable} {val : Bool}
    (h : v ≠ w) : (s.extend w val).get v = s.get v := by
  unfold get extend
  simp only
  rw [show (v == w) = false from beq_false_of_ne h]; rfl

/-- Extending at a fresh variable produces `some val` at that variable. -/
@[simp] theorem extend_get_same (s : Situation) (v : Variable) (val : Bool) :
    (s.extend v val).get v = some val := by
  unfold get extend; simp

end Situation

-- True-subset ordering on situations

/-- s₁ ⊑ s₂ in the true-content ordering: every variable `true` in s₁
    is also `true` in s₂. This is the natural preorder for reasoning about
    monotonicity of positive causal dynamics. -/
def Situation.trueLE (s₁ s₂ : Situation) : Prop :=
  ∀ v, s₁.hasValue v true → s₂.hasValue v true

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

/-- All preconditions of a law are satisfied in a situation.

    A precondition `(v, val)` is met iff `s.get v = some val` — strong-Kleene
    reading. Undetermined (`none`) variables do not satisfy any precondition,
    so laws referring to them are blocked rather than defaulting their value. -/
def preconditionsMet (law : CausalLaw) (s : Situation) : Prop :=
  ∀ p ∈ law.preconditions, s.hasValue p.1 p.2

instance (law : CausalLaw) (s : Situation) : Decidable (law.preconditionsMet s) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- Apply a law to a situation. The law fires iff (i) its preconditions are
    met AND (ii) its effect is undetermined in `s`. Once a variable is
    determined (`some _`), no law overwrites it — this is the
    information-monotonicity invariant that makes `applyLawsOnce` strictly
    decrease the count of undetermined variables on every effective step
    (see `Monotonicity.lean`).

    Exogenous overrides should go through `intervene` (Pearl's
    `do(X = val)`), which removes laws targeting the variable and then
    extends the situation; not through manual `extend` followed by `apply`. -/
def apply (law : CausalLaw) (s : Situation) : Situation :=
  match s.get law.effect with
  | none =>
    if law.preconditionsMet s then
      s.extend law.effect law.effectValue
    else
      s
  | some _ => s

/-- Create a simple law: if cause = true, then effect = true.
    This is the structural equation B := A from @cite{sloman-barbey-hotaling-2009}
    Figure 4 (eq. 2): the causal-model-theoretic representation of "A causes B". -/
def simple (cause effect : Variable) : CausalLaw :=
  { preconditions := [(cause, true)], effect := effect }

/-- Create a conjunctive law: if cause1 = true ∧ cause2 = true, then effect = true.
    This is the structural equation B := A ∧ X from @cite{sloman-barbey-hotaling-2009}
    Figure 4 (eq. 3): the causal-model-theoretic representation of "A enables B"
    where X is the accessory variable. -/
def conjunctive (cause1 cause2 effect : Variable) : CausalLaw :=
  { preconditions := [(cause1, true), (cause2, true)], effect := effect }

/-- Create an inhibitory law: if cause = false (absent), then effect = true.
    This is the structural equation B := ¬A from @cite{sloman-barbey-hotaling-2009}
    Figure 4 (eq. 4a). Inhibitory laws are the structural basis for prevention:
    the effect occurs precisely when the cause is absent. -/
def inhibitory (cause effect : Variable) : CausalLaw :=
  { preconditions := [(cause, false)], effect := effect }

/-- Create a negated-conjunction law: if cause = false ∧ accessory = false,
    then effect = true. This is the structural equation B := ¬(A ∧ X) from
    @cite{sloman-barbey-hotaling-2009} Figure 4 (eq. 4c): a context-dependent
    prevention form where the effect is blocked iff *both* the preventer and
    the accessory are jointly present.

    Note: eq. 4c says `B := ¬(A ∧ X)`, which is equivalent to `B := ¬A ∨ ¬X`.
    A single `CausalLaw` encodes a conjunctive precondition; the disjunctive
    representation requires two laws (use `CausalDynamics.preventionNegConj`). -/
def inhibitoryConj (preventer accessory effect : Variable) : CausalLaw :=
  { preconditions := [(preventer, false), (accessory, false)], effect := effect }

/-- If preconditions are not met, applying the law is a no-op. -/
@[simp] theorem apply_of_not_met {law : CausalLaw} {s : Situation}
    (h : ¬ law.preconditionsMet s) : law.apply s = s := by
  unfold apply
  cases hg : s.get law.effect
  · simp [h]
  · rfl

/-- If the effect is already determined, applying the law is a no-op
    (information-monotonicity invariant). -/
@[simp] theorem apply_of_determined {law : CausalLaw} {s : Situation} {b : Bool}
    (h : s.get law.effect = some b) : law.apply s = s := by
  unfold apply; rw [h]

/-- If preconditions are met AND the effect is undetermined, applying the
    law extends the situation with the effect's value. -/
theorem apply_of_met_undetermined {law : CausalLaw} {s : Situation}
    (hMet : law.preconditionsMet s)
    (hNone : s.get law.effect = none) :
    law.apply s = s.extend law.effect law.effectValue := by
  unfold apply; rw [hNone]; simp [hMet]

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

/-- Prevention via negated conjunction: B := ¬(A ∧ X) (@cite{sloman-barbey-hotaling-2009}
    eq. 4c). Equivalent to `B := ¬A ∨ ¬X` — the effect occurs unless *both*
    preventer and accessory are jointly present. Models "A prevents B (when X)
    only by means of being conjoined with X". Encoded as two disjunctive laws. -/
def preventionNegConj (preventer accessory effect : Variable) : CausalDynamics :=
  ⟨[CausalLaw.inhibitory preventer effect,
    CausalLaw.inhibitory accessory effect]⟩

end CausalDynamics

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
-- § Causal ancestors (@cite{nadathur-2024} Definitions 2 & 11)
-- ============================================================

/-- **Immediate ancestors** of `X`: variables appearing as preconditions
    of any law whose effect is `X`. (@cite{nadathur-2024} Def 2 — the
    relation `R_F`.) -/
def immediateAncestors (dyn : CausalDynamics) (X : Variable) : List Variable :=
  (dyn.laws.filter (·.effect == X)
    |>.flatMap (·.preconditions.map (·.1))).eraseDups

/-- **Causal ancestors** of `X`: transitive closure of `immediateAncestors`.
    @cite{nadathur-2024} Definition 11.

    Computed by iterating "expand by immediate ancestors of current set"
    `|allVariables|` times — guaranteed to reach the closure since the
    ancestor set is bounded above by `allVariables` and grows monotonically. -/
def causalAncestors (dyn : CausalDynamics) (X : Variable) : List Variable :=
  let expand (acc : List Variable) : List Variable :=
    (acc ++ acc.flatMap (immediateAncestors dyn)).eraseDups
  expand^[(allVariables dyn).length] (immediateAncestors dyn X)

namespace Situation

/-- The **domain** of a situation `s`: variables `X` with `s(X) ≠ u`.
    @cite{nadathur-2024} Definition 7. -/
def dom (s : Situation) (vars : List Variable) : List Variable :=
  vars.filter (fun v => decide ((s.get v).isSome))

end Situation

-- ============================================================
-- § Normal Causal Development primitives
-- ============================================================

/-- Apply all laws once to a situation (one step of forward propagation). -/
def applyLawsOnce (dyn : CausalDynamics) (s : Situation) : Situation :=
  dyn.laws.foldl (λ s' law => law.apply s') s

/-- A situation is a fixpoint of the dynamics: every law is satisfied —
    either its preconditions are unmet or its effect is already determined.

    With information-monotone `apply`, a third case — effect determined
    to a *different* value than the law would predict — also counts as
    satisfied (the law won't fire), but that case is semantically weird
    for well-formed dynamics; the user should handle it via `intervene`
    instead. -/
def isFixpoint (dyn : CausalDynamics) (s : Situation) : Prop :=
  ∀ law ∈ dyn.laws, law.preconditionsMet s → s.get law.effect ≠ none

instance (dyn : CausalDynamics) (s : Situation) : Decidable (isFixpoint dyn s) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- If a law is satisfied at `s` (preconditions unmet or effect determined),
    applying the law is a no-op. -/
theorem CausalLaw.apply_of_fixpoint {law : CausalLaw} {s : Situation}
    (h : law.preconditionsMet s → s.get law.effect ≠ none) :
    law.apply s = s := by
  cases hg : s.get law.effect with
  | none =>
    by_cases hMet : law.preconditionsMet s
    · exact absurd hg (h hMet)
    · exact apply_of_not_met hMet
  | some b => exact apply_of_determined hg

/-- Folding law application over a fixpoint is identity. -/
private theorem foldl_apply_fixpoint (laws : List CausalLaw) (s : Situation)
    (h : ∀ l ∈ laws, l.preconditionsMet s → s.get l.effect ≠ none) :
    laws.foldl (fun s' l => l.apply s') s = s := by
  induction laws with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [CausalLaw.apply_of_fixpoint (h hd (List.mem_cons_self ..))]
    exact ih (fun l hl => h l (List.mem_cons_of_mem _ hl))

/-- Applying all laws to a fixpoint situation is a no-op. -/
theorem applyLawsOnce_of_fixpoint {dyn : CausalDynamics} {s : Situation}
    (h : isFixpoint dyn s) : applyLawsOnce dyn s = s :=
  foldl_apply_fixpoint dyn.laws s h

/-- Empty dynamics: any situation is a fixpoint. -/
theorem empty_dynamics_fixpoint (s : Situation) :
    isFixpoint CausalDynamics.empty s := by
  intro law hLaw _ _
  simp [CausalDynamics.empty] at hLaw

end Core.Causal
