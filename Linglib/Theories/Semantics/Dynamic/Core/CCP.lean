/-
# Core Dynamic Semantics Infrastructure

Abstract foundations shared by PLA, DRT, DPL, CDRT, and other dynamic semantics theories.

## Key Abstractions

1. InfoState: set of possibilities (what we know)
2. CCP: Context Change Potential (how meaning changes state)
3. Galois connection: support ↔ content duality

## Mathematical Structures

- `InfoState` forms a `CompleteLattice` (from Set)
- `CCP` forms a `Monoid` (composition + identity)
- Support and Content form a Galois connection

## References

- Heim, I. (1982). The Semantics of Definite and Indefinite Noun Phrases.
- Groenendijk, J. & Stokhof, M. (1991). Dynamic Predicate Logic.
- Veltman, F. (1996). Defaults in Update Semantics.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Group.Defs

namespace Semantics.Dynamic.Core


/--
An InfoState is a set of possibilities.

Different theories instantiate `P` differently:
- PLA: Assignment × WitnessSeq
- DRT: Assignment
- Intensional: World × Assignment
-/
abbrev InfoStateOf (P : Type*) := Set P

-- InfoState is just Set, so we get:
-- ⊤ = Set.univ, ⊥ = ∅, ⊔ = ∪, ⊓ = ∩


/--
A Context Change Potential (CCP) is a function from states to states.

This is the semantic type for dynamic meanings.
-/
abbrev CCP (P : Type*) := InfoStateOf P → InfoStateOf P

namespace CCP

variable {P : Type*}

/-- Identity CCP: leaves state unchanged -/
def id : CCP P := λ s => s

/-- Absurd CCP: yields empty state -/
def absurd : CCP P := λ _ => ∅

/-- Sequential composition of CCPs -/
def seq (u v : CCP P) : CCP P := λ s => v (u s)

infixl:70 " ;; " => seq

-- Monoid laws
theorem seq_assoc (u v w : CCP P) : (u ;; v) ;; w = u ;; (v ;; w) := rfl
theorem id_seq (u : CCP P) : id ;; u = u := rfl
theorem seq_id (u : CCP P) : u ;; id = u := rfl

/-- CCPs form a monoid under sequential composition -/
instance : Monoid (CCP P) where
  mul := seq
  one := id
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

/-- seq_absurd: anything followed by absurd is absurd -/
theorem seq_absurd (u : CCP P) : u ;; absurd = absurd := rfl

/-- Dynamic conjunction: alias for sequential composition -/
def conj (u v : CCP P) : CCP P := seq u v

open Classical in
/--
Test-based negation: passes (returns input) iff φ yields ∅.

This is the standard dynamic negation of Heim (1982), Veltman (1996):
¬φ(s) = s if φ(s) = ∅, else ∅. Does not validate DNE.
-/
noncomputable def neg (φ : CCP P) : CCP P :=
  λ s => if (φ s).Nonempty then ∅ else s

open Classical in
/--
Compatibility test ("might"): passes iff φ yields a nonempty result.

might(φ)(s) = s if φ(s) ≠ ∅, else ∅
-/
noncomputable def might (φ : CCP P) : CCP P :=
  λ s => if (φ s).Nonempty then s else ∅

open Classical in
/--
Full support test ("must"): passes iff φ returns input unchanged.

must(φ)(s) = s if φ(s) = s, else ∅
-/
noncomputable def must (φ : CCP P) : CCP P :=
  λ s => if φ s = s then s else ∅

open Classical in
/--
Dynamic implication test: passes iff output of φ is preserved by ψ.

impl(φ,ψ)(s) = s if φ(s) ⊆ ψ(φ(s)), else ∅
-/
noncomputable def impl (φ ψ : CCP P) : CCP P :=
  λ s => if φ s ⊆ ψ (φ s) then s else ∅

/-- Dynamic entailment: φ entails ψ iff ψ adds no information after φ. -/
def entails (φ ψ : CCP P) : Prop :=
  ∀ s : InfoStateOf P, (φ s).Nonempty → ψ (φ s) = φ s

/-- Entailment is reflexive -/
theorem entails_id (φ : CCP P) : entails φ id := by
  intro s _; rfl

end CCP


/--
An update is eliminative if it never adds possibilities.

This is the fundamental property of dynamic semantics:
information only grows (possibilities only decrease).
-/
def IsEliminative {P : Type*} (u : CCP P) : Prop :=
  ∀ s, u s ⊆ s

/-- Identity is eliminative -/
theorem eliminative_id {P : Type*} : IsEliminative (CCP.id : CCP P) :=
  λ _ => Set.Subset.rfl

/-- Sequential composition preserves eliminativity -/
theorem eliminative_seq {P : Type*} (u v : CCP P)
    (hu : IsEliminative u) (hv : IsEliminative v) :
    IsEliminative (u ;; v) := λ s _ hp =>
  hu s (hv (u s) hp)


/--
A test is a CCP that either passes (returns input) or fails (returns ∅).

Tests don't change information - they check compatibility.
Examples: might, must, presupposition triggers.
-/
def IsTest {P : Type*} (u : CCP P) : Prop :=
  ∀ s, u s = s ∨ u s = ∅

/-- Tests are eliminative -/
theorem test_eliminative {P : Type*} (u : CCP P) (h : IsTest u) :
    IsEliminative u := λ s p hp => by
  cases h s with
  | inl heq => rw [heq] at hp; exact hp
  | inr hemp => rw [hemp] at hp; exact False.elim hp

open Classical in
theorem CCP.neg_isTest {P : Type*} (φ : CCP P) : IsTest (CCP.neg φ) := by
  intro s; simp only [CCP.neg]; split <;> simp

open Classical in
theorem CCP.might_isTest {P : Type*} (φ : CCP P) : IsTest (CCP.might φ) := by
  intro s; simp only [CCP.might]; split <;> simp

open Classical in
theorem CCP.must_isTest {P : Type*} (φ : CCP P) : IsTest (CCP.must φ) := by
  intro s; unfold CCP.must; split <;> simp

open Classical in
theorem CCP.impl_isTest {P : Type*} (φ ψ : CCP P) : IsTest (CCP.impl φ ψ) := by
  intro s; unfold CCP.impl; split <;> simp

open Classical in
/-- Duality: might φ = ¬(¬φ) -/
theorem CCP.might_eq_neg_neg {P : Type*} (φ : CCP P) :
    CCP.might φ = CCP.neg (CCP.neg φ) := by
  funext s
  simp only [CCP.might, CCP.neg]
  split
  · rw [if_neg Set.not_nonempty_empty]
  · rename_i h
    by_cases hs : s.Nonempty
    · rw [if_pos hs]
    · simp only [Set.not_nonempty_iff_eq_empty] at hs
      rw [hs, if_neg Set.not_nonempty_empty]


section GaloisContent

variable {P φ : Type*}

/--
Support relation: s supports ψ if all possibilities in s satisfy ψ.

This is the fundamental entailment relation of dynamic semantics.
-/
def supportOf (sat : P → φ → Prop) (s : InfoStateOf P) (ψ : φ) : Prop :=
  ∀ p ∈ s, sat p ψ

/--
Content of a formula: all possibilities satisfying it.
-/
def contentOf (sat : P → φ → Prop) (ψ : φ) : InfoStateOf P :=
  { p | sat p ψ }

/--
Galois connection: s ⊆ content ψ  ↔  s supports ψ

This is the fundamental duality of dynamic semantics.
-/
theorem support_iff_subset_content (sat : P → φ → Prop) (s : InfoStateOf P) (ψ : φ) :
    supportOf sat s ψ ↔ s ⊆ contentOf sat ψ := by
  constructor
  · intro h p hp
    exact h p hp
  · intro h p hp
    exact h hp

/--
Support is downward closed: smaller states support more.
-/
theorem support_mono (sat : P → φ → Prop) (s t : InfoStateOf P) (ψ : φ)
    (h : t ⊆ s) (hs : supportOf sat s ψ) : supportOf sat t ψ :=
  λ p hp => hs p (h hp)

/--
Empty state supports everything (vacuously).
-/
theorem empty_supports (sat : P → φ → Prop) (ψ : φ) :
    supportOf sat ∅ ψ := λ _ hp => False.elim hp

/--
Content is antitone in entailment.
-/
theorem content_mono (sat : P → φ → Prop) (ψ₁ ψ₂ : φ)
    (h : ∀ p, sat p ψ₁ → sat p ψ₂) :
    contentOf sat ψ₁ ⊆ contentOf sat ψ₂ :=
  λ _ hp => h _ hp

end GaloisContent


/--
The standard update construction: filter by satisfaction.

This is how PLA, DRT, DPL all define updates.
-/
def updateFromSat {P φ : Type*} (sat : P → φ → Prop) (ψ : φ) : CCP P :=
  λ s => { p ∈ s | sat p ψ }

/-- Standard updates are eliminative -/
theorem updateFromSat_eliminative {P φ : Type*} (sat : P → φ → Prop) (ψ : φ) :
    IsEliminative (updateFromSat sat ψ) :=
  λ _ _ hp => hp.1

/-- Standard update membership -/
theorem mem_updateFromSat {P φ : Type*} (sat : P → φ → Prop) (ψ : φ)
    (s : InfoStateOf P) (p : P) :
    p ∈ updateFromSat sat ψ s ↔ p ∈ s ∧ sat p ψ := Iff.rfl

/-- Update equals intersection with content -/
theorem updateFromSat_eq_inter_content {P φ : Type*} (sat : P → φ → Prop)
    (ψ : φ) (s : InfoStateOf P) :
    updateFromSat sat ψ s = s ∩ contentOf sat ψ := by
  ext p
  simp only [mem_updateFromSat, contentOf, Set.mem_inter_iff, Set.mem_setOf_eq]

/-- Support-Update equivalence -/
theorem support_iff_update_eq {P φ : Type*} (sat : P → φ → Prop)
    (ψ : φ) (s : InfoStateOf P) :
    supportOf sat s ψ ↔ updateFromSat sat ψ s = s := by
  constructor
  · intro h
    ext p
    simp only [mem_updateFromSat]
    constructor
    · intro ⟨hp, _⟩; exact hp
    · intro hp; exact ⟨hp, h p hp⟩
  · intro h p hp
    have : p ∈ updateFromSat sat ψ s := by rw [h]; exact hp
    exact this.2


/--
Dynamic entailment: φ dynamically entails ψ if updating with φ
always yields a state that supports ψ.
-/
def dynamicEntailsOf {P φ : Type*} (sat : P → φ → Prop) (ψ₁ ψ₂ : φ) : Prop :=
  ∀ s : InfoStateOf P, supportOf sat (updateFromSat sat ψ₁ s) ψ₂

/-- Dynamic entailment is reflexive -/
theorem dynamicEntails_refl {P φ : Type*} (sat : P → φ → Prop) (ψ : φ) :
    dynamicEntailsOf sat ψ ψ :=
  λ _ _ hp => hp.2

/-- Dynamic entailment is transitive -/
theorem dynamicEntails_trans {P φ : Type*} (sat : P → φ → Prop)
    (ψ₁ ψ₂ ψ₃ : φ) (h1 : dynamicEntailsOf sat ψ₁ ψ₂) (h2 : dynamicEntailsOf sat ψ₂ ψ₃) :
    dynamicEntailsOf sat ψ₁ ψ₃ := λ s p hp => by
  -- p ∈ updateFromSat sat ψ₁ s means p ∈ s and sat p ψ₁
  have hp_sat1 : sat p ψ₁ := hp.2
  have hp_in_s : p ∈ s := hp.1
  -- By h1, updateFromSat sat ψ₁ s supports ψ₂, so sat p ψ₂
  have hp_sat2 : sat p ψ₂ := h1 s p hp
  -- p ∈ updateFromSat sat ψ₂ s
  have hp_in_2 : p ∈ updateFromSat sat ψ₂ s := ⟨hp_in_s, hp_sat2⟩
  -- By h2, updateFromSat sat ψ₂ s supports ψ₃
  exact h2 s p hp_in_2


/--
Update is monotone: larger input states yield larger output states.
-/
theorem updateFromSat_monotone {P φ : Type*} (sat : P → φ → Prop) (ψ : φ)
    (s t : InfoStateOf P) (h : s ⊆ t) :
    updateFromSat sat ψ s ⊆ updateFromSat sat ψ t := by
  intro p hp
  exact ⟨h hp.1, hp.2⟩


-- ═══ Assignment & State Infrastructure ═══

/-- Variable assignment: function from indices to entities. -/
abbrev Assignment (E : Type*) := Nat → E

namespace Assignment

/-- Assignment update g[n↦d]. -/
def update {E : Type*} (g : Assignment E) (n : Nat) (d : E) : Assignment E :=
  λ m => if m = n then d else g m

@[simp] theorem update_at {E : Type*} (g : Assignment E) (n : Nat) (d : E) :
    (g.update n d) n = d := by simp [update]

@[simp] theorem update_ne {E : Type*} (g : Assignment E) {n m : Nat} (d : E) (h : m ≠ n) :
    (g.update n d) m = g m := by simp [update, h]

theorem update_overwrite {E : Type*} (g : Assignment E) (n : Nat) (x y : E) :
    (g.update n x).update n y = g.update n y := by
  funext m; simp [update]; split <;> rfl

theorem update_comm {E : Type*} (g : Assignment E) {n m : Nat} (x y : E) (h : n ≠ m) :
    (g.update n x).update m y = (g.update m y).update n x := by
  funext k; simp [update]; by_cases hn : k = n <;> by_cases hm : k = m <;> simp_all

end Assignment

/-- State: set of world-assignment pairs. -/
abbrev State (W E : Type*) := Set (W × Assignment E)

/-- State-level CCP: context change potential over world-assignment states.
    Definitionally equal to `CCP (W × Assignment E)`, so all CCP infrastructure
    (monoid, neg, might, tests, entailment, Galois connection) applies. -/
abbrev StateCCP (W E : Type*) := CCP (W × Assignment E)

-- ═══ Distributivity ═══

/-- A CCP is distributive when it processes each element of the input independently:
    φ(s) = ⋃_{i∈s} φ({i}). -/
def IsDistributive {P : Type*} (φ : CCP P) : Prop :=
  ∀ s, φ s = {p | ∃ i ∈ s, p ∈ φ {i}}

/-- `updateFromSat` is always distributive: it filters per-element. -/
theorem updateFromSat_isDistributive {P φ : Type*} (sat : P → φ → Prop) (ψ : φ) :
    IsDistributive (updateFromSat sat ψ) := by
  intro s; ext p; simp only [updateFromSat, Set.mem_setOf_eq]
  constructor
  · intro ⟨hp, hsat⟩; exact ⟨p, hp, ⟨rfl, hsat⟩⟩
  · rintro ⟨i, hi, hpi, hsat⟩; cases hpi; exact ⟨hi, hsat⟩

/-- `CCP.might` is not distributive: the whole-context test can pass while
    individual-element tests fail.

    Witness: P = Bool, φ keeps only `true`.
    `might φ {true, false} = {true, false}` (whole-context test passes),
    but per-singleton: `might φ {false} = ∅` (test fails on false-only context).
    So `false` is in the whole-context result but not the distributive union. -/
theorem might_not_isDistributive :
    ∃ (P : Type) (φ : CCP P), ¬IsDistributive (CCP.might φ) := by
  use Bool
  let φ : CCP Bool := λ s => {p ∈ s | p = true}
  use φ
  intro hD
  let s : Set Bool := {true, false}
  have hφ_nonempty : (φ s).Nonempty := by
    refine ⟨true, ?_, rfl⟩
    show true ∈ s
    exact Or.inl rfl
  have hmem : false ∈ CCP.might φ s := by
    simp only [CCP.might, hφ_nonempty, ↓reduceIte]
    show false ∈ s
    exact Or.inr rfl
  rw [hD s] at hmem
  obtain ⟨i, hi, hmem_i⟩ := hmem
  simp only [CCP.might] at hmem_i
  split at hmem_i
  · next hne =>
    cases hi with
    | inl h =>
      subst h
      have : false ∈ ({true} : Set Bool) := hmem_i
      change false = true at this
      exact absurd this (by decide)
    | inr h =>
      subst h
      obtain ⟨x, hx_mem, hx_val⟩ := hne
      change x = false at hx_mem
      subst hx_mem
      exact absurd hx_val (by decide)
  · exact hmem_i

end Semantics.Dynamic.Core
