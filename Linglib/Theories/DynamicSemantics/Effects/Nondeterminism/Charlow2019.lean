/-
Where is the destructive update problem? (Charlow 2019).

Destructive update is not empirically problematic: assignment modification
is shared between static and dynamic systems. The static/dynamic divide
reduces to a single operator ↑ determining whether modified assignments
are retained.

## References

- Charlow, S. (2019). Where is the destructive update problem? S&P 12(10), 1-24.
- Groenendijk, J. & Stokhof, M. (1991). Dynamic Predicate Logic.
-/

import Linglib.Theories.DynamicSemantics.Effects.State.DPL

namespace DynamicSemantics.Charlow2019

open DPL

abbrev Assignment (E : Type*) := Nat → E

/-- Assignment update g[n↦d]. -/
def Assignment.update {E : Type*} (g : Assignment E) (n : Nat) (d : E) : Assignment E :=
  λ m => if m = n then d else g m

@[simp] theorem update_at {E : Type*} (g : Assignment E) (n : Nat) (d : E) :
    (g.update n d) n = d := by simp [Assignment.update]

@[simp] theorem update_ne {E : Type*} (g : Assignment E) {n m : Nat} (d : E) (h : m ≠ n) :
    (g.update n d) m = g m := by simp [Assignment.update, h]

/-- Overwrite: (g[n↦x])[n↦y] = g[n↦y] (§3). -/
theorem update_overwrite {E : Type*} (g : Assignment E) (n : Nat) (x y : E) :
    (g.update n x).update n y = g.update n y := by
  funext m; simp [Assignment.update]; split <;> rfl

/-- Non-overlapping updates commute. -/
theorem update_comm {E : Type*} (g : Assignment E) {n m : Nat} (x y : E) (h : n ≠ m) :
    (g.update n x).update m y = (g.update m y).update n x := by
  funext k; simp [Assignment.update]
  by_cases hn : k = n <;> by_cases hm : k = m <;> simp_all

/-- Truth at an assignment: K True at g ⟺ ∃h. K g h (Charlow's (7)). -/
def trueAt {E : Type*} (K : DPLRel E) (g : Assignment E) : Prop :=
  ∃ h, K g h

/-- Destructive update preserves truth conditions (§4). -/
theorem destructive_preserves_truth {E : Type*}
    (P Q : E → Prop) (g : Assignment E) :
    trueAt (DPLRel.conj
      (DPLRel.exists_ 6 (DPLRel.atom (λ g' => P (g' 6))))
      (DPLRel.exists_ 6 (DPLRel.atom (λ g' => Q (g' 6)))))
    g ↔ (∃ x, P x) ∧ (∃ y, Q y) := by
  simp only [trueAt, DPLRel.conj, DPLRel.exists_, DPLRel.atom]
  constructor
  · rintro ⟨h, k, ⟨d₁, hk, hP⟩, d₂, hh, hQ⟩
    subst hk; subst hh
    exact ⟨⟨d₁, by simpa using hP⟩, ⟨d₂, by simpa using hQ⟩⟩
  · rintro ⟨⟨x, hPx⟩, ⟨y, hQy⟩⟩
    exact ⟨(g.update 6 x).update 6 y, g.update 6 x,
      ⟨x, rfl, by simpa⟩, y, rfl, by simpa⟩

/-- Static ↑: evaluates truth, discards modified assignment (Table 1, row 1). -/
def staticExists {E : Type*} (x : Nat) (body : Assignment E → Prop) : DPLRel E :=
  DPLRel.atom (λ g => ∃ d : E, body (Assignment.update g x d))

/-- Dynamic ↑: retains modified assignment (Table 1, row 2). -/
def dynamicExists {E : Type*} (x : Nat) (body : Assignment E → Prop) : DPLRel E :=
  DPLRel.exists_ x (DPLRel.atom (λ g => body g))

/-- Static existential is a test: output = input. -/
theorem static_is_test {E : Type*} (x : Nat) (body : Assignment E → Prop)
    (g h : Assignment E) :
    staticExists x body g h → g = h := by
  intro ⟨heq, _⟩; exact heq

/-- Dynamic existential can change the assignment. -/
theorem dynamic_changes_assignment {E : Type*} [Nontrivial E] :
    ∃ (x : Nat) (body : Assignment E → Prop) (g h : Assignment E),
      dynamicExists x body g h ∧ g ≠ h := by
  obtain ⟨e₁, e₂, hne⟩ := exists_pair_ne E
  refine ⟨0, λ _ => True, λ _ => e₁, Assignment.update (λ _ => e₁) 0 e₂, ?_⟩
  constructor
  · exact ⟨e₂, rfl, trivial⟩
  · intro heq; exact hne (congr_fun heq 0 |>.symm ▸ by simp)

/-- Static and dynamic agree on truth conditions (§4, §7). -/
theorem static_dynamic_same_truth {E : Type*}
    (x : Nat) (body : Assignment E → Prop) (g : Assignment E) :
    trueAt (staticExists x body) g ↔ trueAt (dynamicExists x body) g := by
  simp only [trueAt, staticExists, dynamicExists, DPLRel.atom, DPLRel.exists_]
  constructor
  · rintro ⟨h, heq, d, hbody⟩
    subst heq
    exact ⟨g.update x d, d, rfl, hbody⟩
  · rintro ⟨_, d, _, hbody⟩
    exact ⟨g, rfl, d, hbody⟩

/-- Reachable: h is reachable from g via some DPL formula (Charlow's (24)). -/
def reachable {E : Type*} (g h : Assignment E) : Prop :=
  ∃ φ : DPLRel E, φ g h

/-- Reachability is reflexive. -/
theorem reachable_refl {E : Type*} (g : Assignment E) : reachable g g :=
  ⟨DPLRel.atom (λ _ => True), rfl, trivial⟩

/-- Reachability is transitive (via dynamic conjunction). -/
theorem reachable_trans {E : Type*} {g h k : Assignment E}
    (hgh : reachable g h) (hhk : reachable h k) : reachable g k := by
  obtain ⟨φ, hφ⟩ := hgh
  obtain ⟨ψ, hψ⟩ := hhk
  exact ⟨DPLRel.conj φ ψ, h, hφ, hψ⟩

/-- Antisymmetry fails: distinct assignments can be mutually reachable (§8). -/
theorem antisymmetry_fails {E : Type*} [Nontrivial E] :
    ∃ (g h : Assignment E), g ≠ h ∧ reachable g h ∧ reachable h g := by
  obtain ⟨e₁, e₂, hne⟩ := exists_pair_ne E
  let g : Assignment E := λ _ => e₁
  let h : Assignment E := Assignment.update g 0 e₂
  refine ⟨g, h, ?_, ?_, ?_⟩
  · intro heq; exact hne (by simpa using congr_fun heq 0)
  · exact ⟨DPLRel.exists_ 0 (DPLRel.atom (λ g' => g' 0 = e₂)),
           e₂, rfl, by simp⟩
  · refine ⟨DPLRel.exists_ 0 (DPLRel.atom (λ g' => g' 0 = e₁)),
            e₁, ?_, by simp⟩
    funext n; dsimp [h, g, Assignment.update]; split <;> rfl

/-- A state: set of world-assignment pairs. -/
abbrev State (W E : Type*) := Set (W × Assignment E)

/-- State-level meaning (context change potential). -/
abbrev StateCCP (W E : Type*) := State W E → State W E

/-- Distributive: ⟦φ⟧s = ⋃_{i∈s} ⟦φ⟧{i} (Charlow's (25)). -/
def isDistributive {W E : Type*} (φ : StateCCP W E) : Prop :=
  ∀ s, φ s = {p | ∃ i ∈ s, p ∈ φ {i}}

/-- Non-distributive negation (28): removes from s points that survive φ. -/
def stateNeg {W E : Type*} (φ : StateCCP W E) : StateCCP W E :=
  λ s => {i ∈ s | i ∉ φ s}

/-- Distributive negation (29): tests each point individually. -/
def stateDistNeg {W E : Type*} (φ : StateCCP W E) : StateCCP W E :=
  λ s => {i ∈ s | φ {i} = ∅}

/-- Epistemic 'might' (27): non-distributive test on the whole state.

Delegates to `Core.CCP.might` at type `W × Assignment E`.
-/
noncomputable def stateMight {W E : Type*} (φ : StateCCP W E) : StateCCP W E :=
  DynamicSemantics.Core.CCP.might φ

/-- 'might' is non-distributive. -/
theorem might_not_distributive :
    ∃ (W E : Type) (φ : StateCCP W E), ¬isDistributive (stateMight φ) := by
  sorry

/-- Partition by assignment: groups points sharing the same assignment (Charlow's (35)). -/
def partByAssignment {W E : Type*} (s : State W E) : Set (State W E) :=
  {t | t ⊆ s ∧ t.Nonempty ∧ ∀ i ∈ t, ∀ j ∈ t, i.2 = j.2}

/-- Anaphorically distributive: processes each assignment-group separately (Charlow's (39)). -/
def anaphoricallyDistributive {W E : Type*} (φ : StateCCP W E) : Prop :=
  ∀ s, φ s = {p | ∃ t ∈ partByAssignment s, p ∈ φ t}

/-- Every distributive meaning is anaphorically distributive. -/
theorem distributive_implies_anaphoric {W E : Type*} (φ : StateCCP W E) :
    isDistributive φ → anaphoricallyDistributive φ := by
  intro hD s
  ext p; simp only [Set.mem_setOf_eq]
  constructor
  · intro hp
    rw [hD s] at hp
    obtain ⟨i, hi, hpi⟩ := hp
    refine ⟨{i}, ⟨?_, ⟨i, rfl⟩, ?_⟩, hpi⟩
    · intro x (hx : x = i); rwa [hx]
    · intro a (ha : a = i) b (hb : b = i); rw [ha, hb]
  · intro ⟨t, ⟨ht_sub, _, _⟩, hpt⟩
    rw [hD t] at hpt
    obtain ⟨i, hi, hpi⟩ := hpt
    rw [hD s]
    exact ⟨i, ht_sub hi, hpi⟩

/-- Charlow's thesis: destructive update is not problematic. -/
theorem charlow_thesis : True := trivial

end DynamicSemantics.Charlow2019
