import Linglib.Semantics.Dynamic.ContextChange
import Linglib.Semantics.Dynamic.Possibility

/-!
# Register-form information states

Unbased information states over register-keyed possibilities
(`Assignment E := Nat → E`, i.e. the point object at `V := ℕ`) — the
state notion of the pre-based dynamic frameworks (PLA, BUS, file change
semantics). The based refinement lives in `State.lean`.

## Main definitions

- `InfoState W E`: sets of register-form possibilities.
- `InfoState.definedAt`, `novelAt`, `worlds`, `subsistsIn`, `supports`:
  the unbased state vocabulary.
- `InfoState.update`, `randomAssign`, `CCP.exists_`, `CCP.ofProp`,
  `CCP.ofPred1`, `CCP.ofPred2`: the possibility-specific CCP
  constructors.

## References

- [kamp-vangenabith-reyle-2011]
- [heim-1982]
-/

namespace DynamicSemantics

open _root_.Core (Assignment)


/-! ### Register-form information states

Register-keyed dynamic semantics (`Assignment E := Nat → E`) instantiates
the point object at `V := ℕ`. -/

/-- Information state: set of possibilities.

This is `InfoStateOf (Possibility W ℕ E)` — a specialization of the
generic `InfoStateOf` to world-assignment possibilities. -/
abbrev InfoState (W : Type*) (E : Type*) := Set (Possibility W ℕ E)

namespace InfoState

variable {W E : Type*}

/-- The trivial state: all possibilities. -/
def univ : InfoState W E := Set.univ

/-- The absurd state: no possibilities. -/
def empty : InfoState W E := (∅ : Set (Possibility W ℕ E))

/-- State is consistent (non-empty). -/
def consistent (s : InfoState W E) : Prop := s.Nonempty

/-- State is trivial (all possibilities). -/
def trivial (s : InfoState W E) : Prop := s = Set.univ

/-- Variable x is defined in state s iff all possibilities agree on x's value. -/
def definedAt (s : InfoState W E) (x : Nat) : Prop :=
  ∀ p q : Possibility W ℕ E, p ∈ s → q ∈ s → p.assignment x = q.assignment x

/-- The set of defined variables in a state. -/
def definedVars (s : InfoState W E) : Set Nat :=
  { x | s.definedAt x }

/-- Variable x is novel in state s iff x is not defined. -/
def novelAt (s : InfoState W E) (x : Nat) : Prop := ¬s.definedAt x

/-- In a consistent state, novel means assignments actually disagree. -/
theorem novelAt_iff_disagree (s : InfoState W E) (x : Nat) (hs : s.consistent) :
    s.novelAt x ↔ ∃ p q : Possibility W ℕ E, p ∈ s ∧ q ∈ s ∧ p.assignment x ≠ q.assignment x := by
  constructor
  · intro h
    simp only [novelAt, definedAt] at h
    push Not at h
    exact h
  · intro ⟨p, q, hp, hq, hne⟩
    simp only [novelAt, definedAt]
    push Not
    exact ⟨p, q, hp, hq, hne⟩

/-- Project to the set of worlds in the state. -/
def worlds (s : InfoState W E) : Set W :=
  { w | ∃ p ∈ s, p.world = w }

end InfoState

/-- State subsistence: s subsists in s' iff every possibility in s has a descendant in s'. -/
def InfoState.subsistsIn {W E : Type*} (s s' : InfoState W E) : Prop :=
  ∀ p ∈ s, ∃ p' ∈ s', p.world = p'.world ∧
    ∀ x, s.definedAt x → p.assignment x = p'.assignment x

scoped notation:50 s " ⪯ " s' => InfoState.subsistsIn s s'

namespace InfoState

variable {W E : Type*}

/-- Subsistence is reflexive. -/
theorem subsistsIn_refl (s : InfoState W E) : s ⪯ s := by
  intro p hp
  exact ⟨p, hp, rfl, λ _ _ => rfl⟩

/-- Subset implies subsistence. -/
theorem subset_subsistsIn {s s' : InfoState W E} (h : s ⊆ s') : s ⪯ s' := by
  intro p hp
  exact ⟨p, h hp, rfl, λ _ _ => rfl⟩

/-- State s supports proposition φ iff φ holds at all worlds in s:
`supportOf` at the world-evaluation satisfaction relation. -/
def supports (s : InfoState W E) (φ : W → Prop) : Prop :=
  supportOf (λ p ψ => ψ p.world) s φ

scoped notation:50 s " ⊫ " φ => InfoState.supports s φ

/-- Support is preserved by subset. -/
theorem supports_mono {s s' : InfoState W E} (h : s ⊆ s')
    (φ : W → Prop) (hsupp : s' ⊫ φ) : s ⊫ φ :=
  support_mono _ s' s φ h hsupp

end InfoState

/-! ### Context change over possibilities -/

/-- Update state with proposition: keep only possibilities where φ holds. -/
def InfoState.update {W E : Type*} (s : InfoState W E) (φ : W → Prop) : InfoState W E :=
  { p ∈ s | φ p.world }

notation:max s "⟦" φ "⟧" => InfoState.update s φ

namespace InfoState

variable {W E : Type*}

/-- Propositional update is monotone in the state argument. -/
theorem update_monotone (φ : W → Prop) : Monotone (· ⟦φ⟧ : InfoState W E → InfoState W E) :=
  sep_monotone _

/-- Update is monotonic: larger states give larger results -/
theorem update_mono {s s' : InfoState W E} (h : s ⊆ s') (φ : W → Prop) :
    s⟦φ⟧ ⊆ s'⟦φ⟧ :=
  update_monotone φ h

/-- Update is idempotent -/
theorem update_update (s : InfoState W E) (φ : W → Prop) :
    s⟦φ⟧⟦φ⟧ = s⟦φ⟧ := by
  ext p
  simp only [update, Set.mem_setOf_eq]
  constructor
  · intro ⟨⟨hs, _⟩, hφ⟩; exact ⟨hs, hφ⟩
  · intro ⟨hs, hφ⟩; exact ⟨⟨hs, hφ⟩, hφ⟩

/-- Sequential update = conjunction -/
theorem update_seq (s : InfoState W E) (φ ψ : W → Prop) :
    s⟦φ⟧⟦ψ⟧ = s⟦λ w => φ w ∧ ψ w⟧ := by
  ext p
  simp only [update, Set.mem_setOf_eq]
  constructor
  · intro ⟨⟨hs, hφ⟩, hψ⟩; exact ⟨hs, hφ, hψ⟩
  · intro ⟨hs, hφ, hψ⟩; exact ⟨⟨hs, hφ⟩, hψ⟩

/-- Update preserves definedness -/
theorem update_preserves_defined (s : InfoState W E) (φ : W → Prop) (x : Nat)
    (h : s.definedAt x) : s⟦φ⟧.definedAt x := by
  intro p q hp hq
  exact h p q hp.1 hq.1

/-- s[φ] ⊫ φ -/
theorem update_supports (s : InfoState W E) (φ : W → Prop) : s⟦φ⟧ ⊫ φ := by
  intro p ⟨_, hφ⟩
  exact hφ

/-- Dynamic entailment for propositions. -/
def dynamicEntails (φ ψ : W → Prop) : Prop :=
  ∀ s : InfoState W E, (s⟦φ⟧).consistent → s⟦φ⟧ ⊫ ψ

/-- Any proposition dynamically entails itself -/
theorem dynamicEntails_refl (φ : W → Prop) : dynamicEntails (W := W) (E := E) φ φ := by
  intro s _
  exact update_supports s φ

/-- φ dynamically entails φ ∧ ψ when φ entails ψ -/
theorem dynamicEntails_conj (φ ψ : W → Prop)
    (h : dynamicEntails (W := W) (E := E) φ ψ) :
    dynamicEntails (W := W) (E := E) φ (λ w => φ w ∧ ψ w) := by
  intro s hcons p hp
  constructor
  · exact update_supports s φ p hp
  · exact h s hcons p hp

end InfoState

/-- Random assignment: introduce new discourse referent at variable x. -/
def InfoState.randomAssign {W E : Type*} (s : InfoState W E) (x : Nat)
    (domain : Set E) : InfoState W E :=
  { p' | ∃ p ∈ s, ∃ e ∈ domain, p' = p.extend x e }

/-- Random assignment with full domain -/
def InfoState.randomAssignFull {W E : Type*} (s : InfoState W E) (x : Nat) : InfoState W E :=
  { p' | ∃ p ∈ s, ∃ e : E, p' = p.extend x e }

namespace InfoState

variable {W E : Type*}

/-- Random assignment makes x novel (when domain has multiple elements) -/
theorem randomAssign_makes_novel (s : InfoState W E) (x : Nat) (domain : Set E)
    (hs : s.consistent) (hdom : ∃ e₁ e₂ : E, e₁ ∈ domain ∧ e₂ ∈ domain ∧ e₁ ≠ e₂) :
    (s.randomAssign x domain).novelAt x := by
  obtain ⟨p, hp⟩ := hs
  obtain ⟨e₁, e₂, he₁, he₂, hne⟩ := hdom
  simp only [novelAt, definedAt]
  push Not
  refine ⟨p.extend x e₁, p.extend x e₂, ?_, ?_, ?_⟩
  · exact ⟨p, hp, e₁, he₁, rfl⟩
  · exact ⟨p, hp, e₂, he₂, rfl⟩
  · simp [Possibility.extend, hne]

/-- Random assignment preserves other defined variables -/
theorem randomAssign_preserves_defined (s : InfoState W E) (x y : Nat) (domain : Set E)
    (h : s.definedAt y) (hne : y ≠ x) : (s.randomAssign x domain).definedAt y := by
  intro p q hp hq
  obtain ⟨p', hp', _, _, rfl⟩ := hp
  obtain ⟨q', hq', _, _, rfl⟩ := hq
  simp only [Possibility.extend]
  simp [hne]
  exact h p' q' hp' hq'

end InfoState

/-- Existential CCP: ∃x.φ introduces x then updates with φ. -/
def CCP.exists_ {W E : Type*} (x : Nat) (domain : Set E)
    (φ : CCP (Possibility W ℕ E)) : CCP (Possibility W ℕ E) :=
  λ (s : InfoState W E) => φ (s.randomAssign x domain)

/-- Existential with full domain -/
def CCP.existsFull {W E : Type*} (x : Nat)
    (φ : CCP (Possibility W ℕ E)) : CCP (Possibility W ℕ E) :=
  λ (s : InfoState W E) => φ (s.randomAssignFull x)

/--
Lift a classical proposition to a CCP.
-/
def CCP.ofProp {W E : Type*} (φ : W → Prop) : CCP (Possibility W ℕ E) :=
  λ (s : InfoState W E) => s⟦φ⟧

/--
Lift a predicate on entities (via variable lookup).
-/
def CCP.ofPred1 {W E : Type*} (p : E → W → Prop) (x : Nat) : CCP (Possibility W ℕ E) :=
  λ (s : InfoState W E) => { poss ∈ s | p (poss.assignment x) poss.world }

/--
Lift a binary predicate.
-/
def CCP.ofPred2 {W E : Type*} (p : E → E → W → Prop) (x y : Nat) : CCP (Possibility W ℕ E) :=
  λ (s : InfoState W E) => { poss ∈ s | p (poss.assignment x) (poss.assignment y) poss.world }


end DynamicSemantics
