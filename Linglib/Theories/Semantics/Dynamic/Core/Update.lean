/-
# Context Change Potentials

Core update operations for dynamic semantics over `Possibility W E` states.

## Main definitions

`update`, `randomAssign`, `exists_`, `ofProp`, `ofPred1`, `ofPred2`

## References

- Heim, I. (1982). The Semantics of Definite and Indefinite Noun Phrases.
- Heim, I. (1983). File Change Semantics. In Bäuerle et al.
- Groenendijk, J. & Stokhof, M. (1991). Dynamic Predicate Logic.
-/

import Linglib.Theories.Semantics.Dynamic.Core.Basic
import Linglib.Theories.Semantics.Dynamic.Core.CCP

namespace DynamicSemantics.Core

open InfoState


/-- Update state with proposition: keep only possibilities where φ holds. -/
def InfoState.update {W E : Type*} (s : InfoState W E) (φ : W → Bool) : InfoState W E :=
  { p ∈ s | φ p.world }

notation:max s "⟦" φ "⟧" => InfoState.update s φ

namespace InfoState

variable {W E : Type*}

/-- Update is monotonic: larger states give larger results -/
theorem update_mono {s s' : InfoState W E} (h : s ⊆ s') (φ : W → Bool) :
    s⟦φ⟧ ⊆ s'⟦φ⟧ := by
  intro p ⟨hp, hφ⟩
  exact ⟨h hp, hφ⟩

/-- Update is idempotent -/
theorem update_update (s : InfoState W E) (φ : W → Bool) :
    s⟦φ⟧⟦φ⟧ = s⟦φ⟧ := by
  ext p
  simp only [update, Set.mem_setOf_eq]
  constructor
  · intro ⟨⟨hs, _⟩, hφ⟩; exact ⟨hs, hφ⟩
  · intro ⟨hs, hφ⟩; exact ⟨⟨hs, hφ⟩, hφ⟩

/-- Sequential update = conjunction -/
theorem update_seq (s : InfoState W E) (φ ψ : W → Bool) :
    s⟦φ⟧⟦ψ⟧ = s⟦λ w => φ w && ψ w⟧ := by
  ext p
  simp only [update, Set.mem_setOf_eq, Bool.and_eq_true]
  constructor
  · intro ⟨⟨hs, hφ⟩, hψ⟩; exact ⟨hs, hφ, hψ⟩
  · intro ⟨hs, hφ, hψ⟩; exact ⟨⟨hs, hφ⟩, hψ⟩

/-- Update preserves definedness -/
theorem update_preserves_defined (s : InfoState W E) (φ : W → Bool) (x : Nat)
    (h : s.definedAt x) : s⟦φ⟧.definedAt x := by
  intro p q hp hq
  exact h p q hp.1 hq.1

/-- s[φ] ⊫ φ -/
theorem update_supports (s : InfoState W E) (φ : W → Bool) : s⟦φ⟧ ⊫ φ := by
  intro p ⟨_, hφ⟩
  exact hφ

/-- Dynamic entailment for propositions. -/
def dynamicEntails (φ ψ : W → Bool) : Prop :=
  ∀ s : InfoState W E, (s⟦φ⟧).consistent → s⟦φ⟧ ⊫ ψ

/-- Any proposition dynamically entails itself -/
theorem dynamicEntails_refl (φ : W → Bool) : dynamicEntails (W := W) (E := E) φ φ := by
  intro s _
  exact update_supports s φ

/-- φ dynamically entails φ ∧ ψ when φ entails ψ -/
theorem dynamicEntails_conj (φ ψ : W → Bool)
    (h : dynamicEntails (W := W) (E := E) φ ψ) :
    dynamicEntails (W := W) (E := E) φ (λ w => φ w && ψ w) := by
  intro s hcons p hp
  simp only [Bool.and_eq_true]
  constructor
  · exact update_supports s φ p hp
  · exact h s hcons p hp

end InfoState


/-- Random assignment: introduce new discourse referent at variable x. -/
def InfoState.randomAssign {W E : Type*} (s : InfoState W E) (x : Nat) (domain : Set E) : InfoState W E :=
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
  push_neg
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
    (φ : CCP (Possibility W E)) : CCP (Possibility W E) :=
  λ (s : InfoState W E) => φ (s.randomAssign x domain)

/-- Existential with full domain -/
def CCP.existsFull {W E : Type*} (x : Nat)
    (φ : CCP (Possibility W E)) : CCP (Possibility W E) :=
  λ (s : InfoState W E) => φ (s.randomAssignFull x)

/--
Lift a classical proposition to a CCP.
-/
def CCP.ofProp {W E : Type*} (φ : W → Bool) : CCP (Possibility W E) :=
  λ (s : InfoState W E) => s⟦φ⟧

/--
Lift a predicate on entities (via variable lookup).
-/
def CCP.ofPred1 {W E : Type*} (p : E → W → Bool) (x : Nat) : CCP (Possibility W E) :=
  λ (s : InfoState W E) => { poss ∈ s | p (poss.assignment x) poss.world }

/--
Lift a binary predicate.
-/
def CCP.ofPred2 {W E : Type*} (p : E → E → W → Bool) (x y : Nat) : CCP (Possibility W E) :=
  λ (s : InfoState W E) => { poss ∈ s | p (poss.assignment x) (poss.assignment y) poss.world }


end DynamicSemantics.Core
