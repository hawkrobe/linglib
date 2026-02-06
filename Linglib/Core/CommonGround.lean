import Linglib.Core.Proposition

/-!
# Common Ground

Conversational common ground following Stalnaker (1974, 2002).
-/

namespace Core.CommonGround

open Core.Proposition

/-- A context set is a predicate on worlds compatible with the common ground. -/
def ContextSet (W : Type*) := W → Prop

namespace ContextSet

variable {W : Type*}

/-- The trivial context: all worlds possible. -/
def trivial : ContextSet W := λ _ => True

/-- The absurd context: no worlds possible. -/
def absurd : ContextSet W := λ _ => False

/-- A world is in the context set. -/
def mem (c : ContextSet W) (w : W) : Prop := c w

/-- The context set is non-empty. -/
def nonEmpty (c : ContextSet W) : Prop := ∃ w, c w

/-- A context entails a proposition iff it holds at all worlds in the context. -/
def entails (c : ContextSet W) (p : BProp W) : Prop :=
  ∀ w, c w → p w = true

notation:50 c " ⊧ " p => entails c p

/-- A proposition is compatible with a context if it holds at some world. -/
def compatible (c : ContextSet W) (p : BProp W) : Prop :=
  ∃ w, c w ∧ p w = true

/-- Trivial context entails only tautologies. -/
theorem trivial_entails_iff (p : BProp W) :
    (trivial ⊧ p) ↔ ∀ w, p w = true := by
  unfold entails trivial
  exact ⟨λ h w => h w True.intro, λ h w _ => h w⟩

/-- Absurd context entails everything. -/
theorem absurd_entails (p : BProp W) : absurd ⊧ p := λ _ hw => hw.elim

/-- Update a context with a proposition: keep only worlds where it holds. -/
def update (c : ContextSet W) (p : BProp W) : ContextSet W :=
  λ w => c w ∧ p w = true

notation:60 c " + " p => update c p

/-- Update restricts the context. -/
theorem update_restricts (c : ContextSet W) (p : BProp W) (w : W) :
    (c + p) w → c w := And.left

/-- Updated context entails the update proposition. -/
theorem update_entails (c : ContextSet W) (p : BProp W) :
    (c + p) ⊧ p := λ _ hw => hw.2

/-- Updating with what's already entailed doesn't change the context. -/
theorem update_entailed (c : ContextSet W) (p : BProp W) (h : c ⊧ p) :
    (c + p) = c := by
  funext w
  unfold update
  exact propext ⟨And.left, λ hw => ⟨hw, h w hw⟩⟩

/-- Sequential updates are associative. -/
theorem update_assoc (c : ContextSet W) (p q : BProp W) :
    ((c + p) + q) = λ w => c w ∧ p w = true ∧ q w = true := by
  funext w
  simp only [update, and_assoc]

/-- Intersection of contexts: worlds in both. -/
def inter (c₁ c₂ : ContextSet W) : ContextSet W :=
  λ w => c₁ w ∧ c₂ w

/-- Union of contexts: worlds in either. -/
def union (c₁ c₂ : ContextSet W) : ContextSet W :=
  λ w => c₁ w ∨ c₂ w

instance : Inter (ContextSet W) where
  inter := inter

instance : Union (ContextSet W) where
  union := union

/-- Create a context from a single proposition: worlds where it holds. -/
def fromProp (p : BProp W) : ContextSet W :=
  λ w => p w = true

/-- Updating trivial context with P gives context from P. -/
theorem trivial_update (p : BProp W) : (trivial + p) = fromProp p := by
  funext w
  simp only [update, trivial, fromProp, true_and]

/-- Entailment is monotonic: smaller context entails more. -/
theorem entails_mono (c₁ c₂ : ContextSet W) (p : BProp W)
    (h_sub : ∀ w, c₁ w → c₂ w) (h_ent : c₂ ⊧ p) : c₁ ⊧ p :=
  λ w hw => h_ent w (h_sub w hw)

/-- Update is monotonic in the context. -/
theorem update_mono (c₁ c₂ : ContextSet W) (p : BProp W)
    (h : ∀ w, c₁ w → c₂ w) (w : W) :
    (c₁ + p) w → (c₂ + p) w := λ ⟨hw, hp⟩ => ⟨h w hw, hp⟩

end ContextSet

/-- Common ground as a set of mutually believed propositions. -/
structure CG (W : Type*) where
  /-- The propositions in the common ground -/
  propositions : List (BProp W)

namespace CG

variable {W : Type*}

/-- The context set determined by a common ground. -/
def contextSet (cg : CG W) : ContextSet W :=
  λ w => cg.propositions.all (λ p => p w)

/-- Add a proposition to the common ground. -/
def add (cg : CG W) (p : BProp W) : CG W :=
  { propositions := p :: cg.propositions }

/-- Empty common ground (no shared beliefs). -/
def empty : CG W := { propositions := [] }

/-- Empty CG gives trivial context set. -/
theorem empty_contextSet : (empty : CG W).contextSet = ContextSet.trivial := by
  funext w
  simp only [contextSet, empty, ContextSet.trivial, List.all_nil]

/-- Adding a proposition restricts the context set. -/
theorem add_restricts (cg : CG W) (p : BProp W) (w : W) :
    (cg.add p).contextSet w → cg.contextSet w := by
  simp only [contextSet, add, List.all_cons, Bool.and_eq_true]
  exact And.right

end CG

/-- Decidable context set: all worlds compatible with common knowledge.
Mirrors `ContextSet` but uses `Bool` instead of `Prop`, enabling computation. -/
abbrev BContextSet (W : Type*) := W → Bool

namespace BContextSet

variable {W : Type*}

/-- Coerce a decidable context set to its classical (Prop-valued) counterpart. -/
def toProp (c : BContextSet W) : ContextSet W :=
  λ w => c w = true

/-- The trivial context: all worlds possible. -/
def trivial : BContextSet W := λ _ => true

/-- The absurd context: no worlds possible. -/
def absurd : BContextSet W := λ _ => false

/-- Update a decidable context with a decidable proposition. -/
def update (c : BContextSet W) (p : W → Bool) : BContextSet W :=
  λ w => c w && p w

/-- Filter a list of worlds to those compatible with the context. -/
def filterWorlds (c : BContextSet W) (worlds : List W) : List W :=
  worlds.filter c

/-- Decidable entailment: p holds at all context-compatible worlds. -/
def entails (c : BContextSet W) (worlds : List W) (p : W → Bool) : Bool :=
  worlds.all λ w => !c w || p w

/-- Trivial context set coerces to classical trivial. -/
theorem trivial_toProp : (trivial : BContextSet W).toProp = ContextSet.trivial := by
  funext w; simp [trivial, toProp, ContextSet.trivial]

/-- Update corresponds to classical update under coercion. -/
theorem update_toProp (c : BContextSet W) (p : W → Bool) :
    (c.update p).toProp = ContextSet.update c.toProp p := by
  funext w
  simp only [update, toProp, ContextSet.update, Bool.and_eq_true]

end BContextSet

end Core.CommonGround
