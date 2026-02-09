/-
# Intensional Logic Primitives

Framework-agnostic types for intensional semantics: intensions as functions
from indices (possible worlds) to extensions, rigid designators, and evaluation.

These primitives are shared by `IntensionalSemantics/`, `TruthConditional/`,
and `RSA/` — any module that needs world-parameterized meanings.

## References

- Gallin (1975). Intensional and Higher-Order Modal Logic.
- von Fintel & Heim (2011). Intensional Semantics. Ch 1.
- SEP, "Intensional Logic".
-/

import Linglib.Core.Proposition

namespace Core.Intension

/-- An intension of type τ over indices W: a function from worlds to extensions. -/
abbrev Intension (W : Type*) (τ : Type*) := W → τ

/-- A rigid designator: an intension that returns the same value at every world. -/
def rigid {W τ : Type*} (x : τ) : Intension W τ := λ _ => x

/-- Evaluate an intension at a world to get its extension. -/
def evalAt {W τ : Type*} (f : Intension W τ) (w : W) : τ := f w

/-- An intension is rigid iff it assigns the same extension at every world. -/
def IsRigid {W τ : Type*} (f : Intension W τ) : Prop := ∀ w₁ w₂, f w₁ = f w₂

/-- A rigid designator is rigid. -/
theorem rigid_isRigid {W τ : Type*} (x : τ) : IsRigid (rigid (W := W) x) :=
  λ _ _ => rfl

/-- Propositions (W → Bool) are intensions of Bool, i.e. BProp. -/
theorem proposition_eq_bprop (W : Type*) : Intension W Bool = BProp W := rfl

/-- evalAt of rigid returns the original value. -/
theorem evalAt_rigid {W τ : Type*} (x : τ) (w : W) : evalAt (rigid x) w = x := rfl

/-- rigid is injective: different values give different intensions. -/
theorem rigid_injective {W τ : Type*} [Inhabited W] :
    Function.Injective (rigid (W := W) (τ := τ)) :=
  λ _ _ h => congr_fun h default

/-- Two intensions co-refer at world w. -/
def CoRefer {W τ : Type*} (f g : Intension W τ) (w : W) : Prop := f w = g w

/-- Two intensions are co-extensional (agree at every world). -/
def CoExtensional {W τ : Type*} (f g : Intension W τ) : Prop := ∀ w, f w = g w

/-- Kripke's necessity of identity: if two rigid designators co-refer at any
world, they are co-extensional (and hence the same intension).

This is the formal kernel of the Kripke (1980) argument: "Hesperus" and
"Phosphorus" are both rigid; if they co-refer at the actual world then
they pick out the same object at every world, so "Hesperus = Phosphorus"
is necessary if true. -/
theorem rigid_identity_necessary {W τ : Type*}
    (f g : Intension W τ) (hf : IsRigid f) (hg : IsRigid g)
    (w : W) (h : CoRefer f g w) : CoExtensional f g :=
  λ w' => calc
    f w' = f w := hf w' w
    _ = g w := h
    _ = g w' := hg w w'

/-- Iff version of the necessity of identity: for rigid designators,
co-reference at ANY world is equivalent to co-reference at EVERY world.
Identity between rigid designators is never contingent — all or nothing. -/
theorem rigid_allOrNothing {W τ : Type*}
    (f g : Intension W τ) (hf : IsRigid f) (hg : IsRigid g)
    (w₁ w₂ : W) : f w₁ = g w₁ ↔ f w₂ = g w₂ :=
  ⟨λ h => rigid_identity_necessary f g hf hg w₁ h w₂,
   λ h => rigid_identity_necessary f g hf hg w₂ h w₁⟩

/-- Without rigidity, identity CAN be contingent: co-reference at one
world does not imply co-reference at another. This is the essential
contrast that makes `rigid_identity_necessary` non-trivial — rigidity
is doing real work, not just any intensions satisfy the theorem. -/
theorem nonrigid_identity_contingent {W τ : Type*}
    (f g : Intension W τ) (w₁ : W)
    (hDisagree : f w₁ ≠ g w₁) :
    ¬ CoExtensional f g :=
  λ h => hDisagree (h w₁)

/-- An intension that takes different values at two worlds is not rigid.
Contrapositive of `IsRigid`. -/
theorem varying_not_rigid {W τ : Type*}
    (f : Intension W τ) (w₁ w₂ : W) (h : f w₁ ≠ f w₂) :
    ¬ IsRigid f :=
  λ hRigid => h (hRigid w₁ w₂)

/-- A rigid intension is never equal to a non-rigid intension. -/
theorem rigid_neq_nonrigid {W τ : Type*} (f g : Intension W τ)
    (hf : IsRigid f) (hg : ¬ IsRigid g) : f ≠ g := by
  intro heq; subst heq; exact hg hf

/-! ## Stable Character (Kaplan 1989 §XIX Remarks 5-8) -/

/-- A character is stable iff it assigns the same content at every context.

Kaplan (1989) Remark 5: non-indexical expressions have stable character —
their content does not depend on the context of utterance. This generalizes
`constantCharacter` from `Reference/Basic.lean` to the framework-agnostic level. -/
def StableCharacter {C W τ : Type*} (char : C → Intension W τ) : Prop :=
  ∀ c₁ c₂ : C, char c₁ = char c₂

/-- Stable character iff pointwise equal content at every context. -/
theorem stableCharacter_iff_sameContent {C W τ : Type*} (char : C → Intension W τ) :
    StableCharacter char ↔ ∀ c₁ c₂ : C, ∀ w : W, char c₁ w = char c₂ w := by
  constructor
  · intro h c₁ c₂ w; exact congrFun (h c₁ c₂) w
  · intro h c₁ c₂; funext w; exact h c₁ c₂ w

/-- Rigid + stable character = fully constant: the same value at every
context and every world. Kaplan (1989) Remark 10.

If an expression has stable character (non-indexical) and rigid content
(designator), then it yields the same extension everywhere. -/
theorem rigid_stableChar_constant {C W τ : Type*} [Inhabited C]
    (char : C → Intension W τ) (hStable : StableCharacter char)
    (hRigid : ∀ c, IsRigid (char c)) :
    ∀ c₁ c₂ : C, ∀ w₁ w₂ : W, char c₁ w₁ = char c₂ w₂ := by
  intro c₁ c₂ w₁ w₂
  calc char c₁ w₁ = char c₁ w₂ := hRigid c₁ w₁ w₂
    _ = char c₂ w₂ := congrFun (hStable c₁ c₂) w₂

end Core.Intension
