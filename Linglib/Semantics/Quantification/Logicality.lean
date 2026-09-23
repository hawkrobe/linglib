module

public import Linglib.Semantics.Quantification.Defs

/-!
# Logicality and Invariance Conditions
[peters-westerstahl-2006] [feferman-1999] [van-benthem-1984]

Invariance conditions that characterize "logical" quantifiers, ordered
by strength: HOM → INJ → ISOM → EXT.

- **ISOM** (isomorphism invariance) = `QuantityInvariant` in `Defs.lean`
- **EXT** (extension) = trivial for `GQ α` (universe-free representation)
- **INJ** (injective-homomorphism invariance)
- **HOM** (surjective-homomorphism invariance, [feferman-1999])

Key result: INJ ≡ ISOM + EXT ([peters-westerstahl-2006] Ch 9 Prop 3).
Since EXT is trivial for `GQ α`, INJ ↔ ISOM in our setting.
-/

@[expose] public section

namespace Quantifier.Logicality

open Quantifier Quantifier.GQ

variable {α β : Type*}

/-! ### Invariance Hierarchy -/

/-- Homomorphism invariance (HOM): Q is preserved under surjective maps.
    [feferman-1999]: HOM characterizes "absolutely logical" operations.
    Stronger than ISOM: surjections can collapse elements, so HOM-invariant
    quantifiers cannot distinguish elements that map to the same image.

    For a family of quantifiers indexed by type, `q` on α and `q'` on β
    are HOM-related when any surjection preserves truth values. -/
def HomInvariant (q : GQ α) (q' : GQ β) : Prop :=
  ∀ (f : α → β), Function.Surjective f →
    ∀ (A B : β → Prop), q (A ∘ f) (B ∘ f) ↔ q' A B

/-- Injective homomorphism invariance (INJ): Q is preserved under injections.
    INJ sits between HOM and ISOM: HOM → INJ → ISOM.
    [peters-westerstahl-2006] Ch 9 §2. -/
def InjInvariant (q : GQ α) (q' : GQ β) : Prop :=
  ∀ (f : α → β), Function.Injective f →
    ∀ (A B : β → Prop), q (A ∘ f) (B ∘ f) ↔ q' A B

/-- HOM (same type) implies ISOM. Every bijection is a surjection.

    Convention alignment: `QuantityInvariant` uses `A(f(x)) ↔ A'(x)` (the bijection
    goes from the *new* domain to the *old*), while `HomInvariant` uses `A ∘ f`.
    Given `hA : A(f(x)) ↔ A'(x)`, we have `A ∘ f = A'` (as functions, via funext).
    So `HomInvariant` with `f` gives `q (A ∘ f) (B ∘ f) ↔ q A B`,
    i.e., `q A' B' ↔ q A B`.

    [peters-westerstahl-2006] Ch 9. -/
theorem hom_implies_isom_same_type (q : GQ α)
    (hHom : HomInvariant q q) :
    QuantityInvariant q := by
  intro A B A' B' f hBij hA hB
  have hAf : A ∘ f = A' := funext (λ x => propext (hA x))
  have hBf : B ∘ f = B' := funext (λ x => propext (hB x))
  have h := hHom f hBij.surjective A B
  rw [hAf, hBf] at h
  exact h.symm

/-! ### INJ ≡ ISOM + EXT -/

/-- [peters-westerstahl-2006] Ch 9 Prop 3 (one direction): ISOM → INJ
    for same-type quantifiers on a finite domain.

    On a finite type, every injection is a bijection, so ISOM (bijection
    invariance) immediately gives INJ (injection invariance). -/
theorem isom_implies_inj_same_type [Fintype α] (q : GQ α)
    (hIsom : QuantityInvariant q) :
    InjInvariant q q := by
  intro f hInj A B
  have hBij : Function.Bijective f :=
    ⟨hInj, Finite.injective_iff_surjective.mp hInj⟩
  exact (hIsom A B (A ∘ f) (B ∘ f) f hBij (λ _ => Iff.rfl) (λ _ => Iff.rfl)).symm

/-- Bijection invariance is definitionally `QuantityInvariant`. -/
theorem quantityInvariant_is_isom (q : GQ α) :
    QuantityInvariant q ↔ (∀ (A B A' B' : α → Prop) (f : α → α),
      Function.Bijective f →
      (∀ x, A (f x) ↔ A' x) → (∀ x, B (f x) ↔ B' x) →
      (q A B ↔ q A' B')) :=
  Iff.rfl

end Quantifier.Logicality
