import Linglib.Core.Logic.Quantification.Defs

/-!
# Logicality and Invariance Conditions
@cite{peters-westerstahl-2006} @cite{feferman-1999} @cite{van-benthem-1984}

Invariance conditions that characterize "logical" quantifiers, ordered
by strength: HOM → INJ → ISOM → EXT.

- **ISOM** (isomorphism invariance) = `QuantityInvariant` in `Defs.lean`
- **EXT** (extension) = trivial for `GQ α` (universe-free representation)
- **INJ** (injective-homomorphism invariance)
- **HOM** (surjective-homomorphism invariance, @cite{feferman-1999})

Key result: INJ ≡ ISOM + EXT (@cite{peters-westerstahl-2006} Ch 9 Prop 3).
Since EXT is trivial for `GQ α`, INJ ↔ ISOM in our setting.
-/

namespace Core.Quantification.Logicality

open Core.Quantification

variable {α β : Type*}

-- ============================================================================
-- §1 Invariance Hierarchy
-- ============================================================================

/-- Homomorphism invariance (HOM): Q is preserved under surjective maps.
    @cite{feferman-1999}: HOM characterizes "absolutely logical" operations.
    Stronger than ISOM: surjections can collapse elements, so HOM-invariant
    quantifiers cannot distinguish elements that map to the same image.

    For a family of quantifiers indexed by type, `q` on α and `q'` on β
    are HOM-related when any surjection preserves truth values. -/
def HomInvariant (q : GQ α) (q' : GQ β) : Prop :=
  ∀ (f : α → β), Function.Surjective f →
    ∀ (A B : β → Bool), q (A ∘ f) (B ∘ f) = q' A B

/-- Injective homomorphism invariance (INJ): Q is preserved under injections.
    INJ sits between HOM and ISOM: HOM → INJ → ISOM.
    @cite{peters-westerstahl-2006} Ch 9 §2. -/
def InjInvariant (q : GQ α) (q' : GQ β) : Prop :=
  ∀ (f : α → β), Function.Injective f →
    ∀ (A B : β → Bool), q (A ∘ f) (B ∘ f) = q' A B

/-- HOM (same type) implies ISOM. Every bijection is a surjection.

    Convention alignment: `QuantityInvariant` uses `A(f(x)) = A'(x)` (the bijection
    goes from the *new* domain to the *old*), while `HomInvariant` uses `A ∘ f`.
    Given `hA : A(f(x)) = A'(x)`, we have `A = A' ∘ f⁻¹` and `A' = A ∘ f`.
    So `HomInvariant` with `f⁻¹` gives `q(A ∘ f⁻¹)(B ∘ f⁻¹) = q A B`,
    i.e., `q A' B' = q A B` — which is `q A B = q A' B'` reversed.

    @cite{peters-westerstahl-2006} Ch 9. -/
theorem hom_implies_isom_same_type (q : GQ α)
    (hHom : HomInvariant q q) :
    QuantityInvariant q := by
  intro A B A' B' f hBij hA hB
  -- hA: A(f(x)) = A'(x), so A' = A ∘ f, meaning A'(x) = A(f(x))
  -- HomInvariant: q(C ∘ g)(D ∘ g) = q C D for surjective g
  -- Apply with g = f, C = A, D = B:
  -- q(A ∘ f)(B ∘ f) = q A B
  -- But A ∘ f = A', B ∘ f = B', so q A' B' = q A B — reversed!
  -- Actually: (A ∘ f)(x) = A(f(x)) and hA says A(f(x)) = A'(x),
  -- so A ∘ f = A' and B ∘ f = B'.
  have hAf : A ∘ f = A' := funext (λ x => hA x)
  have hBf : B ∘ f = B' := funext (λ x => hB x)
  have h := hHom f hBij.surjective A B
  rw [hAf, hBf] at h
  exact h.symm

-- ============================================================================
-- §2 INJ ≡ ISOM + EXT
-- ============================================================================

/-- @cite{peters-westerstahl-2006} Ch 9 Prop 3 (one direction): ISOM → INJ
    for same-type quantifiers on a finite domain.

    On a finite type, every injection is a bijection, so ISOM (bijection
    invariance) immediately gives INJ (injection invariance). -/
theorem isom_implies_inj_same_type [Fintype α] (q : GQ α)
    (hIsom : QuantityInvariant q) :
    InjInvariant q q := by
  intro f hInj A B
  have hBij : Function.Bijective f :=
    ⟨hInj, Finite.injective_iff_surjective.mp hInj⟩
  -- QuantityInvariant: q A B = q A' B' when ∃ bijection g with A(g(x))=A'(x)
  -- InjInvariant wants: q(A∘f)(B∘f) = q A B
  -- Set A' := A, B' := B, g := f. Then A(f(x)) = ? We need A(f(x)) = A(x)
  -- which is only true when f = id. Wrong direction.
  -- Correct: set A' := A∘f, B' := B∘f, g := f. Then A(g(x)) = A(f(x)) = (A∘f)(x) = A'(x). ✓
  -- So q A B = q (A∘f) (B∘f), i.e., q(A∘f)(B∘f) = q A B.
  exact (hIsom A B (A ∘ f) (B ∘ f) f hBij (λ _ => rfl) (λ _ => rfl)).symm

/-- Bijection invariance implies ISOM (definitional equivalence). -/
theorem quantityInvariant_is_isom (q : GQ α) :
    QuantityInvariant q ↔ (∀ (A B A' B' : α → Bool) (f : α → α),
      Function.Bijective f →
      (∀ x, A (f x) = A' x) → (∀ x, B (f x) = B' x) →
      q A B = q A' B') :=
  Iff.rfl

end Core.Quantification.Logicality
