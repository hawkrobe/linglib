import Mathlib.Order.Hom.Lattice
import Mathlib.Data.Set.Lattice
import Linglib.Semantics.Modality.ModalTypes

/-!
# Modals as half-lattice-homomorphisms

A modal operator is a monotone map `Set World →o Prop`. The two canonical modals
are the existential `diamond` (which preserves binary joins — a `SupHom`) and the
universal `box` (which preserves binary meets — an `InfHom`). Their shared
monotonicity yields the one-directional scope facts (`scope_mono_and`,
`scope_mono_or`); the half-homomorphism law for the *matching* coordinator yields
full scope collapse (`scope_collapse`).

This is the truth-conditional skeleton of the "MOD A COORD MOD B" landscape used by
[ciardelli-guerrini-2026]: `◇(A ∨ B) ↔ ◇A ∨ ◇B` and `□(A ∧ B) ↔ □A ∧ □B` (collapse,
on the preserved coordinator), versus a strict one-directional entailment on the
mismatched coordinator (e.g. `◇(A ∧ B) → ◇A ∧ ◇B` but not conversely). Scope is
truth-conditionally detectable exactly where the modal is *not* a homomorphism.

## Main declarations

* `Modal` — the carrier, `Set World →o Prop`.
* `Connective` — the `{⊔, ⊓}` coordinator selector (`or`/`and`).
* `narrow` / `wide` — the LFs `Δ(A ∘ B)` and `ΔA ∘ ΔB`.
* `scope_collapse` — `narrow ↔ wide` when the modal preserves the coordinator.
* `scope_mono_and` / `scope_mono_or` — the monotone one-directional cells.
* `diamond` / `box` — the existential/universal modals, with their preservation
  facts and bundled `SupHom`/`InfHom` (`diamondSupHom`/`boxInfHom`).
* `diamond_not_preserves_and` — a countermodel: the mismatched cell is detectable.
* `ModalForce.interp` — the force-enum → `Modal` keystone.
-/

namespace Semantics.Modality

variable {World : Type*}

/-- A modal operator: a monotone map from propositions-over-worlds to truth values.
`diamond` and `box` are the two canonical instances. -/
abbrev Modal (World : Type*) := Set World →o Prop

/-! ### The coordinator selector -/

/-- The two coordinators, as a choice of `⊔` versus `⊓`. -/
inductive Connective | or | and
  deriving DecidableEq, Repr

/-- Set-level action of a coordinator: `⊔ = ∪` for `or`, `⊓ = ∩` for `and`. -/
def Connective.set : Connective → Set World → Set World → Set World
  | .or  => (· ⊔ ·)
  | .and => (· ⊓ ·)

/-- Prop-level action of a coordinator: the *same* lattice op on `Prop`,
`⊔ = ∨` and `⊓ = ∧`. The shared `⊔`/`⊓` is what makes the `∪ ↔ ∨` and `∩ ↔ ∧`
pairings structural rather than coincidental. -/
def Connective.prop : Connective → Prop → Prop → Prop
  | .or  => (· ⊔ ·)
  | .and => (· ⊓ ·)

/-- A modal *preserves* a coordinator when it is a homomorphism for it:
`Δ(A ∘ B) = ΔA ∘ ΔB`. (`or` ↦ join-preservation, `and` ↦ meet-preservation.) -/
def Modal.Preserves (Δ : Modal World) (c : Connective) : Prop :=
  ∀ A B, Δ (c.set A B) = c.prop (Δ A) (Δ B)

/-! ### The two LFs -/

/-- Narrow-scope LF `Δ(A ∘ B)` — one modal over the coordination. -/
def narrow (Δ : Modal World) (c : Connective) (A B : Set World) : Prop :=
  Δ (c.set A B)

/-- Wide-scope LF `ΔA ∘ ΔB` — a modal in each conjunct. -/
def wide (Δ : Modal World) (c : Connective) (A B : Set World) : Prop :=
  c.prop (Δ A) (Δ B)

/-! ### The 2×2 from two facts -/

/-- **Collapse**: on the coordinator the modal preserves, the two LFs coincide. -/
theorem scope_collapse {Δ : Modal World} {c : Connective}
    (h : Δ.Preserves c) (A B : Set World) : narrow Δ c A B ↔ wide Δ c A B :=
  iff_of_eq (h A B)

/-- **Monotone cell, `and`**: narrow is always at least as strong as wide. -/
theorem scope_mono_and (Δ : Modal World) (A B : Set World) :
    narrow Δ .and A B → wide Δ .and A B :=
  fun h => ⟨Δ.mono inf_le_left h, Δ.mono inf_le_right h⟩

/-- **Monotone cell, `or`**: wide is always at least as strong as narrow. -/
theorem scope_mono_or (Δ : Modal World) (A B : Set World) :
    wide Δ .or A B → narrow Δ .or A B :=
  fun h => h.elim (Δ.mono le_sup_left) (Δ.mono le_sup_right)

/-! ### The two canonical modals -/

/-- ◇ — possibility, the existential modal. -/
def diamond (World : Type*) : Modal World where
  toFun p := ∃ w, p w
  monotone' := fun _ _ hAB ⟨w, hw⟩ => ⟨w, hAB hw⟩

/-- □ — necessity, the universal modal. -/
def box (World : Type*) : Modal World where
  toFun p := ∀ w, p w
  monotone' := fun _ _ hAB h w => hAB (h w)

@[simp] theorem diamond_apply (p : Set World) : diamond World p = ∃ w, p w := rfl
@[simp] theorem box_apply (p : Set World) : box World p = ∀ w, p w := rfl

/-- ◇ preserves `or`: `◇(A ∪ B) = ◇A ∨ ◇B`. -/
theorem diamond_preserves_or (World : Type*) : (diamond World).Preserves .or := by
  intro A B
  simp only [Connective.set, Connective.prop, diamond_apply, Set.sup_eq_union]
  exact propext exists_or

/-- □ preserves `and`: `□(A ∩ B) = □A ∧ □B`. -/
theorem box_preserves_and (World : Type*) : (box World).Preserves .and := by
  intro A B
  simp only [Connective.set, Connective.prop, box_apply, Set.inf_eq_inter]
  exact propext forall_and

/-- ◇ does NOT preserve `and`: on the mismatched cell scope is truth-conditionally
*visible*. Countermodel over `Bool`: `◇({true} ∩ {false}) = ◇∅` is false, but
`◇{true} ∧ ◇{false}` is true. This is [ciardelli-guerrini-2026]'s
conjunctive-permission asymmetry. -/
theorem diamond_not_preserves_and : ¬ (diamond Bool).Preserves .and := by
  intro h
  have hRHS : Connective.prop .and ((diamond Bool) {true}) ((diamond Bool) {false}) :=
    ⟨⟨true, rfl⟩, ⟨false, rfl⟩⟩
  have hLHS : (diamond Bool) (Connective.set .and {true} {false}) :=
    (iff_of_eq (h {true} {false})).mpr hRHS
  obtain ⟨w, hw⟩ := hLHS
  have hmem : w ∈ ({true} ∩ {false} : Set Bool) := hw
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff] at hmem
  exact absurd (hmem.1.symm.trans hmem.2) (by decide)

/-! ### Bundled lattice homomorphisms

`diamond`/`box` are not merely binary-`⊔`/`⊓` preserving; the existential/universal
quantifier preserves *arbitrary* joins/meets, so each is a complete-lattice
homomorphism `Set World → Prop`. Here we export the binary `SupHom`/`InfHom`
bundles for downstream reuse.

[UPSTREAM]: "`fun p => ∃ w, p w` is a `SupHom (Set World) Prop`" (dually for `∀`)
is a clean, mathlib-shaped lemma not currently packaged upstream. -/

/-- ◇ as a bundled join-homomorphism. -/
def diamondSupHom (World : Type*) : SupHom (Set World) Prop where
  toFun := diamond World
  map_sup' := diamond_preserves_or World

/-- □ as a bundled meet-homomorphism. -/
def boxInfHom (World : Type*) : InfHom (Set World) Prop where
  toFun := box World
  map_inf' := box_preserves_and World

/-! ### Force enum → semantics

The keystone connecting [zeijlstra-2007]'s modal-force features to the semantic
modal: a `ModalForce` interprets as the `Modal` that scopes over a coordination,
so "concord yields narrow scope" becomes definitional downstream. -/

/-- Interpret a modal force as a `Modal` operator. -/
def ModalForce.interp (World : Type*) : ModalForce → Modal World
  | .possibility   => diamond World
  | .necessity     => box World
  | .weakNecessity => box World

end Semantics.Modality
