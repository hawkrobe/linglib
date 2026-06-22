/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.TransitionMonoid

/-!
# The syntactic monoid of a language

The *syntactic monoid* of a language `L : Language α` is the quotient of the free monoid
`FreeMonoid α` by the *syntactic congruence*: two words are identified when no two-sided context
distinguishes them as `L`-members, `∀ x y, x ++ u ++ y ∈ L ↔ x ++ v ++ y ∈ L`.

We obtain the syntactic congruence as the kernel of the transition action of the minimal DFA
`L.toDFA` (the *transition monoid* of `L.toDFA`, see
`Linglib.Core.Computability.TransitionMonoid`), and identify it with the two-sided context
equivalence via `Language.syntacticCon_iff`. This is the two-sided refinement of
`Mathlib.Computability.MyhillNerode`, which builds the one-sided right-Nerode quotient
(`Language.leftQuotient`) and proves regularity ↔ finitely many left quotients. It carries a
*monoid* structure rather than just a set of states, and its Myhill–Nerode theorem reads
`L.IsRegular ↔ Finite L.syntacticMonoid`.

## Main definitions

* `Language.syntacticCon L : Con (FreeMonoid α)`: the syntactic congruence, the kernel of the
  transition action of `L.toDFA`.
* `Language.SyntacticEquiv L u v`: the two-sided context equivalence on words.
* `Language.syntacticMonoid L`: the quotient monoid `(syntacticCon L).Quotient`.
* `Language.toSyntacticMonoid L`: the projection `FreeMonoid α →* L.syntacticMonoid`.
* `Language.Recognises φ L`: `φ` recognises `L`, i.e. `L` is a union of `φ`-fibres.

## Main results

* `Language.syntacticCon_iff`: the syntactic congruence is exactly the two-sided context
  equivalence.
* `Language.SyntacticEquiv.mem_iff`: `L` is saturated by syntactic equivalence.
* `Language.ker_le_syntacticCon_of_recognises`: the syntactic congruence is the coarsest congruence
  recognising `L`, so every recognising hom factors through `toSyntacticMonoid` via `Con.lift`.
* `Language.isRegular_iff_finite_syntacticMonoid`: the Myhill–Nerode theorem in monoid form.
-/

noncomputable section

universe u

namespace Language

variable {α : Type u} {L : Language α}

/-- Evaluating the minimal DFA `L.toDFA` from a quotient state `s` along a word `w` lands on the
left quotient of `s` by `w`. -/
@[simp]
theorem evalFrom_toDFA (L : Language α) (s : Set.range L.leftQuotient) (w : List α) :
    (L.toDFA.evalFrom s w).val = s.val.leftQuotient w := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton x a ih =>
    rw [DFA.evalFrom_append_singleton, step_toDFA, ih, ← leftQuotient_append]

/-! ### The syntactic congruence and monoid -/

/-- The *syntactic congruence* of `L`, obtained as the kernel of the transition action of `L.toDFA`
(the transition monoid of the minimal DFA). -/
def syntacticCon (L : Language α) : Con (FreeMonoid α) := Con.ker L.toDFA.transitionHom

/-! ### Syntactic equivalence on words -/

/-- `u` and `v` are *syntactically equivalent* in `L`: no two-sided context distinguishes them. -/
def SyntacticEquiv (L : Language α) (u v : List α) : Prop :=
  ∀ x y : List α, x ++ u ++ y ∈ L ↔ x ++ v ++ y ∈ L

namespace SyntacticEquiv

variable {u v w : List α}

@[refl] protected theorem refl (u : List α) : SyntacticEquiv L u u := fun _ _ => Iff.rfl

@[symm] protected theorem symm (h : SyntacticEquiv L u v) : SyntacticEquiv L v u :=
  fun x y => (h x y).symm

@[trans] protected theorem trans (h₁ : SyntacticEquiv L u v) (h₂ : SyntacticEquiv L v w) :
    SyntacticEquiv L u w := fun x y => (h₁ x y).trans (h₂ x y)

/-- Syntactic equivalence is a two-sided congruence for concatenation. -/
protected theorem append {u₁ u₂ v₁ v₂ : List α} (h₁ : SyntacticEquiv L u₁ v₁)
    (h₂ : SyntacticEquiv L u₂ v₂) : SyntacticEquiv L (u₁ ++ u₂) (v₁ ++ v₂) := fun x y => by
  have e₁ := h₁ x (u₂ ++ y)
  have e₂ := h₂ (x ++ v₁) y
  simp only [List.append_assoc] at e₁ e₂ ⊢
  exact e₁.trans e₂

/-- Left concatenation by a fixed word preserves syntactic equivalence. -/
protected theorem append_left (w : List α) (h : SyntacticEquiv L u v) :
    SyntacticEquiv L (w ++ u) (w ++ v) := (SyntacticEquiv.refl w).append h

/-- Equivalent words have the same `leftQuotient`: the two-sided test specialised to `x = []`. -/
theorem leftQuotient_eq (h : SyntacticEquiv L u v) : L.leftQuotient u = L.leftQuotient v := by
  ext y; simpa using h [] y

/-- Syntactically equivalent words agree on membership of `L`. -/
theorem mem_iff (h : SyntacticEquiv L u v) : u ∈ L ↔ v ∈ L := by simpa using h [] []

end SyntacticEquiv

/-- The kernel of the transition monoid of the minimal DFA is exactly the two-sided syntactic
congruence: `u` and `v` are congruent iff they are interchangeable in every two-sided context. -/
theorem syntacticCon_iff (L : Language α) {u v : FreeMonoid α} :
    L.syntacticCon u v ↔ SyntacticEquiv L u v := by
  rw [syntacticCon, Con.ker_apply, DFA.transitionHom_eq_iff]
  -- `SyntacticEquiv L u v` is defeq to `∀ x y, x ++ u.toList ++ y ∈ L ↔ x ++ v.toList ++ y ∈ L`
  -- (since `u.toList = u` for `FreeMonoid`); make the `.toList` form explicit for `mem_leftQuotient`.
  show _ ↔ ∀ x y : List α, x ++ u.toList ++ y ∈ L ↔ x ++ v.toList ++ y ∈ L
  constructor
  · intro h x y
    have h' := congrArg Subtype.val (h ⟨L.leftQuotient x, ⟨x, rfl⟩⟩)
    rw [evalFrom_toDFA, evalFrom_toDFA, ← leftQuotient_append, ← leftQuotient_append] at h'
    rw [← mem_leftQuotient, ← mem_leftQuotient, h']
  · intro h s
    apply Subtype.ext
    obtain ⟨x, hx⟩ := s.2
    rw [evalFrom_toDFA, evalFrom_toDFA, ← hx, ← leftQuotient_append, ← leftQuotient_append]
    ext y
    rw [mem_leftQuotient, mem_leftQuotient]
    exact h x y

/-- The *syntactic monoid* of `L`: the quotient of `FreeMonoid α` by the syntactic congruence. -/
def syntacticMonoid (L : Language α) : Type u := (syntacticCon L).Quotient

instance : Monoid (syntacticMonoid L) := inferInstanceAs (Monoid (syntacticCon L).Quotient)

/-- The canonical projection sending each word to its syntactic class; the underlying `Con.mk'`. -/
def toSyntacticMonoid (L : Language α) : FreeMonoid α →* L.syntacticMonoid := (syntacticCon L).mk'

/-! ### Universal property -/

/-- `φ` *recognises* `L` when `L` is a union of `φ`-fibres, i.e. `L = φ ⁻¹' S` for some `S ⊆ M`. -/
def Recognises {M : Type*} [Monoid M] (φ : FreeMonoid α →* M) (L : Language α) : Prop :=
  ∃ S : Set M, L = φ ⁻¹' S

/-- An `L`-recognising hom's kernel lies below `syntacticCon L`, the coarsest such congruence. -/
theorem ker_le_syntacticCon_of_recognises {M : Type*} [Monoid M] {φ : FreeMonoid α →* M}
    (hrec : Recognises φ L) : Con.ker φ ≤ syntacticCon L := by
  intro u v huv
  rw [show syntacticCon L u v ↔ SyntacticEquiv L u v from syntacticCon_iff L]
  obtain ⟨S, rfl⟩ := hrec
  change ∀ x y : FreeMonoid α, x * u * y ∈ φ ⁻¹' S ↔ x * v * y ∈ φ ⁻¹' S
  intro x y
  simp only [Set.mem_preimage, map_mul, Con.ker_apply.mp huv]

/-! ### Regularity implies a finite syntactic monoid -/

/-- A regular language has a finite syntactic monoid (forward Myhill–Nerode). -/
theorem finite_syntacticMonoid (h : L.IsRegular) : Finite L.syntacticMonoid := by
  have : Finite (Set.range L.leftQuotient) := h.finite_range_leftQuotient.to_subtype
  exact Finite.of_equiv _ (DFA.transitionMonoidEquiv L.toDFA).symm.toEquiv

/-! ### A finite syntactic monoid implies regularity -/

/-- A language with finite syntactic monoid is regular (reverse Myhill–Nerode). The left-quotient
map factors through the syntactic monoid, so a finite quotient forces finitely many left
quotients. -/
theorem isRegular_of_finite_syntacticMonoid (h : Finite L.syntacticMonoid) : L.IsRegular := by
  apply Language.IsRegular.of_finite_range_leftQuotient
  have factor : ∀ u v : FreeMonoid α, L.syntacticCon u v →
      L.leftQuotient u.toList = L.leftQuotient v.toList := by
    intro u v huv
    rw [syntacticCon_iff] at huv
    ext y; rw [mem_leftQuotient, mem_leftQuotient]; exact huv [] y
  set g : L.syntacticMonoid → Language α :=
    Quot.lift (fun w => L.leftQuotient w.toList) (fun u v huv => factor u v huv) with hg
  have hrange : Set.range L.leftQuotient ⊆ Set.range g := by
    rintro _ ⟨x, rfl⟩
    exact ⟨Quot.mk _ (FreeMonoid.ofList x), rfl⟩
  exact (Set.finite_range g).subset hrange

/-- Myhill–Nerode (syntactic-monoid form): `L` is regular iff `L.syntacticMonoid` is finite. -/
theorem isRegular_iff_finite_syntacticMonoid : L.IsRegular ↔ Finite L.syntacticMonoid :=
  ⟨finite_syntacticMonoid, isRegular_of_finite_syntacticMonoid⟩

end Language

end
