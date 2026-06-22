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
* `Language.syntacticMonoid L`: the quotient monoid `(syntacticCon L).Quotient`.
* `Language.toSyntacticMonoid L`: the projection `FreeMonoid α →* L.syntacticMonoid`.
* `Language.Recognises φ L`: `φ` recognises `L`, i.e. `L` is a union of `φ`-fibres.

## Main results

* `Language.syntacticCon_iff`: the syntactic congruence is exactly the two-sided context
  equivalence `∀ x y, x ++ u ++ y ∈ L ↔ x ++ v ++ y ∈ L`.
* `Language.mem_iff_of_syntacticCon`: `L` is saturated by the syntactic congruence.
* `Language.ker_le_syntacticCon_of_recognises`: the syntactic congruence is the coarsest congruence
  recognising `L`, so every recognising hom factors through `toSyntacticMonoid` via `Con.lift`.
* `Language.isRegular_iff_finite_syntacticMonoid`: the Myhill–Nerode theorem in monoid form.
-/

noncomputable section

universe u

namespace Language

variable {α : Type u} (L : Language α)

/-! ### The syntactic congruence and monoid -/

/-- The *syntactic congruence* of `L`, obtained as the kernel of the transition action of `L.toDFA`
(the transition monoid of the minimal DFA). -/
def syntacticCon : Con (FreeMonoid α) := Con.ker L.toDFA.transitionHom

/-- Evaluating the minimal DFA `L.toDFA` from a quotient state `s` along a word `w` lands on the
left quotient of `s` by `w`. -/
@[simp]
theorem evalFrom_toDFA (s : Set.range L.leftQuotient) (w : List α) :
    (L.toDFA.evalFrom s w).val = s.val.leftQuotient w := by
  induction w using List.reverseRecOn <;>
    simp_all [DFA.evalFrom_append_singleton, step_toDFA, leftQuotient_append]

/-- The kernel of the transition monoid of the minimal DFA is exactly the two-sided context
equivalence: `u` and `v` are congruent iff they are interchangeable in every two-sided context. -/
theorem syntacticCon_iff {u v : FreeMonoid α} :
    L.syntacticCon u v ↔ ∀ x y : List α, x ++ u.toList ++ y ∈ L ↔ x ++ v.toList ++ y ∈ L := by
  rw [syntacticCon, Con.ker_apply, DFA.transitionHom_eq_iff]
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

variable {L} in
/-- Words congruent under the syntactic congruence agree on membership of `L`: `L` is saturated by
`syntacticCon L` (take the empty two-sided context). -/
theorem mem_iff_of_syntacticCon {u v : FreeMonoid α} (h : L.syntacticCon u v) : u ∈ L ↔ v ∈ L := by
  have := (syntacticCon_iff L).mp h [] []
  simp only [List.nil_append, List.append_nil] at this
  exact this

/-- The *syntactic monoid* of `L`: the quotient of `FreeMonoid α` by the syntactic congruence. -/
def syntacticMonoid : Type u := (syntacticCon L).Quotient

instance : Monoid (syntacticMonoid L) := inferInstanceAs (Monoid (syntacticCon L).Quotient)

/-- The canonical projection sending each word to its syntactic class; the underlying `Con.mk'`. -/
def toSyntacticMonoid : FreeMonoid α →* L.syntacticMonoid := (syntacticCon L).mk'

/-! ### Universal property -/

variable {L}

/-- `φ` *recognises* `L` when `L` is a union of `φ`-fibres, i.e. `L = φ ⁻¹' S` for some `S ⊆ M`. -/
def Recognises {M : Type*} [Monoid M] (φ : FreeMonoid α →* M) (L : Language α) : Prop :=
  ∃ S : Set M, L = φ ⁻¹' S

/-- An `L`-recognising hom's kernel lies below `syntacticCon L`, the coarsest such congruence. -/
theorem ker_le_syntacticCon_of_recognises {M : Type*} [Monoid M] {φ : FreeMonoid α →* M}
    (hrec : Recognises φ L) : Con.ker φ ≤ syntacticCon L := by
  intro u v huv
  rw [syntacticCon_iff]
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
  let g : L.syntacticMonoid → Language α := Quot.lift (fun w => L.leftQuotient w.toList) factor
  refine (Set.finite_range g).subset ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨Quot.mk _ (FreeMonoid.ofList x), rfl⟩

/-- Myhill–Nerode (syntactic-monoid form): `L` is regular iff `L.syntacticMonoid` is finite. -/
theorem isRegular_iff_finite_syntacticMonoid : L.IsRegular ↔ Finite L.syntacticMonoid :=
  ⟨finite_syntacticMonoid, isRegular_of_finite_syntacticMonoid⟩

end Language

end
