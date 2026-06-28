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

The syntactic congruence is defined directly as this two-sided context equivalence, and identified
with the kernel of the minimal DFA's transition action (the *transition monoid* of `L.toDFA`, see
`Linglib.Core.Computability.TransitionMonoid`) via `Language.syntacticCon_eq_ker_transitionHom`.
This is the two-sided refinement of `Mathlib.Computability.MyhillNerode`, which builds the one-sided
right-Nerode quotient (`Language.leftQuotient`) and proves regularity ↔ finitely many left
quotients. It carries a *monoid* structure rather than just a set of states, and its Myhill–Nerode
theorem reads `L.IsRegular ↔ Finite L.syntacticMonoid`.

## Main definitions

* `Language.syntacticCon L : Con (FreeMonoid α)`: the syntactic congruence (two-sided context
  equivalence).
* `Language.syntacticMonoid L`: the quotient monoid `(syntacticCon L).Quotient`.
* `Language.toSyntacticMonoid L`: the projection `FreeMonoid α →* L.syntacticMonoid`.
* `Language.syntacticClass L w`: the syntactic class of a word `w : List α`.
* `Language.Recognizes φ L`: `φ` recognizes `L`, i.e. `L` is a union of `φ`-fibres.

## Main results

* `Language.syntacticClass_eq_iff`: two words share a syntactic class iff no two-sided context
  distinguishes them, `∀ x y, x ++ u ++ y ∈ L ↔ x ++ v ++ y ∈ L`.
* `Language.syntacticCon_eq_ker_transitionHom`: the intrinsic congruence is the kernel of the
  transition action of `L.toDFA`.
* `Language.ker_le_syntacticCon_of_recognizes`: the syntactic congruence is the coarsest congruence
  recognizing `L`, so every recognizing hom factors through `toSyntacticMonoid` via `Con.lift`.
* `Language.isRegular_iff_finite_syntacticMonoid`: the Myhill–Nerode theorem in monoid form.
-/

namespace Language

variable {α : Type*} (L : Language α)

/-! ### The syntactic congruence and monoid -/

/-- The *syntactic congruence* of `L`: two words are congruent when no two-sided context
distinguishes them as `L`-members. -/
def syntacticCon : Con (FreeMonoid α) where
  r u v := ∀ x y : List α, x ++ u.toList ++ y ∈ L ↔ x ++ v.toList ++ y ∈ L
  iseqv :=
    ⟨fun _ _ _ => Iff.rfl, fun h x y => (h x y).symm, fun h h' x y => (h x y).trans (h' x y)⟩
  mul' {a b c d} hab hcd x y := by
    have h1 := hab x (c.toList ++ y)
    have h2 := hcd (x ++ b.toList) y
    simp only [FreeMonoid.toList_mul, ← List.append_assoc] at h1 h2 ⊢
    exact h1.trans h2

/-- The syntactic congruence is two-sided context equivalence — by definition. -/
theorem syntacticCon_iff {u v : FreeMonoid α} :
    L.syntacticCon u v ↔ ∀ x y, x ++ u.toList ++ y ∈ L ↔ x ++ v.toList ++ y ∈ L :=
  Iff.rfl

variable {L} in
/-- Words congruent under the syntactic congruence agree on membership of `L`: `L` is saturated by
`syntacticCon L` (take the empty two-sided context). -/
theorem mem_iff_of_syntacticCon {u v : FreeMonoid α} (h : L.syntacticCon u v) :
    u ∈ L ↔ v ∈ L := by
  have := h [] []
  simp only [List.nil_append, List.append_nil] at this
  exact this

/-- The *syntactic monoid* of `L`: the quotient of `FreeMonoid α` by the syntactic congruence. -/
def syntacticMonoid : Type _ := (syntacticCon L).Quotient

instance : Monoid (syntacticMonoid L) := inferInstanceAs (Monoid (syntacticCon L).Quotient)

/-- The canonical projection sending each word to its syntactic class; the underlying `Con.mk'`. -/
def toSyntacticMonoid : FreeMonoid α →* L.syntacticMonoid := (syntacticCon L).mk'

/-- The syntactic projection identifies two words iff they are syntactically congruent. -/
theorem toSyntacticMonoid_eq_iff {u v : FreeMonoid α} :
    L.toSyntacticMonoid u = L.toSyntacticMonoid v ↔ L.syntacticCon u v :=
  Con.eq _

/-! ### The syntactic class of a word -/

/-- The *syntactic class* of a word `w`: its image in the syntactic monoid (the literature's
`η(w)`, applied to a `List α` rather than a bundled `FreeMonoid α`). -/
def syntacticClass (w : List α) : L.syntacticMonoid := L.toSyntacticMonoid (FreeMonoid.ofList w)

@[simp] theorem syntacticClass_nil : L.syntacticClass [] = 1 := by simp [syntacticClass]

@[simp] theorem syntacticClass_append (u v : List α) :
    L.syntacticClass (u ++ v) = L.syntacticClass u * L.syntacticClass v := by
  simp [syntacticClass, FreeMonoid.ofList_append]

theorem syntacticClass_surjective : Function.Surjective L.syntacticClass := fun s => by
  obtain ⟨u, rfl⟩ := Quotient.exists_rep s
  exact ⟨u.toList, congrArg L.toSyntacticMonoid (FreeMonoid.ofList_toList u)⟩

variable {L} in
/-- Word-level form of `syntacticCon_iff`: two words share a syntactic class iff no two-sided
context distinguishes them as `L`-members. -/
theorem syntacticClass_eq_iff {u v : List α} : L.syntacticClass u = L.syntacticClass v ↔
    ∀ x y, x ++ u ++ y ∈ L ↔ x ++ v ++ y ∈ L := by
  simp only [syntacticClass, toSyntacticMonoid_eq_iff, syntacticCon_iff, FreeMonoid.toList_ofList]

variable {L} in
/-- `L` is saturated by syntactic class: equal class implies equal membership. -/
theorem mem_iff_of_syntacticClass_eq {u v : List α}
    (h : L.syntacticClass u = L.syntacticClass v) : u ∈ L ↔ v ∈ L := by
  simpa using syntacticClass_eq_iff.mp h [] []

variable {L} in
/-- **Reverse duality**: a syntactic-class equality in `L.reverse` is the same as the
reversed-word equality in `L`. The syntactic monoid of `L.reverse` is `L`'s, opposite. -/
theorem syntacticClass_reverse_eq_iff {u v : List α} :
    L.reverse.syntacticClass u = L.reverse.syntacticClass v ↔
      L.syntacticClass u.reverse = L.syntacticClass v.reverse := by
  rw [syntacticClass_eq_iff, syntacticClass_eq_iff]
  refine ⟨fun h x y => ?_, fun h x y => ?_⟩ <;>
    · have := h y.reverse x.reverse
      simpa only [Language.mem_reverse, List.reverse_append, List.reverse_reverse,
        List.append_assoc] using this

/-! ### Universal property -/

variable {L}

/-- `φ` *recognizes* `L` when `L` is a union of `φ`-fibres, i.e. `L = φ ⁻¹' S` for some
`S ⊆ M`. -/
def Recognizes {M : Type*} [Monoid M] (φ : FreeMonoid α →* M) (L : Language α) : Prop :=
  ∃ S : Set M, L = φ ⁻¹' S

/-- An `L`-recognizing hom's kernel lies below `syntacticCon L`, the coarsest such congruence. -/
theorem ker_le_syntacticCon_of_recognizes {M : Type*} [Monoid M] {φ : FreeMonoid α →* M}
    (hrec : Recognizes φ L) : Con.ker φ ≤ syntacticCon L := by
  intro u v huv
  rw [syntacticCon_iff]
  obtain ⟨S, rfl⟩ := hrec
  change ∀ x y : FreeMonoid α, x * u * y ∈ φ ⁻¹' S ↔ x * v * y ∈ φ ⁻¹' S
  intro x y
  simp only [Set.mem_preimage, map_mul, Con.ker_apply.mp huv]

/-- Conversely, any hom whose kernel refines `syntacticCon L` recognizes `L`
(witness `S = φ '' L`). -/
theorem recognizes_of_ker_le_syntacticCon {M : Type*} [Monoid M] {φ : FreeMonoid α →* M}
    (h : Con.ker φ ≤ syntacticCon L) : Recognizes φ L := by
  refine ⟨φ '' L, Set.ext fun w => ⟨fun hw => ⟨w, hw, rfl⟩, ?_⟩⟩
  rintro ⟨u, hu, hφ⟩
  exact (mem_iff_of_syntacticCon (h (Con.ker_apply.mpr hφ))).mp hu

/-- **Universal property of the syntactic monoid**: a hom recognizes `L` exactly when its
kernel refines the syntactic congruence — `syntacticCon L` is the coarsest `L`-recognizing
congruence, so every recognizer factors through `toSyntacticMonoid`. -/
theorem recognizes_iff_ker_le_syntacticCon {M : Type*} [Monoid M] {φ : FreeMonoid α →* M} :
    Recognizes φ L ↔ Con.ker φ ≤ syntacticCon L :=
  ⟨ker_le_syntacticCon_of_recognizes, recognizes_of_ker_le_syntacticCon⟩

/-- The syntactic morphism is itself an `L`-recognizer (the canonical one). -/
theorem recognizes_toSyntacticMonoid : Recognizes L.toSyntacticMonoid L := by
  apply recognizes_of_ker_le_syntacticCon
  intro u v h
  exact (Con.eq _).mp (Con.ker_apply.mp h)

/-! ### Connection to the minimal DFA -/

/-- Evaluating the minimal DFA `L.toDFA` from a quotient state `s` along `w` lands on the left
quotient of `s` by `w`. -/
theorem evalFrom_toDFA (s : Set.range L.leftQuotient) (w : List α) :
    (L.toDFA.evalFrom s w).val = s.val.leftQuotient w := by
  induction w using List.reverseRecOn <;>
    simp_all [DFA.evalFrom_append_singleton, step_toDFA, leftQuotient_append]

/-- The intrinsic syntactic congruence is the kernel of the minimal DFA's transition action — the
two-sided context definition agrees with the transition-monoid quotient. -/
theorem syntacticCon_eq_ker_transitionHom : L.syntacticCon = Con.ker L.toDFA.transitionHom := by
  ext u v
  rw [syntacticCon_iff, Con.ker_apply, DFA.transitionHom_eq_iff]
  constructor
  · intro h s
    apply Subtype.ext
    obtain ⟨x, hx⟩ := s.2
    rw [evalFrom_toDFA, evalFrom_toDFA, ← hx, ← leftQuotient_append, ← leftQuotient_append]
    ext y
    rw [mem_leftQuotient, mem_leftQuotient]
    exact h x y
  · intro h x y
    have h' := congrArg Subtype.val (h ⟨L.leftQuotient x, ⟨x, rfl⟩⟩)
    rw [evalFrom_toDFA, evalFrom_toDFA, ← leftQuotient_append, ← leftQuotient_append] at h'
    rw [← mem_leftQuotient, ← mem_leftQuotient, h']

/-! ### Regularity implies a finite syntactic monoid -/

/-- A regular language has a finite syntactic monoid (forward Myhill–Nerode). -/
theorem finite_syntacticMonoid (h : L.IsRegular) : Finite L.syntacticMonoid := by
  have : Finite (Set.range L.leftQuotient) := h.finite_range_leftQuotient.to_subtype
  show Finite (syntacticCon L).Quotient
  rw [syntacticCon_eq_ker_transitionHom]
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
    ext y; rw [mem_leftQuotient, mem_leftQuotient]; exact huv [] y
  let g : L.syntacticMonoid → Language α := Quot.lift (fun w => L.leftQuotient w.toList) factor
  refine (Set.finite_range g).subset ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨Quot.mk _ (FreeMonoid.ofList x), rfl⟩

/-- Myhill–Nerode (syntactic-monoid form): `L` is regular iff `L.syntacticMonoid` is finite. -/
theorem isRegular_iff_finite_syntacticMonoid : L.IsRegular ↔ Finite L.syntacticMonoid :=
  ⟨finite_syntacticMonoid, isRegular_of_finite_syntacticMonoid⟩

/-! ### Complement- and intersection-invariance

Generic syntactic-monoid facts about boolean combinations, used by any class defined through the
syntactic monoid (e.g. `Language.IsStarFree`, and `Monoid.Pseudovariety.langs` in general). -/

/-- The syntactic congruence is complement-invariant: a two-sided context distinguishes `u` from
`v` for `L` exactly when it does for `Lᶜ`. -/
theorem syntacticCon_compl (L : Language α) : Lᶜ.syntacticCon = L.syntacticCon :=
  Con.ext fun u v => by
    rw [syntacticCon_iff, syntacticCon_iff]
    exact forall_congr' fun _ => forall_congr' fun _ => not_iff_not

/-- The syntactic monoid is complement-invariant. -/
theorem syntacticMonoid_compl (L : Language α) : Lᶜ.syntacticMonoid = L.syntacticMonoid := by
  unfold syntacticMonoid; rw [syntacticCon_compl]

/-- The meet of the two syntactic congruences refines that of the intersection: if no `L`-context
and no `M`-context distinguishes `u` from `v`, then no `(L ⊓ M)`-context does either. -/
theorem inf_syntacticCon_le_syntacticCon_inf (L M : Language α) :
    L.syntacticCon ⊓ M.syntacticCon ≤ (L ⊓ M).syntacticCon := by
  rw [Con.le_def]
  intro u v huv x y
  rw [Con.inf_iff_and, syntacticCon_iff, syntacticCon_iff] at huv
  exact and_congr (huv.1 x y) (huv.2 x y)

/-- The kernel of the pairing of the two syntactic morphisms is exactly the meet of the two
syntactic congruences (a word's class in the product is the pair of its classes). -/
theorem ker_prod_toSyntacticMonoid (L M : Language α) :
    Con.ker (L.toSyntacticMonoid.prod M.toSyntacticMonoid) =
      L.syntacticCon ⊓ M.syntacticCon :=
  Con.ext fun u v => by
    rw [Con.ker_apply, MonoidHom.prod_apply, MonoidHom.prod_apply, Prod.ext_iff,
      toSyntacticMonoid_eq_iff, toSyntacticMonoid_eq_iff, Con.inf_iff_and]

end Language
