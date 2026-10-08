module

public import Linglib.Core.Relation.SetRel

/-!
# Modal operators and frame conditions

This file defines the relational necessity and possibility of Kripke semantics over an
accessibility relation `R : SetRel W' W`, as operators on propositions `W → Prop`: `□[R] p w`
holds when `p` holds at every `R`-successor of `w`, `◇[R] p w` when it holds at some. They are
mathlib's `SetRel.core` and `SetRel.preimage` read on predicates (`box_iff_mem_core`,
`diamond_iff_mem_preimage`), in the way `Filter.Eventually` reads a filter on predicates, so
propositions stated as sets use the mathlib operators directly. Of the frame conditions of
correspondence theory, reflexivity, symmetry and transitivity are mathlib's `SetRel.IsRefl`,
`SetRel.IsSymm` and `SetRel.IsTrans`; this file adds seriality and the Euclidean property and
proves the axioms K, T, D, B, 4, 5 and Alt₁ over their frames, each axiom defining its frame
condition. Along a composite relation necessity nests in necessity (`box_comp`).

## Main definitions

* `ModalLogic.Box`, `ModalLogic.Diamond`, with notation `□[R]` and `◇[R]`.
* `ModalLogic.IsSerial`, `ModalLogic.IsEuclidean`: the frame conditions of D and 5.

## References

* [kripke-1963] — relational semantics
* [blackburn-derijke-venema-2001] — Chapter 3, frame definability
-/

@[expose] public section

namespace ModalLogic

open SetRel

/-! ### Box and diamond -/

section Operators

variable {W W' : Type*} (R : SetRel W' W) (p : W → Prop) (w : W')

/-- Necessity along `R`: `p` holds at every `R`-successor of `w`. -/
def Box : Prop := ∀ v, w ~[R] v → p v

/-- Possibility along `R`: `p` holds at some `R`-successor of `w`. -/
def Diamond : Prop := ∃ v, w ~[R] v ∧ p v

@[inherit_doc] scoped notation:max "□[" R "]" => Box R
@[inherit_doc] scoped notation:max "◇[" R "]" => Diamond R

variable {R p w}

/-- Necessity on predicates is the mathlib core on sets. -/
theorem box_iff_mem_core : □[R] p w ↔ w ∈ R.core {v | p v} := .rfl

/-- Possibility on predicates is the mathlib preimage on sets. -/
theorem diamond_iff_mem_preimage : ◇[R] p w ↔ w ∈ R.preimage {v | p v} :=
  exists_congr fun _ ↦ and_comm

@[simp] theorem not_box : ¬ □[R] p w ↔ ◇[R] (fun v ↦ ¬ p v) w := by
  simp [Box, Diamond, not_forall]

@[simp] theorem not_diamond : ¬ ◇[R] p w ↔ □[R] (fun v ↦ ¬ p v) w := by
  simp [Box, Diamond, not_and]

variable (R) in
/-- Necessity distributes over conjunction ([hintikka-1962]'s
`a believes A and B ↔ a believes A and a believes B`). -/
theorem box_and (q : W → Prop) : □[R] (fun v ↦ p v ∧ q v) w ↔ □[R] p w ∧ □[R] q w := by
  simp only [Box, imp_and, forall_and]

variable (R) in
/-- Necessity along a union of relations is necessity along each. -/
theorem box_iUnion {ι : Sort*} (R : ι → SetRel W' W) : □[⋃ i, R i] p w ↔ ∀ i, □[R i] p w := by
  simp only [Box, Set.mem_iUnion, forall_exists_index]
  exact forall_comm

/-- Necessity depends only on the worlds accessed: two worlds accessing the same worlds
carry the same box. -/
theorem box_congr_left {w'' : W'} (h : ∀ v, w ~[R] v ↔ w'' ~[R] v) : □[R] p w ↔ □[R] p w'' :=
  forall_congr' fun v ↦ imp_congr_left (h v)

end Operators

variable {W : Type*} (R : SetRel W W)

/-- Necessity along a composite relation is necessity nested in necessity. -/
theorem box_comp (S : SetRel W W) (p : W → Prop) : □[R ○ S] p = □[R] (□[S] p) :=
  funext fun _ ↦ propext ⟨fun h _ hv _ hu ↦ h _ ⟨_, hv, hu⟩, fun h _ ⟨_, hv, hu⟩ ↦ h _ hv _ hu⟩

/-- Possibility along a composite relation is possibility nested in possibility. -/
theorem diamond_comp (S : SetRel W W) (p : W → Prop) : ◇[R ○ S] p = ◇[R] (◇[S] p) :=
  funext fun _ ↦ propext ⟨fun ⟨u, ⟨v, hv, hu⟩, hp⟩ ↦ ⟨v, hv, u, hu, hp⟩,
    fun ⟨v, hv, u, hu, hp⟩ ↦ ⟨u, ⟨v, hv, hu⟩, hp⟩⟩

/-! ### Frame conditions -/

/-- `R` is **serial** if every world accesses at least one world. -/
class IsSerial : Prop where
  serial : ∀ w, ∃ v, w ~[R] v

/-- `R` is **Euclidean** if any two `R`-successors of a world access each other. -/
class IsEuclidean : Prop where
  eucl : ∀ w v u, w ~[R] v → w ~[R] u → v ~[R] u

variable {R}

instance : IsEuclidean (.univ : SetRel W W) := ⟨fun _ _ _ _ _ ↦ trivial⟩

/-- Reflexive relations are serial. -/
instance [R.IsRefl] : IsSerial R := ⟨fun w ↦ ⟨w, R.rfl⟩⟩

/-- A composite of serial relations is serial. -/
instance {S : SetRel W W} [IsSerial R] [IsSerial S] : IsSerial (R ○ S) where
  serial w := let ⟨v, hv⟩ := IsSerial.serial (R := R) w; let ⟨u, hu⟩ := IsSerial.serial (R := S) v
    ⟨u, v, hv, hu⟩

/-- Reflexive and Euclidean implies symmetric. -/
instance [R.IsRefl] [IsEuclidean R] : R.IsSymm where
  symm w v h := IsEuclidean.eucl w v w h R.rfl

/-- Reflexive and Euclidean implies transitive. -/
instance [R.IsRefl] [IsEuclidean R] : R.IsTrans where
  trans w v u hwv hvu := IsEuclidean.eucl v w u (IsEuclidean.eucl w v w hwv R.rfl) hvu

/-- Symmetric and transitive implies Euclidean. -/
instance [R.IsSymm] [R.IsTrans] : IsEuclidean R where
  eucl _ _ _ hwv hwu := R.trans (R.symm hwv) hwu

/-! ### Axiom correspondence -/

variable {p q : W → Prop} {w : W}

/-- **K**: `□(p → q) → □p → □q`, over any relation. -/
theorem box_K (hpq : □[R] (fun v ↦ p v → q v) w) (hp : □[R] p w) : □[R] q w :=
  fun v hwv ↦ hpq v hwv (hp v hwv)

/-- **T**: over a reflexive relation, `□p → p`. -/
theorem box_T [R.IsRefl] (h : □[R] p w) : p w := h w R.rfl

/-- **D**: over a serial relation, `□p → ◇p`. -/
theorem box_D [IsSerial R] (h : □[R] p w) : ◇[R] p w :=
  let ⟨v, hwv⟩ := IsSerial.serial (R := R) w; ⟨v, hwv, h v hwv⟩

/-- Necessity along `R` gives possibility along a relation sharing an `R`-successor of the
world: `box_D` is the case `S = R`. -/
theorem diamond_of_box {S : SetRel W W} (h : ◇[R] (w ~[S] ·) w) (hp : □[R] p w) : ◇[S] p w :=
  let ⟨v, hR, hS⟩ := h; ⟨v, hS, hp v hR⟩

/-- **B**: over a symmetric relation, `p → □◇p`. -/
theorem box_B [R.IsSymm] (h : p w) : □[R] (◇[R] p) w := fun _ hwv ↦ ⟨w, R.symm hwv, h⟩

/-- **4**: over a transitive relation, `□p → □□p`. -/
theorem box_four [R.IsTrans] (h : □[R] p w) : □[R] (□[R] p) w :=
  fun _ hwv u hvu ↦ h u (R.trans hwv hvu)

/-- **5**: over a Euclidean relation, `◇p → □◇p`. -/
theorem box_five [IsEuclidean R] (h : ◇[R] p w) : □[R] (◇[R] p) w :=
  let ⟨u, hwu, hpu⟩ := h
  fun v hwv ↦ ⟨u, IsEuclidean.eucl w v u hwv hwu, hpu⟩

/-- Over a Euclidean relation, `◇□p → □p`: what is possibly necessary is necessary. -/
theorem box_of_diamond_box [IsEuclidean R] (h : ◇[R] (□[R] p) w) : □[R] p w :=
  let ⟨u, hwu, hpu⟩ := h
  fun v hwv ↦ hpu v (IsEuclidean.eucl w u v hwu hwv)

/-- Over a serial transitive relation, `□p → ◇□p`. -/
theorem diamond_box_of_box [IsSerial R] [R.IsTrans] (h : □[R] p w) : ◇[R] (□[R] p) w :=
  box_D (box_four h)

/-! ### Frame definability

Each axiom, read as an inequality between operators on `W → Prop`, characterizes its frame
condition. -/

/-- **T** defines reflexivity. -/
theorem box_T_iff : Box R ≤ id ↔ R.IsRefl where
  mp h := ⟨fun w ↦ h (w ~[R] ·) w fun _ hv ↦ hv⟩
  mpr _ _ _ := box_T

/-- **T** for the diamond defines reflexivity: what holds is possible. -/
theorem diamond_T_iff : id ≤ Diamond R ↔ R.IsRefl where
  mp h := ⟨fun w ↦ match h (· = w) w rfl with | ⟨_, hv, rfl⟩ => hv⟩
  mpr hR _ w hp := ⟨w, hR.refl w, hp⟩

/-- **D** defines seriality. -/
theorem box_D_iff : Box R ≤ Diamond R ↔ IsSerial R where
  mp h := ⟨fun w ↦ let ⟨v, hv, _⟩ := h (fun _ ↦ True) w fun _ _ ↦ trivial; ⟨v, hv⟩⟩
  mpr _ _ _ := box_D

/-- **B** defines symmetry. -/
theorem box_B_iff : id ≤ Box R ∘ Diamond R ↔ R.IsSymm where
  mp h := ⟨fun w v hwv ↦ match h (· = w) w rfl v hwv with | ⟨_, hvw, rfl⟩ => hvw⟩
  mpr _ _ _ := box_B

/-- **4** defines transitivity. -/
theorem box_four_iff : Box R ≤ Box R ∘ Box R ↔ R.IsTrans where
  mp h := ⟨fun w _ _ hwv hvu ↦ h (w ~[R] ·) w (fun _ hv ↦ hv) _ hwv _ hvu⟩
  mpr _ _ _ := box_four

/-- **5** defines the Euclidean property. -/
theorem box_five_iff : Diamond R ≤ Box R ∘ Diamond R ↔ IsEuclidean R where
  mp h := ⟨fun w v u hwv hwu ↦ match h (· = u) w ⟨u, hwu, rfl⟩ v hwv with | ⟨_, hvu, rfl⟩ => hvu⟩
  mpr _ _ _ := box_five

/-- **Alt₁** at a world: `◇p → □p` for every `p` at `w` iff `w` sees at most one world. -/
theorem diamond_le_box_at_iff :
    (∀ p : W → Prop, ◇[R] p w → □[R] p w) ↔ ∀ ⦃v⦄, w ~[R] v → ∀ ⦃u⦄, w ~[R] u → v = u where
  mp h v hv _ hu := (h (· = v) ⟨v, hv, rfl⟩ _ hu).symm
  mpr h _ := fun ⟨_, hu, hpu⟩ _ hv ↦ h hu hv ▸ hpu

/-- **Alt₁** defines partial functionality. -/
theorem diamond_le_box_iff :
    Diamond R ≤ Box R ↔ ∀ w ⦃v⦄, w ~[R] v → ∀ ⦃u⦄, w ~[R] u → v = u :=
  ⟨fun h _ ↦ diamond_le_box_at_iff.1 fun p ↦ h p _,
    fun h p _ ↦ diamond_le_box_at_iff.2 (h _) p⟩

/-- The excluded middle for every `p` at `w`, `□p ∨ □¬p`, holds iff `w` sees at most one
world. -/
theorem box_or_box_not_at_iff :
    (∀ p : W → Prop, □[R] p w ∨ □[R] (fun v ↦ ¬ p v) w) ↔
      ∀ ⦃v⦄, w ~[R] v → ∀ ⦃u⦄, w ~[R] u → v = u := by
  rw [← diamond_le_box_at_iff]
  refine forall_congr' fun p ↦ ?_
  rw [← not_diamond, or_comm, or_iff_not_imp_left, not_not]

/-- The neg-raising inference for every `p` at `w`, `¬□p → □¬p`, holds iff `w` sees at most
one world. -/
theorem box_not_of_not_box_at_iff :
    (∀ p : W → Prop, ¬ □[R] p w → □[R] (fun v ↦ ¬ p v) w) ↔
      ∀ ⦃v⦄, w ~[R] v → ∀ ⦃u⦄, w ~[R] u → v = u := by
  rw [← box_or_box_not_at_iff]
  exact forall_congr' fun p ↦ (or_iff_not_imp_left).symm

end ModalLogic
