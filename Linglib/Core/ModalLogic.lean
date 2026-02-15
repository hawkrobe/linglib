import Mathlib.Data.Finset.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Linglib.Core.Proposition

/-!
# Modal Logic

Kripke semantics for normal modal logics. Formalizes frames, frame conditions,
correspondence theorems, and the lattice of normal modal logics.

Linguistic interpretations belong in `Theories/Montague/Modal/`.

## References
* Kripke (1963), Semantical Considerations on Modal Logic
* Chellas (1980), Modal Logic: An Introduction
* Blackburn, de Rijke, Venema (2001), Modal Logic
-/

namespace Core.ModalLogic

open Core.Proposition (FiniteWorlds)

/-! ## Operators -/

/-- Modal force: necessity (□) or possibility (◇). -/
inductive ModalForce where
  | necessity
  | possibility
  deriving DecidableEq, BEq, Repr, Inhabited

instance : LawfulBEq ModalForce where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

instance : ToString ModalForce where
  toString | .necessity => "□" | .possibility => "◇"

def ModalForce.dual : ModalForce → ModalForce
  | .necessity => .possibility
  | .possibility => .necessity

@[simp] theorem ModalForce.dual_dual (f : ModalForce) : f.dual.dual = f := by cases f <;> rfl

/-! ## Frames and Accessibility -/

abbrev AccessRel (W : Type*) := W → W → Bool

/-- Agent-indexed accessibility relation: each agent has their own AccessRel. -/
abbrev AgentAccessRel (W E : Type*) := E → AccessRel W

/-- Kripke evaluation of modal formulas. -/
def kripkeEval {W : Type*} [FiniteWorlds W] (R : AccessRel W) (force : ModalForce)
    (p : BProp W) (w : W) : Bool :=
  let accessible := FiniteWorlds.worlds.filter (R w)
  match force with
  | .necessity => accessible.all p
  | .possibility => accessible.any p

theorem duality {W : Type*} [FiniteWorlds W] (R : AccessRel W) (p : BProp W) (w : W) :
    kripkeEval R .necessity p w = !kripkeEval R .possibility (fun v => !p v) w := by
  unfold kripkeEval
  induction FiniteWorlds.worlds.filter (R w) with
  | nil => rfl
  | cons x xs ih => simp only [List.all_cons, List.any_cons, Bool.not_or, Bool.not_not]
                    cases p x <;> simp [ih]

/-! ## Frame Conditions -/

def Refl {W : Type*} (R : AccessRel W) : Prop := ∀ w : W, R w w = true
def Serial {W : Type*} (R : AccessRel W) : Prop := ∀ w : W, ∃ v : W, R w v = true
def Trans {W : Type*} (R : AccessRel W) : Prop := ∀ w v u : W, R w v = true → R v u = true → R w u = true
def Symm {W : Type*} (R : AccessRel W) : Prop := ∀ w v : W, R w v = true → R v w = true
def Eucl {W : Type*} (R : AccessRel W) : Prop := ∀ w v u : W, R w v = true → R w u = true → R v u = true

theorem refl_serial {W : Type*} {R : AccessRel W} (h : Refl R) : Serial R :=
  fun w => ⟨w, h w⟩

theorem refl_eucl_symm {W : Type*} {R : AccessRel W} (hR : Refl R) (hE : Eucl R) : Symm R :=
  fun w v hwv => hE w v w hwv (hR w)

theorem refl_eucl_trans {W : Type*} {R : AccessRel W} (hR : Refl R) (hE : Eucl R) : Trans R := by
  intro w v u hwv hvu
  have hvw := refl_eucl_symm hR hE w v hwv
  exact hE v w u hvw hvu

theorem symm_trans_eucl {W : Type*} {R : AccessRel W} (hS : Symm R) (hT : Trans R) : Eucl R := by
  intro w v u hwv hwu
  exact hT v w u (hS w v hwv) hwu

/-! ## Frame Correspondence -/

/-- T axiom: □p → p -/
theorem T_of_refl {W : Type*} [FiniteWorlds W] {R : AccessRel W}
    (hR : Refl R) (p : BProp W) (w : W)
    (h : kripkeEval R .necessity p w = true) : p w = true := by
  unfold kripkeEval at h
  have hW : w ∈ FiniteWorlds.worlds.filter (R w) := by
    simp only [List.mem_filter]; exact ⟨FiniteWorlds.complete w, hR w⟩
  exact List.all_eq_true.mp h w hW

/-- D axiom: □p → ◇p -/
theorem D_of_serial {W : Type*} [FiniteWorlds W] {R : AccessRel W}
    (hS : Serial R) (p : BProp W) (w : W)
    (h : kripkeEval R .necessity p w = true) :
    kripkeEval R .possibility p w = true := by
  unfold kripkeEval at h ⊢
  obtain ⟨v, hRwv⟩ := hS w
  have hV : v ∈ FiniteWorlds.worlds.filter (R w) := by
    simp only [List.mem_filter]; exact ⟨FiniteWorlds.complete v, hRwv⟩
  exact List.any_eq_true.mpr ⟨v, hV, List.all_eq_true.mp h v hV⟩

/-- K axiom: □(p → q) → □p → □q -/
theorem K_axiom {W : Type*} [FiniteWorlds W] (R : AccessRel W) (p q : BProp W) (w : W)
    (hImp : kripkeEval R .necessity (fun v => !p v || q v) w = true)
    (hP : kripkeEval R .necessity p w = true) :
    kripkeEval R .necessity q w = true := by
  unfold kripkeEval at *
  apply List.all_eq_true.mpr; intro v hV
  have := List.all_eq_true.mp hImp v hV
  have := List.all_eq_true.mp hP v hV
  cases hp : p v <;> simp_all

/-- 4 axiom: □p → □□p -/
theorem four_of_trans {W : Type*} [FiniteWorlds W] {R : AccessRel W}
    (hT : Trans R) (p : BProp W) (w : W)
    (h : kripkeEval R .necessity p w = true) :
    kripkeEval R .necessity (kripkeEval R .necessity p) w = true := by
  unfold kripkeEval at h ⊢
  apply List.all_eq_true.mpr; intro v hV
  apply List.all_eq_true.mpr; intro u hU
  simp only [List.mem_filter] at hV hU
  have hWU : u ∈ FiniteWorlds.worlds.filter (R w) := by
    simp only [List.mem_filter]; exact ⟨hU.1, hT w v u hV.2 hU.2⟩
  exact List.all_eq_true.mp h u hWU

/-- B axiom: p → □◇p -/
theorem B_of_symm {W : Type*} [FiniteWorlds W] {R : AccessRel W}
    (hS : Symm R) (p : BProp W) (w : W) (hP : p w = true) :
    kripkeEval R .necessity (kripkeEval R .possibility p) w = true := by
  unfold kripkeEval
  apply List.all_eq_true.mpr; intro v hV
  apply List.any_eq_true.mpr
  simp only [List.mem_filter] at hV
  have hW : w ∈ FiniteWorlds.worlds.filter (R v) := by
    simp only [List.mem_filter]; exact ⟨FiniteWorlds.complete w, hS w v hV.2⟩
  exact ⟨w, hW, hP⟩

/-- 5 axiom: ◇p → □◇p -/
theorem five_of_eucl {W : Type*} [FiniteWorlds W] {R : AccessRel W}
    (hE : Eucl R) (p : BProp W) (w : W)
    (h : kripkeEval R .possibility p w = true) :
    kripkeEval R .necessity (kripkeEval R .possibility p) w = true := by
  unfold kripkeEval at h ⊢
  obtain ⟨u, hU, hPu⟩ := List.any_eq_true.mp h
  apply List.all_eq_true.mpr; intro v hV
  apply List.any_eq_true.mpr
  simp only [List.mem_filter] at hU hV
  have hVU : u ∈ FiniteWorlds.worlds.filter (R v) := by
    simp only [List.mem_filter]; exact ⟨hU.1, hE w v u hV.2 hU.2⟩
  exact ⟨u, hVU, hPu⟩

/-! ## Lattice of Normal Modal Logics -/

/-- Axiom schemas addable to K. -/
inductive Axiom where
  | M     -- □p → p (T)
  | D     -- □p → ◇p
  | B     -- p → □◇p
  | four  -- □p → □□p
  | five  -- ◇p → □◇p
  deriving DecidableEq, BEq, Repr, Inhabited, Hashable

instance : ToString Axiom where
  toString | .M => "M" | .D => "D" | .B => "B" | .four => "4" | .five => "5"

/-- A normal modal logic is K plus axiom schemas. -/
structure Logic where
  axioms : Finset Axiom
  deriving DecidableEq

namespace Logic

def K : Logic := ⟨∅⟩
def T : Logic := ⟨{.M}⟩
def D : Logic := ⟨{.D}⟩
def KB : Logic := ⟨{.B}⟩
def K4 : Logic := ⟨{.four}⟩
def K5 : Logic := ⟨{.five}⟩
def S4 : Logic := ⟨{.M, .four}⟩
def S5 : Logic := ⟨{.M, .five}⟩
def KTB : Logic := ⟨{.M, .B}⟩
def KD45 : Logic := ⟨{.D, .four, .five}⟩
def K45 : Logic := ⟨{.four, .five}⟩

/-- L₁ ≤ L₂ means L₁ is weaker (fewer axioms). -/
instance : LE Logic := ⟨λ L₁ L₂ => L₁.axioms ⊆ L₂.axioms⟩

instance : PartialOrder Logic where
  le_refl := λ _ => Finset.Subset.refl _
  le_trans := λ _ _ _ h₁ h₂ => Finset.Subset.trans h₁ h₂
  le_antisymm := λ _ _ h₁ h₂ => by
    cases_type* Logic
    simp only [Logic.mk.injEq]
    exact Finset.Subset.antisymm h₁ h₂

instance : Lattice Logic where
  sup := λ L₁ L₂ => ⟨L₁.axioms ∪ L₂.axioms⟩
  inf := λ L₁ L₂ => ⟨L₁.axioms ∩ L₂.axioms⟩
  le_sup_left := λ _ _ => Finset.subset_union_left
  le_sup_right := λ _ _ => Finset.subset_union_right
  sup_le := λ _ _ _ h₁ h₂ => Finset.union_subset h₁ h₂
  inf_le_left := λ _ _ => Finset.inter_subset_left
  inf_le_right := λ _ _ => Finset.inter_subset_right
  le_inf := λ _ _ _ h₁ h₂ => Finset.subset_inter h₁ h₂

def top : Logic := ⟨{.M, .D, .B, .four, .five}⟩

instance : OrderBot Logic where
  bot := K
  bot_le := λ _ => Finset.empty_subset _

instance : OrderTop Logic where
  top := top
  le_top := λ L => by
    simp only [top, LE.le]
    intro a _
    cases a <;> decide

instance : BoundedOrder Logic := BoundedOrder.mk

theorem K_bot : K = ⊥ := rfl
theorem top_all_axioms : top = ⊤ := rfl

def hasAxiom (L : Logic) (a : Axiom) : Bool := a ∈ L.axioms

/-- Frame conditions required by a logic. -/
def frameConditions {W : Type*} (L : Logic) (R : AccessRel W) : Prop :=
  (L.hasAxiom .M → Refl R) ∧
  (L.hasAxiom .D → Serial R) ∧
  (L.hasAxiom .B → Symm R) ∧
  (L.hasAxiom .four → Trans R) ∧
  (L.hasAxiom .five → Eucl R)

end Logic

/-- S5 frames are equivalence relations. -/
theorem S5_equiv {W : Type*} {R : AccessRel W} (hR : Refl R) (hE : Eucl R) :
    Refl R ∧ Symm R ∧ Trans R :=
  ⟨hR, refl_eucl_symm hR hE, refl_eucl_trans hR hE⟩

/-- S4 frames are preorders. -/
theorem S4_preorder {W : Type*} {R : AccessRel W} (hR : Refl R) (hT : Trans R) :
    Refl R ∧ Trans R := ⟨hR, hT⟩

/-- M + 5 implies D (M implies serial). -/
theorem M_implies_D {W : Type*} {R : AccessRel W} (hM : Refl R) : Serial R :=
  refl_serial hM

/-- M + 5 implies B. -/
theorem M5_implies_B {W : Type*} {R : AccessRel W} (hM : Refl R) (h5 : Eucl R) : Symm R :=
  refl_eucl_symm hM h5

/-- M + 5 implies 4. -/
theorem M5_implies_4 {W : Type*} {R : AccessRel W} (hM : Refl R) (h5 : Eucl R) : Trans R :=
  refl_eucl_trans hM h5

/-- S5 = M5 = MB5 = M4B5 = M45 = M4B (all collapse to same frame class).
    Any frame satisfying M and 5 automatically satisfies B and 4. -/
theorem S5_collapse {W : Type*} {R : AccessRel W} (hM : Refl R) (h5 : Eucl R) :
    Refl R ∧ Serial R ∧ Symm R ∧ Trans R ∧ Eucl R :=
  ⟨hM, refl_serial hM, refl_eucl_symm hM h5, refl_eucl_trans hM h5, h5⟩

/-! ## Standard Frames -/

def universalR {W : Type*} : AccessRel W := fun _ _ => true
def emptyR {W : Type*} : AccessRel W := fun _ _ => false
def identityR {W : Type*} [DecidableEq W] : AccessRel W := fun w v => w == v

@[simp] theorem universalR_refl {W : Type*} : Refl (universalR (W := W)) := fun _ => rfl
@[simp] theorem universalR_symm {W : Type*} : Symm (universalR (W := W)) := fun _ _ _ => rfl
@[simp] theorem universalR_trans {W : Type*} : Trans (universalR (W := W)) := fun _ _ _ _ _ => rfl
@[simp] theorem universalR_eucl {W : Type*} : Eucl (universalR (W := W)) := fun _ _ _ _ _ => rfl
@[simp] theorem universalR_serial {W : Type*} : Serial (universalR (W := W)) := fun w => ⟨w, rfl⟩

theorem universalR_S5 {W : Type*} :
    Refl (universalR (W := W)) ∧ Symm (universalR (W := W)) ∧ Trans (universalR (W := W)) :=
  ⟨universalR_refl, universalR_symm, universalR_trans⟩

theorem identityR_refl {W : Type*} [DecidableEq W] : Refl (identityR (W := W)) :=
  fun w => by simp [identityR]

/-! ## Modal Flavors and the Modal Semantic Space

Theory-neutral vocabulary for cross-linguistic modal typology.
A modal's meaning is a set of force-flavor pairs (Imel, Guo, & Steinert-Threlkeld 2026).

* Kratzer (1981). The Notional Category of Modality.
* Imel, Guo, & Steinert-Threlkeld (2026). An Efficient Communication Analysis of Modal Typology.
-/

/-- Modal flavor: the contextual source of modality (Kratzer 1981).
    Theory-neutral: avoids commitment to how flavor is semantically encoded.
    Teleological is subsumed under circumstantial (both concern facts/abilities). -/
inductive ModalFlavor where
  | epistemic       -- Evidence/knowledge
  | deontic         -- Norms/rules
  | circumstantial  -- Facts/abilities (subsumes teleological)
  deriving DecidableEq, BEq, Repr, Inhabited

instance : LawfulBEq ModalFlavor where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

instance : ToString ModalFlavor where
  toString | .epistemic => "e" | .deontic => "d" | .circumstantial => "c"

/-- All modal flavors. -/
def ModalFlavor.all : List ModalFlavor := [.epistemic, .deontic, .circumstantial]

/-- All modal forces. -/
def ModalForce.all : List ModalForce := [.necessity, .possibility]

/-- A force-flavor pair: one point in the modal semantic space P.
    |P| = |Force| × |Flavor| = 2 × 3 = 6.

    Imel, Guo, & Steinert-Threlkeld (2026): modal meanings are subsets of P. -/
structure ForceFlavor where
  force : ModalForce
  flavor : ModalFlavor
  deriving DecidableEq, BEq, Repr

instance : LawfulBEq ForceFlavor where
  eq_of_beq {a b} h := by
    cases a with | mk f1 fl1 => cases b with | mk f2 fl2 =>
    cases f1 <;> cases f2 <;> cases fl1 <;> cases fl2 <;>
      first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a with | mk f fl => cases f <;> cases fl <;> decide

instance : ToString ForceFlavor where
  toString ff := s!"({ff.force},{ff.flavor})"

/-- All six points in the modal semantic space. -/
def ForceFlavor.universe : List ForceFlavor :=
  ModalForce.all.flatMap fun fo => ModalFlavor.all.map fun fl => ⟨fo, fl⟩

theorem ForceFlavor.universe_length : ForceFlavor.universe.length = 6 := by native_decide

/-- The Cartesian product of forces and flavors. Infrastructure for constructing
    modal meanings; no theoretical commitment (just list operations). -/
def ForceFlavor.cartesianProduct (fos : List ModalForce) (fls : List ModalFlavor) :
    List ForceFlavor :=
  fos.flatMap fun fo => fls.map fun fl => ⟨fo, fl⟩

end Core.ModalLogic
