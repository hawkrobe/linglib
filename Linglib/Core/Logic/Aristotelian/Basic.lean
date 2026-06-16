import Mathlib.Logic.Basic
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.Hom.Basic

/-!
# The four Aristotelian relations [demey-smessaert-2018]

Two elements φ, ψ of a Boolean algebra stand in one of four *Aristotelian
relations* ([demey-smessaert-2024], Definition 1):

| Relation       | Condition                   | mathlib                    |
|----------------|-----------------------------|----------------------------|
| Contradictory  | `φ ⊓ ψ = ⊥` and `φ ⊔ ψ = ⊤` | `IsCompl`                  |
| Contrary       | `φ ⊓ ψ = ⊥`, `φ ⊔ ψ ≠ ⊤`    | `Disjoint ∧ ¬ Codisjoint`  |
| Subcontrary    | `φ ⊓ ψ ≠ ⊥`, `φ ⊔ ψ = ⊤`    | `¬ Disjoint ∧ Codisjoint`  |
| Subalternation | `φ < ψ`                     | `(· < ·)`                  |

The collection `{CD, C, SC, SA}` is the *Aristotelian geometry*; elements
standing in none of the four are *unconnected* ([smessaert-demey-2014]).

The relations are defined over an arbitrary `[BooleanAlgebra α]` — the abstract
"template" of [demey-smessaert-2024]. Concrete instances follow by plugging
in a Boolean algebra: the powerset `Set W`, predicate spaces `W → Prop` /
`W → Bool`, bitvectors `Fin n → Bool`, or a Lindenbaum–Tarski algebra. The
relations *are* mathlib's `IsCompl` / `Disjoint` / `Codisjoint` / `<`, so they
inherit that API.

## Main declarations

* `IsContradictory`, `IsContrary`, `IsSubcontrary`, `IsSubaltern`,
  `IsUnconnected` — the relations as predicates over `[BooleanAlgebra α]`.
* `OppositionRel` / `ImplicationRel`, `opposition` / `implication` — the two derived
  relation axes ([deklerck-demey-2025]); each a total classifier with `*_eq_*`
  characterizations, jointly recovering `IsUnconnected` as `NCD ∧ NI`.
* `isContradictory_apply_orderIso` and siblings — a Boolean isomorphism
  (`OrderIso`) is an *Aristotelian isomorphism*: it preserves and reflects all
  four relations ([deklerck-vignero-demey-2024]).
* `isContradictory_iff_forall` and siblings — the pointwise `∀ w`
  characterization at the `W → Bool` instance.

## Implementation notes

`IsContradictory := IsCompl`, `IsSubaltern := (· < ·)`, and contrariety /
subcontrariety are `Disjoint` / `Codisjoint` combinations, so symmetry and the
`OrderIso` transfer come almost entirely from mathlib's order API.

## Todo

* A first-class `AristotelianMorphism` / category of diagrams
  ([deklerck-vignero-demey-2024]); the `OrderIso` transfer lemmas are the
  immediately-useful slice.
-/

namespace Aristotelian

variable {W : Type*}

/-- The **opposition relation** between two elements of a Boolean algebra
([deklerck-demey-2025]): the four mutually-exclusive, jointly-exhaustive cells of
`(Disjoint?, Codisjoint?)`. -/
inductive OppositionRel
  /-- `Disjoint ∧ Codisjoint` — complementary (`IsCompl`). -/
  | contradictory
  /-- `Disjoint ∧ ¬ Codisjoint`. -/
  | contrary
  /-- `¬ Disjoint ∧ Codisjoint`. -/
  | subcontrary
  /-- `¬ Disjoint ∧ ¬ Codisjoint` — the residual `NCD`. -/
  | nonContradictory
  deriving DecidableEq, Repr, Inhabited

/-- The **implication relation** between two elements ([deklerck-demey-2025]): the four cells
of `(x ≤ y?, y ≤ x?)`. `left` is (proper) subalternation, `bi` is equality, `nonImplication`
is incomparability. -/
inductive ImplicationRel
  /-- `x ≤ y ∧ y ≤ x` — equal. -/
  | bi
  /-- `x ≤ y ∧ ¬ y ≤ x` — subalternation (`x` strictly entails `y`). -/
  | left
  /-- `¬ x ≤ y ∧ y ≤ x`. -/
  | right
  /-- `¬ x ≤ y ∧ ¬ y ≤ x` — incomparable. -/
  | nonImplication
  deriving DecidableEq, Repr, Inhabited

/-! ### The four relations -/

section Algebraic
variable {α : Type*} [BooleanAlgebra α]

/-- BA-generic contradictoriness: `φ` and `ψ` are complementary — mathlib's
    `IsCompl` (`Disjoint ∧ Codisjoint`); in a Boolean algebra, `ψ = φᶜ`. -/
abbrev IsContradictory (φ ψ : α) : Prop := IsCompl φ ψ

/-- BA-generic contrariety: jointly impossible (`Disjoint`) but not jointly
    exhaustive (`¬ Codisjoint` — both can be false). -/
abbrev IsContrary (φ ψ : α) : Prop := Disjoint φ ψ ∧ ¬ Codisjoint φ ψ

/-- BA-generic subcontrariety: not jointly impossible (`¬ Disjoint` — both can
    be true) but jointly exhaustive (`Codisjoint`). -/
abbrev IsSubcontrary (φ ψ : α) : Prop := ¬ Disjoint φ ψ ∧ Codisjoint φ ψ

/-- BA-generic *proper* subalternation: `φ` strictly entails `ψ`, i.e. `φ < ψ`. -/
abbrev IsSubaltern (φ ψ : α) : Prop := φ < ψ

/-- BA-generic unconnectedness: `φ` and `ψ` stand in none of the four
    Aristotelian relations. Per [demey-smessaert-2024]. -/
abbrev IsUnconnected (φ ψ : α) : Prop :=
  ¬ Disjoint φ ψ ∧ ¬ Codisjoint φ ψ ∧ ¬ φ ≤ ψ ∧ ¬ ψ ≤ φ

/-! ### Symmetry

`IsContradictory` is symmetric via `IsCompl.symm` (`h.symm`); contrariety and
subcontrariety get their own lemmas; `IsSubaltern` is directional. -/

theorem IsContrary.symm {φ ψ : α} (h : IsContrary φ ψ) :
    IsContrary ψ φ := ⟨h.1.symm, fun h' => h.2 h'.symm⟩

theorem IsSubcontrary.symm {φ ψ : α} (h : IsSubcontrary φ ψ) :
    IsSubcontrary ψ φ := ⟨fun h' => h.1 h'.symm, h.2.symm⟩

/-! ### Transfer along a Boolean isomorphism

A Boolean isomorphism — an `OrderIso` of Boolean algebras — is an *Aristotelian
isomorphism*: it preserves and reflects all four relations
([deklerck-vignero-demey-2024], [demey-smessaert-2024]; the abstract
content of [demey-smessaert-2018]'s bitstring transfer). Each lemma is a
direct consequence of mathlib's `OrderIso` order-preservation API. -/

variable {β : Type*} [BooleanAlgebra β]

theorem isContradictory_apply_orderIso (e : α ≃o β) {φ ψ : α} :
    IsContradictory (e φ) (e ψ) ↔ IsContradictory φ ψ := (e.isCompl_iff).symm

theorem isContrary_apply_orderIso (e : α ≃o β) {φ ψ : α} :
    IsContrary (e φ) (e ψ) ↔ IsContrary φ ψ := by
  simp only [IsContrary, disjoint_map_orderIso_iff, codisjoint_map_orderIso_iff]

theorem isSubcontrary_apply_orderIso (e : α ≃o β) {φ ψ : α} :
    IsSubcontrary (e φ) (e ψ) ↔ IsSubcontrary φ ψ := by
  simp only [IsSubcontrary, disjoint_map_orderIso_iff, codisjoint_map_orderIso_iff]

theorem isSubaltern_apply_orderIso (e : α ≃o β) {φ ψ : α} :
    IsSubaltern (e φ) (e ψ) ↔ IsSubaltern φ ψ := e.lt_iff_lt

/-! ### Two-axis classifiers (opposition × implication)

The relation between two elements factors into a `(Disjoint?, Codisjoint?)` *opposition* and a
`(≤?, ≥?)` *implication* — each a total, mutually-exclusive classifier ([deklerck-demey-2025]),
so no contingency hypothesis is needed. -/

/-- The opposition relation of `x, y`, from the meet/join tests. -/
def opposition [DecidableEq α] (x y : α) : OppositionRel :=
  if x ⊓ y = ⊥ then (if x ⊔ y = ⊤ then .contradictory else .contrary)
  else (if x ⊔ y = ⊤ then .subcontrary else .nonContradictory)

/-- The implication relation of `x, y`, from the order tests. -/
def implication [DecidableLE α] (x y : α) : ImplicationRel :=
  if x ≤ y then (if y ≤ x then .bi else .left)
  else (if y ≤ x then .right else .nonImplication)

@[simp] theorem opposition_eq_contradictory [DecidableEq α] {x y : α} :
    opposition x y = .contradictory ↔ IsContradictory x y := by
  unfold opposition IsContradictory; rw [isCompl_iff, disjoint_iff, codisjoint_iff]
  split_ifs <;> simp_all

@[simp] theorem opposition_eq_contrary [DecidableEq α] {x y : α} :
    opposition x y = .contrary ↔ IsContrary x y := by
  unfold opposition IsContrary; rw [disjoint_iff, codisjoint_iff]; split_ifs <;> simp_all

@[simp] theorem opposition_eq_subcontrary [DecidableEq α] {x y : α} :
    opposition x y = .subcontrary ↔ IsSubcontrary x y := by
  unfold opposition IsSubcontrary; rw [disjoint_iff, codisjoint_iff]; split_ifs <;> simp_all

@[simp] theorem opposition_eq_nonContradictory [DecidableEq α] {x y : α} :
    opposition x y = .nonContradictory ↔ ¬ Disjoint x y ∧ ¬ Codisjoint x y := by
  unfold opposition; rw [disjoint_iff, codisjoint_iff]; split_ifs <;> simp_all

@[simp] theorem implication_eq_bi [DecidableLE α] {x y : α} :
    implication x y = .bi ↔ x ≤ y ∧ y ≤ x := by
  unfold implication; split_ifs <;> simp_all

@[simp] theorem implication_eq_left [DecidableLE α] {x y : α} :
    implication x y = .left ↔ IsSubaltern x y := by
  unfold implication IsSubaltern; rw [lt_iff_le_not_ge]; split_ifs <;> simp_all

@[simp] theorem implication_eq_right [DecidableLE α] {x y : α} :
    implication x y = .right ↔ IsSubaltern y x := by
  unfold implication IsSubaltern; rw [lt_iff_le_not_ge]; split_ifs <;> simp_all

@[simp] theorem implication_eq_nonImplication [DecidableLE α] {x y : α} :
    implication x y = .nonImplication ↔ ¬ x ≤ y ∧ ¬ y ≤ x := by
  unfold implication; split_ifs <;> simp_all

/-- `IsUnconnected` is exactly the `(NCD, NI)` cell of the opposition × implication product
([deklerck-demey-2025]). -/
theorem isUnconnected_iff_classify [DecidableEq α] [DecidableLE α] {x y : α} :
    IsUnconnected x y ↔
      opposition x y = .nonContradictory ∧ implication x y = .nonImplication := by
  unfold IsUnconnected
  simp only [opposition_eq_nonContradictory, implication_eq_nonImplication, and_assoc]

/-- A Boolean isomorphism preserves the opposition relation. -/
theorem opposition_apply_orderIso [DecidableEq α] [DecidableEq β] (e : α ≃o β) (x y : α) :
    opposition (e x) (e y) = opposition x y := by
  have hd : (e x ⊓ e y = ⊥) ↔ (x ⊓ y = ⊥) := by
    rw [← disjoint_iff, ← disjoint_iff, disjoint_map_orderIso_iff]
  have hc : (e x ⊔ e y = ⊤) ↔ (x ⊔ y = ⊤) := by
    rw [← codisjoint_iff, ← codisjoint_iff, codisjoint_map_orderIso_iff]
  simp only [opposition, hd, hc]

/-- A Boolean isomorphism preserves the implication relation. -/
theorem implication_apply_orderIso [DecidableLE α] [DecidableLE β] (e : α ≃o β) (x y : α) :
    implication (e x) (e y) = implication x y := by
  simp only [implication, e.le_iff_le]

end Algebraic

/-! ### Pointwise characterization for `W → Bool`

A `W → Bool` predicate is an element of the Boolean algebra `W → Bool`; the
abstract relations unfold to the familiar model-theoretic `∀ w` conditions
(validity `⊨ φ := ∀ w, φ w = true`). -/

section Pointwise
variable {φ ψ : W → Bool}

private lemma bool_inf_eq_bot_iff (a b : Bool) :
    a ⊓ b = ⊥ ↔ ¬ (a = true ∧ b = true) := by cases a <;> cases b <;> decide
private lemma bool_sup_eq_top_iff (a b : Bool) :
    a ⊔ b = ⊤ ↔ (a = true ∨ b = true) := by cases a <;> cases b <;> decide

theorem disjoint_iff_forall :
    Disjoint φ ψ ↔ ∀ w, ¬ (φ w = true ∧ ψ w = true) := by
  rw [disjoint_iff, funext_iff]
  exact forall_congr' fun w => by
    simp only [Pi.inf_apply, Pi.bot_apply]; exact bool_inf_eq_bot_iff (φ w) (ψ w)

theorem codisjoint_iff_forall :
    Codisjoint φ ψ ↔ ∀ w, φ w = true ∨ ψ w = true := by
  rw [codisjoint_iff, funext_iff]
  exact forall_congr' fun w => by
    simp only [Pi.sup_apply, Pi.top_apply]; exact bool_sup_eq_top_iff (φ w) (ψ w)

theorem le_iff_forall :
    φ ≤ ψ ↔ ∀ w, φ w = true → ψ w = true := by
  simp only [Pi.le_def, Bool.le_iff_imp]

theorem isContradictory_iff_forall :
    IsContradictory φ ψ ↔
      (∀ w, ¬ (φ w = true ∧ ψ w = true)) ∧ (∀ w, φ w = true ∨ ψ w = true) := by
  simp only [IsContradictory, isCompl_iff, disjoint_iff_forall, codisjoint_iff_forall]

theorem isContrary_iff_forall :
    IsContrary φ ψ ↔
      (∀ w, ¬ (φ w = true ∧ ψ w = true)) ∧ ¬ (∀ w, φ w = true ∨ ψ w = true) := by
  simp only [IsContrary, disjoint_iff_forall, codisjoint_iff_forall]

theorem isSubcontrary_iff_forall :
    IsSubcontrary φ ψ ↔
      ¬ (∀ w, ¬ (φ w = true ∧ ψ w = true)) ∧ (∀ w, φ w = true ∨ ψ w = true) := by
  simp only [IsSubcontrary, disjoint_iff_forall, codisjoint_iff_forall]

theorem isSubaltern_iff_forall :
    IsSubaltern φ ψ ↔
      (∀ w, φ w = true → ψ w = true) ∧ ¬ (∀ w, ψ w = true → φ w = true) := by
  simp only [IsSubaltern, lt_iff_le_not_ge, le_iff_forall]

end Pointwise

end Aristotelian
