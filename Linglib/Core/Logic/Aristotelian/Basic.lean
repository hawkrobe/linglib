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

* `AristotelianRel` — the four relations (plus `unconnected`) as an inductive
  label, used by `Diagram.relation` to label edges.
* `IsContradictory`, `IsContrary`, `IsSubcontrary`, `IsSubaltern`,
  `IsUnconnected` — the relations over `[BooleanAlgebra α]`.
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

* Prove that `IsUnconnected` coincides with "no Aristotelian relation" under an
  explicit contingency hypothesis.
* A first-class `AristotelianMorphism` / category of diagrams
  ([deklerck-vignero-demey-2024]); the `OrderIso` transfer lemmas are the
  immediately-useful slice.
-/

namespace Aristotelian

variable {W : Type*}

/-- The four Aristotelian relations as a single inductive label, plus
`unconnected` for pairs standing in none of them. Used by `Diagram.relation`
to label edges. -/
inductive AristotelianRel where
  | contradictory
  | contrary
  | subcontrary
  /-- The `φ → ψ` direction: `φ` is the stronger (superaltern), `ψ` the weaker
  (subaltern). Asymmetric, so `subaltern φ ψ ≠ subaltern ψ φ`. -/
  | subaltern
  | unconnected
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
