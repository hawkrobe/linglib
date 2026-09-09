import Mathlib.Order.Lattice
import Linglib.Core.Order.Bilattice.Basic
import Linglib.Core.Order.Bilattice.Kleene
import Linglib.Core.Order.DeMorganAlgebra.Defs

/-!
# Fitting (1994): Kleene's three valued logics and their children

This file formalizes [fitting-1994]: Kleene's strong three-valued logic ([kleene-1952]) is the
consistent part `x ≤ₖ −x` of Belnap's `FOUR` ([belnap-1977]), and the guard connective `P : Q`
— `Q` if `P` is at least true, `⊥` otherwise — extends Belnap's logic so that Kleene's weak logic
and the asymmetric Lisp logic become definable there (Definition 5.1). Both generalize to the
product bilattices `L ⊙ L` of [ginsberg-1988], where the guard is `⟨a, b⟩ : ⟨c, d⟩ = ⟨a ∧ c, a ∧ d⟩`
(Definition 9.4).

The main results are the identities of Figure 4 for the guard, the closure theorems for exact
and consistent values (Theorems 9.2 and 9.3, `IsClassical.inf`, `Consistent.kSup`), the
identification of the Lisp and weak connectives on Kleene's values with `Trivalent.meetMiddle`
and `Trivalent.meetWeak`, and the collapse for bilinear bilattices: an equivalence of formulas
holds in `L ⊙ L` for a linear `L` iff it holds in `FOUR` (Theorem 10.5, `equivalent_iff_four`).

## Implementation notes

* The product, its negation and the conflation of §§6–7 are `Bilattice.Product`, the `Negation`
  instance on `L ⊙ L`, and `Evidential.conf`; a De Morgan lattice is a `DeMorganAlgebra`.
* The representation theorems of §8 are `Bilattice.decompose` ([avron-1996]); their
  negation- and conflation-preserving refinements (Theorems 8.2 and 8.3) and the tableau system
  of §4 are not formalized.
* Theorem 10.5 is stated for products of linear bounded lattices; `ofFour` embeds `FOUR` by
  sending the Boolean coordinates to the bounds, and `θ_⊤` reads it back.

## References

* [fitting-1994]
* [kleene-1952]
* [belnap-1977]
* [ginsberg-1988]
* [avron-1996]
* [peters-1979]
-/

open Bilattice Product Evidential

namespace Fitting1994

/-! ### Belnap's `FOUR` and Kleene's values (§3) -/

/-- Kleene's three values inside `FOUR`: `indet ↦ ⊥`, `true ↦ T`, `false ↦ F`. -/
def ofTruth : Trivalent → FOUR
  | .indet => FOUR.U
  | .true => FOUR.T
  | .false => FOUR.F

theorem ofTruth_injective : Function.Injective ofTruth := λ a b => by
  cases a <;> cases b <;> decide

/-- Kleene's values are exactly the consistent values, `{x | x ≤ₖ −x}` (§3). -/
theorem range_ofTruth : Set.range ofTruth = {x | FOUR.Consistent x} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    cases a <;> decide
  · intro hx
    obtain ⟨a, b⟩ := x
    cases a <;> cases b
    · exact ⟨.indet, rfl⟩
    · exact ⟨.false, rfl⟩
    · exact ⟨.true, rfl⟩
    · exact absurd hx (by decide)

/-- The classical values, the fixed points of conflation, are the defined Kleene values (§3). -/
theorem isClassical_ofTruth (a : Trivalent) : FOUR.IsClassical (ofTruth a) ↔ a.isDefined := by
  cases a <;> decide

/-- The truth order of `Trivalent` is `FOUR`'s on Kleene's values. -/
theorem le_ofTruth (a b : Trivalent) : a ≤ b ↔ ofTruth a ≤ ofTruth b := by
  cases a <;> cases b <;> decide

/-- The knowledge order of `Trivalent` (`Trivalent.toFlat`) is `FOUR`'s on Kleene's values. -/
theorem kLE_ofTruth (a b : Trivalent) :
    Trivalent.toFlat a ≤ Trivalent.toFlat b ↔ ofTruth a ≤ₖ ofTruth b := by
  cases a <;> cases b <;> decide

/-- Kleene negation is `FOUR`'s negation on Kleene's values. -/
theorem neg_ofTruth (a : Trivalent) : ofTruth (Trivalent.neg a) = neg (ofTruth a) := by
  cases a <;> rfl

/-- Strong Kleene conjunction is `FOUR`'s truth meet on Kleene's values (§3). -/
theorem inf_ofTruth (a b : Trivalent) : ofTruth (a ⊓ b) = ofTruth a ⊓ ofTruth b := by
  cases a <;> cases b <;> decide

/-- Strong Kleene disjunction is `FOUR`'s truth join on Kleene's values (§3). -/
theorem sup_ofTruth (a b : Trivalent) : ofTruth (a ⊔ b) = ofTruth a ⊔ ofTruth b := by
  cases a <;> cases b <;> decide

/-! ### Formulas and the semantics behind the tableaux (§4) -/

/-- Formulas over the bilattice connectives: the truth connectives and negation, consensus `⊗`,
gullibility `⊕`, and the guard `P : Q` of §5. -/
inductive Formula (Atom : Type*) where
  | atom : Atom → Formula Atom
  | inf : Formula Atom → Formula Atom → Formula Atom
  | sup : Formula Atom → Formula Atom → Formula Atom
  | neg : Formula Atom → Formula Atom
  | kInf : Formula Atom → Formula Atom → Formula Atom
  | kSup : Formula Atom → Formula Atom → Formula Atom
  | guard : Formula Atom → Formula Atom → Formula Atom

namespace Formula

variable {Atom L : Type*} [Lattice L]

/-- Evaluation in `L ⊙ L` under a valuation of the atoms (Definition 4.1). -/
def eval (v : Atom → L ⊙ L) : Formula Atom → L ⊙ L
  | atom a => v a
  | inf φ ψ => eval v φ ⊓ eval v ψ
  | sup φ ψ => eval v φ ⊔ eval v ψ
  | neg φ => Bilattice.neg (eval v φ)
  | kInf φ ψ => eval v φ ⊗ eval v ψ
  | kSup φ ψ => (eval v φ ⊕ eval v ψ : L ⊙ L)
  | guard φ ψ => Evidential.guard (eval v φ) (eval v ψ)

/-- Definition 4.2: `X` restricts `Y` when, under every valuation in `FOUR`, `Y` is at most true
(`⊥` or `true`) whenever `X` is. -/
def Restricts (φ ψ : Formula Atom) : Prop :=
  ∀ v : Atom → FOUR, eval v φ ≤ₖ FOUR.T → eval v ψ ≤ₖ FOUR.T

/-- Definition 4.2: `X` requires `Y` when, under every valuation in `FOUR`, `Y` is at least true
(`true` or `⊤`) whenever `X` is. -/
def Requires (φ ψ : Formula Atom) : Prop :=
  ∀ v : Atom → FOUR, FOUR.T ≤ₖ eval v φ → FOUR.T ≤ₖ eval v ψ

/-- `X ≡ Y`: the same value in `FOUR` under every valuation. -/
def Equivalent (φ ψ : Formula Atom) : Prop := ∀ v : Atom → FOUR, eval v φ = eval v ψ

/-- `X` restricts `Y` iff `¬Y` requires `¬X` (§4). -/
theorem restricts_iff_requires_neg (φ ψ : Formula Atom) :
    Restricts φ ψ ↔ Requires (.neg ψ) (.neg φ) := by
  have key : ∀ x y : FOUR, (x ≤ₖ FOUR.T → y ≤ₖ FOUR.T) ↔
      (FOUR.T ≤ₖ Bilattice.neg y → FOUR.T ≤ₖ Bilattice.neg x) := by decide
  exact forall_congr' λ v => key _ _

/-- Two formulas are equivalent iff each restricts and requires the other (§4). -/
theorem equivalent_iff (φ ψ : Formula Atom) :
    Equivalent φ ψ ↔ Restricts φ ψ ∧ Requires φ ψ ∧ Restricts ψ φ ∧ Requires ψ φ := by
  have key : ∀ x y : FOUR, x = y ↔ (x ≤ₖ FOUR.T → y ≤ₖ FOUR.T) ∧ (FOUR.T ≤ₖ x → FOUR.T ≤ₖ y) ∧
      (y ≤ₖ FOUR.T → x ≤ₖ FOUR.T) ∧ (FOUR.T ≤ₖ y → FOUR.T ≤ₖ x) := by decide
  simp only [Equivalent, Restricts, Requires, key, forall_and]

end Formula

/-! ### The guard connective (§5) -/

/-- On `FOUR`, `P : Q` is `Q` when `P` is at least true and `⊥` otherwise. -/
theorem guard_four :
    ∀ x y : FOUR, Evidential.guard x y = if FOUR.T ≤ₖ x then y else FOUR.U := by decide

section Guard

variable {L : Type*} [DistribLattice L] (x y z : L ⊙ L)

/-- Figure 4: `(P ⊗ Q) : R = (P ∧ Q) : R`. -/
theorem guard_kInf_left :
    Evidential.guard (x ⊗ y) z = Evidential.guard (x ⊓ y) z := by ext <;> simp [Evidential.guard]

/-- Figure 4: `(P ⊗ Q) : R = (P : R) ⊗ (Q : R)`. -/
theorem guard_kInf_left_eq :
    Evidential.guard (x ⊗ y) z = Evidential.guard x z ⊗ Evidential.guard y z := by
  ext <;> simp only [Evidential.guard, pro_mk, con_mk, pro_kInf, con_kInf] <;>
    exact inf_inf_distrib_right _ _ _

/-- Figure 4: `(P ⊗ Q) : R = (P : Q) : R`. -/
theorem guard_kInf_left_eq_guard_guard :
    Evidential.guard (x ⊗ y) z = Evidential.guard (Evidential.guard x y) z := by
  ext <;> simp [Evidential.guard]

/-- Figure 4: `(P ⊗ Q) : R = P : (Q : R)`. -/
theorem guard_kInf_left_eq_guard_guard' :
    Evidential.guard (x ⊗ y) z = Evidential.guard x (Evidential.guard y z) := by
  ext <;> simp [Evidential.guard, inf_assoc]

/-- Figure 4: `(P ⊕ Q) : R = (P ∨ Q) : R`. -/
theorem guard_kSup_left :
    Evidential.guard (x ⊕ y) z = Evidential.guard (x ⊔ y) z := by ext <;> simp [Evidential.guard]

/-- Figure 4: `(P ⊕ Q) : R = (P : R) ⊕ (Q : R)`. -/
theorem guard_kSup_left_eq :
    Evidential.guard (x ⊕ y) z = (Evidential.guard x z ⊕ Evidential.guard y z : L ⊙ L) := by
  ext <;> simp [Evidential.guard, inf_sup_right]

/-- Figure 4: `P : ¬Q = ¬(P : Q)`. -/
theorem guard_neg :
    Evidential.guard x (neg y) = neg (Evidential.guard x y) := by
  ext <;> simp [Evidential.guard]

/-- Figure 4: `P : (Q ∧ R) = (P : Q) ∧ (P : R)`. -/
theorem guard_inf : Evidential.guard x (y ⊓ z) = Evidential.guard x y ⊓ Evidential.guard x z := by
  ext <;> simp only [Evidential.guard, pro_mk, con_mk, pro_inf, con_inf]
  · exact inf_inf_distrib_left _ _ _
  · exact inf_sup_left _ _ _

/-- Figure 4: `P : (Q ∨ R) = (P : Q) ∨ (P : R)`. -/
theorem guard_sup : Evidential.guard x (y ⊔ z) = Evidential.guard x y ⊔ Evidential.guard x z := by
  ext <;> simp only [Evidential.guard, pro_mk, con_mk, pro_sup, con_sup]
  · exact inf_sup_left _ _ _
  · exact inf_inf_distrib_left _ _ _

/-- Figure 4: `P : (Q ⊗ R) = (P : Q) ⊗ (P : R)`. -/
theorem guard_kInf : Evidential.guard x (y ⊗ z) = Evidential.guard x y ⊗ Evidential.guard x z := by
  ext <;> simp only [Evidential.guard, pro_mk, con_mk, pro_kInf, con_kInf] <;>
    exact inf_inf_distrib_left _ _ _

/-- Figure 4: `P : (Q ⊕ R) = (P : Q) ⊕ (P : R)`. -/
theorem guard_kSup :
    Evidential.guard x (y ⊕ z) = (Evidential.guard x y ⊕ Evidential.guard x z : L ⊙ L) := by
  ext <;> simp only [Evidential.guard, pro_mk, con_mk, pro_kSup, con_kSup] <;>
    exact inf_sup_left _ _ _

/-- Figure 4: `P ⊕ (Q : P) = P`. -/
theorem kSup_guard_self : (x ⊕ Evidential.guard y x : L ⊙ L) = x := by
  ext <;> simp only [Evidential.guard, pro_mk, con_mk, pro_kSup, con_kSup] <;> rw [inf_comm] <;>
    exact sup_inf_self

/-- Figure 4: `P ⊗ (Q : P) = Q : P`. -/
theorem kInf_guard_self : x ⊗ Evidential.guard y x = Evidential.guard y x := by
  ext <;> simp only [Evidential.guard, pro_mk, con_mk, pro_kInf, con_kInf] <;>
    rw [inf_comm y.pro, inf_left_idem]

variable {x y z}

/-- The guard is truth-monotone in its second input. -/
theorem guard_le_guard_right (h : y ≤ z) : Evidential.guard x y ≤ Evidential.guard x z :=
  ⟨inf_le_inf_left _ h.1, inf_le_inf_left _ h.2⟩

/-- The "curious property": `P₁ ≤ₜ P₂` gives `(P₁ : Q) ≤ₖ (P₂ : Q)`. -/
theorem guard_kLE_guard_of_le (h : x ≤ y) : Evidential.guard x z ≤ₖ Evidential.guard y z :=
  ⟨inf_le_inf_right _ h.1, inf_le_inf_right _ h.1⟩

end Guard

/-- The guard is not truth-monotone in its first input: `⊥ ≤ₜ true` in `FOUR`, yet
`⊥ : false = ⊥` is not below `true : false = false`. -/
theorem not_guard_le_guard_left :
    ¬ ∀ x y z : FOUR, x ≤ y → Evidential.guard x z ≤ Evidential.guard y z :=
  λ h => absurd (h FOUR.U FOUR.T FOUR.F (by decide)) (by decide)

/-! ### Lisp and weak Kleene connectives through the Evidential.guard (§5) -/

section Lisp

variable {L : Type*} [DistribLattice L]

/-- Definition 5.1: Lisp conjunction `P ∧⃗ Q = P ∧ (P : Q)` — the second conjunct is consulted
only past the guard of the first. -/
def landL (x y : L ⊙ L) : L ⊙ L := x ⊓ Evidential.guard x y

/-- Definition 5.1: Lisp disjunction `P ∨⃗ Q = P ∨ (¬P : Q)`. -/
def lorL (x y : L ⊙ L) : L ⊙ L := x ⊔ Evidential.guard (neg x) y

/-- Definition 5.1: weak Kleene conjunction `P ∧ʷ Q = (P ∧⃗ Q) ⊗ (Q ∧⃗ P)`, the consensus of the
two evaluation orders. -/
def landW (x y : L ⊙ L) : L ⊙ L := landL x y ⊗ landL y x

/-- Definition 5.1: weak Kleene disjunction `P ∨ʷ Q = (P ∨⃗ Q) ⊗ (Q ∨⃗ P)`. -/
def lorW (x y : L ⊙ L) : L ⊙ L := lorL x y ⊗ lorL y x

variable (x y : L ⊙ L)

/-- Strong Kleene conjunction is the gullible combination of the two Lisp evaluations,
`P ∧ Q = (P ∧⃗ Q) ⊕ (Q ∧⃗ P)`, in every product. -/
theorem inf_eq_landL_kSup_landL : x ⊓ y = (landL x y ⊕ landL y x : L ⊙ L) := by
  ext
  · simp only [landL, Evidential.guard, pro_kSup, pro_inf, pro_mk]
    rw [inf_left_idem, inf_left_idem, inf_comm y.pro, sup_idem]
  · simp only [landL, Evidential.guard, con_kSup, con_inf, con_mk]
    exact le_antisymm (sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_right le_sup_left))
      (sup_le (sup_le le_sup_left (inf_le_right.trans le_sup_right))
        (sup_le le_sup_right (inf_le_right.trans le_sup_left)))

/-- Strong Kleene disjunction is the gullible combination of the two Lisp evaluations,
`P ∨ Q = (P ∨⃗ Q) ⊕ (Q ∨⃗ P)`. -/
theorem sup_eq_lorL_kSup_lorL : x ⊔ y = (lorL x y ⊕ lorL y x : L ⊙ L) := by
  ext
  · simp only [lorL, Evidential.guard, pro_kSup, pro_sup, pro_mk, pro_neg]
    exact le_antisymm (sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_right le_sup_left))
      (sup_le (sup_le le_sup_left (inf_le_right.trans le_sup_right))
        (sup_le le_sup_right (inf_le_right.trans le_sup_left)))
  · simp only [lorL, Evidential.guard, con_kSup, con_sup, con_mk, pro_neg]
    rw [inf_left_idem, inf_left_idem, inf_comm y.con, sup_idem]

end Lisp

/-- On Kleene's values Lisp conjunction is the middle Kleene conjunction of [peters-1979]. -/
theorem landL_ofTruth : ∀ a b : Trivalent, landL (ofTruth a) (ofTruth b) =
    ofTruth (Trivalent.meetMiddle a b) := by decide

/-- On Kleene's values Lisp disjunction is middle Kleene disjunction. -/
theorem lorL_ofTruth : ∀ a b : Trivalent, lorL (ofTruth a) (ofTruth b) =
    ofTruth (Trivalent.joinMiddle a b) := by decide

/-- On Kleene's values `∧ʷ` is weak Kleene conjunction. -/
theorem landW_ofTruth : ∀ a b : Trivalent, landW (ofTruth a) (ofTruth b) =
    ofTruth (Trivalent.meetWeak a b) := by decide

/-- On Kleene's values `∨ʷ` is weak Kleene disjunction. -/
theorem lorW_ofTruth : ∀ a b : Trivalent, lorW (ofTruth a) (ofTruth b) =
    ofTruth (Trivalent.joinWeak a b) := by decide

/-- Lisp conjunction distributes over Lisp disjunction on three values. -/
theorem meetMiddle_joinMiddle_distrib : ∀ a b c : Trivalent,
    Trivalent.meetMiddle a (Trivalent.joinMiddle b c) =
      Trivalent.joinMiddle (Trivalent.meetMiddle a b) (Trivalent.meetMiddle a c) := by
  decide

/-- The distributivity law fails on four: `P = R = ⊤`, `Q = ⊥` falsifies it. -/
theorem not_landL_lorL_distrib :
    ¬ ∀ x y z : FOUR, landL x (lorL y z) = lorL (landL x y) (landL x z) :=
  λ h => absurd (h FOUR.I FOUR.U FOUR.I) (by decide)

/-! ### Bilattices and the product construction (§§6–7) -/

section Product

variable {L : Type*} [Lattice L] [BoundedOrder L]

/-- The extremal identities (§6) in `L ⊙ L`, with `(⊤, ⊤)` and `(⊥, ⊥)` the knowledge bounds:
`true ⊕ false = ⊤`, `true ⊗ false = ⊥`, `⊤ ∧ ⊥ = false`, `⊤ ∨ ⊥ = true`. -/
theorem extremal :
    ((⊤ : L ⊙ L) ⊕ ⊥ : L ⊙ L) = mk ⊤ ⊤ ∧ (⊤ : L ⊙ L) ⊗ ⊥ = mk ⊥ ⊥ ∧
      (mk ⊤ ⊤ : L ⊙ L) ⊓ mk ⊥ ⊥ = ⊥ ∧ (mk ⊤ ⊤ : L ⊙ L) ⊔ mk ⊥ ⊥ = ⊤ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;> simp

end Product

section Conflation

variable {L : Type*} [LatticeWithInvolution L] (x y : L ⊙ L)

/-- §7: the conflation `−(x, y) = (yᶜ, xᶜ)` from a De Morgan complement is an involution
(Definition 6.2). -/
theorem conf_conf :
    Evidential.conf compl (Evidential.conf compl x) = x := by
  ext <;> simp [Evidential.conf, LatticeWithInvolution.compl_compl]

/-- Conflation preserves the truth order (Definition 6.2). -/
theorem conf_le_conf {x y :
    L ⊙ L} (h : x ≤ y) : Evidential.conf compl x ≤ Evidential.conf compl y :=
  ⟨LatticeWithInvolution.compl_le_compl h.2, LatticeWithInvolution.compl_le_compl h.1⟩

/-- Conflation reverses the knowledge order (Definition 6.2). -/
theorem conf_kLE_conf {x y :
    L ⊙ L} (h : x ≤ₖ y) : Evidential.conf compl y ≤ₖ Evidential.conf compl x :=
  ⟨LatticeWithInvolution.compl_le_compl h.2, LatticeWithInvolution.compl_le_compl h.1⟩

/-- Negation and conflation commute (§7). -/
theorem neg_conf :
    neg (Evidential.conf compl x) = Evidential.conf compl (neg x) := rfl

end Conflation

/-! ### Kleene's logics generalized (§9) -/

section Generalized

variable {L : Type*} [DeMorganAlgebra L]

/-- Definition 9.1: `x` is consistent, `x ≤ₖ −x`, iff its evidence against is below the
complement of its evidence for. -/
theorem consistent_iff (x : L ⊙ L) : Consistent compl x ↔ x.con ≤ x.proᶜ :=
  consistent_iff_con_le LatticeWithInvolution.compl_anti LatticeWithInvolution.compl_compl

/-- Definition 9.1: `x` is exact, `x = −x`, iff its evidence for is the complement of its
evidence against. -/
theorem isClassical_iff (x : L ⊙ L) : IsClassical compl x ↔ x.pro = x.conᶜ :=
  ⟨λ h => congrArg pro h,
    λ h => Product.ext h (by simp [Evidential.conf, h, LatticeWithInvolution.compl_compl])⟩

variable {x y z : L ⊙ L}

/-- Theorem 9.2: `true` is exact. -/
theorem isClassical_top : IsClassical compl (⊤ : L ⊙ L) := (isClassical_iff _).2 (by simp)

/-- Theorem 9.2: `false` is exact. -/
theorem isClassical_bot : IsClassical compl (⊥ : L ⊙ L) := (isClassical_iff _).2 (by simp)

/-- Theorem 9.2: the exact values are closed under `∧`. -/
theorem IsClassical.inf (hx : IsClassical compl x) (hy : IsClassical compl y) :
    IsClassical compl (x ⊓ y) := by
  rw [isClassical_iff] at *
  simp [hx, hy]

/-- Theorem 9.2: the exact values are closed under `∨`. -/
theorem IsClassical.sup (hx : IsClassical compl x) (hy : IsClassical compl y) :
    IsClassical compl (x ⊔ y) := by
  rw [isClassical_iff] at *
  simp [hx, hy]

/-- Theorem 9.2: the exact values are closed under negation. -/
theorem IsClassical.neg (hx : IsClassical compl x) : IsClassical compl (neg x) := by
  rw [isClassical_iff] at *
  simp [hx, LatticeWithInvolution.compl_compl]

/-- Theorem 9.2: the knowledge top `⊤ = (⊤, ⊤)` is not exact. -/
theorem not_isClassical_kTop [Nontrivial L] : ¬ IsClassical compl (mk ⊤ ⊤ : L ⊙ L) := by
  rw [isClassical_iff]
  simp

/-- Theorem 9.2: the knowledge bottom `⊥ = (⊥, ⊥)` is not exact. -/
theorem not_isClassical_kBot [Nontrivial L] : ¬ IsClassical compl (mk ⊥ ⊥ : L ⊙ L) := by
  rw [isClassical_iff]
  simp

/-- Theorem 9.2: the exact values are not closed under `⊗`: `true ⊗ false = ⊥`. -/
theorem not_isClassical_kInf [Nontrivial L] : ¬ IsClassical compl ((⊤ : L ⊙ L) ⊗ ⊥) := by
  rw [isClassical_iff]
  simp

/-- Theorem 9.2: the exact values are not closed under `⊕`: `true ⊕ false = ⊤`. -/
theorem not_isClassical_kSup [Nontrivial L] : ¬ IsClassical compl ((⊤ : L ⊙ L) ⊕ ⊥ : L ⊙ L) := by
  rw [isClassical_iff]
  simp

/-- Theorem 9.3: the exact values are consistent. -/
theorem Consistent.of_isClassical (hx : IsClassical compl x) : Consistent compl x := by
  rw [Evidential.Consistent, ← hx]

/-- Theorem 9.3: the consistent values are closed under `∧`. -/
theorem Consistent.inf (hx : Consistent compl x) (hy : Consistent compl y) :
    Consistent compl (x ⊓ y) := by
  rw [consistent_iff] at *
  simpa using sup_le_sup hx hy

/-- Theorem 9.3: the consistent values are closed under `∨`. -/
theorem Consistent.sup (hx : Consistent compl x) (hy : Consistent compl y) :
    Consistent compl (x ⊔ y) := by
  rw [consistent_iff] at *
  simpa using inf_le_inf hx hy

/-- Theorem 9.3: the consistent values are closed under negation. -/
theorem Consistent.neg (hx : Consistent compl x) : Consistent compl (neg x) := by
  rw [consistent_iff] at *
  simpa using LatticeWithInvolution.le_compl_comm.1 hx

/-- Theorem 9.3: the consistent values are closed under consensus `⊗` — indeed the consensus of a
consistent value with any value is consistent. -/
theorem Consistent.kInf (hx : Consistent compl x) (y : L ⊙ L) : Consistent compl (x ⊗ y) := by
  rw [consistent_iff] at *
  simpa using inf_le_left.trans (hx.trans le_sup_left)

/-- Theorem 9.3: the consistent values are closed under gullibility `⊕` below a common consistent
upper bound. -/
theorem Consistent.kSup (hx : Consistent compl x) (hy : Consistent compl y)
    (hz : Consistent compl z) (hxz : x ≤ₖ z) (hyz : y ≤ₖ z) : Consistent compl (x ⊕ y) := by
  rw [consistent_iff] at *
  simp only [pro_kSup, con_kSup, LatticeWithInvolution.compl_sup]
  exact sup_le (le_inf hx (hxz.2.trans (hz.trans (LatticeWithInvolution.compl_le_compl hyz.1))))
    (le_inf (hyz.2.trans (hz.trans (LatticeWithInvolution.compl_le_compl hxz.1))) hy)

/-- The generalized guard of Definition 9.4, `(a, b) : (c, d) = (a ∧ c, a ∧ d)`, characterized
as `[(P ⊗ true) ⊕ ¬(P ⊗ true)] ⊗ Q` (§9). -/
theorem guard_eq_kSup_neg (x y : L ⊙ L) :
    Evidential.guard x y = ((x ⊗ ⊤ ⊕ neg (x ⊗ ⊤) : L ⊙ L) ⊗ y) := by
  ext <;> simp [Evidential.guard]

/-- §9: the guard of a consistent value is consistent. -/
theorem Consistent.guard (hy :
    Consistent compl y) (x : L ⊙ L) : Consistent compl (Evidential.guard x y) := by
  rw [consistent_iff] at *
  simpa [Evidential.guard] using inf_le_right.trans (hy.trans le_sup_right)

variable {x' y' : L ⊙ L}

/-- §9: Lisp conjunction is knowledge-monotone. -/
theorem landL_kLE_landL (hx : x ≤ₖ x') (hy : y ≤ₖ y') : landL x y ≤ₖ landL x' y' :=
  ⟨inf_le_inf hx.1 (inf_le_inf hx.1 hy.1), sup_le_sup hx.2 (inf_le_inf hx.1 hy.2)⟩

/-- §9: Lisp disjunction is knowledge-monotone. -/
theorem lorL_kLE_lorL (hx : x ≤ₖ x') (hy : y ≤ₖ y') : lorL x y ≤ₖ lorL x' y' :=
  ⟨sup_le_sup hx.1 (inf_le_inf hx.2 hy.1), inf_le_inf hx.2 (inf_le_inf hx.2 hy.2)⟩

/-- §9: weak conjunction is knowledge-monotone. -/
theorem landW_kLE_landW (hx : x ≤ₖ x') (hy : y ≤ₖ y') : landW x y ≤ₖ landW x' y' :=
  ⟨inf_le_inf (landL_kLE_landL hx hy).1 (landL_kLE_landL hy hx).1,
    inf_le_inf (landL_kLE_landL hx hy).2 (landL_kLE_landL hy hx).2⟩

/-- §9: weak disjunction is knowledge-monotone. -/
theorem lorW_kLE_lorW (hx : x ≤ₖ x') (hy : y ≤ₖ y') : lorW x y ≤ₖ lorW x' y' :=
  ⟨inf_le_inf (lorL_kLE_lorL hx hy).1 (lorL_kLE_lorL hy hx).1,
    inf_le_inf (lorL_kLE_lorL hx hy).2 (lorL_kLE_lorL hy hx).2⟩

/-- §9: the consistent values are closed under the four Kleene connectives. -/
theorem Consistent.landL (hx : Consistent compl x) (hy : Consistent compl y) :
    Consistent compl (landL x y) :=
  Consistent.inf hx (Consistent.guard hy x)

theorem Consistent.lorL (hx : Consistent compl x) (hy : Consistent compl y) :
    Consistent compl (lorL x y) :=
  Consistent.sup hx (Consistent.guard hy (Bilattice.neg x))

theorem Consistent.landW (hx : Consistent compl x) (hy : Consistent compl y) :
    Consistent compl (landW x y) :=
  Consistent.kInf (Consistent.landL hx hy) _

theorem Consistent.lorW (hx : Consistent compl x) (hy : Consistent compl y) :
    Consistent compl (lorW x y) :=
  Consistent.kInf (Consistent.lorL hx hy) _

end Generalized

/-! ### Bilinear bilattices (§10) -/

/-- Definition 10.1: any two members are comparable in at least one of the two orders. -/
def Bilinear (B : Type*) [Preorder B] [Preorder (Know B)] : Prop :=
  ∀ x y : B, x ≤ y ∨ y ≤ x ∨ x ≤ₖ y ∨ y ≤ₖ x

/-- Proposition 10.2: a product is bilinear iff each factor is linearly ordered. -/
theorem bilinear_iff {L R : Type*} [PartialOrder L] [PartialOrder R] [BoundedOrder L]
    [BoundedOrder R] :
    Bilinear (L ⊙ R) ↔ (∀ a b : L, a ≤ b ∨ b ≤ a) ∧ ∀ a b : R, a ≤ b ∨ b ≤ a := by
  constructor
  · intro h
    refine ⟨λ a b => ?_, λ a b => ?_⟩
    · rcases h (mk a ⊥) (mk b ⊥) with h | h | h | h
      · exact .inl h.1
      · exact .inr h.1
      · exact .inl h.1
      · exact .inr h.1
    · rcases h (mk ⊥ a) (mk ⊥ b) with h | h | h | h
      · exact .inr h.2
      · exact .inl h.2
      · exact .inl h.2
      · exact .inr h.2
  · rintro ⟨hL, hR⟩ x y
    rcases hL x.pro y.pro with h₁ | h₁ <;> rcases hR x.con y.con with h₂ | h₂
    · exact .inr (.inr (.inl ⟨h₁, h₂⟩))
    · exact .inl ⟨h₁, h₂⟩
    · exact .inr (.inl ⟨h₁, h₂⟩)
    · exact .inr (.inr (.inr ⟨h₁, h₂⟩))

section Theta

variable {L : Type*} [LinearOrder L] (a : L)

/-- Definition 10.3: `θ_a` reads a member of `L ⊙ L` into `FOUR` coordinatewise by `a → x`,
which is `true` iff `a ≤ x`. -/
def theta (x : L ⊙ L) : FOUR := mk (decide (a ≤ x.pro)) (decide (a ≤ x.con))

variable (x y : L ⊙ L)

private theorem decide_inf (p q : L) : decide (a ≤ p ⊓ q) = (decide (a ≤ p) ⊓ decide (a ≤ q)) := by
  by_cases hp : a ≤ p <;> by_cases hq : a ≤ q <;> simp [hp, hq]

private theorem decide_sup (p q : L) : decide (a ≤ p ⊔ q) = (decide (a ≤ p) ⊔ decide (a ≤ q)) := by
  by_cases hp : a ≤ p <;> by_cases hq : a ≤ q <;> simp [hp, hq]

theorem theta_neg : theta a (neg x) = neg (theta a x) := rfl

/-- Lemma 10.4: `θ_a` preserves `∧` when `L` is linear. -/
theorem theta_inf : theta a (x ⊓ y) = theta a x ⊓ theta a y := by
  ext <;> simp only [theta, pro_mk, con_mk, pro_inf, con_inf, decide_inf, decide_sup]

theorem theta_sup : theta a (x ⊔ y) = theta a x ⊔ theta a y := by
  ext <;> simp only [theta, pro_mk, con_mk, pro_sup, con_sup, decide_inf, decide_sup]

theorem theta_kInf : theta a (x ⊗ y) = theta a x ⊗ theta a y := by
  ext <;> simp only [theta, pro_mk, con_mk, pro_kInf, con_kInf, decide_inf]

theorem theta_kSup : theta a (x ⊕ y) = (theta a x ⊕ theta a y : FOUR) := by
  ext <;> simp only [theta, pro_mk, con_mk, pro_kSup, con_kSup, decide_sup]

theorem theta_guard :
    theta a (Evidential.guard x y) = Evidential.guard (theta a x) (theta a y) := by
  ext <;> simp only [theta, Evidential.guard, pro_mk, con_mk, decide_inf]

variable {Atom : Type*}

/-- Lemma 10.4: `θ_a` is a homomorphism for every connective, so it commutes with evaluation. -/
theorem eval_theta (v : Atom → L ⊙ L) (φ : Formula Atom) :
    Formula.eval (theta a ∘ v) φ = theta a (Formula.eval v φ) := by
  induction φ with
  | atom _ => rfl
  | inf φ ψ ihφ ihψ => simp only [Formula.eval, ihφ, ihψ, theta_inf]
  | sup φ ψ ihφ ihψ => simp only [Formula.eval, ihφ, ihψ, theta_sup]
  | neg φ ih => simp only [Formula.eval, ih, theta_neg]
  | kInf φ ψ ihφ ihψ => simp only [Formula.eval, ihφ, ihψ, theta_kInf]
  | kSup φ ψ ihφ ihψ => simp only [Formula.eval, ihφ, ihψ, theta_kSup]
  | guard φ ψ ihφ ihψ => simp only [Formula.eval, ihφ, ihψ, theta_guard]

variable {a x y}

private theorem decide_ne {p q : L} (h : p ≠ q) : decide (p ⊔ q ≤ p) ≠ decide (p ⊔ q ≤ q) := by
  intro heq
  rw [decide_eq_decide, sup_le_iff, sup_le_iff, and_iff_right le_rfl, and_iff_left le_rfl] at heq
  rcases le_total p q with hle | hle
  · exact h (hle.antisymm (heq.2 hle))
  · exact h ((heq.1 hle).antisymm hle)

/-- Distinct members of `L ⊙ L` are separated by some `θ_a` (the proof of Theorem 10.5). -/
theorem exists_theta_ne (h : x ≠ y) : ∃ a, theta a x ≠ theta a y := by
  by_cases hp : x.pro = y.pro
  · have hc : x.con ≠ y.con := λ hc => h (Product.ext hp hc)
    exact ⟨x.con ⊔ y.con, λ heq => decide_ne hc (congrArg con heq)⟩
  · exact ⟨x.pro ⊔ y.pro, λ heq => decide_ne hp (congrArg pro heq)⟩

variable [BoundedOrder L]

/-- `FOUR` inside `L ⊙ L`: the Boolean coordinates sent to the bounds. -/
def ofFour (z : FOUR) : L ⊙ L := mk (if z.pro then ⊤ else ⊥) (if z.con then ⊤ else ⊥)

/-- `θ_⊤` reads `ofFour` back. -/
theorem theta_top_ofFour [Nontrivial L] (z : FOUR) : theta (⊤ : L) (ofFour z) = z := by
  ext
  · show decide ((⊤ : L) ≤ if z.pro then ⊤ else ⊥) = z.pro
    cases z.pro <;> simp
  · show decide ((⊤ : L) ≤ if z.con then ⊤ else ⊥) = z.con
    cases z.con <;> simp

/-- Theorem 10.5: an equivalence is valid in the bilinear product `L ⊙ L` iff it is valid in
`FOUR`. -/
theorem equivalent_iff_four [Nontrivial L] (φ ψ : Formula Atom) :
    (∀ v : Atom → L ⊙ L, Formula.eval v φ = Formula.eval v ψ) ↔ Formula.Equivalent φ ψ := by
  constructor
  · intro h v
    have hv : theta (⊤ : L) ∘ (ofFour ∘ v) = v := funext λ b => theta_top_ofFour (v b)
    calc Formula.eval v φ = Formula.eval (theta (⊤ : L) ∘ (ofFour ∘ v)) φ := by rw [hv]
      _ = theta (⊤ : L) (Formula.eval (ofFour ∘ v) φ) := eval_theta _ _ _
      _ = theta (⊤ : L) (Formula.eval (ofFour ∘ v) ψ) := by rw [h]
      _ = Formula.eval (theta (⊤ : L) ∘ (ofFour ∘ v)) ψ := (eval_theta _ _ _).symm
      _ = Formula.eval v ψ := by rw [hv]
  · intro h v
    by_contra hne
    obtain ⟨a, ha⟩ := exists_theta_ne hne
    exact ha (by rw [← eval_theta, ← eval_theta, h])

end Theta

end Fitting1994
