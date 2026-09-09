import Linglib.Core.Order.Bilattice.Product
import Linglib.Core.Order.DeMorganAlgebra.Defs

/-!
# Evidential bilattices over a chain
[fitting-1994] [schoter-1996]

The *evidential* bilattices ([schoter-1996]) are the diagonal Ginsberg–Fitting
products `S ⊙ S` over a chain `S` (`Core.Order.Bilattice.Product`): a value is
a pair `(for, against)` of degrees of evidence, with

* `≤` truer = more evidence-for, less evidence-against (the truth order);
* `≤ₖ` more informative = more evidence both ways (the knowledge order);
* `Product.neg` (truth inversion) swaps the two coordinates;
* `conf` (knowledge inversion, the *conflation*) complements each coordinate.

With `S = Bool` this is [belnap-1977]'s `FOUR`, whose logic is developed as a
bilattice by [arieli-avron-1996]; with `S = Fin 3` (the chain `0 < ½ < 1`) it
is [schoter-1996]'s 9-valued `PRESUP` (see `Studies.Schoter1996`).

## Main definitions

* `Bilattice.Evidential S := S ⊙ S` — the evidential bilattice over a chain `S`
* `Evidential.conf`/`Consistent` — conflation and the consistent (`x ≤ₖ −x`,
  non-glut) fragment
* `Bilattice.FOUR := Evidential Bool` — Belnap's four-valued bilattice
-/

namespace Bilattice

/-- The evidential bilattice over a chain `S`: the diagonal product `S ⊙ S`,
values are `(for, against)` pairs ([schoter-1996]). -/
abbrev Evidential (S : Type*) := Product S S

namespace Evidential

variable {S : Type*}

/-- Conflation `−`: knowledge inversion, complements each coordinate by `compl`,
which is intended to be the order-reversing involution on the chain `S`
(`(! ·)` for `Bool`, `Fin.rev` for `Fin n`). -/
def conf (compl : S → S) (x : Evidential S) : Evidential S :=
  .mk (compl x.con) (compl x.pro)

/-- The consistent (non-glut) fragment: `x ≤ₖ −x` ([fitting-1994]). -/
@[reducible] def Consistent [Preorder S] (compl : S → S) (x : Evidential S) : Prop :=
  x ≤ₖ conf compl x

/-- The classical fragment: `x = −x`, the fixed points of conflation
([fitting-1994]; [schoter-1996]'s `CLAS`). -/
@[reducible] def IsClassical (compl : S → S) (x : Evidential S) : Prop :=
  x = conf compl x

/-- Over an order-reversing involution `compl`, consistency reduces to a single
inequality: the evidence-against is below the complement of the evidence-for
([schoter-1996]'s `CONS = {⟨a, b⟩ | a ≤ b′}`). -/
theorem consistent_iff_con_le [Preorder S] {compl : S → S} (hanti : Antitone compl)
    (hinv : Function.Involutive compl) {x : Evidential S} :
    Consistent compl x ↔ x.con ≤ compl x.pro := by
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  have h' := hanti h
  rw [hinv x.pro] at h'
  exact h'

section Guard

variable [SemilatticeInf S]

/-- Fitting's guard connective `φ : ψ` ([schoter-1996] Def 4): the value of the
second coordinate, attenuated by the positive evidence for the first. -/
def guard (x y : Evidential S) : Evidential S := .mk (x.pro ⊓ y.pro) (x.pro ⊓ y.con)

/-- The guard is monotone in the knowledge order (in both arguments), as
[schoter-1996] Def 4 notes — though it is not a lattice-theoretic connective. -/
theorem guard_kLE_guard {x x' y y' : Evidential S} (hx : x ≤ₖ x') (hy : y ≤ₖ y') :
    guard x y ≤ₖ guard x' y' :=
  ⟨inf_le_inf hx.1 hy.1, inf_le_inf hx.1 hy.2⟩

variable [BoundedOrder S]

/-- If the guard's first coordinate is at least true on `≤ₖ`, the guard is its
second coordinate ([schoter-1996] Def 4). -/
theorem guard_of_top_kLE {x : Evidential S} (h : (⊤ : Evidential S) ≤ₖ x)
    (y : Evidential S) : guard x y = y := by
  have hp : x.pro = ⊤ := le_antisymm le_top h.1
  simp [guard, hp]

/-- With no positive evidence for the first coordinate, the guard is `U`
([schoter-1996] Def 4). -/
theorem guard_of_pro_bot {x : Evidential S} (h : x.pro = ⊥) (y : Evidential S) :
    guard x y = .mk ⊥ ⊥ := by
  simp [guard, h]

end Guard

/-! ### Conflation from a De Morgan complement

Over a lattice with an involutive antitone complement, `conf compl` is a conflation in the sense
of `Bilattice.Conflation` — an involution preserving the truth order and reversing the knowledge
order — and it commutes with Ginsberg negation ([fitting-1994] §7, [fitting-2021] §8.8). The
exact, consistent and anticonsistent values then read off the coordinates. -/

section Involution

variable [LatticeWithInvolution S]

theorem conf_conf (x : Evidential S) : Evidential.conf compl (Evidential.conf compl x) = x := by
  ext <;> simp [Evidential.conf, LatticeWithInvolution.compl_compl]

theorem conf_le_conf {x y : Evidential S} (h : x ≤ y) :
    Evidential.conf compl x ≤ Evidential.conf compl y :=
  ⟨LatticeWithInvolution.compl_le_compl h.2, LatticeWithInvolution.compl_le_compl h.1⟩

theorem conf_kLE_conf {x y : Evidential S} (h : x ≤ₖ y) :
    Evidential.conf compl y ≤ₖ Evidential.conf compl x :=
  ⟨LatticeWithInvolution.compl_le_compl h.2, LatticeWithInvolution.compl_le_compl h.1⟩

instance : Conflation (Evidential S) where
  conf := Evidential.conf compl
  conf_conf := conf_conf
  conf_le_conf := conf_le_conf
  conf_kLE_conf := conf_kLE_conf

instance : NegConfComm (Evidential S) := ⟨λ _ => rfl⟩

@[simp] theorem pro_conf (x : Evidential S) : (Conflation.conf x).pro = x.conᶜ := rfl
@[simp] theorem con_conf (x : Evidential S) : (Conflation.conf x).con = x.proᶜ := rfl

/-- The exact values are the pairs `⟨a, aᶜ⟩`. -/
theorem isExact_iff (x : Evidential S) : IsExact x ↔ x.con = x.proᶜ :=
  ⟨λ h => (congrArg Product.con h).symm,
    λ h => Product.ext (by simp [h, LatticeWithInvolution.compl_compl]) (by simpa using h.symm)⟩

/-- The consistent values: the evidence against is below the complement of the evidence for. -/
theorem isConsistent_iff (x : Evidential S) : IsConsistent x ↔ x.con ≤ x.proᶜ :=
  consistent_iff_con_le LatticeWithInvolution.compl_anti LatticeWithInvolution.compl_compl

/-- The anticonsistent values: the complement of the evidence for is below the evidence
against. -/
theorem isAnticonsistent_iff (x : Evidential S) : IsAnticonsistent x ↔ x.proᶜ ≤ x.con :=
  ⟨And.right, λ h => ⟨(LatticeWithInvolution.compl_le_compl h).trans
    (LatticeWithInvolution.compl_compl x.pro).le, h⟩⟩

end Involution

/-! ### The truth lattice as a De Morgan lattice

With Ginsberg negation as complement, the truth lattice of `S ⊙ S` is a lattice with involution,
distributive when `S` is: `FOUR` under `≤ₜ` is a De Morgan algebra ([fitting-2021] §8.3). -/

section Involutive

variable [Lattice S] [BoundedOrder S]

instance : LatticeWithInvolution (Evidential S) where
  toLattice := inferInstance
  toBoundedOrder := inferInstance
  compl := Product.neg
  compl_compl := Product.neg_neg
  compl_le_compl := Product.neg_le_neg

@[simp] theorem compl_eq_neg (x : Evidential S) : xᶜ = neg x := rfl

end Involutive

instance [DistribLattice S] [BoundedOrder S] : DeMorganAlgebra (Evidential S) :=
  { (inferInstance : DistribLattice (Evidential S)),
    (inferInstance : LatticeWithInvolution (Evidential S)) with }

end Evidential

/-- [belnap-1977]'s four-valued bilattice `FOUR = Bool ⊙ Bool`, `(for, against)`
over `Bool`. -/
abbrev FOUR := Evidential Bool

namespace FOUR

/-- `⊥`: neither — no information (a truth-value gap). -/
def U : FOUR := .mk false false
/-- `true`. -/
def T : FOUR := .mk true false
/-- `false`. -/
def F : FOUR := .mk false true
/-- `⊤`: both — inconsistent (a truth-value glut). -/
def I : FOUR := .mk true true

/-- Conflation on `FOUR` (Boolean complement). -/
@[reducible] def conf (x : FOUR) : FOUR := Evidential.conf (! ·) x
/-- The consistent (non-glut) fragment of `FOUR` — equivalently `x ≠ I`. -/
@[reducible] def Consistent (x : FOUR) : Prop := Evidential.Consistent (! ·) x
/-- The classical fragment of `FOUR` — equivalently `{F, T}`. -/
@[reducible] def IsClassical (x : FOUR) : Prop := Evidential.IsClassical (! ·) x

@[simp] theorem consistent_iff (x : FOUR) : Consistent x ↔ x ≠ I := by
  obtain ⟨a, b⟩ := x; cases a <;> cases b <;> decide

/-- The classical fragment of `FOUR` is `{F, T}` ([fitting-1994];
[schoter-1996]). -/
@[simp] theorem isClassical_iff (x : FOUR) : IsClassical x ↔ x = F ∨ x = T := by
  obtain ⟨a, b⟩ := x; cases a <;> cases b <;> decide

end FOUR

end Bilattice
