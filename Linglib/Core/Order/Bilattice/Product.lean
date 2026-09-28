module

public import Linglib.Core.Order.Bilattice.Representation
public import Linglib.Core.Order.DeMorganAlgebra.Defs
public import Linglib.Core.Order.Hom.Basic
public import Mathlib.Data.Fintype.Prod

/-!
# The Ginsberg–Fitting product bilattice

The fundamental bilattice construction ([avron-1996] Def 2.4): the product `L ⊙ R` of two
lattices carries pairs `(a, b)` recording evidence for (`a ∈ L`) and against (`b ∈ R`) a
proposition, ordered two ways.

* The truth order, more for and less against, is the carrier's `≤`. As a type
  `L ⊙ R := L × Rᵒᵈ`, so the `Prod` and `OrderDual` instances provide the truth lattice, its
  bounds `t = (⊤, ⊥)` and `f = (⊥, ⊤)`, and distributivity.
* The knowledge order, more evidence both ways, is the plain `Prod` order, installed on the
  synonym `Know (L ⊙ R)`.

The `IsInterlaced (L ⊙ R)` instance packages the four monotonicity laws ([avron-1996]
Def 2.1(3)), so the product is an interlaced bilattice ([avron-1996] Thm 2.5); the converse is
`Bilattice.decompose` (ibid. Thm 4.3). On the diagonal `L ⊙ L`, swapping the coordinates is
Ginsberg's negation ([ginsberg-1988]; [avron-1996] Thm 2.5(2)). The construction "was
essentially introduced by Ginsberg [ginsberg-1988], and further generalized by Fitting"
([avron-1996]). `[UPSTREAM]` candidate: mathlib has no bilattices.

## Main definitions

* `Bilattice.Product` (`L ⊙ R`): the carrier, with truth-order instances from `L × Rᵒᵈ` and
  knowledge-order instances on `Know (L ⊙ R)` from `L × R`.
* `Bilattice.Product.mk`, `Bilattice.Product.pro`, `Bilattice.Product.con`: the plain-coordinate
  constructor and projections.
* the `Compl (L ⊙ L)` instance: Ginsberg negation on the diagonal, with the
  `LatticeWithInvolution`, `Negation` and `DeMorganAlgebra` instances it underlies.
* `Bilattice.Product.conflation`: the conflation induced by an involution of the factor.

## Main results

* `Bilattice.Product.isExact_iff`, `Bilattice.Product.isConsistent_iff`,
  `Bilattice.Product.isAnticonsistent_iff`: the three classes in coordinates.
* `Bilattice.Product.disjoint_pro_con_inf`, `Bilattice.Product.disjoint_pro_con_sup`: pairs with
  disjoint coordinates are closed under the truth operations;
  `Bilattice.Product.isConsistent_iff_disjoint` identifies them with the consistent pairs over a
  Boolean factor.
* `Bilattice.Product.decomposeProdIso`: the representation theorem applied to a product recovers
  its factors.

## References

* [avron-1996]
* [fitting-1994]
* [fitting-2021]
* [ginsberg-1988]
-/

@[expose] public section

namespace Bilattice

/-- The Ginsberg–Fitting product `L ⊙ R` ([avron-1996] Def 2.4): pairs of
evidence for/against. The carrier order is the *truth* order (`L × Rᵒᵈ`: more
for, less against); the *knowledge* order lives on `Know (L ⊙ R)` (`L × R`:
more evidence both ways). -/
def Product (L R : Type*) : Type _ := L × Rᵒᵈ

@[inherit_doc] scoped infixl:70 " ⊙ " => Product

namespace Product

variable {L R : Type*}

/-- Build `L ⊙ R` from plain coordinates: evidence `a` for, `b` against. -/
def mk (a : L) (b : R) : L ⊙ R := (a, OrderDual.toDual b)

/-- The evidence-for coordinate. -/
def pro (x : L ⊙ R) : L := x.1

/-- The evidence-against coordinate. -/
def con (x : L ⊙ R) : R := OrderDual.ofDual x.2

@[simp] theorem pro_mk (a : L) (b : R) : pro (mk a b) = a := rfl
@[simp] theorem con_mk (a : L) (b : R) : con (mk a b) = b := rfl
@[simp] theorem mk_pro_con (x : L ⊙ R) : mk x.pro x.con = x := rfl

@[ext] theorem ext {x y : L ⊙ R} (h₁ : x.pro = y.pro) (h₂ : x.con = y.con) : x = y :=
  Prod.ext h₁ (congrArg OrderDual.toDual h₂)

/-! ### The truth order

The carrier instances, transported from `L × Rᵒᵈ`: `≤` is the truth order
([avron-1996] Def 2.4(ii)), `⊓`/`⊔` the truth meet/join (ibid. Def 2.4(iv),
(iii)), `⊤ = t`/`⊥ = f` the truth bounds (ibid. Def 2.4(vii)), and the product
of distributive lattices is distributive (ibid. Thm 2.5). -/

instance [Preorder L] [Preorder R] : Preorder (L ⊙ R) :=
  inferInstanceAs (Preorder (L × Rᵒᵈ))
instance [PartialOrder L] [PartialOrder R] : PartialOrder (L ⊙ R) :=
  inferInstanceAs (PartialOrder (L × Rᵒᵈ))
instance [Lattice L] [Lattice R] : Lattice (L ⊙ R) :=
  inferInstanceAs (Lattice (L × Rᵒᵈ))
instance [DistribLattice L] [DistribLattice R] : DistribLattice (L ⊙ R) :=
  inferInstanceAs (DistribLattice (L × Rᵒᵈ))
instance [Preorder L] [Preorder R] [BoundedOrder L] [BoundedOrder R] :
    BoundedOrder (L ⊙ R) :=
  inferInstanceAs (BoundedOrder (L × Rᵒᵈ))
instance [Preorder L] [Preorder R] [DecidableLE L] [DecidableLE R] :
    DecidableLE (L ⊙ R) :=
  inferInstanceAs (DecidableLE (L × Rᵒᵈ))
instance [DecidableEq L] [DecidableEq R] : DecidableEq (L ⊙ R) :=
  inferInstanceAs (DecidableEq (L × Rᵒᵈ))
instance [Fintype L] [Fintype R] : Fintype (L ⊙ R) :=
  inferInstanceAs (Fintype (L × Rᵒᵈ))

/-- The truth order in plain coordinates: more for, less against
([avron-1996] Def 2.4(ii)). -/
@[simp] theorem mk_le_mk [Preorder L] [Preorder R] {a₁ a₂ : L} {b₁ b₂ : R} :
    mk a₁ b₁ ≤ mk a₂ b₂ ↔ a₁ ≤ a₂ ∧ b₂ ≤ b₁ := Iff.rfl

/-- Truth meet `∧` in plain coordinates ([avron-1996] Def 2.4(iv)). -/
@[simp] theorem mk_inf_mk [Lattice L] [Lattice R] {a₁ a₂ : L} {b₁ b₂ : R} :
    mk a₁ b₁ ⊓ mk a₂ b₂ = mk (a₁ ⊓ a₂) (b₁ ⊔ b₂) := rfl

/-- Truth join `∨` in plain coordinates ([avron-1996] Def 2.4(iii)). -/
@[simp] theorem mk_sup_mk [Lattice L] [Lattice R] {a₁ a₂ : L} {b₁ b₂ : R} :
    mk a₁ b₁ ⊔ mk a₂ b₂ = mk (a₁ ⊔ a₂) (b₁ ⊓ b₂) := rfl

/-- The truth top `t = (⊤, ⊥)` ([avron-1996] Def 2.4(vii)). -/
theorem top_eq [Preorder L] [Preorder R] [BoundedOrder L] [BoundedOrder R] :
    (⊤ : L ⊙ R) = mk ⊤ ⊥ := rfl

/-- The truth bottom `f = (⊥, ⊤)` ([avron-1996] Def 2.4(vii)). -/
theorem bot_eq [Preorder L] [Preorder R] [BoundedOrder L] [BoundedOrder R] :
    (⊥ : L ⊙ R) = mk ⊥ ⊤ := rfl

/-- The truth order on the projections. -/
theorem le_def [Preorder L] [Preorder R] {x y : L ⊙ R} :
    x ≤ y ↔ x.pro ≤ y.pro ∧ y.con ≤ x.con := Iff.rfl

section Proj

variable [Lattice L] [Lattice R] (x y : L ⊙ R)

@[simp] theorem pro_inf : (x ⊓ y).pro = x.pro ⊓ y.pro := rfl
@[simp] theorem con_inf : (x ⊓ y).con = x.con ⊔ y.con := rfl
@[simp] theorem pro_sup : (x ⊔ y).pro = x.pro ⊔ y.pro := rfl
@[simp] theorem con_sup : (x ⊔ y).con = x.con ⊓ y.con := rfl

end Proj

section ProjBounds

variable [Preorder L] [Preorder R] [BoundedOrder L] [BoundedOrder R]

@[simp] theorem pro_top : (⊤ : L ⊙ R).pro = ⊤ := rfl
@[simp] theorem con_top : (⊤ : L ⊙ R).con = ⊥ := rfl
@[simp] theorem pro_bot : (⊥ : L ⊙ R).pro = ⊥ := rfl
@[simp] theorem con_bot : (⊥ : L ⊙ R).con = ⊤ := rfl

end ProjBounds

/-! ### The knowledge order

The instances on the synonym `Know (L ⊙ R)`, transported from the plain
`Prod` order on `L × R`; `⊓ₖ`/`⊔ₖ`/`≤ₖ` are then the generic knowledge
operations of `Core.Order.Bilattice.Defs`. -/

instance [Preorder L] [Preorder R] : Preorder (Know (L ⊙ R)) :=
  inferInstanceAs (Preorder (L × R))
instance [PartialOrder L] [PartialOrder R] : PartialOrder (Know (L ⊙ R)) :=
  inferInstanceAs (PartialOrder (L × R))
instance [Lattice L] [Lattice R] : Lattice (Know (L ⊙ R)) :=
  inferInstanceAs (Lattice (L × R))
instance [DistribLattice L] [DistribLattice R] : DistribLattice (Know (L ⊙ R)) :=
  inferInstanceAs (DistribLattice (L × R))
instance [Preorder L] [Preorder R] [BoundedOrder L] [BoundedOrder R] :
    BoundedOrder (Know (L ⊙ R)) :=
  inferInstanceAs (BoundedOrder (L × R))
instance [Preorder L] [Preorder R] [DecidableLE L] [DecidableLE R] :
    DecidableLE (Know (L ⊙ R)) :=
  inferInstanceAs (DecidableLE (L × R))

/-- The knowledge order in plain coordinates: more evidence both ways
([avron-1996] Def 2.4). -/
@[simp] theorem mk_kLE_mk [Preorder L] [Preorder R] {a₁ a₂ : L} {b₁ b₂ : R} :
    mk a₁ b₁ ≤ₖ mk a₂ b₂ ↔ a₁ ≤ a₂ ∧ b₁ ≤ b₂ := Iff.rfl

/-- Knowledge meet `⊓ₖ` (consensus) in plain coordinates ([avron-1996] Def 2.4). -/
@[simp] theorem mk_kInf_mk [Lattice L] [Lattice R] {a₁ a₂ : L} {b₁ b₂ : R} :
    mk a₁ b₁ ⊓ₖ mk a₂ b₂ = mk (a₁ ⊓ a₂) (b₁ ⊓ b₂) := rfl

/-- Knowledge join `⊔ₖ` (gullibility) in plain coordinates ([avron-1996] Def 2.4). -/
@[simp] theorem mk_kSup_mk [Lattice L] [Lattice R] {a₁ a₂ : L} {b₁ b₂ : R} :
    (mk a₁ b₁ ⊔ₖ mk a₂ b₂) = mk (a₁ ⊔ a₂) (b₁ ⊔ b₂) := rfl

/-- The knowledge top `⊤ = (⊤, ⊤)` ([avron-1996] Def 2.4(vii)). -/
theorem know_top_eq [Preorder L] [Preorder R] [BoundedOrder L] [BoundedOrder R] :
    (⊤ : Know (L ⊙ R)) = toKnow (mk ⊤ ⊤) := rfl

/-- The knowledge bottom `⊥ = (⊥, ⊥)` ([avron-1996] Def 2.4(vii)). -/
theorem know_bot_eq [Preorder L] [Preorder R] [BoundedOrder L] [BoundedOrder R] :
    (⊥ : Know (L ⊙ R)) = toKnow (mk ⊥ ⊥) := rfl

/-- The knowledge order on the projections. -/
theorem kLE_iff [Preorder L] [Preorder R] {x y : L ⊙ R} :
    x ≤ₖ y ↔ x.pro ≤ y.pro ∧ x.con ≤ y.con := Iff.rfl

section KProj

variable [Lattice L] [Lattice R] (x y : L ⊙ R)

@[simp] theorem pro_kInf : (x ⊓ₖ y).pro = x.pro ⊓ y.pro := rfl
@[simp] theorem con_kInf : (x ⊓ₖ y).con = x.con ⊓ y.con := rfl
@[simp] theorem pro_kSup : (x ⊔ₖ y).pro = x.pro ⊔ y.pro := rfl
@[simp] theorem con_kSup : (x ⊔ₖ y).con = x.con ⊔ y.con := rfl

end KProj

/-- **The product is an interlaced bilattice** ([avron-1996] Thm 2.5): each
order's meet and join are monotone for the other order. -/
instance [Lattice L] [Lattice R] : IsInterlaced (L ⊙ R) where
  inf_kmono h _ := ⟨inf_le_inf h.1 le_rfl, sup_le_sup h.2 le_rfl⟩
  sup_kmono h _ := ⟨sup_le_sup h.1 le_rfl, inf_le_inf h.2 le_rfl⟩
  kInf_tmono h _ := ⟨inf_le_inf h.1 le_rfl, inf_le_inf h.2 le_rfl⟩
  kSup_tmono h _ := ⟨sup_le_sup h.1 le_rfl, sup_le_sup h.2 le_rfl⟩

/-! ### Negation

On the diagonal `L ⊙ L`, Ginsberg's negation swaps the coordinates ([ginsberg-1988];
[avron-1996] Thm 2.5(2)). It needs no order on `L`, so it is a bare `Compl` instance. Over a
bounded lattice it is the involution of a `LatticeWithInvolution` on the truth lattice and a
bilattice `Negation`, and over a distributive lattice the truth lattice is a De Morgan algebra. -/

section Negation

/-- Ginsberg negation on `L ⊙ L` swaps the evidence for and the evidence against. -/
instance : Compl (L ⊙ L) := ⟨fun x ↦ mk x.con x.pro⟩

@[simp] theorem pro_compl (x : L ⊙ L) : (xᶜ).pro = x.con := rfl
@[simp] theorem con_compl (x : L ⊙ L) : (xᶜ).con = x.pro := rfl
@[simp] theorem mk_compl (a b : L) : (mk a b)ᶜ = mk b a := rfl
@[simp] protected theorem compl_compl (x : L ⊙ L) : xᶜᶜ = x := rfl

/-- Negation reverses the truth order ([avron-1996] Def 2.3(ii)). -/
protected theorem compl_le_compl [Preorder L] {x y : L ⊙ L} (h : x ≤ y) : yᶜ ≤ xᶜ := ⟨h.2, h.1⟩

/-- Negation preserves the knowledge order ([avron-1996] Def 2.3(iii)). -/
protected theorem compl_kLE_compl [Preorder L] {x y : L ⊙ L} (h : x ≤ₖ y) : xᶜ ≤ₖ yᶜ :=
  ⟨h.2, h.1⟩

instance [Lattice L] [BoundedOrder L] : LatticeWithInvolution (L ⊙ L) where
  toCompl := inferInstance
  compl_compl := Product.compl_compl
  compl_le_compl := Product.compl_le_compl

/-- Ginsberg's swap is a negation on the diagonal ([avron-1996] Thm 2.5(2)). -/
instance [Lattice L] [BoundedOrder L] : Negation (L ⊙ L) := ⟨Product.compl_kLE_compl⟩

/-- Over a distributive lattice the truth lattice of `L ⊙ L` is a De Morgan algebra
([fitting-2021] §8.3). -/
instance [DistribLattice L] [BoundedOrder L] : DeMorganAlgebra (L ⊙ L) where

end Negation

/-! ### Conflation

Swapping the coordinates and applying an order-reversing involution of the factor to each is a
conflation of `L ⊙ L` ([fitting-1994] §7, [fitting-2021] §8.8). The involution of a
`LatticeWithInvolution` factor gives the conflation instance, which commutes with Ginsberg
negation, and the exact, consistent and anticonsistent values read off the coordinates. -/

section Conflation

/-- The conflation `⟨a, b⟩ ↦ ⟨f b, f a⟩` of `L ⊙ L` induced by an order-reversing involution `f`
of the factor. -/
abbrev conflation [Preorder L] (f : L → L) (hf : Function.Involutive f) (ha : Antitone f) :
    Conflation (L ⊙ L) where
  conf x := mk (f x.con) (f x.pro)
  conf_conf x := ext (hf x.pro) (hf x.con)
  conf_le_conf h := ⟨ha h.2, ha h.1⟩
  conf_kLE_conf h := ⟨ha h.2, ha h.1⟩

variable [LatticeWithInvolution L]

instance : Conflation (L ⊙ L) :=
  conflation (·ᶜ) LatticeWithInvolution.compl_compl LatticeWithInvolution.compl_anti

instance : NegConfComm (L ⊙ L) := ⟨fun _ ↦ rfl⟩

@[simp] theorem pro_conf (x : L ⊙ L) : (conf x).pro = x.conᶜ := rfl
@[simp] theorem con_conf (x : L ⊙ L) : (conf x).con = x.proᶜ := rfl

/-- The exact values are the pairs `⟨a, aᶜ⟩`. -/
theorem isExact_iff (x : L ⊙ L) : IsExact x ↔ x.con = x.proᶜ :=
  ⟨fun h ↦ (congrArg con h.eq).symm,
    fun h ↦ ext (by simp [h, LatticeWithInvolution.compl_compl]) h.symm⟩

/-- The consistent values: the evidence against is below the complement of the evidence for. -/
theorem isConsistent_iff (x : L ⊙ L) : IsConsistent x ↔ x.con ≤ x.proᶜ :=
  ⟨And.right, fun h ↦ ⟨LatticeWithInvolution.le_compl_comm.1 h, h⟩⟩

/-- The anticonsistent values: the complement of the evidence for is below the evidence
against. -/
theorem isAnticonsistent_iff (x : L ⊙ L) : IsAnticonsistent x ↔ x.proᶜ ≤ x.con :=
  ⟨And.right, fun h ↦ ⟨(LatticeWithInvolution.compl_le_compl h).trans
    (LatticeWithInvolution.compl_compl x.pro).le, h⟩⟩

end Conflation

/-! ### Disjoint coordinates

The pairs whose evidence for and against are disjoint are closed under the truth operations over
a distributive factor, and under negation by the symmetry of `Disjoint`. Over a Boolean factor disjointness is Fitting's consistency;
over a De Morgan factor it is stronger (`⟨indet, indet⟩` in `Trivalent ⊙ Trivalent` is consistent),
and over a Heyting factor, whose pseudocomplement is no involution, it is the only notion
available. -/

section Disjoint

variable [DistribLattice L] [OrderBot L] {x y : L ⊙ L}

theorem disjoint_pro_con_inf (hx : Disjoint x.pro x.con) (hy : Disjoint y.pro y.con) :
    Disjoint (x ⊓ y).pro (x ⊓ y).con :=
  (hx.inf_left _).sup_right (hy.inf_left' _)

theorem disjoint_pro_con_sup (hx : Disjoint x.pro x.con) (hy : Disjoint y.pro y.con) :
    Disjoint (x ⊔ y).pro (x ⊔ y).con :=
  (hx.inf_right _).sup_left (hy.inf_right' _)

end Disjoint

/-- Over a Boolean factor, Fitting's consistency is disjointness of the evidence for and against. -/
theorem isConsistent_iff_disjoint [BooleanAlgebra L] (x : L ⊙ L) :
    IsConsistent x ↔ Disjoint x.pro x.con :=
  (isConsistent_iff x).trans le_compl_iff_disjoint_left

/-! ### Recovering the factors

The abstract decomposition applied to a product recovers its factors: the
knowledge ideals below the truth bounds are order-isomorphic to `L` and `R`
(`iicKTopIso`/`iicKBotIso`), so `Bilattice.decompose` closes the representation
loop, `Know (L ⊙ R) ≃o L × R` (`decomposeProdIso`) — the concrete half of
[avron-1996] Thm 4.3's uniqueness clause. -/

section FactorRecovery

variable [PartialOrder L] [PartialOrder R] [BoundedOrder L] [BoundedOrder R]

/-- The knowledge ideal below the truth top is the evidence-for factor,
`L_{L ⊙ R} ≃o L`. -/
def iicKTopIso : Set.Iic (toKnow (⊤ : L ⊙ R)) ≃o L where
  toFun x := (ofKnow x.1).pro
  invFun a := ⟨toKnow (mk a ⊥), ⟨le_top, le_rfl⟩⟩
  left_inv x := Subtype.ext (ext rfl
    (le_bot_iff.mp (show (ofKnow x.1).con ≤ ⊥ from x.2.2)).symm)
  right_inv _ := rfl
  map_rel_iff' {x _} := ⟨fun h => ⟨h, (le_bot_iff.mp x.2.2).le.trans bot_le⟩, And.left⟩

/-- The knowledge ideal below the truth bottom is the evidence-against factor,
`R_{L ⊙ R} ≃o R`. -/
def iicKBotIso : Set.Iic (toKnow (⊥ : L ⊙ R)) ≃o R where
  toFun x := (ofKnow x.1).con
  invFun b := ⟨toKnow (mk ⊥ b), ⟨le_rfl, le_top⟩⟩
  left_inv x := Subtype.ext (ext
    (le_bot_iff.mp (show (ofKnow x.1).pro ≤ ⊥ from x.2.1)).symm rfl)
  right_inv _ := rfl
  map_rel_iff' {x _} := ⟨fun h => ⟨(le_bot_iff.mp x.2.1).le.trans bot_le, h⟩, And.right⟩

end FactorRecovery

/-- **The representation loop closed**: `Bilattice.decompose` applied to a
product recovers the factors, `Know (L ⊙ R) ≃o L × R` — the concrete half of
[avron-1996] Thm 4.3's uniqueness clause. -/
def decomposeProdIso [Lattice L] [Lattice R] [BoundedOrder L] [BoundedOrder R] :
    Know (L ⊙ R) ≃o L × R :=
  decompose.trans (iicKTopIso.prodCongr iicKBotIso)

end Product

end Bilattice
