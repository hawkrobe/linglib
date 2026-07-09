import Linglib.Core.Logic.Bilattice.Interlaced

/-!
# The Ginsberg–Fitting product bilattice
[avron-1996] [ginsberg-1988]

The fundamental bilattice construction ([avron-1996] Def 2.4): the **product**
`L ⊙ R` of two lattices carries pairs `(a, b)` recording evidence *for*
(`a ∈ L`) and *against* (`b ∈ R`) a proposition, ordered two ways:

* the **truth** order — more for, less against — is the carrier's `≤`: as a
  type, `L ⊙ R := L × Rᵒᵈ`, so the `Prod`/`OrderDual` instances provide the
  truth lattice, its bounds `t = (⊤, ⊥)` and `f = (⊥, ⊤)`, and distributivity
  outright;
* the **knowledge** order — more evidence both ways — is the plain `Prod`
  order, installed on the synonym `Know (L ⊙ R)`
  (see `Core.Logic.Bilattice.Interlaced`).

The `Interlaced (L ⊙ R)` instance packages the four monotonicity laws
([avron-1996] Def 2.1(3)): the product is an interlaced bilattice — the
constructive half of the structure theory ([avron-1996] Thm 2.5). The converse
representation theorem is `Bilattice.decompose` (ibid. Thm 4.3). On the
diagonal `L ⊙ L`, swapping the coordinates is Ginsberg's negation
([ginsberg-1988]; [avron-1996] Thm 2.5(2)).

The construction "was essentially introduced by Ginsberg [ginsberg-1988], and
further generalized by Fitting" ([avron-1996]). The algebraic-logic literature
sometimes calls the diagonal case with swap-negation a *twist structure*; that
term names an older single-factor lineage, so this file keeps Avron's name.
`[UPSTREAM]` candidate (mathlib has no bilattices).

## Main definitions

* `Bilattice.Product` (`L ⊙ R`) — the carrier, with truth-order instances from
  `L × Rᵒᵈ` and knowledge-order instances on `Know (L ⊙ R)` from `L × R`
* `Product.mk`/`pro`/`con` — plain-coordinate constructor and projections
* the `Interlaced (L ⊙ R)` instance — the four interlacing laws
* `Product.neg` — Ginsberg negation on the diagonal `L ⊙ L`
-/

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

/-! ### The knowledge order

The instances on the synonym `Know (L ⊙ R)`, transported from the plain
`Prod` order on `L × R`; `⊗`/`⊕`/`≤ₖ` are then the generic knowledge
operations of `Core.Logic.Bilattice.Interlaced`. -/

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

/-- Knowledge meet `⊗` (consensus) in plain coordinates ([avron-1996] Def 2.4). -/
@[simp] theorem mk_kInf_mk [Lattice L] [Lattice R] {a₁ a₂ : L} {b₁ b₂ : R} :
    mk a₁ b₁ ⊗ mk a₂ b₂ = mk (a₁ ⊓ a₂) (b₁ ⊓ b₂) := rfl

/-- Knowledge join `⊕` (gullibility) in plain coordinates ([avron-1996] Def 2.4). -/
@[simp] theorem mk_kSup_mk [Lattice L] [Lattice R] {a₁ a₂ : L} {b₁ b₂ : R} :
    (mk a₁ b₁ ⊕ mk a₂ b₂ : L ⊙ R) = mk (a₁ ⊔ a₂) (b₁ ⊔ b₂) := rfl

/-- The knowledge top `⊤ = (⊤, ⊤)` ([avron-1996] Def 2.4(vii)). -/
theorem know_top_eq [Preorder L] [Preorder R] [BoundedOrder L] [BoundedOrder R] :
    (⊤ : Know (L ⊙ R)) = toKnow (mk ⊤ ⊤) := rfl

/-- The knowledge bottom `⊥ = (⊥, ⊥)` ([avron-1996] Def 2.4(vii)). -/
theorem know_bot_eq [Preorder L] [Preorder R] [BoundedOrder L] [BoundedOrder R] :
    (⊥ : Know (L ⊙ R)) = toKnow (mk ⊥ ⊥) := rfl

/-- **The product is an interlaced bilattice** ([avron-1996] Thm 2.5): each
order's meet and join are monotone for the other order. -/
instance [Lattice L] [Lattice R] : Interlaced (L ⊙ R) where
  inf_kmono h _ := ⟨inf_le_inf h.1 le_rfl, sup_le_sup h.2 le_rfl⟩
  sup_kmono h _ := ⟨sup_le_sup h.1 le_rfl, inf_le_inf h.2 le_rfl⟩
  kInf_tmono h _ := ⟨inf_le_inf h.1 le_rfl, inf_le_inf h.2 le_rfl⟩
  kSup_tmono h _ := ⟨sup_le_sup h.1 le_rfl, sup_le_sup h.2 le_rfl⟩

/-! ### Negation

On the diagonal `L ⊙ L`, Ginsberg's negation swaps the coordinates: an
involution reversing the truth order and preserving the knowledge order
([ginsberg-1988]; [avron-1996] Thm 2.5(2)). -/

/-- Ginsberg negation on `L ⊙ L`: swap evidence for/against. -/
def neg (x : L ⊙ L) : L ⊙ L := mk x.con x.pro

@[simp] theorem neg_mk (a b : L) : neg (mk a b) = mk b a := rfl
@[simp] theorem neg_neg (x : L ⊙ L) : neg (neg x) = x := rfl

variable [Preorder L]

/-- Negation reverses the truth order ([avron-1996] Def 2.3(ii)). -/
theorem neg_le_neg {x y : L ⊙ L} (h : x ≤ y) : neg y ≤ neg x := ⟨h.2, h.1⟩

/-- Negation preserves the knowledge order ([avron-1996] Def 2.3(iii)). -/
theorem neg_kLE_neg {x y : L ⊙ L} (h : x ≤ₖ y) : neg x ≤ₖ neg y := ⟨h.2, h.1⟩

end Product

end Bilattice
