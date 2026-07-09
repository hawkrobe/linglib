import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Interval.Set.Basic

/-!
# Interlaced bilattices (abstract)
[avron-1996]

An *interlaced bilattice* ([avron-1996] Def 2.1) is one carrier with two bounded
lattice orders — a **truth** order `≤_t` and a **knowledge** order `≤_k` — such
that all four lattice operations are monotone with respect to *both* orders. The
interlacing condition is due to [fitting-1990]; [avron-1996], cited throughout
for statement locations, develops its structure theory.

To carry two lattice structures on one carrier without an instance clash, we use
the `OrderDual`-style trick: the truth lattice is the carrier's own
`[Lattice B] [BoundedOrder B]`, while the knowledge lattice lives on a type
synonym `Know B` (a distinct type head, so `[Lattice (Know B)]` is a separate
instance). The truth meet/join are `⊓`/`⊔`; the knowledge meet/join (consensus
`⊗`, gullibility `⊕`) are written through the synonym.

This file sets up the synonym, the interlacing mixin, and proves the
**representation theorem** ([avron-1996] Thm 4.3) for any interlaced bilattice:
the knowledge lattice decomposes as the Ginsberg–Fitting product of the
knowledge-order principal ideals of the truth bounds (`decompose`), and the
truth order is recovered from the decomposition (`le_iff_kInf_top_kInf_bot`).
Unlike `Core.Logic.Bilattice.Representation` (which handles the distributive
special case via whole-lattice distributivity), the key identities (Cor 3.5,
Cor 3.8) are derived from interlacing alone, by truth-antisymmetry and a fiber
lemma rather than Avron's interval argument. The constructive converse — the
product of two lattices is interlaced — is `Core.Logic.Bilattice.Product`.
`[UPSTREAM]` candidate (mathlib has no bilattices).

## Main definitions / results

* `Bilattice.Know` — the knowledge-order synonym; `toKnow`/`ofKnow` the casts
* `Bilattice.kInf`/`kSup` — knowledge meet `⊗` / join `⊕` (scoped `⊗`/`⊕`)
* `Bilattice.kLE` — knowledge order `≤_k` (scoped `≤ₖ`)
* `Bilattice.Interlaced` — the four interlacing laws (mixin, [avron-1996] Def 2.1)
* `Bilattice.inf_kT_sup_inf_kF` — Cor 3.8: `X = (X ⊗ t) ⊕ (X ⊗ f)`
* `Bilattice.isCompl_truthBounds` — Cor 3.5: `t`, `f` are knowledge-complementary
* `Bilattice.decompose` — Thm 4.3: `Know B ≃o Iic t × Iic f`
* `Bilattice.le_iff_kInf_top_kInf_bot` — Thm 4.3, truth side: `x ≤ y` iff the
  `t`-components grow and the `f`-components shrink in the knowledge order
* `Bilattice.Negation` — negation mixin ([avron-1996] Def 2.3), with the
  derived bounds/De Morgan/knowledge-homomorphism equations
* `Bilattice.negIicIso`, `neg_kInf_top` — Prop 4.7: with a negation the two
  ideals are isomorphic (`λ x, ∼x : L_B ≃o R_B`) and the decomposition is a
  diagonal product
* `Bilattice.Conflation` — the knowledge-order inversion ([fitting-2021] §8.4),
  with `IsConsistent`/`IsAnticonsistent`/`IsExact` ([fitting-2021] Def 8.5.1)
  and their closure, interpolation, and antichain laws (ibid. Props 8.5.2–8.5.4)

## TODO

Package [avron-1996] Prop 4.7's full equivalence `⟨B, ∼⟩ ≅ L_B ⊙ L_B` (its two
proof steps are `negIicIso` and `neg_kInf_top`); abstract uniqueness of the
factors up to isomorphism (ibid. Thm 4.3; the concrete half for products is
`Bilattice.Product.decomposeProdIso`).
-/

universe u

variable {B : Type u}

namespace Bilattice

/-- The knowledge-order synonym of a bilattice carrier (cf. `OrderDual`). It is
the same underlying type as `B`, but a distinct type head, so it can carry the
*knowledge* lattice as a separate instance from `B`'s *truth* lattice. -/
def Know (B : Type u) : Type u := B

/-- Cast into the knowledge synonym. -/
def toKnow : B ≃ Know B := Equiv.refl B
/-- Cast out of the knowledge synonym. -/
def ofKnow : Know B ≃ B := Equiv.refl B

@[simp] theorem toKnow_ofKnow (x : Know B) : toKnow (ofKnow x) = x := rfl
@[simp] theorem ofKnow_toKnow (x : B) : ofKnow (toKnow x) = x := rfl

instance [DecidableEq B] : DecidableEq (Know B) := inferInstanceAs (DecidableEq B)

section Defs

variable [Lattice (Know B)]

/-- Knowledge meet `⊗` (consensus): the meet in the knowledge lattice. -/
def kInf (x y : B) : B := ofKnow (toKnow x ⊓ toKnow y)
/-- Knowledge join `⊕` (gullibility): the join in the knowledge lattice. -/
def kSup (x y : B) : B := ofKnow (toKnow x ⊔ toKnow y)

@[inherit_doc] scoped infixl:70 " ⊗ " => kInf
@[inherit_doc] scoped infixl:65 " ⊕ " => kSup

@[simp] theorem toKnow_kInf (x y : B) : toKnow (x ⊗ y) = toKnow x ⊓ toKnow y := rfl
@[simp] theorem toKnow_kSup (x y : B) : toKnow (x ⊕ y) = toKnow x ⊔ toKnow y := rfl

/-- Knowledge meet is idempotent. -/
theorem kInf_self (x : B) : x ⊗ x = x :=
  toKnow.injective (by simp only [toKnow_kInf, inf_idem])

/-- Knowledge join is idempotent. -/
theorem kSup_self (x : B) : (x ⊕ x : B) = x :=
  toKnow.injective (by simp only [toKnow_kSup, sup_idem])

/-- Knowledge meet is commutative. -/
theorem kInf_comm (x y : B) : x ⊗ y = y ⊗ x :=
  toKnow.injective (by simp only [toKnow_kInf, inf_comm])

/-- Knowledge join is commutative. -/
theorem kSup_comm (x y : B) : (x ⊕ y : B) = y ⊕ x :=
  toKnow.injective (by simp only [toKnow_kSup, sup_comm])

/-- Knowledge absorption: `x ⊕ (x ⊗ y) = x`. -/
theorem kSup_kInf_self (x y : B) : (x ⊕ (x ⊗ y) : B) = x :=
  toKnow.injective (by simp only [toKnow_kSup, toKnow_kInf, sup_inf_self])

/-- Knowledge absorption: `x ⊗ (x ⊕ y) = x`. -/
theorem kInf_kSup_self (x y : B) : (x ⊗ (x ⊕ y) : B) = x :=
  toKnow.injective (by simp only [toKnow_kInf, toKnow_kSup, inf_sup_self])

end Defs

section KLE

variable [Preorder (Know B)]

/-- Knowledge order `≤_k`. -/
def kLE (x y : B) : Prop := toKnow x ≤ toKnow y

@[inherit_doc] scoped infix:50 " ≤ₖ " => kLE

theorem kLE_def {x y : B} : x ≤ₖ y ↔ toKnow x ≤ toKnow y := Iff.rfl

@[refl] theorem kLE_refl (x : B) : x ≤ₖ x := le_rfl
theorem kLE_trans {x y z : B} (h₁ : x ≤ₖ y) (h₂ : y ≤ₖ z) : x ≤ₖ z := le_trans h₁ h₂

instance : Trans (kLE (B := B)) (kLE (B := B)) (kLE (B := B)) := ⟨kLE_trans⟩

instance [DecidableLE (Know B)] : DecidableRel (kLE (B := B)) :=
  fun x y => inferInstanceAs (Decidable (toKnow x ≤ toKnow y))

end KLE

section KLEAntisymm

variable [PartialOrder (Know B)]

theorem kLE_antisymm {x y : B} (h₁ : x ≤ₖ y) (h₂ : y ≤ₖ x) : x = y :=
  toKnow.injective (le_antisymm h₁ h₂)

end KLEAntisymm

/-! ### The interlacing mixin -/

open scoped Bilattice in
/-- The four **interlacing** laws ([avron-1996] Def 2.1(3)): each operation is
monotone w.r.t. the *other* order. The same-order monotonicities are automatic
(an operation is monotone for its own order). -/
class Interlaced (B : Type u) [Lattice B] [Lattice (Know B)] : Prop where
  /-- truth meet `∧ = ⊓` is `≤_k`-monotone -/
  inf_kmono : ∀ {x y : B}, x ≤ₖ y → ∀ z, (x ⊓ z) ≤ₖ (y ⊓ z)
  /-- truth join `∨ = ⊔` is `≤_k`-monotone -/
  sup_kmono : ∀ {x y : B}, x ≤ₖ y → ∀ z, (x ⊔ z) ≤ₖ (y ⊔ z)
  /-- knowledge meet `⊗` is `≤_t`-monotone -/
  kInf_tmono : ∀ {x y : B}, x ≤ y → ∀ z, (x ⊗ z) ≤ (y ⊗ z)
  /-- knowledge join `⊕` is `≤_t`-monotone -/
  kSup_tmono : ∀ {x y : B}, x ≤ y → ∀ z, (x ⊕ z) ≤ (y ⊕ z)

/-! ### Negation

A **negation** on a bilattice ([avron-1996] Def 2.3) is an involution reversing
the truth order and preserving the knowledge order. The note following Def 2.3
derives the equations used below: negation exchanges the truth bounds
(`∼t = f`), anti-commutes with the truth lattice operations (De Morgan), and is
an automorphism of the knowledge lattice. -/

section Negation

section Defs

variable [Preorder B] [Preorder (Know B)]

/-- A **negation** ([avron-1996] Def 2.3): an involution (i) that reverses the
truth order (ii) and preserves the knowledge order (iii). -/
class Negation (B : Type u) [Preorder B] [Preorder (Know B)] : Type u where
  /-- The negation operation `∼`. -/
  neg : B → B
  /-- Negation is an involution ([avron-1996] Def 2.3(i)). -/
  neg_neg : ∀ a : B, neg (neg a) = a
  /-- Negation reverses the truth order ([avron-1996] Def 2.3(ii)). -/
  neg_le_neg : ∀ {a b : B}, a ≤ b → neg b ≤ neg a
  /-- Negation preserves the knowledge order ([avron-1996] Def 2.3(iii)). -/
  neg_kLE_neg : ∀ {a b : B}, a ≤ₖ b → neg a ≤ₖ neg b

export Negation (neg neg_neg neg_le_neg neg_kLE_neg)

attribute [simp] Negation.neg_neg

variable [Negation B]

theorem neg_le_neg_iff {a b : B} : neg b ≤ neg a ↔ a ≤ b :=
  ⟨fun h => by simpa only [neg_neg] using neg_le_neg h, neg_le_neg⟩

theorem neg_kLE_neg_iff {a b : B} : neg a ≤ₖ neg b ↔ a ≤ₖ b :=
  ⟨fun h => by simpa only [neg_neg] using neg_kLE_neg h, neg_kLE_neg⟩

/-- Negation as an antitone automorphism of the truth order, `B ≃o Bᵒᵈ`. -/
def Negation.dualIso : B ≃o Bᵒᵈ where
  toFun a := OrderDual.toDual (neg a)
  invFun a := neg (OrderDual.ofDual a)
  left_inv := neg_neg
  right_inv _ := congrArg OrderDual.toDual (neg_neg _)
  map_rel_iff' := neg_le_neg_iff

/-- Negation as an automorphism of the knowledge order. -/
def Negation.knowIso : Know B ≃o Know B where
  toFun X := toKnow (neg (ofKnow X))
  invFun X := toKnow (neg (ofKnow X))
  left_inv _ := congrArg toKnow (neg_neg _)
  right_inv _ := congrArg toKnow (neg_neg _)
  map_rel_iff' := neg_kLE_neg_iff

end Defs

section Bounds

variable [PartialOrder B] [Preorder (Know B)] [BoundedOrder B] [Negation B]

/-- Negation exchanges the truth bounds, `∼t = f` (note following
[avron-1996] Def 2.3). -/
@[simp] theorem neg_top : neg (⊤ : B) = ⊥ :=
  le_antisymm (by simpa only [neg_neg] using neg_le_neg (le_top : neg (⊥ : B) ≤ ⊤)) bot_le

/-- Negation exchanges the truth bounds, `∼f = t` (note following
[avron-1996] Def 2.3). -/
@[simp] theorem neg_bot : neg (⊥ : B) = ⊤ :=
  le_antisymm le_top (by simpa only [neg_neg] using neg_le_neg (bot_le : (⊥ : B) ≤ neg ⊤))

end Bounds

section DeMorgan

variable [Lattice B] [Preorder (Know B)] [Negation B]

/-- De Morgan: `∼(a ∧ b) = ∼a ∨ ∼b` (note following [avron-1996] Def 2.3). -/
theorem neg_inf (a b : B) : neg (a ⊓ b) = neg a ⊔ neg b :=
  OrderDual.toDual.injective (Negation.dualIso.map_inf a b)

/-- De Morgan: `∼(a ∨ b) = ∼a ∧ ∼b` (note following [avron-1996] Def 2.3). -/
theorem neg_sup (a b : B) : neg (a ⊔ b) = neg a ⊓ neg b :=
  OrderDual.toDual.injective (Negation.dualIso.map_sup a b)

end DeMorgan

section KnowHom

variable [Preorder B] [Lattice (Know B)] [Negation B]

/-- Negation is a homomorphism of the knowledge meet, `∼(a ⊗ b) = ∼a ⊗ ∼b`
(note following [avron-1996] Def 2.3). -/
theorem neg_kInf (a b : B) : neg (a ⊗ b) = neg a ⊗ neg b :=
  toKnow.injective (Negation.knowIso.map_inf (toKnow a) (toKnow b))

/-- Negation is a homomorphism of the knowledge join, `∼(a ⊕ b) = ∼a ⊕ ∼b`
(note following [avron-1996] Def 2.3). -/
theorem neg_kSup (a b : B) : (neg (a ⊕ b) : B) = neg a ⊕ neg b :=
  toKnow.injective (Negation.knowIso.map_sup (toKnow a) (toKnow b))

end KnowHom

end Negation

/-! ### Conflation

The knowledge-order counterpart of negation ([fitting-1994]'s coinage; axioms
as in [fitting-2021]): an involution *preserving* the truth order and
*reversing* the knowledge order. With both inversions present, the carrier
splits into **consistent** (`a ≤ₖ −a`), **anticonsistent** (`−a ≤ₖ a`), and
**exact** (`−a = a`) values — the abstract forms of Kleene's, Priest's, and the
classical value spaces inside a bilattice ([fitting-2021] Def 8.5.1) — and the
three classes are closed under the truth operations and (when negation and
conflation commute) negation. -/

section Conflation

section Defs

variable [Preorder B] [Preorder (Know B)]

/-- A **conflation** ([fitting-2021] §8.4): an involution (Con-3) that
preserves the truth order (Con-2) and reverses the knowledge order (Con-1). -/
class Conflation (B : Type u) [Preorder B] [Preorder (Know B)] : Type u where
  /-- The conflation operation `−`. -/
  conf : B → B
  /-- Conflation is an involution (Con-3). -/
  conf_conf : ∀ a : B, conf (conf a) = a
  /-- Conflation preserves the truth order (Con-2). -/
  conf_le_conf : ∀ {a b : B}, a ≤ b → conf a ≤ conf b
  /-- Conflation reverses the knowledge order (Con-1). -/
  conf_kLE_conf : ∀ {a b : B}, a ≤ₖ b → conf b ≤ₖ conf a

export Conflation (conf conf_conf conf_le_conf conf_kLE_conf)

attribute [simp] Conflation.conf_conf

/-- Negation and conflation commute (Con-4). -/
class NegConfComm (B : Type u) [Preorder B] [Preorder (Know B)] [Negation B]
    [Conflation B] : Prop where
  neg_conf : ∀ a : B, neg (conf a) = conf (neg a)

export NegConfComm (neg_conf)

variable [Conflation B]

theorem conf_le_conf_iff {a b : B} : conf a ≤ conf b ↔ a ≤ b :=
  ⟨fun h => by simpa only [conf_conf] using conf_le_conf h, conf_le_conf⟩

theorem conf_kLE_conf_iff {a b : B} : conf b ≤ₖ conf a ↔ a ≤ₖ b :=
  ⟨fun h => by simpa only [conf_conf] using conf_kLE_conf h, conf_kLE_conf⟩

/-- Conflation as an automorphism of the truth order. -/
def Conflation.orderIso : B ≃o B where
  toFun := conf
  invFun := conf
  left_inv := conf_conf
  right_inv := conf_conf
  map_rel_iff' := conf_le_conf_iff

/-- Conflation as an antitone automorphism of the knowledge order,
`Know B ≃o (Know B)ᵒᵈ`. -/
def Conflation.knowDualIso : Know B ≃o (Know B)ᵒᵈ where
  toFun X := OrderDual.toDual (toKnow (conf (ofKnow X)))
  invFun X := toKnow (conf (ofKnow (OrderDual.ofDual X)))
  left_inv _ := congrArg toKnow (conf_conf _)
  right_inv _ := congrArg (OrderDual.toDual ∘ toKnow) (conf_conf _)
  map_rel_iff' := conf_kLE_conf_iff

end Defs

section Bounds

variable [PartialOrder B] [Preorder (Know B)] [BoundedOrder B] [Conflation B]

/-- Conflation fixes the truth top, `−t = t` (note following
[fitting-2021] Def 8.5.1). -/
@[simp] theorem conf_top : conf (⊤ : B) = ⊤ :=
  le_antisymm le_top (by simpa only [conf_conf] using conf_le_conf (le_top : conf (⊤ : B) ≤ ⊤))

/-- Conflation fixes the truth bottom, `−f = f`. -/
@[simp] theorem conf_bot : conf (⊥ : B) = ⊥ :=
  le_antisymm (by simpa only [conf_conf] using conf_le_conf (bot_le : (⊥ : B) ≤ conf ⊥)) bot_le

end Bounds

section DeMorgan

variable [Lattice B] [Preorder (Know B)] [Conflation B]

/-- Conflation commutes with truth meet (CDeM-1). -/
theorem conf_inf (a b : B) : conf (a ⊓ b) = conf a ⊓ conf b :=
  Conflation.orderIso.map_inf a b

/-- Conflation commutes with truth join (CDeM-2). -/
theorem conf_sup (a b : B) : conf (a ⊔ b) = conf a ⊔ conf b :=
  Conflation.orderIso.map_sup a b

end DeMorgan

/-! #### The consistent / anticonsistent / exact classes -/

section Classes

variable [Preorder B] [Preorder (Know B)] [Conflation B]

/-- Consistent values, `a ≤ₖ −a` ([fitting-2021] Def 8.5.1): the abstract form
of the Kleene value space. -/
def IsConsistent (a : B) : Prop := a ≤ₖ conf a

/-- Anticonsistent values, `−a ≤ₖ a` ([fitting-2021] Def 8.5.1): the abstract
form of Priest's LP value space. -/
def IsAnticonsistent (a : B) : Prop := conf a ≤ₖ a

/-- Exact values, `−a = a` ([fitting-2021] Def 8.5.1): the abstract classical
value space. -/
def IsExact (a : B) : Prop := conf a = a

theorem IsExact.isConsistent {a : B} (h : IsExact a) : IsConsistent a := by
  rw [IsConsistent, h]
theorem IsExact.isAnticonsistent {a : B} (h : IsExact a) : IsAnticonsistent a := by
  rw [IsAnticonsistent, h]

instance [DecidableLE (Know B)] : DecidablePred (IsConsistent (B := B)) :=
  fun a => inferInstanceAs (Decidable (a ≤ₖ conf a))
instance [DecidableLE (Know B)] : DecidablePred (IsAnticonsistent (B := B)) :=
  fun a => inferInstanceAs (Decidable (conf a ≤ₖ a))
instance [DecidableEq B] : DecidablePred (IsExact (B := B)) :=
  fun a => inferInstanceAs (Decidable (conf a = a))

end Classes

section ClassesBounds

variable [PartialOrder B] [Preorder (Know B)] [BoundedOrder B] [Conflation B]

/-- The truth bounds are exact ([fitting-2021] Prop 8.5.2). -/
theorem isExact_top : IsExact (⊤ : B) := conf_top
theorem isExact_bot : IsExact (⊥ : B) := conf_bot

end ClassesBounds

section ClassesClosure

variable [Lattice B] [Lattice (Know B)] [Interlaced B] [Conflation B]

/-- The consistent values are closed under truth meet
([fitting-2021] Prop 8.5.2). -/
theorem IsConsistent.inf {a b : B} (ha : IsConsistent a) (hb : IsConsistent b) :
    IsConsistent (a ⊓ b) := by
  rw [IsConsistent, conf_inf]
  calc a ⊓ b ≤ₖ conf a ⊓ b := Interlaced.inf_kmono ha b
    _ = b ⊓ conf a := inf_comm ..
    _ ≤ₖ conf b ⊓ conf a := Interlaced.inf_kmono hb (conf a)
    _ = conf a ⊓ conf b := inf_comm ..

/-- The consistent values are closed under truth join. -/
theorem IsConsistent.sup {a b : B} (ha : IsConsistent a) (hb : IsConsistent b) :
    IsConsistent (a ⊔ b) := by
  rw [IsConsistent, conf_sup]
  calc a ⊔ b ≤ₖ conf a ⊔ b := Interlaced.sup_kmono ha b
    _ = b ⊔ conf a := sup_comm ..
    _ ≤ₖ conf b ⊔ conf a := Interlaced.sup_kmono hb (conf a)
    _ = conf a ⊔ conf b := sup_comm ..

/-- The anticonsistent values are closed under truth meet. -/
theorem IsAnticonsistent.inf {a b : B} (ha : IsAnticonsistent a)
    (hb : IsAnticonsistent b) : IsAnticonsistent (a ⊓ b) := by
  rw [IsAnticonsistent, conf_inf]
  calc conf a ⊓ conf b ≤ₖ a ⊓ conf b := Interlaced.inf_kmono ha (conf b)
    _ = conf b ⊓ a := inf_comm ..
    _ ≤ₖ b ⊓ a := Interlaced.inf_kmono hb a
    _ = a ⊓ b := inf_comm ..

/-- The anticonsistent values are closed under truth join. -/
theorem IsAnticonsistent.sup {a b : B} (ha : IsAnticonsistent a)
    (hb : IsAnticonsistent b) : IsAnticonsistent (a ⊔ b) := by
  rw [IsAnticonsistent, conf_sup]
  calc conf a ⊔ conf b ≤ₖ a ⊔ conf b := Interlaced.sup_kmono ha (conf b)
    _ = conf b ⊔ a := sup_comm ..
    _ ≤ₖ b ⊔ a := Interlaced.sup_kmono hb a
    _ = a ⊔ b := sup_comm ..

omit [Interlaced B] in
/-- The exact values are closed under truth meet. -/
theorem IsExact.inf {a b : B} (ha : IsExact a) (hb : IsExact b) :
    IsExact (a ⊓ b) := by rw [IsExact, conf_inf, ha, hb]

omit [Interlaced B] in
/-- The exact values are closed under truth join. -/
theorem IsExact.sup {a b : B} (ha : IsExact a) (hb : IsExact b) :
    IsExact (a ⊔ b) := by rw [IsExact, conf_sup, ha, hb]

variable [Negation B] [NegConfComm B]

omit [Interlaced B] in
/-- The consistent values are closed under negation
([fitting-2021] Prop 8.5.2; needs Con-4). -/
theorem IsConsistent.neg {a : B} (ha : IsConsistent a) : IsConsistent (neg a) := by
  rw [IsConsistent, ← neg_conf]
  exact neg_kLE_neg ha

omit [Interlaced B] in
/-- The anticonsistent values are closed under negation. -/
theorem IsAnticonsistent.neg {a : B} (ha : IsAnticonsistent a) :
    IsAnticonsistent (neg a) := by
  rw [IsAnticonsistent, ← neg_conf]
  exact neg_kLE_neg ha

omit [Interlaced B] in
/-- The exact values are closed under negation. -/
theorem IsExact.neg {a : B} (ha : IsExact a) : IsExact (neg a) := by
  rw [IsExact, ← neg_conf, ha]

end ClassesClosure

section Interpolation

variable [Lattice B] [Lattice (Know B)] [Interlaced B] [Conflation B]

/-- Every consistent value is knowledge-below an exact value
([fitting-2021] Prop 8.5.3): `a ⊔ −a` is exact. -/
theorem IsConsistent.exists_exact_kLE {a : B} (ha : IsConsistent a) :
    ∃ b : B, IsExact b ∧ a ≤ₖ b := by
  refine ⟨a ⊔ conf a, by rw [IsExact, conf_sup, conf_conf, sup_comm], ?_⟩
  calc a ≤ₖ conf a ⊔ a := by
        simpa only [sup_idem] using Interlaced.sup_kmono ha a
    _ = a ⊔ conf a := sup_comm ..

/-- Every anticonsistent value is knowledge-above an exact value
([fitting-2021] Prop 8.5.3): `a ⊓ −a` is exact. -/
theorem IsAnticonsistent.exists_exact_kLE {a : B} (ha : IsAnticonsistent a) :
    ∃ b : B, IsExact b ∧ b ≤ₖ a := by
  refine ⟨a ⊓ conf a, by rw [IsExact, conf_inf, conf_conf, inf_comm], ?_⟩
  calc a ⊓ conf a = conf a ⊓ a := inf_comm ..
    _ ≤ₖ a := by simpa only [inf_idem] using Interlaced.inf_kmono ha a

end Interpolation

section ExactAntichain

variable [Preorder B] [PartialOrder (Know B)] [Conflation B]

/-- The exact values form a knowledge-order antichain
([fitting-2021] Prop 8.5.4). -/
theorem IsExact.eq_of_kLE {a b : B} (ha : IsExact a) (hb : IsExact b)
    (h : a ≤ₖ b) : a = b :=
  kLE_antisymm h (by
    have h' := conf_kLE_conf h
    rwa [show conf a = a from ha, show conf b = b from hb] at h')

end ExactAntichain

end Conflation

/-! ### Representation (Avron Thm 4.3, interlaced case)

The converse of `Core.Logic.Bilattice.Product`: every interlaced bilattice is
isomorphic to the product `(Iic t) ⊙ (Iic f)` of the knowledge-order principal
ideals of its truth bounds `t = ⊤`, `f = ⊥`. Proved here at the knowledge lattice via the
decomposition `X ↦ (X ⊓ t, X ⊓ f)`, inverse `(a, b) ↦ a ⊔ b` ([avron-1996] Thm
4.3). The two helper lemmas are [avron-1996]'s Cor 3.5 and Cor 3.8, derived from
interlacing (Prop 3.2 → 3.6 → 3.7 → 3.8). -/

section Representation

open scoped Bilattice

variable [Lattice B] [BoundedOrder B] [Lattice (Know B)] [BoundedOrder (Know B)]
  [Interlaced B]

/-- The truth bounds `t = ⊤`, `f = ⊥` viewed in the knowledge lattice. -/
local notation "kT" => (toKnow (⊤ : B))
local notation "kF" => (toKnow (⊥ : B))

/-! #### Avron §3 chain (interlacing helpers)

The §3 lemmas below are stated in `B`-land via the knowledge operations
`⊗`/`⊕`/`≤ₖ`, then ported to `Know B` for the representation theorem. The two
truth-monotonicity facts `tle_kInf_top`/`kInf_bot_tle` (Avron's building blocks
for Prop 3.2) feed the decomposition identities `decomp_kSup`/`decomp_kInf`
(Cor 3.8 and its dual), which in turn give Cor 3.5. -/

omit [BoundedOrder B] [BoundedOrder (Know B)] in
/-- A building block for Avron Prop 3.2: from `y ≤ b` (truth), `y ≤ y ⊗ b`. The
knowledge meet `⊗` is truth-monotone, so `y = y ⊗ y ≤ b ⊗ y = y ⊗ b`. -/
private theorem tle_kInf_of_tle {y b : B} (h : y ≤ b) : y ≤ y ⊗ b := by
  simpa only [kInf_self, kInf_comm] using Interlaced.kInf_tmono h y

omit [BoundedOrder B] [BoundedOrder (Know B)] in
/-- Dual building block: from `a ≤ y` (truth), `y ⊗ a ≤ y`. -/
private theorem kInf_tle_of_tle {a y : B} (h : a ≤ y) : y ⊗ a ≤ y := by
  simpa only [kInf_self, kInf_comm] using Interlaced.kInf_tmono h y

omit [BoundedOrder B] [BoundedOrder (Know B)] in
/-- A building block for the dual of Prop 3.2: from `a ≤ y` (truth),
`y ⊕ a ≤ y`. The knowledge join `⊕` is truth-monotone. -/
private theorem kSup_tle_of_tle {a y : B} (h : a ≤ y) : (y ⊕ a : B) ≤ y := by
  simpa only [kSup_self, kSup_comm] using Interlaced.kSup_tmono h y

omit [BoundedOrder B] [BoundedOrder (Know B)] in
/-- Dual building block: from `y ≤ b` (truth), `y ≤ y ⊕ b`. -/
private theorem tle_kSup_of_tle {y b : B} (h : y ≤ b) : y ≤ (y ⊕ b : B) := by
  simpa only [kSup_self, kSup_comm] using Interlaced.kSup_tmono h y

omit [BoundedOrder (Know B)] in
/-- [avron-1996] Cor 3.8(1) in `B`-land: every element is the knowledge-join of
its knowledge-meets with the truth bounds, `x = (x ⊗ ⊤) ⊕ (x ⊗ ⊥)`. Proved by
truth-antisymmetry: both `x ≤ (x ⊗ ⊤) ⊕ (x ⊗ ⊥)` and the reverse hold, each
via truth-monotonicity of `⊕` plus knowledge absorption. -/
private theorem decomp_kSup (x : B) : ((x ⊗ ⊤) ⊕ (x ⊗ ⊥) : B) = x :=
  le_antisymm
    (by simpa only [kSup_kInf_self, kSup_comm] using
      Interlaced.kSup_tmono (kInf_tle_of_tle bot_le : x ⊗ ⊥ ≤ x) (x ⊗ ⊤))
    (by simpa only [kSup_kInf_self] using
      Interlaced.kSup_tmono (tle_kInf_of_tle le_top : x ≤ x ⊗ ⊤) (x ⊗ ⊥))

omit [BoundedOrder (Know B)] in
/-- Dual of [avron-1996] Cor 3.8: `x = (x ⊕ ⊤) ⊗ (x ⊕ ⊥)`. -/
private theorem decomp_kInf (x : B) : ((x ⊕ ⊤) ⊗ (x ⊕ ⊥) : B) = x :=
  le_antisymm
    (by simpa only [kInf_kSup_self, kInf_comm] using
      Interlaced.kInf_tmono (kSup_tle_of_tle bot_le : (x ⊕ ⊥ : B) ≤ x) (x ⊕ ⊤ : B))
    (by simpa only [kInf_kSup_self] using
      Interlaced.kInf_tmono (tle_kSup_of_tle le_top : x ≤ (x ⊕ ⊤ : B)) (x ⊕ ⊥ : B))

omit [BoundedOrder (Know B)] in
/-- On the knowledge-ideal below the truth top `t`, the truth order refines into
the knowledge order: if `u ≤ₖ t` and `u ≤ v` (truth) then `u ≤ₖ v`. Proved from
the knowledge-monotonicity of truth meet (`inf_kmono`) plus `u ⊓ v = u`. -/
private theorem kLE_of_tle_of_kLE_top {u v : B} (hu : u ≤ₖ ⊤) (huv : u ≤ v) :
    u ≤ₖ v := by
  simpa only [top_inf_eq, inf_eq_left.mpr huv] using Interlaced.inf_kmono hu v

omit [BoundedOrder (Know B)] in
/-- Dual: on the knowledge-ideal below the truth bottom `f`, the truth order
refines into the *reverse* knowledge order: if `u ≤ₖ f` and `v ≤ u` (truth) then
`u ≤ₖ v`. Proved from the knowledge-monotonicity of truth join (`sup_kmono`). -/
private theorem kLE_of_tge_of_kLE_bot {u v : B} (hu : u ≤ₖ ⊥) (hvu : v ≤ u) :
    u ≤ₖ v := by
  simpa only [bot_sup_eq, sup_eq_left.mpr hvu] using Interlaced.sup_kmono hu v

omit [BoundedOrder (Know B)] in
/-- The truth-order comparison underlying [avron-1996]'s onto direction: if `b` is
knowledge-below the truth bottom `f` and `a` is knowledge-below the truth top `t`,
then `b ≤ a` in the *truth* order. (In the twist picture `a = (a₁, ⊥)` and
`b = (⊥, b₂)`, so `b ≤ₜ a` always.) Proved by knowledge-antisymmetry on the truth
join `a ⊔ b`, using both `sup_kmono` and `inf_kmono`. -/
private theorem tle_of_kLE_top_kLE_bot {a b : B} (ha : a ≤ₖ ⊤) (hb : b ≤ₖ ⊥) :
    b ≤ a := by
  have hc1 : (a ⊔ b : B) ≤ₖ a := by
    simpa only [sup_comm, sup_bot_eq] using Interlaced.sup_kmono hb a
  have hc2 : a ≤ₖ (a ⊔ b : B) := by
    simpa only [inf_sup_self, top_inf_eq] using Interlaced.inf_kmono ha (a ⊔ b)
  exact sup_eq_left.mp (kLE_antisymm hc1 hc2)

omit [BoundedOrder (Know B)] in
/-- [avron-1996] Thm 4.3 onto, first component: for `a ≤ₖ t`, `b ≤ₖ f`, the
knowledge-meet of `a ⊕ b` with the truth top recovers `a`, `(a ⊕ b) ⊗ t = a`. -/
private theorem kInf_top_kSup (a b : B) (ha : a ≤ₖ ⊤) (hb : b ≤ₖ ⊥) :
    ((a ⊕ b) ⊗ ⊤ : B) = a := by
  have hba : b ≤ a := tle_of_kLE_top_kLE_bot ha hb
  have hsab : (a ⊕ b : B) ≤ a := by
    simpa only [kSup_self, kSup_comm] using Interlaced.kSup_tmono hba a
  have haT : (a ⊗ ⊤ : B) = a := toKnow.injective (by
    simp only [toKnow_kInf]; exact inf_eq_left.mpr ha)
  have hwle : ((a ⊕ b) ⊗ ⊤ : B) ≤ a := by
    simpa only [haT] using Interlaced.kInf_tmono hsab ⊤
  have hw_kT : ((a ⊕ b) ⊗ ⊤ : B) ≤ₖ ⊤ := by
    rw [kLE_def, toKnow_kInf]; exact inf_le_right
  have hwa : ((a ⊕ b) ⊗ ⊤ : B) ≤ₖ a := kLE_of_tle_of_kLE_top hw_kT hwle
  have haw : a ≤ₖ ((a ⊕ b) ⊗ ⊤ : B) := by
    rw [kLE_def, toKnow_kInf]
    exact le_inf (by rw [← kLE_def]; exact (le_sup_left : a ≤ₖ a ⊕ b)) ha
  exact kLE_antisymm hwa haw

omit [BoundedOrder (Know B)] in
/-- [avron-1996] Thm 4.3 onto, second component: for `a ≤ₖ t`, `b ≤ₖ f`,
`(a ⊕ b) ⊗ f = b`. -/
private theorem kInf_bot_kSup (a b : B) (ha : a ≤ₖ ⊤) (hb : b ≤ₖ ⊥) :
    ((a ⊕ b) ⊗ ⊥ : B) = b := by
  have hba : b ≤ a := tle_of_kLE_top_kLE_bot ha hb
  have hbab : b ≤ (a ⊕ b : B) := by
    simpa only [kSup_self] using Interlaced.kSup_tmono hba b
  have hbF : (b ⊗ ⊥ : B) = b := toKnow.injective (by
    simp only [toKnow_kInf]; exact inf_eq_left.mpr hb)
  have hwge : b ≤ ((a ⊕ b) ⊗ ⊥ : B) := by
    simpa only [hbF] using Interlaced.kInf_tmono hbab ⊥
  have hw_kF : ((a ⊕ b) ⊗ ⊥ : B) ≤ₖ ⊥ := by
    rw [kLE_def, toKnow_kInf]; exact inf_le_right
  have hwb : ((a ⊕ b) ⊗ ⊥ : B) ≤ₖ b := kLE_of_tge_of_kLE_bot hw_kF hwge
  have hbw : b ≤ₖ ((a ⊕ b) ⊗ ⊥ : B) := by
    rw [kLE_def, toKnow_kInf]
    exact le_inf (by rw [← kLE_def]; exact (le_sup_right : b ≤ₖ a ⊕ b)) hb
  exact kLE_antisymm hwb hbw

/-- [avron-1996] Cor 3.5: the truth bounds are complementary in the knowledge
order (`t ⊗ f = ⊥`, `t ⊕ f = ⊤`). Derived from interlacing via `decomp_kSup`
(for codisjointness: every `Z` is `≤ₖ kT ⊕ kF`) and `decomp_kInf` (for
disjointness: `kT ⊗ kF` is `≤ₖ` every `Z`). -/
theorem isCompl_truthBounds : IsCompl kT kF := by
  constructor
  · -- Disjoint: `kT ⊓ kF ≤ ⊥`. Show `kT ⊗ kF ≤ₖ Z` for all `Z`, via `decomp_kInf`.
    rw [disjoint_iff_inf_le]
    have key : ∀ Z : Know B, (kT ⊓ kF) ≤ Z := by
      intro Z
      have hZ : ((ofKnow Z ⊕ ⊤) ⊗ (ofKnow Z ⊕ ⊥) : B) = ofKnow Z := decomp_kInf (ofKnow Z)
      have e₁ : kT ⊓ kF ≤ toKnow (ofKnow Z ⊕ ⊤ : B) := by
        rw [toKnow_kSup, toKnow_ofKnow]; exact le_trans inf_le_left le_sup_right
      have e₂ : kT ⊓ kF ≤ toKnow (ofKnow Z ⊕ ⊥ : B) := by
        rw [toKnow_kSup, toKnow_ofKnow]; exact le_trans inf_le_right le_sup_right
      have : kT ⊓ kF ≤ toKnow ((ofKnow Z ⊕ ⊤) ⊗ (ofKnow Z ⊕ ⊥) : B) := by
        rw [toKnow_kInf]; exact le_inf e₁ e₂
      rwa [hZ, toKnow_ofKnow] at this
    exact key ⊥
  · -- Codisjoint: `⊤ ≤ kT ⊔ kF`. Show `Z ≤ₖ kT ⊕ kF` for all `Z`, via `decomp_kSup`.
    rw [codisjoint_iff_le_sup]
    have key : ∀ Z : Know B, Z ≤ (kT ⊔ kF) := by
      intro Z
      have hZ : ((ofKnow Z ⊗ ⊤) ⊕ (ofKnow Z ⊗ ⊥) : B) = ofKnow Z := decomp_kSup (ofKnow Z)
      have e₁ : toKnow (ofKnow Z ⊗ ⊤) ≤ kT ⊔ kF := by
        rw [toKnow_kInf, toKnow_ofKnow]; exact le_trans inf_le_right le_sup_left
      have e₂ : toKnow (ofKnow Z ⊗ ⊥) ≤ kT ⊔ kF := by
        rw [toKnow_kInf, toKnow_ofKnow]; exact le_trans inf_le_right le_sup_right
      have : toKnow ((ofKnow Z ⊗ ⊤) ⊕ (ofKnow Z ⊗ ⊥) : B) ≤ kT ⊔ kF := by
        rw [toKnow_kSup]; exact sup_le e₁ e₂
      rwa [hZ, toKnow_ofKnow] at this
    exact key ⊤

omit [BoundedOrder (Know B)] in
/-- [avron-1996] Cor 3.8(1): every element is the knowledge-join of its
knowledge-meets with the two truth bounds — `X = (X ⊗ t) ⊕ (X ⊗ f)`. This is
`decomp_kSup` ported to `Know B`: the knowledge meets/join `⊓`/`⊔` on `Know B`
are definitionally the `B`-land `⊗`/`⊕`. -/
theorem inf_kT_sup_inf_kF (X : Know B) : (X ⊓ kT) ⊔ (X ⊓ kF) = X :=
  calc (X ⊓ kT) ⊔ (X ⊓ kF)
      = toKnow ((ofKnow X ⊗ ⊤) ⊕ (ofKnow X ⊗ ⊥) : B) := rfl
    _ = toKnow (ofKnow X) := by rw [decomp_kSup]
    _ = X := toKnow_ofKnow X

/-- [avron-1996] Thm 4.3 (interlaced case): the knowledge lattice of an
interlaced bilattice decomposes as the twist product of the principal ideals of
its truth bounds, `X ↦ (X ⊓ t, X ⊓ f)`. -/
def decompose : Know B ≃o (Set.Iic kT × Set.Iic kF) where
  toFun X := (⟨X ⊓ kT, inf_le_right⟩, ⟨X ⊓ kF, inf_le_right⟩)
  invFun p := p.1.1 ⊔ p.2.1
  left_inv X := inf_kT_sup_inf_kF X
  right_inv := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    -- the two principal-ideal memberships, transported to `B`-land
    have ha' : ofKnow a ≤ₖ ⊤ := by rw [kLE_def, toKnow_ofKnow]; exact ha
    have hb' : ofKnow b ≤ₖ ⊥ := by rw [kLE_def, toKnow_ofKnow]; exact hb
    -- onto: `(a ⊔ b) ⊓ kT = a` and `(a ⊔ b) ⊓ kF = b` (Avron Thm 4.3 onto)
    have eT : (a ⊔ b) ⊓ kT = a := by
      have := kInf_top_kSup (ofKnow a) (ofKnow b) ha' hb'
      calc (a ⊔ b) ⊓ kT
          = toKnow ((ofKnow a ⊕ ofKnow b) ⊗ ⊤ : B) := rfl
        _ = toKnow (ofKnow a) := by rw [this]
        _ = a := toKnow_ofKnow a
    have eF : (a ⊔ b) ⊓ kF = b := by
      have := kInf_bot_kSup (ofKnow a) (ofKnow b) ha' hb'
      calc (a ⊔ b) ⊓ kF
          = toKnow ((ofKnow a ⊕ ofKnow b) ⊗ ⊥ : B) := rfl
        _ = toKnow (ofKnow b) := by rw [this]
        _ = b := toKnow_ofKnow b
    exact Prod.ext (Subtype.ext eT) (Subtype.ext eF)
  map_rel_iff' {X Y} := by
    -- order: ⟸ monotone (`inf_le_inf_right`); ⟹ rebuild `X`/`Y` via Cor 3.8
    rw [Prod.le_def]
    show (X ⊓ kT ≤ Y ⊓ kT ∧ X ⊓ kF ≤ Y ⊓ kF) ↔ X ≤ Y
    constructor
    · rintro ⟨h₁, h₂⟩
      calc X = (X ⊓ kT) ⊔ (X ⊓ kF) := (inf_kT_sup_inf_kF X).symm
        _ ≤ (Y ⊓ kT) ⊔ (Y ⊓ kF) := sup_le_sup h₁ h₂
        _ = Y := inf_kT_sup_inf_kF Y
    · intro h
      exact ⟨inf_le_inf_right kT h, inf_le_inf_right kF h⟩

/-! #### The truth side of Thm 4.3

`decompose` is a knowledge-order isomorphism; the theorem below recovers the
*truth* order from the same components: `x ≤ y` iff the `t`-components grow and
the `f`-components shrink in the knowledge order — the product's twisted truth
order on the factors (cf. `Bilattice.Product.mk_le_mk`). -/

omit [BoundedOrder (Know B)] in
/-- Converse of `kLE_of_tle_of_kLE_top`: below the truth top, the knowledge
order refines into the truth order. By knowledge-antisymmetry on `u ⊔ v`. -/
private theorem tle_of_kLE_of_kLE_top {u v : B} (huv : u ≤ₖ v) (hv : v ≤ₖ ⊤) :
    u ≤ v := by
  have h₁ : (u ⊔ v : B) ≤ₖ v := by
    simpa only [sup_idem] using Interlaced.sup_kmono huv v
  have h₂ : v ≤ₖ (u ⊔ v : B) := by
    simpa only [top_inf_eq, inf_eq_left.mpr (le_sup_right : v ≤ u ⊔ v)] using
      Interlaced.inf_kmono hv (u ⊔ v)
  exact le_sup_left.trans_eq (kLE_antisymm h₁ h₂)

omit [BoundedOrder (Know B)] in
/-- Dual: below the truth bottom, the knowledge order refines into the *reverse*
truth order. -/
private theorem tge_of_kLE_of_kLE_bot {u v : B} (huv : u ≤ₖ v) (hv : v ≤ₖ ⊥) :
    v ≤ u := by
  have h₁ : (u ⊓ v : B) ≤ₖ v := by
    simpa only [inf_idem] using Interlaced.inf_kmono huv v
  have h₂ : v ≤ₖ (u ⊓ v : B) := by
    simpa only [bot_sup_eq, sup_eq_left.mpr (inf_le_right : u ⊓ v ≤ v)] using
      Interlaced.sup_kmono hv (u ⊓ v)
  exact (kLE_antisymm h₁ h₂).symm.trans_le inf_le_left

omit [BoundedOrder (Know B)] in
/-- [avron-1996] Thm 4.3, truth side: the truth order is recovered from the
knowledge-order decomposition — `x ≤ y` iff the `t`-components grow and the
`f`-components shrink in the knowledge order. -/
theorem le_iff_kInf_top_kInf_bot {x y : B} :
    x ≤ y ↔ (x ⊗ ⊤ : B) ≤ₖ (y ⊗ ⊤ : B) ∧ (y ⊗ ⊥ : B) ≤ₖ (x ⊗ ⊥ : B) := by
  have mem : ∀ (z c : B), (z ⊗ c : B) ≤ₖ c := fun z c => by
    rw [kLE_def, toKnow_kInf]; exact inf_le_right
  constructor
  · intro h
    exact ⟨kLE_of_tle_of_kLE_top (mem x ⊤) (Interlaced.kInf_tmono h ⊤),
           kLE_of_tge_of_kLE_bot (mem y ⊥) (Interlaced.kInf_tmono h ⊥)⟩
  · rintro ⟨h₁, h₂⟩
    have e₁ : (x ⊗ ⊤ : B) ≤ (y ⊗ ⊤ : B) := tle_of_kLE_of_kLE_top h₁ (mem y ⊤)
    have e₂ : (x ⊗ ⊥ : B) ≤ (y ⊗ ⊥ : B) := tge_of_kLE_of_kLE_bot h₂ (mem x ⊥)
    calc x = ((x ⊗ ⊤) ⊕ (x ⊗ ⊥) : B) := (decomp_kSup x).symm
      _ ≤ ((y ⊗ ⊤) ⊕ (x ⊗ ⊥) : B) := Interlaced.kSup_tmono e₁ _
      _ = ((x ⊗ ⊥) ⊕ (y ⊗ ⊤) : B) := kSup_comm _ _
      _ ≤ ((y ⊗ ⊥) ⊕ (y ⊗ ⊤) : B) := Interlaced.kSup_tmono e₂ _
      _ = ((y ⊗ ⊤) ⊕ (y ⊗ ⊥) : B) := kSup_comm _ _
      _ = y := decomp_kSup y

/-! #### Negation and the decomposition (Avron Prop 4.7)

With a negation, the two decomposition factors are isomorphic and the
decomposition is a *diagonal* product: [avron-1996] Prop 4.7 exhibits
`⟨B, ∼⟩ ≅ L_B ⊙ L_B` with Ginsberg's swap negation, via `x ↦ (x ⊗ t, x ⊗ f)`
followed by `(x, y) ↦ (x, ∼y)`. Formalized here: the ideal isomorphism
`λ x, ∼x : L_B ≃o R_B` (`negIicIso`) and the transport equation
`∼x ⊗ t = ∼(x ⊗ f)` (`neg_kInf_top`) — the two steps of Avron's proof. -/

omit [Interlaced B] [BoundedOrder (Know B)] in
/-- [avron-1996] Prop 4.7, key step: negation is an isomorphism between the
knowledge ideals `L_B = Iic t` and `R_B = Iic f`. -/
def negIicIso [Negation B] : Set.Iic kT ≃o Set.Iic kF where
  toFun x := ⟨toKnow (neg (ofKnow x.1)), by
    simpa only [Set.mem_Iic, kLE_def, toKnow_ofKnow, neg_top] using
      neg_kLE_neg (show ofKnow x.1 ≤ₖ (⊤ : B) from x.2)⟩
  invFun y := ⟨toKnow (neg (ofKnow y.1)), by
    simpa only [Set.mem_Iic, kLE_def, toKnow_ofKnow, neg_bot] using
      neg_kLE_neg (show ofKnow y.1 ≤ₖ (⊥ : B) from y.2)⟩
  left_inv x := Subtype.ext (congrArg toKnow (neg_neg _))
  right_inv y := Subtype.ext (congrArg toKnow (neg_neg _))
  map_rel_iff' := neg_kLE_neg_iff

omit [Interlaced B] [BoundedOrder (Know B)] in
/-- [avron-1996] Prop 4.7, transport step (the map `(x, y) ↦ (x, ∼y)`):
negation exchanges the two decomposition components, `∼x ⊗ t = ∼(x ⊗ f)`. -/
theorem neg_kInf_top [Negation B] (x : B) : (neg x ⊗ ⊤ : B) = neg (x ⊗ ⊥) := by
  rw [neg_kInf, neg_bot]

end Representation

end Bilattice
