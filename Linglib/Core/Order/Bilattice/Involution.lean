module

public import Linglib.Core.Order.Bilattice.Defs
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Hom.Basic

/-!
# Negation and conflation

A negation on a bilattice ([avron-1996] Def 2.3) is an involution that reverses the truth order
and preserves the knowledge order. A conflation ([fitting-2021] §8.4) is an involution that
preserves the truth order and reverses the knowledge order. A conflation splits the carrier into
consistent values `a ≤ₖ −a`, anticonsistent values `−a ≤ₖ a` and exact values `−a = a`, the
abstract forms of the value spaces of Kleene's, Priest's and classical logic ([fitting-2021]
Def 8.5.1). The three classes are closed under the truth operations and, when negation and
conflation commute, under negation.

## Main definitions

* `Bilattice.Negation`, `Bilattice.Conflation`: the two involutions.
* `Bilattice.NegConfComm`: negation and conflation commute.
* `Bilattice.IsConsistent`, `Bilattice.IsAnticonsistent`, `Bilattice.IsExact`: the three classes.

## Main results

* `Bilattice.neg_inf`, `Bilattice.neg_sup`, `Bilattice.neg_kInf`, `Bilattice.neg_kSup`: negation
  anti-commutes with the truth operations and commutes with the knowledge operations.
* `Bilattice.IsConsistent.inf` and its kin: the closure laws ([fitting-2021] Prop 8.5.2).
* `Bilattice.IsConsistent.exists_exact_kLE`, `Bilattice.IsExact.eq_of_kLE`: interpolation and
  the antichain law ([fitting-2021] Props 8.5.3 and 8.5.4).

## References

* [avron-1996]
* [fitting-1994]
* [fitting-2021]
-/

@[expose] public section

universe u

variable {B : Type u}

namespace Bilattice

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

/-- Negation is a homomorphism of the knowledge meet, `∼(a ⊓ₖ b) = ∼a ⊓ₖ ∼b`
(note following [avron-1996] Def 2.3). -/
theorem neg_kInf (a b : B) : neg (a ⊓ₖ b) = neg a ⊓ₖ neg b :=
  toKnow.injective (Negation.knowIso.map_inf (toKnow a) (toKnow b))

/-- Negation is a homomorphism of the knowledge join, `∼(a ⊔ₖ b) = ∼a ⊔ₖ ∼b`
(note following [avron-1996] Def 2.3). -/
theorem neg_kSup (a b : B) : (neg (a ⊔ₖ b) : B) = neg a ⊔ₖ neg b :=
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

instance [DecidableRel (kLE (B := B))] : DecidablePred (IsConsistent (B := B)) :=
  fun a => inferInstanceAs (Decidable (a ≤ₖ conf a))

instance [DecidableRel (kLE (B := B))] : DecidablePred (IsAnticonsistent (B := B)) :=
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

variable [Lattice B] [Lattice (Know B)] [IsInterlaced B] [Conflation B]

/-- The consistent values are closed under truth meet
([fitting-2021] Prop 8.5.2). -/
theorem IsConsistent.inf {a b : B} (ha : IsConsistent a) (hb : IsConsistent b) :
    IsConsistent (a ⊓ b) := by
  rw [IsConsistent, conf_inf]
  calc a ⊓ b ≤ₖ conf a ⊓ b := IsInterlaced.inf_kmono ha b
    _ = b ⊓ conf a := inf_comm ..
    _ ≤ₖ conf b ⊓ conf a := IsInterlaced.inf_kmono hb (conf a)
    _ = conf a ⊓ conf b := inf_comm ..

/-- The consistent values are closed under truth join. -/
theorem IsConsistent.sup {a b : B} (ha : IsConsistent a) (hb : IsConsistent b) :
    IsConsistent (a ⊔ b) := by
  rw [IsConsistent, conf_sup]
  calc a ⊔ b ≤ₖ conf a ⊔ b := IsInterlaced.sup_kmono ha b
    _ = b ⊔ conf a := sup_comm ..
    _ ≤ₖ conf b ⊔ conf a := IsInterlaced.sup_kmono hb (conf a)
    _ = conf a ⊔ conf b := sup_comm ..

/-- The anticonsistent values are closed under truth meet. -/
theorem IsAnticonsistent.inf {a b : B} (ha : IsAnticonsistent a)
    (hb : IsAnticonsistent b) : IsAnticonsistent (a ⊓ b) := by
  rw [IsAnticonsistent, conf_inf]
  calc conf a ⊓ conf b ≤ₖ a ⊓ conf b := IsInterlaced.inf_kmono ha (conf b)
    _ = conf b ⊓ a := inf_comm ..
    _ ≤ₖ b ⊓ a := IsInterlaced.inf_kmono hb a
    _ = a ⊓ b := inf_comm ..

/-- The anticonsistent values are closed under truth join. -/
theorem IsAnticonsistent.sup {a b : B} (ha : IsAnticonsistent a)
    (hb : IsAnticonsistent b) : IsAnticonsistent (a ⊔ b) := by
  rw [IsAnticonsistent, conf_sup]
  calc conf a ⊔ conf b ≤ₖ a ⊔ conf b := IsInterlaced.sup_kmono ha (conf b)
    _ = conf b ⊔ a := sup_comm ..
    _ ≤ₖ b ⊔ a := IsInterlaced.sup_kmono hb a
    _ = a ⊔ b := sup_comm ..

omit [IsInterlaced B] in
/-- The exact values are closed under truth meet. -/
theorem IsExact.inf {a b : B} (ha : IsExact a) (hb : IsExact b) :
    IsExact (a ⊓ b) := by rw [IsExact, conf_inf, ha, hb]

omit [IsInterlaced B] in
/-- The exact values are closed under truth join. -/
theorem IsExact.sup {a b : B} (ha : IsExact a) (hb : IsExact b) :
    IsExact (a ⊔ b) := by rw [IsExact, conf_sup, ha, hb]

variable [Negation B] [NegConfComm B]

omit [IsInterlaced B] in
/-- The consistent values are closed under negation
([fitting-2021] Prop 8.5.2; needs Con-4). -/
theorem IsConsistent.neg {a : B} (ha : IsConsistent a) : IsConsistent (neg a) := by
  rw [IsConsistent, ← neg_conf]
  exact neg_kLE_neg ha

omit [IsInterlaced B] in
/-- The anticonsistent values are closed under negation. -/
theorem IsAnticonsistent.neg {a : B} (ha : IsAnticonsistent a) :
    IsAnticonsistent (neg a) := by
  rw [IsAnticonsistent, ← neg_conf]
  exact neg_kLE_neg ha

omit [IsInterlaced B] in
/-- The exact values are closed under negation. -/
theorem IsExact.neg {a : B} (ha : IsExact a) : IsExact (neg a) := by
  rw [IsExact, ← neg_conf, ha]

end ClassesClosure

section Interpolation

variable [Lattice B] [Lattice (Know B)] [IsInterlaced B] [Conflation B]

/-- Every consistent value is knowledge-below an exact value
([fitting-2021] Prop 8.5.3): `a ⊔ −a` is exact. -/
theorem IsConsistent.exists_exact_kLE {a : B} (ha : IsConsistent a) :
    ∃ b : B, IsExact b ∧ a ≤ₖ b := by
  refine ⟨a ⊔ conf a, by rw [IsExact, conf_sup, conf_conf, sup_comm], ?_⟩
  calc a ≤ₖ conf a ⊔ a := by
        simpa only [sup_idem] using IsInterlaced.sup_kmono ha a
    _ = a ⊔ conf a := sup_comm ..

/-- Every anticonsistent value is knowledge-above an exact value
([fitting-2021] Prop 8.5.3): `a ⊓ −a` is exact. -/
theorem IsAnticonsistent.exists_exact_kLE {a : B} (ha : IsAnticonsistent a) :
    ∃ b : B, IsExact b ∧ b ≤ₖ a := by
  refine ⟨a ⊓ conf a, by rw [IsExact, conf_inf, conf_conf, inf_comm], ?_⟩
  calc a ⊓ conf a = conf a ⊓ a := inf_comm ..
    _ ≤ₖ a := by simpa only [inf_idem] using IsInterlaced.inf_kmono ha a

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

end Bilattice
