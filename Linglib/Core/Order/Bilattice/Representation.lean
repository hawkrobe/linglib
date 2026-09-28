module

public import Linglib.Core.Order.Bilattice.Involution
public import Mathlib.Order.Interval.Set.Basic

/-!
# The representation of interlaced bilattices

Every interlaced bilattice is a product bilattice ([avron-1996] Thm 4.3). Its knowledge lattice
decomposes as the product of the knowledge-order principal ideals of the truth bounds, by
`x ↦ (x ⊓ₖ ⊤, x ⊓ₖ ⊥)` with inverse `(a, b) ↦ a ⊔ₖ b`, and the truth order is the twisted order
on the two factors. The key identities, [avron-1996]'s Cor 3.5 and Cor 3.8, are derived here from
interlacing alone. With a negation the two factors are isomorphic ([avron-1996] Prop 4.7). The
converse, that a product of two lattices is interlaced, is `Bilattice.Product`.

## Main results

* `Bilattice.decompose`: the knowledge lattice is `Iic ⊤ × Iic ⊥` (Thm 4.3).
* `Bilattice.le_iff_kInf_top_kInf_bot`: the truth order read off the decomposition (Thm 4.3).
* `Bilattice.isCompl_truthBounds`: the truth bounds are knowledge-complementary (Cor 3.5).
* `Bilattice.inf_kT_sup_inf_kF`: every element is `(x ⊓ₖ ⊤) ⊔ₖ (x ⊓ₖ ⊥)` (Cor 3.8).
* `Bilattice.complIicIso`, `Bilattice.compl_kInf_top`: the two steps of Prop 4.7.

## TODO

Package Prop 4.7's equivalence `⟨B, ∼⟩ ≅ L_B ⊙ L_B`, and the abstract uniqueness of the factors up
to isomorphism (Thm 4.3; the concrete half for products is `Bilattice.Product.decomposeProdIso`).

## References

* [avron-1996]
-/

@[expose] public section

universe u

variable {B : Type u}

namespace Bilattice

section Representation

open scoped Bilattice

variable [Lattice B] [BoundedOrder B] [Lattice (Know B)] [BoundedOrder (Know B)]
  [IsInterlaced B]

/-- The truth bounds `t = ⊤`, `f = ⊥` viewed in the knowledge lattice. -/
local notation "kT" => (toKnow (⊤ : B))
local notation "kF" => (toKnow (⊥ : B))

/-! #### Avron §3 chain (interlacing helpers)

The §3 lemmas below are stated in `B`-land via the knowledge operations
`⊓ₖ`/`⊔ₖ`/`≤ₖ`, then ported to `Know B` for the representation theorem. The two
truth-monotonicity facts `tle_kInf_top`/`kInf_bot_tle` (Avron's building blocks
for Prop 3.2) feed the decomposition identities `decomp_kSup`/`decomp_kInf`
(Cor 3.8 and its dual), which in turn give Cor 3.5. -/

omit [BoundedOrder B] [BoundedOrder (Know B)] in
/-- A building block for Avron Prop 3.2: from `y ≤ b` (truth), `y ≤ y ⊓ₖ b`. The
knowledge meet `⊓ₖ` is truth-monotone, so `y = y ⊓ₖ y ≤ b ⊓ₖ y = y ⊓ₖ b`. -/
private theorem tle_kInf_of_tle {y b : B} (h : y ≤ b) : y ≤ y ⊓ₖ b := by
  simpa only [kInf_self, kInf_comm] using IsInterlaced.kInf_tmono h y

omit [BoundedOrder B] [BoundedOrder (Know B)] in
/-- Dual building block: from `a ≤ y` (truth), `y ⊓ₖ a ≤ y`. -/
private theorem kInf_tle_of_tle {a y : B} (h : a ≤ y) : y ⊓ₖ a ≤ y := by
  simpa only [kInf_self, kInf_comm] using IsInterlaced.kInf_tmono h y

omit [BoundedOrder B] [BoundedOrder (Know B)] in
/-- A building block for the dual of Prop 3.2: from `a ≤ y` (truth),
`y ⊔ₖ a ≤ y`. The knowledge join `⊔ₖ` is truth-monotone. -/
private theorem kSup_tle_of_tle {a y : B} (h : a ≤ y) : y ⊔ₖ a ≤ y := by
  simpa only [kSup_self, kSup_comm] using IsInterlaced.kSup_tmono h y

omit [BoundedOrder B] [BoundedOrder (Know B)] in
/-- Dual building block: from `y ≤ b` (truth), `y ≤ y ⊔ₖ b`. -/
private theorem tle_kSup_of_tle {y b : B} (h : y ≤ b) : y ≤ y ⊔ₖ b := by
  simpa only [kSup_self, kSup_comm] using IsInterlaced.kSup_tmono h y

omit [BoundedOrder (Know B)] in
/-- [avron-1996] Cor 3.8(1) in `B`-land: every element is the knowledge-join of
its knowledge-meets with the truth bounds, `x = (x ⊓ₖ ⊤) ⊔ₖ (x ⊓ₖ ⊥)`. Proved by
truth-antisymmetry: both `x ≤ (x ⊓ₖ ⊤) ⊔ₖ (x ⊓ₖ ⊥)` and the reverse hold, each
via truth-monotonicity of `⊔ₖ` plus knowledge absorption. -/
private theorem decomp_kSup (x : B) : (x ⊓ₖ ⊤) ⊔ₖ (x ⊓ₖ ⊥) = x :=
  le_antisymm
    (by simpa only [kSup_kInf_self, kSup_comm] using
      IsInterlaced.kSup_tmono (kInf_tle_of_tle bot_le : x ⊓ₖ ⊥ ≤ x) (x ⊓ₖ ⊤))
    (by simpa only [kSup_kInf_self] using
      IsInterlaced.kSup_tmono (tle_kInf_of_tle le_top : x ≤ x ⊓ₖ ⊤) (x ⊓ₖ ⊥))

omit [BoundedOrder (Know B)] in
/-- Dual of [avron-1996] Cor 3.8: `x = (x ⊔ₖ ⊤) ⊓ₖ (x ⊔ₖ ⊥)`. -/
private theorem decomp_kInf (x : B) : (x ⊔ₖ ⊤) ⊓ₖ (x ⊔ₖ ⊥) = x :=
  le_antisymm
    (by simpa only [kInf_kSup_self, kInf_comm] using
      IsInterlaced.kInf_tmono (kSup_tle_of_tle bot_le : x ⊔ₖ ⊥ ≤ x) (x ⊔ₖ ⊤))
    (by simpa only [kInf_kSup_self] using
      IsInterlaced.kInf_tmono (tle_kSup_of_tle le_top : x ≤ x ⊔ₖ ⊤) (x ⊔ₖ ⊥))

omit [BoundedOrder (Know B)] in
/-- On the knowledge-ideal below the truth top `t`, the truth order refines into
the knowledge order: if `u ≤ₖ t` and `u ≤ v` (truth) then `u ≤ₖ v`. Proved from
the knowledge-monotonicity of truth meet (`inf_kmono`) plus `u ⊓ v = u`. -/
private theorem kLE_of_tle_of_kLE_top {u v : B} (hu : u ≤ₖ ⊤) (huv : u ≤ v) :
    u ≤ₖ v := by
  simpa only [top_inf_eq, inf_eq_left.mpr huv] using IsInterlaced.inf_kmono hu v

omit [BoundedOrder (Know B)] in
/-- Dual: on the knowledge-ideal below the truth bottom `f`, the truth order
refines into the *reverse* knowledge order: if `u ≤ₖ f` and `v ≤ u` (truth) then
`u ≤ₖ v`. Proved from the knowledge-monotonicity of truth join (`sup_kmono`). -/
private theorem kLE_of_tge_of_kLE_bot {u v : B} (hu : u ≤ₖ ⊥) (hvu : v ≤ u) :
    u ≤ₖ v := by
  simpa only [bot_sup_eq, sup_eq_left.mpr hvu] using IsInterlaced.sup_kmono hu v

omit [BoundedOrder (Know B)] in
/-- The truth-order comparison underlying [avron-1996]'s onto direction: if `b` is
knowledge-below the truth bottom `f` and `a` is knowledge-below the truth top `t`,
then `b ≤ a` in the *truth* order. (In a product `a = (a₁, ⊥)` and
`b = (⊥, b₂)`, so `b ≤ₜ a` always.) Proved by knowledge-antisymmetry on the truth
join `a ⊔ b`, using both `sup_kmono` and `inf_kmono`. -/
private theorem tle_of_kLE_top_kLE_bot {a b : B} (ha : a ≤ₖ ⊤) (hb : b ≤ₖ ⊥) :
    b ≤ a := by
  have hc1 : (a ⊔ b : B) ≤ₖ a := by
    simpa only [sup_comm, sup_bot_eq] using IsInterlaced.sup_kmono hb a
  have hc2 : a ≤ₖ (a ⊔ b : B) := by
    simpa only [inf_sup_self, top_inf_eq] using IsInterlaced.inf_kmono ha (a ⊔ b)
  exact sup_eq_left.mp (kLE_antisymm hc1 hc2)

omit [BoundedOrder (Know B)] in
/-- [avron-1996] Thm 4.3 onto, first component: for `a ≤ₖ t`, `b ≤ₖ f`, the
knowledge-meet of `a ⊔ₖ b` with the truth top recovers `a`, `(a ⊔ₖ b) ⊓ₖ t = a`. -/
private theorem kInf_top_kSup (a b : B) (ha : a ≤ₖ ⊤) (hb : b ≤ₖ ⊥) :
    ((a ⊔ₖ b) ⊓ₖ ⊤) = a := by
  have hba : b ≤ a := tle_of_kLE_top_kLE_bot ha hb
  have hsab : a ⊔ₖ b ≤ a := by
    simpa only [kSup_self, kSup_comm] using IsInterlaced.kSup_tmono hba a
  have haT : a ⊓ₖ ⊤ = a := toKnow.injective (by
    simp only [toKnow_kInf]; exact inf_eq_left.mpr ha)
  have hwle : (a ⊔ₖ b) ⊓ₖ ⊤ ≤ a := by
    simpa only [haT] using IsInterlaced.kInf_tmono hsab ⊤
  have hw_kT : (a ⊔ₖ b) ⊓ₖ ⊤ ≤ₖ ⊤ := by
    rw [kLE_def, toKnow_kInf]; exact inf_le_right
  have hwa : (a ⊔ₖ b) ⊓ₖ ⊤ ≤ₖ a := kLE_of_tle_of_kLE_top hw_kT hwle
  have haw : a ≤ₖ (a ⊔ₖ b) ⊓ₖ ⊤ := by
    rw [kLE_def, toKnow_kInf]
    exact le_inf (by rw [← kLE_def]; exact (le_sup_left : a ≤ₖ a ⊔ₖ b)) ha
  exact kLE_antisymm hwa haw

omit [BoundedOrder (Know B)] in
/-- [avron-1996] Thm 4.3 onto, second component: for `a ≤ₖ t`, `b ≤ₖ f`,
`(a ⊔ₖ b) ⊓ₖ f = b`. -/
private theorem kInf_bot_kSup (a b : B) (ha : a ≤ₖ ⊤) (hb : b ≤ₖ ⊥) :
    ((a ⊔ₖ b) ⊓ₖ ⊥) = b := by
  have hba : b ≤ a := tle_of_kLE_top_kLE_bot ha hb
  have hbab : b ≤ a ⊔ₖ b := by
    simpa only [kSup_self] using IsInterlaced.kSup_tmono hba b
  have hbF : b ⊓ₖ ⊥ = b := toKnow.injective (by
    simp only [toKnow_kInf]; exact inf_eq_left.mpr hb)
  have hwge : b ≤ (a ⊔ₖ b) ⊓ₖ ⊥ := by
    simpa only [hbF] using IsInterlaced.kInf_tmono hbab ⊥
  have hw_kF : (a ⊔ₖ b) ⊓ₖ ⊥ ≤ₖ ⊥ := by
    rw [kLE_def, toKnow_kInf]; exact inf_le_right
  have hwb : (a ⊔ₖ b) ⊓ₖ ⊥ ≤ₖ b := kLE_of_tge_of_kLE_bot hw_kF hwge
  have hbw : b ≤ₖ (a ⊔ₖ b) ⊓ₖ ⊥ := by
    rw [kLE_def, toKnow_kInf]
    exact le_inf (by rw [← kLE_def]; exact (le_sup_right : b ≤ₖ a ⊔ₖ b)) hb
  exact kLE_antisymm hwb hbw

/-- [avron-1996] Cor 3.5: the truth bounds are complementary in the knowledge
order (`t ⊓ₖ f = ⊥`, `t ⊔ₖ f = ⊤`). Derived from interlacing via `decomp_kSup`
(for codisjointness: every `Z` is `≤ₖ kT ⊔ₖ kF`) and `decomp_kInf` (for
disjointness: `kT ⊓ₖ kF` is `≤ₖ` every `Z`). -/
theorem isCompl_truthBounds : IsCompl kT kF := by
  constructor
  · -- Disjoint: `kT ⊓ kF ≤ ⊥`. Show `kT ⊓ₖ kF ≤ₖ Z` for all `Z`, via `decomp_kInf`.
    rw [disjoint_iff_inf_le]
    have key : ∀ Z : Know B, (kT ⊓ kF) ≤ Z := by
      intro Z
      have hZ : (ofKnow Z ⊔ₖ ⊤) ⊓ₖ (ofKnow Z ⊔ₖ ⊥) = ofKnow Z := decomp_kInf (ofKnow Z)
      have e₁ : kT ⊓ kF ≤ toKnow (ofKnow Z ⊔ₖ ⊤) := by
        rw [toKnow_kSup, toKnow_ofKnow]; exact le_trans inf_le_left le_sup_right
      have e₂ : kT ⊓ kF ≤ toKnow (ofKnow Z ⊔ₖ ⊥) := by
        rw [toKnow_kSup, toKnow_ofKnow]; exact le_trans inf_le_right le_sup_right
      have : kT ⊓ kF ≤ toKnow ((ofKnow Z ⊔ₖ ⊤) ⊓ₖ (ofKnow Z ⊔ₖ ⊥)) := by
        rw [toKnow_kInf]; exact le_inf e₁ e₂
      rwa [hZ, toKnow_ofKnow] at this
    exact key ⊥
  · -- Codisjoint: `⊤ ≤ kT ⊔ kF`. Show `Z ≤ₖ kT ⊔ₖ kF` for all `Z`, via `decomp_kSup`.
    rw [codisjoint_iff_le_sup]
    have key : ∀ Z : Know B, Z ≤ (kT ⊔ kF) := by
      intro Z
      have hZ : (ofKnow Z ⊓ₖ ⊤) ⊔ₖ (ofKnow Z ⊓ₖ ⊥) = ofKnow Z := decomp_kSup (ofKnow Z)
      have e₁ : toKnow (ofKnow Z ⊓ₖ ⊤) ≤ kT ⊔ kF := by
        rw [toKnow_kInf, toKnow_ofKnow]; exact le_trans inf_le_right le_sup_left
      have e₂ : toKnow (ofKnow Z ⊓ₖ ⊥) ≤ kT ⊔ kF := by
        rw [toKnow_kInf, toKnow_ofKnow]; exact le_trans inf_le_right le_sup_right
      have : toKnow ((ofKnow Z ⊓ₖ ⊤) ⊔ₖ (ofKnow Z ⊓ₖ ⊥)) ≤ kT ⊔ kF := by
        rw [toKnow_kSup]; exact sup_le e₁ e₂
      rwa [hZ, toKnow_ofKnow] at this
    exact key ⊤

omit [BoundedOrder (Know B)] in
/-- [avron-1996] Cor 3.8(1): every element is the knowledge-join of its
knowledge-meets with the two truth bounds — `X = (X ⊓ₖ t) ⊔ₖ (X ⊓ₖ f)`. This is
`decomp_kSup` ported to `Know B`: the knowledge meets/join `⊓`/`⊔` on `Know B`
are definitionally the `B`-land `⊓ₖ`/`⊔ₖ`. -/
theorem inf_kT_sup_inf_kF (X : Know B) : (X ⊓ kT) ⊔ (X ⊓ kF) = X :=
  calc (X ⊓ kT) ⊔ (X ⊓ kF)
      = toKnow ((ofKnow X ⊓ₖ ⊤) ⊔ₖ (ofKnow X ⊓ₖ ⊥)) := rfl
    _ = toKnow (ofKnow X) := by rw [decomp_kSup]
    _ = X := toKnow_ofKnow X

/-- [avron-1996] Thm 4.3 (interlaced case): the knowledge lattice of an
interlaced bilattice decomposes as the product of the principal ideals of
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
          = toKnow ((ofKnow a ⊔ₖ ofKnow b) ⊓ₖ ⊤) := rfl
        _ = toKnow (ofKnow a) := by rw [this]
        _ = a := toKnow_ofKnow a
    have eF : (a ⊔ b) ⊓ kF = b := by
      have := kInf_bot_kSup (ofKnow a) (ofKnow b) ha' hb'
      calc (a ⊔ b) ⊓ kF
          = toKnow ((ofKnow a ⊔ₖ ofKnow b) ⊓ₖ ⊥) := rfl
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
    simpa only [sup_idem] using IsInterlaced.sup_kmono huv v
  have h₂ : v ≤ₖ (u ⊔ v : B) := by
    simpa only [top_inf_eq, inf_eq_left.mpr (le_sup_right : v ≤ u ⊔ v)] using
      IsInterlaced.inf_kmono hv (u ⊔ v)
  exact le_sup_left.trans_eq (kLE_antisymm h₁ h₂)

omit [BoundedOrder (Know B)] in
/-- Dual: below the truth bottom, the knowledge order refines into the *reverse*
truth order. -/
private theorem tge_of_kLE_of_kLE_bot {u v : B} (huv : u ≤ₖ v) (hv : v ≤ₖ ⊥) :
    v ≤ u := by
  have h₁ : (u ⊓ v : B) ≤ₖ v := by
    simpa only [inf_idem] using IsInterlaced.inf_kmono huv v
  have h₂ : v ≤ₖ (u ⊓ v : B) := by
    simpa only [bot_sup_eq, sup_eq_left.mpr (inf_le_right : u ⊓ v ≤ v)] using
      IsInterlaced.sup_kmono hv (u ⊓ v)
  exact (kLE_antisymm h₁ h₂).symm.trans_le inf_le_left

omit [BoundedOrder (Know B)] in
/-- [avron-1996] Thm 4.3, truth side: the truth order is recovered from the
knowledge-order decomposition — `x ≤ y` iff the `t`-components grow and the
`f`-components shrink in the knowledge order. -/
theorem le_iff_kInf_top_kInf_bot {x y : B} :
    x ≤ y ↔ x ⊓ₖ ⊤ ≤ₖ (y ⊓ₖ ⊤) ∧ (y ⊓ₖ ⊥) ≤ₖ x ⊓ₖ ⊥ := by
  have mem : ∀ (z c : B), (z ⊓ₖ c) ≤ₖ c := fun z c => by
    rw [kLE_def, toKnow_kInf]; exact inf_le_right
  constructor
  · intro h
    exact ⟨kLE_of_tle_of_kLE_top (mem x ⊤) (IsInterlaced.kInf_tmono h ⊤),
           kLE_of_tge_of_kLE_bot (mem y ⊥) (IsInterlaced.kInf_tmono h ⊥)⟩
  · rintro ⟨h₁, h₂⟩
    have e₁ : x ⊓ₖ ⊤ ≤ y ⊓ₖ ⊤ := tle_of_kLE_of_kLE_top h₁ (mem y ⊤)
    have e₂ : x ⊓ₖ ⊥ ≤ y ⊓ₖ ⊥ := tge_of_kLE_of_kLE_bot h₂ (mem x ⊥)
    calc x = (x ⊓ₖ ⊤) ⊔ₖ (x ⊓ₖ ⊥) := (decomp_kSup x).symm
      _ ≤ (y ⊓ₖ ⊤) ⊔ₖ (x ⊓ₖ ⊥) := IsInterlaced.kSup_tmono e₁ _
      _ = (x ⊓ₖ ⊥) ⊔ₖ (y ⊓ₖ ⊤) := kSup_comm _ _
      _ ≤ (y ⊓ₖ ⊥) ⊔ₖ (y ⊓ₖ ⊤) := IsInterlaced.kSup_tmono e₂ _
      _ = (y ⊓ₖ ⊤) ⊔ₖ (y ⊓ₖ ⊥) := kSup_comm _ _
      _ = y := decomp_kSup y

end Representation

/-! ### Negation and the decomposition

With a negation the two decomposition factors are isomorphic, and the decomposition is a diagonal
product: [avron-1996] Prop 4.7 exhibits `⟨B, ∼⟩ ≅ L_B ⊙ L_B` with Ginsberg's swap negation, via
`x ↦ (x ⊓ₖ t, x ⊓ₖ f)` followed by `(x, y) ↦ (x, yᶜ)`. The two steps of that proof are the ideal
isomorphism `complIicIso` and the transport equation `compl_kInf_top`. -/

section Negation

variable [LatticeWithInvolution B] [Lattice (Know B)] [Negation B]

/-- [avron-1996] Prop 4.7, key step: negation is an isomorphism between the knowledge ideals
`L_B = Iic t` and `R_B = Iic f`. -/
def complIicIso : Set.Iic (toKnow (⊤ : B)) ≃o Set.Iic (toKnow (⊥ : B)) where
  toFun x := ⟨toKnow (ofKnow x.1)ᶜ, by
    simpa only [Set.mem_Iic, kLE_def, toKnow_ofKnow, LatticeWithInvolution.compl_top] using
      compl_kLE_compl (show ofKnow x.1 ≤ₖ (⊤ : B) from x.2)⟩
  invFun y := ⟨toKnow (ofKnow y.1)ᶜ, by
    simpa only [Set.mem_Iic, kLE_def, toKnow_ofKnow, LatticeWithInvolution.compl_bot] using
      compl_kLE_compl (show ofKnow y.1 ≤ₖ (⊥ : B) from y.2)⟩
  left_inv _ := Subtype.ext (congrArg toKnow (LatticeWithInvolution.compl_compl _))
  right_inv _ := Subtype.ext (congrArg toKnow (LatticeWithInvolution.compl_compl _))
  map_rel_iff' := compl_kLE_compl_iff

/-- [avron-1996] Prop 4.7, transport step (the map `(x, y) ↦ (x, yᶜ)`): negation exchanges the
two decomposition components, `xᶜ ⊓ₖ t = (x ⊓ₖ f)ᶜ`. -/
theorem compl_kInf_top (x : B) : xᶜ ⊓ₖ ⊤ = (x ⊓ₖ ⊥)ᶜ := by
  rw [compl_kInf, LatticeWithInvolution.compl_bot]

end Negation

end Bilattice
