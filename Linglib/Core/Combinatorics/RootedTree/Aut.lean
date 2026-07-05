/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.RoseTree.DecEq
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Antidiagonal
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic

set_option autoImplicit false

/-!
# Automorphism cardinality for rooted nonplanar trees

The cardinality of the automorphism group of a rooted nonplanar tree
(or a forest of such trees), used as the symmetry-weight in the
Connes-Kreimer / Grossman-Larson pairing
(`Linglib/Core/Algebra/RootedTree/GrossmanLarsonPairing.lean`).

## RoseTree-level formula

For a node with children-multiset `M = {c₁ × k₁, c₂ × k₂, …}` (distinct
trees `cᵢ` with multiplicities `kᵢ`):
```
|Aut(node a M)| = ∏ᵢ kᵢ! · |Aut(cᵢ)|^kᵢ
```
A leaf has `|Aut(leaf)| = 1`.

The factorial factor `kᵢ!` accounts for permutations of identical
children; the power `|Aut(cᵢ)|^kᵢ` accounts for independent choice of
auts within each copy.

## Forest-level formula

For a forest (multiset of trees) `F = {T₁ × m₁, T₂ × m₂, …}`:
```
|Aut(F)| = ∏ⱼ mⱼ! · |Aut(Tⱼ)|^mⱼ
```
Same formula structure as the tree-level case, applied to the
top-level multiset of constituent trees.

## Implementation status

`[UPSTREAM]` candidate. Eventual mathlib home would be
`Mathlib.Combinatorics.RootedTree.Aut`. **Sorry-free.**

`Nonplanar.autCard` descends from `treeAutCard` on the `RoseTree α`
representative, defined by structural recursion over the children list
(`(cs.map treeAutCard).prod` aggregates the children product; no aux
twin — `RoseTree`'s nested-`List` recursion is handled by the equation
compiler and its `@[induction_eliminator]`). `Perm`-invariance is
established via a `PermList` companion pair, and the lift to
`Nonplanar` uses `Nonplanar.lift`. `autCard_node` bridges to the
`forestAutCard`-as-Finset-product form via `Finset.prod_multiset_map_count`
(turning the all-children prod into a `∏ distinct, c ^ count`-form) +
`Finset.prod_mul_distrib`.

`forestAutCard` is defined in terms of `autCard`.
-/

namespace RootedTree

namespace Nonplanar

variable {α : Type*} [DecidableEq α]

/-! ### RoseTree-representative substrate

`treeAutCard` computes `|Aut(mk t)|` on a planar `RoseTree` representative
`t`; `Perm`-invariance (below) lets it descend to `Nonplanar.autCard`
through the quotient. -/

/-- Symmetry-factor at one node: `∏_{distinct c ∈ M} (M.count c)!`. -/
def multinomialFactor (M : Multiset (Nonplanar α)) : ℕ :=
  M.toFinset.prod fun t => (M.count t).factorial

/-- `multinomialFactor` as a `Finsupp.prod` over `M.toFinsupp` — the
    multiplicity-indexed form used by the multinomial arguments below. -/
theorem multinomialFactor_eq_prod (M : Multiset (Nonplanar α)) :
    multinomialFactor M = M.toFinsupp.prod fun _ k => k.factorial := by
  simp only [multinomialFactor, Finsupp.prod, Multiset.toFinsupp_support, Multiset.toFinsupp_apply]

/-- The automorphism count `|Aut(mk t)|` of the nonplanar tree represented
    by a planar `RoseTree` `t`. Substrate for `Nonplanar.autCard` (which lifts
    it through the `Perm` quotient). At a node, the product of the
    children's counts times `multinomialFactor` on the multiset of
    nonplanar-`mk` children (counting symmetric rearrangements). -/
def treeAutCard : RoseTree α → ℕ
  | .node _ cs =>
      (cs.map treeAutCard).prod * multinomialFactor (Multiset.ofList (cs.map mk))

theorem treeAutCard_node (a : α) (cs : List (RoseTree α)) :
    treeAutCard (RoseTree.node a cs) =
      (cs.map treeAutCard).prod * multinomialFactor (Multiset.ofList (cs.map mk)) := by
  rw [treeAutCard]

/-! #### `treeAutCard` is `Perm`-invariant -/

mutual
/-- `treeAutCard` is invariant under `Perm`. At a node the algebra reads the
    children only through the child-`treeAutCard` product and the `mk`-multiset,
    both fixed by the `PermList` companion. -/
theorem treeAutCard_perm : ∀ {t s : RoseTree α}, RoseTree.Perm t s →
    treeAutCard t = treeAutCard s
  | _, _, .node h => by
    rw [treeAutCard_node, treeAutCard_node]
    obtain ⟨hprod, hmk⟩ := treeAutCard_permList h
    rw [hprod, hmk]
  | _, _, .trans h₁ h₂ => (treeAutCard_perm h₁).trans (treeAutCard_perm h₂)

/-- The two children statistics `treeAutCard` reads — the child-`treeAutCard`
    product and the `mk`-multiset — are `PermList`-invariant: `cons` matches heads
    by the mutual `treeAutCard_perm` and `mk_eq_mk_iff`, `swap` by commutativity
    of `*` and `Multiset.cons_swap`. -/
theorem treeAutCard_permList : ∀ {cs ds : List (RoseTree α)}, RoseTree.PermList cs ds →
    (cs.map treeAutCard).prod = (ds.map treeAutCard).prod ∧
      (Multiset.ofList (cs.map mk) : Multiset (Nonplanar α)) = Multiset.ofList (ds.map mk)
  | _, _, .nil => ⟨rfl, rfl⟩
  | _, _, .cons h hs => by
    obtain ⟨hprod, hmk⟩ := treeAutCard_permList hs
    refine ⟨by simp only [List.map_cons, List.prod_cons, treeAutCard_perm h, hprod], ?_⟩
    simp only [List.map_cons, ← Multiset.cons_coe]
    rw [mk_eq_mk_iff.mpr h, hmk]
  | _, _, .swap c d cs =>
    ⟨by simp only [List.map_cons, List.prod_cons]; exact mul_left_comm _ _ _,
     by simp only [List.map_cons, ← Multiset.cons_coe]; exact Multiset.cons_swap _ _ _⟩
  | _, _, .trans h₁ h₂ =>
    match treeAutCard_permList h₁, treeAutCard_permList h₂ with
    | ⟨p₁, m₁⟩, ⟨p₂, m₂⟩ => ⟨p₁.trans p₂, m₁.trans m₂⟩
end

/-! #### Positivity of `treeAutCard` -/

/-- Every factor in `multinomialFactor M` is positive (each is a factorial). -/
private theorem multinomialFactor_pos (M : Multiset (Nonplanar α)) :
    0 < multinomialFactor M :=
  Finset.prod_pos fun _ _ => Nat.factorial_pos _

/-- `treeAutCard` is positive: at a node, `multinomialFactor` is positive
    (factorials) and the children product is positive by the IH. -/
theorem treeAutCard_pos (t : RoseTree α) : 0 < treeAutCard t := by
  induction t with
  | node a cs ih =>
    rw [treeAutCard_node]
    refine Nat.mul_pos ?_ (multinomialFactor_pos _)
    exact List.prod_pos_iff_forall_pos_nat.mpr (by simpa using ih)

/-! ### Nonplanar automorphism count via lift -/

/-- The cardinality `|Aut(t)|` of the automorphism group of a rooted
    nonplanar tree `t`.

    Recursive structure: for `t = node a M` with children-multiset `M`,
    `autCard t = ∏ distinct c ∈ M, (M.count c)! * (autCard c)^(M.count c)`
    (see `autCard_node`). A leaf has `autCard = 1` (`autCard_leaf`).

    Defined by lifting `treeAutCard` through the `Perm` quotient. -/
def autCard : Nonplanar α → ℕ :=
  Nonplanar.lift treeAutCard (fun _ _ h => treeAutCard_perm h)

@[simp] theorem autCard_mk (t : RoseTree α) : autCard (mk t) = treeAutCard t := rfl

/-- A leaf has trivial aut group. -/
@[simp] theorem autCard_leaf (a : α) : autCard (Nonplanar.leaf a : Nonplanar α) = 1 := by
  show treeAutCard (RoseTree.leaf a) = 1
  rw [RoseTree.leaf_def, treeAutCard_node]
  simp [multinomialFactor]

/-- The automorphism group of any tree is non-trivial (contains identity).
    Stated as positivity of the cardinality. Descends from
    `treeAutCard_pos` via the quotient. -/
theorem autCard_pos (t : Nonplanar α) : 0 < autCard t :=
  Quotient.inductionOn t treeAutCard_pos

/-- The cardinality `|Aut(F)|` of the automorphism group of a forest
    `F` (multiset of nonplanar trees), defined as the product over
    distinct trees `T ∈ F`:
    ```
    forestAutCard F = ∏_{distinct T ∈ F} (F.count T)! · (autCard T)^(F.count T)
    ```
    Stays in `Nonplanar` namespace (rather than `Forest`) because
    `Forest = Multiset` is just a stylistic alias used at the
    `ConnesKreimer` algebra layer; here we work directly with
    `Multiset (Nonplanar α)` to keep the combinatorics layer free of
    algebra-layer abbreviations. -/
def forestAutCard (F : Multiset (Nonplanar α)) : ℕ :=
  F.toFinset.prod fun t => Nat.factorial (F.count t) * autCard t ^ F.count t

/-- `forestAutCard` as a `Finsupp.prod` over `F.toFinsupp` — the
    multiplicity-indexed form used by `forestAutCard_add`. -/
theorem forestAutCard_eq_prod (F : Multiset (Nonplanar α)) :
    forestAutCard F = F.toFinsupp.prod fun t k => k.factorial * autCard t ^ k := by
  simp only [forestAutCard, Finsupp.prod, Multiset.toFinsupp_support, Multiset.toFinsupp_apply]

/-- The empty forest has trivial aut group. -/
@[simp] theorem forestAutCard_zero :
    forestAutCard (0 : Multiset (Nonplanar α)) = 1 := by
  simp [forestAutCard]

/-- The aut group of any forest is non-trivial (contains identity).
    Each factor `(F.count t)! * autCard t ^ F.count t` is positive
    (factorial always positive; `autCard_pos` gives the tree factor). -/
theorem forestAutCard_pos (F : Multiset (Nonplanar α)) : 0 < forestAutCard F := by
  unfold forestAutCard
  exact Finset.prod_pos fun t _ =>
    Nat.mul_pos (Nat.factorial_pos _) (pow_pos (autCard_pos t) _)

/-- `treeAutCard` of a representative equals `autCard` of its class. -/
private theorem treeAutCard_out (x : Nonplanar α) :
    treeAutCard x.out = autCard x := by
  conv_rhs => rw [← x.out_eq]
  rfl

/-- The `treeAutCard`-product over `Quotient.out`-representatives of a list
    of nonplanar trees equals the `autCard`-product over the list. -/
private theorem prod_out_treeAutCard (lst : List (Nonplanar α)) :
    ((lst.map Quotient.out).map treeAutCard).prod = (lst.map autCard).prod := by
  congr 1
  rw [List.map_map]
  exact List.map_congr_left fun x _ => treeAutCard_out x

omit [DecidableEq α] in
/-- The mk-multiset of `Q.out`-lifted list of nonplanar trees equals the
    original list. -/
private theorem ofList_map_mk_qout (lst : List (Nonplanar α)) :
    (Multiset.ofList (((lst.map Quotient.out).map mk)) :
        Multiset (Nonplanar α)) = Multiset.ofList lst := by
  rw [List.map_map]
  congr 1
  exact (List.map_congr_left (fun x _ => x.out_eq)).trans (List.map_id lst)

/-- `autCard` on the smart `node` constructor: the recursive definition.
    Proof: induct on `F` to get a list rep `lst`; `treeAutCard` on the
    tree node splits into a children-product factor (which lifts to
    `(lst.map autCard).prod` via `prod_out_treeAutCard`) and a
    `multinomialFactor` factor (which lifts to `multinomialFactor F` via
    `ofList_map_mk_qout`). Combine via `Finset.prod_multiset_map_count`
    (to express `(F.map autCard).prod` as a Finset prod over `F.toFinset`)
    and `Finset.prod_mul_distrib` (to recombine the two legs into
    `forestAutCard F`). -/
@[simp] theorem autCard_node (a : α) (F : Multiset (Nonplanar α)) :
    autCard (Nonplanar.node a F) = forestAutCard F := by
  induction F using Quotient.inductionOn with
  | h lst =>
    -- Convert `Quotient.mk _ lst` to `Multiset.ofList lst` (definitionally equal).
    show treeAutCard (RoseTree.node a (lst.map Quotient.out)) =
        forestAutCard (Multiset.ofList lst)
    rw [treeAutCard_node, prod_out_treeAutCard lst, ofList_map_mk_qout lst]
    -- LHS: (lst.map autCard).prod * multinomialFactor (Multiset.ofList lst).
    -- RHS: forestAutCard (Multiset.ofList lst) =
    --      (Multiset.ofList lst).toFinset.prod fun t => (count t)! * autCard t ^ count t.
    unfold forestAutCard multinomialFactor
    -- (lst.map autCard).prod = ((Multiset.ofList lst).map autCard).prod
    --                       = ∏ t ∈ toFinset, autCard t ^ count t.
    have hprod_lst : ((Multiset.ofList lst).map autCard).prod
                  = ((Multiset.ofList lst).toFinset).prod
                      fun t => autCard t ^ (Multiset.ofList lst).count t :=
      Finset.prod_multiset_map_count (Multiset.ofList lst) autCard
    have hcoe : (lst.map autCard).prod = ((Multiset.ofList lst).map autCard).prod := rfl
    rw [hcoe, hprod_lst]
    -- Combine the two Finset prods via Finset.prod_mul_distrib.
    rw [← Finset.prod_mul_distrib]
    -- Match summands: pow * factorial = factorial * pow.
    apply Finset.prod_congr rfl
    intro t _
    ring

/-! ### Multinomial split identity

The automorphism count of a disjoint union `F + G` factors through any
fixed split: `|Aut(F+G)| = N · |Aut F| · |Aut G|` where `N` counts the
occurrences of the ordered pair `(F, G)` among the two-sided sub-multiset
splits of `F + G` (`Multiset.antidiagonal`). Per distinct tree `t`, this
is `(m₁ + m₂)! = C(m₁ + m₂, m₁) · m₁! · m₂!` with `mᵢ` the
multiplicities in `F`, `G` — `Nat.add_choose_mul_factorial_mul_factorial`
aggregated over `(F + G).toFinset`. The adjoint role: this is exactly
what makes the symmetry-weighted pairing turn CK multiplication into the
sub-multiset split coproduct (`GrossmanLarsonPairing.pairing_of'_mul`).

Computationally validated (`scratch/validate_duality.lean`, V2 battery,
exhaustive over forests of weight ≤ 3 plus duplicate-tree traps). -/

/-- Count of an ordered split `(F, G)` in `antidiagonal (F + G)` equals the
    count of `G` in `powerset (F + G)`: `antidiagonal_eq_map_powerset`
    expresses the antidiagonal as the powerset mapped through the injective
    `t ↦ (s - t, t)`, and the second coordinate `G` is in the image at
    exactly one preimage. -/
private theorem count_antidiagonal_eq_count_powerset
    (F G : Multiset (Nonplanar α)) :
    Multiset.count (F, G) (Multiset.antidiagonal (F + G)) =
      Multiset.count G (Multiset.powerset (F + G)) := by
  rw [Multiset.antidiagonal_eq_map_powerset]
  -- Map is `fun t => (F + G - t, t)`, which is injective in `t` (second coord).
  have hinj : Function.Injective
      (fun t : Multiset (Nonplanar α) => (F + G - t, t)) :=
    fun _ _ h => congrArg Prod.snd h
  -- `(F, G) = (F + G - G, G)` because `F + G - G = F`.
  have hpair : ((F + G - G, G) : Multiset (Nonplanar α) × _) = (F, G) := by
    rw [Multiset.add_sub_cancel_right]
  rw [← hpair]
  exact Multiset.count_map_eq_count' _ _ hinj _

/-- Peel the multiplicity at `a` out of a `Multiset.toFinsupp`-product, for `a ∈ M`. -/
private theorem prod_toFinsupp_of_mem (M : Multiset (Nonplanar α)) (a : Nonplanar α)
    (g : Nonplanar α → ℕ → ℕ) (ha : a ∈ M) :
    M.toFinsupp.prod g = g a (M.count a) * (Finsupp.erase a M.toFinsupp).prod g := by
  have ha' : a ∈ M.toFinsupp.support := by
    rw [Multiset.toFinsupp_support, Multiset.mem_toFinset]; exact ha
  rw [← Finsupp.mul_prod_erase M.toFinsupp a g ha', Multiset.toFinsupp_apply]

/-- Erasing `a` from `(a ::ₘ M).toFinsupp` agrees with erasing it from `M.toFinsupp`:
    the two finsupps coincide away from `a`. -/
private theorem erase_toFinsupp_cons (a : Nonplanar α) (M : Multiset (Nonplanar α)) :
    Finsupp.erase a (a ::ₘ M).toFinsupp = Finsupp.erase a M.toFinsupp := by
  ext t
  rcases eq_or_ne t a with rfl | ht
  · rw [Finsupp.erase_same, Finsupp.erase_same]
  · rw [Finsupp.erase_ne ht, Finsupp.erase_ne ht, Multiset.toFinsupp_apply,
        Multiset.toFinsupp_apply, Multiset.count_cons_of_ne ht]

/-- The count of `F` in `powerset H` is the product over distinct elements
    of `H` of `(H.count t).choose (F.count t)`, provided `F ≤ H`. Proved by
    induction on `H`: at `H = a ::ₘ H'`, peel the multiplicity of `a` out of
    each `toFinsupp`-product (`prod_toFinsupp_of_mem`) and close with Pascal's
    rule `Nat.choose_succ_succ'` at the single updated point. -/
private theorem count_powerset_eq_prod_choose
    (F H : Multiset (Nonplanar α)) (hFH : F ≤ H) :
    Multiset.count F (Multiset.powerset H) =
      H.toFinsupp.prod (fun t k => k.choose (F.count t)) := by
  induction H using Multiset.induction_on generalizing F with
  | empty =>
    obtain rfl := Multiset.le_zero.mp hFH
    simp
  | cons a H' ih =>
    rw [Multiset.powerset_cons, Multiset.count_add,
        prod_toFinsupp_of_mem (a ::ₘ H') a _ (Multiset.mem_cons_self a H'),
        Multiset.count_cons_self, erase_toFinsupp_cons]
    have h_inj : Function.Injective (Multiset.cons a) := fun _ _ h =>
      (Multiset.cons_inj_right a).mp h
    by_cases ha_in_F : a ∈ F
    · -- `a ∈ F`: `F = a ::ₘ F'` with `F' ≤ H'`.
      obtain ⟨F', rfl⟩ := Multiset.exists_cons_of_mem ha_in_F
      have hF'_le : F' ≤ H' := (Multiset.cons_le_cons_iff a).mp hFH
      have hca : Multiset.count a F' ≤ Multiset.count a H' := Multiset.le_iff_count.mp hF'_le a
      -- Off `a`, the erased product does not see the `cons a`.
      have hP : (Finsupp.erase a H'.toFinsupp).prod (fun t k => k.choose ((a ::ₘ F').count t)) =
          (Finsupp.erase a H'.toFinsupp).prod (fun t k => k.choose (F'.count t)) := by
        refine Finsupp.prod_congr fun x hx => ?_
        have hxa : x ≠ a := by rw [Finsupp.support_erase, Finset.mem_erase] at hx; exact hx.1
        rw [Multiset.count_cons_of_ne hxa]
      have h_second : Multiset.count (a ::ₘ F') ((Multiset.powerset H').map (Multiset.cons a)) =
          Multiset.count F' (Multiset.powerset H') := Multiset.count_map_eq_count' _ _ h_inj F'
      rw [h_second, Multiset.count_cons_self, hP, ih F' hF'_le]
      by_cases ha_in_H' : a ∈ H'
      · -- Peel `a` from the second summand's IH; the first splits by Pascal.
        rw [prod_toFinsupp_of_mem H' a _ ha_in_H']
        by_cases h_strict : Multiset.count a F' + 1 ≤ Multiset.count a H'
        · have h_le' : a ::ₘ F' ≤ H' := by
            rw [Multiset.le_iff_count]
            intro b
            rcases eq_or_ne b a with rfl | hb
            · rw [Multiset.count_cons_self]; omega
            · have hb' := Multiset.le_iff_count.mp hFH b
              rw [Multiset.count_cons_of_ne hb, Multiset.count_cons_of_ne hb] at hb'
              rwa [Multiset.count_cons_of_ne hb]
          rw [ih (a ::ₘ F') h_le', prod_toFinsupp_of_mem H' a _ ha_in_H',
            Multiset.count_cons_self, hP, ← add_mul, Nat.choose_succ_succ']
          ring
        · -- `count a F' = count a H'`: the first summand is `0` and both `choose`s are `1`.
          have h_eq : Multiset.count a F' = Multiset.count a H' := by omega
          have h_first_zero : Multiset.count (a ::ₘ F') (Multiset.powerset H') = 0 := by
            rw [Multiset.count_eq_zero, Multiset.mem_powerset]
            intro h_le_H'
            have := Multiset.le_iff_count.mp h_le_H' a
            rw [Multiset.count_cons_self] at this; omega
          rw [h_first_zero, Nat.zero_add, h_eq, Nat.choose_self, Nat.choose_self]
      · -- `a ∉ H'`: erase is a no-op and the first summand vanishes.
        rw [Finsupp.erase_of_notMem_support
          (by rw [Multiset.toFinsupp_support, Multiset.mem_toFinset]; exact ha_in_H')]
        have h_first_zero : Multiset.count (a ::ₘ F') (Multiset.powerset H') = 0 := by
          rw [Multiset.count_eq_zero, Multiset.mem_powerset]
          exact fun h_le_H' => ha_in_H' (Multiset.subset_of_le h_le_H' (Multiset.mem_cons_self a F'))
        have h_count_aF' : Multiset.count a F' = 0 :=
          Multiset.count_eq_zero.mpr fun h => ha_in_H' (Multiset.subset_of_le hF'_le h)
        rw [h_first_zero, Nat.zero_add, Multiset.count_eq_zero.mpr ha_in_H', h_count_aF']
        simp
    · -- `a ∉ F`: `F ≤ H'` and the second summand vanishes.
      have hF_le' : F ≤ H' := by
        rw [Multiset.le_iff_count]
        intro b
        rcases eq_or_ne b a with rfl | hb
        · rw [Multiset.count_eq_zero.mpr ha_in_F]; exact Nat.zero_le _
        · have := Multiset.le_iff_count.mp hFH b
          rwa [Multiset.count_cons_of_ne hb] at this
      have h_second_zero :
          Multiset.count F ((Multiset.powerset H').map (Multiset.cons a)) = 0 := by
        rw [Multiset.count_eq_zero, Multiset.mem_map]
        rintro ⟨S, _, hS⟩
        exact ha_in_F (hS ▸ Multiset.mem_cons_self a S)
      have h_count_aF : Multiset.count a F = 0 := Multiset.count_eq_zero.mpr ha_in_F
      rw [h_second_zero, Nat.add_zero, ih F hF_le', h_count_aF, Nat.choose_zero_right, one_mul]
      by_cases ha_in_H' : a ∈ H'
      · rw [prod_toFinsupp_of_mem H' a _ ha_in_H', h_count_aF, Nat.choose_zero_right, one_mul]
      · rw [Finsupp.erase_of_notMem_support
          (by rw [Multiset.toFinsupp_support, Multiset.mem_toFinset]; exact ha_in_H')]

/-- Per-element multinomial: at every distinct tree `t`,
    `((F+G).count t).choose (G.count t) * (F.count t)! * (G.count t)!
      = ((F+G).count t)!`. This is
    `Nat.add_choose_mul_factorial_mul_factorial` with
    `i = F.count t`, `j = G.count t`, after rewriting
    `(F+G).count t = F.count t + G.count t`. -/
private theorem pointwise_factorial_split
    (F G : Multiset (Nonplanar α)) (t : Nonplanar α) :
    ((F + G).count t).choose (G.count t) *
        Nat.factorial (F.count t) * Nat.factorial (G.count t) =
      Nat.factorial ((F + G).count t) := by
  rw [Multiset.count_add]
  exact Nat.add_choose_mul_factorial_mul_factorial _ _

/-- **Multinomial split identity** for `forestAutCard`:
    `count (F,G) (antidiagonal (F+G)) · |Aut F| · |Aut G| = |Aut (F+G)|`. -/
theorem forestAutCard_add (F G : Multiset (Nonplanar α)) :
    Multiset.count (F, G) (Multiset.antidiagonal (F + G)) *
      (forestAutCard F * forestAutCard G) = forestAutCard (F + G) := by
  rw [count_antidiagonal_eq_count_powerset,
      count_powerset_eq_prod_choose G (F + G) (Multiset.le_add_left G F),
      forestAutCard_eq_prod F, forestAutCard_eq_prod G, forestAutCard_eq_prod (F + G)]
  -- Extend the `F`- and `G`-legs onto `(F+G).toFinset` (each missing factor is
  -- `0! · autCard ^ 0 = 1`), then match the combined product pointwise.
  have hext : ∀ M : Multiset (Nonplanar α), M ≤ F + G →
      M.toFinsupp.prod (fun t k => k.factorial * autCard t ^ k) =
        ∏ x ∈ (F + G).toFinset, (M.count x).factorial * autCard x ^ M.count x := by
    intro M hM
    have hsub : M.toFinsupp.support ⊆ (F + G).toFinset := fun t ht => by
      rw [Multiset.toFinsupp_support, Multiset.mem_toFinset] at ht
      exact Multiset.mem_toFinset.mpr (Multiset.subset_of_le hM ht)
    rw [Finsupp.prod_of_support_subset _ hsub
          (fun t k => k.factorial * autCard t ^ k) (fun i _ => by simp)]
    exact Finset.prod_congr rfl fun x _ => by rw [Multiset.toFinsupp_apply]
  have hchoose : (F + G).toFinsupp.prod (fun t k => k.choose (G.count t)) =
      ∏ x ∈ (F + G).toFinset, ((F + G).count x).choose (G.count x) := by
    simp only [Finsupp.prod, Multiset.toFinsupp_support, Multiset.toFinsupp_apply]
  rw [hext F (Multiset.le_add_right F G), hext G (Multiset.le_add_left G F),
      hext (F + G) le_rfl, hchoose, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [Multiset.count_add, pow_add]
  have h_fact := pointwise_factorial_split F G t
  rw [Multiset.count_add] at h_fact
  set m₁ := F.count t
  set m₂ := G.count t
  set a := autCard t
  -- h_fact : (m₁ + m₂).choose m₂ * m₁! * m₂! = (m₁ + m₂)!
  calc (m₁ + m₂).choose m₂ * (m₁.factorial * a ^ m₁ * (m₂.factorial * a ^ m₂))
      = ((m₁ + m₂).choose m₂ * m₁.factorial * m₂.factorial) *
          (a ^ m₁ * a ^ m₂) := by ring
    _ = (m₁ + m₂).factorial * (a ^ m₁ * a ^ m₂) := by rw [h_fact]

end Nonplanar

end RootedTree
