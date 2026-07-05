/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.RoseTree.Nonplanar
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
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

variable {α : Type*}

/-! ### RoseTree-representative substrate

`treeAutCard` computes `|Aut(mk t)|` on a planar `RoseTree` representative
`t`; `Perm`-invariance (below) lets it descend to `Nonplanar.autCard`
through the quotient. -/

/-- Symmetry-factor at one node: `∏_{distinct c ∈ M} (M.count c)!`. Uses
    `Classical.decEq` for `Multiset.toFinset` and `Multiset.count`. -/
noncomputable def multinomialFactor (M : Multiset (Nonplanar α)) : ℕ :=
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  M.toFinset.prod fun t => Nat.factorial (M.count t)

/-- The automorphism count `|Aut(mk t)|` of the nonplanar tree represented
    by a planar `RoseTree` `t`. Substrate for `Nonplanar.autCard` (which lifts
    it through the `Perm` quotient). At a node, the product of the
    children's counts times `multinomialFactor` on the multiset of
    nonplanar-`mk` children (counting symmetric rearrangements). -/
noncomputable def treeAutCard : RoseTree α → ℕ
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
    0 < multinomialFactor M := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  unfold multinomialFactor
  exact Finset.prod_pos fun _ _ => Nat.factorial_pos _

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
noncomputable def autCard : Nonplanar α → ℕ :=
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
theorem autCard_pos (t : Nonplanar α) : 0 < autCard t := by
  induction t using Quotient.inductionOn with
  | h p => exact treeAutCard_pos p

/-- The cardinality `|Aut(F)|` of the automorphism group of a forest
    `F` (multiset of nonplanar trees), defined as the product over
    distinct trees `T ∈ F`:
    ```
    forestAutCard F = ∏_{distinct T ∈ F} (F.count T)! · (autCard T)^(F.count T)
    ```
    Uses `Classical.decEq` for the multiset operations (the function is
    noncomputable regardless).

    Stays in `Nonplanar` namespace (rather than `Forest`) because
    `Forest = Multiset` is just a stylistic alias used at the
    `ConnesKreimer` algebra layer; here we work directly with
    `Multiset (Nonplanar α)` to keep the combinatorics layer free of
    algebra-layer abbreviations. -/
noncomputable def forestAutCard (F : Multiset (Nonplanar α)) : ℕ :=
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  F.toFinset.prod fun t => Nat.factorial (F.count t) * autCard t ^ F.count t

/-- The empty forest has trivial aut group. -/
@[simp] theorem forestAutCard_zero :
    forestAutCard (0 : Multiset (Nonplanar α)) = 1 := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  simp [forestAutCard]

/-- The aut group of any forest is non-trivial (contains identity).
    Each factor `(F.count t)! * autCard t ^ F.count t` is positive
    (factorial always positive; `autCard_pos` gives the tree factor). -/
theorem forestAutCard_pos (F : Multiset (Nonplanar α)) : 0 < forestAutCard F := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
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
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
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
    letI : DecidableEq (Nonplanar α) := Classical.decEq _
    Multiset.count (F, G) (Multiset.antidiagonal (F + G)) =
      Multiset.count G (Multiset.powerset (F + G)) := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  rw [Multiset.antidiagonal_eq_map_powerset]
  -- Map is `fun t => (F + G - t, t)`, which is injective in `t` (second coord).
  have hinj : Function.Injective
      (fun t : Multiset (Nonplanar α) => (F + G - t, t)) := by
    intro t₁ t₂ h
    exact ((Prod.mk.injEq _ _ _ _).mp h).2
  -- `(F, G) = (F + G - G, G)` because `F + G - G = F`.
  have hpair : ((F + G - G, G) : Multiset (Nonplanar α) × _) = (F, G) := by
    rw [Multiset.add_sub_cancel_right]
  rw [← hpair]
  exact Multiset.count_map_eq_count' _ _ hinj _

/-- Pascal-style aggregation helper used inside `count_powerset_eq_prod_choose`.
    At every element of `H'.toFinset`, the per-element identity
    `H'.count t.choose ((a ::ₘ F').count t) + H'.count t.choose (F'.count t)
      = (a ::ₘ H').count t.choose ((a ::ₘ F').count t)` collapses two
    `H'.count t`-indexed products into one `(a ::ₘ H').count t`-indexed product,
    using `Nat.choose_succ_succ'` at `t = a` and matching `cons`-counts elsewhere. -/
private theorem pascal_choose_sum_aux
    (F' H' : Multiset (Nonplanar α)) (a : Nonplanar α)
    (ha_in_H' : a ∈ H') :
    letI : DecidableEq (Nonplanar α) := Classical.decEq _
    H'.toFinset.prod (fun t => (H'.count t).choose ((a ::ₘ F').count t)) +
        H'.toFinset.prod (fun t => (H'.count t).choose (F'.count t)) =
      H'.toFinset.prod
        (fun t => ((a ::ₘ H').count t).choose ((a ::ₘ F').count t)) := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  -- Pull `a` out of each Finset prod via `prod_eq_prod_diff_singleton_mul`.
  have ha_toFin : a ∈ H'.toFinset := Multiset.mem_toFinset.mpr ha_in_H'
  rw [Finset.prod_eq_prod_sdiff_singleton_mul ha_toFin
        (f := fun t => (H'.count t).choose ((a ::ₘ F').count t)),
      Finset.prod_eq_prod_sdiff_singleton_mul ha_toFin
        (f := fun t => (H'.count t).choose (F'.count t)),
      Finset.prod_eq_prod_sdiff_singleton_mul ha_toFin
        (f := fun t => ((a ::ₘ H').count t).choose ((a ::ₘ F').count t))]
  -- At each `t ∈ H'.toFinset \ {a}`, the three products agree (count_cons on a t ≠ a).
  have h_diff_LHS1 :
      (H'.toFinset \ {a}).prod (fun t => (H'.count t).choose ((a ::ₘ F').count t))
        = (H'.toFinset \ {a}).prod (fun t => (H'.count t).choose (F'.count t)) := by
    refine Finset.prod_congr rfl ?_
    intro t ht
    have ht_ne_a : t ≠ a := by
      rw [Finset.mem_sdiff, Finset.mem_singleton] at ht
      exact ht.2
    rw [Multiset.count_cons_of_ne ht_ne_a]
  have h_diff_RHS :
      (H'.toFinset \ {a}).prod
          (fun t => ((a ::ₘ H').count t).choose ((a ::ₘ F').count t))
        = (H'.toFinset \ {a}).prod (fun t => (H'.count t).choose (F'.count t)) := by
    refine Finset.prod_congr rfl ?_
    intro t ht
    have ht_ne_a : t ≠ a := by
      rw [Finset.mem_sdiff, Finset.mem_singleton] at ht
      exact ht.2
    rw [Multiset.count_cons_of_ne ht_ne_a,
        Multiset.count_cons_of_ne ht_ne_a]
  rw [h_diff_LHS1, h_diff_RHS]
  -- Now: P * x + P * y = P * z (where P = diff prod common factor).
  rw [← mul_add]
  congr 1
  -- Normalize counts at `a` via `count_cons_self`.
  simp only [Multiset.count_cons_self]
  -- Goal:
  --   H'.count a.choose (F'.count a + 1) + H'.count a.choose (F'.count a)
  --   = (H'.count a + 1).choose (F'.count a + 1)
  -- Pascal: `(n+1).choose (k+1) = n.choose k + n.choose (k+1)`.
  rw [Nat.choose_succ_succ', add_comm]

/-- The count of `F` in `powerset H` is the product over distinct elements
    of `H` of `(H.count t).choose (F.count t)`, provided `F ≤ H`. Proved by
    induction on `H`: at `H = a ::ₘ H'`, split `powerset (a ::ₘ H')` via
    Pascal's rule and case on `a ∈ F`. -/
private theorem count_powerset_eq_prod_choose
    (F H : Multiset (Nonplanar α)) (hFH : F ≤ H) :
    letI : DecidableEq (Nonplanar α) := Classical.decEq _
    Multiset.count F (Multiset.powerset H) =
      H.toFinset.prod (fun t => (H.count t).choose (F.count t)) := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  induction H using Multiset.induction_on generalizing F with
  | empty =>
    -- `F ≤ 0` forces `F = 0`. RHS is empty product = 1.
    have hF : F = 0 := Multiset.le_zero.mp hFH
    subst hF
    simp [Multiset.powerset_zero, Multiset.toFinset_zero]
  | cons a H' ih =>
    rw [Multiset.powerset_cons, Multiset.count_add]
    -- `cons a` is injective.
    have h_inj : Function.Injective (Multiset.cons a) := fun _ _ h =>
      (Multiset.cons_inj_right a).mp h
    by_cases ha_in_F : a ∈ F
    · -- `a ∈ F`: F = a ::ₘ F' with F' ≤ H'.
      obtain ⟨F', hF_eq⟩ := Multiset.exists_cons_of_mem ha_in_F
      subst hF_eq
      have hF'_le : F' ≤ H' := (Multiset.cons_le_cons_iff a).mp hFH
      -- Second summand = count F' (powerset H'); rewrite via `count_map_eq_count'`.
      have h_second :
          Multiset.count (a ::ₘ F')
              ((Multiset.powerset H').map (Multiset.cons a)) =
            Multiset.count F' (Multiset.powerset H') :=
        Multiset.count_map_eq_count' _ _ h_inj F'
      by_cases ha_in_H' : a ∈ H'
      · -- a ∈ H'. Sub-case on whether `a ::ₘ F' ≤ H'` (i.e. `count a F' < count a H'`).
        have ha_pos : 1 ≤ Multiset.count a H' :=
          Multiset.one_le_count_iff_mem.mpr ha_in_H'
        have h_aH'_toFinset : (a ::ₘ H').toFinset = H'.toFinset := by
          rw [Multiset.toFinset_cons]
          exact Finset.insert_eq_of_mem (Multiset.mem_toFinset.mpr ha_in_H')
        -- F'.count a ≤ H'.count a (from F' ≤ H').
        have h_cF'_le_cH' : Multiset.count a F' ≤ Multiset.count a H' :=
          Multiset.le_iff_count.mp hF'_le a
        by_cases h_strict : Multiset.count a F' + 1 ≤ Multiset.count a H'
        · -- A1: `a ::ₘ F' ≤ H'`. Apply ih to both `a ::ₘ F'` and `F'`.
          have h_le' : a ::ₘ F' ≤ H' := by
            rw [Multiset.le_iff_count]
            intro b
            have h_master := Multiset.le_iff_count.mp hFH b
            by_cases hb : b = a
            · rw [hb, Multiset.count_cons_self, Multiset.count_cons_self] at h_master
              rw [hb, Multiset.count_cons_self]; omega
            · rw [Multiset.count_cons_of_ne hb, Multiset.count_cons_of_ne hb] at h_master
              rw [Multiset.count_cons_of_ne hb]; exact h_master
          rw [ih (a ::ₘ F') h_le', h_second, ih F' hF'_le]
          rw [h_aH'_toFinset]
          exact pascal_choose_sum_aux F' H' a ha_in_H'
        · -- A2: `count a F' + 1 > count a H'`. Combined with `count a F' ≤ count a H'`,
          -- forces `count a F' = count a H'`. So `a ::ₘ F' ≰ H'`, first summand = 0.
          have h_eq : Multiset.count a F' = Multiset.count a H' := by omega
          have h_first_zero :
              Multiset.count (a ::ₘ F') (Multiset.powerset H') = 0 := by
            rw [Multiset.count_eq_zero, Multiset.mem_powerset]
            intro h_le_H'
            have := Multiset.le_iff_count.mp h_le_H' a
            rw [Multiset.count_cons_self] at this
            omega
          rw [h_first_zero, Nat.zero_add, h_second, ih F' hF'_le]
          rw [h_aH'_toFinset]
          -- Goal: ∏ t ∈ H'.toFinset, H'.count t.choose F'.count t
          --     = ∏ t ∈ H'.toFinset, (a ::ₘ H').count t.choose (a ::ₘ F').count t.
          refine Finset.prod_congr rfl ?_
          intro t _
          by_cases ht_eq : t = a
          · -- At t = a: H'.count a.choose F'.count a on LHS;
            -- (H'.count a + 1).choose (F'.count a + 1) on RHS.
            -- Using h_eq, F'.count a = H'.count a, so LHS = n.choose n = 1 and
            -- RHS = (n+1).choose (n+1) = 1.
            subst ht_eq
            rw [Multiset.count_cons_self, Multiset.count_cons_self, h_eq]
            simp
          · rw [Multiset.count_cons_of_ne ht_eq, Multiset.count_cons_of_ne ht_eq]
      · -- a ∉ H': first summand is 0 (a ::ₘ F' ≰ H').
        have h_first_zero : Multiset.count (a ::ₘ F') (Multiset.powerset H') = 0 := by
          rw [Multiset.count_eq_zero, Multiset.mem_powerset]
          intro h_le_H'
          have := Multiset.le_iff_count.mp h_le_H' a
          rw [Multiset.count_cons_self, Multiset.count_eq_zero.mpr ha_in_H'] at this
          omega
        rw [h_first_zero, Nat.zero_add, h_second, ih F' hF'_le]
        rw [Multiset.toFinset_cons]
        have h_a_notin : a ∉ H'.toFinset := fun h =>
          ha_in_H' (Multiset.mem_toFinset.mp h)
        rw [Finset.prod_insert h_a_notin]
        rw [Multiset.count_cons_self, Multiset.count_cons_self,
            Multiset.count_eq_zero.mpr ha_in_H']
        -- `F'.count a = 0` since `F' ≤ H'` and `a ∉ H'`.
        have h_count_aF' : Multiset.count a F' = 0 := by
          rw [Multiset.count_eq_zero]
          intro h_mem
          exact ha_in_H' (Multiset.subset_of_le hF'_le h_mem)
        rw [h_count_aF']
        simp only [Nat.zero_add, Nat.choose_self, one_mul]
        refine Finset.prod_congr rfl ?_
        intro t ht
        have ht_ne_a : t ≠ a := fun h => h_a_notin (h ▸ ht)
        rw [Multiset.count_cons_of_ne ht_ne_a, Multiset.count_cons_of_ne ht_ne_a]
    · -- a ∉ F: F ≤ H'.
      have hF_le' : F ≤ H' := by
        rw [Multiset.le_iff_count]
        intro b
        by_cases hb : b = a
        · subst hb
          rw [Multiset.count_eq_zero.mpr ha_in_F]
          exact Nat.zero_le _
        · have h_master := Multiset.le_iff_count.mp hFH b
          rw [Multiset.count_cons_of_ne hb] at h_master
          exact h_master
      -- Second summand is 0 (F doesn't contain `a`).
      have h_second_zero :
          Multiset.count F ((Multiset.powerset H').map (Multiset.cons a)) = 0 := by
        rw [Multiset.count_eq_zero, Multiset.mem_map]
        rintro ⟨S, _, hS⟩
        have : a ∈ F := hS ▸ Multiset.mem_cons_self a S
        exact ha_in_F this
      rw [h_second_zero, Nat.add_zero, ih F hF_le']
      rw [Multiset.toFinset_cons]
      by_cases ha_in_H' : a ∈ H'
      · rw [Finset.insert_eq_of_mem (Multiset.mem_toFinset.mpr ha_in_H')]
        refine Finset.prod_congr rfl ?_
        intro t _
        by_cases ht_eq : t = a
        · subst ht_eq
          rw [Multiset.count_cons_self, Multiset.count_eq_zero.mpr ha_in_F]
          simp [Nat.choose_zero_right]
        · rw [Multiset.count_cons_of_ne ht_eq]
      · have h_a_notin : a ∉ H'.toFinset :=
          fun h => ha_in_H' (Multiset.mem_toFinset.mp h)
        rw [Finset.prod_insert h_a_notin]
        rw [Multiset.count_cons_self, Multiset.count_eq_zero.mpr ha_in_H',
            Multiset.count_eq_zero.mpr ha_in_F]
        simp only [Nat.zero_add, Nat.choose_zero_right, one_mul]
        refine Finset.prod_congr rfl ?_
        intro t ht
        have ht_ne_a : t ≠ a := fun h => h_a_notin (h ▸ ht)
        rw [Multiset.count_cons_of_ne ht_ne_a]

/-- Per-element multinomial: at every distinct tree `t`,
    `((F+G).count t).choose (G.count t) * (F.count t)! * (G.count t)!
      = ((F+G).count t)!`. This is
    `Nat.add_choose_mul_factorial_mul_factorial` with
    `i = F.count t`, `j = G.count t`, after rewriting
    `(F+G).count t = F.count t + G.count t`. -/
private theorem pointwise_factorial_split
    (F G : Multiset (Nonplanar α)) (t : Nonplanar α) :
    letI : DecidableEq (Nonplanar α) := Classical.decEq _
    ((F + G).count t).choose (G.count t) *
        Nat.factorial (F.count t) * Nat.factorial (G.count t) =
      Nat.factorial ((F + G).count t) := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  rw [Multiset.count_add]
  exact Nat.add_choose_mul_factorial_mul_factorial _ _

/-- **Multinomial split identity** for `forestAutCard`:
    `count (F,G) (antidiagonal (F+G)) · |Aut F| · |Aut G| = |Aut (F+G)|`. -/
theorem forestAutCard_add (F G : Multiset (Nonplanar α)) :
    (letI : DecidableEq (Nonplanar α) := Classical.decEq _
     Multiset.count (F, G) (Multiset.antidiagonal (F + G))) *
      (forestAutCard F * forestAutCard G) = forestAutCard (F + G) := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  rw [count_antidiagonal_eq_count_powerset]
  rw [count_powerset_eq_prod_choose G (F + G) (Multiset.le_add_left G F)]
  -- Unfold forestAutCard in three places.
  unfold forestAutCard
  -- Extend `F.toFinset`/`G.toFinset` prods to `(F+G).toFinset` prods
  -- (extension by factors equal to 1).
  set S := (F + G).toFinset with hS_def
  have hF_sub : F.toFinset ⊆ S := by
    intro t ht
    rw [hS_def, Multiset.mem_toFinset] at *
    exact Multiset.subset_of_le (Multiset.le_add_right F G) ht
  have hG_sub : G.toFinset ⊆ S := by
    intro t ht
    rw [hS_def, Multiset.mem_toFinset] at *
    exact Multiset.subset_of_le (Multiset.le_add_left G F) ht
  have hF_ext : F.toFinset.prod
      (fun t => Nat.factorial (F.count t) * autCard t ^ F.count t) =
      S.prod (fun t => Nat.factorial (F.count t) * autCard t ^ F.count t) := by
    refine Finset.prod_subset hF_sub ?_
    intro t _ htF
    have h_cF : F.count t = 0 := Multiset.count_eq_zero.mpr (fun h_mem =>
      htF (Multiset.mem_toFinset.mpr h_mem))
    rw [h_cF]; simp
  have hG_ext : G.toFinset.prod
      (fun t => Nat.factorial (G.count t) * autCard t ^ G.count t) =
      S.prod (fun t => Nat.factorial (G.count t) * autCard t ^ G.count t) := by
    refine Finset.prod_subset hG_sub ?_
    intro t _ htG
    have h_cG : G.count t = 0 := Multiset.count_eq_zero.mpr (fun h_mem =>
      htG (Multiset.mem_toFinset.mpr h_mem))
    rw [h_cG]; simp
  rw [hF_ext, hG_ext]
  -- Combine into a single `Finset.prod` over `S`.
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro t _
  -- Per-element identity:
  --   choose(G.count t) * ((F.count t! * a^F.count t) * (G.count t! * a^G.count t))
  -- = (F.count t + G.count t)! * a^(F.count t + G.count t)
  -- where a = autCard t. Use `pointwise_factorial_split` and `pow_add`.
  have h_fact := pointwise_factorial_split F G t
  rw [Multiset.count_add] at h_fact
  rw [Multiset.count_add, pow_add]
  -- Goal: choose(m₂) * ((m₁! * a^m₁) * (m₂! * a^m₂)) = (m₁+m₂)! * (a^m₁ * a^m₂)
  -- where m₁ = F.count t, m₂ = G.count t.
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
