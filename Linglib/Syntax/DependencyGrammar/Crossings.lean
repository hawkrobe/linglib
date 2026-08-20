/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.DependencyGrammar.Projectivity
import Linglib.Syntax.DependencyGrammar.Length
import Linglib.Core.Combinatorics.Enumerative.PermutationPattern
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Crossings under random linearization

This file proves that if a sentence's word order were lost and replaced by
a uniformly random one, the expected number of crossings would depend only
on the arc structure: two links cross in a third of the linearizations
when they share no endpoint, and in none otherwise. No tree hypothesis is
needed; the identity holds for any link structure.

## Main definitions

* `Graph.crossingsUnder` is the crossings `g` would show under a
  permutation of its positions.
* `Graph.disjointLinkPairs` is the number of unordered pairs of links
  sharing no endpoint — the pairs that can cross at all.

## Main results

* `Graph.crossings_relabel`: the crossings of a relabelled graph are the
  crossings under the permutation.
* `Graph.three_mul_sum_crossings_relabel`: the expected-crossings identity
  `3 * ∑ σ, (g.relabel σ).crossings = n ! * g.disjointLinkPairs`.

## References

[ferrer-i-cancho-2017] — Random crossings in dependency trees, source of
the expected-crossings identity (eq. 13)
[ferrer-i-cancho-2013] — Hubiness, length, crossings and their
relationships in syntactic dependencies, reduces the disjoint-pair count
to the link count and the degree second moment
-/

namespace DependencyGrammar

open Finset Equiv Nat Matrix

variable {n : ℕ} (g : Graph n)

/-! ### Crossings under a relabelling -/

/-- The crossings `g` would show if its positions were rearranged by `σ`:
    crossing quadruples are scored in the positions `σ` assigns rather than
    in `g`'s own. -/
def Graph.crossingsUnder (σ : Perm (Fin n)) : Nat :=
  (Finset.univ.filter (λ x : Fin n × Fin n × Fin n × Fin n =>
    g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2 ∧
      Alternate (σ x.1) (σ x.2.1) (σ x.2.2.1) (σ x.2.2.2))).card

/-- The unordered pairs of links sharing no endpoint — the pairs that can
    cross at all, [ferrer-i-cancho-2017]'s potential crossings. Each pair is
    counted once, by the representative with both links least-endpoint-first
    and the earlier-starting link first. -/
def Graph.disjointLinkPairs : Nat :=
  (Finset.univ.filter (λ x : Fin n × Fin n × Fin n × Fin n =>
    g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2 ∧
      x.1 < x.2.1 ∧ x.2.2.1 < x.2.2.2 ∧ x.1 < x.2.2.1 ∧
        x.2.1 ≠ x.2.2.1 ∧ x.2.1 ≠ x.2.2.2)).card

variable {g}

@[simp] theorem Graph.crossingsUnder_one : g.crossingsUnder 1 = g.crossings := rfl

/-- Relabelling moves the crossings to the relabelled positions. -/
theorem Graph.crossings_relabel (σ : Perm (Fin n)) :
    (g.relabel σ).crossings = g.crossingsUnder σ := by
  refine Finset.card_equiv
    (σ.symm.prodCongr (σ.symm.prodCongr (σ.symm.prodCongr σ.symm))) ?_
  rintro ⟨a, b, c, d⟩
  simp [Graph.Linked, Alternate]

/-! ### One linearization in twenty-four alternates a distinct quadruple -/

private theorem injective_vec4 {w x y z : Fin n} (hwx : w ≠ x) (hwy : w ≠ y)
    (hwz : w ≠ z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Function.Injective ![w, x, y, z] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- Alternation is monotonicity of the permutation along the reordered
    quadruple. -/
private theorem alternate_comp_iff {a b c d : Fin n} (σ : Perm (Fin n))
    (hq : Function.Injective ![a, c, b, d]) :
    Alternate (σ a) (σ b) (σ c) (σ d) ↔ Monotone (σ ∘ ![a, c, b, d]) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ((Fin.strictMono_iff_lt_succ).mpr ?_).monotone
    intro i
    fin_cases i <;> simpa
  · intro hm
    have hs := hm.strictMono_of_injective (σ.injective.comp hq)
    exact ⟨by simpa using hs (show (0 : Fin 4) < 1 by decide),
      by simpa using hs (show (1 : Fin 4) < 2 by decide),
      by simpa using hs (show (2 : Fin 4) < 3 by decide)⟩

/-- One linearization in `24` puts four fixed distinct positions into the
    alternating pattern. -/
private theorem card_alternate {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    24 * #{σ : Perm (Fin n) | Alternate (σ a) (σ b) (σ c) (σ d)} = n ! := by
  have hq : Function.Injective ![a, c, b, d] :=
    injective_vec4 hac hab had (Ne.symm hbc) hcd hbd
  have h := factorial_mul_card_monotone_comp (⟨_, hq⟩ : Fin 4 ↪ Fin n)
  rw [Fintype.card_fin, show (4 : ℕ)! = 24 from rfl] at h
  rw [← h]
  refine congrArg (24 * ·) (Finset.card_equiv (Equiv.refl _) (λ σ => ?_))
  simpa using alternate_comp_iff σ hq

/-- Alternation forces its four positions to be distinct. -/
private theorem card_alternate_eq_zero {a b c d : Fin n}
    (h : ¬(a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)) :
    #{σ : Perm (Fin n) | Alternate (σ a) (σ b) (σ c) (σ d)} = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro σ - ⟨h1, h2, h3⟩
  refine h ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> omega

/-! ### Summing over linearizations, grouped by quadruple -/

private def distinct4 (x : Fin n × Fin n × Fin n × Fin n) : Prop :=
  x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2.1 ∧ x.1 ≠ x.2.2.2 ∧
    x.2.1 ≠ x.2.2.1 ∧ x.2.1 ≠ x.2.2.2 ∧ x.2.2.1 ≠ x.2.2.2

private instance : DecidablePred (distinct4 (n := n)) :=
  λ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The crossings of all linearizations, regrouped by the quadruple that
    crosses. -/
private theorem sum_crossingsUnder :
    ∑ σ : Perm (Fin n), g.crossingsUnder σ =
      ∑ x ∈ univ.filter (λ x : Fin n × Fin n × Fin n × Fin n =>
          g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2),
        #{σ : Perm (Fin n) | Alternate (σ x.1) (σ x.2.1) (σ x.2.2.1) (σ x.2.2.2)} := by
  simp only [Graph.crossingsUnder, Finset.card_filter]
  rw [Finset.sum_comm]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (λ x _ => ?_)
  by_cases h1 : g.Linked x.1 x.2.1 <;> by_cases h2 : g.Linked x.2.2.1 x.2.2.2 <;>
    simp [h1, h2]

/-- Each linked quadruple of distinct positions contributes `n !` to
    twenty-four times the crossings of all linearizations; degenerate
    quadruples contribute nothing. -/
private theorem mul_sum_crossingsUnder :
    24 * ∑ σ : Perm (Fin n), g.crossingsUnder σ =
      n ! * #(univ.filter (λ x : Fin n × Fin n × Fin n × Fin n =>
        (g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2) ∧ distinct4 x)) := by
  rw [sum_crossingsUnder, Finset.mul_sum]
  have hcongr : ∀ x ∈ univ.filter (λ x : Fin n × Fin n × Fin n × Fin n =>
      g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2),
      24 * #{σ : Perm (Fin n) |
        Alternate (σ x.1) (σ x.2.1) (σ x.2.2.1) (σ x.2.2.2)} =
        if distinct4 x then n ! else 0 := by
    intro x _
    by_cases hd : distinct4 x
    · rw [if_pos hd]
      obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd
      exact card_alternate d1 d2 d3 d4 d5 d6
    · rw [if_neg hd, card_alternate_eq_zero hd, Nat.mul_zero]
  rw [Finset.sum_congr rfl hcongr, ← Finset.sum_filter, Finset.filter_filter,
    Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-! ### Eight ordered witnesses per unordered disjoint pair -/

/-- An involution preserving `P` and toggling `C` halves the count: there
    are as many `P`-elements with `C` as without. -/
private theorem card_filter_eq_two_mul {α : Type*} [Fintype α] [DecidableEq α]
    {P C : α → Prop} [DecidablePred P] [DecidablePred C] (e : α → α)
    (he : Function.Involutive e) (hP : ∀ x, P x → P (e x))
    (hC : ∀ x, P x → (C (e x) ↔ ¬ C x)) :
    #(univ.filter P) = 2 * #(univ.filter (λ x => P x ∧ C x)) := by
  rw [← Finset.filter_filter,
    ← Finset.card_filter_add_card_filter_not (s := univ.filter P) C, two_mul]
  congr 1
  refine Finset.card_equiv (he.toPerm e) (λ x => ?_)
  simp only [mem_filter, mem_univ, true_and, Function.Involutive.coe_toPerm]
  constructor
  · rintro ⟨hp, hnc⟩
    exact ⟨hP x hp, (hC x hp).mpr hnc⟩
  · rintro ⟨hpe, hce⟩
    have hp : P x := he x ▸ hP _ hpe
    exact ⟨hp, (hC x hp).mp hce⟩

/-- Ordered linked quadruples of distinct positions come in eights: an
    orientation for each link and the order of the two links. -/
private theorem card_linked_distinct :
    #(univ.filter (λ x : Fin n × Fin n × Fin n × Fin n =>
        (g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2) ∧ distinct4 x)) =
      8 * g.disjointLinkPairs := by
  have h1 : #(univ.filter (λ x : Fin n × Fin n × Fin n × Fin n =>
        (g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2) ∧ distinct4 x)) =
      2 * #(univ.filter (λ x : Fin n × Fin n × Fin n × Fin n =>
        ((g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2) ∧ distinct4 x) ∧
          x.1 < x.2.1)) := by
    refine card_filter_eq_two_mul (λ x => (x.2.1, x.1, x.2.2)) (λ _ => rfl) ?_ ?_
    · rintro ⟨a, b, c, d⟩ ⟨⟨h1, h2⟩, d1, d2, d3, d4, d5, d6⟩
      exact ⟨⟨h1.symm, h2⟩, d1.symm, d4, d5, d2, d3, d6⟩
    · rintro ⟨a, b, c, d⟩ ⟨-, d1, -⟩
      have hd : a ≠ b := d1
      show b < a ↔ ¬ a < b
      omega
  have h2 : #(univ.filter (λ x : Fin n × Fin n × Fin n × Fin n =>
        ((g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2) ∧ distinct4 x) ∧
          x.1 < x.2.1)) =
      2 * #(univ.filter (λ x : Fin n × Fin n × Fin n × Fin n =>
        (((g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2) ∧ distinct4 x) ∧
          x.1 < x.2.1) ∧ x.2.2.1 < x.2.2.2)) := by
    refine card_filter_eq_two_mul (λ x => (x.1, x.2.1, x.2.2.2, x.2.2.1))
      (λ _ => rfl) ?_ ?_
    · rintro ⟨a, b, c, d⟩ ⟨⟨⟨h1, h2⟩, d1, d2, d3, d4, d5, d6⟩, hab⟩
      exact ⟨⟨⟨h1, h2.symm⟩, d1, d3, d2, d5, d4, d6.symm⟩, hab⟩
    · rintro ⟨a, b, c, d⟩ ⟨⟨-, -, -, -, -, -, d6⟩, -⟩
      have hd : c ≠ d := d6
      show d < c ↔ ¬ c < d
      omega
  have h3 : #(univ.filter (λ x : Fin n × Fin n × Fin n × Fin n =>
        (((g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2) ∧ distinct4 x) ∧
          x.1 < x.2.1) ∧ x.2.2.1 < x.2.2.2)) =
      2 * #(univ.filter (λ x : Fin n × Fin n × Fin n × Fin n =>
        ((((g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2) ∧ distinct4 x) ∧
          x.1 < x.2.1) ∧ x.2.2.1 < x.2.2.2) ∧ x.1 < x.2.2.1)) := by
    refine card_filter_eq_two_mul (λ x => (x.2.2.1, x.2.2.2, x.1, x.2.1))
      (λ _ => rfl) ?_ ?_
    · rintro ⟨a, b, c, d⟩ ⟨⟨⟨⟨h1, h2⟩, d1, d2, d3, d4, d5, d6⟩, hab⟩, hcd⟩
      exact ⟨⟨⟨⟨h2, h1⟩, d6, d2.symm, d4.symm, d3.symm, d5.symm, d1⟩, hcd⟩, hab⟩
    · rintro ⟨a, b, c, d⟩ ⟨⟨⟨-, -, d2, -⟩, -⟩, -⟩
      have hd : a ≠ c := d2
      show c < a ↔ ¬ a < c
      omega
  have h4 : univ.filter (λ x : Fin n × Fin n × Fin n × Fin n =>
        ((((g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2) ∧ distinct4 x) ∧
          x.1 < x.2.1) ∧ x.2.2.1 < x.2.2.2) ∧ x.1 < x.2.2.1) =
      univ.filter (λ x : Fin n × Fin n × Fin n × Fin n =>
        g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2 ∧
          x.1 < x.2.1 ∧ x.2.2.1 < x.2.2.2 ∧ x.1 < x.2.2.1 ∧
            x.2.1 ≠ x.2.2.1 ∧ x.2.1 ≠ x.2.2.2) := by
    refine Finset.filter_congr (λ x _ => ?_)
    obtain ⟨a, b, c, d⟩ := x
    constructor
    · rintro ⟨⟨⟨⟨⟨h1, h2⟩, d1, d2, d3, d4, d5, d6⟩, hab⟩, hcd⟩, hac⟩
      exact ⟨h1, h2, hab, hcd, hac, d4, d5⟩
    · rintro ⟨h1, h2, hab, hcd, hac, hbc, hbd⟩
      exact ⟨⟨⟨⟨⟨h1, h2⟩, hab.ne, hac.ne, (hac.trans hcd).ne, hbc, hbd, hcd.ne⟩,
        hab⟩, hcd⟩, hac⟩
  rw [h1, h2, h3, h4, ← Nat.mul_assoc, ← Nat.mul_assoc]
  rfl

/-! ### The expected-crossings identity -/

/-- **Expected crossings under random linearization** ([ferrer-i-cancho-2017],
    eq. 13): summed over all `n !` linearizations, three times the crossing
    count is `n !` times the number of disjoint link pairs. So a uniformly
    random ordering expects a third of a crossing per pair of links sharing no
    endpoint, whatever the sentence's own order was. -/
theorem Graph.three_mul_sum_crossings_relabel :
    3 * ∑ σ : Perm (Fin n), (g.relabel σ).crossings =
      n ! * g.disjointLinkPairs := by
  have key : 24 * ∑ σ : Perm (Fin n), g.crossingsUnder σ =
      n ! * (8 * g.disjointLinkPairs) := by
    rw [mul_sum_crossingsUnder, card_linked_distinct]
  have hsum : ∑ σ : Perm (Fin n), (g.relabel σ).crossings =
      ∑ σ : Perm (Fin n), g.crossingsUnder σ :=
    Finset.sum_congr rfl (λ σ _ => Graph.crossings_relabel σ)
  refine Nat.eq_of_mul_eq_mul_left (show 0 < 8 by omega) ?_
  calc 8 * (3 * ∑ σ : Perm (Fin n), (g.relabel σ).crossings)
      = 24 * ∑ σ : Perm (Fin n), g.crossingsUnder σ := by
        rw [hsum, ← Nat.mul_assoc]
    _ = n ! * (8 * g.disjointLinkPairs) := key
    _ = 8 * (n ! * g.disjointLinkPairs) := Nat.mul_left_comm _ _ _

end DependencyGrammar
