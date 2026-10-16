/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.DependencyGrammar.Projectivity
public import Linglib.Syntax.DependencyGrammar.Length
public import Linglib.Core.Combinatorics.Enumerative.PermutationPattern
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fin.VecNotation

/-!
# Crossings under random linearization

This file proves that if a sentence's word order were lost and replaced by
a uniformly random one, the expected number of crossings would depend only
on the arc structure: two links cross in a third of the linearizations
when they share no endpoint, and in none otherwise. No tree hypothesis is
needed; the identity holds for any link structure.

## Main definitions

* `Graph.disjointLinkPairs` is the number of unordered pairs of links
  sharing no endpoint, the pairs that can cross at all.

## Main statements

* `Graph.three_mul_sum_crossings_map`: the expected-crossings identity
  `3 * ∑ σ, (g.map σ).crossings = n ! * g.disjointLinkPairs`.

## Implementation notes

Crossings are counted as ordered quadruples. Four distinct linked positions
alternate in one of their `4 !` equally likely relative orders
(`Equiv.Perm.factorial_mul_card_monotone_comp`), and each unordered pair of
disjoint links has eight ordered witnesses.

## References

[ferrer-i-cancho-2017] — Random crossings in dependency trees, source of
the expected-crossings identity (eq. 13)
[ferrer-i-cancho-2013] — Hubiness, length, crossings and their
relationships in dependency trees, expresses the disjoint-pair count of a
tree through its length and degree second moment
-/

@[expose] public section

namespace DependencyGrammar

open Finset Equiv Nat

variable {n : ℕ} (g : Graph n)

/-- The unordered pairs of links sharing no endpoint — the pairs that can
cross at all, [ferrer-i-cancho-2017]'s potential crossings. Each pair is
counted once, by the representative with both links least-endpoint-first
and the earlier-starting link first. -/
def Graph.disjointLinkPairs : ℕ :=
  #{x : Fin n × Fin n × Fin n × Fin n | g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2 ∧
    x.1 < x.2.1 ∧ x.2.2.1 < x.2.2.2 ∧ x.1 < x.2.2.1 ∧ x.2.1 ≠ x.2.2.1 ∧ x.2.1 ≠ x.2.2.2}

variable {g}

/-! ### Crossings under a relabelling -/

/-- Relabelling scores the crossing quadruples in the positions the
permutation assigns rather than in `g`'s own. -/
theorem Graph.crossings_map (σ : Perm (Fin n)) :
    (g.map σ).crossings = #{x : Fin n × Fin n × Fin n × Fin n |
      g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2 ∧
        Alternate (σ x.1) (σ x.2.1) (σ x.2.2.1) (σ x.2.2.2)} := by
  refine Finset.card_equiv
    (σ.symm.prodCongr (σ.symm.prodCongr (σ.symm.prodCongr σ.symm))) ?_
  rintro ⟨a, b, c, d⟩
  simp [Graph.Linked, Alternate]

/-! ### One linearization in twenty-four alternates a distinct quadruple -/

/-- Alternation is monotonicity of the permutation along the reordered
quadruple. -/
private theorem alternate_comp_iff {a b c d : Fin n} (σ : Perm (Fin n))
    (hq : Function.Injective ![a, c, b, d]) :
    Alternate (σ a) (σ b) (σ c) (σ d) ↔ Monotone (σ ∘ ![a, c, b, d]) :=
  .trans (by simp [Fin.strictMono_iff_lt_succ, Fin.forall_fin_succ])
    ⟨StrictMono.monotone, (·.strictMono_of_injective (σ.injective.comp hq))⟩

/-- One linearization in `24` puts four fixed distinct positions into the
alternating pattern. -/
private theorem card_alternate {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    24 * #{σ : Perm (Fin n) | Alternate (σ a) (σ b) (σ c) (σ d)} = n ! := by
  have hq : Function.Injective ![a, c, b, d] := List.nodup_ofFn.mp (by simp [*, hbc.symm])
  simpa only [Fintype.card_fin, Function.Embedding.coeFn_mk, ← alternate_comp_iff _ hq,
    show (4 : ℕ)! = 24 from rfl] using
    Perm.factorial_mul_card_monotone_comp (⟨_, hq⟩ : Fin 4 ↪ Fin n)

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
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The crossings of all linearizations, regrouped by the quadruple that
crosses. -/
private theorem sum_crossings_map :
    ∑ σ : Perm (Fin n), (g.map σ).crossings =
      ∑ x ∈ univ.filter (fun x : Fin n × Fin n × Fin n × Fin n ↦
          g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2),
        #{σ : Perm (Fin n) | Alternate (σ x.1) (σ x.2.1) (σ x.2.2.1) (σ x.2.2.2)} := by
  simp only [Graph.crossings_map, Finset.card_filter]
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun x _ ↦ ?_)
  by_cases h1 : g.Linked x.1 x.2.1 <;> by_cases h2 : g.Linked x.2.2.1 x.2.2.2 <;>
    simp [h1, h2]

/-- Each linked quadruple of distinct positions contributes `n !` to
twenty-four times the crossings of all linearizations; degenerate
quadruples contribute nothing. -/
private theorem mul_sum_crossings_map :
    24 * ∑ σ : Perm (Fin n), (g.map σ).crossings =
      n ! * #(univ.filter (fun x : Fin n × Fin n × Fin n × Fin n ↦
        (g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2) ∧ distinct4 x)) := by
  rw [sum_crossings_map, Finset.mul_sum]
  have hcongr : ∀ x ∈ univ.filter (fun x : Fin n × Fin n × Fin n × Fin n ↦
      g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2),
      24 * #{σ : Perm (Fin n) |
        Alternate (σ x.1) (σ x.2.1) (σ x.2.2.1) (σ x.2.2.2)} =
        if distinct4 x then n ! else 0 := by
    intro x _
    by_cases hd : distinct4 x
    · rw [ite_eq_left hd]
      obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd
      exact card_alternate d1 d2 d3 d4 d5 d6
    · rw [ite_eq_right hd, card_alternate_eq_zero hd, Nat.mul_zero]
  rw [Finset.sum_congr rfl hcongr, ← Finset.sum_filter, Finset.filter_filter,
    Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-! ### Eight ordered witnesses per unordered disjoint pair -/

/-- An involution preserving `P` and toggling `C` halves the count: there
are as many `P`-elements with `C` as without. -/
private theorem card_filter_eq_two_mul {α : Type*} [Fintype α] [DecidableEq α]
    {P C : α → Prop} [DecidablePred P] [DecidablePred C] (e : α → α)
    (he : Function.Involutive e) (hP : ∀ x, P x → P (e x))
    (hC : ∀ x, P x → (C (e x) ↔ ¬ C x)) :
    #(univ.filter P) = 2 * #(univ.filter (fun x ↦ P x ∧ C x)) := by
  rw [← Finset.filter_filter,
    ← Finset.card_filter_add_card_filter_not (s := univ.filter P) C, two_mul]
  congr 1
  refine Finset.card_equiv (he.toPerm e) (fun x ↦ ?_)
  simp only [mem_filter, mem_univ, true_and, Function.Involutive.coe_toPerm]
  grind [Function.Involutive]

/-- Ordered linked quadruples of distinct positions come in eights: an
orientation for each link and the order of the two links. -/
private theorem card_linked_distinct :
    #(univ.filter (fun x : Fin n × Fin n × Fin n × Fin n ↦
        (g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2) ∧ distinct4 x)) =
      8 * g.disjointLinkPairs := by
  rw [card_filter_eq_two_mul (C := fun x ↦ x.1 < x.2.1) (fun x ↦ (x.2.1, x.1, x.2.2))
      (fun _ ↦ rfl) ?_ ?_,
    card_filter_eq_two_mul (C := fun x ↦ x.2.2.1 < x.2.2.2)
      (fun x ↦ (x.1, x.2.1, x.2.2.2, x.2.2.1)) (fun _ ↦ rfl) ?_ ?_,
    card_filter_eq_two_mul (C := fun x ↦ x.1 < x.2.2.1)
      (fun x ↦ (x.2.2.1, x.2.2.2, x.1, x.2.1)) (fun _ ↦ rfl) ?_ ?_,
    ← Nat.mul_assoc, ← Nat.mul_assoc, Graph.disjointLinkPairs]
  · congr 2
    refine filter_congr fun x _ ↦ ?_
    simp only [distinct4]
    grind
  all_goals rintro ⟨a, b, c, d⟩; simp only [distinct4, Graph.Linked]; grind

/-! ### The expected-crossings identity -/

/-- **Expected crossings under random linearization** ([ferrer-i-cancho-2017],
eq. 13): summed over all `n !` linearizations, three times the crossing
count is `n !` times the number of disjoint link pairs. So a uniformly
random ordering expects a third of a crossing per pair of links sharing no
endpoint, whatever the sentence's own order was. -/
theorem Graph.three_mul_sum_crossings_map :
    3 * ∑ σ : Perm (Fin n), (g.map σ).crossings = n ! * g.disjointLinkPairs := by
  have key := mul_sum_crossings_map (g := g)
  rw [card_linked_distinct, Nat.mul_left_comm] at key
  omega

end DependencyGrammar
