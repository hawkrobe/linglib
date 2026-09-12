/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.ContextFreeGrammar.Tree

/-!
# The pumping lemma for context-free languages

Every context-free language has the pumping property: beyond the pumping constant of a grammar,
every word splits as `u ++ v ++ x ++ y ++ z` with `v ++ x ++ y` short, `v ++ y` nonempty, and
every `u ++ vⁱ ++ x ++ yⁱ ++ z` in the language.

The proof is the textbook one through derivation trees. A word longer than
`maxBranch ^ (rules.card + 1)` has a valid tree of height above `rules.card`
(`RoseTree.ValidFor.length_yield_le`); a longest path in a tree of least size passes two nodes
with the same nonterminal (`RoseTree.ValidFor.exists_repeat`); replacing the lower by the upper
would shrink the tree unless it adds terminals, and grafting the lower into the upper repeatedly
pumps them (`RoseTree.ValidFor.replaceAt`, `RoseTree.ValidFor.derives`).

## Main definitions

* `HasCFLPumpingProperty`: the pumping property of a language.

## Main results

* `cfl_pumping_lemma`: every context-free language has the pumping property.
* `not_isContextFree_of_not_pumpable`: a language without it is not context-free.
-/

open RoseTree

/-- The pumping property of a language: beyond some length, every word splits as
`u ++ v ++ x ++ y ++ z` with `v ++ x ++ y` no longer than that length, `v ++ y` nonempty, and every
`u ++ vⁱ ++ x ++ yⁱ ++ z` in the language. -/
def HasCFLPumpingProperty {α : Type*} (L : Language α) : Prop :=
  ∃ p : ℕ, 0 < p ∧ ∀ w ∈ L, p ≤ w.length →
    ∃ u v x y z : List α, w = u ++ v ++ x ++ y ++ z ∧ (v ++ x ++ y).length ≤ p ∧
      1 ≤ v.length + y.length ∧
      ∀ i : ℕ, u ++ (List.replicate i v).flatten ++ x ++ (List.replicate i y).flatten ++ z ∈ L

namespace ContextFreeGrammar

variable {T : Type*} {g : ContextFreeGrammar T}

private theorem flatten_replicate_succ (l : List T) (n : ℕ) :
    (List.replicate (n + 1) l).flatten = (List.replicate n l).flatten ++ l := by
  rw [List.replicate_succ', List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil]

/-- A valid tree from the start symbol whose yield reaches the pumping constant pumps. -/
theorem pumping_from_tall_tree {t : RoseTree (Symbol T g.NT)} (ht : t.ValidFor g)
    (hroot : t.value = .nonterminal g.initial) (hlong : g.pumpingConstant ≤ t.yield.length) :
    ∃ u v x y z : List T, t.yield = u ++ v ++ x ++ y ++ z ∧
      (v ++ x ++ y).length ≤ g.pumpingConstant ∧ 1 ≤ v.length + y.length ∧
      ∀ i : ℕ, u ++ (List.replicate i v).flatten ++ x ++ (List.replicate i y).flatten ++ z ∈
        g.language := by
  classical
  have hb : 1 < g.maxBranch := g.two_le_maxBranch
  -- a valid tree of least size with the same yield and root
  obtain ⟨t₁, ht₁, hy₁, hr₁, hmin⟩ := ht.exists_min_numNodes
  -- it is taller than the number of rules
  have htall : g.rules.card < t₁.height := by
    by_contra hle
    have h1 := ht₁.length_yield_le
    have h2 : g.maxBranch ^ t₁.height ≤ g.maxBranch ^ g.rules.card :=
      Nat.pow_le_pow_right (by omega) (not_lt.mp hle)
    have h3 : g.maxBranch ^ g.rules.card < g.maxBranch ^ (g.rules.card + 1) :=
      Nat.pow_lt_pow_right hb (by omega)
    rw [hy₁] at h1
    unfold pumpingConstant at hlong
    omega
  -- a longest path, and the window of its last `g.rules.card + 1` nodes
  obtain ⟨p, hp, hpath⟩ := exists_subtreeAt_height_sub t₁ (t₁.height - 1) (by omega)
  set off := t₁.height - 1 - g.rules.card with hoff
  obtain ⟨t₀, ht₀, hh₀⟩ := hpath off (by omega)
  set q := p.drop off with hq
  have hql : q.length = g.rules.card := by simp [q, hp]; omega
  have hpq : p = p.take off ++ q := (List.take_append_drop off p).symm
  obtain ⟨e, he, heh⟩ := hpath p.length hp.le
  rw [List.take_length, hpq, subtreeAt_append, ht₀, Option.bind_some] at he
  obtain ⟨i, j, hij, hjK, A, csᵢ, csⱼ, hi, hj⟩ :=
    (ht₁.subtreeAt ht₀).exists_repeat he (by omega) hql.ge
  -- the outer and inner repeats, and their addresses
  set outer := node (Symbol.nonterminal A) csᵢ with houter
  set inner := node (Symbol.nonterminal A) csⱼ with hinner
  set po := p.take off ++ q.take i with hpo
  have hpo_sub : t₁.subtreeAt po = some outer := by
    rw [hpo, subtreeAt_append, ht₀, Option.bind_some, hi]
  set pr := (q.take j).drop i with hpr
  have hqj : q.take j = q.take i ++ pr := by
    conv_lhs => rw [← List.take_append_drop i (q.take j)]
    rw [List.take_take, min_eq_left hij.le]
  have hpr_sub : outer.subtreeAt pr = some inner := by
    rw [hqj, subtreeAt_append, hi, Option.bind_some] at hj; exact hj
  have hpr_ne : pr ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [pr, hql] at this
    omega
  have houter_h : outer.height ≤ g.rules.card + 1 := by
    obtain ⟨s, hs, hsh⟩ := hpath (off + i) (by omega)
    rw [List.take_add, ← hq, ← hpo, hpo_sub, Option.some.injEq] at hs
    rw [hs, hsh]; omega
  have houter_v : outer.ValidFor g := ht₁.subtreeAt hpo_sub
  have hinner_v : inner.ValidFor g := houter_v.subtreeAt hpr_sub
  -- yield decompositions
  obtain ⟨u, z, hyu, hyu'⟩ := yield_replaceAt hpo_sub
  obtain ⟨v, y, hyv, hyv'⟩ := yield_replaceAt hpr_sub
  refine ⟨u, v, inner.yield, y, z, ?_, ?_, ?_, fun k => ?_⟩
  · rw [← hy₁, hyu, hyv]; simp only [List.append_assoc]
  · rw [← hyv]
    exact houter_v.length_yield_le.trans (Nat.pow_le_pow_right (by omega) houter_h)
  · -- `v ++ y` is nonempty, by minimality
    by_contra hvy
    have hv : v = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy : y = [] := List.eq_nil_of_length_eq_zero (by omega)
    obtain ⟨i', rest, hpr'⟩ := List.exists_cons_of_ne_nil hpr_ne
    have hlt : (t₁.replaceAt po inner).numNodes < t₁.numNodes :=
      numNodes_replaceAt_lt hpo_sub (numNodes_lt_of_subtreeAt_cons (hpr' ▸ hpr_sub))
    have := hmin _ (ht₁.replaceAt hpo_sub hinner_v rfl)
      (by rw [hyu' inner, ← hy₁, hyu, hyv, hv, hy]; simp)
      (by rw [value_replaceAt (new := inner) hpo_sub rfl, hr₁])
    omega
  · -- pumping: graft the inner tree into the outer one `k` times, then into the tree
    let pump : ℕ → RoseTree (Symbol T g.NT) := fun n =>
      Nat.rec inner (fun _ prev => outer.replaceAt pr prev) n
    have hpump : ∀ n, (pump n).yield =
          (List.replicate n v).flatten ++ inner.yield ++ (List.replicate n y).flatten ∧
        (pump n).value = inner.value ∧ (pump n).ValidFor g := fun n => by
      induction n with
      | zero => exact ⟨by show inner.yield = _; simp, rfl, hinner_v⟩
      | succ n ih =>
        refine ⟨?_, ?_, houter_v.replaceAt hpr_sub ih.2.2 ih.2.1⟩
        · show (outer.replaceAt pr (pump n)).yield = _
          rw [hyv' (pump n), ih.1, List.replicate_succ, List.flatten_cons, flatten_replicate_succ]
          simp only [List.append_assoc]
        · exact (value_replaceAt hpr_sub ih.2.1).trans rfl
    have hfinal := ht₁.replaceAt hpo_sub (hpump k).2.2 (hpump k).2.1
    rw [mem_language_iff, ← hroot, ← hr₁, ← value_replaceAt hpo_sub (hpump k).2.1,
      show u ++ (List.replicate k v).flatten ++ inner.yield ++ (List.replicate k y).flatten ++ z =
        (t₁.replaceAt po (pump k)).yield by rw [hyu' (pump k), (hpump k).1]; simp]
    exact hfinal.derives

end ContextFreeGrammar

/-- **The pumping lemma for context-free languages.** -/
theorem cfl_pumping_lemma {T : Type*} (L : Language T) (hcf : L.IsContextFree) :
    HasCFLPumpingProperty L := by
  obtain ⟨g, rfl⟩ := hcf
  refine ⟨g.pumpingConstant, g.pumpingConstant_pos, fun w hw hlen => ?_⟩
  obtain ⟨t, hvalid, hyield, hroot⟩ := g.exists_valid_tree hw
  obtain ⟨u, v, x, y, z, hdecomp, hvxy, hvy, hpump⟩ :=
    ContextFreeGrammar.pumping_from_tall_tree hvalid hroot (hyield ▸ hlen)
  exact ⟨u, v, x, y, z, hyield ▸ hdecomp, hvxy, hvy, hpump⟩

/-- A language without the pumping property is not context-free. -/
theorem not_isContextFree_of_not_pumpable {T : Type*} (L : Language T)
    (h : ¬ HasCFLPumpingProperty L) : ¬ L.IsContextFree :=
  fun hcf => h (cfl_pumping_lemma L hcf)
