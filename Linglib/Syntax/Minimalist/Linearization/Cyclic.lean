/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Relation.ReflTransGen
import Linglib.Core.Data.List.Sublist
import Mathlib.Logic.Relation

/-!
# Cyclic linearization of syntactic structure

[fox-pesetsky-2005]'s theory of the syntax–phonology interface: linearization
applies at the end of each phase (Spell-out domain), the ordering statements it
establishes are never deleted (Order Preservation, their (52)), and a derivation
converges only if the accumulated statements cohere.

The account is one mathematical object: a derivation exposes a word of phase
snapshots, each snapshot carries its pair-sublist relation (`[a, b] <+ p` — the
paper's ordering statements, their (10)), and `spelloutOrder` is the transitive
closure of their union. Grammaticality (`Consistent`) is the statement that this
candidate is a genuine strict order (`consistent_iff_isStrictOrder`); transitivity
is free, so the entire crash condition is irreflexivity. Order Preservation is
monotonicity (`spelloutOrder_mono`), not an axiom, and the order is blind to the
sequencing of Spell-outs (`spelloutOrder_perm`) — the account reads only the *set*
of snapshots.

The paper's worked examples (Scenarios (13)/(14), successive-cyclic movement
(3)–(8), Holmberg's Generalization §3) live in `Studies/FoxPesetsky2005.lean`;
Malayic and Guébie applications in `Studies/ErlewineSommerlot2025.lean` and
`Studies/SandeClemDabkowski2026.lean`.

## Main declarations

* `Minimalist.Linearization.spelloutOrder`: the induced candidate order.
* `Minimalist.Linearization.Consistent`: the derivation linearizes — decidable on
  concrete phase data.

## Main results

* `Minimalist.Linearization.consistent_iff_isStrictOrder`: the crash condition is
  exactly "spell-out induces a strict order".
* `Minimalist.Linearization.spelloutOrder_mono`, `spelloutOrder_perm`: Order
  Preservation and snapshot-set blindness.
* `Minimalist.Linearization.consistent_singleton`: a single Spell-out of distinct
  terminals always linearizes.
-/

namespace Minimalist.Linearization

open List

variable {α : Type*}

/-- The spell-out order induced by a derivation's phase snapshots: the transitive
    closure of "`a` precedes `b` at some Spell-out", per-phase precedence being the
    pair-sublist relation ([fox-pesetsky-2005] (10), (52)). -/
def spelloutOrder (phases : List (List α)) : α → α → Prop :=
  Relation.TransGen fun a b => ∃ p ∈ phases, [a, b] <+ p

/-- The derivation linearizes: spell-out induces a genuine strict order
    ([fox-pesetsky-2005]'s convergence condition). Transitivity is free, so the
    content is irreflexivity — no ordering cycle of any length. -/
def Consistent (phases : List (List α)) : Prop :=
  ∀ a, ¬ spelloutOrder phases a a

variable {phases ps qs : List (List α)} {a b : α}

/-- The crash condition, in order-theoretic vocabulary. -/
theorem consistent_iff_isStrictOrder :
    Consistent phases ↔ IsStrictOrder α (spelloutOrder phases) :=
  ⟨fun h => { irrefl := h, trans := fun _ _ _ => Relation.TransGen.trans },
   fun h => h.toIrrefl.irrefl⟩

/-- Order Preservation ([fox-pesetsky-2005] (52)): ordering statements are never
    deleted — a larger derivation induces a larger order. -/
theorem spelloutOrder_mono (h : ∀ p ∈ ps, p ∈ qs) (hab : spelloutOrder ps a b) :
    spelloutOrder qs a b :=
  Relation.TransGen.mono (fun _ _ ⟨p, hp, hs⟩ => ⟨p, h p hp, hs⟩) hab

/-- The induced order is blind to the sequencing of Spell-outs: it reads only the
    set of phase snapshots. -/
theorem spelloutOrder_perm (h : ps.Perm qs) : spelloutOrder ps = spelloutOrder qs := by
  funext a b
  exact propext ⟨spelloutOrder_mono fun p hp => h.mem_iff.mp hp,
    spelloutOrder_mono fun p hp => h.mem_iff.mpr hp⟩

variable [DecidableEq α]

/-- On a single duplicate-free snapshot, the induced order is index order. -/
theorem spelloutOrder_singleton_idxOf {p : List α} (hnd : p.Nodup)
    (h : spelloutOrder [p] a b) : p.idxOf a < p.idxOf b := by
  induction h with
  | single h =>
    obtain ⟨q, hq, hs⟩ := h
    rw [List.mem_singleton] at hq
    exact hq ▸ List.idxOf_lt_of_pair_sublist (hq ▸ hnd) hs
  | tail _ h ih =>
    obtain ⟨q, hq, hs⟩ := h
    rw [List.mem_singleton] at hq
    exact ih.trans (hq ▸ List.idxOf_lt_of_pair_sublist (hq ▸ hnd) hs)

/-- A single Spell-out of distinct terminals always linearizes. -/
theorem consistent_singleton {p : List α} (hnd : p.Nodup) : Consistent [p] :=
  fun _ h => Nat.lt_irrefl _ (spelloutOrder_singleton_idxOf hnd h)

/-! ### Decidability

`Consistent` decides on concrete phase data: the candidate order's generator only
relates terminals mentioned at some Spell-out, so irreflexivity reduces to a finite
check over the support, with reachability decided by
`Relation.ReflTransGen.decidable_of_finite`. -/

section Decidability

variable (phases : List (List α))

/-- Every terminal mentioned at any Spell-out. -/
def support : List α := phases.flatten.dedup

private theorem gen_src_mem {a b : α} (h : ∃ p ∈ phases, [a, b] <+ p) :
    a ∈ support phases := by
  obtain ⟨p, hp, hs⟩ := h
  exact List.mem_dedup.mpr (List.mem_flatten.mpr ⟨p, hp, hs.subset (by simp)⟩)

private theorem gen_dst_mem {a b : α} (h : ∃ p ∈ phases, [a, b] <+ p) :
    b ∈ support phases := by
  obtain ⟨p, hp, hs⟩ := h
  exact List.mem_dedup.mpr (List.mem_flatten.mpr ⟨p, hp, hs.subset (by simp)⟩)

instance instDecidableReflTransGen (a b : α) :
    Decidable (Relation.ReflTransGen (fun a b => ∃ p ∈ phases, [a, b] <+ p) a b) :=
  Relation.ReflTransGen.decidable_of_finite (support phases)
    (fun _ _ h => gen_dst_mem phases h) a b

instance instDecidableSpelloutOrder (a b : α) : Decidable (spelloutOrder phases a b) :=
  decidable_of_iff (∃ c ∈ support phases, (∃ p ∈ phases, [a, c] <+ p) ∧
      Relation.ReflTransGen (fun a b => ∃ p ∈ phases, [a, b] <+ p) c b) <| by
    rw [spelloutOrder, Relation.TransGen.head'_iff]
    exact ⟨fun ⟨c, _, h, h'⟩ => ⟨c, h, h'⟩, fun ⟨c, h, h'⟩ => ⟨c, gen_dst_mem phases h, h, h'⟩⟩

instance instDecidableConsistent : Decidable (Consistent phases) :=
  decidable_of_iff (∀ a ∈ support phases, ¬ spelloutOrder phases a a) <| by
    refine ⟨fun h a ha => ?_, fun h a _ => h a⟩
    rcases (Relation.TransGen.head'_iff.mp ha) with ⟨c, hac, _⟩
    exact h a (gen_src_mem phases hac) ha

end Decidability

end Minimalist.Linearization
