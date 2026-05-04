import Mathlib.Logic.Relation
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Perm.Subperm

/-!
# Decidability of `Relation.ReflTransGen` on a finite carrier

Generic substrate: given a relation `r : α → α → Prop` whose successors lie
in some finite list `s : List α`, derive `Decidable (Relation.ReflTransGen r a b)`
via path compression.

## Construction

A `Path r a chain b` is a list of intermediates `[c₁, …, cₖ]` with
`r a c₁ ∧ r c₁ c₂ ∧ … ∧ r cₖ b`. The empty chain `[]` witnesses a direct
edge `r a b`. Then:

1. `ReflTransGen r a b` is equivalent to `a = b` or the existence of some
   `Path r a chain b` (`ReflTransGen.eq_or_path`).
2. Any `Path` reduces to one whose intermediates are pairwise distinct and
   contain neither `a` nor `b` (`Path.compress`).
3. A compressed `Path` has length `< s.length` by `List.Subperm`.
4. Hence reachability is decidable via bounded BFS at fuel `s.length`.

## Naming

`Path` is named to match `Quiver.Path` / `SimpleGraph.Walk`-style naming.
It is **distinct** from `List.Chain'` (which is a relation between
consecutive list elements without fixed endpoints).

## Provenance

Lifted from `Core/Inheritance/Basic.lean` where it was first proved for
Hudson's Word Grammar `IsA` relation. Generalised to be reusable across
`Network.IsA`, `CausalGraph.IsAncestor`, `SemClass.IsA`, and
`SDRT.availableViaChain`.
-/

set_option autoImplicit false

universe u

namespace Relation.ReflTransGen

variable {α : Type u}

-- ----------------------------------------------------------------------------
-- Path: chain of intermediates witnessing ReflTransGen
-- ----------------------------------------------------------------------------

/-- A chain of intermediate nodes `[c₁, c₂, …, cₖ]` witnesses
`a → c₁ → c₂ → … → cₖ → b` via `r`-steps. The empty chain `[]` witnesses
a direct edge `r a b`.

Distinct from `List.Chain'`: `Path r a chain b` pins the source `a` and
target `b`; `List.Chain' r l` does not. -/
def Path (r : α → α → Prop) (a : α) : List α → α → Prop
  | [], b => r a b
  | x :: xs, b => r a x ∧ Path r x xs b

@[simp] theorem Path.cons_iff {r : α → α → Prop} (a x b : α) (xs : List α) :
    Path r a (x :: xs) b ↔ r a x ∧ Path r x xs b := Iff.rfl

@[simp] theorem Path.nil_iff {r : α → α → Prop} (a b : α) :
    Path r a [] b ↔ r a b := Iff.rfl

/-- A path realises `ReflTransGen`. -/
theorem Path.toReflTransGen {r : α → α → Prop} {a b : α} :
    ∀ {chain : List α}, Path r a chain b → Relation.ReflTransGen r a b
  | [], h => Relation.ReflTransGen.single h
  | _ :: _, ⟨hax, hr⟩ => Relation.ReflTransGen.head hax (Path.toReflTransGen hr)

/-- Extend a path by one edge at the END. -/
theorem Path.snoc {r : α → α → Prop} {a b c : α} :
    ∀ {chain : List α}, Path r a chain b → r b c → Path r a (chain ++ [b]) c
  | [], h, hbc => ⟨h, hbc⟩
  | _ :: _, ⟨hax, hr⟩, hbc => ⟨hax, Path.snoc hr hbc⟩

/-- `ReflTransGen r a b` decomposes either as `a = b` or as a `Path`. -/
theorem _root_.Relation.ReflTransGen.eq_or_path {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) : a = b ∨ ∃ chain : List α, Path r a chain b := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail b' c _ hbc ih =>
    rcases ih with rfl | ⟨chain, hc⟩
    · exact Or.inr ⟨[], hbc⟩
    · exact Or.inr ⟨chain ++ [b'], hc.snoc hbc⟩

-- ----------------------------------------------------------------------------
-- Path compression
-- ----------------------------------------------------------------------------

/-- **Compression** (right-truncation): if `b` appears in the chain, take
the prefix ending at its first occurrence. -/
theorem Path.truncate_at_target {r : α → α → Prop} {a b : α} :
    ∀ {chain : List α}, Path r a chain b → b ∈ chain →
        ∃ chain' : List α, chain'.length < chain.length ∧ Path r a chain' b
  | [], _, hb_in => by simp at hb_in
  | x :: xs, ⟨hax, hr⟩, hb_in => by
    rcases List.mem_cons.mp hb_in with rfl | hb_in_xs
    · exact ⟨[], List.length_nil ▸ Nat.zero_lt_succ _, hax⟩
    · obtain ⟨chain', hlen, hc'⟩ := Path.truncate_at_target hr hb_in_xs
      refine ⟨x :: chain', ?_, hax, hc'⟩
      simp only [List.length_cons]; omega

/-- Helper: if a chain `Path r x chain b` contains `y`, the suffix from
`y`'s first occurrence is itself a chain `Path r y _ b`. -/
theorem Path.suffix_from {r : α → α → Prop} {x b : α} (y : α) :
    ∀ {chain : List α}, Path r x chain b → y ∈ chain →
        ∃ tail : List α, tail.length < chain.length ∧ Path r y tail b
  | [], _, h_in => by simp at h_in
  | z :: zs, ⟨_, hr⟩, h_in => by
    rcases List.mem_cons.mp h_in with rfl | h_in_zs
    · exact ⟨zs, by simp only [List.length_cons]; omega, hr⟩
    · obtain ⟨tail, hlen, htail⟩ := Path.suffix_from y hr h_in_zs
      exact ⟨tail, by simp only [List.length_cons]; omega, htail⟩

/-- **Compression** (skip-to-self): if `a` appears in the chain, take the
suffix from its reappearance. -/
theorem Path.skip_to_self {r : α → α → Prop} {a b : α} {chain : List α}
    (h : Path r a chain b) (ha_in : a ∈ chain) :
    ∃ chain' : List α, chain'.length < chain.length ∧ Path r a chain' b := by
  match chain, h with
  | x :: xs, ⟨_, hr⟩ =>
    rcases List.mem_cons.mp ha_in with rfl | ha_in_xs
    · exact ⟨xs, by simp only [List.length_cons]; omega, hr⟩
    · obtain ⟨tail, hlen, htail⟩ := Path.suffix_from a hr ha_in_xs
      exact ⟨tail, by simp only [List.length_cons]; omega, htail⟩

/-- **Compression** (interior duplication): if some node appears twice in
the chain, splice out the cycle. -/
theorem Path.dedup_interior {r : α → α → Prop} {a b : α} :
    ∀ {chain : List α}, Path r a chain b → ¬ chain.Nodup →
        ∃ chain' : List α, chain'.length < chain.length ∧ Path r a chain' b
  | [], _, hnd => absurd List.nodup_nil hnd
  | x :: xs, ⟨hax, hr⟩, hnd => by
    rw [List.nodup_cons, not_and_or] at hnd
    rcases hnd with hx_in_xs | hxs_not_nodup
    · simp only [not_not] at hx_in_xs
      obtain ⟨tail, hlen, htail⟩ := Path.suffix_from x hr hx_in_xs
      exact ⟨x :: tail, by simp only [List.length_cons]; omega, hax, htail⟩
    · obtain ⟨xs', hlen, hxs'⟩ := Path.dedup_interior hr hxs_not_nodup
      exact ⟨x :: xs', by simp only [List.length_cons]; omega, hax, hxs'⟩

private theorem Path.compress_aux [DecidableEq α] {r : α → α → Prop} {a b : α} :
    ∀ (n : Nat) (chain : List α), chain.length = n → Path r a chain b →
        ∃ chain' : List α, Path r a chain' b ∧ chain'.Nodup ∧
            a ∉ chain' ∧ b ∉ chain' := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro chain hlen h
    by_cases hb_in : b ∈ chain
    · obtain ⟨chain', hlen', hc'⟩ := h.truncate_at_target hb_in
      exact ih chain'.length (hlen ▸ hlen') chain' rfl hc'
    by_cases ha_in : a ∈ chain
    · obtain ⟨chain', hlen', hc'⟩ := h.skip_to_self ha_in
      exact ih chain'.length (hlen ▸ hlen') chain' rfl hc'
    by_cases hnd : chain.Nodup
    · exact ⟨chain, h, hnd, ha_in, hb_in⟩
    · obtain ⟨chain', hlen', hc'⟩ := h.dedup_interior hnd
      exact ih chain'.length (hlen ▸ hlen') chain' rfl hc'

/-- **Chain compression**: any path reduces to one with no repeats whose
intermediates are disjoint from `{a, b}`. -/
theorem Path.compress [DecidableEq α] {r : α → α → Prop} {a b : α} {chain : List α}
    (h : Path r a chain b) :
    ∃ chain' : List α, Path r a chain' b ∧ chain'.Nodup ∧
        a ∉ chain' ∧ b ∉ chain' :=
  Path.compress_aux chain.length chain rfl h

-- ----------------------------------------------------------------------------
-- Subset bound: path intermediates contained in any successor-closed list
-- ----------------------------------------------------------------------------

/-- All intermediates of a path are contained in any list that contains
`r`-successors. -/
theorem Path.intermediates_subset {r : α → α → Prop} {a b : α} {s : List α}
    (succ_in_s : ∀ x y, r x y → y ∈ s) :
    ∀ {chain : List α}, Path r a chain b → ∀ y ∈ chain, y ∈ s
  | [], _, _, hy => by simp at hy
  | _ :: xs, ⟨hax, hr⟩, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hy_tail
    · exact succ_in_s _ _ hax
    · exact Path.intermediates_subset succ_in_s hr y hy_tail

/-- The endpoint of a path is contained in any list that contains
`r`-successors. -/
theorem Path.endpoint_mem {r : α → α → Prop} {a b : α} {s : List α}
    (succ_in_s : ∀ x y, r x y → y ∈ s) :
    ∀ {chain : List α}, Path r a chain b → b ∈ s
  | [], h => succ_in_s _ _ h
  | _ :: _, ⟨_, hr⟩ => Path.endpoint_mem succ_in_s hr

/-- Length bound: a `Nodup` path with `b` not in the chain is bounded by the
size of any successor-closed list. -/
theorem Path.length_lt_of_nodup [DecidableEq α] {r : α → α → Prop} {a b : α} {s : List α}
    (succ_in_s : ∀ x y, r x y → y ∈ s)
    {chain : List α} (h : Path r a chain b)
    (hnodup : chain.Nodup) (hb_notin : b ∉ chain) :
    chain.length < s.length := by
  have h_subset : chain ⊆ s :=
    fun x hx => h.intermediates_subset succ_in_s x hx
  have hb_in_s : b ∈ s := h.endpoint_mem succ_in_s
  have hbchain_nodup : (b :: chain).Nodup := List.nodup_cons.mpr ⟨hb_notin, hnodup⟩
  have hbchain_subset : (b :: chain) ⊆ s := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx_tail
    · exact hb_in_s
    · exact h_subset hx_tail
  have hsub : List.Subperm (b :: chain) s :=
    hbchain_nodup.subperm hbchain_subset
  have hle : (b :: chain).length ≤ s.length := hsub.length_le
  simpa using hle

-- ----------------------------------------------------------------------------
-- Bounded BFS over a step function
-- ----------------------------------------------------------------------------

/-- Bounded BFS over a step function. `stepBFS step a n` collects all nodes
reachable from `a` via at most `n` step-applications. -/
def stepBFS (step : α → List α) (a : α) : Nat → List α
  | 0 => []
  | n + 1 =>
    let ps := step a
    ps ++ ps.flatMap (fun p => stepBFS step p n)

theorem mem_stepBFS_succ_iff (step : α → List α) (a x : α) (n : Nat) :
    x ∈ stepBFS step a (n + 1) ↔
      x ∈ step a ∨ ∃ p ∈ step a, x ∈ stepBFS step p n := by
  simp only [stepBFS, List.mem_append, List.mem_flatMap]

/-- BFS membership corresponds to existence of a `Path` of bounded length,
where the relation is `fun a b => b ∈ step a`. -/
theorem mem_stepBFS_iff_path (step : α → List α) (a b : α) :
    ∀ n, b ∈ stepBFS step a n ↔
        ∃ chain : List α, chain.length < n ∧ Path (fun a b => b ∈ step a) a chain b
  | 0 => by
    simp only [stepBFS, List.not_mem_nil, false_iff, not_exists]
    intro chain ⟨h, _⟩
    exact Nat.not_lt_zero _ h
  | n + 1 => by
    rw [mem_stepBFS_succ_iff]
    constructor
    · rintro (hpar | ⟨p, hp_par, hp_anc⟩)
      · exact ⟨[], Nat.zero_lt_succ _, hpar⟩
      · obtain ⟨chain, hlen, hc⟩ := (mem_stepBFS_iff_path step p b n).mp hp_anc
        refine ⟨p :: chain, ?_, hp_par, hc⟩
        simpa using Nat.succ_lt_succ hlen
    · rintro ⟨chain, hlen, hc⟩
      match chain, hc with
      | [], h => exact Or.inl h
      | x :: xs, ⟨hax, hr⟩ =>
        right
        refine ⟨x, hax, ?_⟩
        have hxs_lt : xs.length < n := by
          simpa using Nat.lt_of_succ_lt_succ hlen
        exact (mem_stepBFS_iff_path step x b n).mpr ⟨xs, hxs_lt, hr⟩

-- ----------------------------------------------------------------------------
-- Headline: decidability
-- ----------------------------------------------------------------------------

/-- **Decidability of `Relation.ReflTransGen` on a finite carrier**, given an
explicit step function and a successor-bound list `s`. -/
def decidable_of_finite_step [DecidableEq α] {r : α → α → Prop}
    (step : α → List α) (s : List α)
    (step_eq : ∀ a b, r a b ↔ b ∈ step a)
    (step_in_s : ∀ a b, b ∈ step a → b ∈ s)
    (a b : α) : Decidable (Relation.ReflTransGen r a b) := by
  have key : Relation.ReflTransGen r a b ↔
      a = b ∨ b ∈ stepBFS step a s.length := by
    have hr_eq : r = fun x y => y ∈ step x := by
      ext x y; exact step_eq x y
    constructor
    · intro h
      rcases h.eq_or_path with rfl | ⟨chain, hc⟩
      · exact Or.inl rfl
      · have hc' : Path (fun x y => y ∈ step x) a chain b := hr_eq ▸ hc
        obtain ⟨chain', hc'', hnodup, _, hb_notin⟩ := hc'.compress
        have succ_in_s : ∀ x y, (fun x y => y ∈ step x) x y → y ∈ s :=
          step_in_s
        have hlen : chain'.length < s.length :=
          hc''.length_lt_of_nodup succ_in_s hnodup hb_notin
        exact Or.inr ((mem_stepBFS_iff_path step a b s.length).mpr
          ⟨chain', hlen, hc''⟩)
    · rintro (rfl | hmem)
      · exact Relation.ReflTransGen.refl
      · obtain ⟨chain, _, hc⟩ := (mem_stepBFS_iff_path step a b s.length).mp hmem
        have hc' : Path r a chain b := by
          have hr_eq' : (fun x y => y ∈ step x) = r := hr_eq.symm
          exact hr_eq' ▸ hc
        exact hc'.toReflTransGen
  exact decidable_of_iff _ key.symm

/-- **Decidability of `Relation.ReflTransGen` on a finite carrier**, derived
from a `[DecidableRel r]` instance and a successor-bound list. A convenience
wrapper around `decidable_of_finite_step` for callers that have `r` decidable
but no natural step function. -/
def decidable_of_finite [DecidableEq α] {r : α → α → Prop} [DecidableRel r]
    (s : List α)
    (succ_in_s : ∀ a b, r a b → b ∈ s)
    (a b : α) : Decidable (Relation.ReflTransGen r a b) :=
  decidable_of_finite_step
    (fun a => s.filter (fun b => decide (r a b)))
    s
    (fun a b => by
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨fun h => ⟨succ_in_s a b h, h⟩, fun h => h.2⟩)
    (fun _ _ h => (List.mem_filter.mp h).1)
    a b

end Relation.ReflTransGen
