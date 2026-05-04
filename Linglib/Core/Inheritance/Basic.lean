import Mathlib.Logic.Relation
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Perm.Subperm

/-!
# Inheritance Networks — Basic Types and Taxonomy

@cite{hudson-2010}

Hudson's Word Grammar organizes all linguistic knowledge as networks of nodes
connected by labeled directed links. Properties are not key-value pairs attached
to nodes — they ARE links between nodes. "Bird has wing" is a link labeled
`front-limb` from `bird` to `wing`. IsA links form a taxonomy; properties flow
down the taxonomy by default inheritance.

## Hudson's six primitive relations (Ch 3 summary box, p. 68)

`isA`, `argument`, `value`, `or` (choice), `quantity`, `identity` —
listed verbatim in @cite{hudson-2010}'s Ch 3 summary box on p. 68 under
"Links between concepts are therefore of two types: primitive relations /
conceptual relations".

This module distinguishes three link kinds at the type level:

- **isA** — taxonomic classification (`bird isA animal`)
- **or** — mutual exclusivity / choice sets (`male or female`)
- **prop** — named property/relation links (`bird --front-limb--> wing`),
  covering `argument`, `value`, `identity`, `quantity` via the relation label

## Key definitions

- `LinkKind`, `Link`, `Network`
- `Network.nodeUniverse` — finite carrier derived from the link list
- `parents`, `ancestorsBound`, `ancestors` — computational taxonomy traversal
- `IsA` — the canonical reflexive-transitive `isA`, defined as
  `Relation.ReflTransGen` of the parent edge

`IsA` is the API; `parents`/`ancestors` are computational evidence producers
(`b ∈ ancestors net a → IsA net a b` via `IsA.of_mem_ancestors`). Termination
of `ancestors` is bounded by `nodeUniverse.length`, not a magic constant.
-/

set_option autoImplicit false

namespace Core.Inheritance

-- ============================================================================
-- Links
-- ============================================================================

/-- Distinguished link types in a WG network @cite{hudson-2010} §3.2.
`isA` and `or` are separated from general property links because the
inheritance algorithm must traverse `isA` links and choice-set resolution
uses `or` links. -/
inductive LinkKind where
  | isA   -- taxonomic inheritance
  | or    -- mutual exclusivity (choice set)
  | prop  -- named property / relation
  deriving Repr, DecidableEq

/-- A labeled directed edge: `source --[kind, label]--> target`.
In WG, all knowledge is encoded as links between nodes: "cat isA mammal",
"bird --front-limb--> wing", "male or female". -/
structure Link (α R : Type) where
  kind : LinkKind
  source : α
  target : α
  label : Option R := none
  deriving Repr, DecidableEq

-- ============================================================================
-- Network
-- ============================================================================

/-- A WG inheritance network: nodes connected by labeled directed links.
Parameterized over node type `α` and relation-label type `R`. -/
structure Network (α R : Type) [DecidableEq α] [DecidableEq R] where
  links : List (Link α R)

section NetworkOps

variable {α R : Type} [DecidableEq α] [DecidableEq R]

/-- The finite set of nodes mentioned by the network's links.
Used as the natural termination bound for traversals — the longest acyclic
path in a finite network cannot exceed `nodeUniverse.length` steps. -/
def Network.nodeUniverse (net : Network α R) : List α :=
  (net.links.map Link.source ++ net.links.map Link.target).dedup

-- ============================================================================
-- Taxonomy (isA)
-- ============================================================================

/-- Direct isA parents of a node. -/
def parents (net : Network α R) (node : α) : List α :=
  (net.links.filter (fun l => l.kind == .isA && l.source == node)).map Link.target

/-- Bounded transitive closure of `parents`. The `bound` parameter is intended
to be ≥ `(nodeUniverse net).length`; under that assumption every reachable
ancestor appears. Structurally recursive on `Nat` to keep `decide` happy. -/
def ancestorsBound (net : Network α R) (node : α) : Nat → List α
  | 0 => []
  | n + 1 =>
    let ps := parents net node
    ps ++ ps.flatMap (fun p => ancestorsBound net p n)

/-- Transitive ancestors of `node` in the isA taxonomy. The recursion bound
is derived from the network itself (number of distinct nodes), so finite
networks always traverse to fixpoint without a magic constant. -/
def ancestors (net : Network α R) (node : α) : List α :=
  ancestorsBound net node net.nodeUniverse.length

-- ============================================================================
-- IsA: propositional reflexive-transitive `isA` via mathlib's `ReflTransGen`
-- ============================================================================

/-- The single-step parent relation. -/
def isAEdge (net : Network α R) (a b : α) : Prop := b ∈ parents net a

instance (net : Network α R) (a b : α) : Decidable (isAEdge net a b) :=
  inferInstanceAs (Decidable (b ∈ parents net a))

/-- Reflexive-transitive `isA`: `a` inherits from `b` along the chain of isA
links. Defined as `Relation.ReflTransGen` of the parent edge — the same
construction mathlib uses for transitive closures elsewhere, so every lemma
about `ReflTransGen` (and the `Preorder` structure in `Core.Inheritance.Order`)
applies for free. -/
def IsA (net : Network α R) (a b : α) : Prop := Relation.ReflTransGen (isAEdge net) a b

/-- Every node `IsA` itself. -/
theorem IsA.refl (net : Network α R) (a : α) : IsA net a a :=
  Relation.ReflTransGen.refl

/-- `IsA` is transitive (mathlib gives this for free via `ReflTransGen.trans`). -/
theorem IsA.trans (net : Network α R) {a b c : α}
    (hab : IsA net a b) (hbc : IsA net b c) : IsA net a c :=
  Relation.ReflTransGen.trans hab hbc

-- ----------------------------------------------------------------------------
-- Constructors and computational-evidence bridges
-- ----------------------------------------------------------------------------

/-- Single isA links are tracked: if `a → b` is an isA link, then `b ∈ parents net a`. -/
theorem mem_parents_of_isALink (net : Network α R) {a b : α}
    (h : ⟨LinkKind.isA, a, b, none⟩ ∈ net.links) :
    b ∈ parents net a := by
  simp only [parents, List.mem_map, List.mem_filter]
  exact ⟨⟨LinkKind.isA, a, b, none⟩, ⟨h, by simp⟩, rfl⟩

/-- A direct isA edge gives the propositional `IsA` in one step. -/
theorem IsA.of_isAEdge (net : Network α R) {a b : α}
    (h : isAEdge net a b) : IsA net a b :=
  Relation.ReflTransGen.single h

/-- Membership in the bounded transitive closure implies `IsA`. Proved by
induction on the fuel. -/
theorem IsA.of_mem_ancestorsBound (net : Network α R) :
    ∀ (n : Nat) (a b : α), b ∈ ancestorsBound net a n → IsA net a b
  | 0, _, _, h => by simp [ancestorsBound] at h
  | n + 1, a, b, h => by
    simp only [ancestorsBound, List.mem_append, List.mem_flatMap] at h
    rcases h with hpar | ⟨p, hp_par, hp_anc⟩
    · exact IsA.of_isAEdge net hpar
    · have h_pa : isAEdge net a p := hp_par
      have h_pb : IsA net p b := IsA.of_mem_ancestorsBound net n p b hp_anc
      exact Relation.ReflTransGen.head h_pa h_pb

/-- Membership in `ancestors` implies `IsA`. The convenience entry point for
constructing `IsA net a b` proofs from a `decide`-able list-membership goal:
`IsA.of_mem_ancestors _ (by decide)`. -/
theorem IsA.of_mem_ancestors (net : Network α R) {a b : α}
    (h : b ∈ ancestors net a) : IsA net a b :=
  IsA.of_mem_ancestorsBound net _ a b h

-- ----------------------------------------------------------------------------
-- Path compression: the reverse direction `IsA → b ∈ ancestors`
-- ----------------------------------------------------------------------------

/-- Membership characterization for `ancestorsBound (n+1)`: a node `x` is reachable
within `n+1` steps from `a` iff it is a direct parent of `a`, or it is reachable
within `n` steps from some direct parent of `a`. -/
theorem mem_ancestorsBound_succ_iff (net : Network α R) (a x : α) (n : Nat) :
    x ∈ ancestorsBound net a (n + 1) ↔
      x ∈ parents net a ∨ ∃ p ∈ parents net a, x ∈ ancestorsBound net p n := by
  simp only [ancestorsBound, List.mem_append, List.mem_flatMap]

/-- `ancestorsBound` is monotone in fuel: more fuel gives at least as many
ancestors. The new layer `n + 1` always contains the layer `n`. -/
theorem ancestorsBound_succ_subset (net : Network α R) (a : α) :
    ∀ n, ancestorsBound net a n ⊆ ancestorsBound net a (n + 1)
  | 0 => by intro x hx; simp [ancestorsBound] at hx
  | n + 1 => by
    intro x hx
    rw [mem_ancestorsBound_succ_iff] at hx
    rw [mem_ancestorsBound_succ_iff]
    rcases hx with hpar | ⟨p, hp_par, hp_anc⟩
    · exact Or.inl hpar
    · exact Or.inr ⟨p, hp_par, ancestorsBound_succ_subset net p n hp_anc⟩

/-- Monotonicity of `ancestorsBound` in the fuel parameter. -/
theorem ancestorsBound_mono (net : Network α R) (a : α) {n m : Nat} (h : n ≤ m) :
    ancestorsBound net a n ⊆ ancestorsBound net a m := by
  induction h with
  | refl => exact fun _ hx => hx
  | step _ ih =>
    exact fun x hx => ancestorsBound_succ_subset net a _ (ih hx)

/-- Direct parents of any node are mentioned by some isA link, hence in
`nodeUniverse`. -/
theorem mem_nodeUniverse_of_mem_parents (net : Network α R) (a b : α)
    (h : b ∈ parents net a) : b ∈ net.nodeUniverse := by
  simp only [parents, List.mem_map, List.mem_filter] at h
  obtain ⟨l, ⟨hmem, _⟩, htgt⟩ := h
  simp only [Network.nodeUniverse, List.mem_dedup]
  exact List.mem_append_right _ (List.mem_map.2 ⟨l, hmem, htgt⟩)

/-- Every element of `ancestorsBound net a n` for `n ≥ 1` is in `nodeUniverse net`
(it must appear as the target of some isA link). -/
theorem mem_nodeUniverse_of_mem_ancestorsBound (net : Network α R) (a : α) :
    ∀ n b, b ∈ ancestorsBound net a n → b ∈ net.nodeUniverse
  | 0, _, h => by simp [ancestorsBound] at h
  | n + 1, b, h => by
    simp only [ancestorsBound, List.mem_append, List.mem_flatMap] at h
    rcases h with hpar | ⟨p, _, hp_anc⟩
    · exact mem_nodeUniverse_of_mem_parents net a b hpar
    · exact mem_nodeUniverse_of_mem_ancestorsBound net p n b hp_anc

/-- Helper: extend an `ancestorsBound` membership by one isA edge.
If `b ∈ ancestorsBound net a n` and `isAEdge net b c`, then `c ∈ ancestorsBound net a (n+1)`. -/
theorem ancestorsBound_extend (net : Network α R) (a b c : α) :
    ∀ n, b ∈ ancestorsBound net a n → isAEdge net b c →
        c ∈ ancestorsBound net a (n + 1)
  | 0, h, _ => by simp [ancestorsBound] at h
  | n + 1, h, hbc => by
    rw [mem_ancestorsBound_succ_iff] at h
    rw [mem_ancestorsBound_succ_iff]
    rcases h with hpar | ⟨p, hp_par, hp_anc⟩
    · -- b is a direct parent of a; chain a → b → c gives c ∈ ancestorsBound a (n+2)
      -- via p = b, c ∈ ancestorsBound b (n+1) by the parents-of-b case.
      right
      refine ⟨b, hpar, ?_⟩
      rw [mem_ancestorsBound_succ_iff]
      exact Or.inl hbc
    · right
      exact ⟨p, hp_par, ancestorsBound_extend net p b c n hp_anc hbc⟩

/-- An `IsA` chain witnesses membership in `ancestorsBound` at some fuel level.
The fuel `n` here is the chain length and may be larger than `nodeUniverse.length`;
the next lemma compresses it. -/
theorem mem_ancestorsBound_of_isA (net : Network α R) {a b : α} (h : IsA net a b) :
    a = b ∨ ∃ n, b ∈ ancestorsBound net a n := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail b' c _ hbc ih =>
    rcases ih with hab | ⟨n, hmem⟩
    · subst hab
      refine Or.inr ⟨1, ?_⟩
      simp only [ancestorsBound, List.mem_append]
      exact Or.inl hbc
    · exact Or.inr ⟨n + 1, ancestorsBound_extend net a b' c n hmem hbc⟩

-- ----------------------------------------------------------------------------
-- Chain characterization and path compression
-- ----------------------------------------------------------------------------

/-- A chain of intermediate nodes `[c₁, c₂, ..., cₖ]` witnesses
`a → c₁ → c₂ → ... → cₖ → b` via `isAEdge` steps. The empty chain `[]`
witnesses a direct edge `a → b`. -/
def IsAChain (net : Network α R) (a : α) : List α → α → Prop
  | [], b => isAEdge net a b
  | x :: xs, b => isAEdge net a x ∧ IsAChain net x xs b

/-- Membership in `ancestorsBound (n+1)` is equivalent to existence of an
intermediate chain of length `≤ n`. -/
theorem mem_ancestorsBound_iff_chain (net : Network α R) (a b : α) :
    ∀ n, b ∈ ancestorsBound net a n ↔ ∃ chain : List α, chain.length < n ∧ IsAChain net a chain b
  | 0 => by
    simp only [ancestorsBound, List.not_mem_nil, false_iff, not_exists]
    intro chain ⟨h, _⟩
    exact Nat.not_lt_zero _ h
  | n + 1 => by
    rw [mem_ancestorsBound_succ_iff]
    constructor
    · rintro (hpar | ⟨p, hp_par, hp_anc⟩)
      · exact ⟨[], Nat.zero_lt_succ _, hpar⟩
      · obtain ⟨chain, hlen, hc⟩ := (mem_ancestorsBound_iff_chain net p b n).mp hp_anc
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
        exact (mem_ancestorsBound_iff_chain net x b n).mpr ⟨xs, hxs_lt, hr⟩

/-- An `IsAChain` from `a` to `b` realises `IsA net a b`. -/
theorem IsA.of_chain (net : Network α R) {a b : α} :
    ∀ {chain : List α}, IsAChain net a chain b → IsA net a b
  | [], h => IsA.of_isAEdge net h
  | _ :: _, ⟨hax, hr⟩ => Relation.ReflTransGen.head hax (IsA.of_chain net hr)

/-- Helper: extend a chain by one edge at the END. -/
theorem IsAChain.snoc (net : Network α R) {a b c : α} :
    ∀ {chain : List α}, IsAChain net a chain b → isAEdge net b c →
        IsAChain net a (chain ++ [b]) c
  | [], h, hbc => ⟨h, hbc⟩
  | _ :: _, ⟨hax, hr⟩, hbc => ⟨hax, IsAChain.snoc net hr hbc⟩

/-- `IsA` either holds reflexively or yields an explicit chain. -/
theorem IsA.cases_chain (net : Network α R) {a b : α} (h : IsA net a b) :
    a = b ∨ ∃ chain : List α, IsAChain net a chain b := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail b' c _ hbc ih =>
    rcases ih with rfl | ⟨chain, hc⟩
    · exact Or.inr ⟨[], hbc⟩
    · exact Or.inr ⟨chain ++ [b'], hc.snoc net hbc⟩

/-- All intermediate nodes of a chain are in the network's `nodeUniverse`. -/
theorem IsAChain.intermediates_in_universe (net : Network α R) {a b : α} :
    ∀ {chain : List α}, IsAChain net a chain b → ∀ x ∈ chain, x ∈ net.nodeUniverse
  | [], _, _, hx => by simp at hx
  | _ :: xs, ⟨hax, hr⟩, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx_tail
    · exact mem_nodeUniverse_of_mem_parents net _ _ hax
    · exact IsAChain.intermediates_in_universe net hr x hx_tail

/-- The endpoint `b` of a chain is in `nodeUniverse`. -/
theorem IsAChain.endpoint_in_universe (net : Network α R) {a b : α} :
    ∀ {chain : List α}, IsAChain net a chain b → b ∈ net.nodeUniverse
  | [], h => mem_nodeUniverse_of_mem_parents net _ _ h
  | _ :: _, ⟨_, hr⟩ => IsAChain.endpoint_in_universe net hr

/-- **Chain compression** (right-truncation): if `b` appears as an intermediate
in the chain, truncate to the prefix ending at `b`'s first occurrence. -/
theorem IsAChain.truncate_at_target (net : Network α R) {a b : α} :
    ∀ {chain : List α}, IsAChain net a chain b → b ∈ chain →
        ∃ chain' : List α, chain'.length < chain.length ∧ IsAChain net a chain' b
  | [], _, hb_in => by simp at hb_in
  | x :: xs, ⟨hax, hr⟩, hb_in => by
    rcases List.mem_cons.mp hb_in with rfl | hb_in_xs
    · exact ⟨[], by simp, hax⟩
    · obtain ⟨chain', hlen, hc'⟩ := IsAChain.truncate_at_target net hr hb_in_xs
      refine ⟨x :: chain', ?_, hax, hc'⟩
      simp; omega

/-- Helper: if a chain `IsAChain net x chain b` contains node `y`, the suffix
from `y`'s first occurrence is itself a chain `IsAChain net y _ b` of strictly
smaller length. -/
theorem IsAChain.suffix_from (net : Network α R) {x b : α} (y : α) :
    ∀ {chain : List α}, IsAChain net x chain b → y ∈ chain →
        ∃ tail : List α, tail.length < chain.length ∧ IsAChain net y tail b
  | [], _, h_in => by simp at h_in
  | z :: zs, ⟨_, hr⟩, h_in => by
    rcases List.mem_cons.mp h_in with rfl | h_in_zs
    · exact ⟨zs, by simp, hr⟩
    · obtain ⟨tail, hlen, htail⟩ := IsAChain.suffix_from net y hr h_in_zs
      exact ⟨tail, by simp; omega, htail⟩

/-- **Chain compression** (skip-to-self): if `a` appears as an intermediate,
take the suffix from `a`'s reappearance. -/
theorem IsAChain.skip_to_self (net : Network α R) {a b : α}
    {chain : List α} (h : IsAChain net a chain b) (ha_in : a ∈ chain) :
    ∃ chain' : List α, chain'.length < chain.length ∧ IsAChain net a chain' b := by
  -- chain = x :: xs; if x = a use xs directly, else recurse via suffix_from on xs
  match chain, h with
  | x :: xs, ⟨_, hr⟩ =>
    rcases List.mem_cons.mp ha_in with rfl | ha_in_xs
    · exact ⟨xs, by simp, hr⟩
    · obtain ⟨tail, hlen, htail⟩ := IsAChain.suffix_from net a hr ha_in_xs
      exact ⟨tail, by simp; omega, htail⟩

/-- **Chain compression** (interior duplication): if some node appears twice
in the chain, splice out the cycle. Uses `suffix_from` on the duplicate. -/
theorem IsAChain.dedup_interior (net : Network α R) {a b : α} :
    ∀ {chain : List α}, IsAChain net a chain b → ¬ chain.Nodup →
        ∃ chain' : List α, chain'.length < chain.length ∧ IsAChain net a chain' b
  | [], _, hnd => absurd List.nodup_nil hnd
  | x :: xs, ⟨hax, hr⟩, hnd => by
    rw [List.nodup_cons, not_and_or] at hnd
    rcases hnd with hx_in_xs | hxs_not_nodup
    · -- x appears in xs; can splice via suffix_from
      simp only [not_not] at hx_in_xs
      obtain ⟨tail, hlen, htail⟩ := IsAChain.suffix_from net x hr hx_in_xs
      exact ⟨x :: tail, by simp; omega, hax, htail⟩
    · -- xs itself has duplicates; recurse
      obtain ⟨xs', hlen, hxs'⟩ := IsAChain.dedup_interior net hr hxs_not_nodup
      exact ⟨x :: xs', by simp; omega, hax, hxs'⟩

/-- The full compression: any chain reduces to one with no repeats and
disjoint from `{a, b}`. Strong induction on chain length, applying the three
truncation forms in order. -/
theorem IsAChain.compress (net : Network α R) {a b : α} :
    ∀ (n : Nat) (chain : List α), chain.length = n → IsAChain net a chain b →
        ∃ chain' : List α, IsAChain net a chain' b ∧ chain'.Nodup ∧
            a ∉ chain' ∧ b ∉ chain' := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro chain hlen h
    by_cases hb_in : b ∈ chain
    · obtain ⟨chain', hlen', hc'⟩ := h.truncate_at_target net hb_in
      exact ih chain'.length (hlen ▸ hlen') chain' rfl hc'
    by_cases ha_in : a ∈ chain
    · obtain ⟨chain', hlen', hc'⟩ := h.skip_to_self net ha_in
      exact ih chain'.length (hlen ▸ hlen') chain' rfl hc'
    by_cases hnd : chain.Nodup
    · exact ⟨chain, h, hnd, ha_in, hb_in⟩
    · obtain ⟨chain', hlen', hc'⟩ := h.dedup_interior net hnd
      exact ih chain'.length (hlen ▸ hlen') chain' rfl hc'

/-- Convenience wrapper around `compress` without the explicit length. -/
theorem IsAChain.compress' (net : Network α R) {a b : α} {chain : List α}
    (h : IsAChain net a chain b) :
    ∃ chain' : List α, IsAChain net a chain' b ∧ chain'.Nodup ∧
        a ∉ chain' ∧ b ∉ chain' :=
  IsAChain.compress net chain.length chain rfl h

/-- Length bound: a `Nodup` chain whose intermediates lie in `nodeUniverse`,
and whose target `b` is also in `nodeUniverse` and not in the chain, has
length `< nodeUniverse.length`. -/
theorem IsAChain.compressed_length_lt (net : Network α R) {a b : α}
    {chain : List α} (h : IsAChain net a chain b)
    (hnodup : chain.Nodup) (hb_notin : b ∉ chain) :
    chain.length < net.nodeUniverse.length := by
  have h_subset : chain ⊆ net.nodeUniverse :=
    fun x hx => h.intermediates_in_universe net x hx
  have hb_in_U : b ∈ net.nodeUniverse := h.endpoint_in_universe net
  have hbchain_nodup : (b :: chain).Nodup := List.nodup_cons.mpr ⟨hb_notin, hnodup⟩
  have hbchain_subset : (b :: chain) ⊆ net.nodeUniverse := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx_tail
    · exact hb_in_U
    · exact h_subset hx_tail
  have hsub : List.Subperm (b :: chain) net.nodeUniverse :=
    hbchain_nodup.subperm hbchain_subset
  have hle : (b :: chain).length ≤ net.nodeUniverse.length := hsub.length_le
  simpa using hle

/-- **Path compression theorem**: if `b` is reachable from `a` at any fuel,
it is reachable at fuel `nodeUniverse.length`. -/
theorem mem_ancestors_of_mem_ancestorsBound (net : Network α R) (a b : α) :
    ∀ n, b ∈ ancestorsBound net a n → b ∈ ancestors net a := by
  intro n h
  obtain ⟨chain, _, hc⟩ := (mem_ancestorsBound_iff_chain net a b n).mp h
  obtain ⟨chain', hc', hnodup', _, hb_notin'⟩ := hc.compress' net
  have hlen : chain'.length < net.nodeUniverse.length :=
    hc'.compressed_length_lt net hnodup' hb_notin'
  exact (mem_ancestorsBound_iff_chain net a b net.nodeUniverse.length).mpr
    ⟨chain', hlen, hc'⟩

/-- The reverse direction: `IsA` is captured by the bounded BFS. -/
theorem mem_ancestors_of_isA (net : Network α R) {a b : α} (h : IsA net a b) :
    a = b ∨ b ∈ ancestors net a := by
  rcases h.cases_chain net with heq | ⟨chain, hc⟩
  · exact Or.inl heq
  · obtain ⟨chain', hc', hnodup', _, hb_notin'⟩ := hc.compress' net
    have hlen : chain'.length < net.nodeUniverse.length :=
      hc'.compressed_length_lt net hnodup' hb_notin'
    exact Or.inr ((mem_ancestorsBound_iff_chain net a b net.nodeUniverse.length).mpr
      ⟨chain', hlen, hc'⟩)

/-- The full characterization: `IsA` iff reflexive or BFS-reachable. -/
theorem isA_iff_eq_or_mem_ancestors (net : Network α R) (a b : α) :
    IsA net a b ↔ a = b ∨ b ∈ ancestors net a := by
  refine ⟨mem_ancestors_of_isA net, ?_⟩
  rintro (rfl | hmem)
  · exact IsA.refl net a
  · exact IsA.of_mem_ancestors net hmem

/-- `IsA` is decidable on finite networks (no `Fintype α` required —
the network's own `nodeUniverse` provides the bound). -/
instance isA_decidable (net : Network α R) (a b : α) : Decidable (IsA net a b) :=
  decidable_of_iff _ (isA_iff_eq_or_mem_ancestors net a b).symm

end NetworkOps

end Core.Inheritance
