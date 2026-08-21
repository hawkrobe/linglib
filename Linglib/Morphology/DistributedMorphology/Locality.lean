import Linglib.Morphology.DistributedMorphology.Categorizer.Basic
import Mathlib.Tactic.Abel

/-!
# Locality domains for contextual allomorphy and allosemy

A word is its root with the heads merged above it, innermost first. A cyclic
head sends its complement for interpretation, and the root adjoins to the
first categorizing head, so the root's spell-out domain is that head together
with the noncyclic heads above it, up to the next cyclic head: a head is local
to the root when at most one cyclic head lies at or below it. Within the
domain each interface adds its own adjacency — a head conditions the root
only across heads that are null at that interface, phonologically for
allomorphy, semantically for allosemy — so the two domains coincide exactly
where the two kinds of nullness do. The idiom domain is a different bound,
the heads below an agentive Voice, and neither contains the other.

## Main definitions

* `Spine`, `Spine.toWordStructure`: the word as root and head sequence, and
  its word-structure tree.
* `Spine.RootLocal`: the root's spell-out domain.
* `Spine.Visible`: locality plus adjacency through heads null at an interface.
* `Spine.IdiomLocal`: the heads below an agentive Voice.

## Main results

* `RootLocal.of_le`: the domain is an initial segment.
* `not_rootLocal_of_cyclic_of_cyclic`, `RootLocal.cyclic_first`: an outer
  cyclic head is not local, and a local cyclic head is the first.
* `not_visible_of_not_null`: an intervening non-null head blocks conditioning.
* `visible_congr`: the interface domains agree where nullness agrees.

## References

* [A. Marantz, *Locality domains for contextual allomorphy across the
  interfaces*][marantz-2013]
* [D. Embick, *Localism versus globalism in morphology and phonology*][embick-2010]
* [D. Embick, *The motivation for roots in Distributed Morphology*][embick-2021]
-/

namespace DistributedMorphology

/-- A word as its root and the heads merged above it, innermost first. -/
structure Spine (H : Type*) where
  /-- The root. -/
  root : Root
  /-- The heads above the root, innermost first. -/
  heads : List H
  deriving DecidableEq, Repr

namespace Spine

variable {H : Type*} (s : Spine H)

/-! ### The word-structure tree -/

/-- The word structure the spine builds: each head categorizes what lies below it. -/
noncomputable def toWordStructure : WordStructure H :=
  s.heads.foldl (fun T h => categorize h T) (ofRoot s.root)

theorem heads_foldl_categorize (T : WordStructure H) : ∀ hs : List H,
    DistributedMorphology.heads (hs.foldl (fun T h => categorize h T) T) =
      ↑hs + DistributedMorphology.heads T
  | [] => by simp
  | h :: hs => by
    rw [List.foldl_cons, heads_foldl_categorize (categorize h T) hs, heads_categorize]
    simp only [← Multiset.cons_coe, ← Multiset.singleton_add]
    abel

theorem roots_foldl_categorize (T : WordStructure H) : ∀ hs : List H,
    DistributedMorphology.roots (hs.foldl (fun T h => categorize h T) T) =
      DistributedMorphology.roots T
  | [] => rfl
  | h :: hs => by rw [List.foldl_cons, roots_foldl_categorize (categorize h T) hs, roots_categorize]

@[simp] theorem roots_toWordStructure :
    DistributedMorphology.roots s.toWordStructure = {s.root} := by
  rw [toWordStructure, roots_foldl_categorize, roots_ofRoot]

@[simp] theorem heads_toWordStructure :
    DistributedMorphology.heads s.toWordStructure = ↑s.heads := by
  rw [toWordStructure, heads_foldl_categorize, heads_ofRoot, add_zero]

/-! ### The root's spell-out domain -/

variable (cyclic : H → Prop)

/-- A head is local to the root when at most one cyclic head lies at or below
it: the first categorizer, which the root adjoins to, and the noncyclic heads
above it up to the next cyclic head. -/
def RootLocal (i : Fin s.heads.length) : Prop :=
  ∀ j k, j ≤ i → k ≤ i → cyclic s.heads[j] → cyclic s.heads[k] → j = k

instance [DecidablePred cyclic] (i : Fin s.heads.length) : Decidable (s.RootLocal cyclic i) := by
  unfold RootLocal; infer_instance

variable {s cyclic} {i j : Fin s.heads.length}

/-- The domain is an initial segment. -/
theorem RootLocal.of_le (h : s.RootLocal cyclic i) (hji : j ≤ i) : s.RootLocal cyclic j :=
  fun _ _ hj hk => h _ _ (hj.trans hji) (hk.trans hji)

/-- A cyclic head above a cyclic head is not local to the root: category
change closes the root's domain. -/
theorem not_rootLocal_of_cyclic_of_cyclic (hji : j < i) (hj : cyclic s.heads[j])
    (hi : cyclic s.heads[i]) : ¬ s.RootLocal cyclic i :=
  fun h => hji.ne (h j i hji.le le_rfl hj hi)

/-- A local cyclic head is the first one. -/
theorem RootLocal.cyclic_first (h : s.RootLocal cyclic i) (hi : cyclic s.heads[i]) :
    ∀ j < i, ¬ cyclic s.heads[j] :=
  fun j hji hj => hji.ne (h j i hji.le le_rfl hj hi)

/-! ### Interface adjacency -/

variable (s cyclic) (null : H → Prop)

/-- A head is visible to the root at an interface when it is local and every
head between them is null at that interface: phonologically null for
allomorphy, semantically null for allosemy. -/
def Visible (i : Fin s.heads.length) : Prop :=
  s.RootLocal cyclic i ∧ ∀ j < i, null s.heads[j]

instance [DecidablePred cyclic] [DecidablePred null] (i : Fin s.heads.length) :
    Decidable (s.Visible cyclic null i) :=
  inferInstanceAs (Decidable (_ ∧ ∀ j < i, _))

variable {s cyclic null}

theorem Visible.rootLocal (h : s.Visible cyclic null i) : s.RootLocal cyclic i := h.1

/-- An intervening head that is not null at the interface blocks conditioning,
local or not. -/
theorem not_visible_of_not_null (hji : j < i) (hj : ¬ null s.heads[j]) :
    ¬ s.Visible cyclic null i :=
  fun h => hj (h.2 j hji)

/-- The interface domains agree wherever the two kinds of nullness agree below
the head: the single cycle bounds both. -/
theorem visible_congr {null' : H → Prop}
    (h : ∀ j < i, null s.heads[j] ↔ null' s.heads[j]) :
    s.Visible cyclic null i ↔ s.Visible cyclic null' i :=
  and_congr_right fun _ => forall₂_congr fun j hji => h j hji

/-! ### The idiom domain -/

variable (s) (agentive : H → Prop)

/-- The heads below an agentive Voice: special meaning may be assigned to any
structure not containing an external-argument-introducing head, across cyclic
heads. -/
def IdiomLocal (i : Fin s.heads.length) : Prop :=
  ∀ j ≤ i, ¬ agentive s.heads[j]

instance [DecidablePred agentive] (i : Fin s.heads.length) : Decidable (s.IdiomLocal agentive i) :=
  inferInstanceAs (Decidable (∀ j ≤ i, _))

variable {s agentive}

theorem IdiomLocal.of_le (h : s.IdiomLocal agentive i) (hji : j ≤ i) : s.IdiomLocal agentive j :=
  fun _ hj => h _ (hj.trans hji)

end Spine

end DistributedMorphology
