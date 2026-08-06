/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.DependencyGrammar.Projection
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Catenae

This file defines a catena: a word or combination of words connected in
the undirected presentation of a dependency tree. 

-/

namespace DependencyGrammar

variable {n : ℕ}

/-- `s` is a **catena** if the subgraph induced on `s` is connected. -/
def IsCatena (g : Graph n) (s : Finset (Fin n)) : Prop :=
  (g.toSimpleGraph.induce ↑s).Connected

/-- `s` is a **constituent**: exactly the dominance cone of some position. -/
def IsConstituent (g : Graph n) (s : Finset (Fin n)) : Prop :=
  ∃ v, ∀ w, w ∈ s ↔ Dominates g v w

instance (g : Graph n) (s : Finset (Fin n)) : Decidable (IsCatena g s) :=
  inferInstanceAs (Decidable (SimpleGraph.Connected _))

instance (g : Graph n) (s : Finset (Fin n)) : Decidable (IsConstituent g s) :=
  inferInstanceAs (Decidable (∃ _, _))

/-- Every single word is a catena. -/
theorem singleton_isCatena (g : Graph n) (v : Fin n) : IsCatena g {v} := by
  rw [IsCatena, Finset.coe_singleton]
  exact .of_subsingleton

/-- The dominance cone of a position induces a connected subgraph of the
    undirected view: each dominated position is reached along its own
    dominance path, which never leaves the cone. -/
theorem connected_induce_cone (g : Graph n) (v : Fin n) :
    (g.toSimpleGraph.induce {x | Dominates g v x}).Connected := by
  refine (SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨⟨v, .refl⟩, ?_⟩
  rintro ⟨w, hw⟩
  induction hw with
  | refl => exact .rfl
  | @tail b c hb hbc ih =>
    rcases eq_or_ne b c with rfl | hne
    · exact ih
    · exact ih.trans (SimpleGraph.Adj.reachable ⟨hne, Or.inl hbc⟩)

/-- Every constituent is a catena: a constituent is the dominance cone of
    some position, and cones induce connected subgraphs. -/
theorem IsConstituent.isCatena {g : Graph n} {s : Finset (Fin n)}
    (h : IsConstituent g s) : IsCatena g s := by
  obtain ⟨v, hv⟩ := h
  rw [IsCatena, show (↑s : Set (Fin n)) = {x | Dominates g v x} from Set.ext hv]
  exact connected_induce_cone g v

end DependencyGrammar
