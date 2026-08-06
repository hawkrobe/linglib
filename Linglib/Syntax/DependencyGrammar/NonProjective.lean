/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.DependencyGrammar.Projection

/-!
# Planarity, well-nestedness, and projectivity

The mild non-projectivity hierarchy of [kuhlmann-nivre-2006] and
[kuhlmann-2013], stated Prop-natively over the dominance relation:
projectivity as order-convexity of each position's dominance cone,
planarity as the absence of crossing links (the notion [melcuk-1988]
introduced, via Sleator & Temperley's Link Grammar), and well-nestedness
as the absence of interleaving between disjoint subtrees. All three are
decidable, so concrete fixtures close by `decide`; the hierarchy theorems
(projective ⊆ planar ⊆ well-nested on trees, [kuhlmann-nivre-2006] §3.5)
are ported in a follow-up stage, together with the bridge from
`Graph.IsTree` to mathlib's order-theoretic `RootedTree` (dominance as the
partial order, parent as `pred`, root as `⊥`, lowest common governor
as `⊓`).

The canonical fixture pair from [kuhlmann-2013] Figure 1 — Dutch
cross-serial vs German nested infinitives — lives here, together with
[kuhlmann-nivre-2006] Figure 2a's planar-but-not-projective witness, the
distinction the paper most insists on.
-/

namespace DependencyGrammar

open Morphology (Word)

section Defs

variable {n : ℕ}

/-- Positions linked by an arc in either direction — the undirected view
    under which planarity is stated. -/
def Linked (g : Graph n) (a b : Fin n) : Prop := g.Adj a b ∨ g.Adj b a

instance (g : Graph n) (a b : Fin n) : Decidable (Linked g a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- **Planarity**: no two links cross — spans, taken left-to-right, never
    strictly interleave. ([melcuk-1988]'s constraint; [kuhlmann-nivre-2006]
    §3.) -/
def IsPlanar (g : Graph n) : Prop :=
  ∀ ⦃a b c d : Fin n⦄, a < b → c < d → Linked g a b → Linked g c d →
    ¬ (a < c ∧ c < b ∧ b < d)

/-- **Projectivity**, relationally: every dominance cone is order-convex.
    Equivalent to "every projection is an interval"
    ([kuhlmann-nivre-2006], Definition 3). -/
def IsProjective (g : Graph n) : Prop :=
  ∀ v : Fin n, ∀ ⦃a b c : Fin n⦄,
    Dominates g v a → Dominates g v c → a ≤ b → b ≤ c → Dominates g v b

/-- The subtrees at `v` and `w` interleave: each contributes two positions
    arranged strictly alternately. ([kuhlmann-nivre-2006], Definition 8) -/
def Interleave (g : Graph n) (v w : Fin n) : Prop :=
  ∃ a ∈ projection g v, ∃ b ∈ projection g v,
    ∃ c ∈ projection g w, ∃ d ∈ projection g w,
      a < c ∧ c < b ∧ b < d

/-- **Well-nestedness**: disjoint subtrees (neither root dominating the
    other) never interleave. ([kuhlmann-nivre-2006], Definition 8) -/
def IsWellNested (g : Graph n) : Prop :=
  ∀ v w : Fin n, ¬ Dominates g v w → ¬ Dominates g w v → ¬ Interleave g v w

instance (g : Graph n) : Decidable (IsPlanar g) :=
  inferInstanceAs (Decidable (∀ _, _))

instance (g : Graph n) : Decidable (IsProjective g) :=
  inferInstanceAs (Decidable (∀ _, _))

instance (g : Graph n) (v w : Fin n) : Decidable (Interleave g v w) :=
  List.decidableBEx _ _

instance (g : Graph n) : Decidable (IsWellNested g) :=
  inferInstanceAs (Decidable (∀ _, _))

end Defs

/-! ### Canonical fixtures

[kuhlmann-2013] Figure 1: Dutch cross-serial dependencies against German
nested infinitives — same dependencies, opposite verb-cluster orders. -/

/-- Dutch cross-serial: "dat Jan Piet Marie zag helpen lezen". -/
def dutchCrossSerial : Graph 7 :=
  .ofArcs
    [Word.mk' "dat" .SCONJ, Word.mk' "Jan" .PROPN, Word.mk' "Piet" .PROPN,
     Word.mk' "Marie" .PROPN, Word.mk' "zag" .VERB, Word.mk' "helpen" .VERB,
     Word.mk' "lezen" .VERB]
    0
    [(0, 4, .dep), (4, 1, .nsubj), (4, 5, .xcomp),
     (5, 2, .nsubj), (5, 6, .xcomp), (6, 3, .nsubj)]

/-- German nested: "dass Jan Piet Marie lesen helfen sah". -/
def germanNested : Graph 7 :=
  .ofArcs
    [Word.mk' "dass" .SCONJ, Word.mk' "Jan" .PROPN, Word.mk' "Piet" .PROPN,
     Word.mk' "Marie" .PROPN, Word.mk' "lesen" .VERB, Word.mk' "helfen" .VERB,
     Word.mk' "sah" .VERB]
    0
    [(0, 6, .dep), (6, 1, .nsubj), (6, 5, .xcomp),
     (5, 2, .nsubj), (5, 4, .xcomp), (4, 3, .nsubj)]

/-- [kuhlmann-nivre-2006] Figure 2a: planar but **not** projective — no
    crossing links, yet the yield of position 0 is not an interval. -/
def planarNotProjective : Graph 4 :=
  .ofArcs
    [Word.mk' "w0" .X, Word.mk' "w1" .X, Word.mk' "w2" .X, Word.mk' "w3" .X]
    2
    [(2, 0, .dep), (2, 1, .dep), (0, 3, .dep)]

example : dutchCrossSerial.IsTree := by decide
example : germanNested.IsTree := by decide
example : ¬ IsPlanar dutchCrossSerial := by decide
example : ¬ IsProjective dutchCrossSerial := by decide
example : IsWellNested dutchCrossSerial := by decide
example : IsPlanar germanNested := by decide
example : IsProjective germanNested := by decide
example : IsPlanar planarNotProjective := by decide
example : ¬ IsProjective planarNotProjective := by decide
example : dutchCrossSerial.gapDegree = 1 := by decide
example : germanNested.gapDegree = 0 := by decide

end DependencyGrammar
