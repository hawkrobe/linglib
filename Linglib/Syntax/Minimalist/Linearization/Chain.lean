/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Build
public import Linglib.Syntax.Minimalist.SyntacticObject.Position
public import Linglib.Syntax.Projection
public import Linglib.Core.Data.RoseTree.Get
public import Linglib.Syntax.Minimalist.SyntacticObject.Phase

/-!
# Chains on planar syntactic objects

A planar syntactic object is a copy-theoretic representation. A vertex `Vertex.lex tok` is a
pronounced copy of `tok` and a vertex `Vertex.traceOf tok` a deleted one, the trace Internal Merge
leaves, Marcolli, Chomsky and Berwick's cancellation `T/T_v` with the head of `T_v` remembered.
The chain of a token is the list of its copies, and a copy stands for the maximal projection of
its token, so a moved phrase sits where its head projects. A token moves when it has a deleted
copy. A token bound in situ by an operator, as for Pesetsky, has a single copy. A deleted copy
above the pronounced one is Huang's covert movement, and a pronounced copy between two deleted
ones is Sato and Ngui's partial movement, so where a phrase is pronounced and where it takes scope
come apart without a separate choice of the copy to spell out. A token with two pronounced copies
is shared, dominated by two mothers, Citko's Parallel Merge.

A copy is linked to the nearest copy above it, the one whose projection c-commands it with no
other copy's projection in between, c-command being Barker and Pullum's `PhraseStructure.CCommands`.
Locality constrains links. Chomsky's Phase Impenetrability Condition bars a link from the interior
of a phase, the positions its head c-commands, to a position outside the head's maximal
projection, so that the edge is the escape hatch (`Crosses`); an island is a domain no link may
leave (`Escapes`). A token with one copy has no link, so binding in situ is subject to neither
(`links_eq_nil_of_length_le_one`), and movement, covert movement included, is subject to both, as
Sato and Ngui find.

## Main definitions

* `Minimalist.tokenList`, `Minimalist.traceList`: the pronounced and the deleted copies.
* `occurrences`, `traces`, `chain`, `Moves`, `IsShared`: the copies of a token.
* `projectionAt`: the phrase a copy stands for, its maximal projection along head daughters
  (`headIndex?`, `PhraseStructure.maximalProjectionAt`).
* `HasAntecedent`, `orphanTraces`: whether a pronounced copy c-commands a deleted one, and the
  deleted copies without antecedents, seen from their own conjunct copies.
* `IsLink`, `links`, `chainTop`: the links of a chain and its scope position.
* `interior`, `Crosses`, `Escapes`: phases, islands, and the links that leave them.

## Main statements

* `withinComplement_iff_exists_mem_interior`: the positions in `interior` carry the terms within
  the complement of a phase head occurring once.

## Implementation notes

* Positions, not terms, individuate copies: two deleted copies of one token are the same term,
  so the phase interior of the unordered object (`SyntacticObject.phaseInterior`, the terms
  within the head's complement) cannot tell the links of a successive-cyclic chain apart.
  `interior` is the head's c-command domain on positions.
* The head daughters follow the raising head, and the drawing convention only where it is
  undefined (`headIndex?`, `SyntacticObject/Position.lean`), so that a phrase with a specifier
  merged in place still has a maximal projection to locate a copy in.
* A chain here is the copies an object contains; the replay of a derivation
  (`Derivation.externalize?`) builds overt chains with bound traces, while covert movement,
  sharing and copies without antecedents are available to the representation only.

## TODO

* A successful `Derivation.externalize?` has no deleted copy without an antecedent.

## References

* [marcolli-chomsky-berwick-2025]
* [citko-2005]
* [pesetsky-1987]
* [huang-1982]
* [sato-ngui-2017]
* [barker-pullum-1990]
* [chomsky-2000]
-/

@[expose] public section

namespace Minimalist

open RoseTree SyntacticObject Core.Order PhraseStructure

/-! ### Copies -/

/-- The positions of `t` whose label `f` accepts, with the values, in preorder. -/
def positions {β : Type*} (f : Vertex → Option β) (t : RoseTree Vertex) : List (TreePath × β) :=
  t.positionedSubtrees.filterMap fun x ↦ (f x.2.value).map (x.1, ·)

theorem mem_positions_iff {β : Type*} {f : Vertex → Option β} {t : RoseTree Vertex}
    {p : TreePath} {b : β} :
    (p, b) ∈ positions f t ↔ ∃ s, subtreeAt t p.toList = some s ∧ f s.value = some b := by
  simp only [positions, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq, Prod.exists,
    mem_positionedSubtrees]
  exact ⟨fun ⟨_, s, hs, _, hb, rfl, rfl⟩ ↦ ⟨s, hs, hb⟩,
    fun ⟨s, hs, hb⟩ ↦ ⟨p, s, hs, b, hb, rfl, rfl⟩⟩

/-- The pronounced copies, left to right. -/
def tokenList : RoseTree Vertex → List (TreePath × LIToken) :=
  positions (Sum.elim id fun _ ↦ none)

/-- The deleted copies, left to right. -/
def traceList : RoseTree Vertex → List (TreePath × LIToken) :=
  positions (Sum.elim (fun _ ↦ none) id)

variable (t : PlanarSyntacticObject) (tok : LIToken)

/-- The positions of the pronounced copies of `tok`. -/
def occurrences : List TreePath :=
  (tokenList t.val).filterMap fun x ↦ if x.2 = tok then some x.1 else none

/-- The positions of the deleted copies of `tok`. -/
def traces : List TreePath :=
  (traceList t.val).filterMap fun x ↦ if x.2 = tok then some x.1 else none

/-- The chain of `tok` lists the positions of its copies, pronounced or deleted, left to right. -/
def chain : List TreePath :=
  (positions (Sum.elim id id) t.val).filterMap fun x ↦ if x.2 = tok then some x.1 else none

/-- `tok` moves when it has a deleted copy. -/
def Moves : Prop := traces t tok ≠ []

instance : Decidable (Moves t tok) := inferInstanceAs (Decidable (_ ≠ _))

/-- `tok` is shared, dominated by two mothers, when it has two pronounced copies. -/
def IsShared : Prop := 2 ≤ (occurrences t tok).length

instance : Decidable (IsShared t tok) := inferInstanceAs (Decidable (_ ≤ _))

/-! ### The phrase a copy stands for -/

/-- The maximal projection of the copy at `p` is the highest position reached from `p` by
climbing while the position is the head daughter of its mother. -/
def projectionAt (p : TreePath) : TreePath :=
  maximalProjectionAt (fun q ↦ (subtreeAt t.val q.toList).bind headIndex?) p

theorem projectionAt_le (p : TreePath) : projectionAt t p ≤ p := maximalProjectionAt_le _ p

/-- A deleted copy has an antecedent when the projection of a pronounced copy of its token
c-commands it. -/
def HasAntecedent (x : TreePath × LIToken) : Prop :=
  ∃ p ∈ occurrences t x.2, CCommands t.val (projectionAt t p) x.1

instance (x : TreePath × LIToken) : Decidable (HasAntecedent t x) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The deleted copies without antecedents. -/
def orphanTraces : List (TreePath × LIToken) := (traceList t.val).filter (¬ HasAntecedent t ·)

/-! ### Links -/

/-- The copy at `p` is linked to the copy at `q` below it when its projection c-commands `q` and
the projection of no other copy of `tok` lies between them. -/
def IsLink (p q : TreePath) : Prop :=
  CCommands t.val (projectionAt t p) q ∧
    ∀ r ∈ chain t tok, CCommands t.val (projectionAt t p) (projectionAt t r) →
      ¬ CCommands t.val (projectionAt t r) q

instance (p q : TreePath) : Decidable (IsLink t tok p q) := inferInstanceAs (Decidable (_ ∧ _))

/-- The links of the chain of `tok` pair each copy with the projection of the copy linked to it. -/
def links : List (TreePath × TreePath) :=
  (chain t tok).flatMap fun q ↦
    ((chain t tok).filter fun p ↦ IsLink t tok p q).map fun p ↦ (projectionAt t p, q)

/-- The top of the chain of `tok` consists of the copies no copy's projection c-commands, where it
takes scope. -/
def chainTop : List TreePath :=
  (chain t tok).filter fun q ↦ (chain t tok).all fun p ↦ ¬ CCommands t.val (projectionAt t p) q

theorem not_isLink_self (p : TreePath) : ¬ IsLink t tok p p :=
  fun h ↦ h.1.2.1 (projectionAt_le t p)

/-- A token with at most one copy has no link. -/
theorem links_eq_nil_of_length_le_one (h : (chain t tok).length ≤ 1) : links t tok = [] := by
  simp only [links, List.flatMap_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff,
    decide_eq_true_eq]
  intro q hq p hp
  obtain rfl : p = q := by
    rcases hc : chain t tok with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [hc] at hp
    · simp only [hc, List.mem_singleton] at hp hq
      rw [hp, hq]
    · simp [hc] at h
  exact not_isLink_self t tok p


/-! ### Locality -/

/-- The interior of the phase headed at `h` is the set of positions the head c-commands. -/
def interior (h : TreePath) : Set TreePath := {q | CCommands t.val h q}

instance (h q : TreePath) : Decidable (q ∈ interior t h) :=
  inferInstanceAs (Decidable (CCommands _ _ _))

/-- The interior positions of a phase head occurring only at `a` carry the terms within its
complement. -/
theorem withinComplement_iff_exists_mem_interior {t : PlanarSyntacticObject} {ℓ : LIToken}
    {a : t.val.Positions} {x : SyntacticObject}
    (hu : ∀ q, t.termAt q = SyntacticObject.leaf ℓ ↔ q = a)
    (hph : (t : SyntacticObject).IsPhaseHead ℓ) :
    (t : SyntacticObject).WithinComplement ℓ x ↔ ∃ q : t.val.Positions, ↑q ∈ interior t a ∧
      t.termAt q = x := by
  have ha : t.termAt a = SyntacticObject.leaf ℓ := (hu a).2 rfl
  have hu' : ∀ q, t.termAt q = t.termAt a → q = a := fun q hq ↦ (hu q).1 (hq.trans ha)
  obtain ⟨m₀, hm₀, hℓ, hm₀ℓ⟩ := hph
  rw [← mem_phaseInterior, phaseInterior_eq_domainIn fun m hm hmℓ ↦ ?_, mem_domainIn, ← ha]
  · exact PlanarSyntacticObject.cCommandsIn_termAt_iff hu'
  · rw [PlanarSyntacticObject.eq_termAt_pred_of_immediatelyContains hu' hm (by rwa [ha]),
      ← PlanarSyntacticObject.eq_termAt_pred_of_immediatelyContains hu' hm₀ (by rwa [ha])]
    exact hℓ

/-- A link of the chain of `tok` leaves the phase headed at `h` when it runs from the interior to
a position outside the head's maximal projection; the Phase Impenetrability Condition forbids it,
and a link to the edge does not leave. -/
def Crosses (h : TreePath) : Prop :=
  ∃ x ∈ links t tok, x.2 ∈ interior t h ∧ ¬ projectionAt t h ≤ x.1

instance (h : TreePath) : Decidable (Crosses t tok h) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- A link of the chain of `tok` leaves the domain at `D` when it runs from inside `D` to outside,
as movement out of an island does. -/
def Escapes (D : TreePath) : Prop := ∃ x ∈ links t tok, D ≤ x.2 ∧ ¬ D ≤ x.1

instance (D : TreePath) : Decidable (Escapes t tok D) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

theorem not_crosses_of_length_le_one (h : (chain t tok).length ≤ 1) (hd : TreePath) :
    ¬ Crosses t tok hd := by
  simp [Crosses, links_eq_nil_of_length_le_one t tok h]

theorem not_escapes_of_length_le_one (h : (chain t tok).length ≤ 1) (D : TreePath) :
    ¬ Escapes t tok D := by
  simp [Escapes, links_eq_nil_of_length_le_one t tok h]

end Minimalist
