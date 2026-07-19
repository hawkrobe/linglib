import Linglib.Syntax.DependencyGrammar.Formal.Catena

open Morphology (Word)

/-!
# Finite-VP divergence: catena ⊋ constituent

The finite VP (verb + complements, excluding subject) is the textbook
demonstration of [osborne-2019]'s thesis that constituency and
connectedness come apart in dependency grammar: in a flat DG analysis, the
finite VP is a **catena** (connected in the dependency graph) but not a
**constituent** (the verb's complete subtree includes the subject). The
phrase-structure analysis groups verb and complements under a `VP` node,
so it predicts the opposite.

Five standard constituency tests for the finite VP (Osborne 2019, Ch. 2,
ex. 25) — topicalization, clefting, pseudoclefting, do-so substitution,
answer fragments — pattern with the DG prediction on four out of five
items, the proform-substitution case being the well-known exception.
Empirical writeups of those judgments live in paper-anchored Studies
files; this module formalizes only the structural DG-side claim.

## Main declarations

* `billPlaysChess`, `sheReadsEverything` — small DG example trees from
  Osborne 2019 Ch. 2.
* `vp_is_catena_*`, `vp_not_constituent_*` — the divergence theorems for
  each tree.
* `exists_catena_not_constituent` — the universal witness (any internal
  node forms a singleton catena that is not a constituent).

## Implementation notes

* Predicate-shape definitions (`isCatena`, `isConstituent`) inherit the
  substrate-wide `Bool` convention; statements are `... = true` / `= false`.
* No `PSTree` straw-man: phrase-structure analyses are formalized in the
  HPSG and Minimalism directories, not re-stipulated here. Genuine
  DG-vs-PSG rivalry theorems should branch off those formalizations
  rather than a hand-rolled `inductive PSTree`.
-/

namespace DepGrammar.VPDivergence


open DepGrammar DepGrammar.Catena

/-! ### Example trees from [osborne-2019] -/

/-- DG tree for "Bill plays chess" (Ch. 2, ex. 24):
    `plays(0)` heads `Bill(1)` (nsubj) and `chess(2)` (obj). -/
def billPlaysChess : DepTree :=
  { words := [Word.mk' "plays" .VERB, Word.mk' "Bill" .PROPN, Word.mk' "chess" .NOUN]
    deps := [⟨0, 1, .nsubj⟩, ⟨0, 2, .obj⟩]
    rootIdx := 0 }

/-- DG tree for "She reads everything" (Ch. 2, ex. 12): same shape as
    "Bill plays chess", confirming the divergence is structural. -/
def sheReadsEverything : DepTree :=
  { words := [Word.mk' "reads" .VERB, Word.mk' "She" .PRON, Word.mk' "everything" .PRON]
    deps := [⟨0, 1, .nsubj⟩, ⟨0, 2, .obj⟩]
    rootIdx := 0 }

/-! ### The finite-VP divergence

For each tree, the verb-plus-object set `{0, 2}` is connected in the
dependency graph (a catena) but is not the projection of any node (the
verb's projection includes the subject). -/

theorem vp_is_catena_billPlaysChess :
    isCatena billPlaysChess.deps [0, 2] = true := by decide

theorem vp_not_constituent_billPlaysChess :
    isConstituent billPlaysChess.deps 3 [0, 2] = false := by decide

theorem vp_is_catena_sheReadsEverything :
    isCatena sheReadsEverything.deps [0, 2] = true := by decide

theorem vp_not_constituent_sheReadsEverything :
    isConstituent sheReadsEverything.deps 3 [0, 2] = false := by decide

/-! ### Universal witness

The two-tree examples instantiate a general phenomenon: any internal node
forms a singleton catena that fails to be a constituent. -/

/-- For any tree with an edge `v → w` (`v ≠ w`), the singleton `[v]` is a
    catena but `projection deps v ≠ [v]` (the projection contains `w`). -/
theorem exists_catena_not_constituent
    (deps : List Dependency) (v w : Nat) (hvw : v ≠ w)
    (hedge : parentEdge deps v w) :
    isCatena deps [v] = true ∧ ¬ projection deps v = [v] := by
  refine ⟨singleton_isCatena deps v, ?_⟩
  intro heq
  have hw : w ∈ projection deps v := child_mem_projection deps v w hedge
  rw [heq] at hw
  simp at hw
  exact hvw hw.symm

end DepGrammar.VPDivergence
