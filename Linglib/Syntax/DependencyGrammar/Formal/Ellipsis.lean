import Linglib.Syntax.DependencyGrammar.Formal.Catena

open Morphology (Word)

/-!
# Ellipsis as catena-targeting

[osborne-2019]'s central thesis: VP ellipsis, gapping, pseudogapping,
sluicing, stripping, and fragment answers all elide a **catena** (connected
in the dependency graph) that is not in general a **constituent** (the
projection of any single node). The structural reason is that in a flat DG
analysis the verb's projection always includes its subject, so even ordinary
VP ellipsis already removes a non-projection set of words.

## Main declarations

* `EllipsisType` — the six English ellipsis types Osborne classifies as
  catena-targeting.
* `gappingTree`, `gappingElided` — the worked Osborne example "Fred eats
  beans and Jim rice"; consumed by `Studies/Osborne2019Ellipsis.lean` to
  bridge to the phenomenon-level gapping taxonomy.
* `gapping_elided_is_catena`, `gapping_elided_not_constituent` — the
  catena-not-constituent divergence for that example.

## Implementation notes

* The per-paper trees for the other five ellipsis types and the paper-level
  aggregate theorems live in the corresponding `Studies/` file rather than
  the substrate, per the project's anchoring rule that single-paper
  empirical replication does not belong in the framework layer.
* Predicate-shape definitions (`isCatena`, `isConstituent`) inherit the
  substrate-wide `Bool` convention; statements are `... = true` / `= false`.
-/

namespace DepGrammar.Ellipsis


open DepGrammar Catena

/-! ### Ellipsis type taxonomy -/

/-- Ellipsis types in English ([osborne-2019], Ch. 12–13). -/
inductive EllipsisType where
  | vpEllipsis
  | gapping
  | pseudogapping
  | stripping
  | sluicing
  | fragmentAnswer
  deriving Repr, DecidableEq

/-! ### Worked example: gapping -/

/-- DG tree for the pre-ellipsis second clause of "Fred eats beans and Jim
    eats rice": `eats(0)` heads `Jim(1)` (nsubj) and `rice(2)` (obj). -/
def gappingTree : DepTree :=
  { words := [Word.mk' "eats" .VERB, Word.mk' "Jim" .PROPN, Word.mk' "rice" .NOUN]
    deps := [⟨0, 1, .nsubj⟩, ⟨0, 2, .obj⟩]
    rootIdx := 0 }

/-- Gapping elides the verb alone: `{eats} = {0}`. -/
def gappingElided : List Nat := [0]

/-- The elided material in gapping is a catena (a singleton is trivially
    connected). -/
theorem gapping_elided_is_catena :
    isCatena gappingTree.deps gappingElided = true := by decide

/-- The elided material in gapping is not a constituent: the verb's
    projection also contains its subject and object. -/
theorem gapping_elided_not_constituent :
    isConstituent gappingTree.deps 3 gappingElided = false := by decide

end DepGrammar.Ellipsis
