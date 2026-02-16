import Linglib.Theories.Syntax.DependencyGrammar.Formal.Catena
import Linglib.Theories.Syntax.DependencyGrammar.Core.Basic

/-!
# Ellipsis as Catena-Targeting

Formalizes Osborne's (2019, Ch 12–13) thesis: ellipsis targets catenae, not
constituents. This is the primary empirical motivation for the catena concept —
it explains why VP ellipsis, gapping, pseudogapping, sluicing, stripping, and
fragment answers all elide connected-but-not-necessarily-complete-subtree material.

## Key Insight

In DG, the "VP" is NOT a complete subtree (constituent) because the verb's
subject is also its dependent. This means even VP ellipsis targets a catena,
not a constituent — making catenae essential.

## Bridges

- → `Catena.lean`: uses `isCatena`, `isConstituent` for proofs

## References

- Osborne, T. (2019). *A Dependency Grammar of English*, Ch 12–13.
  Amsterdam: John Benjamins.
- Osborne, T., Putnam, M. & Groß, T. (2012). Catenae: Introducing a novel
  unit of syntactic analysis. *Syntax* 15(4):354–396.
-/

namespace DepGrammar.Ellipsis

open DepGrammar Catena

-- ============================================================================
-- §1: Ellipsis Type Taxonomy
-- ============================================================================

/-- Ellipsis types in English (Osborne 2019, Ch 12–13). -/
inductive EllipsisType where
  | vpEllipsis       -- "She will help, and he will _ too"
  | gapping          -- "Fred eats beans and Jim _ rice"
  | pseudogapping    -- "She has helped him, and he has _ her too"
  | stripping        -- "Fred likes salad, and Jim _ too"
  | sluicing         -- "She helped someone, but I don't know who _"
  | fragmentAnswer   -- "Who helped him? — She."
  deriving Repr, DecidableEq

-- ============================================================================
-- §2: Example Trees with Elided Catenae
-- ============================================================================

/-- **VP Ellipsis**: "She will cook dinner, and he will too"
    Pre-ellipsis second clause: cook(0) → he(1:nsubj), will(2:aux), dinner(3:obj).
    Elided = {0, 3} (cook + dinner): connected via obj → **catena**.
    Subtree of cook = {0,1,2,3} ≠ {0,3} → **NOT constituent**.
    Osborne (2019, Ch 12). -/
def vpEllipsisTree : DepTree :=
  { words := [ Word.mk' "cook" .VERB, Word.mk' "he" .PRON
             , Word.mk' "will" .AUX, Word.mk' "dinner" .NOUN ]
    deps := [⟨0, 1, .nsubj⟩, ⟨0, 2, .aux⟩, ⟨0, 3, .obj⟩]
    rootIdx := 0 }

/-- Elided nodes in VP ellipsis: {cook, dinner} = {0, 3}. -/
def vpEllipsisElided : List Nat := [0, 3]

/-- **Gapping**: "Fred eats beans and Jim rice"
    Pre-ellipsis second clause: eats(0) → Jim(1:nsubj), rice(2:obj).
    Elided = {0} (eats only): singleton → **catena**.
    Subtree of eats = {0,1,2} ≠ {0} → **NOT constituent**.
    Osborne (2019, Ch 12). -/
def gappingTree : DepTree :=
  { words := [ Word.mk' "eats" .VERB, Word.mk' "Jim" .PROPN
             , Word.mk' "rice" .NOUN ]
    deps := [⟨0, 1, .nsubj⟩, ⟨0, 2, .obj⟩]
    rootIdx := 0 }

/-- Elided nodes in gapping: {eats} = {0}. -/
def gappingElided : List Nat := [0]

/-- **Pseudogapping**: "She has helped him, and he has her too"
    Pre-ellipsis: helped(0) → he(1:nsubj), has(2:aux), her(3:obj), too(4:advmod).
    Elided = {0} (helped only): singleton → **catena**, **NOT constituent**.
    Osborne (2019, Ch 12). -/
def pseudogappingTree : DepTree :=
  { words := [ Word.mk' "helped" .VERB, Word.mk' "he" .PRON
             , Word.mk' "has" .AUX, Word.mk' "her" .PRON
             , Word.mk' "too" .ADV ]
    deps := [⟨0, 1, .nsubj⟩, ⟨0, 2, .aux⟩, ⟨0, 3, .obj⟩, ⟨0, 4, .advmod⟩]
    rootIdx := 0 }

/-- Elided nodes in pseudogapping: {helped} = {0}. -/
def pseudogappingElided : List Nat := [0]

/-- **Sluicing**: "She helped someone, but I don't know who"
    Embedded clause (pre-ellipsis): helped(0) → she(1:nsubj), someone(2:obj).
    Elided = {0, 1} (helped + she): connected via nsubj → **catena**.
    Subtree of helped = {0,1,2} ≠ {0,1} → **NOT constituent**.
    Osborne (2019, Ch 13). -/
def sluicingTree : DepTree :=
  { words := [ Word.mk' "helped" .VERB, Word.mk' "she" .PRON
             , Word.mk' "someone" .PRON ]
    deps := [⟨0, 1, .nsubj⟩, ⟨0, 2, .obj⟩]
    rootIdx := 0 }

/-- Elided nodes in sluicing: {helped, she} = {0, 1}. -/
def sluicingElided : List Nat := [0, 1]

/-- **Fragment answer**: "Who helped? — Him."
    Full answer: helped(0) → him(1:obj).
    Elided = {0} (helped): singleton → **catena**, **NOT constituent**.
    Osborne (2019, Ch 13). -/
def fragmentTree : DepTree :=
  { words := [ Word.mk' "helped" .VERB, Word.mk' "him" .PRON ]
    deps := [⟨0, 1, .obj⟩]
    rootIdx := 0 }

/-- Elided nodes in fragment answer: {helped} = {0}. -/
def fragmentElided : List Nat := [0]

-- ============================================================================
-- §3: Catena-Not-Constituent Proofs
-- ============================================================================

-- VP Ellipsis: {cook, dinner} is catena but not constituent

/-- VP ellipsis elided material is a catena. -/
theorem vpEllipsis_elided_is_catena :
    isCatena vpEllipsisTree.deps vpEllipsisElided = true := by native_decide

/-- VP ellipsis elided material is NOT a constituent (not a complete subtree). -/
theorem vpEllipsis_elided_not_constituent :
    isConstituent vpEllipsisTree.deps 4 vpEllipsisElided = false := by native_decide

-- Gapping: {eats} is catena (trivially) but not constituent

/-- Gapping elided material is a catena. -/
theorem gapping_elided_is_catena :
    isCatena gappingTree.deps gappingElided = true := by native_decide

/-- Gapping elided material is NOT a constituent. -/
theorem gapping_elided_not_constituent :
    isConstituent gappingTree.deps 3 gappingElided = false := by native_decide

-- Pseudogapping: {helped} is catena but not constituent

/-- Pseudogapping elided material is a catena. -/
theorem pseudogapping_elided_is_catena :
    isCatena pseudogappingTree.deps pseudogappingElided = true := by native_decide

/-- Pseudogapping elided material is NOT a constituent. -/
theorem pseudogapping_elided_not_constituent :
    isConstituent pseudogappingTree.deps 5 pseudogappingElided = false := by native_decide

-- Sluicing: {helped, she} is catena but not constituent

/-- Sluicing elided material is a catena. -/
theorem sluicing_elided_is_catena :
    isCatena sluicingTree.deps sluicingElided = true := by native_decide

/-- Sluicing elided material is NOT a constituent. -/
theorem sluicing_elided_not_constituent :
    isConstituent sluicingTree.deps 3 sluicingElided = false := by native_decide

-- Fragment answer: {helped} is catena but not constituent

/-- Fragment answer elided material is a catena. -/
theorem fragment_elided_is_catena :
    isCatena fragmentTree.deps fragmentElided = true := by native_decide

/-- Fragment answer elided material is NOT a constituent. -/
theorem fragment_elided_not_constituent :
    isConstituent fragmentTree.deps 2 fragmentElided = false := by native_decide

-- ============================================================================
-- §4: Osborne's Generalization
-- ============================================================================

/-- Osborne (2019, Ch 12): All five types of ellipsis target catenae.
    Verified for all example trees. -/
theorem all_ellipsis_targets_catenae :
    isCatena vpEllipsisTree.deps vpEllipsisElided = true ∧
    isCatena gappingTree.deps gappingElided = true ∧
    isCatena pseudogappingTree.deps pseudogappingElided = true ∧
    isCatena sluicingTree.deps sluicingElided = true ∧
    isCatena fragmentTree.deps fragmentElided = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- Osborne (2019, Ch 12): ALL five ellipsis types target non-constituent
    catenae. This is the empirical advantage of catenae over constituents:
    a constituent-based theory cannot capture these ellipsis patterns. -/
theorem all_ellipsis_not_constituent :
    isConstituent vpEllipsisTree.deps 4 vpEllipsisElided = false ∧
    isConstituent gappingTree.deps 3 gappingElided = false ∧
    isConstituent pseudogappingTree.deps 5 pseudogappingElided = false ∧
    isConstituent sluicingTree.deps 3 sluicingElided = false ∧
    isConstituent fragmentTree.deps 2 fragmentElided = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end DepGrammar.Ellipsis
