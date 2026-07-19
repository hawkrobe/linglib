import Linglib.Syntax.DependencyGrammar.Formal.Catena
import Linglib.Syntax.DependencyGrammar.Formal.Discontinuity

open Morphology (Word)

/-!
# Islands as Constraints on Rising Catenae

Formalizes [osborne-2019]'s analysis of islands in dependency grammar:
islands are syntactic configurations that constrain which rising catenae can
form, limiting the reach of discontinuities. Each island example below
exhibits both (i) island material that is itself a catena and (ii) an
extraction that produces a risen catena with non-contiguous yield.

## Main declarations

* `OsborneIslandType` — eight island categories from [osborne-2019] Ch 9.
* `islandLeftBranch`, `islandSubject`, `islandAdjunct`, `islandWhIsland`,
  `islandSpecifiedNP` — minimal DG example trees, one per island type with
  a worked extraction.
* `*_NP_is_catena` / `*_clause_is_catena` — the island material is catena-shaped.
* `*_extraction_risen` — the extracted-plus-governor pair is a risen catena.

## Implementation notes

* Predicates inherit the substrate-wide `Bool` convention from
  `Catena.lean` / `Discontinuity.lean`; statements are `... = true`.
* The `OsborneIslandType` enum's three cases (adjunct, subject, whIsland) line
  up with the Ross-1967 inventory in `ConstraintType` (`Studies/Ross1967.lean`).

## Todo

* Consume the canonical Ross-1967 `ConstraintType` enum directly so
  `OsborneIslandType` becomes a refinement mapping onto it.
-/

namespace DepGrammar.Islands


open DepGrammar Catena Discontinuity

/-! ### Extended island taxonomy -/

/-- Island types from [osborne-2019], Ch 9. Each variant names the
construction whose extraction Osborne's rising-catena constraints rule out. -/
inductive OsborneIslandType where
  /-- §9.4: *"Whose do you like house?" -/
  | leftBranch
  /-- §9.6: ??"Who did you find those pictures of?" -/
  | specifiedNP
  /-- §9.7: *"Which car did the driver of ignore the light?" -/
  | subject
  /-- §9.8: *"What do they always argue before one of them cleans?" -/
  | adjunct
  /-- §9.9: *"Which judge might they inquire which performance surprised?" -/
  | whIsland
  /-- §9.10: *"That someone was there was a relief who I knew" -/
  | rightRoof
  /-- §9.3: *"Wem hast du mit gesprochen?" (German P-stranding) -/
  | pStranding
  /-- §9.5: pied-piping overcomes left branch islands -/
  | piedPiping
  deriving Repr, DecidableEq

/-! ### Island example trees

Each tree models a sentence where extraction from an island creates a risen
catena whose rising catena violates the corresponding island constraint. -/

/-- DG tree for the left-branch island *"Whose do you like house?". -/
def islandLeftBranch : DepTree :=
  { words := [ { form :="whose", cat := .DET, features := { pronType := some .Int }}, Word.mk' "do" .AUX
             , Word.mk' "you" .PRON, Word.mk' "like" .VERB
             , Word.mk' "house" .NOUN ]
    deps := [ ⟨1, 3, .ccomp⟩, ⟨1, 2, .nsubj⟩
            , ⟨3, 4, .obj⟩, ⟨4, 0, .det⟩ ]
    rootIdx := 1 }

/-- DG tree for the subject island *"Which car did the driver of ignore the light?"
([osborne-2019], §9.7, ex. 48). -/
def islandSubject : DepTree :=
  { words := [ { form :="which", cat := .DET, features := { pronType := some .Int }}, Word.mk' "car" .NOUN
             , Word.mk' "did" .AUX, Word.mk' "the" .DET
             , Word.mk' "driver" .NOUN, Word.mk' "of" .ADP
             , Word.mk' "ignore" .VERB, Word.mk' "the" .DET
             , Word.mk' "light" .NOUN ]
    deps := [ ⟨2, 6, .ccomp⟩, ⟨2, 4, .nsubj⟩
            , ⟨4, 3, .det⟩, ⟨4, 5, .nmod⟩
            , ⟨5, 1, .nmod⟩, ⟨1, 0, .det⟩
            , ⟨6, 8, .obj⟩, ⟨8, 7, .det⟩ ]
    rootIdx := 2 }

/-- DG tree for the adjunct island *"What do they argue before cleaning?"
([osborne-2019], §9.8, ex. 50b/59, simplified). -/
def islandAdjunct : DepTree :=
  { words := [ { form :="what", cat := .PRON, features := { pronType := some .Int }}, Word.mk' "do" .AUX
             , Word.mk' "they" .PRON, Word.mk' "argue" .VERB
             , Word.mk' "before" .SCONJ, Word.mk' "cleaning" .VERB ]
    deps := [ ⟨1, 3, .ccomp⟩, ⟨1, 2, .nsubj⟩
            , ⟨3, 5, .advcl⟩, ⟨5, 4, .mark⟩, ⟨5, 0, .obj⟩ ]
    rootIdx := 1 }

/-- DG tree for the wh-island *"Which judge might they inquire surprised?"
([osborne-2019], §9.9, ex. 61b', simplified). -/
def islandWhIsland : DepTree :=
  { words := [ { form :="which", cat := .DET, features := { pronType := some .Int }}, Word.mk' "judge" .NOUN
             , Word.mk' "might" .AUX, Word.mk' "they" .PRON
             , Word.mk' "inquire" .VERB, Word.mk' "surprised" .VERB ]
    deps := [ ⟨2, 4, .ccomp⟩, ⟨2, 3, .nsubj⟩
            , ⟨4, 5, .ccomp⟩
            , ⟨5, 1, .nsubj⟩, ⟨1, 0, .det⟩ ]
    rootIdx := 2 }

/-- DG tree for the specified-NP island ??"Who did you find those pictures of?"
([osborne-2019], §9.6, ex. 36b). -/
def islandSpecifiedNP : DepTree :=
  { words := [ { form :="who", cat := .PRON, features := { pronType := some .Int }}, Word.mk' "did" .AUX
             , Word.mk' "you" .PRON, Word.mk' "find" .VERB
             , Word.mk' "those" .DET, Word.mk' "pictures" .NOUN
             , Word.mk' "of" .ADP ]
    deps := [ ⟨1, 3, .ccomp⟩, ⟨1, 2, .nsubj⟩
            , ⟨3, 5, .obj⟩, ⟨5, 4, .det⟩
            , ⟨5, 6, .nmod⟩, ⟨6, 0, .nmod⟩ ]
    rootIdx := 1 }

/-! ### Island material is catena-shaped

Osborne's key insight: islands are syntactic contexts (catenae) that constrain
which rising catenae can form. The island material itself is connected. -/

theorem leftBranch_NP_is_catena :
    Catena.isCatena islandLeftBranch.deps [4] = true := by decide

theorem subject_NP_is_catena :
    Catena.isCatena islandSubject.deps [3, 4, 5] = true := by decide

theorem adjunct_clause_is_catena :
    Catena.isCatena islandAdjunct.deps [4, 5] = true := by decide

theorem whIsland_clause_is_catena :
    Catena.isCatena islandWhIsland.deps [5] = true := by decide

theorem specifiedNP_is_catena :
    Catena.isCatena islandSpecifiedNP.deps [4, 5, 6] = true := by decide

/-! ### Extraction creates risen catenae

When extraction reaches into an island, the extracted element and its
governor form a risen catena: connected in the tree but with non-contiguous
yield. The island constraint blocks the risen catena from being well-formed. -/

theorem leftBranch_extraction_risen :
    isRisenCatena islandLeftBranch [0, 4] = true := by decide

theorem subject_extraction_risen :
    isRisenCatena islandSubject [1, 5] = true := by decide

theorem adjunct_extraction_risen :
    isRisenCatena islandAdjunct [0, 5] = true := by decide

theorem whIsland_extraction_risen :
    isRisenCatena islandWhIsland [1, 5] = true := by decide

theorem specifiedNP_extraction_risen :
    isRisenCatena islandSpecifiedNP [0, 6] = true := by decide

end DepGrammar.Islands
