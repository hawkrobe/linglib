import Linglib.Phenomena.Syntax.DependencyGrammar.Formal.Discontinuity
import Linglib.Theories.Syntax.DependencyGrammar.Formal.Catena
import Linglib.Phenomena.Syntax.DependencyGrammar.LongDistance
import Linglib.Phenomena.Islands.Data

/-!
# Islands as Constraints on Rising Catenae

Formalizes Osborne's (2019, Ch 9) analysis of islands in dependency grammar.
Islands are syntactic configurations that constrain which rising catenae can
form — they limit the reach of discontinuities.

## Core Insight

In Osborne's framework, discontinuities are analyzed as **risen catenae** —
catenae with non-contiguous yield (see `Discontinuity.lean`). Islands are
constraints on the **rising catena** (the minimal catena connecting the risen
catena to its governor). Different island types constrain rising catenae in
different ways:

- **Left branch islands** (§9.4): The root of a risen catena may not be a
  determiner, attributive adjective, or degree adverb.
- **Subject islands** (§9.7): Rising catenae of wh-fronting reluctantly include
  the subject dependency.
- **Adjunct islands** (§9.8): Within a rising catena, an adjunct dependency
  may not dominate a finite verb.
- **Wh-islands** (§9.9): Wh-expressions are islands to wh-fronting only (not
  to topicalization or extraposition).
- **Specified NP islands** (§9.6): Rising catenae cannot easily reach into
  definite/specific NPs.
- **Right roof islands** (§9.10): Extraposition is clause-bound; a rising catena
  of extraposition may not contain more than one finite verb.

## Bridges

- → `Discontinuity.lean`: islands block the formation of risen catenae
- → `Catena.lean`: island material forms catenae (proven), uses `isCatena`
- → `LongDistance.lean`: maps to `IslandType` (4 shared types + 5 new)
- → `Phenomena/Islands/Data.lean`: maps to `ConstraintType` and connects to
  Hofmeister & Sag (2010) gradience data

## References

- Osborne, T. (2019). *A Dependency Grammar of English*, Ch 9.
  Amsterdam: John Benjamins.
- Ross, J.R. (1967). Constraints on Variables in Syntax.
- Huang, C.-T. J. (1982). Logical Relations in Chinese.
-/

namespace DepGrammar.Islands

open DepGrammar Catena Discontinuity

-- ============================================================================
-- §1: Extended Island Taxonomy
-- ============================================================================

/-- Island types (Osborne 2019, Ch 9). Each type constrains rising catenae
    in a different way. -/
inductive OsborneIslandType where
  | leftBranch      -- §9.4: *"Whose do you like house?"
  | specifiedNP     -- §9.6: ??"Who did you find those pictures of?"
  | subject         -- §9.7: *"Which car did the driver of ignore the light?"
  | adjunct         -- §9.8: *"What do they always argue before one of them cleans?"
  | whIsland        -- §9.9: *"Which judge might they inquire which performance surprised?"
  | rightRoof       -- §9.10: *"That someone was there was a relief who I knew"
  | pStranding      -- §9.3: *"Wem hast du mit gesprochen?" (German)
  | piedPiping      -- §9.5: pied-piping overcomes left branch islands
  deriving Repr, DecidableEq

-- ============================================================================
-- §2: Island Example Trees
-- ============================================================================

-- Each tree models a sentence where extraction from an island creates a
-- risen catena whose rising catena violates an island constraint.

/-- **Left branch island**: *"Whose do you like house?" (Osborne 2019, §9.4)
    Words: whose(0) do(1) you(2) like(3) house(4)
    Deps: do(1) → like(3:ccomp), do(1) → you(2:nsubj),
          like(3) → house(4:obj), house(4) → whose(0:det)

    Risen catena = {whose(0)} — determiner extracted from left branch.
    Rising catena = {whose(0), do(1), ..., house(4)}.
    The catena {whose(0), house(4)} has non-contiguous yield.
    Constraint: root of risen catena may NOT be a determiner. -/
def island_leftBranch : DepTree :=
  { words := [ ⟨"whose", .DET, { wh := true }⟩, Word.mk' "do" .AUX
             , Word.mk' "you" .PRON, Word.mk' "like" .VERB
             , Word.mk' "house" .NOUN ]
    deps := [ ⟨1, 3, .ccomp⟩, ⟨1, 2, .nsubj⟩
            , ⟨3, 4, .obj⟩, ⟨4, 0, .det⟩ ]
    rootIdx := 1 }

/-- **Subject island**: *"Which car did the driver of ignore the traffic light?"
    (Osborne 2019, §9.7, example 48)
    Simplified: "Which car did the driver of ignore the light?"
    Words: which(0) car(1) did(2) the(3) driver(4) of(5) ignore(6) the_(7) light(8)
    Deps: did(2) → ignore(6:ccomp), did(2) → driver(4:nsubj),
          driver(4) → the(3:det), driver(4) → of(5:nmod),
          of(5) → car(1:nmod), car(1) → which(0:det),
          ignore(6) → light(8:obj), light(8) → the_(7:det)

    Risen catena = {which(0), car(1)} — extracted from inside subject NP.
    The catena {car(1), of(5)} has non-contiguous yield (did, the, driver intervene).
    Constraint: rising catena reluctantly includes subject dependency. -/
def island_subject : DepTree :=
  { words := [ ⟨"which", .DET, { wh := true }⟩, Word.mk' "car" .NOUN
             , Word.mk' "did" .AUX, Word.mk' "the" .DET
             , Word.mk' "driver" .NOUN, Word.mk' "of" .ADP
             , Word.mk' "ignore" .VERB, Word.mk' "the" .DET
             , Word.mk' "light" .NOUN ]
    deps := [ ⟨2, 6, .ccomp⟩, ⟨2, 4, .nsubj⟩
            , ⟨4, 3, .det⟩, ⟨4, 5, .nmod⟩
            , ⟨5, 1, .nmod⟩, ⟨1, 0, .det⟩
            , ⟨6, 8, .obj⟩, ⟨8, 7, .det⟩ ]
    rootIdx := 2 }

/-- **Adjunct island**: *"What do they always argue before one of them cleans?"
    (Osborne 2019, §9.8, example 50b/59)
    Simplified: "What do they argue before cleaning?"
    Words: what(0) do(1) they(2) argue(3) before(4) cleaning(5)
    Deps: do(1) → argue(3:ccomp), do(1) → they(2:nsubj),
          argue(3) → cleaning(5:advcl), cleaning(5) → before(4:mark),
          cleaning(5) → what(0:obj)

    Risen catena = {what(0)} — extracted from inside adjunct clause.
    Rising catena contains adjunct dep (argue → cleaning:advcl).
    The catena {what(0), cleaning(5)} has non-contiguous yield.
    Constraint: within a rising catena, an adjunct dep may not dominate
    a finite verb. -/
def island_adjunct : DepTree :=
  { words := [ ⟨"what", .PRON, { wh := true }⟩, Word.mk' "do" .AUX
             , Word.mk' "they" .PRON, Word.mk' "argue" .VERB
             , Word.mk' "before" .SCONJ, Word.mk' "cleaning" .VERB ]
    deps := [ ⟨1, 3, .ccomp⟩, ⟨1, 2, .nsubj⟩
            , ⟨3, 5, .advcl⟩, ⟨5, 4, .mark⟩, ⟨5, 0, .obj⟩ ]
    rootIdx := 1 }

/-- **Wh-island**: *"Which judge might they inquire which performance surprised?"
    (Osborne 2019, §9.9, example 61b')
    Simplified: "Which judge might they inquire surprised?"
    Words: which(0) judge(1) might(2) they(3) inquire(4) surprised(5)
    Deps: might(2) → inquire(4:ccomp), might(2) → they(3:nsubj),
          inquire(4) → surprised(5:ccomp),
          surprised(5) → judge(1:nsubj), judge(1) → which(0:det)

    Risen catena = {which(0), judge(1)} — extracted from embedded wh-clause.
    The catena {judge(1), surprised(5)} has non-contiguous yield.
    Constraint: wh-expressions are islands to wh-fronting. -/
def island_whIsland : DepTree :=
  { words := [ ⟨"which", .DET, { wh := true }⟩, Word.mk' "judge" .NOUN
             , Word.mk' "might" .AUX, Word.mk' "they" .PRON
             , Word.mk' "inquire" .VERB, Word.mk' "surprised" .VERB ]
    deps := [ ⟨2, 4, .ccomp⟩, ⟨2, 3, .nsubj⟩
            , ⟨4, 5, .ccomp⟩
            , ⟨5, 1, .nsubj⟩, ⟨1, 0, .det⟩ ]
    rootIdx := 2 }

/-- **Specified NP island**: ??"Who did you find those pictures of?"
    (Osborne 2019, §9.6, example 36b)
    Words: who(0) did(1) you(2) find(3) those(4) pictures(5) of(6)
    Deps: did(1) → find(3:ccomp), did(1) → you(2:nsubj),
          find(3) → pictures(5:obj), pictures(5) → those(4:det),
          pictures(5) → of(6:nmod), of(6) → who(0:nmod)

    Risen catena = {who(0)} — extracted from inside definite NP.
    The catena {who(0), of(6)} has non-contiguous yield.
    Constraint: rising catenae cannot easily reach into specific NPs. -/
def island_specifiedNP : DepTree :=
  { words := [ ⟨"who", .PRON, { wh := true }⟩, Word.mk' "did" .AUX
             , Word.mk' "you" .PRON, Word.mk' "find" .VERB
             , Word.mk' "those" .DET, Word.mk' "pictures" .NOUN
             , Word.mk' "of" .ADP ]
    deps := [ ⟨1, 3, .ccomp⟩, ⟨1, 2, .nsubj⟩
            , ⟨3, 5, .obj⟩, ⟨5, 4, .det⟩
            , ⟨5, 6, .nmod⟩, ⟨6, 0, .nmod⟩ ]
    rootIdx := 1 }

-- ============================================================================
-- §3: Island Material as Catenae
-- ============================================================================

-- Osborne's key insight: islands are syntactic contexts (catenae) that
-- constrain which rising catenae can form. The island material itself is
-- a catena — a connected subgraph of the tree.

/-- The NP containing the left branch {house(4)} is a catena (trivially). -/
theorem leftBranch_NP_is_catena :
    Catena.isCatena island_leftBranch.deps [4] = true := by native_decide

/-- The subject NP {the(3), driver(4), of(5)} in the subject island is a catena. -/
theorem subject_NP_is_catena :
    Catena.isCatena island_subject.deps [3, 4, 5] = true := by native_decide

/-- The adjunct clause {before(4), cleaning(5)} is a catena. -/
theorem adjunct_clause_is_catena :
    Catena.isCatena island_adjunct.deps [4, 5] = true := by native_decide

/-- The embedded clause in the wh-island {surprised(5)} is a (trivial) catena. -/
theorem whIsland_clause_is_catena :
    Catena.isCatena island_whIsland.deps [5] = true := by native_decide

/-- The specified NP {those(4), pictures(5), of(6)} is a catena. -/
theorem specifiedNP_is_catena :
    Catena.isCatena island_specifiedNP.deps [4, 5, 6] = true := by native_decide

-- ============================================================================
-- §4: Extraction Creates Risen Catenae
-- ============================================================================

-- When extraction reaches into an island, the extracted element and its
-- governor form a risen catena: connected in the tree but with non-contiguous
-- yield. The island constraint blocks this risen catena from being well-formed.

/-- Left branch: {whose(0), house(4)} is a risen catena — connected via det
    but do(1), you(2), like(3) intervene. -/
theorem leftBranch_extraction_risen :
    isRisenCatena island_leftBranch [0, 4] = true := by native_decide

/-- Subject: {car(1), of(5)} is a risen catena — connected via nmod
    but did(2), the(3), driver(4) intervene. -/
theorem subject_extraction_risen :
    isRisenCatena island_subject [1, 5] = true := by native_decide

/-- Adjunct: {what(0), cleaning(5)} is a risen catena — connected via obj
    but do(1), they(2), argue(3), before(4) intervene. -/
theorem adjunct_extraction_risen :
    isRisenCatena island_adjunct [0, 5] = true := by native_decide

/-- Wh-island: {judge(1), surprised(5)} is a risen catena — connected via
    nsubj but might(2), they(3), inquire(4) intervene. -/
theorem whIsland_extraction_risen :
    isRisenCatena island_whIsland [1, 5] = true := by native_decide

/-- Specified NP: {who(0), of(6)} is a risen catena — connected via nmod
    but did(1)..pictures(5) intervene. -/
theorem specifiedNP_extraction_risen :
    isRisenCatena island_specifiedNP [0, 6] = true := by native_decide

/-- All island violations produce risen catenae: extraction from an island
    creates a catena with non-contiguous yield. -/
theorem all_island_extractions_risen :
    isRisenCatena island_leftBranch [0, 4] = true ∧
    isRisenCatena island_subject [1, 5] = true ∧
    isRisenCatena island_adjunct [0, 5] = true ∧
    isRisenCatena island_whIsland [1, 5] = true ∧
    isRisenCatena island_specifiedNP [0, 6] = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

-- ============================================================================
-- §5: Bridges
-- ============================================================================

/-- **Bridge → LongDistance.lean**: Map `OsborneIslandType` to existing
    `IslandType` for the 4 shared types. Osborne's taxonomy is more
    fine-grained, distinguishing types by their constraints on rising catenae. -/
def toLongDistanceIslandType :
    OsborneIslandType → Option LongDistance.IslandType
  | .adjunct    => some .adjunct
  | .subject    => some .subject
  | _           => none  -- leftBranch, specifiedNP, whIsland, rightRoof, pStranding, piedPiping are new

/-- **Bridge → Phenomena/Islands/Data.lean**: Map `OsborneIslandType` to
    `ConstraintType` for the shared types. -/
def toPhenomenaConstraintType :
    OsborneIslandType → Option ConstraintType
  | .adjunct       => some .adjunct
  | .subject       => some .subject
  | .whIsland      => some .embeddedQuestion
  | _              => none

/-- **Bridge → Discontinuity.lean**: islands constrain the formation of risen
    catenae. All island violation examples contain risen catenae (proven above),
    connecting the island constraint to Osborne's discontinuity theory. -/
theorem island_extractions_are_discontinuities :
    isRisenCatena island_leftBranch [0, 4] = true ∧
    isRisenCatena island_adjunct [0, 5] = true ∧
    isRisenCatena island_whIsland [1, 5] = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- **Bridge → Catena.lean**: all island material forms catenae. The island
    is a connected subgraph from which extraction is constrained. -/
theorem all_islands_are_catenae :
    Catena.isCatena island_leftBranch.deps [4] = true ∧
    Catena.isCatena island_subject.deps [3, 4, 5] = true ∧
    Catena.isCatena island_adjunct.deps [4, 5] = true ∧
    Catena.isCatena island_whIsland.deps [5] = true ∧
    Catena.isCatena island_specifiedNP.deps [4, 5, 6] = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end DepGrammar.Islands
