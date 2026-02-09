import Linglib.Theories.DependencyGrammar.Formal.NonProjective
import Linglib.Theories.DependencyGrammar.Formal.Catena
import Linglib.Theories.DependencyGrammar.Phenomena.LongDistance

/-!
# Discontinuities as Risen Catenae

Formalizes Osborne's (2019, Ch 7–8) analysis of discontinuities in dependency
grammar. The central concept is the **risen catena**: a catena that takes on a
word as its head that is not its governor, producing a non-contiguous yield.

## Core Concepts

A **catena** (Osborne et al. 2012) is a connected subgraph of a dependency tree.
When a dependent is displaced from its canonical position (e.g., by topicalization,
wh-fronting, or extraposition), the displaced element and its governor still form
a catena — they are connected in the tree — but their string yield is no longer
contiguous: other words intervene. This catena is a **risen catena**.

The **rising catena** (Osborne 2019, Ch 9 §9.2) is the minimal catena that
includes the root of the risen catena and the governor of the risen catena.
Every discontinuity has a rising catena.

**The Rising Principle** (Osborne 2019, Ch 7 §7.12): The head of the risen
catena must dominate the governor of the risen catena. This constrains which
discontinuities are possible.

## Discontinuity Types (Ch 8)

Osborne identifies five types:
- **Wh-fronting**: "Which song do you like?" — constituent rising
- **Topicalization**: "That song, you don't like" — constituent rising
- **NP-internal fronting**: "too difficult (of) a problem" — non-constituent rising
- **Scrambling**: German "dass uns Maria etwas gebacken hat" — constituent rising
- **Extraposition**: "The idea arose to try again" — constituent rising

Rising vs. lowering: wh-fronting, topicalization, and scrambling displace
leftward (rising); extraposition displaces rightward (lowering).

## Bridges

- → `Catena.lean`: risen catenae are catenae with non-contiguous yield
- → `NonProjective.lean`: arc-crossing non-projectivity is a stricter notion;
  risen catenae generalize it
- → `LongDistance.lean`: topicalization and wh-fronting map to `GapType.objGap`

## References

- Osborne, T. (2019). *A Dependency Grammar of English*, Ch 7–8.
  Amsterdam: John Benjamins.
- Osborne, T., Putnam, M. & Groß, T. (2012). Catenae: Introducing a novel
  unit of syntactic analysis. *Syntax* 15(4):354–396.
-/

namespace DepGrammar.Discontinuity

open DepGrammar

-- ============================================================================
-- §1: Discontinuity Classification
-- ============================================================================

/-- Discontinuity types (Osborne 2019, Ch 8, Table 19). -/
inductive DiscontinuityType where
  | whFronting        -- "Which song do you like?"
  | topicalization    -- "That song, you don't like"
  | npInternalFront   -- "too difficult (of) a problem"
  | scrambling        -- German: "dass uns Maria etwas gebacken hat"
  | extraposition     -- "The idea arose to try again"
  deriving Repr, DecidableEq

/-- Direction of displacement relative to canonical position.
    Osborne (2019, Ch 8 Table 19): wh-fronting, topicalization,
    NP-internal fronting, and scrambling displace leftward;
    extraposition displaces rightward. -/
inductive DisplacementDir where
  | rising    -- displaced leftward (precedes governor)
  | lowering  -- displaced rightward (follows governor)
  deriving Repr, DecidableEq

/-- Classify a discontinuity type by its displacement direction.
    Scrambling can go either direction, but the canonical case is leftward. -/
def displacementDir : DiscontinuityType → DisplacementDir
  | .whFronting       => .rising
  | .topicalization   => .rising
  | .npInternalFront  => .rising
  | .scrambling       => .rising
  | .extraposition    => .lowering

/-- Whether a discontinuity type involves constituent or non-constituent rising.
    Osborne (2019, Ch 7 §7.11): constituent rising = risen catena is a
    constituent; non-constituent rising = risen catena is not a constituent. -/
inductive RisingType where
  | constituent     -- Risen catena is a constituent
  | nonConstituent  -- Risen catena is not a constituent
  deriving Repr, DecidableEq

-- ============================================================================
-- §2: Risen Catenae
-- ============================================================================

/-- Check if a list of node indices is contiguous (no gaps in the sequence). -/
def isContiguous (nodes : List Nat) : Bool :=
  match nodes with
  | [] => true
  | _ =>
    let sorted := nodes.mergeSort (· ≤ ·)
    let min_ := sorted.head!
    let max_ := sorted.getLast!
    max_ - min_ + 1 == sorted.length

/-- A **risen catena** (Osborne 2019, Ch 7 §7.10) is a catena whose string yield
    is not contiguous — the catena is connected in the dependency tree but its
    words are separated by intervening material in linear order.

    This is the core formalization of Osborne's "discontinuity": when a
    dependent is displaced, it and its governor remain a catena, but the
    catena's yield is no longer contiguous. -/
def isRisenCatena (t : DepTree) (nodes : List Nat) : Bool :=
  Catena.isCatena t.deps nodes && !isContiguous nodes

/-- Classify a dependency as rising or lowering based on whether the
    dependent precedes or follows its head in linear order.
    Osborne (2019, Ch 8 Table 19). -/
def classifyDisplacement (d : Dependency) : DisplacementDir :=
  if d.depIdx < d.headIdx then .rising else .lowering

-- ============================================================================
-- §3: Example Trees — From Osborne (2019, Ch 7–8)
-- ============================================================================

/-- **Wh-fronting**: "What did you eat?" (Osborne 2019, Ch 8 §8.2)
    Words: what(0) did(1) you(2) eat(3)
    Deps: eat(3) → you(2:nsubj), eat(3) → what(0:obj), eat(3) → did(1:aux)

    Risen catena = {what(0)} — displaced to sentence-initial position.
    Rising catena = {what(0), did(1), you(2), eat(3)} — minimal catena from
    risen catena root to governor eat(3).
    The catena {what(0), eat(3)} has non-contiguous yield. -/
def whFrontingTree : DepTree :=
  { words := [ ⟨"what", .PRON, { wh := true }⟩, Word.mk' "did" .AUX
             , Word.mk' "you" .PRON, Word.mk' "eat" .VERB ]
    deps := [⟨3, 2, .nsubj⟩, ⟨3, 0, .obj⟩, ⟨3, 1, .aux⟩]
    rootIdx := 3 }

/-- The displaced dependency: eat(3) → what(0). -/
def whFrontingArc : Dependency := ⟨3, 0, .obj⟩

/-- **Topicalization**: "...but those ideas I do accept" (Osborne 2019, Ch 8 §8.3)
    Simplified to core: "Those ideas I do accept"
    Words: those(0) ideas(1) I(2) do(3) accept(4)
    Deps: accept(4) → I(2:nsubj), accept(4) → do(3:aux),
          accept(4) → ideas(1:obj), ideas(1) → those(0:det)

    Risen catena = {those(0), ideas(1)} — topicalized NP.
    Rising catena connects risen catena to governor accept(4).
    The catena {ideas(1), accept(4)} has non-contiguous yield. -/
def topicalizationTree : DepTree :=
  { words := [ Word.mk' "those" .DET, Word.mk' "ideas" .NOUN
             , Word.mk' "I" .PRON, Word.mk' "do" .AUX
             , Word.mk' "accept" .VERB ]
    deps := [ ⟨4, 2, .nsubj⟩, ⟨4, 3, .aux⟩
            , ⟨4, 1, .obj⟩, ⟨1, 0, .det⟩ ]
    rootIdx := 4 }

/-- The displaced dependency: accept(4) → ideas(1). -/
def topicalizationArc : Dependency := ⟨4, 1, .obj⟩

/-- **Scrambling** (German): "dass uns Maria etwas gebacken hat"
    (that us Maria something baked has)
    Words: dass(0) uns(1) Maria(2) etwas(3) gebacken(4) hat(5)
    Deps: dass(0) → hat(5:...), hat(5) → gebacken(4:xcomp),
          gebacken(4) → Maria(2:nsubj), gebacken(4) → etwas(3:obj),
          gebacken(4) → uns(1:iobj)

    Risen catena = {uns(1)} — scrambled to pre-subject position.
    The catena {uns(1), gebacken(4)} has non-contiguous yield.
    Osborne (2019, Ch 8 §8.5, example 33d variant). -/
def scramblingTree : DepTree :=
  { words := [ Word.mk' "dass" .SCONJ, Word.mk' "uns" .PRON
             , Word.mk' "Maria" .PROPN, Word.mk' "etwas" .PRON
             , Word.mk' "gebacken" .VERB, Word.mk' "hat" .AUX ]
    deps := [ ⟨0, 5, .dep⟩, ⟨5, 4, .xcomp⟩
            , ⟨4, 2, .nsubj⟩, ⟨4, 3, .obj⟩, ⟨4, 1, .iobj⟩ ]
    rootIdx := 0 }

/-- **Extraposition**: "The idea arose to try again" (Osborne 2019, Ch 8 §8.6)
    Words: the(0) idea(1) arose(2) to(3) try(4) again(5)
    Deps: arose(2) → idea(1:nsubj), idea(1) → the(0:det),
          idea(1) → try(4:acl), try(4) → to(3:mark), try(4) → again(5:advmod)

    Risen catena = {to(3), try(4), again(5)} — extraposed infinitival.
    The catena {idea(1), try(4)} has non-contiguous yield: arose(2), to(3)
    intervene. Lowering displacement. -/
def extrapositionTree : DepTree :=
  { words := [ Word.mk' "the" .DET, Word.mk' "idea" .NOUN
             , Word.mk' "arose" .VERB, Word.mk' "to" .PART
             , Word.mk' "try" .VERB, Word.mk' "again" .ADV ]
    deps := [ ⟨2, 1, .nsubj⟩, ⟨1, 0, .det⟩
            , ⟨1, 4, .acl⟩, ⟨4, 3, .mark⟩, ⟨4, 5, .advmod⟩ ]
    rootIdx := 2 }

/-- The displaced dependency: idea(1) → try(4). -/
def extrapositionArc : Dependency := ⟨1, 4, .acl⟩

/-- **Right dislocation**: "He's nice, that boy"
    Words: he(0) is(1) nice(2) that(3) boy(4)
    Deps: nice(2) → he(0:nsubj), nice(2) → is(1:cop),
          nice(2) → boy(4:dislocated), boy(4) → that(3:det)

    The catena {nice(2), boy(4)} — the predicate and its dislocated
    dependent — has non-contiguous yield (that(3) intervenes). -/
def rightDislocationTree : DepTree :=
  { words := [ Word.mk' "he" .PRON, Word.mk' "is" .AUX
             , Word.mk' "nice" .ADJ, Word.mk' "that" .DET
             , Word.mk' "boy" .NOUN ]
    deps := [⟨2, 0, .nsubj⟩, ⟨2, 1, .cop⟩, ⟨2, 4, .dislocated⟩, ⟨4, 3, .det⟩]
    rootIdx := 2 }

-- ============================================================================
-- §4: Risen Catena Proofs
-- ============================================================================

-- The CORE results: each example contains a risen catena — a catena whose
-- yield is non-contiguous. This is what Osborne means by "discontinuity".

/-- Wh-fronting: {what(0), eat(3)} is a risen catena — connected via obj
    but did(1), you(2) intervene in the yield. -/
theorem whFronting_risen_catena :
    isRisenCatena whFrontingTree [0, 3] = true := by native_decide

/-- Topicalization: {ideas(1), accept(4)} is a risen catena — connected
    via obj but I(2), do(3) intervene. -/
theorem topicalization_risen_catena :
    isRisenCatena topicalizationTree [1, 4] = true := by native_decide

/-- Scrambling: {uns(1), gebacken(4)} is a risen catena — connected via
    iobj but Maria(2), etwas(3) intervene. -/
theorem scrambling_risen_catena :
    isRisenCatena scramblingTree [1, 4] = true := by native_decide

/-- Extraposition: {idea(1), try(4)} is a risen catena — connected via acl
    but arose(2), to(3) intervene. -/
theorem extraposition_risen_catena :
    isRisenCatena extrapositionTree [1, 4] = true := by native_decide

/-- Right dislocation: {nice(2), boy(4)} is a risen catena — connected via
    dislocated dep but that(3) intervenes in the yield. -/
theorem rightDislocation_risen_catena :
    isRisenCatena rightDislocationTree [2, 4] = true := by native_decide

/-- Osborne (2019, Ch 8): all discontinuity types produce risen catenae. -/
theorem all_discontinuities_are_risen_catenae :
    isRisenCatena whFrontingTree [0, 3] = true ∧
    isRisenCatena topicalizationTree [1, 4] = true ∧
    isRisenCatena scramblingTree [1, 4] = true ∧
    isRisenCatena extrapositionTree [1, 4] = true ∧
    isRisenCatena rightDislocationTree [2, 4] = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

-- ============================================================================
-- §5: Displacement Direction
-- ============================================================================

/-- Wh-fronting is rising: what(0) precedes eat(3). -/
theorem whFronting_is_rising :
    classifyDisplacement whFrontingArc = .rising := by native_decide

/-- Topicalization is rising: ideas(1) precedes accept(4). -/
theorem topicalization_is_rising :
    classifyDisplacement topicalizationArc = .rising := by native_decide

/-- Extraposition is lowering: try(4) follows idea(1). -/
theorem extraposition_is_lowering :
    classifyDisplacement extrapositionArc = .lowering := by native_decide

/-- Rising discontinuities: wh-fronting, topicalization, NP-internal fronting,
    scrambling. (Osborne 2019, Ch 8 Table 19). -/
theorem rising_types :
    displacementDir .whFronting = .rising ∧
    displacementDir .topicalization = .rising ∧
    displacementDir .npInternalFront = .rising ∧
    displacementDir .scrambling = .rising := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Lowering discontinuity: extraposition. (Osborne 2019, Ch 8 Table 19). -/
theorem lowering_types :
    displacementDir .extraposition = .lowering := rfl

-- ============================================================================
-- §6: Bridges
-- ============================================================================

/-- **Bridge → Catena.lean**: all displaced element + governor pairs form catenae.
    The catena structure is what allows Osborne's analysis — even though the
    yield is non-contiguous, the syntactic connection remains. -/
theorem displaced_pairs_are_catenae :
    Catena.isCatena whFrontingTree.deps [0, 3] = true ∧
    Catena.isCatena topicalizationTree.deps [1, 4] = true ∧
    Catena.isCatena scramblingTree.deps [1, 4] = true ∧
    Catena.isCatena extrapositionTree.deps [1, 4] = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **Bridge → LongDistance.lean**: wh-fronting and topicalization involve
    object extraction, mapping to `GapType.objGap`. -/
theorem wh_fronting_is_obj_gap :
    LongDistance.gapToDepRel .objGap = .obj := rfl

/-- **Bridge → NonProjective.lean**: risen catenae generalize arc-crossing
    non-projectivity. The `nonProjectiveTree` from NonProjective.lean has arcs
    0→2 and 1→3 — these genuinely cross AND produce risen catenae. Osborne's
    single-clause examples produce risen catenae without crossing arcs. -/
theorem nonProjective_tree_also_risen :
    isRisenCatena nonProjectiveTree [0, 2] = true := by native_decide

end DepGrammar.Discontinuity
