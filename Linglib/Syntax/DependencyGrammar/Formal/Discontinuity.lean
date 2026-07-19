import Linglib.Syntax.DependencyGrammar.Formal.Catena
import Linglib.Syntax.DependencyGrammar.Formal.NonProjective
import Linglib.Syntax.DependencyGrammar.LongDistance

open Morphology (Word)

/-!
# Discontinuities as risen catenae
[osborne-2019] [osborne-gross-2012]

A **risen catena** ([osborne-2019], Ch 7 §7.10) is a catena whose string
yield is not contiguous: the catena is connected in the dependency graph but
intervening words separate it in linear order. Osborne treats every
discontinuity (wh-fronting, topicalization, scrambling, extraposition, right
dislocation) as a risen catena, replacing the movement transformations of
phrase-structure grammar with a single tree-level predicate.

## Main definitions

* `DiscontinuityType` — Osborne's Ch 8 taxonomy (five constructions).
* `DisplacementDir` — rising vs. lowering displacement.
* `isContiguous`, `isRisenCatena` — predicates over node lists.
* `classifyDisplacement`, `displacementDir` — direction lookups.
* Example trees `whFrontingTree`, `topicalizationTree`, `scramblingTree`,
  `extrapositionTree`, `rightDislocationTree`.

## Main theorems

* `whFronting_risen_catena`, `topicalization_risen_catena`,
  `scrambling_risen_catena`, `extraposition_risen_catena`,
  `rightDislocation_risen_catena` — each example tree carries a risen
  catena over the indicated node pair.

## Implementation notes

* `isContiguous` and `isRisenCatena` return `Bool` to match the substrate-wide
  `Catena.isCatena` convention; a project-level `Bool → Prop` migration would
  refactor `Catena.lean` first.
* `isContiguous` delegates to `isInterval` after `insertionSort` so kernel
  `decide` proofs reduce; see `Syntax/DependencyGrammar/Projection.lean`.
-/

namespace DepGrammar.Discontinuity


open DepGrammar

/-! ### Discontinuity classification -/

/-- Discontinuity types ([osborne-2019], Ch 8 Table 19). -/
inductive DiscontinuityType where
  | whFronting        -- "Which song do you like?"
  | topicalization    -- "That song, you don't like"
  | npInternalFront   -- "too difficult (of) a problem"
  | scrambling        -- German: "dass uns Maria etwas gebacken hat"
  | extraposition     -- "The idea arose to try again"
  deriving Repr, DecidableEq

/-- Direction of displacement relative to canonical position. Wh-fronting,
    topicalization, NP-internal fronting, and scrambling displace leftward;
    extraposition displaces rightward. -/
inductive DisplacementDir where
  | rising    -- displaced leftward (precedes governor)
  | lowering  -- displaced rightward (follows governor)
  deriving Repr, DecidableEq

/-- Classify a discontinuity type by its displacement direction. Scrambling
    can go either direction; the canonical case is leftward. -/
def displacementDir : DiscontinuityType → DisplacementDir
  | .whFronting       => .rising
  | .topicalization   => .rising
  | .npInternalFront  => .rising
  | .scrambling       => .rising
  | .extraposition    => .lowering

/-! ### Risen catenae -/

/-- A list of node indices is contiguous iff its sorted form is an interval.
    Uses `insertionSort` (not `mergeSort`) so downstream `decide` proofs
    reduce in the kernel. -/
def isContiguous (nodes : List Nat) : Bool :=
  isInterval (nodes.insertionSort (· ≤ ·))

/-- A **risen catena** ([osborne-2019], Ch 7 §7.10) is a catena whose
    string yield is not contiguous — connected in the dependency tree but
    separated in linear order by intervening material. -/
def isRisenCatena (t : DepTree) (nodes : List Nat) : Bool :=
  Catena.isCatena t.deps nodes && !isContiguous nodes

/-- Classify a dependency as rising or lowering by whether the dependent
    precedes or follows its head in linear order. -/
def classifyDisplacement (d : Dependency) : DisplacementDir :=
  if d.depIdx < d.headIdx then .rising else .lowering

/-! ### Example trees from [osborne-2019] Ch 8 -/

/-- **Wh-fronting**: "What did you eat?". The catena `{what(0), eat(3)}` is
    risen — connected via `obj` but `did(1), you(2)` intervene. -/
def whFrontingTree : DepTree :=
  { words := [ { form :="what", cat := .PRON, features := { pronType := some .Int }}, Word.mk' "did" .AUX
             , Word.mk' "you" .PRON, Word.mk' "eat" .VERB ]
    deps := [⟨3, 2, .nsubj⟩, ⟨3, 0, .obj⟩, ⟨3, 1, .aux⟩]
    rootIdx := 3 }

/-- The displaced dependency in `whFrontingTree`: `eat(3) → what(0)`. -/
def whFrontingArc : Dependency := ⟨3, 0, .obj⟩

/-- **Topicalization**: "Those ideas I do accept". The catena
    `{ideas(1), accept(4)}` is risen — connected via `obj` but `I(2), do(3)`
    intervene. -/
def topicalizationTree : DepTree :=
  { words := [ Word.mk' "those" .DET, Word.mk' "ideas" .NOUN
             , Word.mk' "I" .PRON, Word.mk' "do" .AUX
             , Word.mk' "accept" .VERB ]
    deps := [ ⟨4, 2, .nsubj⟩, ⟨4, 3, .aux⟩
            , ⟨4, 1, .obj⟩, ⟨1, 0, .det⟩ ]
    rootIdx := 4 }

/-- The displaced dependency in `topicalizationTree`: `accept(4) → ideas(1)`. -/
def topicalizationArc : Dependency := ⟨4, 1, .obj⟩

/-- **Scrambling** (German): "dass uns Maria etwas gebacken hat". The catena
    `{uns(1), gebacken(4)}` is risen — `uns` is scrambled past the subject. -/
def scramblingTree : DepTree :=
  { words := [ Word.mk' "dass" .SCONJ, Word.mk' "uns" .PRON
             , Word.mk' "Maria" .PROPN, Word.mk' "etwas" .PRON
             , Word.mk' "gebacken" .VERB, Word.mk' "hat" .AUX ]
    deps := [ ⟨0, 5, .dep⟩, ⟨5, 4, .xcomp⟩
            , ⟨4, 2, .nsubj⟩, ⟨4, 3, .obj⟩, ⟨4, 1, .iobj⟩ ]
    rootIdx := 0 }

/-- **Extraposition**: "The idea arose to try again". The catena
    `{idea(1), try(4)}` is risen — `arose(2), to(3)` intervene. Lowering. -/
def extrapositionTree : DepTree :=
  { words := [ Word.mk' "the" .DET, Word.mk' "idea" .NOUN
             , Word.mk' "arose" .VERB, Word.mk' "to" .PART
             , Word.mk' "try" .VERB, Word.mk' "again" .ADV ]
    deps := [ ⟨2, 1, .nsubj⟩, ⟨1, 0, .det⟩
            , ⟨1, 4, .acl⟩, ⟨4, 3, .mark⟩, ⟨4, 5, .advmod⟩ ]
    rootIdx := 2 }

/-- The displaced dependency in `extrapositionTree`: `idea(1) → try(4)`. -/
def extrapositionArc : Dependency := ⟨1, 4, .acl⟩

/-- **Right dislocation**: "He's nice, that boy". The catena
    `{nice(2), boy(4)}` is risen — `that(3)` intervenes. -/
def rightDislocationTree : DepTree :=
  { words := [ Word.mk' "he" .PRON, Word.mk' "is" .AUX
             , Word.mk' "nice" .ADJ, Word.mk' "that" .DET
             , Word.mk' "boy" .NOUN ]
    deps := [⟨2, 0, .nsubj⟩, ⟨2, 1, .cop⟩, ⟨2, 4, .dislocated⟩, ⟨4, 3, .det⟩]
    rootIdx := 2 }

/-! ### Risen-catena theorems

Each example tree carries a risen catena over the displaced-element / governor
pair: connected via the dependency edge but yielding non-contiguously. -/

theorem whFronting_risen_catena :
    isRisenCatena whFrontingTree [0, 3] = true := by decide

theorem topicalization_risen_catena :
    isRisenCatena topicalizationTree [1, 4] = true := by decide

theorem scrambling_risen_catena :
    isRisenCatena scramblingTree [1, 4] = true := by decide

theorem extraposition_risen_catena :
    isRisenCatena extrapositionTree [1, 4] = true := by decide

theorem rightDislocation_risen_catena :
    isRisenCatena rightDislocationTree [2, 4] = true := by decide

/-! ### Displacement direction -/

theorem whFronting_is_rising :
    classifyDisplacement whFrontingArc = .rising := by decide

theorem topicalization_is_rising :
    classifyDisplacement topicalizationArc = .rising := by decide

theorem extraposition_is_lowering :
    classifyDisplacement extrapositionArc = .lowering := by decide

end DepGrammar.Discontinuity
