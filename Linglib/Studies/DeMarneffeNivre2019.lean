import Linglib.Syntax.DependencyGrammar.LongDistance
import Linglib.Syntax.DependencyGrammar.Coordination

open Morphology (Word)

/-!
# de Marneffe & Nivre 2019: UD enhanced dependencies for English LD and coordination
[de-marneffe-nivre-2019]

Worked English examples illustrating Universal Dependencies' basic vs
enhanced representations (cf. §4.2 and Figure 9 of
[de-marneffe-nivre-2019]). The substrate — gap-filling
(`DepGrammar.LongDistance.fillGap`) and shared-dependent propagation
(`DepGrammar.Coordination.enhanceSharedDeps`) — lives in the corresponding
substrate files.

## Examples

### Long-distance dependencies

* `exWhatDidJohnSee`, `exWhoSawMary`, `exWhoDidJohnSee` — wh-question
  fixtures (object extraction, subject question, object with `who`).
* `exTheBookThatJohnRead` / `_enhanced` — object relative clause and its
  enhanced graph.
* `exJohnThinksThatMarySleeps`, `exJohnThinksMarySleeps`,
  `exJohnWondersIfMarySleeps`, `exJohnWondersWhatMarySaw` — complement
  clauses with and without overt complementizer, with and without
  embedded extraction.

### Coordination

* `exJohnAndMarySleep`, `exJohnSleepsAndMarySleeps` — NP and S coordination
  (no shared-dependent propagation needed).
* `exJohnSeesAndHearsMary` / `_enhanced` — VP coordination; the enhanced
  graph adds `obj` from `hears` to `Mary`.
* `exOldAndWiseMan` — adjective coordination.
* `exRNR` / `_enhanced` — Right Node Raising; the enhanced graph adds
  `obj` to the second-conjunct verb.

## Implementation notes

Fixtures use `Word.mk'` (featureless); the worked theorems are structural
(`hasUniqueHeads`, edge counts, `decide` over UD relation labels) and
agreement / valence checks pass vacuously. A future revision could add
feature-tagged fixtures if richer parallelism theorems are wanted.
-/

namespace DeMarneffeNivre2019


open DepGrammar DepGrammar.LongDistance DepGrammar.Coordination

/-! ### Wh-question fixtures -/

/-- "What did John see?" — object wh-question (basic tree).
Words: what(0) did(1) John(2) see(3). The wh-word attaches as `obj` of
the main verb. -/
def exWhatDidJohnSee : DepTree :=
  { words := [{ form :="what", cat := .PRON, features := { pronType := some .Int }}, Word.mk' "did" .AUX,
              Word.mk' "John" .PROPN, Word.mk' "see" .VERB]
    deps  := [⟨1, 2, .nsubj⟩, ⟨1, 3, .aux⟩, ⟨1, 0, .obj⟩]
    rootIdx := 1 }

/-- "Who saw Mary?" — subject wh-question (no gap needed). -/
def exWhoSawMary : DepTree :=
  { words := [{ form :="who", cat := .PRON, features := { pronType := some .Int }}, Word.mk' "saw" .VERB,
              Word.mk' "Mary" .PROPN]
    deps  := [⟨1, 0, .nsubj⟩, ⟨1, 2, .obj⟩]
    rootIdx := 1 }

/-- "Who did John see?" — object wh-question with `who`. -/
def exWhoDidJohnSee : DepTree :=
  { words := [{ form :="who", cat := .PRON, features := { pronType := some .Int }}, Word.mk' "did" .AUX,
              Word.mk' "John" .PROPN, Word.mk' "see" .VERB]
    deps  := [⟨1, 2, .nsubj⟩, ⟨1, 3, .aux⟩, ⟨1, 0, .obj⟩]
    rootIdx := 1 }

/-! ### Relative-clause fixtures -/

/-- "the book that John read" — object relative clause (basic tree). In UD
the relative clause attaches via `acl` from head noun to RC verb; the gap
(`book` as `obj` of `read`) is implicit. -/
def exTheBookThatJohnRead : DepTree :=
  { words := [Word.mk' "the" .DET, Word.mk' "book" .NOUN,
              Word.mk' "that" .SCONJ, Word.mk' "John" .PROPN,
              Word.mk' "read" .VERB]
    deps  := [⟨1, 0, .det⟩, ⟨1, 4, .acl⟩, ⟨4, 2, .mark⟩, ⟨4, 3, .nsubj⟩]
    rootIdx := 1 }

/-- Enhanced graph for "the book that John read": `book` is added as `obj`
of `read`. -/
def exTheBookThatJohnRead_enhanced : DepGraph :=
  fillGap exTheBookThatJohnRead 1 4 .objGap

/-! ### Complement-clause fixtures -/

/-- "John thinks that Mary sleeps" — that-complement (no gap). -/
def exJohnThinksThatMarySleeps : DepTree :=
  { words := [Word.mk' "John" .PROPN, Word.mk' "thinks" .VERB,
              Word.mk' "that" .SCONJ, Word.mk' "Mary" .PROPN,
              Word.mk' "sleeps" .VERB]
    deps  := [⟨1, 0, .nsubj⟩, ⟨1, 4, .ccomp⟩, ⟨4, 2, .mark⟩, ⟨4, 3, .nsubj⟩]
    rootIdx := 1 }

/-- "John thinks Mary sleeps" — bare complement (that-omission, no gap). -/
def exJohnThinksMarySleeps : DepTree :=
  { words := [Word.mk' "John" .PROPN, Word.mk' "thinks" .VERB,
              Word.mk' "Mary" .PROPN, Word.mk' "sleeps" .VERB]
    deps  := [⟨1, 0, .nsubj⟩, ⟨1, 3, .ccomp⟩, ⟨3, 2, .nsubj⟩]
    rootIdx := 1 }

/-- "John wonders if Mary sleeps" — if-complement (no gap). -/
def exJohnWondersIfMarySleeps : DepTree :=
  { words := [Word.mk' "John" .PROPN, Word.mk' "wonders" .VERB,
              Word.mk' "if" .SCONJ, Word.mk' "Mary" .PROPN,
              Word.mk' "sleeps" .VERB]
    deps  := [⟨1, 0, .nsubj⟩, ⟨1, 4, .ccomp⟩, ⟨4, 2, .mark⟩, ⟨4, 3, .nsubj⟩]
    rootIdx := 1 }

/-- "John wonders what Mary saw" — embedded wh-question.
Words: John(0) wonders(1) what(2) Mary(3) saw(4). -/
def exJohnWondersWhatMarySaw : DepTree :=
  { words := [Word.mk' "John" .PROPN, Word.mk' "wonders" .VERB,
              { form :="what", cat := .PRON, features := { pronType := some .Int }},
              Word.mk' "Mary" .PROPN, Word.mk' "saw" .VERB]
    deps  := [⟨1, 0, .nsubj⟩, ⟨1, 4, .ccomp⟩, ⟨4, 3, .nsubj⟩, ⟨4, 2, .obj⟩]
    rootIdx := 1 }

/-! ### Coordination fixtures -/

/-- "John and Mary sleep" — NP coordination. -/
def exJohnAndMarySleep : DepTree :=
  { words := [Word.mk' "John" .PROPN, Word.mk' "and" .CCONJ,
              Word.mk' "Mary" .PROPN, Word.mk' "sleep" .VERB]
    deps  := [⟨3, 0, .nsubj⟩, ⟨0, 2, .conj⟩]
    rootIdx := 3 }

/-- "John sleeps and Mary sleeps" — S coordination. -/
def exJohnSleepsAndMarySleeps : DepTree :=
  { words := [Word.mk' "John" .PROPN, Word.mk' "sleeps" .VERB,
              Word.mk' "and" .CCONJ, Word.mk' "Mary" .PROPN,
              Word.mk' "sleeps" .VERB]
    deps  := [⟨1, 0, .nsubj⟩, ⟨1, 4, .conj⟩, ⟨4, 3, .nsubj⟩]
    rootIdx := 1 }

/-- "John sees and hears Mary" — VP coordination (basic tree). `Mary`
attaches as `obj` of `sees` only; `hears` is `conj` of `sees`. -/
def exJohnSeesAndHearsMary : DepTree :=
  { words := [Word.mk' "John" .PROPN, Word.mk' "sees" .VERB,
              Word.mk' "and" .CCONJ, Word.mk' "hears" .VERB,
              Word.mk' "Mary" .PROPN]
    deps  := [⟨1, 0, .nsubj⟩, ⟨1, 2, .cc⟩, ⟨1, 3, .conj⟩, ⟨1, 4, .obj⟩]
    rootIdx := 1 }

/-- Enhanced graph for "John sees and hears Mary": `Mary` is `obj` of
*both* `sees` and `hears` (shared-dep propagation). -/
def exJohnSeesAndHearsMary_enhanced : DepGraph :=
  enhanceSharedDeps exJohnSeesAndHearsMary

/-- "the happy and smart boy" — adjective coordination. -/
def exOldAndWiseMan : DepTree :=
  { words := [Word.mk' "the" .DET, Word.mk' "happy" .ADJ,
              Word.mk' "and" .CCONJ, Word.mk' "smart" .ADJ,
              Word.mk' "boy" .NOUN]
    deps  := [⟨4, 0, .det⟩, ⟨4, 1, .amod⟩, ⟨1, 3, .conj⟩]
    rootIdx := 4 }

/-- "John likes and Mary hates pizza" — Right Node Raising (basic tree).
`pizza` attaches to `likes` only. -/
def exRNR : DepTree :=
  { words := [Word.mk' "John" .PROPN, Word.mk' "likes" .VERB,
              Word.mk' "and" .CCONJ, Word.mk' "Mary" .PROPN,
              Word.mk' "hates" .VERB, Word.mk' "pizza" .NOUN]
    deps  := [⟨1, 0, .nsubj⟩, ⟨1, 4, .conj⟩, ⟨4, 3, .nsubj⟩, ⟨1, 5, .obj⟩]
    rootIdx := 1 }

/-- Enhanced graph for RNR: `pizza` is `obj` of both verbs. -/
def exRNR_enhanced : DepGraph := enhanceSharedDeps exRNR

/-! ### Smoke tests -/

#guard isLDWellFormed exWhatDidJohnSee [(0, 3, .objGap)]
#guard isLDWellFormed exWhoSawMary []
#guard isLDWellFormed exTheBookThatJohnRead [(1, 4, .objGap)]
#guard checkCatMatch exJohnAndMarySleep
#guard checkCatMatch exJohnSleepsAndMarySleeps
#guard checkArgStrMatch exJohnSeesAndHearsMary

/-! ### Worked theorems — long-distance dependencies -/

/-- Object wh-questions have a `[wh]` filler at index 0. -/
theorem whatDidJohnSee_has_wh :
    exWhatDidJohnSee.words[0]?.map (·.features.isWh) = some true := rfl

/-- Subject wh-questions don't need gaps (empty gap list). -/
theorem whoSawMary_no_gap :
    isLDWellFormed exWhoSawMary [] = true := by decide

/-- The enhanced graph for "the book that John read" has the obj-gap edge. -/
theorem relclause_enhanced_has_obj :
    exTheBookThatJohnRead_enhanced.deps.any
      (λ d => d.headIdx == 4 && d.depIdx == 1 && d.depType == .obj) = true := by
  decide

/-- The basic tree of "the book that John read" does NOT have this obj edge. -/
theorem relclause_basic_lacks_obj :
    ¬ (exTheBookThatJohnRead.deps.any
      (λ d => d.headIdx == 4 && d.depIdx == 1 && d.depType == .obj) = true) := by
  decide

/-- The enhanced graph has strictly more edges than the basic tree. -/
theorem relclause_enhanced_more_edges :
    exTheBookThatJohnRead_enhanced.deps.length >
      exTheBookThatJohnRead.deps.length := by decide

/-- The enhanced relclause graph violates unique-heads (book has edges from
both `det` and `obj`), per [de-marneffe-nivre-2019] §4.4. -/
theorem relclause_enhanced_not_tree :
    hasUniqueHeads { words := exTheBookThatJohnRead_enhanced.words
                     deps  := exTheBookThatJohnRead_enhanced.deps
                     rootIdx := exTheBookThatJohnRead_enhanced.rootIdx } = false := by
  decide

/-- The basic relclause tree IS a tree (unique heads). -/
theorem relclause_basic_is_tree :
    hasUniqueHeads exTheBookThatJohnRead = true := by decide

/-- `extractionLabel` recovers the object-gap label from the basic/enhanced
diff at the head-noun index. -/
theorem relclause_objExtraction_derived :
    extractionLabel exTheBookThatJohnRead exTheBookThatJohnRead_enhanced 1
      = some .objGap := by decide

/-- Complement clauses have no filler-gap dependencies (vacuous heuristic
island check). -/
theorem complement_no_gap :
    checkNoIslandViolation exJohnThinksThatMarySleeps [] = true := by decide

/-! ### Worked theorems — coordination -/

/-- NP coordination has matching categories. -/
theorem johnAndMary_cat_match :
    checkCatMatch exJohnAndMarySleep = true := by decide

/-- S coordination has matching categories. -/
theorem johnSleepsAndMarySleeps_cat_match :
    checkCatMatch exJohnSleepsAndMarySleeps = true := by decide

/-- VP coordination has matching argument structures (vacuously, since
the example uses featureless verbs). -/
theorem seesAndHears_argstr_match :
    checkArgStrMatch exJohnSeesAndHearsMary = true := by decide

/-- Adjective coordination has matching categories. -/
theorem oldAndWise_cat_match :
    checkCatMatch exOldAndWiseMan = true := by decide

/-- `enhanceSharedDeps` adds the missing `obj` edge from `hears` to `Mary`. -/
theorem coord_enhanced_has_shared_obj :
    exJohnSeesAndHearsMary_enhanced.deps.any
      (λ d => d.headIdx == 3 && d.depIdx == 4 && d.depType == .obj) = true := by
  decide

/-- The basic VP-coord tree does NOT have the shared obj edge. -/
theorem coord_basic_lacks_shared_obj :
    ¬ (exJohnSeesAndHearsMary.deps.any
      (λ d => d.headIdx == 3 && d.depIdx == 4 && d.depType == .obj) = true) := by
  decide

/-- The coord enhanced graph has strictly more edges than the basic tree. -/
theorem coord_enhanced_more_edges :
    exJohnSeesAndHearsMary_enhanced.deps.length >
      exJohnSeesAndHearsMary.deps.length := by decide

/-- The coord enhanced graph violates unique-heads (`Mary` has incoming `obj`
from both `sees` and `hears`), per [de-marneffe-nivre-2019] §4.4. -/
theorem coord_enhanced_not_tree :
    hasUniqueHeads { words := exJohnSeesAndHearsMary_enhanced.words
                     deps  := exJohnSeesAndHearsMary_enhanced.deps
                     rootIdx := exJohnSeesAndHearsMary_enhanced.rootIdx } = false := by
  decide

/-- The basic coord tree IS a tree (unique heads). -/
theorem coord_basic_is_tree :
    hasUniqueHeads exJohnSeesAndHearsMary = true := by decide

/-- RNR enhancement propagates `obj` to the second-conjunct verb. -/
theorem rnr_enhanced_has_shared_obj :
    exRNR_enhanced.deps.any
      (λ d => d.headIdx == 4 && d.depIdx == 5 && d.depType == .obj) = true := by
  decide

/-- RNR enhanced graph violates unique-heads. -/
theorem rnr_enhanced_not_tree :
    hasUniqueHeads { words := exRNR_enhanced.words
                     deps  := exRNR_enhanced.deps
                     rootIdx := exRNR_enhanced.rootIdx } = false := by
  decide

end DeMarneffeNivre2019
