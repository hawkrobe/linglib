import Linglib.Syntax.DependencyGrammar.Projection
import Linglib.Syntax.DependencyGrammar.Basic

open Morphology (Word)

/-!
# de Marneffe & Nivre 2019: UD enhanced dependencies for English LD and coordination
[de-marneffe-nivre-2019]

Worked English examples illustrating Universal Dependencies' basic vs
enhanced representations (cf. §4.2 and Figure 9 of
[de-marneffe-nivre-2019]). Enhanced graphs are built by adding the
extra arcs with `Graph.enhance`.

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


open DependencyGrammar

/-! ### Wh-question fixtures -/

/-- "What did John see?" — object wh-question (basic tree).
Words: what(0) did(1) John(2) see(3). The wh-word attaches as `obj` of
the main verb. -/
def exWhatDidJohnSee : Graph 4 :=
  .ofArcs [{ form :="what", cat := .PRON, features := { pronType := some .Int }}, Word.mk' "did" .AUX,
              Word.mk' "John" .PROPN, Word.mk' "see" .VERB]
    1 [(1, 2, .nsubj), (1, 3, .aux), (1, 0, .obj)]

/-- "Who saw Mary?" — subject wh-question (no gap needed). -/
def exWhoSawMary : Graph 3 :=
  .ofArcs [{ form :="who", cat := .PRON, features := { pronType := some .Int }}, Word.mk' "saw" .VERB,
              Word.mk' "Mary" .PROPN]
    1 [(1, 0, .nsubj), (1, 2, .obj)]

/-- "Who did John see?" — object wh-question with `who`. -/
def exWhoDidJohnSee : Graph 4 :=
  .ofArcs [{ form :="who", cat := .PRON, features := { pronType := some .Int }}, Word.mk' "did" .AUX,
              Word.mk' "John" .PROPN, Word.mk' "see" .VERB]
    1 [(1, 2, .nsubj), (1, 3, .aux), (1, 0, .obj)]

/-! ### Relative-clause fixtures -/

/-- "the book that John read" — object relative clause (basic tree). In UD
the relative clause attaches via `acl` from head noun to RC verb; the gap
(`book` as `obj` of `read`) is implicit. -/
def exTheBookThatJohnRead : Graph 5 :=
  .ofArcs [Word.mk' "the" .DET, Word.mk' "book" .NOUN,
              Word.mk' "that" .SCONJ, Word.mk' "John" .PROPN,
              Word.mk' "read" .VERB]
    1 [(1, 0, .det), (1, 4, .acl), (4, 2, .mark), (4, 3, .nsubj)]

/-- Enhanced graph for "the book that John read": `book` is added as `obj`
of `read`. -/
def exTheBookThatJohnRead_enhanced : Graph 5 :=
  exTheBookThatJohnRead.enhance [(4, 1, .obj)]

/-! ### Complement-clause fixtures -/

/-- "John thinks that Mary sleeps" — that-complement (no gap). -/
def exJohnThinksThatMarySleeps : Graph 5 :=
  .ofArcs [Word.mk' "John" .PROPN, Word.mk' "thinks" .VERB,
              Word.mk' "that" .SCONJ, Word.mk' "Mary" .PROPN,
              Word.mk' "sleeps" .VERB]
    1 [(1, 0, .nsubj), (1, 4, .ccomp), (4, 2, .mark), (4, 3, .nsubj)]

/-- "John thinks Mary sleeps" — bare complement (that-omission, no gap). -/
def exJohnThinksMarySleeps : Graph 4 :=
  .ofArcs [Word.mk' "John" .PROPN, Word.mk' "thinks" .VERB,
              Word.mk' "Mary" .PROPN, Word.mk' "sleeps" .VERB]
    1 [(1, 0, .nsubj), (1, 3, .ccomp), (3, 2, .nsubj)]

/-- "John wonders if Mary sleeps" — if-complement (no gap). -/
def exJohnWondersIfMarySleeps : Graph 5 :=
  .ofArcs [Word.mk' "John" .PROPN, Word.mk' "wonders" .VERB,
              Word.mk' "if" .SCONJ, Word.mk' "Mary" .PROPN,
              Word.mk' "sleeps" .VERB]
    1 [(1, 0, .nsubj), (1, 4, .ccomp), (4, 2, .mark), (4, 3, .nsubj)]

/-- "John wonders what Mary saw" — embedded wh-question.
Words: John(0) wonders(1) what(2) Mary(3) saw(4). -/
def exJohnWondersWhatMarySaw : Graph 5 :=
  .ofArcs [Word.mk' "John" .PROPN, Word.mk' "wonders" .VERB,
              { form :="what", cat := .PRON, features := { pronType := some .Int }},
              Word.mk' "Mary" .PROPN, Word.mk' "saw" .VERB]
    1 [(1, 0, .nsubj), (1, 4, .ccomp), (4, 3, .nsubj), (4, 2, .obj)]

/-! ### Coordination fixtures -/

/-- "John and Mary sleep" — NP coordination. -/
def exJohnAndMarySleep : Graph 4 :=
  .ofArcs [Word.mk' "John" .PROPN, Word.mk' "and" .CCONJ,
              Word.mk' "Mary" .PROPN, Word.mk' "sleep" .VERB]
    3 [(3, 0, .nsubj), (0, 2, .conj)]

/-- "John sleeps and Mary sleeps" — S coordination. -/
def exJohnSleepsAndMarySleeps : Graph 5 :=
  .ofArcs [Word.mk' "John" .PROPN, Word.mk' "sleeps" .VERB,
              Word.mk' "and" .CCONJ, Word.mk' "Mary" .PROPN,
              Word.mk' "sleeps" .VERB]
    1 [(1, 0, .nsubj), (1, 4, .conj), (4, 3, .nsubj)]

/-- "John sees and hears Mary" — VP coordination (basic tree). `Mary`
attaches as `obj` of `sees` only; `hears` is `conj` of `sees`. -/
def exJohnSeesAndHearsMary : Graph 5 :=
  .ofArcs [Word.mk' "John" .PROPN, Word.mk' "sees" .VERB,
              Word.mk' "and" .CCONJ, Word.mk' "hears" .VERB,
              Word.mk' "Mary" .PROPN]
    1 [(1, 0, .nsubj), (1, 2, .cc), (1, 3, .conj), (1, 4, .obj)]

/-- Enhanced graph for "John sees and hears Mary": `Mary` is `obj` of
*both* `sees` and `hears` (shared-dep propagation). -/
def exJohnSeesAndHearsMary_enhanced : Graph 5 :=
  exJohnSeesAndHearsMary.enhance [(3, 4, .obj)]

/-- "the happy and smart boy" — adjective coordination. -/
def exOldAndWiseMan : Graph 5 :=
  .ofArcs [Word.mk' "the" .DET, Word.mk' "happy" .ADJ,
           Word.mk' "and" .CCONJ, Word.mk' "smart" .ADJ, Word.mk' "boy" .NOUN]
    4 [(4, 0, .det), (4, 1, .amod), (1, 3, .conj)]

/-- "John likes and Mary hates pizza" — Right Node Raising (basic tree).
`pizza` attaches to `likes` only. -/
def exRNR : Graph 6 :=
  .ofArcs [Word.mk' "John" .PROPN, Word.mk' "likes" .VERB,
           Word.mk' "and" .CCONJ, Word.mk' "Mary" .PROPN,
           Word.mk' "hates" .VERB, Word.mk' "pizza" .NOUN]
    1 [(1, 0, .nsubj), (1, 4, .conj), (4, 3, .nsubj), (1, 5, .obj)]

/-- Enhanced graph for RNR: `pizza` is `obj` of both verbs. -/
def exRNR_enhanced : Graph 6 := exRNR.enhance [(4, 5, .obj)]

/-- Conjuncts share their category — the parallelism constraint on
    coordination ([de-marneffe-nivre-2019] §4.2), study-locally. -/
def conjunctsCatMatch {n : ℕ} (g : Graph n) : Bool :=
  (List.finRange n).all λ v => (List.finRange n).all λ w =>
    if g.label v w == some .conj then (g.words v).cat == (g.words w).cat else true

/-! ### Worked theorems — long-distance dependencies -/

/-- Object wh-questions have a `[wh]` filler at position 0. -/
theorem whatDidJohnSee_has_wh :
    (exWhatDidJohnSee.words 0).features.isWh = true := rfl

/-- Subject wh-questions need no gap: the basic tree is already a
    well-formed tree. -/
theorem whoSawMary_no_gap : exWhoSawMary.IsTree := by decide

/-- The enhanced graph for "the book that John read" has the obj-gap arc;
    the basic tree lacks it. -/
theorem relclause_enhancement :
    exTheBookThatJohnRead_enhanced.label 4 1 = some .obj ∧
    exTheBookThatJohnRead.label 4 1 = none := by decide

/-- `book` gains an unrepresented argument — the gap made explicit. -/
theorem relclause_gap_recovered :
    HasUnrepresentedArg exTheBookThatJohnRead exTheBookThatJohnRead_enhanced 1 := by
  decide

/-- The enhanced relclause graph violates tree-hood (`book` now has two
    heads), per [de-marneffe-nivre-2019] §4.4; the basic tree is a tree. -/
theorem relclause_enhanced_not_tree :
    ¬ exTheBookThatJohnRead_enhanced.IsTree ∧ exTheBookThatJohnRead.IsTree := by
  decide

/-! ### Worked theorems — coordination -/

theorem johnAndMary_cat_match : conjunctsCatMatch exJohnAndMarySleep = true := by decide

theorem johnSleepsAndMarySleeps_cat_match :
    conjunctsCatMatch exJohnSleepsAndMarySleeps = true := by decide

theorem oldAndWise_cat_match : conjunctsCatMatch exOldAndWiseMan = true := by decide

/-- Shared-dependent propagation adds the missing `obj` arc from `hears`
    to `Mary`; the basic tree lacks it. -/
theorem coord_enhancement :
    exJohnSeesAndHearsMary_enhanced.label 3 4 = some .obj ∧
    exJohnSeesAndHearsMary.label 3 4 = none := by decide

/-- `Mary` gains an unrepresented argument in the enhanced graph. -/
theorem coord_gap_recovered :
    HasUnrepresentedArg exJohnSeesAndHearsMary exJohnSeesAndHearsMary_enhanced 4 := by
  decide

/-- The enhanced coordination graph violates tree-hood; the basic tree is
    a tree. -/
theorem coord_enhanced_not_tree :
    ¬ exJohnSeesAndHearsMary_enhanced.IsTree ∧ exJohnSeesAndHearsMary.IsTree := by
  decide

/-- RNR enhancement propagates `obj` to the second-conjunct verb, and the
    result is no longer a tree. -/
theorem rnr_enhancement :
    exRNR_enhanced.label 4 5 = some .obj ∧ ¬ exRNR_enhanced.IsTree := by decide

end DeMarneffeNivre2019
