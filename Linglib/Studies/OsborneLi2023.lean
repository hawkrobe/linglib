import Linglib.Syntax.DependencyGrammar.Basic
import Linglib.Data.UD.Basic
import Linglib.Data.Examples.Schema
import Linglib.Syntax.DependencyGrammar.Coordination
import Linglib.Morphology.Word.Basic
import Linglib.Data.Examples.OsborneLi2023

open Morphology (Word)

/-!
# CRDC: Conjunct Referential Dependency Constraint
[osborne-li-2023]

The Conjunct Referential Dependency Constraint (CRDC), formulated by
[osborne-li-2023] in *Folia Linguistica* 57(3): 629–659, is a
dependency-grammar constraint on co-valuation in sentences that involve
coordinate structures.

Paper text, p. 651 (verbatim):

> A referentially dependent conjunct valent can be co-valued with a full
> co-valent, but a referentially dependent full valent can hardly be
> co-valued with a conjunct co-valent.

The CRDC governs *only* configurations in which one of the relevant
positions sits inside a coordinate structure; non-coordinate binding
falls under standard binding-theoretic principles (Conditions A/B/C).
The paper is explicit on p. 651: "The CRDC therefore says nothing about
[cases where no coordination is involved]."

Marginality is constitutive of the CRDC's empirical content. The paper's
crowdsourced acceptability table (p. 630 fn. 3) maps mean scores to
markers — `?` (1.65–2.29), `??` (2.30–2.94), `*` (2.95–4.00). The CRDC's
prediction is `??`, which corresponds to `Judgment.questionable` in the
project's 5-level enum.

## Main definitions

* `isConjunctValent` / `isFullValent` — the paper's predicate-valent
  type distinction, operationalised over `DepTree` via
  `UD.DepRel.isValencyArg` from `Core/UD.lean`.
* `crdcPredictedJudgment` — the `Judgment` the CRDC assigns to a
  candidate co-valuation; `.questionable` exactly when CRDC fires,
  `.acceptable` when CRDC is silent (other binding principles may
  still apply).

## Implementation notes

* "Valent" is operationalised as a direct UD valency-relation dependent
  of the predicate. This is a deliberate simplification of the paper's
  catena-based notion (paper §4); the example set does not exercise the
  distinction.
* `getConjuncts` is reused from `DepGrammar.Coordination` rather than
  reinventing coord-structure traversal. UD's basic-tree convention
  makes the first conjunct the head of the coordinate structure; the
  remaining conjuncts attach via `.conj`.
* The CRDC alone is not a full binding theory — it predicts only the
  coord-conjunct-vs-full-valent contribution to acceptability. Example
  (9b) "Max talked about him" is sentence-level `.questionable` from
  Condition B, but `crdcPredictedJudgment` returns `.acceptable`
  because the CRDC is silent on non-coordinate cases.

## Cross-framework relationship

The standard binding theories formalized elsewhere in linglib —
[chomsky-1981] (`Studies/Chomsky1981.lean`),
[hudson-1990] (`Studies/Hudson1990.lean`),
[pollard-sag-1994] / [sag-wasow-bender-2003]
(`Syntax/HPSG/Coreference.lean`,
`Studies/SagWasowBender2003.lean`) — make *categorical*
predictions via `Bool`-valued `grammaticalForCoreference`. The CRDC
contributes a *graded* prediction (`.questionable`) that those
predicates cannot express in their current shape; the comparison is
not a head-to-head bake-off because the two frameworks answer
different questions on disjoint stimulus subsets:

* CRDC: graded marginality, coordinate-structure stimuli, silent
  on non-coordinate cases (paper p. 651 explicit).
* Conditions A/B/C: categorical grammaticality, non-coordinate
  stimuli (current parsers do not traverse coordinate structures,
  so any coordinated input categorically returns `false` — a
  parser limitation, not a theoretical claim).

A direct CRDC-vs-Conditions-A/B/C bake-off requires (a) extending
the binding-theory parsers to coordination and (b) lifting their
output to `Judgment`. Both are out of scope for this study file.

## Todo

* Paper §6 counterexamples (e.g. *vote*-predicate identity split,
  example (55a) in the JSON) are encoded as data but not yet covered
  by a CRDC-vs-data theorem; needs integration with a third-party-
  referent disjunct.
* Paper §7 — coordination-as-phrase-structure vs subordination-as-
  dependency contrast — is theoretical commentary without formal
  content here yet.
* Bool→Prop migration of `isConjunctValent` / `isFullValent` should
  happen as part of a unified `DepGrammar/*` sweep, not piecemeal.
* Cross-framework CRDC-vs-Conditions-A/B/C bake-off blocked on
  parser/coordination work (see Cross-framework relationship).
-/

namespace OsborneLi2023


open DepGrammar
open DepGrammar.Coordination
open Data.Examples (LinguisticExample)
open Features (Judgment)

/-! ### Predicate-valent type -/

/-- Word `valentIdx` is a *conjunct valent* of predicate `predIdx`: it
    is a conjunct of a coordinate structure that fills a valency role
    of `predIdx`. Concretely: there is a valency-eligible edge from
    `predIdx` to some coord-head `c`, and `valentIdx` is in
    `allConjuncts c` (the first conjunct, which heads the structure
    in UD, plus the remaining conjuncts attached via `.conj`). -/
def isConjunctValent (t : DepTree) (predIdx valentIdx : Nat) : Bool :=
  t.deps.any λ d =>
    d.headIdx == predIdx && d.depType.isValencyArg
      && hasConjuncts t d.depIdx
      && (allConjuncts t d.depIdx).contains valentIdx

/-- Word `valentIdx` is a *full valent* of `predIdx`: a valent of
    `predIdx` that is not a conjunct valent. Matches the paper's
    definition (p. 651): "a valent of a given predicate is a full
    valent thereof if it is complete, that is, it is *not* a conjunct
    valent." Operationalised as "direct valency-eligible dependent of
    `predIdx` AND not a conjunct valent." -/
def isFullValent (t : DepTree) (predIdx valentIdx : Nat) : Bool :=
  (t.deps.any λ d =>
      d.headIdx == predIdx && d.depType.isValencyArg
        && d.depIdx == valentIdx)
    && ¬ isConjunctValent t predIdx valentIdx

/-! ### CRDC prediction -/

/-- The CRDC's predicted judgment for co-valuing anaphor `anaIdx` with
    antecedent `anteIdx` under predicate `predIdx` in tree `t`.

    Fires (`.questionable`) exactly when the anaphor is a full valent
    and the antecedent is a conjunct valent of the same predicate.
    Otherwise returns `.acceptable` — CRDC is silent, and other binding
    principles (Conditions A/B/C) may still apply. -/
def crdcPredictedJudgment
    (t : DepTree) (predIdx anaIdx anteIdx : Nat) : Judgment :=
  if isFullValent t predIdx anaIdx && isConjunctValent t predIdx anteIdx then
    .questionable
  else
    .acceptable

/-! ### CRDC-prediction theorems

Each theorem builds a `DepTree` matching one of the example sentences
and checks that `crdcPredictedJudgment` returns the contribution the
CRDC is responsible for. For data points whose sentence-level judgment
is set by a different principle (e.g. ex9b by Condition B, ex5a
strengthened by `both...and`), the theorem records that CRDC alone
predicts `.acceptable` or `.questionable` respectively — separating the
CRDC's contribution from other determinants of acceptability. -/

/-- Tree for "Max and Lucie talked about him."
    `Max(0) and(1) Lucie(2) talked(3) about(4) him(5)`. -/
def ex2a_tree : DepTree :=
  { words := [ { form :="Max", cat := .PROPN, features := {}}, { form :="and", cat := .CCONJ, features := {}}
             , { form :="Lucie", cat := .PROPN, features := {}}, { form :="talked", cat := .VERB, features := {}}
             , { form :="about", cat := .ADP, features := {}}, { form :="him", cat := .PRON, features := {}} ]
    deps  := [ ⟨3, 0, .nsubj⟩, ⟨0, 1, .cc⟩, ⟨0, 2, .conj⟩
             , ⟨3, 5, .obl⟩, ⟨5, 4, .case_⟩ ]
    rootIdx := 3 }

theorem ex2a_predicts_questionable :
    crdcPredictedJudgment ex2a_tree 3 5 0 = .questionable := by decide

/-- Tree for "Max talked about himself." — non-coordinate baseline. -/
def ex9a_tree : DepTree :=
  { words := [ { form :="Max", cat := .PROPN, features := {}}, { form :="talked", cat := .VERB, features := {}}
             , { form :="about", cat := .ADP, features := {}}, { form :="himself", cat := .PRON, features := {}} ]
    deps  := [ ⟨1, 0, .nsubj⟩, ⟨1, 3, .obl⟩, ⟨3, 2, .case_⟩ ]
    rootIdx := 1 }

theorem ex9a_predicts_acceptable :
    crdcPredictedJudgment ex9a_tree 1 3 0 = .acceptable := by decide

/-- Tree for "Max talked about him." — non-coordinate Condition B
    context. The sentence-level `.questionable` reading comes from
    Condition B, not the CRDC; here we record only that the CRDC is
    silent. -/
def ex9b_tree : DepTree :=
  { words := [ { form :="Max", cat := .PROPN, features := {}}, { form :="talked", cat := .VERB, features := {}}
             , { form :="about", cat := .ADP, features := {}}, { form :="him", cat := .PRON, features := {}} ]
    deps  := [ ⟨1, 0, .nsubj⟩, ⟨1, 3, .obl⟩, ⟨3, 2, .case_⟩ ]
    rootIdx := 1 }

theorem ex9b_crdc_silent :
    crdcPredictedJudgment ex9b_tree 1 3 0 = .acceptable := by decide

/-- Tree for "John talked about himself and his mother." — coordinate
    *object*. `himself` heads the coord, so it is a conjunct valent;
    `John` is a full valent. CRDC's permitted direction (conjunct
    anaphor of full antecedent). -/
def ex24a_tree : DepTree :=
  { words := [ { form :="John", cat := .PROPN, features := {}}, { form :="talked", cat := .VERB, features := {}}
             , { form :="about", cat := .ADP, features := {}}, { form :="himself", cat := .PRON, features := {}}
             , { form :="and", cat := .CCONJ, features := {}}, { form :="his", cat := .PRON, features := {}}
             , { form :="mother", cat := .NOUN, features := {}} ]
    deps  := [ ⟨1, 0, .nsubj⟩, ⟨1, 3, .obl⟩, ⟨3, 2, .case_⟩
             , ⟨3, 4, .cc⟩, ⟨3, 6, .conj⟩, ⟨6, 5, .nmod⟩ ]
    rootIdx := 1 }

theorem ex24a_predicts_acceptable :
    crdcPredictedJudgment ex24a_tree 1 3 0 = .acceptable := by decide

/-- Tree for "Both John and Mary love him." — coordinate subject with
    paired coordinator; pronoun in object position. The CRDC fires.
    Sentence-level judgment is stronger (`.ungrammatical`) due to
    `both...and` strengthening; the CRDC alone predicts
    `.questionable`. -/
def ex5a_tree : DepTree :=
  { words := [ { form :="Both", cat := .CCONJ, features := {}}, { form :="John", cat := .PROPN, features := {}}
             , { form :="and", cat := .CCONJ, features := {}}, { form :="Mary", cat := .PROPN, features := {}}
             , { form :="love", cat := .VERB, features := {}}, { form :="him", cat := .PRON, features := {}} ]
    deps  := [ ⟨4, 1, .nsubj⟩, ⟨1, 0, .cc⟩, ⟨1, 2, .cc⟩
             , ⟨1, 3, .conj⟩, ⟨4, 5, .obj⟩ ]
    rootIdx := 4 }

theorem ex5a_predicts_questionable :
    crdcPredictedJudgment ex5a_tree 4 5 1 = .questionable := by decide

/-- Tree for "John expected Mary and him to be able to leave soon."
    Coordinate-*object* under raising-to-object; `John` is the matrix
    subject (full valent), `him` is a conjunct of the embedded subject
    coord. Permitted direction; the CRDC is silent on `him↔John`
    co-valuation because `him` is a conjunct valent (not a full valent). -/
def ex28d_tree : DepTree :=
  { words := [ { form :="John", cat := .PROPN, features := {}}, { form :="expected", cat := .VERB, features := {}}
             , { form :="Mary", cat := .PROPN, features := {}}, { form :="and", cat := .CCONJ, features := {}}
             , { form :="him", cat := .PRON, features := {}}, { form :="to", cat := .PART, features := {}}
             , { form :="leave", cat := .VERB, features := {}}, { form :="soon", cat := .ADV, features := {}} ]
    deps  := [ ⟨1, 0, .nsubj⟩, ⟨1, 2, .obj⟩, ⟨2, 3, .cc⟩
             , ⟨2, 4, .conj⟩, ⟨1, 6, .xcomp⟩, ⟨6, 5, .mark⟩
             , ⟨6, 7, .advmod⟩ ]
    rootIdx := 1 }

theorem ex28d_predicts_acceptable :
    crdcPredictedJudgment ex28d_tree 1 4 0 = .acceptable := by decide

/-! ### Directionality

The CRDC is asymmetric: full-anaphor-of-conjunct-antecedent triggers
marginality (`.questionable`); the reverse direction (conjunct-anaphor
of-full-antecedent) does not. The asymmetry is exhibited on a single
tree by swapping `anaIdx` and `anteIdx`: only the (full, conjunct)
ordering fires the constraint. -/

/-- On ex2a's tree, swapping which index is the anaphor and which is
    the antecedent flips the verdict — only `him` (full) over `Max`
    (conjunct) triggers the CRDC. The reverse swap is structurally
    irreflexive of CRDC's prediction function; it does not correspond
    to a semantically coherent anaphoric reading. -/
theorem direction_asymmetry :
    -- (a) Blocked direction: full anaphor of conjunct antecedent
    crdcPredictedJudgment ex2a_tree 3 5 0 = .questionable ∧
    -- (b) Permitted direction (same tree, swapped indices)
    crdcPredictedJudgment ex2a_tree 3 0 5 = .acceptable := by
  refine ⟨?_, ?_⟩ <;> decide

end OsborneLi2023
