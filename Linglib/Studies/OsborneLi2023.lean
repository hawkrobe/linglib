import Linglib.Syntax.DependencyGrammar.Basic
import Linglib.Data.UD.Basic
import Linglib.Data.Examples.Schema
import Linglib.Morphology.Word.Basic
import Linglib.Data.Examples.OsborneLi2023

/-!
# CRDC: Conjunct Referential Dependency Constraint
[osborne-li-2023]

The Conjunct Referential Dependency Constraint of [osborne-li-2023],
p. 651 (verbatim):

> A referentially dependent conjunct valent can be co-valued with a full
> co-valent, but a referentially dependent full valent can hardly be
> co-valued with a conjunct co-valent.

The CRDC governs *only* configurations in which one of the relevant
positions sits inside a coordinate structure; non-coordinate binding
falls under Conditions A/B/C, on which the paper is explicit that the
CRDC is silent (p. 651). Marginality is constitutive of its empirical
content: the paper's crowdsourced acceptability table (p. 630 fn. 3)
maps mean scores to markers — `?` (1.65–2.29), `??` (2.30–2.94), `*`
(2.95–4.00) — and the CRDC's prediction is `??`,
`Judgment.questionable` in the project's enum.

Each theorem builds the tree of a stimulus from
`Data.Examples.OsborneLi2023` and compares `crdcPredictedJudgment`
with the row's recorded judgment: equality where the CRDC is the
operative principle, and a recorded divergence for ex9b, whose
sentence-level marginality is Condition B's contribution.

## Implementation notes

* "Valent" is operationalised as a direct UD valency-relation dependent
  of the predicate (`UD.DepRel.isValencyArg`) — a deliberate
  simplification of the paper's catena-based notion (§4); the example
  set does not exercise the difference.
* UD's basic-tree convention makes the first conjunct head the
  coordinate structure, with remaining conjuncts attached via `.conj`;
  the conjunct helpers are two-liners over `Graph.children`.
* Binding theories elsewhere in linglib (`Studies/Chomsky1981.lean`,
  `Syntax/HPSG/Coreference.lean`) make categorical predictions on
  non-coordinate stimuli; the CRDC contributes a graded prediction on
  coordinate ones. A head-to-head comparison needs coordination-aware
  binding parsers and `Judgment`-valued output on their side.

## TODO

* Cover §6's counterexamples (e.g. the *vote*-predicate identity split,
  ex (55a) in the data) with a third-party-referent treatment.
-/

namespace OsborneLi2023

open DependencyGrammar
open Features (Judgment)
open Morphology (Word)

/-! ### Predicate-valent type -/

/-- The conjuncts of the coordinate structure headed at `c`: the head
    (first conjunct, per UD) plus its `.conj` dependents. -/
def allConjuncts {n : ℕ} (g : Graph n) (c : Fin n) : List (Fin n) :=
  c :: (g.children c).filter (λ w => g.label c w == some .conj)

/-- Position `c` heads a coordinate structure: it has a `conj` dependent. -/
def HasConjuncts {n : ℕ} (g : Graph n) (c : Fin n) : Prop :=
  ∃ w ∈ g.children c, g.label c w = some .conj

instance {n : ℕ} (g : Graph n) (c : Fin n) : Decidable (HasConjuncts g c) :=
  List.decidableBEx _ _

/-- Word `valentIdx` is a *conjunct valent* of predicate `predIdx`: a
    conjunct of a coordinate structure that fills a valency role of
    `predIdx`. -/
def IsConjunctValent {n : ℕ} (g : Graph n) (predIdx valentIdx : Fin n) : Prop :=
  ∃ c ∈ g.children predIdx, ∃ r ∈ g.label predIdx c, r.isValencyArg
    ∧ HasConjuncts g c ∧ valentIdx ∈ allConjuncts g c

instance {n : ℕ} (g : Graph n) (predIdx valentIdx : Fin n) :
    Decidable (IsConjunctValent g predIdx valentIdx) :=
  List.decidableBEx _ _

/-- Word `valentIdx` is a *full valent* of `predIdx`: a valent that is
    not a conjunct valent — the paper's definition (p. 651): "a valent
    of a given predicate is a full valent thereof if it is complete,
    that is, it is *not* a conjunct valent." -/
def IsFullValent {n : ℕ} (g : Graph n) (predIdx valentIdx : Fin n) : Prop :=
  (∃ r ∈ g.label predIdx valentIdx, r.isValencyArg)
    ∧ ¬ IsConjunctValent g predIdx valentIdx

instance {n : ℕ} (g : Graph n) (predIdx valentIdx : Fin n) :
    Decidable (IsFullValent g predIdx valentIdx) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### CRDC prediction -/

/-- The CRDC's predicted judgment for co-valuing anaphor `anaIdx` with
    antecedent `anteIdx` under predicate `predIdx`: `.questionable`
    exactly when the anaphor is a full valent and the antecedent a
    conjunct valent of the same predicate; `.acceptable` otherwise —
    the CRDC is silent, and other binding principles may still apply. -/
def crdcPredictedJudgment {n : ℕ}
    (t : Graph n) (predIdx anaIdx anteIdx : Fin n) : Judgment :=
  if IsFullValent t predIdx anaIdx ∧ IsConjunctValent t predIdx anteIdx then
    .questionable
  else
    .acceptable

/-! ### CRDC predictions against the data rows -/

/-- Ex (2a): "Max and Lucie talked about him."
    `Max(0) and(1) Lucie(2) talked(3) about(4) him(5)`. -/
def coordSubject : Graph 6 :=
  .ofArcs
    [Word.mk' "Max" .PROPN, Word.mk' "and" .CCONJ, Word.mk' "Lucie" .PROPN,
     Word.mk' "talked" .VERB, Word.mk' "about" .ADP, Word.mk' "him" .PRON]
    3
    [(3, 0, .nsubj), (0, 1, .cc), (0, 2, .conj), (3, 5, .obl), (5, 4, .case_)]

/-- Full-valent `him` over conjunct-valent `Max`: the CRDC fires and
    matches the observed `??`. -/
theorem coordSubject_matches_data :
    crdcPredictedJudgment coordSubject 3 5 0 = Examples.ex2a.judgment := by decide

/-- Ex (9a): "Max talked about himself." — non-coordinate baseline. -/
def reflexiveBaseline : Graph 4 :=
  .ofArcs
    [Word.mk' "Max" .PROPN, Word.mk' "talked" .VERB,
     Word.mk' "about" .ADP, Word.mk' "himself" .PRON]
    1
    [(1, 0, .nsubj), (1, 3, .obl), (3, 2, .case_)]

theorem reflexiveBaseline_matches_data :
    crdcPredictedJudgment reflexiveBaseline 1 3 0 = Examples.ex9a.judgment := by decide

/-- Ex (9b): "Max talked about him." — non-coordinate Condition B context. The
    CRDC is silent; the row's marginality is Condition B's
    contribution, so prediction and row diverge by design. -/
def pronounBaseline : Graph 4 :=
  .ofArcs
    [Word.mk' "Max" .PROPN, Word.mk' "talked" .VERB,
     Word.mk' "about" .ADP, Word.mk' "him" .PRON]
    1
    [(1, 0, .nsubj), (1, 3, .obl), (3, 2, .case_)]

theorem pronounBaseline_crdc_silent :
    crdcPredictedJudgment pronounBaseline 1 3 0 = .acceptable ∧
    Examples.ex9b.judgment = .questionable := by decide

/-- Ex (24a): "John talked about himself and his mother." — coordinate *object*;
    `himself` heads the coordination, so it is a conjunct valent and
    `John` a full valent: the CRDC's permitted direction. -/
def coordObject : Graph 7 :=
  .ofArcs
    [Word.mk' "John" .PROPN, Word.mk' "talked" .VERB, Word.mk' "about" .ADP,
     Word.mk' "himself" .PRON, Word.mk' "and" .CCONJ, Word.mk' "his" .PRON,
     Word.mk' "mother" .NOUN]
    1
    [(1, 0, .nsubj), (1, 3, .obl), (3, 2, .case_),
     (3, 4, .cc), (3, 6, .conj), (6, 5, .nmod)]

theorem coordObject_matches_data :
    crdcPredictedJudgment coordObject 1 3 0 = Examples.ex24a.judgment := by decide

/-- Ex (5a): "Both John and Mary love him." — coordinate subject with paired
    coordinator; pronoun in object position. The CRDC fires and matches
    the observed `??`. -/
def pairedCoordSubject : Graph 6 :=
  .ofArcs
    [Word.mk' "Both" .CCONJ, Word.mk' "John" .PROPN, Word.mk' "and" .CCONJ,
     Word.mk' "Mary" .PROPN, Word.mk' "love" .VERB, Word.mk' "him" .PRON]
    4
    [(4, 1, .nsubj), (1, 0, .cc), (1, 2, .cc), (1, 3, .conj), (4, 5, .obj)]

theorem pairedCoordSubject_matches_data :
    crdcPredictedJudgment pairedCoordSubject 4 5 1 = Examples.ex5a.judgment := by decide

/-- Ex (28d): "John expected Mary and him to be able to leave soon." —
    coordinate object under raising-to-object: `him` is a conjunct
    valent, so the CRDC is silent on co-valuing it with `John`. -/
def raisingCoordObject : Graph 8 :=
  .ofArcs
    [Word.mk' "John" .PROPN, Word.mk' "expected" .VERB, Word.mk' "Mary" .PROPN,
     Word.mk' "and" .CCONJ, Word.mk' "him" .PRON, Word.mk' "to" .PART,
     Word.mk' "leave" .VERB, Word.mk' "soon" .ADV]
    1
    [(1, 0, .nsubj), (1, 2, .obj), (2, 3, .cc), (2, 4, .conj),
     (1, 6, .xcomp), (6, 5, .mark), (6, 7, .advmod)]

theorem raisingCoordObject_matches_data :
    crdcPredictedJudgment raisingCoordObject 1 4 0 = Examples.ex28d.judgment := by decide

/-! ### Directionality -/

/-- The CRDC is asymmetric: on ex2a's tree, only the full-anaphor-of-
    conjunct-antecedent direction fires; swapping anaphor and antecedent
    leaves the CRDC silent. -/
theorem direction_asymmetry :
    crdcPredictedJudgment coordSubject 3 5 0 = .questionable ∧
    crdcPredictedJudgment coordSubject 3 0 5 = .acceptable := by decide

end OsborneLi2023
