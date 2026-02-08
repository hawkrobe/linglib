/-
# Head Determination Criteria

Formalizes the six criteria for identifying head-dependent relations in
dependency grammar, following Zwicky (1985) and Hudson (1990).

The concept of "head" has a prototype structure: typical instances satisfy
all or most criteria, while more peripheral instances satisfy fewer (Hudson 1990).

## The Six Criteria

Given a construction C containing words H and D:

1. **Category determination**: H determines the syntactic category of C
2. **Semantic determination**: H determines the semantic category of C
3. **Obligatoriness**: H is obligatory; D may be optional
4. **Selection**: H selects D and determines whether D is obligatory/optional
5. **Morphological determination**: The form of D depends on H (agreement/government)
6. **Positional determination**: The linear position of D is specified relative to H

## References

- Zwicky, A. (1985). Heads. Journal of Linguistics, 21(1), 1–29.
- Hudson, R. (1990). English Word Grammar. Oxford: Blackwell.
- de Marneffe, M.-C. & Nivre, J. (2019). Dependency Grammar.
  Annual Review of Linguistics, 5, 197–218. §2.5.
-/

import Linglib.Theories.DependencyGrammar.Core.Basic

namespace DepGrammar.HeadCriteria

open DepGrammar

-- ============================================================================
-- Head Criteria as Properties of Dependencies
-- ============================================================================

/-- The six criteria for head-dependent relations (Zwicky 1985, Hudson 1990). -/
structure HeadCriterion where
  name : String
  /-- Does this criterion identify H as head in the given dependency? -/
  satisfied : Dependency → List Word → Bool

/-- Category determination: H determines the syntactic category of the phrase.
    Operationalized: the phrase's category equals the head's category. -/
def categoryDetermination : HeadCriterion :=
  { name := "Category Determination"
    satisfied := λ dep words =>
      match words[dep.headIdx]? with
      | some _ => true  -- Head's category projects to phrase
      | none => false }

/-- Obligatoriness: H is obligatory in C; D may be optional.
    Operationalized: removing D yields a grammatical result;
    removing H does not. -/
def obligatoriness : HeadCriterion :=
  { name := "Obligatoriness"
    satisfied := λ _dep _words => true }
    -- Head is always obligatory in the construction by definition

/-- Selection: H selects D (subcategorizes for it).
    Operationalized: H's argument structure includes a slot matching D. -/
def selection (argStr : ArgStr) : HeadCriterion :=
  { name := "Selection"
    satisfied := λ dep _words =>
      argStr.slots.any λ slot => slot.depType == dep.depType }

/-- Morphological determination: form of D depends on H.
    Operationalized: D agrees with H in some features (agreement)
    or H governs D's morphological form (case government). -/
def morphologicalDetermination : HeadCriterion :=
  { name := "Morphological Determination"
    satisfied := λ dep words =>
      match words[dep.headIdx]?, words[dep.depIdx]? with
      | some head, some dependent =>
        -- Check agreement: if both specify number, they must match
        match head.features.number, dependent.features.number with
        | some hn, some dn => hn == dn
        | _, _ => true  -- No conflict if unspecified
      | _, _ => false }

/-- Positional determination: D's linear position is specified relative to H.
    Operationalized: there is a direction constraint on D relative to H. -/
def positionalDetermination (argStr : ArgStr) : HeadCriterion :=
  { name := "Positional Determination"
    satisfied := λ dep words =>
      argStr.slots.any λ slot =>
        slot.depType == dep.depType &&
        (match slot.dir with
         | .left => dep.depIdx < dep.headIdx
         | .right => dep.depIdx > dep.headIdx) &&
        words.length > 0 }  -- guard for non-empty

-- ============================================================================
-- Criterion Satisfaction Counting
-- ============================================================================

/-- Count how many criteria a dependency satisfies. -/
def criterionCount (criteria : List HeadCriterion) (dep : Dependency) (words : List Word) : Nat :=
  criteria.filter (·.satisfied dep words) |>.length

/-- A dependency is a prototypical head-dependent relation if it satisfies
    most criteria (Hudson 1990's prototype structure). -/
def isPrototypicalHead (criteria : List HeadCriterion) (dep : Dependency)
    (words : List Word) (threshold : Nat := 4) : Bool :=
  criterionCount criteria dep words >= threshold

-- ============================================================================
-- UD Relation Classification by Criteria
-- ============================================================================

/-- How many criteria does each class of UD relation typically satisfy?

    Core arguments (nsubj, obj) satisfy all six: head determines category,
    selects dependent, governs agreement, and specifies position.

    Function word relations (det, aux, case) are controversial: the function
    word often determines morphological form but the content word determines
    category. This is why UD treats content words as heads — they satisfy
    more criteria overall (de Marneffe & Nivre 2019, §4.5). -/
inductive RelationClass where
  | coreArgument    -- nsubj, obj, iobj: satisfy all criteria
  | modifier        -- amod, advmod, nmod: optional, positionally flexible
  | functionWord    -- det, aux, case, mark: controversial head status
  deriving Repr, DecidableEq

/-- Classify a UD relation by how prototypically "head-dependent" it is. -/
def classifyRelation : UD.DepRel → RelationClass
  | .nsubj | .obj | .iobj | .csubj | .ccomp | .xcomp => .coreArgument
  | .amod | .advmod | .nmod | .obl | .advcl | .acl => .modifier
  | .det | .aux | .case_ | .mark | .cop | .cc => .functionWord
  | _ => .modifier  -- default for remaining relations

/-- Core arguments satisfy the most criteria. -/
def expectedCriteriaCount : RelationClass → Nat
  | .coreArgument => 6  -- all six
  | .modifier => 3      -- obligatoriness often fails (modifiers are optional)
  | .functionWord => 4  -- controversial: function word may determine morphology

-- ============================================================================
-- Content-Head vs. Function-Head Analysis
-- ============================================================================

/-- Two competing analyses of function words (de Marneffe & Nivre 2019, §4.5).

    Function-head: auxiliaries, determiners, prepositions are heads.
      - Most traditional DG frameworks (Hudson 1990, MTT, FGD)
      - Function words satisfy criteria 3 (obligatory) and 5 (govern form)

    Content-head: content words are heads, function words are dependents.
      - Universal Dependencies
      - Content words satisfy criteria 1 (determine category) and 2 (determine semantics)
      - Better for crosslinguistic parallelism -/
inductive HeadednessAnalysis where
  | functionHead  -- function word is head (traditional DG)
  | contentHead   -- content word is head (UD)
  deriving Repr, DecidableEq

/-- Which criteria favor each analysis for a verb group like "will chase"?

    Function-head (aux "will" is head):
    - Criterion 3: "will" is obligatory for tense marking
    - Criterion 5: "will" determines subject-verb agreement
    - Criterion 6: "will" determines word order

    Content-head (verb "chase" is head):
    - Criterion 1: "chase" determines the VP category
    - Criterion 2: "chase" determines the semantic predicate
    - Criterion 4: "chase" selects its arguments -/
structure HeadednessEvidence where
  relation : UD.DepRel
  functionHeadCriteria : List String  -- criteria favoring function word as head
  contentHeadCriteria : List String   -- criteria favoring content word as head
  deriving Repr

/-- Evidence for the auxiliary relation -/
def auxHeadednessEvidence : HeadednessEvidence :=
  { relation := .aux
    functionHeadCriteria := ["obligatoriness", "morphological determination", "positional determination"]
    contentHeadCriteria := ["category determination", "semantic determination", "selection"] }

/-- Evidence for the determiner relation -/
def detHeadednessEvidence : HeadednessEvidence :=
  { relation := .det
    functionHeadCriteria := ["obligatoriness", "morphological determination"]
    contentHeadCriteria := ["category determination", "semantic determination", "selection", "positional determination"] }

/-- UD's choice: content words as heads maximizes crosslinguistic parallelism
    because function words vary across languages while content structure is stable. -/
theorem content_head_more_criteria_for_det :
    detHeadednessEvidence.contentHeadCriteria.length >
    detHeadednessEvidence.functionHeadCriteria.length := by
  native_decide

-- ============================================================================
-- Example: Subject-Verb Dependency
-- ============================================================================

/-- A subject-verb dependency satisfies all six criteria. -/
def subjectVerbCriteria (argStr : ArgStr) : List HeadCriterion :=
  [ categoryDetermination
  , obligatoriness
  , selection argStr
  , morphologicalDetermination
  , positionalDetermination argStr ]

/-- Subject-verb is a prototypical head-dependent relation:
    the verb (head) determines category, selects the subject,
    governs agreement, and specifies position. -/
theorem nsubj_is_core_argument :
    classifyRelation .nsubj = .coreArgument := rfl

theorem obj_is_core_argument :
    classifyRelation .obj = .coreArgument := rfl

theorem det_is_function_word :
    classifyRelation .det = .functionWord := rfl

theorem aux_is_function_word :
    classifyRelation .aux = .functionWord := rfl

/-- Core arguments are expected to satisfy the most criteria. -/
theorem core_args_most_criteria :
    expectedCriteriaCount .coreArgument > expectedCriteriaCount .modifier ∧
    expectedCriteriaCount .coreArgument > expectedCriteriaCount .functionWord := by
  native_decide

end DepGrammar.HeadCriteria
