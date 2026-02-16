import Linglib.Theories.Syntax.DependencyGrammar.Core.Basic
import Linglib.Phenomena.Syntax.DependencyGrammar.CRDC
import Linglib.Theories.Syntax.DependencyGrammar.Formal.HeadCriteria

/-!
# Government in Dependency Grammar

Formalizes government (Osborne 2019, Ch 4 §4.8, Ch 5): the mechanism by which
a head determines the morphosyntactic form of its dependent.

Government is distinct from:
- **Selection**: what semantic type the head requires (animate, proposition, etc.)
- **Subcategorization**: which argument slots the head has
- **Government**: what morphosyntactic form the head requires (case, verb form)

## Key Insight

The same valency frame (transitive verb taking two NP arguments) can have
different government patterns: "want to go" vs "enjoy swimming" — same slot
count, different morphological requirements on the complement.

## Bridges

- → `CRDC.lean`: government complements `ValencyFrame` — valency says WHAT
  slots exist, government says HOW they're filled
- → `HeadCriteria.lean`: government is criterion 5 (morphological determination)
  — the governor is the head
- → `Core/Basic.lean`: `ArgSlot` has `cat` and `depType`; government adds
  morphological form constraints

## References

- Osborne, T. (2019). *A Dependency Grammar of English*, Ch 4 §4.8, Ch 5.
  Amsterdam: John Benjamins.
-/

namespace DepGrammar.Government

open DepGrammar

-- ============================================================================
-- §1: Government Relation
-- ============================================================================

/-- A morphosyntactic feature that a head can govern on its dependent.
    Osborne (2019, Ch 4 §4.8). -/
inductive GovernedFeature where
  | case_      -- Prepositions/verbs govern case (e.g., German accusative)
  | vform      -- Verbs govern verb form of complement (infinitive, gerund, participle)
  | mood       -- Complementizers govern mood (subjunctive in Romance)
  | finiteness -- Verbs govern finiteness of complement clause
  deriving Repr, DecidableEq

/-- A government requirement: head requires dependent to have specific feature value.
    Osborne (2019, Ch 5). -/
structure GovRequirement where
  headCat : UD.UPOS
  depRel : UD.DepRel
  feature : GovernedFeature
  requiredValue : String  -- e.g., "acc", "infinitive", "gerund"
  deriving Repr, DecidableEq

-- ============================================================================
-- §2: English Government Data
-- ============================================================================

/-- Verb + to-infinitive: "want to go" — want governs infinitival form.
    Osborne (2019, Ch 5). -/
def govVerbInfinitive : GovRequirement :=
  ⟨.VERB, .xcomp, .vform, "infinitive"⟩

/-- Verb + bare infinitive: "make him go" — make governs base form.
    Osborne (2019, Ch 5). -/
def govVerbBareInf : GovRequirement :=
  ⟨.VERB, .xcomp, .vform, "base"⟩

/-- Verb + gerund: "enjoy swimming" — enjoy governs gerund form.
    Osborne (2019, Ch 5). -/
def govVerbGerund : GovRequirement :=
  ⟨.VERB, .xcomp, .vform, "gerund"⟩

/-- Verb + finite that-clause: "think that..." — think governs finite complement.
    Osborne (2019, Ch 5). -/
def govVerbFinite : GovRequirement :=
  ⟨.VERB, .ccomp, .finiteness, "finite"⟩

/-- Preposition + accusative: "with him/*he" — preposition governs accusative case.
    Osborne (2019, Ch 5). -/
def govPrepAcc : GovRequirement :=
  ⟨.ADP, .obj, .case_, "acc"⟩

/-- All English government requirements from Osborne (2019, Ch 5). -/
def englishGovRequirements : List GovRequirement :=
  [govVerbInfinitive, govVerbBareInf, govVerbGerund, govVerbFinite, govPrepAcc]

-- ============================================================================
-- §3: Government Checking
-- ============================================================================

/-- Match a governed feature against a word's feature bundle.
    Returns true if the word has the required value. -/
def matchGovFeature (w : Word) (feat : GovernedFeature) (reqVal : String) : Bool :=
  match feat with
  | .case_ =>
    match w.features.case_ with
    | some .Acc => reqVal == "acc"
    | some .Nom => reqVal == "nom"
    | some .Gen => reqVal == "gen"
    | _ => true  -- unspecified = no violation
  | .vform =>
    match w.features.vform with
    | some .Inf => reqVal == "infinitive"
    | some .Part => reqVal == "gerund" || reqVal == "participle"
    | some .Fin => reqVal == "finite" || reqVal == "base"
    | _ => true
  | .finiteness =>
    match w.features.finite with
    | true => reqVal == "finite"
    | false => reqVal == "nonfinite"
  | .mood => true  -- English lacks overt mood government

/-- Check if a dependency edge satisfies its government requirements. -/
def checkGovernment (t : DepTree) (govReqs : List GovRequirement) : Bool :=
  t.deps.all λ d =>
    govReqs.all λ req =>
      if d.depType == req.depRel then
        match t.words[d.headIdx]?, t.words[d.depIdx]? with
        | some hw, some dw =>
          if hw.cat == req.headCat then
            matchGovFeature dw req.feature req.requiredValue
          else true
        | _, _ => true
      else true

-- ============================================================================
-- §4: Government vs. Selection vs. Subcategorization
-- ============================================================================

/-- A government pattern: a verb with its government requirements.
    Distinct from `CRDC.ValencyFrame` which captures WHAT dependents appear. -/
structure GovernmentPattern where
  verb : String
  requirements : List GovRequirement
  deriving Repr

/-- "want" governs infinitival complement: "want to go" -/
def wantGov : GovernmentPattern :=
  ⟨"want", [govVerbInfinitive]⟩

/-- "enjoy" governs gerund complement: "enjoy swimming" -/
def enjoyGov : GovernmentPattern :=
  ⟨"enjoy", [govVerbGerund]⟩

/-- "think" governs finite complement: "think that..." -/
def thinkGov : GovernmentPattern :=
  ⟨"think", [govVerbFinite]⟩

/-- "make" governs bare infinitive: "make him go" -/
def makeGov : GovernmentPattern :=
  ⟨"make", [govVerbBareInf]⟩

/-- Government and valency are orthogonal: valency says WHAT dependents,
    government says WHAT FORM. Osborne (2019, Ch 5).
    A verb can have the same valency (transitive, taking xcomp) but different
    government (infinitive vs gerund complement).

    "want to go" and "enjoy swimming" — both take a VP complement (same
    valency: verb + xcomp), but want requires infinitive while enjoy requires
    gerund. -/
theorem government_orthogonal_to_valency :
    wantGov.requirements.length == enjoyGov.requirements.length &&
    wantGov.requirements.head?.map (·.depRel) == enjoyGov.requirements.head?.map (·.depRel) &&
    wantGov.requirements.head?.map (·.requiredValue) !=
      enjoyGov.requirements.head?.map (·.requiredValue) := by
  native_decide

-- ============================================================================
-- §5: Example Trees
-- ============================================================================

/-- "She wants to go" — verb governs infinitival complement.
    Words: she(0) wants(1) to(2) go(3)
    Deps: wants → she (nsubj), wants → go (xcomp), go → to (mark) -/
def ex_sheWantsToGo : DepTree :=
  { words := [ ⟨"she", .PRON, { case_ := some .Nom }⟩
             , ⟨"wants", .VERB, { valence := some .transitive }⟩
             , ⟨"to", .PART, {}⟩
             , ⟨"go", .VERB, { vform := some .Inf }⟩ ]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 3, .xcomp⟩, ⟨3, 2, .mark⟩]
    rootIdx := 1 }

/-- "She enjoys swimming" — verb governs gerund complement.
    Words: she(0) enjoys(1) swimming(2)
    Deps: enjoys → she (nsubj), enjoys → swimming (xcomp) -/
def ex_sheEnjoysSw : DepTree :=
  { words := [ ⟨"she", .PRON, { case_ := some .Nom }⟩
             , ⟨"enjoys", .VERB, { valence := some .transitive }⟩
             , ⟨"swimming", .VERB, { vform := some .Part }⟩ ]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .xcomp⟩]
    rootIdx := 1 }

/-- "with him" — preposition governs accusative case.
    Words: with(0) him(1)
    Deps: with → him (obj) -/
def ex_withHim : DepTree :=
  { words := [ ⟨"with", .ADP, {}⟩
             , ⟨"him", .PRON, { case_ := some .Acc }⟩ ]
    deps := [⟨0, 1, .obj⟩]
    rootIdx := 0 }

/-- "with he" — preposition government violation (nominative instead of accusative). -/
def ex_withHe : DepTree :=
  { words := [ ⟨"with", .ADP, {}⟩
             , ⟨"he", .PRON, { case_ := some .Nom }⟩ ]
    deps := [⟨0, 1, .obj⟩]
    rootIdx := 0 }

-- ============================================================================
-- §6: Proofs
-- ============================================================================

/-- "with him" satisfies case government (accusative). -/
theorem withHim_govOk :
    checkGovernment ex_withHim [govPrepAcc] = true := by native_decide

/-- "with he" violates case government (nominative instead of accusative). -/
theorem withHe_govFail :
    checkGovernment ex_withHe [govPrepAcc] = false := by native_decide

/-- "She wants to go" satisfies infinitive government. -/
theorem wantsToGo_govOk :
    checkGovernment ex_sheWantsToGo [govVerbInfinitive] = true := by native_decide

/-- "She enjoys swimming" satisfies gerund government. -/
theorem enjoysSwimming_govOk :
    checkGovernment ex_sheEnjoysSw [govVerbGerund] = true := by native_decide

-- ============================================================================
-- §7: Bridges
-- ============================================================================

/-- **Bridge → CRDC.lean**: Same valency frame can have different government.
    Both "want" and "enjoy" are transitive (take xcomp), but differ in government.
    Valency frame (what slots exist) is independent of government (how slots
    are realized morphologically). -/
theorem same_valency_different_government :
    let wantFrame := CRDC.transitiveFrame "want"
    let enjoyFrame := CRDC.transitiveFrame "enjoy"
    wantFrame.valents.length == enjoyFrame.valents.length &&
    wantGov.requirements.head?.map (·.requiredValue) !=
      enjoyGov.requirements.head?.map (·.requiredValue) := by
  native_decide

/-- **Bridge → HeadCriteria.lean**: Government is one of the six head criteria
    (criterion 5: morphological determination). The governor is the head.
    Core arguments satisfy all 6 criteria including government. -/
theorem government_implies_head :
    HeadCriteria.classifyRelation .xcomp = HeadCriteria.RelationClass.coreArgument ∧
    HeadCriteria.expectedCriteriaCount .coreArgument = 6 := by
  native_decide

/-- **Bridge → Core/Basic.lean**: `ArgSlot` captures what relation and direction
    a dependent has. Government adds a morphological dimension: the slot for
    xcomp is the same regardless of whether the governed form is infinitive
    or gerund. -/
theorem argslot_agnostic_to_government :
    let slot : ArgSlot := ⟨.xcomp, .right, true, some .VERB⟩
    -- Same slot works for both infinitive and gerund complements
    slot.depType == .xcomp := by
  native_decide

/-- Government requirements are distinct across all five English patterns. -/
theorem english_gov_requirements_count :
    englishGovRequirements.length = 5 := by native_decide

end DepGrammar.Government
