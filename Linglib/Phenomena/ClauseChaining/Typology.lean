import Linglib.Core.Lexical.UD
import Linglib.Core.Lexical.Word

/-! # Clause Chaining Typology @cite{sarvasy-aikhenvald-2025} @cite{foley-r-d-van-valin-1984} @cite{longacre-2007}

Cross-linguistic typology of clause chaining: multi-clause constructions in which
one or more **medial** (dependent, morphologically reduced) clauses combine with
a single **final** (independent, fully inflected) clause. The final verb supplies
tense, mood, and often agreement for the entire chain.

Clause chaining is typologically distinct from both coordination (syntactically
equal independent clauses) and subordination (embedded dependent clauses).
Following @cite{foley-r-d-van-valin-1984} and @cite{longacre-2007}, chained medial clauses
are **dependent but not embedded** — what Role & Reference Grammar calls
"cosubordination."

## Core structural asymmetry
@cite{chomsky-1981} @cite{dryer-1992} @cite{givon-1983}


The medial/final asymmetry is the defining property. Medial verbs carry a
**reduced** morphological paradigm: some TAM categories are absent or restricted,
while the final verb is fully inflected. The final verb's TAM values scope over
the entire chain. This creates a characteristic "head-final scope" pattern where
interpretive parameters flow rightward (in medial-final chains) from the final
verb to all preceding medial clauses.

## Switch-reference

Many clause-chaining languages mark **switch-reference** (SR) on medial verbs:
morphology tracking whether the subject of the next clause is the same as (SS)
or different from (DS) the current clause's subject. SR is orthogonal to binding
theory: binding constrains intra-clausal coreference via syntactic
configuration, while SR tracks inter-clausal participant continuity via verbal
morphology. Some languages (Greater Awyu) track topical participants rather than
syntactic subjects, revealing SR as discourse-pragmatic rather than purely
syntactic.

## Typological parameters

The formalization captures five parameter dimensions:

| Dimension | Types | Examples |
|-----------|-------|----------|
| Chain direction | medial-final, initial-medial | most SOV langs, some V-initial |
| SR system | none, SS/DS, SS/DS+temporal, multi-track | Korean, Nungon, Korowai |
| Medial morphology | per-category retention (full/restricted/absent) | 5 TAM dimensions |
| Interclausal semantics | 9 relation types marked on medial verbs | sequential, simultaneous,... |
| Bridging constructions | recapitulative, summary | tail-head linkage, generic verb |

-/

namespace Phenomena.ClauseChaining.Typology

-- ============================================================================
-- § Clause status
-- ============================================================================

/-- Structural status of a clause within a chain.

    The medial/final asymmetry is the defining property of clause chaining:
    medial verbs have reduced morphology and depend on the final verb for
    full TAM interpretation. -/
inductive ClauseStatus where
  /-- Dependent clause with reduced morphology. Typically carries converbal
      or participial marking (UD `VerbForm.Conv`). May encode SR and
      interclausal semantic relations but lacks full tense/agreement. -/
  | medial
  /-- Independent clause with full inflection. Supplies tense, mood, and
      often agreement for the entire chain. Exactly one per chain. -/
  | final
  deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================================
-- § Chain directionality
-- ============================================================================

/-- Linear order of medial and final clauses.

    Medial-final order is overwhelmingly dominant, correlating strongly with
    verb-final (SOV/SOV-flexible) word order. Initial-medial order is rare,
    attested in some verb-initial languages. The correlation follows from the
    head-direction generalization: the final verb is the "head"
    of the chain, and its position mirrors the language's general head direction.

    @cite{sarvasy-aikhenvald-2025} §1.2. -/
inductive ChainDirection where
  /-- Medial clauses precede the final clause. By far the most common pattern,
      strongly correlated with verb-final (OV) word order.
      E.g., Nungon, Turkish, Korean, Japanese, Manambu, Ku Waru. -/
  | medialFinal
  /-- An initial independent clause precedes medial dependent clauses. Rare;
      attested in some verb-initial and SVO languages (e.g., Barai, some
      Papuan languages with initial-verb tendencies). -/
  | initialMedial
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Predicted head direction for a given chain direction.

    Medial-final chains place the "head" (final verb, which determines TAM
    for the chain) at the right edge — consistent with head-final languages.
    Initial-medial chains place it at the left edge — consistent with
    head-initial languages. -/
def ChainDirection.predictedHeadDirection : ChainDirection → HeadDirection
  | .medialFinal  => .headFinal
  | .initialMedial => .headInitial

-- ============================================================================
-- § Morphological reduction on medial verbs
-- ============================================================================

/-- How much of a morphological category a medial verb retains relative to
    independent (final) verbs.

    Medial verbs are characteristically "partially finite": they may retain some
    TAM distinctions while lacking others. This three-way scale captures the
    cross-linguistic variation. The ordering is full > restricted > absent.

    @cite{sarvasy-aikhenvald-2025} §§1.3-1.5; @cite{de-vries-2025} §2. -/
inductive CategoryRetention where
  /-- Full paradigm: medial verbs mark this category with the same range of
      values as independent verbs. E.g., Turkish converbs retain aspect. -/
  | full
  /-- Reduced paradigm: medial verbs distinguish fewer values than independent
      verbs. E.g., only realis/irrealis (binary mood), not the full mood
      paradigm; or only perfective/imperfective, not all aspect values. -/
  | restricted
  /-- Category unmarked: medial verbs carry no morphology for this category.
      Its value is inherited from the final verb's specification (scope).
      E.g., Nungon medial verbs lack tense entirely. -/
  | absent
  deriving DecidableEq, Repr, BEq, Inhabited

instance : LE CategoryRetention where
  le a b := match a, b with
    | .absent, _ => True
    | .restricted, .restricted | .restricted, .full => True
    | .full, .full => True
    | _, _ => False

instance : DecidableRel (α := CategoryRetention) (· ≤ ·) := λ a b =>
  match a, b with
  | .absent, _ => isTrue trivial
  | .restricted, .restricted | .restricted, .full => isTrue trivial
  | .full, .full => isTrue trivial
  | .full, .absent | .full, .restricted | .restricted, .absent =>
    isFalse (λ h => nomatch h)

/-- Absent ≤ everything: the bottom of the retention scale. -/
theorem absent_le (r : CategoryRetention) : .absent ≤ r := trivial

/-- Morphological profile of medial verbs along five TAM dimensions.

    Each dimension records how much of the category's paradigm is retained on
    medial verbs. A fully reduced medial verb (all `.absent`) is a bare converb;
    a fully retained profile (all `.full`) approaches an independent verb.

    This structure is effectively a 5-dimensional finiteness vector. The
    traditional binary finite/non-finite distinction is a coarsening that
    collapses all five dimensions into one bit. -/
structure MedialMorphProfile where
  /-- Tense marking. Absent in many Papuan languages (Nungon, Ku Waru);
      restricted in some (Manambu: only yesterday/today/remote); full in
      some Turkic and Caucasian languages. -/
  tense     : CategoryRetention
  /-- Subject agreement. Often absent on medial verbs (agreement inherited
      from final verb when SS); sometimes restricted to person only. -/
  agreement : CategoryRetention
  /-- Mood distinctions. Typically restricted to a binary realis/irrealis
      split when present at all. Full mood paradigms on medial verbs are
      rare cross-linguistically. -/
  mood      : CategoryRetention
  /-- Independent negation. Whether medial clauses can be independently
      negated. Some languages restrict negation to the final clause only
      (polarity scopes over chain); others allow medial negation. -/
  polarity  : CategoryRetention
  /-- Aspectual distinctions. Some languages retain perfective/imperfective
      on medial verbs to distinguish completed vs. ongoing subevents. -/
  aspect    : CategoryRetention
  deriving Repr, BEq, DecidableEq

/-- Whether this profile represents maximal reduction (all categories absent). -/
def MedialMorphProfile.isMaximallyReduced (p : MedialMorphProfile) : Bool :=
  p.tense == .absent && p.agreement == .absent && p.mood == .absent &&
  p.polarity == .absent && p.aspect == .absent

/-- Whether this profile represents no reduction (all categories full). -/
def MedialMorphProfile.isFullyRetained (p : MedialMorphProfile) : Bool :=
  p.tense == .full && p.agreement == .full && p.mood == .full &&
  p.polarity == .full && p.aspect == .full

/-- Expected UD VerbForm for a medial verb given its morphological profile.

    Maximally or partially reduced medial verbs map to `VerbForm.Conv` (converb).
    Fully retained medial verbs approach `VerbForm.Fin`, though they still differ
    from independent verbs in lacking illocutionary force. -/
def MedialMorphProfile.udVerbForm (p : MedialMorphProfile) : UD.VerbForm :=
  if p.isFullyRetained then .Fin else .Conv

-- ============================================================================
-- § Switch-reference
-- ============================================================================

/-- Type of switch-reference system.

    SR is a morphological system on medial verbs that tracks referential
    continuity across clause boundaries. It is orthogonal to binding theory:
    binding constrains coreference within a clause via syntactic configuration
    (c-command); SR tracks coreference between clauses via verbal morphology.

    @cite{sarvasy-aikhenvald-2025} §§1.4-1.5; @cite{de-vries-2025} §§3-4;
    @cite{sarvasy-aikhenvald-2025} §3. -/
inductive SRSystem where
  /-- No SR morphology. The language may still have clause chaining (e.g.,
      Korean, Turkish, Japanese) but does not grammatically mark whether
      subjects corefer across clause boundaries. -/
  | none
  /-- Binary SS/DS distinction. Medial verbs carry morphology indicating
      same-subject (SS) or different-subject (DS) relative to the next
      clause. The canonical and most widespread SR system.
      E.g., Nungon, Ku Waru, many Papuan and Amerindian languages. -/
  | ssDs
  /-- SS/DS plus temporal relation encoding. Medial verb morphology
      simultaneously signals referential continuity and temporal relation
      (sequential vs. simultaneous). SS-sequential, SS-simultaneous,
      DS-sequential, DS-simultaneous are distinct forms.
      E.g., Nungon, Amele, many Trans-New Guinea languages. -/
  | ssDsTemporal
  /-- Multi-track SR. Tracks continuity of more than one argument: e.g.,
      subject and object, or subject and possessor. Rare.
      E.g., Panoan languages (subject+object tracking). -/
  | multiTrack
  deriving DecidableEq, Repr, BEq, Inhabited

/-- What participant role(s) SR tracks.

    Canonical SR tracks syntactic subjects. Some systems track topical
    participants (pragmatic, not syntactic) or multiple arguments. -/
inductive SRTarget where
  /-- Track syntactic subject only. The canonical and most widespread pattern.
      E.g., Nungon, Ku Waru, most Papuan and Amerindian languages. -/
  | subjectOnly
  /-- Track both subject and object. Rare.
      E.g., some Panoan languages. -/
  | subjectAndObject
  /-- Track the topical participant, which may not be the syntactic subject.
      The tracked referent is determined by discourse prominence rather than
      grammatical function.
      E.g., Greater Awyu languages (de Vries 2025 §4.4). -/
  | topicBased
  deriving DecidableEq, Repr, BEq, Inhabited

/-- SR marking asymmetry.

    Cross-linguistically, SS forms tend to be morphologically simpler (shorter,
    less marked) than DS forms. This asymmetry reflects the discourse-pragmatic
    default: subject continuity is the unmarked expectation in connected
    discourse. -/
inductive SRMarkedness where
  /-- SS is the morphologically unmarked member (shorter, zero, or suffix-only).
      DS carries overt marking. The cross-linguistically dominant pattern. -/
  | ssUnmarked
  /-- DS is the morphologically unmarked member. Rare. -/
  | dsUnmarked
  /-- SS and DS are both overtly marked with comparable morphological weight. -/
  | symmetric
  deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================================
-- § Interclausal semantic relations
-- ============================================================================

/-- Semantic relation between a medial clause and the next clause in the chain.

    These relations may be encoded on the medial verb (via dedicated morphology
    or converbal suffixes), inferred from context, or signaled by the SR system
    (e.g., SS-sequential vs. SS-simultaneous as distinct forms).

    @cite{sarvasy-aikhenvald-2025} §1.4; @cite{longacre-2007}. -/
inductive InterclauseRelation where
  | sequential    -- medial event precedes next event (iconic temporal order)
  | simultaneous  -- medial event overlaps temporally with next event
  | causal        -- medial event is reason/cause for next event
  | conditional   -- medial event is condition for next event
  | concessive    -- medial event holds despite next event (although/even though)
  | manner        -- medial event specifies how next event occurs
  | contrastive   -- medial and next events contrast (but/whereas)
  | additive      -- medial event added to next without temporal/causal import
  | purpose       -- medial event is purpose of next event (in order to)
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Whether a relation involves temporal ordering. -/
def InterclauseRelation.isTemporal : InterclauseRelation → Bool
  | .sequential   => true
  | .simultaneous => true
  | _             => false

/-- Whether a relation can be encoded purely via SR morphology
    (without a separate connective or adverbial suffix).
    In many Papuan languages, SR forms directly encode sequential vs.
    simultaneous, while other relations require additional marking. -/
def InterclauseRelation.encodableViaSR : InterclauseRelation → Bool
  | .sequential   => true
  | .simultaneous => true
  | _             => false

-- ============================================================================
-- § Bridging constructions
-- ============================================================================

/-- Discourse-level bridging constructions that span clause chain boundaries.

    These are characteristic of oral narrative in clause-chaining languages
    and serve to structure discourse into episodes.

    @cite{sarvasy-aikhenvald-2025} §1.6; de Vries (2005); @cite{sarvasy-aikhenvald-2025} §3.3. -/
inductive BridgingType where
  /-- Recapitulative (tail-head) linkage: the first medial clause of a new chain
      repeats (wholly or in reduced form) the final clause of the preceding chain.
      Creates cohesion across chain boundaries in oral narrative.
      E.g., Nungon, Ku Waru, many Trans-New Guinea languages. -/
  | recapitulative
  /-- Summary linkage: a generic verb form (typically 'do' or 'say') summarizes
      the entire preceding episode before the next chain begins.
      E.g., Ku Waru *ab-*, Manambu *a-yk-*. -/
  | summary
  deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================================
-- § Clause-linking strategy (shared vocabulary)
-- ============================================================================

/-- The three major clause-linking strategies, following @cite{foley-r-d-van-valin-1984}.

    This type provides shared vocabulary across the clause-combining phenomenon
    directories (Coordination, Complementation, FillerGap, ClauseChaining).
    The key insight: clause chaining is neither coordination nor subordination
    but a third strategy — dependent but not embedded. -/
inductive ClauseLinkingStrategy where
  /-- Coordination: syntactically equal, independent clauses joined by a
      conjunction or juxtaposition. Neither clause is embedded in the other.
      E.g., "John sang and Mary danced." -/
  | coordination
  /-- Subordination: one clause is embedded within the other as a syntactic
      constituent (complement, relative clause, adverbial clause). The
      embedded clause is both dependent and structurally contained.
      E.g., "I know [that John sang]." -/
  | subordination
  /-- Cosubordination: one clause is dependent on the other (reduced morphology,
      cannot stand alone) but is not embedded as a constituent. The medial clause
      is structurally adjacent, not contained within the final clause.
      Clause chaining is the prototypical instantiation.
      E.g., Nungon: "he having.come, she cooked" (medial + final). -/
  | cosubordination
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Clause chaining is cosubordination: dependent but not embedded. -/
def clauseChainingStrategy : ClauseLinkingStrategy := .cosubordination

/-- Whether the dependent clause is embedded as a syntactic constituent. -/
def ClauseLinkingStrategy.isEmbedded : ClauseLinkingStrategy → Bool
  | .subordination => true
  | _              => false

/-- Whether the dependent clause is morphologically reduced (non-independent). -/
def ClauseLinkingStrategy.isDependentReduced : ClauseLinkingStrategy → Bool
  | .subordination    => true
  | .cosubordination  => true
  | .coordination     => false

-- ============================================================================
-- § Language-level parameter bundle
-- ============================================================================

/-- Full clause chaining parameter bundle for a language.

    Captures the five major typological dimensions:
    1. Chain structure (direction, length, non-canonical possibilities)
    2. Switch-reference (system type, target, obligatoriness, markedness)
    3. Medial verb morphology (5-dimensional TAM retention profile)
    4. Interclausal semantics (which relations are grammatically marked)
    5. Discourse bridging (recapitulative and/or summary linkage) -/
structure ClauseChainingParams where
  /-- Linear order of medial and final clauses. -/
  direction           : ChainDirection
  /-- Type of switch-reference system (if any). -/
  srSystem            : SRSystem
  /-- What participant role(s) SR tracks (if SR exists). -/
  srTarget            : Option SRTarget
  /-- Whether SR marking is obligatory on every medial verb. -/
  srObligatory        : Bool
  /-- Markedness asymmetry in the SR system. -/
  srMarkedness        : Option SRMarkedness
  /-- Morphological profile of medial verbs. -/
  medialMorph         : MedialMorphProfile
  /-- Interclausal semantic relations grammatically marked on medial verbs. -/
  relationsMarked     : List InterclauseRelation
  /-- Whether recapitulative (tail-head) linkage is attested. -/
  hasRecapLinkage     : Bool
  /-- Whether summary linkage is attested. -/
  hasSummaryLinkage   : Bool
  /-- Whether medial clauses can occur without a final clause
      (non-canonical stand-alone medial; Sarvasy 2015). -/
  medialCanStandAlone : Bool
  deriving Repr, BEq

-- ============================================================================
-- § Key functions
-- ============================================================================

/-- Whether the language has any SR system. -/
def ClauseChainingParams.hasSR (p : ClauseChainingParams) : Bool :=
  p.srSystem != .none

/-- Whether tense on medial verbs is inherited from the final verb (scope).
    This is the case when medial verbs lack tense marking entirely. -/
def ClauseChainingParams.tenseFromFinalVerb (p : ClauseChainingParams) : Bool :=
  p.medialMorph.tense == .absent

/-- Whether the chain has any discourse bridging constructions. -/
def ClauseChainingParams.hasBridging (p : ClauseChainingParams) : Bool :=
  p.hasRecapLinkage || p.hasSummaryLinkage

/-- Whether temporal relations are encoded via SR morphology (as opposed to
    requiring separate adverbial marking). -/
def ClauseChainingParams.temporalViaSR (p : ClauseChainingParams) : Bool :=
  p.srSystem == .ssDsTemporal

/-- Expected UD VerbForm for medial verbs in this language. -/
def ClauseChainingParams.medialVerbForm (p : ClauseChainingParams) : UD.VerbForm :=
  p.medialMorph.udVerbForm

-- ============================================================================
-- § Invariant theorems
-- ============================================================================

/-- Clause chaining is cosubordination: dependent but not embedded. -/
theorem chaining_not_embedded :
    clauseChainingStrategy.isEmbedded = false := rfl

/-- Clause chaining involves dependent reduction (unlike coordination). -/
theorem chaining_is_dependent :
    clauseChainingStrategy.isDependentReduced = true := rfl

/-- Medial-final chains predict head-final word order. -/
theorem medialFinal_is_headFinal :
    ChainDirection.medialFinal.predictedHeadDirection = .headFinal := rfl

/-- Initial-medial chains predict head-initial word order. -/
theorem initialMedial_is_headInitial :
    ChainDirection.initialMedial.predictedHeadDirection = .headInitial := rfl

/-- A maximally reduced medial verb maps to UD converb. -/
theorem maxReduced_is_converb :
    (MedialMorphProfile.mk .absent .absent .absent .absent .absent).udVerbForm
    = UD.VerbForm.Conv := rfl

/-- A fully retained medial verb maps to UD finite. -/
theorem fullRetained_is_finite :
    (MedialMorphProfile.mk .full .full .full .full .full).udVerbForm
    = UD.VerbForm.Fin := rfl

/-- Temporal relations (sequential, simultaneous) are encodable via SR. -/
theorem sequential_encodable_via_sr :
    InterclauseRelation.sequential.encodableViaSR = true := rfl

theorem simultaneous_encodable_via_sr :
    InterclauseRelation.simultaneous.encodableViaSR = true := rfl

/-- Non-temporal relations require additional marking beyond SR. -/
theorem causal_not_sr_only :
    InterclauseRelation.causal.encodableViaSR = false := rfl

end Phenomena.ClauseChaining.Typology
