import Linglib.Data.UD.Basic
import Linglib.Features.WordOrder

/-!
# Clause chaining

[sarvasy-aikhenvald-2025]

Typology of clause chaining: multi-clause constructions in which one or
more **medial** clauses (dependent, morphologically reduced) combine
with a single **final** clause (independent, fully inflected) that
supplies tense, mood, and often agreement for the whole chain. Chaining
is the prototypical *cosubordinate* combining scheme
(`Clause.CombiningScheme`): the medial clause is dependent but not
embedded ([foley-r-d-van-valin-1984]; [longacre-2007]). Anchors:
[sarvasy-aikhenvald-2025] and [de-vries-2025], with per-language
bundles and generalizations in `Studies/SarvasyAikhenvald2025.lean`.

## Main definitions

* `Clause.CombiningScheme` (+ `Embedded`, `Dependent`) — the
  [scancarelli-2003] combination schemes
* `ClauseStatus`, `ChainDirection` — medial/final and chain order
* `CategoryRetention`, `MedialMorphProfile` — the medial verb's
  per-category finiteness profile
* `SRSystem`, `SRTarget`, `SRMarkedness` — switch-reference
* `InterclauseRelation` — marked interclausal semantic relations
* `BridgingType` — discourse bridging across chain boundaries
* `System` — a language's clause-chaining system; per-language
  instances live in `Studies/SarvasyAikhenvald2025.lean`
-/

namespace Clause

/-! ### Combining schemes -/

/-- How a clause combines with its neighbors into a larger structure
    ([scancarelli-2003]): relatively independent conjuncts, dependence
    on a main clause, chained cosubordination (dependent but not
    embedded, [foley-r-d-van-valin-1984]), or serialization with the
    relationship left unmarked. Languages differ in which schemes they
    use at all. -/
inductive CombiningScheme where
  | coordinate
  | subordinate
  | cosubordinate
  | serial
  deriving DecidableEq, Repr

namespace CombiningScheme

/-- The dependent clause is embedded as a syntactic constituent of the
    other. -/
def Embedded (s : CombiningScheme) : Prop := s = subordinate

instance : DecidablePred Embedded := fun _ =>
  inferInstanceAs (Decidable (_ = _))

/-- The dependent clause is morphologically reduced (cannot stand
    alone). -/
def Dependent (s : CombiningScheme) : Prop :=
  s = subordinate ∨ s = cosubordinate

instance : DecidablePred Dependent := fun _ =>
  inferInstanceAs (Decidable (_ ∨ _))

end CombiningScheme

namespace Chaining

/-- Clause chaining is cosubordination — dependent but not embedded
    ([foley-r-d-van-valin-1984]). -/
def scheme : CombiningScheme := .cosubordinate

/-! ### Clause status and chain direction -/

/-- Structural status of a clause within a chain. -/
inductive ClauseStatus where
  /-- Dependent clause with reduced morphology. Typically carries
      converbal or participial marking (UD `VerbForm.Conv`); may encode
      switch-reference and interclausal relations but lacks full
      tense/agreement. -/
  | medial
  /-- Independent clause with full inflection. Supplies tense, mood,
      and often agreement for the entire chain; exactly one per
      chain. -/
  | final
  deriving DecidableEq, Repr, Inhabited

/-- Linear order of medial and final clauses
    ([sarvasy-aikhenvald-2025] §1.2). -/
inductive ChainDirection where
  /-- Medial clauses precede the final clause — by far the most common,
      strongly correlated with verb-final word order (Nungon, Turkish,
      Korean, Manambu, Ku Waru). -/
  | medialFinal
  /-- An initial independent clause precedes medial dependent clauses —
      rare, attested in some verb-initial languages (Barai). -/
  | initialMedial
  deriving DecidableEq, Repr, Inhabited

/-- Predicted head direction: the final verb determines the chain's TAM
    and patterns as its head, so chain direction mirrors the language's
    head direction ([dryer-1992]-style correlation;
    [sarvasy-aikhenvald-2025] §1.2). -/
def ChainDirection.predictedHeadDirection : ChainDirection → HeadDirection
  | .medialFinal => .headFinal
  | .initialMedial => .headInitial

/-! ### Medial-verb morphology -/

/-- How much of a morphological category a medial verb retains relative
    to independent verbs — the three-point scale `absent < restricted <
    full` ([sarvasy-aikhenvald-2025] §§1.3–1.5; [de-vries-2025] §2). -/
inductive CategoryRetention where
  /-- Unmarked on medial verbs; the value is inherited from the final
      verb (Nungon medial verbs lack tense entirely). -/
  | absent
  /-- Fewer values than independent verbs (e.g. binary realis/irrealis
      rather than a full mood paradigm). -/
  | restricted
  /-- The same range of values as independent verbs (Turkish converbs
      retain aspect). -/
  | full
  deriving DecidableEq, Repr, Inhabited

/-- Position on the retention scale. -/
def CategoryRetention.rank : CategoryRetention → Nat
  | .absent => 0
  | .restricted => 1
  | .full => 2

/-- The retention scale as a linear order: `absent < restricted <
    full`. -/
instance : LinearOrder CategoryRetention :=
  .lift' CategoryRetention.rank fun a b => by
    cases a <;> cases b <;> simp [CategoryRetention.rank]

/-- `absent` is the bottom of the retention scale. -/
theorem CategoryRetention.absent_le (r : CategoryRetention) :
    absent ≤ r := by cases r <;> decide

/-- Morphological profile of medial verbs along five TAM dimensions —
    a per-category finiteness vector, of which the binary
    finite/non-finite cut is a coarsening. -/
structure MedialMorphProfile where
  /-- Tense (absent in Nungon and Ku Waru; restricted in Manambu; full
      in some Turkic and Caucasian languages). -/
  tense : CategoryRetention
  /-- Subject agreement (often inherited from the final verb under
      same-subject marking). -/
  agreement : CategoryRetention
  /-- Mood (typically at most a binary realis/irrealis split). -/
  mood : CategoryRetention
  /-- Independent negation of the medial clause (some languages
      restrict negation to the final clause, so polarity scopes over
      the chain). -/
  polarity : CategoryRetention
  /-- Aspect (some languages retain perfective/imperfective to
      distinguish completed vs ongoing subevents). -/
  aspect : CategoryRetention
  deriving Repr, DecidableEq

namespace MedialMorphProfile

variable (p : MedialMorphProfile)

/-- Every category is absent: a bare converb. -/
def MaximallyReduced : Prop :=
  p.tense = .absent ∧ p.agreement = .absent ∧ p.mood = .absent ∧
    p.polarity = .absent ∧ p.aspect = .absent

instance : DecidablePred MaximallyReduced := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- Every category is full: the profile of an independent verb (though
    a medial verb still lacks illocutionary force). -/
def FullyRetained : Prop :=
  p.tense = .full ∧ p.agreement = .full ∧ p.mood = .full ∧
    p.polarity = .full ∧ p.aspect = .full

instance : DecidablePred FullyRetained := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- Expected UD verb form for a medial verb with this profile: converb
    unless fully retained. -/
def udVerbForm : UD.VerbForm :=
  if p.FullyRetained then .Fin else .Conv

end MedialMorphProfile

/-! ### Switch-reference -/

/-- Type of switch-reference system: morphology on medial verbs
    tracking referential continuity across clause boundaries —
    orthogonal to binding theory, which constrains intra-clausal
    coreference configurationally ([sarvasy-aikhenvald-2025] §§1.4–1.5,
    §3; [de-vries-2025] §§3–4). -/
inductive SRSystem where
  /-- No SR morphology; the language may still chain (Korean, Turkish,
      Japanese). -/
  | none
  /-- Binary same-subject vs different-subject marking — the canonical
      system (Nungon, Ku Waru, many Papuan and Amerindian languages). -/
  | ssDs
  /-- SS/DS fused with temporal relation: SS-sequential,
      SS-simultaneous, DS-sequential, DS-simultaneous as distinct forms
      (Nungon, Amele, many Trans-New Guinea languages). -/
  | ssDsTemporal
  /-- Tracks more than one argument (e.g. subject and object) — rare
      (Panoan). -/
  | multiTrack
  deriving DecidableEq, Repr, Inhabited

/-- What the SR system tracks. -/
inductive SRTarget where
  /-- Syntactic subject only — the canonical pattern. -/
  | subjectOnly
  /-- Subject and object — rare (some Panoan languages). -/
  | subjectAndObject
  /-- The topical participant, determined by discourse prominence
      rather than grammatical function (Greater Awyu,
      [de-vries-2025] §4.4). -/
  | topicBased
  deriving DecidableEq, Repr, Inhabited

/-- Markedness asymmetry between the SS and DS forms. Subject
    continuity is the discourse default, so SS is usually the unmarked
    member. -/
inductive SRMarkedness where
  /-- SS shorter, zero, or suffix-only; DS overtly marked — the
      dominant pattern. -/
  | ssUnmarked
  /-- DS unmarked — rare. -/
  | dsUnmarked
  /-- Both overtly marked with comparable weight. -/
  | symmetric
  deriving DecidableEq, Repr, Inhabited

/-! ### Interclausal relations and bridging -/

/-- Semantic relation between a medial clause and the next clause,
    encoded on the medial verb, inferred, or signaled by the SR system
    ([sarvasy-aikhenvald-2025] §1.4; [longacre-2007]). -/
inductive InterclauseRelation where
  | sequential    -- medial event precedes next event (iconic order)
  | simultaneous  -- medial event overlaps the next event
  | causal        -- medial event is reason for the next event
  | conditional   -- medial event is condition for the next event
  | concessive    -- medial event holds despite the next event
  | manner        -- medial event specifies how the next event occurs
  | contrastive   -- the events contrast
  | additive      -- added without temporal or causal import
  | purpose       -- medial event is the purpose of the next event
  deriving DecidableEq, Repr, Inhabited

/-- The temporal relations — exactly the ones SR morphology can encode
    without additional marking (`SRSystem.ssDsTemporal`). -/
def InterclauseRelation.Temporal (r : InterclauseRelation) : Prop :=
  r = .sequential ∨ r = .simultaneous

instance : DecidablePred InterclauseRelation.Temporal :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Discourse bridging constructions spanning chain boundaries,
    characteristic of oral narrative ([sarvasy-aikhenvald-2025] §1.6,
    §3.3). -/
inductive BridgingType where
  /-- Recapitulative (tail-head) linkage: the first medial clause of a
      new chain repeats the final clause of the preceding one (Nungon,
      Ku Waru). -/
  | recapitulative
  /-- Summary linkage: a generic verb ('do', 'say') summarizes the
      preceding episode (Ku Waru, Manambu). -/
  | summary
  deriving DecidableEq, Repr, Inhabited

/-! ### The per-language bundle -/

/-- A language's clause-chaining system: chain structure,
    switch-reference, medial morphology, marked relations, and
    bridging. Per-language instances and generalizations over them
    live in `Studies/SarvasyAikhenvald2025.lean`. -/
structure System where
  /-- Linear order of medial and final clauses. -/
  direction : ChainDirection
  /-- Type of switch-reference system, if any. -/
  srSystem : SRSystem
  /-- What SR tracks, when present. -/
  srTarget : Option SRTarget
  /-- Whether SR marking is obligatory on every medial verb. -/
  srObligatory : Bool
  /-- Markedness asymmetry of the SR system, when recorded. -/
  srMarkedness : Option SRMarkedness
  /-- Morphological profile of medial verbs. -/
  medialMorph : MedialMorphProfile
  /-- Interclausal relations grammatically marked on medial verbs. -/
  relationsMarked : List InterclauseRelation
  /-- Recapitulative (tail-head) linkage attested. -/
  hasRecapLinkage : Bool
  /-- Summary linkage attested. -/
  hasSummaryLinkage : Bool
  /-- Medial clauses can stand without a final clause — the
      non-canonical stand-alone medial ([sarvasy-2015]). -/
  medialCanStandAlone : Bool
  deriving Repr, BEq

namespace System

variable (p : System)

/-- The language has an SR system. -/
def hasSR : Bool := p.srSystem != .none

/-- Medial tense is inherited from the final verb (no medial tense
    marking). -/
def tenseFromFinalVerb : Bool := p.medialMorph.tense == .absent

/-- Some discourse bridging construction is attested. -/
def hasBridging : Bool := p.hasRecapLinkage || p.hasSummaryLinkage

/-- Temporal relations are encoded by the SR morphology itself. -/
def temporalViaSR : Bool := p.srSystem == .ssDsTemporal

/-- Expected UD verb form for this language's medial verbs. -/
def medialVerbForm : UD.VerbForm := p.medialMorph.udVerbForm

end System

end Chaining

end Clause
