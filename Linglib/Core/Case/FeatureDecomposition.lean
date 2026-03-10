import Linglib.Core.Case.Basic

/-!
# Case Feature Decomposition @cite{anderson-jm-2006}

@cite{anderson-jm-2006} "Modern Grammars of Case" (Ch. 6) develops a localist
case grammar (LCG) in which all semantic relations decompose into combinations
of three first-order case features:

- **abs** (absolutive): holistic participant — the entity that participates
  as a whole in the predication. Semantically the least specific relation;
  every predication is assumed to have an absolutive.
- **src** (source/ergative): first-order source — the origin of action or
  force. Anderson's "ergative". In spatial contexts, the source of motion.
- **loc** (locative): place/location — the spatial or abstract location.

These features combine freely, yielding up to 8 possible argument roles.
The four SIMPLE case relations are (eq. 11):

| Features   | Relation   | Typical role       |
|------------|------------|--------------------|
| ∅          | abs        | patient/theme      |
| {src}      | source/erg | agent              |
| {loc}      | locative   | location           |
| {loc,src²} | ablative   | spatial source      |

where `src²` denotes second-order source subordinated to loc, distinct from
first-order src. Second-order features are not separately represented in
this flat model — ablative appears as just `loc`.

## Complex roles (argument-level combinations)

Arguments can bear COMBINATIONS of first-order features (§6.2–6.3):

- **Agent**: src — first-order source alone (eq. 39a: "Bill read the book")
- **Experiencer**: src + loc — locative source (eq. 39h: "Bill knew the answer")
- **Contactive/patient**: abs + loc — located affected entity (eq. 22)
- **Self-mover**: abs + src — affected source (eq. 39c: "Bill flew to China")

## Subject selection hierarchy (eq. 38')

Anderson **directly states** the hierarchy — it is NOT derived from feature
cardinality:

    erg > abs

First-order source (src) outranks absolutive. The argument with `src`
becomes subject; if no argument has `src`, the absolutive becomes subject.

Subject formation (eq. 40): absolutive ⇒ absolutive{erg}. When an absolutive
is selected as subject, it acquires the ergative feature — assimilatory
neutralization.

## Relation to Blake and Caha

- Blake's typological hierarchy (`Core.Case.Hierarchy`) and Anderson's
  hierarchy are **concordant** on core cases.
- Caha's containment hierarchy (`Core.Case.Containment`) operates at a
  different level (morphosyntactic form, not semantic features).
-/

namespace Core

-- ============================================================================
-- § 1: Case Features
-- ============================================================================

/-- Anderson's three first-order case features (@cite{anderson-jm-2006}, Ch. 6).

    The three features are the primitives from which all semantic relations
    are composed. Their names reflect Anderson's localist tradition. -/
inductive CaseFeature where
  /-- Absolutive: holistic participant, the affected/located entity. -/
  | abs
  /-- Source/ergative: the origin of action or force (first-order). -/
  | src
  /-- Locative: place or spatial/abstract location. -/
  | loc
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Case Relations (Feature Bundles)
-- ============================================================================

/-- An argument's case specification: a bundle of first-order features
    (@cite{anderson-jm-2006}, Ch. 6).

    Represented as three Bools for computational tractability.
    The 8 possible bundles include both simple case relations (abs, erg, loc)
    and complex argument roles (abs+src, src+loc, abs+loc, abs+src+loc).

    Second-order features ({goal}, {source} subordinated to loc/abs) are
    not separately represented. In particular, ablative (loc{source}) and
    plain locative (loc) are both `⟨false, false, true⟩`. This is an
    acknowledged simplification: second-order source does not participate
    in subject selection, so the flat representation suffices for linking. -/
structure CaseRelation where
  /-- Does this argument bear the absolutive feature? -/
  abs : Bool
  /-- Does this argument bear the source/ergative feature (first-order)? -/
  src : Bool
  /-- Does this argument bear the locative feature? -/
  loc : Bool
  deriving DecidableEq, BEq, Repr, Inhabited

-- ============================================================================
-- § 3: Named Case Relations
-- ============================================================================

/-- ∅: no features. The semantically empty base. -/
def CaseRelation.neutral : CaseRelation := ⟨false, false, false⟩

/-- {abs}: absolutive alone. Patient/theme — affected entity. -/
def CaseRelation.absolutive : CaseRelation := ⟨true, false, false⟩

/-- {src}: source/ergative. Agent — source of action. -/
def CaseRelation.ergative : CaseRelation := ⟨false, true, false⟩

/-- {loc}: locative. Place/location (also covers ablative = loc{source}
    in this flat representation, since second-order source is not tracked). -/
def CaseRelation.locative : CaseRelation := ⟨false, false, true⟩

/-- {abs, src}: absolutive + source. Self-moving agent — both the
    source of action AND the affected/moving entity.
    "Bill flew to China" (eq. 39c). -/
def CaseRelation.srcAbs : CaseRelation := ⟨true, true, false⟩

/-- {src, loc}: source + locative. Experiencer — locative source.
    "Bill knew the answer" (eq. 39h). The experience is "located at"
    the experiencer, who is also the source of the knowing.
    Anderson's notation: E (= erg,loc). -/
def CaseRelation.srcLoc : CaseRelation := ⟨false, true, true⟩

/-- {abs, loc}: absolutive + locative. Contactive — the entity that
    is simultaneously located and holistically affected.
    "The ferry reached Patra" (20a); Contactive = abs,loc (eq. 22). -/
def CaseRelation.absLoc : CaseRelation := ⟨true, false, true⟩

/-- {abs, src, loc}: all three features. Complex experiencer/sufferer.
    "Phil suffered from asthma" (eq. 34). -/
def CaseRelation.absSrcLoc : CaseRelation := ⟨true, true, true⟩

-- ============================================================================
-- § 4: Subject Selection Hierarchy
-- ============================================================================

/-- The subject selection rank of a case relation on Anderson's hierarchy
    (eq. 38', Ch. 6).

    Anderson DIRECTLY STATES this hierarchy — it is NOT derived from feature
    cardinality. The rule: first-order source (src/erg) outranks absolutive.
    If an argument has src, it becomes subject. If no argument has src,
    the absolutive becomes subject.

    - rank 2: any relation containing src (agent, experiencer, etc.)
    - rank 1: any relation containing abs but not src (patient, theme)
    - rank 0: locative without abs or src (pure spatial, not a subject) -/
def CaseRelation.subjectRank (cr : CaseRelation) : Nat :=
  if cr.src then 2 else if cr.abs then 1 else 0

-- ============================================================================
-- § 5: Hierarchy Theorems
-- ============================================================================

/-- Source/ergative (agent) has rank 2 — highest. -/
theorem ergative_rank : CaseRelation.ergative.subjectRank = 2 := rfl

/-- Absolutive (patient) has rank 1. -/
theorem absolutive_rank : CaseRelation.absolutive.subjectRank = 1 := rfl

/-- Pure locative has rank 0 — not a subject candidate. -/
theorem locative_rank : CaseRelation.locative.subjectRank = 0 := rfl

/-- Neutral has rank 0. -/
theorem neutral_rank : CaseRelation.neutral.subjectRank = 0 := rfl

/-- Agent outranks patient: erg > abs. This IS Anderson's hierarchy. -/
theorem erg_above_abs :
    CaseRelation.ergative.subjectRank > CaseRelation.absolutive.subjectRank := by
  decide

/-- Patient outranks pure locative: abs > loc. -/
theorem abs_above_loc :
    CaseRelation.absolutive.subjectRank > CaseRelation.locative.subjectRank := by
  decide

/-- Experiencer (src+loc) has same rank as agent (src): both rank 2.
    Anderson DISTINGUISHES them (different feature bundles) but they are
    at the SAME tier for subject selection (both contain src). -/
theorem experiencer_agent_same_rank :
    CaseRelation.srcLoc.subjectRank = CaseRelation.ergative.subjectRank := rfl

/-- Self-moving agent (abs+src) has rank 2, same as simple agent. -/
theorem selfMover_agent_same_rank :
    CaseRelation.srcAbs.subjectRank = CaseRelation.ergative.subjectRank := rfl

/-- Contactive (abs+loc) has rank 1, same as simple absolutive. -/
theorem contactive_abs_same_rank :
    CaseRelation.absLoc.subjectRank = CaseRelation.absolutive.subjectRank := rfl

-- ============================================================================
-- § 5b: Subject Selection is Determined by src
-- ============================================================================

/-- Anderson's hierarchy (eq. 38') entails that subject selection depends
    ONLY on the src feature — loc has no effect on subjectRank.
    This captures his direct statement: "erg > abs". -/
theorem src_determines_subject_rank (cr : CaseRelation) (h : cr.src = true) :
    cr.subjectRank = 2 := by simp [CaseRelation.subjectRank, h]

/-- Absence of src with abs yields rank 1. -/
theorem abs_without_src_rank (cr : CaseRelation)
    (h1 : cr.src = false) (h2 : cr.abs = true) :
    cr.subjectRank = 1 := by simp [CaseRelation.subjectRank, h1, h2]

-- ============================================================================
-- § 6: Feature Containment
-- ============================================================================

/-- Does `inner` have a subset of `outer`'s features? -/
def CaseRelation.isSubsetOf (inner outer : CaseRelation) : Bool :=
  (!inner.abs || outer.abs) && (!inner.src || outer.src) && (!inner.loc || outer.loc)

/-- {abs, src, loc} contains every case relation. -/
theorem absSrcLoc_is_top (cr : CaseRelation) :
    cr.isSubsetOf .absSrcLoc = true := by
  cases cr with | mk a s l => cases a <;> cases s <;> cases l <;> rfl

/-- ∅ is contained in every case relation. -/
theorem neutral_is_bottom (cr : CaseRelation) :
    CaseRelation.neutral.isSubsetOf cr = true := by
  cases cr with | mk a s l => cases a <;> cases s <;> cases l <;> rfl

-- ============================================================================
-- § 7: Exhaustive Enumeration
-- ============================================================================

/-- All 8 case relations, ordered by subject rank (highest first). -/
def CaseRelation.all : List CaseRelation :=
  [.absSrcLoc, .srcAbs, .srcLoc, .ergative,
   .absLoc, .absolutive, .locative, .neutral]

theorem CaseRelation.all_length : CaseRelation.all.length = 8 := rfl

/-- Membership check for decidable enumeration. -/
def CaseRelation.inAll (cr : CaseRelation) : Bool :=
  CaseRelation.all.any (· == cr)

/-- Every case relation is in the enumeration. -/
theorem CaseRelation.all_complete (cr : CaseRelation) :
    cr.inAll = true := by
  cases cr with | mk a s l => cases a <;> cases s <;> cases l <;> native_decide

-- ============================================================================
-- § 8: Scenario (Predicate Argument Structure)
-- ============================================================================

/-- A predicate's **scenario** (@cite{anderson-jm-2006}, Ch. 6): the case
    relations assigned to its arguments, listed with the subject first
    (highest subjectRank), then the object.

    Eq. 39 shows Anderson's derivations for six English verb types:
    - "Bill read the book": [erg, abs] — agent + patient
    - "Bill fell to the ground": [abs, loc] — theme + locative goal
    - "Bill flew to China": [srcAbs, loc] — self-mover + goal
    - "Bill knew the answer": [srcLoc, abs] — experiencer + stimulus
    - "Bill ran": [erg] — unergative agent -/
structure Scenario where
  relations : List CaseRelation
  deriving Repr

/-- Number of arguments in the scenario. -/
def Scenario.arity (s : Scenario) : Nat := s.relations.length

/-- Case relation of the subject (highest-ranked argument). -/
def Scenario.subjectRelation (s : Scenario) : Option CaseRelation :=
  s.relations.head?

/-- Case relation of the direct object (second argument). -/
def Scenario.objectRelation (s : Scenario) : Option CaseRelation :=
  match s.relations with
  | _ :: cr :: _ => some cr
  | _ => none

-- ============================================================================
-- § 9: Anderson's Verb Derivations (eq. 39)
-- ============================================================================

/-- "Bill read the book" (eq. 39a): erg + abs.
    Agent (src) acts on patient (abs). Agent is subject: src > abs. -/
def Scenario.transitive : Scenario := ⟨[.ergative, .absolutive]⟩

/-- "Bill ran" (unergative): erg alone.
    Agent only, no patient. -/
def Scenario.unergative : Scenario := ⟨[.ergative]⟩

/-- "Bill fell to the ground" (eq. 39b): abs + loc{goal}.
    Theme (abs) moves to locative goal. No src, so abs is subject. -/
def Scenario.unaccusative : Scenario := ⟨[.absolutive, .locative]⟩

/-- "Bill flew to China" (eq. 39c): abs,erg + loc{goal}.
    Self-moving agent (abs+src) travels to goal. Has src → subject. -/
def Scenario.selfMoving : Scenario := ⟨[.srcAbs, .locative]⟩

/-- "Bill knew the answer" (eq. 39h): E + abs = erg,loc + abs.
    Experiencer (src+loc) knows stimulus (abs). Has src → subject. -/
def Scenario.experiencer : Scenario := ⟨[.srcLoc, .absolutive]⟩

-- ============================================================================
-- § 10: Scenario Verification
-- ============================================================================

/-- Transitive: subject is erg (agent), object is abs (patient). -/
theorem transitive_subject_object :
    Scenario.transitive.subjectRelation = some .ergative ∧
    Scenario.transitive.objectRelation = some .absolutive := ⟨rfl, rfl⟩

/-- Unergative: subject is erg, no object. -/
theorem unergative_subject_only :
    Scenario.unergative.subjectRelation = some .ergative ∧
    Scenario.unergative.objectRelation = none := ⟨rfl, rfl⟩

/-- Unaccusative: subject is abs, second argument is loc. -/
theorem unaccusative_subject_loc :
    Scenario.unaccusative.subjectRelation = some .absolutive ∧
    Scenario.unaccusative.objectRelation = some .locative := ⟨rfl, rfl⟩

/-- Self-moving: subject is abs+src, second argument is loc. -/
theorem selfMoving_subject :
    Scenario.selfMoving.subjectRelation = some .srcAbs ∧
    Scenario.selfMoving.objectRelation = some .locative := ⟨rfl, rfl⟩

/-- Experiencer: subject is src+loc, object is abs. -/
theorem experiencer_subject_object :
    Scenario.experiencer.subjectRelation = some .srcLoc ∧
    Scenario.experiencer.objectRelation = some .absolutive := ⟨rfl, rfl⟩

/-- In a transitive, the subject (erg) outranks the object (abs). -/
theorem transitive_subject_outranks_object :
    CaseRelation.ergative.subjectRank > CaseRelation.absolutive.subjectRank := by
  decide

/-- Unergative and unaccusative have different subject case relations:
    unergative = src (agentive), unaccusative = abs (patient-like). -/
theorem unergative_unaccusative_differ :
    Scenario.unergative.subjectRelation ≠
    Scenario.unaccusative.subjectRelation := by decide

-- ============================================================================
-- § 11: Morphological Case → Case Relation
-- ============================================================================

/-- Canonical mapping from Blake's morphological case inventory to
    Anderson's case-feature bundles (@cite{anderson-jm-2006}, Ch. 6).

    NOM and ERG both map to abs+src: subject formation (eq. 40) means
    all subjects acquire the src feature, so nominative = abs{erg}.
    ACC and ABS map to abs (goal-absolutive for ACC, plain abs for ABS).

    Peripheral spatial cases: ABL → loc (second-order source not tracked),
    LOC → loc, INST → src (source of force). -/
def Case.toCaseRelation : Case → Option CaseRelation
  | .nom  => some .srcAbs     -- subject = abs{erg} by subject formation
  | .acc  => some .absolutive  -- abs{goal} (goal absolutive)
  | .erg  => some .srcAbs     -- agent in ergative = src + abs
  | .abs  => some .absolutive  -- S/P in ergative = abs
  | .abl  => some .locative   -- loc{source} (second-order src)
  | .loc  => some .locative   -- loc (place)
  | .inst => some .ergative   -- src (source of force)
  | _     => none

/-- NOM and ERG map to the same case relation: abs+src. -/
theorem Case.nom_erg_same_relation :
    Case.toCaseRelation .nom = Case.toCaseRelation .erg := rfl

/-- ACC and ABS map to the same case relation: abs. -/
theorem Case.acc_abs_same_relation :
    Case.toCaseRelation .acc = Case.toCaseRelation .abs := rfl

end Core
