import Linglib.Semantics.ArgumentStructure.EntailmentProfile
import Linglib.Semantics.ArgumentStructure.Affectedness
import Linglib.Semantics.ArgumentStructure.Projection
import Linglib.Semantics.Lexical.LevinClassProfiles
import Linglib.Semantics.Lexical.DiathesisAlternation
import Linglib.Data.Examples.Levin1993

/-!
# [beavers-2010] The Structure of Lexical Meaning: Why Semantics Really Matters

Argument realization in direct/oblique alternations is governed not by event
structure but by **strength of truth conditions**. Direct realization encodes
monotonically stronger truth conditions than oblique realization. This is
captured by:

1. An **affectedness hierarchy** — four degrees of change, each an existential
   weakening of the last: quantized ⊃ nonquantized ⊃ potential ⊃ unspecified.

2. **L-thematic roles** — sets of implicationally related entailments. The
   three affectedness entailments produce a structured subset hierarchy
   with exactly 4 semantically non-vacuous roles (of 8 possible).

3. The **Morphosyntactic Alignment Principle (MAP)** — when an argument
   alternates between direct and oblique realization, the direct variant
   bears L-thematic role R and the oblique bears Q ⊆_M R (minimal weakening).

## Deepest theorem

`MAP_holds_all_alternations`: for every attested object/oblique alternation
in the data, the oblique role is the *next-weakest* (minimal, ⊆_M) weakening
of the direct role. The subset form (direct degree ≥ oblique degree) is the
derived corollary `MAP_subset` / `MapHolds.oblique_le`, via the substrate's
`AffectednessDegree` order.
-/

namespace Beavers2010

open ArgumentStructure
open Features.LevinClassProfiles
open ArgumentStructure.Affectedness (AffectednessDegree profileToDegree)
open Semantics.Lexical (DiathesisAlternation)

-- ════════════════════════════════════════════════════
-- § 2. L-Thematic Roles as Entailment Sets (§4.3)
-- ════════════════════════════════════════════════════

/-- An L-thematic role for patienthood: a set of the three affectedness
    entailments ([beavers-2010]'s reduction of Dowty's 5 P-Patient
    entailments). -/
structure PatientLRole where
  quantized    : Bool
  nonquantized : Bool
  potential    : Bool
  deriving DecidableEq, Repr

namespace PatientLRole

/-- An L-role is valid iff it respects the implicational chain
    quantized → nonquantized → potential. -/
def valid (r : PatientLRole) : Bool :=
  (!r.quantized || r.nonquantized) &&    -- q → nq
  (!r.nonquantized || r.potential)         -- nq → p

/-- The four valid L-thematic roles. -/
def quantizedRole : PatientLRole := ⟨true, true, true⟩
def nonquantizedRole : PatientLRole := ⟨false, true, true⟩
def potentialRole : PatientLRole := ⟨false, false, true⟩
def unspecifiedRole : PatientLRole := ⟨false, false, false⟩

/-- Exactly 4 of the 8 combinations are valid: the implicational chain
    prunes the role space to the four semantically contentful L-roles. -/
theorem exactly_four_valid_roles :
    ∀ r : PatientLRole, r.valid = true ↔
      (r = quantizedRole ∨ r = nonquantizedRole ∨
       r = potentialRole ∨ r = unspecifiedRole) := by
  rintro ⟨q, n, p⟩; revert q n p; decide

/-- Subset ordering on L-thematic roles: R₁ ⊆ R₂ iff every entailment
    in R₁ is also in R₂. -/
def subset (r₁ r₂ : PatientLRole) : Bool :=
  (!r₁.quantized || r₂.quantized) &&
  (!r₁.nonquantized || r₂.nonquantized) &&
  (!r₁.potential || r₂.potential)

/-- Strict subset: ⊂ -/
def strictSubset (r₁ r₂ : PatientLRole) : Bool :=
  subset r₁ r₂ && !subset r₂ r₁

/-- The four valid roles form a linear chain under ⊂:
    {} ⊂ {p} ⊂ {nq,p} ⊂ {q,nq,p} -/
theorem valid_roles_form_chain :
    strictSubset unspecifiedRole potentialRole = true ∧
    strictSubset potentialRole nonquantizedRole = true ∧
    strictSubset nonquantizedRole quantizedRole = true := ⟨rfl, rfl, rfl⟩

/-- The hierarchy is linear: no incomparable pairs among valid roles. -/
theorem no_incomparable_valid_pairs :
    -- Every pair is ordered
    subset unspecifiedRole potentialRole = true ∧
    subset unspecifiedRole nonquantizedRole = true ∧
    subset unspecifiedRole quantizedRole = true ∧
    subset potentialRole nonquantizedRole = true ∧
    subset potentialRole quantizedRole = true ∧
    subset nonquantizedRole quantizedRole = true := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Minimal contrast: Q ⊆_M R iff Q = R or Q ⊂ R with no valid role
    strictly between them. -/
def minimalContrast (q r : PatientLRole) : Bool :=
  q == r || (strictSubset q r &&
    !([quantizedRole, nonquantizedRole, potentialRole, unspecifiedRole].any
        fun p => strictSubset q p && strictSubset p r))

/-- The attested minimal contrasts are exactly the adjacent pairs. -/
theorem minimal_contrasts_are_adjacent :
    minimalContrast unspecifiedRole potentialRole = true ∧
    minimalContrast potentialRole nonquantizedRole = true ∧
    minimalContrast nonquantizedRole quantizedRole = true := ⟨rfl, rfl, rfl⟩

/-- Skipping a level is NOT a minimal contrast. -/
theorem skip_not_minimal :
    minimalContrast unspecifiedRole nonquantizedRole = false ∧
    minimalContrast unspecifiedRole quantizedRole = false ∧
    minimalContrast potentialRole quantizedRole = false := ⟨rfl, rfl, rfl⟩

/-- The affectedness degree corresponding to a valid L-thematic role. -/
def toDegree (r : PatientLRole) : AffectednessDegree :=
  if r.quantized then .quantized
  else if r.nonquantized then .nonquantized
  else if r.potential then .potential
  else .unspecified

/-- The valid L-thematic role realizing a degree (section of `toDegree`). -/
def ofDegree : AffectednessDegree → PatientLRole
  | .quantized => quantizedRole
  | .nonquantized => nonquantizedRole
  | .potential => potentialRole
  | .unspecified => unspecifiedRole

theorem ofDegree_valid : ∀ d, (ofDegree d).valid = true := by
  intro d; cases d <;> rfl

theorem toDegree_ofDegree : ∀ d, (ofDegree d).toDegree = d := by
  intro d; cases d <;> rfl

/-- The subset order on valid roles is the substrate's `AffectednessDegree`
    order, transported along `toDegree`. -/
theorem subset_iff_toDegree_le :
    ∀ q r : PatientLRole, q.valid = true → r.valid = true →
      (subset q r = true ↔ q.toDegree ≤ r.toDegree) := by
  rintro ⟨a, b, c⟩ ⟨d, e, f⟩; revert a b c d e f; decide

end PatientLRole

-- ════════════════════════════════════════════════════
-- § 3. Morphosyntactic Alignment Principle (§4.3)
-- ════════════════════════════════════════════════════

/-- The MAP ([beavers-2010]; canonical wording in Beavers' 2023 Sag Lectures
    handout): when an argument may be either an object or a PP, it bears role
    R as an object and the *next weakest* role Q ⊆_M R as a PP — a minimal
    weakening, not mere subset. -/
def MAP (directRole obliqueRole : PatientLRole) : Bool :=
  PatientLRole.minimalContrast obliqueRole directRole

/-- Derived corollary of the MAP (the weakened form an earlier version of
    this file stated as the MAP itself): the oblique role's entailments are
    a subset of the direct role's. -/
theorem MAP_subset :
    ∀ d o : PatientLRole, MAP d o = true → PatientLRole.subset o d = true := by
  rintro ⟨a, b, c⟩ ⟨d, e, f⟩; revert a b c d e f; decide

/-- The case the strengthening excludes: a level-skipping weakening
    (potential oblique under a quantized direct role) satisfies the subset
    corollary but violates the MAP proper. -/
theorem skip_violates_MAP :
    MAP PatientLRole.quantizedRole PatientLRole.potentialRole = false ∧
    PatientLRole.subset PatientLRole.potentialRole PatientLRole.quantizedRole
      = true :=
  ⟨PatientLRole.skip_not_minimal.2.2, rfl⟩

-- ════════════════════════════════════════════════════
-- § 4. Alternation Contrasts (§3.2)
-- ════════════════════════════════════════════════════

/-- An observed alternation contrast: a verb with its direct-object
    and oblique affectedness degrees. -/
structure AlternationContrast where
  verb : String
  alternationType : DiathesisAlternation
  directDegree : AffectednessDegree
  obliqueDegree : AffectednessDegree
  deriving Repr, BEq

-- ── Conative alternations (Table 3) ──

/-- *eat* conative: "ate the pizza" (quantized) vs "ate at the pizza" (nonquantized).
    The object variant entails total consumption; the oblique entails only some
    consumption occurred. -/
def eatConative : AlternationContrast :=
  ⟨"eat", .conative, .quantized, .nonquantized⟩

/-- *cut* conative: "cut the rope" (nonquantized) vs "cut at the rope" (potential).
    The object variant entails some damage; the oblique entails only that
    damage was possible (contact under modality). -/
def cutConative : AlternationContrast :=
  ⟨"cut", .conative, .nonquantized, .potential⟩

/-- *hit* conative: "hit the rope" (potential) vs "hit at the rope" (unspecified).
    The object variant entails potential for change (if contact, then possible
    result); the oblique entails only potential contact under double modality. -/
def hitConative : AlternationContrast :=
  ⟨"hit", .conative, .potential, .unspecified⟩

-- ── Locative alternations (Table 4) ──

/-- *load* locative (location as object): "loaded the wagon" (quantized)
    vs "loaded hay onto the wagon" — the wagon undergoes quantized change
    (completely filled), the hay undergoes nonquantized change (moved). -/
def loadLocation : AlternationContrast :=
  ⟨"load", .locative, .quantized, .nonquantized⟩

/-- *load* locative (theme as object): "loaded the hay" (quantized)
    vs "loaded the wagon with the hay" — the hay undergoes quantized
    change (all moved), the wagon undergoes nonquantized change. -/
def loadTheme : AlternationContrast :=
  ⟨"load", .locative, .quantized, .nonquantized⟩

/-- *cut/slice* locative (location as object): "cut the window with
    the diamond" (nonquantized) vs "cut the diamond on the window"
    — both undergo potential change, but the object has nonquantized. -/
def cutLocation : AlternationContrast :=
  ⟨"cut", .locative, .nonquantized, .potential⟩

/-- *cut/slice* locative (theme as object): same contrast. -/
def cutTheme : AlternationContrast :=
  ⟨"cut", .locative, .nonquantized, .potential⟩

/-- All attested alternation contrasts. -/
def allContrasts : List AlternationContrast :=
  [eatConative, cutConative, hitConative,
   loadLocation, loadTheme, cutLocation, cutTheme]

-- ════════════════════════════════════════════════════
-- § 5. MAP Verification
-- ════════════════════════════════════════════════════

/-- The MAP holds of a contrast: the oblique role is the next-weakest
    (minimal) weakening of the direct role. -/
def MapHolds (c : AlternationContrast) : Prop :=
  MAP (.ofDegree c.directDegree) (.ofDegree c.obliqueDegree) = true

instance (c : AlternationContrast) : Decidable (MapHolds c) := by
  unfold MapHolds; infer_instance

/-- Degree-level corollary via `MAP_subset` and the substrate's
    `AffectednessDegree` order: the direct degree dominates the oblique. -/
theorem MapHolds.oblique_le {c : AlternationContrast} (h : MapHolds c) :
    c.obliqueDegree ≤ c.directDegree := by
  have hle := (PatientLRole.subset_iff_toDegree_le _ _
    (PatientLRole.ofDegree_valid _) (PatientLRole.ofDegree_valid _)).mp
    (MAP_subset _ _ h)
  simpa [PatientLRole.toDegree_ofDegree] using hle

-- ── Per-contrast MAP verification ──

theorem MAP_eat_conative : MapHolds eatConative := by decide
theorem MAP_cut_conative : MapHolds cutConative := by decide
theorem MAP_hit_conative : MapHolds hitConative := by decide
theorem MAP_load_location : MapHolds loadLocation := by decide
theorem MAP_load_theme : MapHolds loadTheme := by decide
theorem MAP_cut_location : MapHolds cutLocation := by decide
theorem MAP_cut_theme : MapHolds cutTheme := by decide

/-- The MAP — in its strengthened next-weakest form — holds for ALL attested
    alternation contrasts: every oblique realization is a *minimal* weakening
    of its direct counterpart. -/
theorem MAP_holds_all_alternations :
    ∀ c ∈ allContrasts, MapHolds c := by decide

-- ════════════════════════════════════════════════════
-- § 6. Minimal Contrast Verification
-- ════════════════════════════════════════════════════

/-- The three conatives *tile* the hierarchy — every adjacent pair appears
    exactly once, so together they exhibit the full implicational chain.
    (That each is a minimal contrast is the per-contrast `MAP_*_conative`
    theorem above.) -/
theorem conatives_cover_hierarchy :
    eatConative.directDegree = .quantized ∧
    eatConative.obliqueDegree = .nonquantized ∧
    cutConative.directDegree = .nonquantized ∧
    cutConative.obliqueDegree = .potential ∧
    hitConative.directDegree = .potential ∧
    hitConative.obliqueDegree = .unspecified := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 7. Impossible Alternations
-- ════════════════════════════════════════════════════

/-- A hypothetical alternation whose oblique has *more* entailments than
    its direct object (potential DO, quantized oblique) — the less prominent
    realization would carry stronger truth conditions. -/
def impossibleConative : AlternationContrast :=
  ⟨"impossible", .conative, .potential, .quantized⟩

/-- A level-skipping alternation: quantized direct, potential oblique.
    Satisfies the subset corollary but not the MAP proper — the degree-level
    face of `skip_violates_MAP`. -/
def skippingLocative : AlternationContrast :=
  ⟨"skipping", .locative, .quantized, .potential⟩

/-- A reversed alternation: the oblique strictly outranks the direct. -/
def reversedConative : AlternationContrast :=
  ⟨"reversed", .conative, .unspecified, .potential⟩

theorem reversed_violates_MAP : ¬ MapHolds reversedConative := by decide

theorem impossible_violates_MAP : ¬ MapHolds impossibleConative := by decide

/-- Skipping a level violates the MAP even though the degree order is
    respected — `skip_not_minimal` is what excludes it. -/
theorem skipping_violates_MAP :
    ¬ MapHolds skippingLocative ∧
    skippingLocative.obliqueDegree ≤ skippingLocative.directDegree :=
  ⟨by decide, by decide⟩

-- ════════════════════════════════════════════════════
-- § 8. Bridge to Existing Data and EntailmentProfile
-- ════════════════════════════════════════════════════

/-- Bridge to [levin-1993]'s judgment rows: the conative alternation is
    attested for *cut* and *hit*, confirming the Table 3 contrasts. -/
theorem conative_data_attested :
    Levin1993.Examples.con_cut.judgment = .acceptable ∧
    Levin1993.Examples.con_hit.judgment = .acceptable := ⟨rfl, rfl⟩

/-- Bridge to [levin-1993]'s judgment rows: break does NOT participate
    in the conative. This is predicted: break objects undergo quantized
    change (CoS), and the conative would weaken to nonquantized — but
    break's meaning inherently requires a specific result state, so the
    weakening is blocked by the verb's lexical semantics. -/
theorem break_no_conative :
    Levin1993.Examples.con_break.judgment = .ungrammatical := rfl

/-- Bridge to [levin-1993]'s judgment rows: the locative alternation is
    attested for spray/load verbs, confirming the Table 4 contrasts. -/
theorem locative_data_attested :
    Levin1993.Examples.loc_spray.judgment = .acceptable ∧
    Levin1993.Examples.loc_load.judgment = .acceptable := ⟨rfl, rfl⟩

/-! The `profileToDegree` bridge (formerly §8) and its verification theorems
    have been promoted to `Semantics/Events/Affectedness.lean`.
    They are opened at the top of this file. -/

-- ════════════════════════════════════════════════════
-- § 9. Cross-Study Connection: Decompositions Fill Gaps
-- ════════════════════════════════════════════════════

/-! [beavers-2010] argues that the MAP and event decompositions are
    *complementary*, not competing (the paper's conclusion, §6):

    | Approach        | Semantics                        | Morphosyntax             |
    |-----------------|----------------------------------|--------------------------|
    | Decompositions  | gross causal/temporal structure   | subject/nonsubject       |
    | MAP             | fine-grained lexical entailments  | direct/oblique           |

    The existing `EntailmentProfile` captures the gross agentivity structure
    (P-Agent features → subject selection). Beavers 2010 adds the missing
    piece: fine-grained P-Patient structure → direct/oblique alternations. -/

/-- Subject selection (from [dowty-1991]) and object alternations
    (from [beavers-2010]) are *independent* principles operating on
    different argument positions. The ASP governs subjects; the MAP governs
    direct vs. oblique objects. -/
theorem asp_and_map_orthogonal :
    -- ASP: kick subject outranks object for subjecthood
    OutranksForSubject mannerContact.subjectProfile contactObject ∧
    -- MAP: kick object has potential affectedness (surface contact, no
    -- entailed change — [beavers-2011] eq. (60c), same degree the paper
    -- assigns the *hit* conative's direct object)
    profileToDegree contactObject = .potential ∧
    -- The two operate on different dimensions
    -- (subjecthood is about P-Agent; alternation is about P-Patient strength)
    mannerContact.subjectProfile.pAgentScore > 0 ∧
    contactObject.pPatientScore > 0 :=
  ⟨by decide, rfl, by decide, by decide⟩

-- ════════════════════════════════════════════════════
-- § 10. Bridge to [grimm-2011] Persistence Lattice
-- ════════════════════════════════════════════════════

/-! [grimm-2011]'s `PersistenceLevel` reformulates P-Patient as 4
    persistence dimensions (existential/qualitative × beginning/end).
    Beavers' affectedness hierarchy maps systematically onto this lattice:

    | Beavers degree   | Grimm persistence    | Interpretation              |
    |------------------|----------------------|-----------------------------|
    | quantized        | exPersEnd            | Entity created/consumed     |
    |                  | quPersBeginning      | Entity changed to specific  |
    | nonquantized     | quPersBeginning      | Entity changed (nonspecific)|
    | potential         | totalPersistence     | Entity may change           |
    | unspecified       | totalPersistence     | No change entailment        |

    The mapping is not injective: both `quantized` and `nonquantized` can
    map to `quPersBeginning` (the entity changes but persists). The
    distinction between them is about *specificity of the result state*,
    which Grimm's persistence dimensions don't capture — it's a property
    of the scale, not of persistence. This is where the theories are
    genuinely complementary. -/

/-- Map affectedness degrees to their most typical persistence level.
    This captures the systematic correspondence; edge cases (creation verbs
    mapping to exPersEnd for quantized) require verb-specific information. -/
def degreeToPersistence : AffectednessDegree → PersistenceLevel
  | .quantized    => .quPersBeginning   -- entity changes (possibly to specific state)
  | .nonquantized => .quPersBeginning   -- entity changes (nonspecifically)
  | .potential    => .totalPersistence   -- entity MAY change (but persists)
  | .unspecified  => .totalPersistence   -- no change entailed

/-- The two Grimm levels that correspond to "affected" roles
    (quPersBeginning = changed, exPersEnd = created/destroyed) are both
    ranked lower than totalPersistence on Grimm's lattice. Lower persistence
    = higher affectedness. This is the Grimm-Beavers convergence. -/
theorem changed_lower_than_unaffected :
    (PersistenceLevel.quPersBeginning ≤ PersistenceLevel.totalPersistence) := by
  decide

/-- Bridge: kick object has persistence totalPersistence (persists, no
    entailed change) and affectedness potential — exactly the
    `degreeToPersistence` correspondence for potential change. Beavers'
    surface-contact classification ([beavers-2011] eq. (60c)); note
    [grimm-2011]'s own Fig. 5 instead places contact-verb objects at
    quPersBeginning (`TransitivityRank.contact.patientType`), a genuine
    cross-paper disagreement over whether contact entails impingement. -/
theorem kick_grimm_beavers_consistent :
    PersistenceLevel.fromPatientProfile contactObject = .totalPersistence ∧
    profileToDegree contactObject = .potential := ⟨rfl, rfl⟩

/-- Bridge: build object has persistence exPersEnd (created) and
    affectedness quantized — both theories agree on maximal patient status. -/
theorem build_grimm_beavers_consistent :
    PersistenceLevel.fromPatientProfile creationObject = .exPersEnd ∧
    profileToDegree creationObject = .quantized := ⟨rfl, rfl⟩

/-- Bridge: eat object has persistence exPersBeginning (consumed) and
    affectedness quantized — both theories agree on maximal change. -/
theorem eat_grimm_beavers_consistent :
    PersistenceLevel.fromPatientProfile consumptionObject = .exPersBeginning ∧
    profileToDegree consumptionObject = .quantized := ⟨rfl, rfl⟩

/-- The deepest cross-theory result: Grimm's persistence ordering and
    Beavers' affectedness ordering are **monotonically related** for
    canonical verb profiles. Arguments with higher affectedness (Beavers)
    have lower persistence (Grimm). They formalize the same intuition
    — degree of change — from complementary perspectives. -/
theorem grimm_beavers_monotone_canonical :
    -- kick: potential → totalPersistence (may change, persists unchanged)
    profileToDegree contactObject = .potential ∧
    PersistenceLevel.fromPatientProfile contactObject = .totalPersistence ∧
    -- build: quantized → exPersEnd (created, lower persistence)
    profileToDegree creationObject = .quantized ∧
    PersistenceLevel.fromPatientProfile creationObject = .exPersEnd ∧
    -- see: unspecified → totalNonPersistence (no P-Patient entailments at all)
    profileToDegree perception.subjectProfile = .unspecified ∧
    PersistenceLevel.fromPatientProfile perception.subjectProfile = .totalNonPersistence :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 11. ArgTemplate → ParticipantType Bridge
-- ════════════════════════════════════════════════════

/-! Cross-framework bridge from Levin/RHL `ArgTemplate` (event-template
    decomposition) to Grimm's `ParticipantType` (privative agentivity lattice) and
    Beavers' affectedness degree. Each canonical template is verified to
    project into the predicted positions in both systems, and the consistency
    of affectedness ↔ persistence is checked. -/


/-- Project an ArgTemplate's subject profile to a ParticipantType. -/
def _root_.Features.LevinClassProfiles.ArgTemplate.subjectGrimm
    (t : ArgTemplate) : ParticipantType :=
  ParticipantType.fromSubjectProfile t.subjectProfile

/-- Project an ArgTemplate's object profile (if any) to a ParticipantType. -/
def _root_.Features.LevinClassProfiles.ArgTemplate.objectGrimm
    (t : ArgTemplate) : Option ParticipantType :=
  t.objectProfile.map ParticipantType.fromObjectProfile

/-- Project an ArgTemplate's object to its affectedness degree. -/
def _root_.Features.LevinClassProfiles.ArgTemplate.objectAffectedness
    (t : ArgTemplate) : Option AffectednessDegree :=
  t.objectProfile.map profileToDegree

-- ── Per-template ParticipantType verification ──

/-- Manner-contact subject → full agent on the Grimm lattice. -/
theorem mannerContact_subject_grimm :
    mannerContact.subjectGrimm.agentivity = ⊤ := by decide

/-- Manner-contact object → potential affectedness (no CoS entailed). -/
theorem mannerContact_object_affectedness :
    mannerContact.objectAffectedness = some AffectednessDegree.potential := rfl

/-- Result-change object → nonquantized affectedness (CoS, no IT). -/
theorem resultChange_object_affectedness :
    resultChange.objectAffectedness = some AffectednessDegree.nonquantized := rfl

/-- Creation object → quantized affectedness (CoS + IT). -/
theorem creation_object_affectedness :
    creation.objectAffectedness = some AffectednessDegree.quantized := rfl

/-- Consumption object → quantized affectedness (CoS + IT). -/
theorem consumption_object_affectedness :
    consumption.objectAffectedness = some AffectednessDegree.quantized := rfl

/-- Self-motion (intransitive) → no object affectedness. -/
theorem selfMotion_no_object :
    selfMotion.objectAffectedness = none := rfl

/-- **Affectedness ordering across templates**: the named templates are
    ordered by truth-conditional strength on the object side, reproducing
    [beavers-2010]'s hierarchy: creation/consumption (quantized) >
    resultChange (nonquantized) > mannerContact (potential) > perception
    (unspecified). -/
theorem template_affectedness_hierarchy :
    AffectednessDegree.nonquantized ≤ .quantized ∧
    AffectednessDegree.potential ≤ .nonquantized ∧
    creation.objectAffectedness = some AffectednessDegree.quantized ∧
    resultChange.objectAffectedness = some AffectednessDegree.nonquantized ∧
    mannerContact.objectAffectedness = some AffectednessDegree.potential ∧
    perception.objectAffectedness = some AffectednessDegree.unspecified :=
  ⟨by decide, by decide, rfl, rfl, rfl, rfl⟩

-- ── Cross-projection consistency: affectedness vs. persistence ──

/-- The affectedness and persistence projections are consistent for
    manner-contact objects: potential affectedness ↔ totalPersistence
    (the object may change but the verb doesn't entail it). -/
theorem mannerContact_cross_projection :
    mannerContact.objectAffectedness = some AffectednessDegree.potential ∧
    mannerContact.objectProfile.map PersistenceLevel.fromPatientProfile =
      some .totalPersistence := ⟨rfl, by decide⟩

/-- Result-change: nonquantized ↔ quPersBeginning (changed but persists). -/
theorem resultChange_cross_projection :
    resultChange.objectAffectedness = some AffectednessDegree.nonquantized ∧
    resultChange.objectProfile.map PersistenceLevel.fromPatientProfile =
      some .quPersBeginning := ⟨rfl, by decide⟩

/-- Creation: quantized ↔ exPersEnd (entity comes into existence). -/
theorem creation_cross_projection :
    creation.objectAffectedness = some AffectednessDegree.quantized ∧
    creation.objectProfile.map PersistenceLevel.fromPatientProfile =
      some .exPersEnd := ⟨rfl, by decide⟩

end Beavers2010
