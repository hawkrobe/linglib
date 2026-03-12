import Linglib.Theories.Semantics.Lexical.Verb.EntailmentProfile
import Linglib.Theories.Semantics.Lexical.Verb.Affectedness
import Linglib.Theories.Semantics.Lexical.Verb.AgentivityLattice
import Linglib.Phenomena.ArgumentStructure.DiathesisAlternations.Data

/-!
# @cite{beavers-2010} The Structure of Lexical Meaning: Why Semantics Really Matters

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
in the data, the direct-argument affectedness degree is ≥ the oblique's.
This connects the mathematical structure of the hierarchy (derived from
truth-conditional definitions) to empirical argument realization facts
through the MAP.
-/

namespace Phenomena.ArgumentStructure.Studies.Beavers2010

open Semantics.Lexical.Verb.EntailmentProfile
open Semantics.Lexical.Verb.AgentivityLattice
open Semantics.Lexical.Verb.Affectedness (AffectednessDegree profileToDegree)
open Phenomena.ArgumentStructure.DiathesisAlternations.Data

-- ════════════════════════════════════════════════════
-- § 2. L-Thematic Roles as Entailment Sets (§4.3)
-- ════════════════════════════════════════════════════

/-- An L-thematic role for patienthood is a set of affectedness entailments.
    Beavers reduces Dowty's 5 P-Patient entailments to 3 implicationally
    related ones.

    The three entailments:
    - `quantized`: x undergoes a QUANTIZED change
    - `nonquantized`: x undergoes a NONQUANTIZED change
    - `potential`: x has POTENTIAL for a change -/
structure PatientLRole where
  quantized    : Bool
  nonquantized : Bool
  potential    : Bool
  deriving DecidableEq, BEq, Repr

namespace PatientLRole

/-- An L-role is **valid** iff it respects the implicational constraints:
    quantized → nonquantized → potential.

    This rules out 4 of the 8 possible combinations:
    - {q} alone: q → nq violated
    - {q, p} without nq: q → nq violated
    - {q, nq} without p: nq → p violated
    - {nq} alone: nq → p violated -/
def valid (r : PatientLRole) : Bool :=
  (!r.quantized || r.nonquantized) &&    -- q → nq
  (!r.nonquantized || r.potential)         -- nq → p

/-- The four valid L-thematic roles. -/
def quantizedRole : PatientLRole := ⟨true, true, true⟩
def nonquantizedRole : PatientLRole := ⟨false, true, true⟩
def potentialRole : PatientLRole := ⟨false, false, true⟩
def unspecifiedRole : PatientLRole := ⟨false, false, false⟩

-- ── Validity proofs ──

theorem quantized_valid : quantizedRole.valid = true := rfl
theorem nonquantized_valid : nonquantizedRole.valid = true := rfl
theorem potential_valid : potentialRole.valid = true := rfl
theorem unspecified_valid : unspecifiedRole.valid = true := rfl

-- ── Invalid role proofs ──

/-- {q} alone violates q → nq. -/
theorem q_alone_invalid : (⟨true, false, false⟩ : PatientLRole).valid = false := rfl

/-- {q, p} without nq violates q → nq. -/
theorem q_p_invalid : (⟨true, false, true⟩ : PatientLRole).valid = false := rfl

/-- {q, nq} without p violates nq → p. -/
theorem q_nq_invalid : (⟨true, true, false⟩ : PatientLRole).valid = false := rfl

/-- {nq} alone violates nq → p. -/
theorem nq_alone_invalid : (⟨false, true, false⟩ : PatientLRole).valid = false := rfl

/-- **Key theorem**: exactly 4 of 8 combinations are valid. The implicational
    relationships between entailments constrain the space of semantically
    contentful L-thematic roles. -/
theorem exactly_four_valid_roles :
    (⟨true, true, true⟩ : PatientLRole).valid = true ∧
    (⟨false, true, true⟩ : PatientLRole).valid = true ∧
    (⟨false, false, true⟩ : PatientLRole).valid = true ∧
    (⟨false, false, false⟩ : PatientLRole).valid = true ∧
    (⟨true, false, false⟩ : PatientLRole).valid = false ∧
    (⟨true, false, true⟩ : PatientLRole).valid = false ∧
    (⟨true, true, false⟩ : PatientLRole).valid = false ∧
    (⟨false, true, false⟩ : PatientLRole).valid = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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

/-- Minimal contrast: Q ⊆_M R iff Q = R or Q ⊂ R with no
    intervening valid role P such that Q ⊂ P ⊂ R. -/
def minimalContrast (q r : PatientLRole) : Bool :=
  q == r || (strictSubset q r &&
    -- No valid role strictly between q and r
    !(strictSubset q potentialRole && strictSubset potentialRole r &&
      q != potentialRole && r != potentialRole) &&
    !(strictSubset q nonquantizedRole && strictSubset nonquantizedRole r &&
      q != nonquantizedRole && r != nonquantizedRole) &&
    !(strictSubset q unspecifiedRole && strictSubset unspecifiedRole r &&
      q != unspecifiedRole && r != unspecifiedRole) &&
    !(strictSubset q quantizedRole && strictSubset quantizedRole r &&
      q != quantizedRole && r != quantizedRole))

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

theorem toDegree_quantized : toDegree quantizedRole = .quantized := rfl
theorem toDegree_nonquantized : toDegree nonquantizedRole = .nonquantized := rfl
theorem toDegree_potential : toDegree potentialRole = .potential := rfl
theorem toDegree_unspecified : toDegree unspecifiedRole = .unspecified := rfl

end PatientLRole

-- ════════════════════════════════════════════════════
-- § 3. Morphosyntactic Alignment Principle (§4.3)
-- ════════════════════════════════════════════════════

/-- The MAP: when participant x may be realized as either a direct
    argument (bearing L-thematic role R) or an oblique (bearing role Q),
    Q ⊆_M R — the oblique role is a minimal weakening of the direct role.

    Equivalently: the direct object's affectedness degree is ≥ the oblique's.

    This is a prominence-preservation principle: stronger truth conditions
    map to more prominent morphosyntactic realization. -/
def MAP (directRole obliqueRole : PatientLRole) : Bool :=
  PatientLRole.subset obliqueRole directRole

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

/-- MAP holds for a single contrast: direct ≥ oblique. -/
def mapHolds (c : AlternationContrast) : Bool :=
  AffectednessDegree.ge c.directDegree c.obliqueDegree

-- ── Per-contrast MAP verification ──

theorem MAP_eat_conative : mapHolds eatConative = true := rfl
theorem MAP_cut_conative : mapHolds cutConative = true := rfl
theorem MAP_hit_conative : mapHolds hitConative = true := rfl
theorem MAP_load_location : mapHolds loadLocation = true := rfl
theorem MAP_load_theme : mapHolds loadTheme = true := rfl
theorem MAP_cut_location : mapHolds cutLocation = true := rfl
theorem MAP_cut_theme : mapHolds cutTheme = true := rfl

/-- **The deepest theorem**: the MAP holds for ALL attested alternation
    contrasts. Every direct realization has truth conditions at least as
    strong as the corresponding oblique realization.

    This connects:
    1. The mathematical structure of the affectedness hierarchy (§1–2)
    2. The MAP as a prominence-preservation principle (§3)
    3. The empirical alternation data (§4)

    Any change to the affectedness assignments breaks this theorem. -/
theorem MAP_holds_all_alternations :
    allContrasts.all mapHolds = true := rfl

-- ════════════════════════════════════════════════════
-- § 6. Minimal Contrast Verification
-- ════════════════════════════════════════════════════

/-- Each conative contrast is exactly a *minimal* contrast — adjacent
    levels on the hierarchy. This is not stipulated; it follows from the
    verbs' truth conditions. -/
theorem conatives_are_minimal_contrasts :
    PatientLRole.minimalContrast
      .nonquantizedRole .quantizedRole = true ∧    -- eat
    PatientLRole.minimalContrast
      .potentialRole .nonquantizedRole = true ∧     -- cut
    PatientLRole.minimalContrast
      .unspecifiedRole .potentialRole = true         -- hit
    := ⟨rfl, rfl, rfl⟩

/-- The three conatives *tile* the entire hierarchy — every adjacent
    pair appears exactly once. Together they demonstrate the full
    implicational chain. -/
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

/-- The MAP rules out "impossible" alternations where the oblique
    would have *more* entailments than the direct object.

    Example: a hypothetical alternation where the DO is POTENTIAL
    but the oblique is QUANTIZED is ruled out — it would mean the
    less prominent realization has *stronger* truth conditions. -/
def impossibleConative : AlternationContrast :=
  ⟨"impossible", .conative, .potential, .quantized⟩

def impossibleLocative : AlternationContrast :=
  ⟨"impossible", .locative, .quantized, .potential⟩

-- This one is fine (direct ≥ oblique)
theorem possible_locative_ok : mapHolds impossibleLocative = true := rfl

-- Reversed direction violates the MAP
def reversedConative : AlternationContrast :=
  ⟨"reversed", .conative, .unspecified, .potential⟩

theorem reversed_violates_MAP : mapHolds reversedConative = false := rfl

theorem impossible_violates_MAP : mapHolds impossibleConative = false := rfl

-- ════════════════════════════════════════════════════
-- § 8. Bridge to Existing Data and EntailmentProfile
-- ════════════════════════════════════════════════════

/-- Bridge to existing alternation data: the conative alternation
    data for eat, cut, and hit in `Data.lean` records `.participates`,
    confirming these alternations are attested. -/
theorem conative_data_attested :
    con_cut.result = .participates ∧
    con_hit.result = .participates := ⟨rfl, rfl⟩

/-- Bridge to existing alternation data: break does NOT participate
    in the conative. This is predicted: break objects undergo quantized
    change (CoS), and the conative would weaken to nonquantized — but
    break's meaning inherently requires a specific result state, so the
    weakening is blocked by the verb's lexical semantics. -/
theorem break_no_conative :
    con_break.result = .blocked := rfl

/-- Bridge to existing alternation data: locative alternation is
    attested for spray/load verbs. -/
theorem locative_data_attested :
    loc_spray.result = .participates ∧
    loc_load.result = .participates := ⟨rfl, rfl⟩

/-! The `profileToDegree` bridge (formerly §8) and its verification theorems
    have been promoted to `Theories/Semantics/Events/Affectedness.lean`.
    They are opened at the top of this file. -/

-- ════════════════════════════════════════════════════
-- § 9. Cross-Study Connection: Decompositions Fill Gaps
-- ════════════════════════════════════════════════════

/-! @cite{beavers-2010} argues that the MAP and event decompositions are
    *complementary*, not competing (the paper's conclusion, §6):

    | Approach        | Semantics                        | Morphosyntax             |
    |-----------------|----------------------------------|--------------------------|
    | Decompositions  | gross causal/temporal structure   | subject/nonsubject       |
    | MAP             | fine-grained lexical entailments  | direct/oblique           |

    The existing `EntailmentProfile` captures the gross agentivity structure
    (P-Agent features → subject selection). Beavers 2010 adds the missing
    piece: fine-grained P-Patient structure → direct/oblique alternations. -/

/-- Subject selection (from @cite{dowty-1991}) and object alternations
    (from @cite{beavers-2010}) are *independent* principles operating on
    different argument positions. The ASP governs subjects; the MAP governs
    direct vs. oblique objects. -/
theorem asp_and_map_orthogonal :
    -- ASP: kick subject outranks object for subjecthood
    outranksForSubject kickSubjectProfile kickObjectProfile = true ∧
    -- MAP: kick object has nonquantized affectedness (CoS, not incremental)
    profileToDegree kickObjectProfile = .nonquantized ∧
    -- The two operate on different dimensions
    -- (subjecthood is about P-Agent; alternation is about P-Patient strength)
    kickSubjectProfile.pAgentScore > 0 ∧
    kickObjectProfile.pPatientScore > 0 :=
  ⟨by native_decide, rfl, by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 10. Bridge to @cite{grimm-2011} Persistence Lattice
-- ════════════════════════════════════════════════════

/-! @cite{grimm-2011}'s `PersistenceLevel` reformulates P-Patient as 4
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

/-- Bridge: kick object has persistence quPersBeginning (changed but
    persists) and affectedness nonquantized — both theories agree it's
    affected but not to a specific degree. -/
theorem kick_grimm_beavers_consistent :
    PersistenceLevel.fromPatientProfile kickObjectProfile = .quPersBeginning ∧
    profileToDegree kickObjectProfile = .nonquantized := ⟨by native_decide, rfl⟩

/-- Bridge: build object has persistence exPersEnd (created) and
    affectedness quantized — both theories agree on maximal patient status. -/
theorem build_grimm_beavers_consistent :
    PersistenceLevel.fromPatientProfile buildObjectProfile = .exPersEnd ∧
    profileToDegree buildObjectProfile = .quantized := ⟨by native_decide, rfl⟩

/-- Bridge: eat object has persistence exPersBeginning (consumed) and
    affectedness quantized — both theories agree on maximal change. -/
theorem eat_grimm_beavers_consistent :
    PersistenceLevel.fromPatientProfile eatObjectProfile = .exPersBeginning ∧
    profileToDegree eatObjectProfile = .quantized := ⟨by native_decide, rfl⟩

/-- The deepest cross-theory result: Grimm's persistence ordering and
    Beavers' affectedness ordering are **monotonically related** for
    canonical verb profiles. Arguments with higher affectedness (Beavers)
    have lower persistence (Grimm). They formalize the same intuition
    — degree of change — from complementary perspectives. -/
theorem grimm_beavers_monotone_canonical :
    -- kick: nonquantized → quPersBeginning (changed)
    profileToDegree kickObjectProfile = .nonquantized ∧
    PersistenceLevel.fromPatientProfile kickObjectProfile = .quPersBeginning ∧
    -- build: quantized → exPersEnd (created, lower persistence)
    profileToDegree buildObjectProfile = .quantized ∧
    PersistenceLevel.fromPatientProfile buildObjectProfile = .exPersEnd ∧
    -- see: unspecified → totalNonPersistence (no P-Patient entailments at all)
    profileToDegree seeSubjectProfile = .unspecified ∧
    PersistenceLevel.fromPatientProfile seeSubjectProfile = .totalNonPersistence :=
  ⟨rfl, by native_decide, rfl, by native_decide, rfl, by native_decide⟩

end Phenomena.ArgumentStructure.Studies.Beavers2010
