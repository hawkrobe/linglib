/-!
# Case
@cite{blake-1994} @cite{anderson-jm-2006} @cite{stassen-1985}
@cite{comrie-1978} @cite{dixon-1994} @cite{heine-2009}

Framework-agnostic case infrastructure drawn from @cite{blake-1994}'s
cross-linguistic survey and @cite{anderson-jm-2006}'s localist case grammar.

**§ 1–3: Case Inventory** (@cite{blake-1994}). 19 cross-linguistic case values,
exhaustive enumeration, and case assignment modes.

**§ 4–5: Blake's Hierarchy** (@cite{blake-1994}, §5.8). Implicational hierarchy
over case inventories with contiguity checking.

**§ 6–11: Feature Decomposition** (@cite{anderson-jm-2006}). Three first-order
case features [abs, src, loc], 8 case relations, subject selection hierarchy,
scenarios, and morphological case mapping.

**§ 12: Split Ergativity** (@cite{blake-1994}, @cite{dixon-1994}). Parameterized
split-ergative conditioning.

**§ 13: Case Extension** (@cite{heine-2009}).
Grammaticalization of case functions: source categories, extension paths
(Table 29.6), chains, principles, and beyond-case targets.

**§ 14: Comparative Entry** (@cite{stassen-1985}). Typed record for
comparative construction parameters.

Nanosyntax-specific material (Caha's containment hierarchy, *ABA constraint,
syncretism adjacency) lives in `Theories/Morphology/CaseContainment.lean`.
-/

namespace Core

-- ============================================================================
-- § 1: Alignment Family
-- ============================================================================

/-- The two major morphosyntactic alignment families. -/
inductive AlignmentFamily where
  | accusative
  | ergative
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Case Inventory
-- ============================================================================

/-- Cross-linguistic case inventory (@cite{blake-1994}, Chs. 2, 5).

    The 19 values cover the morphological cases attested across Blake's
    typological sample. Ordered roughly by the Blake hierarchy, from core
    grammatical cases to peripheral semantic cases. -/
inductive Case where
  | nom    -- Nominative: unmarked subject in accusative systems
  | acc    -- Accusative: transitive patient in accusative systems
  | erg    -- Ergative: transitive agent in ergative systems
  | abs    -- Absolutive: unmarked S/P in ergative systems
  | gen    -- Genitive: possessor, partitive source
  | dat    -- Dative: recipient, goal, experiencer
  | loc    -- Locative: spatial location
  | abl    -- Ablative: spatial source, origin
  | all    -- Allative: spatial goal, direction toward
  | inst   -- Instrumental: means, instrument
  | com    -- Comitative: accompaniment ('with X')
  | voc    -- Vocative: direct address
  | part   -- Partitive: partial affectedness, existential
  | perl   -- Perlative: path, motion through
  | ben    -- Benefactive: beneficiary
  | caus   -- Causal: reason, cause
  | ess    -- Essive: state or role ('as X') — Finnish -nA
  | transl -- Translative: change of state ('becoming X') — Finnish -ksi
  | abess  -- Abessive: privative ('without X') — Finnish -ttA
  deriving DecidableEq, BEq, Repr, Inhabited

-- ============================================================================
-- § 3: Exhaustive Enumeration and Case Assignment
-- ============================================================================

/-- All 19 case values (for finite verification). -/
def Case.allCases : List Case :=
  [.nom, .acc, .erg, .abs, .gen, .dat, .loc, .abl,
   .all, .inst, .com, .voc, .part, .perl, .ben, .caus,
   .ess, .transl, .abess]

theorem Case.allCases_length : Case.allCases.length = 19 := by native_decide

def Case.inAllCases (c : Case) : Bool :=
  Case.allCases.any (· == c)

theorem Case.allCases_complete (c : Case) : c.inAllCases = true := by
  cases c <;> native_decide

/-- How case is assigned to an NP in a given construction
    (@cite{stassen-1985}, §2.2.1). -/
inductive CaseAssignment where
  | derived
  | fixed
  deriving DecidableEq, BEq, Repr

/-- For fixed-case NPs, what syntactic role the NP occupies. -/
inductive FixedCaseEncoding where
  | directObject
  | adverbial
  deriving DecidableEq, BEq, Repr

/-- The three spatial cases that serve as adverbial markers
    cross-linguistically (@cite{stassen-1985}, §2.2.3). -/
def Case.spatialTriad : List Case := [.abl, .all, .loc]

theorem Case.spatialTriad_length : Case.spatialTriad.length = 3 := by native_decide

-- ============================================================================
-- § 4: Blake's Case Hierarchy
-- ============================================================================

/-- Position on Blake's case hierarchy (@cite{blake-1994}, §5.8, ex. 68).

    Higher rank = more likely to exist in a language's case inventory.

    Ranks: 6 = core (NOM/ACC/ERG/ABS), 5 = GEN, 4 = DAT, 3 = LOC,
    2 = ABL/INST, 1 = COM/ALL/PERL/BEN, 0 = VOC/PART/CAUS/ESS/TRANSL/ABESS. -/
def Case.hierarchyRank : Case → Nat
  | .nom | .acc | .erg | .abs => 6
  | .gen                      => 5
  | .dat                      => 4
  | .loc                      => 3
  | .abl | .inst              => 2
  | .com | .all | .perl | .ben => 1
  | .voc | .part | .caus | .ess | .transl | .abess => 0

-- ============================================================================
-- § 5: Hierarchy Contiguity
-- ============================================================================

private def hasRank (inv : List Case) (r : Nat) : Bool :=
  inv.any fun c => c.hierarchyRank == r

/-- A case inventory is contiguous (no rank gaps) on the hierarchy.
    Formalizes Blake's implicational tendency (1994, §5.8). -/
def validInventory (inv : List Case) : Bool :=
  inv.all fun c =>
    inv.all fun c' =>
      if c'.hierarchyRank > c.hierarchyRank then
        let lo := c.hierarchyRank
        let hi := c'.hierarchyRank
        List.range hi |>.all fun r =>
          if r > lo && r < hi then hasRank inv r
          else true
      else true

theorem core_highest : Case.hierarchyRank .nom = 6 := rfl

theorem gen_above_dat :
    Case.hierarchyRank .gen > Case.hierarchyRank .dat := by decide

theorem dat_above_loc :
    Case.hierarchyRank .dat > Case.hierarchyRank .loc := by decide

theorem loc_above_abl :
    Case.hierarchyRank .loc > Case.hierarchyRank .abl := by decide

theorem loc_above_inst :
    Case.hierarchyRank .loc > Case.hierarchyRank .inst := by decide

theorem abl_inst_same_rank :
    Case.hierarchyRank .abl = Case.hierarchyRank .inst := rfl

theorem two_case_valid :
    validInventory [.nom, .acc] = true := by native_decide

theorem three_case_with_gen_valid :
    validInventory [.nom, .acc, .gen] = true := by native_decide

theorem four_case_valid :
    validInventory [.nom, .acc, .gen, .dat] = true := by native_decide

theorem five_case_valid :
    validInventory [.nom, .acc, .gen, .dat, .loc] = true := by native_decide

theorem seven_case_valid :
    validInventory [.nom, .acc, .gen, .dat, .loc, .abl, .inst] = true := by
  native_decide

theorem ergative_four_case_valid :
    validInventory [.erg, .abs, .gen, .dat] = true := by native_decide

theorem split_ergative_valid :
    validInventory [.nom, .erg, .abs, .gen] = true := by native_decide

theorem skip_gen_invalid :
    validInventory [.nom, .acc, .dat] = false := by native_decide

theorem skip_gen_dat_invalid :
    validInventory [.nom, .acc, .loc] = false := by native_decide

theorem skip_to_abl_invalid :
    validInventory [.nom, .acc, .abl] = false := by native_decide

theorem skip_dat_invalid :
    validInventory [.nom, .acc, .gen, .loc] = false := by native_decide

-- ============================================================================
-- § 6: Case Features (Anderson 2006)
-- ============================================================================

/-- Anderson's three first-order case features (@cite{anderson-jm-2006}, Ch. 6). -/
inductive CaseFeature where
  | abs
  | src
  | loc
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 7: Case Relations (Feature Bundles)
-- ============================================================================

/-- An argument's case specification: a bundle of first-order features
    (@cite{anderson-jm-2006}, Ch. 6). 8 possible bundles from 3 Bools. -/
structure CaseRelation where
  abs : Bool
  src : Bool
  loc : Bool
  deriving DecidableEq, BEq, Repr, Inhabited

def CaseRelation.neutral : CaseRelation := ⟨false, false, false⟩
def CaseRelation.absolutive : CaseRelation := ⟨true, false, false⟩
def CaseRelation.ergative : CaseRelation := ⟨false, true, false⟩
def CaseRelation.locative : CaseRelation := ⟨false, false, true⟩
def CaseRelation.srcAbs : CaseRelation := ⟨true, true, false⟩
def CaseRelation.srcLoc : CaseRelation := ⟨false, true, true⟩
def CaseRelation.absLoc : CaseRelation := ⟨true, false, true⟩
def CaseRelation.absSrcLoc : CaseRelation := ⟨true, true, true⟩

-- ============================================================================
-- § 8: Subject Selection Hierarchy
-- ============================================================================

/-- The subject selection rank (@cite{anderson-jm-2006}, eq. 38').
    src (agent) outranks abs (patient) outranks loc (spatial). -/
def CaseRelation.subjectRank (cr : CaseRelation) : Nat :=
  if cr.src then 2 else if cr.abs then 1 else 0

theorem ergative_rank : CaseRelation.ergative.subjectRank = 2 := rfl
theorem absolutive_rank : CaseRelation.absolutive.subjectRank = 1 := rfl
theorem locative_rank : CaseRelation.locative.subjectRank = 0 := rfl
theorem neutral_rank : CaseRelation.neutral.subjectRank = 0 := rfl

theorem erg_above_abs :
    CaseRelation.ergative.subjectRank > CaseRelation.absolutive.subjectRank := by
  decide

theorem abs_above_loc :
    CaseRelation.absolutive.subjectRank > CaseRelation.locative.subjectRank := by
  decide

theorem experiencer_agent_same_rank :
    CaseRelation.srcLoc.subjectRank = CaseRelation.ergative.subjectRank := rfl

theorem selfMover_agent_same_rank :
    CaseRelation.srcAbs.subjectRank = CaseRelation.ergative.subjectRank := rfl

theorem contactive_abs_same_rank :
    CaseRelation.absLoc.subjectRank = CaseRelation.absolutive.subjectRank := rfl

theorem src_determines_subject_rank (cr : CaseRelation) (h : cr.src = true) :
    cr.subjectRank = 2 := by simp [CaseRelation.subjectRank, h]

theorem abs_without_src_rank (cr : CaseRelation)
    (h1 : cr.src = false) (h2 : cr.abs = true) :
    cr.subjectRank = 1 := by simp [CaseRelation.subjectRank, h1, h2]

-- ============================================================================
-- § 9: Feature Containment and Enumeration
-- ============================================================================

def CaseRelation.isSubsetOf (inner outer : CaseRelation) : Bool :=
  (!inner.abs || outer.abs) && (!inner.src || outer.src) && (!inner.loc || outer.loc)

theorem absSrcLoc_is_top (cr : CaseRelation) :
    cr.isSubsetOf .absSrcLoc = true := by
  cases cr with | mk a s l => cases a <;> cases s <;> cases l <;> rfl

theorem neutral_is_bottom (cr : CaseRelation) :
    CaseRelation.neutral.isSubsetOf cr = true := by
  cases cr with | mk a s l => cases a <;> cases s <;> cases l <;> rfl

def CaseRelation.all : List CaseRelation :=
  [.absSrcLoc, .srcAbs, .srcLoc, .ergative,
   .absLoc, .absolutive, .locative, .neutral]

theorem CaseRelation.all_length : CaseRelation.all.length = 8 := rfl

def CaseRelation.inAll (cr : CaseRelation) : Bool :=
  CaseRelation.all.any (· == cr)

theorem CaseRelation.all_complete (cr : CaseRelation) :
    cr.inAll = true := by
  cases cr with | mk a s l => cases a <;> cases s <;> cases l <;> native_decide

-- ============================================================================
-- § 10: Scenarios (Predicate Argument Structure)
-- ============================================================================

/-- A predicate's **scenario** (@cite{anderson-jm-2006}, Ch. 6): the case
    relations assigned to its arguments. -/
structure Scenario where
  relations : List CaseRelation
  deriving Repr

def Scenario.arity (s : Scenario) : Nat := s.relations.length

def Scenario.subjectRelation (s : Scenario) : Option CaseRelation :=
  s.relations.head?

def Scenario.objectRelation (s : Scenario) : Option CaseRelation :=
  match s.relations with
  | _ :: cr :: _ => some cr
  | _ => none

def Scenario.transitive : Scenario := ⟨[.ergative, .absolutive]⟩
def Scenario.unergative : Scenario := ⟨[.ergative]⟩
def Scenario.unaccusative : Scenario := ⟨[.absolutive, .locative]⟩
def Scenario.selfMoving : Scenario := ⟨[.srcAbs, .locative]⟩
def Scenario.experiencer : Scenario := ⟨[.srcLoc, .absolutive]⟩

theorem transitive_subject_object :
    Scenario.transitive.subjectRelation = some .ergative ∧
    Scenario.transitive.objectRelation = some .absolutive := ⟨rfl, rfl⟩

theorem unergative_subject_only :
    Scenario.unergative.subjectRelation = some .ergative ∧
    Scenario.unergative.objectRelation = none := ⟨rfl, rfl⟩

theorem unaccusative_subject_loc :
    Scenario.unaccusative.subjectRelation = some .absolutive ∧
    Scenario.unaccusative.objectRelation = some .locative := ⟨rfl, rfl⟩

theorem selfMoving_subject :
    Scenario.selfMoving.subjectRelation = some .srcAbs ∧
    Scenario.selfMoving.objectRelation = some .locative := ⟨rfl, rfl⟩

theorem experiencer_subject_object :
    Scenario.experiencer.subjectRelation = some .srcLoc ∧
    Scenario.experiencer.objectRelation = some .absolutive := ⟨rfl, rfl⟩

theorem transitive_subject_outranks_object :
    CaseRelation.ergative.subjectRank > CaseRelation.absolutive.subjectRank := by
  decide

theorem unergative_unaccusative_differ :
    Scenario.unergative.subjectRelation ≠
    Scenario.unaccusative.subjectRelation := by decide

-- ============================================================================
-- § 11: Morphological Case → Case Relation
-- ============================================================================

/-- Canonical mapping from Blake's morphological cases to Anderson's
    case-feature bundles (@cite{anderson-jm-2006}, Ch. 6). -/
def Case.toCaseRelation : Case → Option CaseRelation
  | .nom  => some .srcAbs
  | .acc  => some .absolutive
  | .erg  => some .srcAbs
  | .abs  => some .absolutive
  | .abl  => some .locative
  | .loc  => some .locative
  | .inst => some .ergative
  | _     => none

theorem Case.nom_erg_same_relation :
    Case.toCaseRelation .nom = Case.toCaseRelation .erg := rfl

theorem Case.acc_abs_same_relation :
    Case.toCaseRelation .acc = Case.toCaseRelation .abs := rfl

-- ============================================================================
-- § 12: Split Ergativity
-- ============================================================================

/-- A split-ergative system (@cite{blake-1994}, @cite{dixon-1994}):
    alignment varies by some conditioning factor. -/
structure SplitErgativity (Factor : Type) where
  ergCondition : Factor → Bool

def SplitErgativity.alignment {Factor : Type} (split : SplitErgativity Factor)
    (f : Factor) : AlignmentFamily :=
  if split.ergCondition f then .ergative else .accusative

inductive Aspect where
  | perfective
  | imperfective
  deriving DecidableEq, BEq, Repr

def hindiSplit : SplitErgativity Aspect :=
  { ergCondition := fun a => a == .perfective }

theorem hindi_perfective_erg :
    hindiSplit.alignment .perfective = .ergative := rfl

theorem hindi_imperfective_acc :
    hindiSplit.alignment .imperfective = .accusative := rfl

-- ============================================================================
-- § 13: Case Grammaticalization (@cite{heine-2009})
-- ============================================================================

-- § 13.1: Four Principles of Case Grammaticalization
-- (@cite{heine-2009} §29.1, following Heine and Kuteva 2002, 2005)

/-- The four principles governing grammaticalization of case markers.
    Development from lexical item to case marker is unidirectional and
    involves all or a subset of these principles. -/
inductive GramPrinciple where
  /-- Use extended to wider range of complement nouns; meaning generalizes. -/
  | extension
  /-- Lexical meaning lost; schematic case function acquired. -/
  | desemanticization
  /-- Morphosyntactic properties lost: becomes invariable clitic/affix,
      positionally restricted, paradigm shrinks. -/
  | decategorialization
  /-- Phonetic substance lost: loses stress, assimilates to host,
      may reduce to zero. -/
  | erosion
  deriving DecidableEq, BEq, Repr

/-- Source category of a case marker on the grammaticalization cline
    (@cite{heine-2009} §29.1 eq. (1), §29.2).

    noun, verb (> adverb) > adposition > case affix > loss

    Parallel to `Diachronic.Grammaticalization.GramStage` (for verbal
    elements), but specific to case-marker development. -/
inductive CaseGramStage where
  /-- Lexical noun or verb source (§29.2.1–29.2.2). -/
  | lexical
  /-- Free adposition: preposition or postposition (§29.2.3). -/
  | adposition
  /-- Bound case affix: suffix or prefix (§29.2.3 endpoint). -/
  | caseAffix
  /-- Case marker lost: erosion endpoint or merger. -/
  | lost
  deriving DecidableEq, BEq, Repr

/-- Boundedness increases monotonically along the case cline. -/
def CaseGramStage.boundedness : CaseGramStage → Nat
  | .lexical    => 0
  | .adposition => 1
  | .caseAffix  => 2
  | .lost       => 3

instance : LE CaseGramStage where
  le a b := a.boundedness ≤ b.boundedness

instance : LT CaseGramStage where
  lt a b := a.boundedness < b.boundedness

instance (a b : CaseGramStage) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.boundedness ≤ b.boundedness))

instance (a b : CaseGramStage) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.boundedness < b.boundedness))

theorem caseGramCline_ordered :
    CaseGramStage.lexical < CaseGramStage.adposition ∧
    CaseGramStage.adposition < CaseGramStage.caseAffix ∧
    CaseGramStage.caseAffix < CaseGramStage.lost :=
  ⟨by decide, by decide, by decide⟩

-- § 13.2: Case Extension Paths
-- (@cite{heine-2009} §29.3, Table 29.6)

/-- Extension from one case function to another (@cite{heine-2009} Table 29.6).

    When a case marker's use is extended from one syntactic context to another,
    the source function is less grammaticalized than the target. Direction is
    always concrete/peripheral → abstract/core.

    Three Table 29.6 targets are not representable as `Case` values and are
    omitted: **purposive** (from allative, benefactive), **manner** (from
    comitative, instrumental), **agent** (from locative; collapses with
    ergative in our system). The A → S core realignment is also omitted
    (it concerns grammatical roles, not morphological cases).

    See also `Phenomena.Possession.Typology.PossessionSource` for
    @cite{heine-2009} Table 29.5 (possessive case sources, adapted from
    @cite{heine-1997}). -/
def caseExtension : Case → List Case
  | .abl  => [.caus, .gen, .part, .inst]  -- cause, possessive, partitive, instrumental
  | .all  => [.ben, .dat, .acc]           -- benefactive, dative, accusative/O
  | .com  => [.inst, .erg, .gen]          -- instrumental, ergative, possessive
  | .dat  => [.acc]                       -- accusative/O
  | .inst => [.erg]                       -- ergative
  | .loc  => [.com, .erg, .inst]          -- comitative, ergative, instrumental
  | _     => []

-- Per-entry verification (one theorem per Table 29.6 row)

theorem abl_extends_inst : Case.inst ∈ caseExtension .abl := by simp [caseExtension]
theorem abl_extends_caus : Case.caus ∈ caseExtension .abl := by simp [caseExtension]
theorem abl_extends_gen  : Case.gen  ∈ caseExtension .abl := by simp [caseExtension]
theorem abl_extends_part : Case.part ∈ caseExtension .abl := by simp [caseExtension]

theorem all_extends_ben : Case.ben ∈ caseExtension .all := by simp [caseExtension]
theorem all_extends_dat : Case.dat ∈ caseExtension .all := by simp [caseExtension]
theorem all_extends_acc : Case.acc ∈ caseExtension .all := by simp [caseExtension]

theorem com_extends_inst : Case.inst ∈ caseExtension .com := by simp [caseExtension]
theorem com_extends_erg  : Case.erg  ∈ caseExtension .com := by simp [caseExtension]
theorem com_extends_gen  : Case.gen  ∈ caseExtension .com := by simp [caseExtension]

theorem dat_extends_acc : Case.acc ∈ caseExtension .dat := by simp [caseExtension]

theorem inst_extends_erg : Case.erg ∈ caseExtension .inst := by simp [caseExtension]

theorem loc_extends_com  : Case.com  ∈ caseExtension .loc := by simp [caseExtension]
theorem loc_extends_erg  : Case.erg  ∈ caseExtension .loc := by simp [caseExtension]
theorem loc_extends_inst : Case.inst ∈ caseExtension .loc := by simp [caseExtension]

-- Core grammatical cases are never sources of extension
theorem nom_no_extension : caseExtension .nom = [] := rfl
theorem acc_no_extension : caseExtension .acc = [] := rfl
theorem erg_no_extension : caseExtension .erg = [] := rfl
theorem abs_no_extension : caseExtension .abs = [] := rfl

-- § 13.3: Grammaticalization Chains
-- (@cite{heine-2009} §29.3, eq. (2))

/-- Chain (2a): allative > benefactive > purposive.
    Only the first step is representable as Case → Case. -/
theorem chain_all_ben : Case.ben ∈ caseExtension .all := all_extends_ben

/-- Chain (2b): allative > dative > accusative/O.
    Both steps are in `caseExtension`. -/
theorem chain_all_dat_acc :
    Case.dat ∈ caseExtension .all ∧
    Case.acc ∈ caseExtension .dat :=
  ⟨all_extends_dat, dat_extends_acc⟩

/-- Chain (2c): locative > comitative > instrumental > manner.
    The first two steps are representable as Case → Case. -/
theorem chain_loc_com_inst :
    Case.com ∈ caseExtension .loc ∧
    Case.inst ∈ caseExtension .com :=
  ⟨loc_extends_com, com_extends_inst⟩

/-- Transitivity: if c₁ extends to c₂ and c₂ extends to c₃, then c₃ is
    reachable from c₁ via a two-step grammaticalization chain. -/
def caseExtensionReachable2 (c₁ c₃ : Case) : Bool :=
  (caseExtension c₁).any fun c₂ => (caseExtension c₂).any (· == c₃)

/-- Accusative is reachable from allative in two steps (via dative). -/
theorem acc_reachable_from_all :
    caseExtensionReachable2 .all .acc = true := by native_decide

/-- Instrumental is reachable from locative in two steps (via comitative). -/
theorem inst_reachable_from_loc :
    caseExtensionReachable2 .loc .inst = true := by native_decide

-- § 13.4: Beyond-Case Grammaticalization
-- (@cite{heine-2009} §29.4)

/-- Case markers can further grammaticalize into non-case functions.
    These are the four main directions (@cite{heine-2009} §29.4). -/
inductive BeyondCaseTarget where
  /-- Case → clause subordinator (e.g., Newari instrumental *-na* →
      temporal subordinator). -/
  | clauseSubordinator
  /-- Case → modality marker: subordinate clauses acquire subjunctive/
      irrealis readings (connects to `Semantics.Modality.Narrog`). -/
  | modalMarker
  /-- Comitative → NP conjunction 'and' (e.g., *X with Y* → *X and Y*). -/
  | conjunction
  /-- Purposive → future tense marker. -/
  | tenseMarker
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 14: Comparative Entry
-- ============================================================================

/-- A language's comparative construction entry (@cite{stassen-1985}). -/
structure ComparativeEntry where
  standardCase : Case
  caseAssignment : CaseAssignment
  fixedEncoding : Option FixedCaseEncoding
  standardMarker : String
  hasDegreeMorphology : Bool
  deriving Repr, BEq

end Core
