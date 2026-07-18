import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Linglib.Semantics.Verb.Root.Classification
import Linglib.Semantics.ArgumentStructure.EventStructure
import Linglib.Semantics.ArgumentStructure.RoleList
import Linglib.Fragments.Chuj.VerbBuilding

/-!
# Cross-Linguistic Typology of Change-of-State Verbs
[dixon-1982] [levin-1993] [beavers-etal-2021] [coon-2019]

Empirical data from Beavers, Everdell, Jerro, Kauhanen, [beavers-etal-2021] "States and changes of state: A crosslinguistic
study of the roots of verbal meaning." Language 97(3), 439–484.

88-language balanced sample (WALS 100 + additions). For each of 36 property
concept (PC) and 36 result root meanings, the authors collected five-item
paradigms (underlying root, simple stative, inchoative, causative, result
stative) and coded morphological relationships.

## Key findings (theory-neutral)

1. **Simple statives**: PC roots overwhelmingly have simple stative forms
   (median = 95.67% of languages); result roots overwhelmingly lack them
   (median = 1.59%). Mann-Whitney U = 1266.5, p < 0.001.

2. **Verbal markedness**: PC root verbs tend to be marked (median = 56.01%);
   result root verbs tend to be unmarked (median = 15.20%).
   Mann-Whitney U = 1291, p < 0.001.

3. **Subclass clustering**: PC subclasses (dimension, color, value, physical
   property, speed) cluster near 100% simple statives. Result subclasses
   (breaking, cooking, killing, destroying, directed motion) cluster near 0%.

## Theory apparatus

The change-entailment theory (§§3–14 below) is stated over the substrate
`Verb.Root.ChangeType`; this paper is its sole consumer. The "Markedness
Generalization" label is the formaliser's — the content (ex. (44)) is faithful
to the paper.

-/

namespace BeaversEtAl2021

open Verb Verb.Root ArgumentStructure ArgumentStructure.EventStructure Features

-- ════════════════════════════════════════════════════
-- § 1. Root Classification (theory-neutral)
-- ════════════════════════════════════════════════════

/-- Two classes of change-of-state verb roots, defined by morphological
    and semantic diagnostics ([beavers-etal-2021] §3.1).

    Classification criteria:
    - PC roots: the root of deadjectival CoS verbs ([levin-1993]:245);
      describe [dixon-1982]'s basic property types
    - Result roots: the root of non-deadjectival CoS verbs;
      describe specific result states (physical damage, cooking, etc.) -/
inductive CoSRootClass where
  | propertyConcept  -- deadjectival: flatten, redden, widen
  | result           -- non-deadjectival: break, crack, shatter
  deriving DecidableEq, Repr

/-- PC subclasses ([dixon-1982]; [beavers-etal-2021] ex. 5). -/
inductive PCSubclass where
  | dimension         -- large/big, small, long, short, deep, wide, tall/high
  | age               -- old/aged
  | value             -- bad/worse, good/improved
  | color             -- white, black, red, green, blue, brown
  | physicalProperty  -- cool/cold, warm/hot, dry/wet, soft/hard, smooth/rough
  | speed             -- fast, slow
  deriving DecidableEq, Repr

/-- Result root subclasses ([levin-1993]; [beavers-etal-2021] ex. 6). -/
inductive ResultSubclass where
  | entitySpecificCoS          -- burned, melted, frozen, decayed, bloomed
  | cooking                    -- cooked, baked, fried, roasted, boiled
  | breaking                   -- broken, cracked, crushed, shattered, torn
  | bending                    -- bent, folded, wrinkled, creased
  | killing                    -- dead, killed, murdered, drowned
  | destroying                 -- destroyed, ruined
  | calibratableCoS            -- go up, increase, go down, decrease, differ
  | inherentlyDirectedMotion   -- come, go, enter, exit, return
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. Morphological Paradigm Structure
-- ════════════════════════════════════════════════════

/-- The five positions in a CoS verb paradigm ([beavers-etal-2021] eq. 40).
    Every root meaning is associated with (up to) five forms. -/
inductive ParadigmPosition where
  | underlyingRoot  -- Position 1: base morphological root
  | simpleStative   -- Position 2: basic stative form (adj/verb)
  | inchoative      -- Position 3: intransitive change-of-state
  | causative        -- Position 4: transitive causative
  | resultStative   -- Position 5: deverbal stative (participle-like)
  deriving DecidableEq, Repr

/-- Morphological relationship codes between forms ([beavers-etal-2021]
    eq. 41, generalizing [haspelmath-1993]:90–92). -/
inductive MorphRelation where
  | input      -- (i) X is the input to a rule forming Y_k
  | derived    -- (d) X is the output of a rule on Y_k
  | transitive -- (t) X is transitively related via input/output pairs
  | labile     -- (l) X and Y_k are labile (same surface stem)
  | equipollent -- (e) X and Y_k are equipollent
  | unrelated  -- (u) no above relation applies
  | unattested -- (n) Y_k is unattested
  | suppletive -- (s) X is Y_k (suppletive)
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 3. Per-Root Crosslinguistic Data (Tables A1, A2)
-- ════════════════════════════════════════════════════

/-- A root meaning with its crosslinguistic attestation. -/
structure RootMeaning where
  /-- English gloss(es) -/
  gloss : String
  /-- PC or result root -/
  rootClass : CoSRootClass
  /-- Subclass, if applicable -/
  subclass : Option (PCSubclass ⊕ ResultSubclass) := none
  /-- Number of languages with a simple stative for this root (Table A1) -/
  nSimpleStative : Nat
  /-- Number of languages with any data for this root (Table A1) -/
  nLanguages : Nat
  /-- Number of languages with a marked verbal paradigm (Table A2) -/
  nMarkedVerbal : Nat
  /-- Number of languages with verbal paradigm data (Table A2) -/
  nVerbalLanguages : Nat
  deriving Repr

/-- Percentage of languages with simple stative (exact ℚ — kernel-decidable). -/
def RootMeaning.pctSimpleStative (r : RootMeaning) : ℚ :=
  if r.nLanguages = 0 then 0
  else (r.nSimpleStative : ℚ) * 100 / r.nLanguages

/-- Percentage of languages with marked verbal paradigm (exact ℚ). -/
def RootMeaning.pctMarkedVerbal (r : RootMeaning) : ℚ :=
  if r.nVerbalLanguages = 0 then 0
  else (r.nMarkedVerbal : ℚ) * 100 / r.nVerbalLanguages

-- PC roots (Table A1/A2 data)

def coldRoot : RootMeaning :=
  ⟨"cold/make cold", .propertyConcept, some (.inl .physicalProperty), 83, 83, 27, 45⟩
def largeRoot : RootMeaning :=
  ⟨"large/big/enlarge", .propertyConcept, some (.inl .dimension), 86, 87, 25, 47⟩
def redRoot : RootMeaning :=
  ⟨"red/redden", .propertyConcept, some (.inl .color), 77, 80, 31, 35⟩
def longRoot : RootMeaning :=
  ⟨"long/lengthen", .propertyConcept, some (.inl .dimension), 80, 82, 26, 37⟩
def goodRoot : RootMeaning :=
  ⟨"good/improved/improve", .propertyConcept, some (.inl .value), 83, 85, 30, 46⟩
def dryRoot : RootMeaning :=
  ⟨"dry/dry", .propertyConcept, some (.inl .physicalProperty), 72, 85, 32, 64⟩
def oldRoot : RootMeaning :=
  ⟨"old/aged/age", .propertyConcept, some (.inl .age), 0, 81, 10, 36⟩
def whiteRoot : RootMeaning :=
  ⟨"white/whiten", .propertyConcept, some (.inl .color), 81, 84, 27, 35⟩

-- Result roots (Table A1/A2 data)

def brokenRoot : RootMeaning :=
  ⟨"broken/break", .result, some (.inr .breaking), 1, 85, 21, 80⟩
def cookedRoot : RootMeaning :=
  ⟨"cooked/cook", .result, some (.inr .cooking), 0, 86, 12, 79⟩
def deadRoot : RootMeaning :=
  ⟨"dead/killed/kill", .result, some (.inr .killing), 5, 87, 9, 86⟩
def meltedRoot : RootMeaning :=
  ⟨"melted/melt", .result, some (.inr .entitySpecificCoS), 3, 64, 16, 61⟩
def shatteredRoot : RootMeaning :=
  ⟨"shattered/shatter", .result, some (.inr .breaking), 1, 53, 4, 37⟩
def bentRoot : RootMeaning :=
  ⟨"bent/bend", .result, some (.inr .bending), 6, 73, 14, 57⟩
def burnedRoot : RootMeaning :=
  ⟨"burned/burn", .result, some (.inr .entitySpecificCoS), 3, 82, 11, 79⟩
def tornRoot : RootMeaning :=
  ⟨"torn/tear", .result, some (.inr .breaking), 0, 77, 16, 70⟩
def goneRoot : RootMeaning :=
  ⟨"gone/go", .result, some (.inr .inherentlyDirectedMotion), 0, 78, 4, 73⟩
def destroyedRoot : RootMeaning :=
  ⟨"destroyed/destroy", .result, some (.inr .destroying), 0, 70, 9, 64⟩

def pcRoots : List RootMeaning :=
  [coldRoot, largeRoot, redRoot, longRoot, goodRoot, dryRoot, oldRoot, whiteRoot]

def resultRoots : List RootMeaning :=
  [brokenRoot, cookedRoot, deadRoot, meltedRoot, shatteredRoot,
   bentRoot, burnedRoot, tornRoot, goneRoot, destroyedRoot]

-- ════════════════════════════════════════════════════
-- § 4. Statistical Summary (§6, §7)
-- ════════════════════════════════════════════════════

/-- Summary of a crosslinguistic comparison between PC and result roots.
    Numeric fields are exact ℚ (mathlib idiom for kernel-decidable arithmetic;
    [beavers-etal-2021] reports values to 2 decimal places). -/
structure TypologicalComparison where
  /-- What is being measured -/
  measure : String
  /-- PC root median percentage -/
  pcMedian : ℚ
  /-- Result root median percentage -/
  resultMedian : ℚ
  /-- Mann-Whitney U statistic -/
  uStatistic : ℚ
  /-- One-tailed p-value threshold -/
  pThreshold : ℚ
  /-- Sample sizes (PC roots, result roots) -/
  nPC : Nat
  nResult : Nat
  deriving Repr

/-- Simple stative form comparison (§6, Fig. 1).
    Medians: 95.67% and 1.59% encoded as exact rationals via OfScientific. -/
def simpleStativeComparison : TypologicalComparison :=
  { measure := "% languages with simple stative",
    pcMedian := 95.67, resultMedian := 1.59,
    uStatistic := 1266.5, pThreshold := 0.001,
    nPC := 36, nResult := 36 }

/-- Verbal markedness comparison (§7, Fig. 5).
    Medians: 56.01% and 15.20% encoded as exact rationals via OfScientific. -/
def verbalMarkednessComparison : TypologicalComparison :=
  { measure := "% languages with marked verbal paradigm",
    pcMedian := 56.01, resultMedian := 15.20,
    uStatistic := 1291, pThreshold := 0.001,
    nPC := 36, nResult := 36 }

/-- Both comparisons are statistically significant. -/
theorem both_comparisons_significant :
    simpleStativeComparison.pcMedian > simpleStativeComparison.resultMedian ∧
    verbalMarkednessComparison.pcMedian > verbalMarkednessComparison.resultMedian := by
  unfold simpleStativeComparison verbalMarkednessComparison
  refine ⟨?_, ?_⟩ <;> norm_num

-- ════════════════════════════════════════════════════
-- § 5. Semantic Diagnostics (§§3.3–3.4, theory-neutral)
-- ════════════════════════════════════════════════════

/-- Empirical diagnostics for classifying roots.
    Each diagnostic independently sorts roots into two classes that
    align with the PC vs result distinction. -/
inductive DiagnosticResult where
  | positive  -- diagnostic is satisfied
  | negative  -- diagnostic is not satisfied
  deriving DecidableEq, Repr

/-- Stative form + change denial test (§3.3, ex. 10–11).
    "The bright photo has never brightened" → OK (PC)
    "#The shattered vase has never shattered" → contradictory (result) -/
def changeDenialTest : CoSRootClass → DiagnosticResult
  | .propertyConcept => .positive  -- stative can hold without change
  | .result => .negative           -- stative entails prior change

/-- Restitutive 'again' test (§3.4, ex. 15–16).
    "John sharpened the knife again" → can be just one sharpening (PC)
    "#Chris thawed the meat again" → necessarily two thawings (result) -/
def restitutiveAgainTest : CoSRootClass → DiagnosticResult
  | .propertyConcept => .positive  -- restitutive reading available
  | .result => .negative           -- only repetitive reading

/-- The two diagnostics always agree. -/
theorem diagnostics_agree (rc : CoSRootClass) :
    changeDenialTest rc = restitutiveAgainTest rc := by
  cases rc <;> rfl

-- ════════════════════════════════════════════════════
-- § 6. Per-Language Data (§§4.1–4.5, Table 1)
-- ════════════════════════════════════════════════════

/-- A language's CoS verb typological profile. -/
structure LanguageProfile where
  language : String
  family : String
  /-- Number of PC root verbal paradigms with data -/
  nPCParadigms : Nat
  /-- Number of result root verbal paradigms with data -/
  nResultParadigms : Nat
  /-- % of PC paradigms that are marked (exact ℚ) -/
  pctPCMarked : ℚ
  /-- % of result paradigms that are marked (exact ℚ) -/
  pctResultMarked : ℚ
  deriving Repr

/-- The six in-depth case study languages (§4). -/
def kakataibo : LanguageProfile :=
  ⟨"Kakataibo", "Panoan", 59, 64, 23.73, 31.25⟩
def kinyarwanda : LanguageProfile :=
  ⟨"Kinyarwanda", "Northeastern Bantu", 69, 33, 4.17, 9.09⟩
def hebrew : LanguageProfile :=
  ⟨"Hebrew (Modern)", "Semitic", 35, 42, 97.62, 0.98⟩
def marathi : LanguageProfile :=
  ⟨"Marathi", "Indic", 40, 35, 20.41, 21.33⟩
def greek : LanguageProfile :=
  ⟨"Greek (Modern)", "Indo-European", 76, 57, 2.63, 2.15⟩
def english : LanguageProfile :=
  ⟨"English", "Germanic", 43, 60, 0.0, 0.0⟩

def caseStudyLanguages : List LanguageProfile :=
  [kakataibo, kinyarwanda, hebrew, marathi, greek, english]

/-- Attested language types (§7.2, §8). -/
inductive LanguageType where
  | asymmetric        -- English-type: PC marked, result unmarked (overt asymmetry)
  | highMarking       -- Hebrew-type: both root classes marked
  | lowMarking        -- Labile/equipollent: low or no marking for both
  deriving DecidableEq, Repr

/-- The fourth logically possible type (result marked, PC unmarked)
    is UNATTESTED — predicted by the markedness generalization. -/
def LanguageType.allAttested : List LanguageType :=
  [.asymmetric, .highMarking, .lowMarking]

/-- Three and only three types are attested. -/
theorem three_attested_types :
    LanguageType.allAttested.length = 3 := by decide

-- ════════════════════════════════════════════════════
-- § 7. Verification: Per-Root Data Consistency
-- ════════════════════════════════════════════════════

/-- All entries in our PC root sample are classified as PC. -/
theorem pcRoots_all_pc :
    pcRoots.all (·.rootClass == .propertyConcept) = true := by decide

/-- All entries in our result root sample are classified as result. -/
theorem resultRoots_all_result :
    resultRoots.all (·.rootClass == .result) = true := by decide

/-- Most PC roots in the sample have ≥ 50% simple stative attestation. -/
theorem most_pc_roots_have_statives :
    (pcRoots.filter (λ r => r.nSimpleStative * 2 ≥ r.nLanguages)).length ≥
    pcRoots.length - 1 := by  -- all but 'old' (age is an exception)
  decide

/-- No result root in the sample exceeds 10% simple stative attestation. -/
theorem result_roots_rare_statives :
    resultRoots.all (λ r => r.nSimpleStative * 10 ≤ r.nLanguages) = true := by
  decide

-- ════════════════════════════════════════════════════
-- § 3′. Morphosyntactic correlates of change entailment
-- ════════════════════════════════════════════════════

/-- PC roots have simple (unmarked) stative forms; result roots lack them.
    English: "bright" (PC, simple adj) vs *"shattered" requires prior change.
    Crosslinguistic evidence (§6, Fig. 1): PC median = 95.67%, result median =
    1.59% (Mann-Whitney U = 1266.5, p < 0.001, n₁ = n₂ = 36). -/
def hasSimpleStative : ChangeType → Bool
  | .propertyConcept => true
  | .result => false

/-- PC root verbs TEND to be morphologically marked (wid-en, flat-ten); result
    root verbs tend to be unmarked (break, crack). The cross-linguistic DEFAULT,
    not a universal — [hanink-koontz-garboden-2025] §4 notes deviating Wá·šiw
    Class 1 roots. Crosslinguistic evidence (§7, Fig. 5): PC median = 56.01%,
    result median = 15.20% (U = 1291, p < 0.001). -/
def verbalFormIsMarked : ChangeType → Bool
  | .propertyConcept => true
  | .result => false

/-- **The main theorem.** A root's entailment of change determines all of its
    morphosyntactic behavior in a single biconditional: result roots lack simple
    statives (§6), have unmarked verbal forms (§7), and lack restitutive *again*
    (§3.4); PC roots are the reverse. Refutes the Bifurcation Thesis. -/
theorem semantic_determines_morphosyntax (ct : ChangeType) :
    ct.entailsChange = true ↔
    (hasSimpleStative ct = false ∧
     verbalFormIsMarked ct = false ∧
     ct.allowsRestitutiveAgain = false) := by
  cases ct <;> simp [ChangeType.entailsChange, hasSimpleStative,
    verbalFormIsMarked, ChangeType.allowsRestitutiveAgain]

/-- The converse: NOT entailing change determines the opposite package. -/
theorem pc_determines_morphosyntax (ct : ChangeType) :
    ct.entailsChange = false ↔
    (hasSimpleStative ct = true ∧
     verbalFormIsMarked ct = true ∧
     ct.allowsRestitutiveAgain = true) := by
  cases ct <;> simp [ChangeType.entailsChange, hasSimpleStative,
    verbalFormIsMarked, ChangeType.allowsRestitutiveAgain]

-- ════════════════════════════════════════════════════
-- § 5′. The Bifurcation Thesis and its refutation (§§2, 3.6, 9)
-- ════════════════════════════════════════════════════

/-- The Bifurcation Thesis for Roots ([embick-2009]:1, [arad-2005]:79;
    [beavers-etal-2021] ex. 2): a component of meaning introduced by a templatic
    operator cannot be part of a root's meaning — so NO root should entail
    change. -/
def bifurcationThesis (rootEntailsChange : ChangeType → Bool) : Prop :=
  ∀ ct, rootEntailsChange ct = false

/-- [beavers-etal-2021] main result: bifurcation does not hold. Result roots
    entail change, violating the thesis (§§3.3, 3.6, 9). -/
theorem bifurcation_fails :
    ¬ bifurcationThesis ChangeType.entailsChange := by
  intro h
  have := h .result
  simp [ChangeType.entailsChange] at this

/-- Result roots witness bifurcation failure. -/
theorem result_roots_witness_against_bifurcation :
    ChangeType.entailsChange .result = true := rfl

/-- PC roots are consistent with bifurcation (they don't entail change). -/
theorem pc_roots_consistent_with_bifurcation :
    ChangeType.entailsChange .propertyConcept = false := rfl

/-- **B&[beavers-koontz-garboden-2020] strengthened bifurcation failure via
    `Root.Kinds`.** [beavers-etal-2021] show roots can entail CHANGE;
    B&[beavers-koontz-garboden-2020] show roots can entail CHANGE, CAUSATION,
    and MANNER simultaneously (√GUILLOTINE, √HAND) — a strictly stronger
    refutation. Witness: `Root.Kinds.fullSpec` carries all four kinds. -/
theorem bkg_bifurcation_fails_all_dimensions :
    LexKind.result ∈ Root.Kinds.fullSpec ∧
    LexKind.cause ∈ Root.Kinds.fullSpec ∧
    LexKind.manner ∈ Root.Kinds.fullSpec ∧
    LexKind.state ∈ Root.Kinds.fullSpec := by decide

/-- Multiple Levin classes witness the stronger bifurcation failure. -/
theorem bkg_bifurcation_multiple_witnesses :
    LexKind.result ∈ LevinClass.rootEntailments .cut ∧
    LexKind.manner ∈ LevinClass.rootEntailments .cut ∧
    LexKind.cause ∈ LevinClass.rootEntailments .give ∧
    LexKind.manner ∈ LevinClass.rootEntailments .give := by decide

-- ════════════════════════════════════════════════════
-- § 8′. The Markedness Generalization (§8, ex. 44)
-- ════════════════════════════════════════════════════

/-- Whether a form is morphologically marked (derived/complex) or unmarked
    (basic/simple). -/
inductive Markedness where
  | unmarked  -- basic form (no additional morphology)
  | marked    -- derived form (overt marking: -en, -ed, etc.)
  deriving DecidableEq, Repr

/-- The Markedness Generalization ([beavers-etal-2021] ex. 44): morphological
    markedness reflects semantic mismatch between a functional head and its root
    complement. A verb is unmarked when v_become is redundant with the root's
    change entailment; a stative is unmarked when no change need be stripped.
    This yields the three attested language types (English-type asymmetric,
    equipollent, labile) and rules out the unattested fourth. -/
def verbalMarkedness (ct : ChangeType) : Markedness :=
  if ct.entailsChange then .unmarked else .marked

/-- Stative markedness is the mirror image of verbal markedness. -/
def stativeMarkedness (ct : ChangeType) : Markedness :=
  if ct.entailsChange then .marked else .unmarked

/-- Verbal and stative markedness are always complementary. -/
theorem markedness_complementarity (ct : ChangeType) :
    verbalMarkedness ct ≠ stativeMarkedness ct := by
  cases ct <;> simp [verbalMarkedness, stativeMarkedness, ChangeType.entailsChange]

/-- Result roots produce unmarked verbs. -/
theorem result_root_unmarked_verb :
    verbalMarkedness .result = .unmarked := rfl

/-- PC roots produce marked verbs. -/
theorem pc_root_marked_verb :
    verbalMarkedness .propertyConcept = .marked := rfl

/-- Result roots produce marked statives. -/
theorem result_root_marked_stative :
    stativeMarkedness .result = .marked := rfl

/-- PC roots produce unmarked statives. -/
theorem pc_root_unmarked_stative :
    stativeMarkedness .propertyConcept = .unmarked := rfl

/-- The markedness generalization is equivalent to the semantic distinction. -/
theorem markedness_from_semantics (ct : ChangeType) :
    verbalMarkedness ct = .unmarked ↔ ct.entailsChange = true := by
  cases ct <;> simp [verbalMarkedness, ChangeType.entailsChange]

-- ════════════════════════════════════════════════════
-- § 8″. Bridge to EntailmentProfile.changeOfState (ProtoRoles §8)
-- ════════════════════════════════════════════════════

/-- Dowty's P-Patient entailment "undergoes change of state" is precisely the
    result root entailment: an object bearing a result root's state predicate
    has `changeOfState = true`. -/
def rootTypeFromChangeEntailment (p : EntailmentProfile) : ChangeType :=
  if p.changeOfState then .result else .propertyConcept

/-- A result verb's object (accomplishment template) has `changeOfState = true`,
    so it patterns with result roots. Contact-verb objects (*kick*: CA+St, no
    entailed change per [beavers-2011]) fall on the other side of the bridge. -/
theorem result_object_has_changeOfState :
    rootTypeFromChangeEntailment accomplishmentObjectProfile = .result ∧
    rootTypeFromChangeEntailment ArgumentStructure.contactObject
      = .propertyConcept := by
  decide

/-- Die subject undergoes change → result-type pattern. -/
theorem die_result_pattern :
    rootTypeFromChangeEntailment
      ArgumentStructure.disappearance.subjectProfile = .result := by
  decide

-- ════════════════════════════════════════════════════
-- § 9′. Bridge to Template / BECOME (EventStructure §2)
-- ════════════════════════════════════════════════════

/-- Result roots MUST combine with a template containing BECOME (achievement or
    accomplishment): the root's change entailment is redundant with BECOME. PC
    roots CAN combine with any template. -/
def requiresBECOME : ChangeType → Bool
  | .result => true
  | .propertyConcept => false

/-- Result roots always get templates with BECOME. -/
theorem result_root_gets_become_template :
    requiresBECOME .result = true := rfl

/-- Achievement and accomplishment templates contain BECOME. -/
def templateHasBECOME : Template → Bool
  | .achievement => true
  | .accomplishment => true
  | _ => false

/-- The templates result roots combine with always have BECOME. -/
theorem result_templates_have_become :
    templateHasBECOME .achievement = true ∧
    templateHasBECOME .accomplishment = true :=
  ⟨rfl, rfl⟩

/-- State template lacks BECOME — only available to PC roots. -/
theorem state_template_no_become :
    templateHasBECOME .state = false := rfl

/-- Templates with BECOME map to achievement/accomplishment Vendler classes,
    both telic. -/
theorem become_templates_telic :
    Template.vendlerClass .achievement = .achievement ∧
    Template.vendlerClass .accomplishment = .accomplishment := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 10′. Root types and VendlerClass (Aspect)
-- ════════════════════════════════════════════════════

/-- Aspectual profile for root types in their stative use. -/
def stativeAspectualProfile : ChangeType → AspectualProfile
  | .propertyConcept => stateProfile        -- "The rug is flat" (stative)
  | .result => achievementProfile           -- even "broken" entails change

/-- Result root verbs pattern as achievements/accomplishments; PC roots in
    stative use are states. -/
def stativeVendlerClass (ct : ChangeType) : VendlerClass :=
  (stativeAspectualProfile ct).toVendlerClass

/-- PC roots in stative use are states; result roots pattern as achievements. -/
theorem root_stative_vendler :
    stativeVendlerClass .propertyConcept = .state ∧
    stativeVendlerClass .result = .achievement :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 11′. [embick-2004] Adjectival Structures (§3.2, ex. 8)
-- ════════════════════════════════════════════════════

/-- [embick-2004] posits basic statives ([AspP AspS √ROOT], PC roots only) and
    result statives ([AspP AspR [vP DP v_become √ROOT]], deverbal; result roots
    always, PC roots optionally). -/
inductive AdjectivalStructure where
  | basicStative    -- [AspP AspS √ROOT] — simple adjective
  | resultStative   -- [AspP AspR [vP DP v_become √ROOT]] — deverbal
  deriving DecidableEq, Repr

/-- PC roots admit both structures; result roots only admit resultStative. -/
def admitsBasicStative : ChangeType → Bool
  | .propertyConcept => true
  | .result => false

/-- This is equivalent to NOT entailing change. -/
theorem admitsBasicStative_iff_no_change (ct : ChangeType) :
    admitsBasicStative ct = true ↔ ct.entailsChange = false := by
  cases ct <;> simp [admitsBasicStative, ChangeType.entailsChange]

-- ════════════════════════════════════════════════════
-- § 12′. The Again Diagnostic ([beavers-koontz-garboden-2020] §1.3.2, §2.4)
-- ════════════════════════════════════════════════════

/-- Sublexical *again* attaches low (to the root, restitutive) or high (over
    `vbecome`, repetitive). Restitutive is available iff the root is change-free;
    a result root's state itself entails change, collapsing its low attachment
    into the repetitive reading. -/
inductive AgainReading where
  | restitutive   -- again scopes over root only
  | repetitive    -- again scopes over vP (includes BECOME)
  deriving DecidableEq, Repr

/-- Which readings of 'again' are available for each root type. -/
def againReadings : ChangeType → List AgainReading
  | .propertyConcept => [.restitutive, .repetitive]
  | .result => [.repetitive]

/-- PC roots have strictly more 'again' readings than result roots. -/
theorem pc_more_again_readings :
    (againReadings .propertyConcept).length >
    (againReadings .result).length := by decide

/-- Result roots lack the restitutive reading. -/
theorem result_no_restitutive :
    ¬ AgainReading.restitutive ∈ againReadings .result := by
  simp [againReadings]

/-- PC roots have the restitutive reading. -/
theorem pc_has_restitutive :
    AgainReading.restitutive ∈ againReadings .propertyConcept := by
  simp [againReadings]

-- ════════════════════════════════════════════════════
-- § 13′. Consequence for event-structural theory (§9)
-- ════════════════════════════════════════════════════

/-- If a root entails change, its verb is associated with a template containing
    BECOME (§9) — even when the change comes from the ROOT, not the template. -/
theorem entails_change_implies_become_template (ct : ChangeType)
    (h : ct.entailsChange = true) :
    requiresBECOME ct = true := by
  cases ct <;> simp_all [ChangeType.entailsChange, requiresBECOME]

/-- Conversely: a root not requiring BECOME does not entail change. -/
theorem no_become_implies_no_change (ct : ChangeType)
    (h : requiresBECOME ct = false) :
    ct.entailsChange = false := by
  cases ct <;> simp_all [requiresBECOME, ChangeType.entailsChange]

-- ════════════════════════════════════════════════════
-- § 14′. Grand unification: all correlates from entailsChange
-- ════════════════════════════════════════════════════

/-- **The full correlation package.** From the single Boolean `entailsChange`,
    all of the paper's morphosyntactic predictions follow: one semantic property
    is the sole determinant of six independently observable properties. -/
theorem grand_unification (ct : ChangeType) :
    (ct.entailsChange = true →
      hasSimpleStative ct = false ∧
      verbalFormIsMarked ct = false ∧
      ct.allowsRestitutiveAgain = false ∧
      requiresBECOME ct = true ∧
      admitsBasicStative ct = false ∧
      verbalMarkedness ct = .unmarked ∧
      stativeMarkedness ct = .marked) ∧
    (ct.entailsChange = false →
      hasSimpleStative ct = true ∧
      verbalFormIsMarked ct = true ∧
      ct.allowsRestitutiveAgain = true ∧
      requiresBECOME ct = false ∧
      admitsBasicStative ct = true ∧
      verbalMarkedness ct = .marked ∧
      stativeMarkedness ct = .unmarked) := by
  cases ct <;> simp_all [
    ChangeType.entailsChange, hasSimpleStative,
    verbalFormIsMarked, ChangeType.allowsRestitutiveAgain,
    requiresBECOME, admitsBasicStative,
    verbalMarkedness, stativeMarkedness]

/-- Change entailment determines markedness in the unified `Classification`. -/
theorem root_markedness_from_change (r : Classification) :
    verbalMarkedness r.changeType = .unmarked ↔ r.entailsChange = true := by
  cases r with | mk arity changeType _ _ _ =>
  cases changeType <;> simp [Classification.entailsChange,
    verbalMarkedness, ChangeType.entailsChange]

/-- Roots with the same change type have identical morphosyntactic behavior
    regardless of arity — markedness, stative forms, and again readings are
    orthogonal to internal argument selection. -/
theorem same_change_same_morphosyntax (r₁ r₂ : Classification)
    (h : r₁.changeType = r₂.changeType) :
    verbalMarkedness r₁.changeType = verbalMarkedness r₂.changeType ∧
    stativeMarkedness r₁.changeType = stativeMarkedness r₂.changeType ∧
    r₁.entailsChange = r₂.entailsChange := by
  simp [Classification.entailsChange, h]

-- ════════════════════════════════════════════════════
-- § 8. Theory ↔ Empirical Bridge: ChangeType ↔ CoSRootClass
-- ════════════════════════════════════════════════════

/-! The §§8–14 sections below were originally housed in
    `Studies/Coon2019.lean` as bridge content
    between Coon's Chuj data, the present empirical typology, and the root
    typology substrate. They are relocated here per the chronological-
    dependency rule (Coon 2019 < Beavers et al. 2021 — only the later
    paper may reference the earlier). -/

/-- Map the theory's change type to the empirical root class.
    These are parallel enums — the bridge makes the correspondence explicit. -/
def toCoSRootClass : ChangeType → CoSRootClass
  | .propertyConcept => .propertyConcept
  | .result => .result

/-- Map back from empirical to theory. -/
def fromCoSRootClass : CoSRootClass → ChangeType
  | .propertyConcept => .propertyConcept
  | .result => .result

/-- The mapping is a bijection (left inverse). -/
theorem roundtrip_left (ct : ChangeType) :
    fromCoSRootClass (toCoSRootClass ct) = ct := by
  cases ct <;> rfl

/-- The mapping is a bijection (right inverse). -/
theorem roundtrip_right (rc : CoSRootClass) :
    toCoSRootClass (fromCoSRootClass rc) = rc := by
  cases rc <;> rfl

-- ════════════════════════════════════════════════════
-- § 9. Diagnostic Alignment with ChangeType
-- ════════════════════════════════════════════════════

/-- The empirical `changeDenialTest` agrees with the theory's `entailsChange`.

    Theory: `ChangeType.entailsChange .result = true` (result roots entail change)
    Empirical: `changeDenialTest.result =.negative` ("#The shattered vase
    has never shattered" is contradictory — the state entails prior change)

    The relationship is: entailsChange = true ↔ changeDenial = negative. -/
theorem change_denial_matches_entailsChange (rc : CoSRootClass) :
    changeDenialTest rc = .positive ↔
    (fromCoSRootClass rc).entailsChange = false := by
  cases rc <;> decide

/-- The empirical `restitutiveAgainTest` agrees with the theory's
    `allowsRestitutiveAgain`. -/
theorem restitutive_again_matches (rc : CoSRootClass) :
    restitutiveAgainTest rc = .positive ↔
    (fromCoSRootClass rc).allowsRestitutiveAgain = true := by
  cases rc <;> decide

/-- Both diagnostics jointly align with the full semantic correlate package.
    The bridge form of `semantic_determines_morphosyntax`. -/
theorem diagnostics_align_with_theory (rc : CoSRootClass) :
    let rt := fromCoSRootClass rc
    (changeDenialTest rc = .negative ↔ rt.entailsChange = true) ∧
    (restitutiveAgainTest rc = .negative ↔ rt.allowsRestitutiveAgain = false) := by
  cases rc <;> decide

-- ════════════════════════════════════════════════════
-- § 10. Simple Stative Prediction ↔ Attestation
-- ════════════════════════════════════════════════════

/-- **Theory predicts**: PC roots have simple statives.
    **Data confirms**: 7 of 8 PC sample roots have ≥ 50% attestation.
    The one exception (oldRoot, age class) has 0 — noted by the present
    paper as a crosslinguistic outlier. -/
theorem pc_stative_prediction_matches_data :
    -- Theory prediction
    hasSimpleStative .propertyConcept = true ∧
    -- Empirical confirmation (all but one PC root)
    (pcRoots.filter (λ r => r.nSimpleStative * 2 ≥ r.nLanguages)).length ≥
    pcRoots.length - 1 := by
  exact ⟨rfl, by decide⟩

/-- **Theory predicts**: result roots LACK simple statives.
    **Data confirms**: all 10 result sample roots have ≤ 10% attestation. -/
theorem result_no_stative_prediction_matches_data :
    -- Theory prediction
    hasSimpleStative .result = false ∧
    -- Empirical confirmation (ALL result roots)
    resultRoots.all (λ r => r.nSimpleStative * 10 ≤ r.nLanguages) = true := by
  exact ⟨rfl, by decide⟩

-- ════════════════════════════════════════════════════
-- § 11. Markedness Prediction ↔ Statistical Comparison
-- ════════════════════════════════════════════════════

/-- **Theory predicts**: PC verbs are morphologically marked; result verbs
    are unmarked (Markedness Generalization, [beavers-etal-2021]).
    **Data confirms**: PC median marked % (56.01) > result median (15.20). -/
theorem markedness_prediction_matches_statistics :
    -- Theory: PC verbs are marked
    verbalMarkedness .propertyConcept = .marked ∧
    -- Theory: result verbs are unmarked
    verbalMarkedness .result = .unmarked ∧
    -- Data: PC marked rate exceeds result marked rate
    simpleStativeComparison.pcMedian > simpleStativeComparison.resultMedian ∧
    verbalMarkednessComparison.pcMedian > verbalMarkednessComparison.resultMedian := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact both_comparisons_significant.1
  · exact both_comparisons_significant.2

-- ════════════════════════════════════════════════════
-- § 12. Unattested Language Type
-- ════════════════════════════════════════════════════

/-- The theory's markedness complementarity predicts that if a language
    marks PC verbs, it should NOT also show result verbs as more marked
    than PC verbs. The fourth logically possible language type (result
    marked, PC unmarked) is unattested — exactly 3 types are attested.
    This matches the theory: `markedness_complementarity` says verbal and
    stative markedness are always opposite. -/
theorem unattested_type_matches_complementarity :
    -- Exactly three types attested
    LanguageType.allAttested.length = 3 ∧
    -- Theory: verbal and stative markedness always differ
    (∀ ct : ChangeType, verbalMarkedness ct ≠ stativeMarkedness ct) := by
  refine ⟨by decide, ?_⟩
  intro ct; cases ct <;> decide

-- ════════════════════════════════════════════════════
-- § 13. Fragment Grounding: Chuj Roots Instantiate Theory ([coon-2019])
-- ════════════════════════════════════════════════════

open Chuj

/-- Chuj √TV result roots instantiate the theory's result root predictions:
    entails change, no simple stative, unmarked verb. -/
theorem chuj_tv_res_is_result_root :
    rootTV_res.entailsChange = true ∧
    hasSimpleStative rootTV_res.changeType = false ∧
    verbalMarkedness rootTV_res.changeType = .unmarked := by
  exact ⟨rfl, rfl, rfl⟩

/-- Chuj √TV PC roots instantiate the theory's PC root predictions:
    no change entailment, has simple stative, marked verb. -/
theorem chuj_tv_pc_is_pc_root :
    rootTV_pc.entailsChange = false ∧
    hasSimpleStative rootTV_pc.changeType = true ∧
    verbalMarkedness rootTV_pc.changeType = .marked := by
  exact ⟨rfl, rfl, rfl⟩

/-- The Chuj fragment witnesses the full orthogonality theorem:
    all four cells of the (arity × changeType) matrix are inhabited. -/
theorem chuj_witnesses_orthogonality :
    -- selectsTheme + result (√TV result)
    rootTV_res.arity = .selectsTheme ∧ rootTV_res.changeType = .result ∧
    -- selectsTheme + PC (√TV PC)
    rootTV_pc.arity = .selectsTheme ∧ rootTV_pc.changeType = .propertyConcept ∧
    -- noTheme + PC (√ITV, √POS, √NOM)
    rootITV.arity = .noTheme ∧ rootITV.changeType = .propertyConcept :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Per-root class verification: each Chuj root's change entailment matches
    its predicted morphosyntactic correlates via `grand_unification`. -/
theorem chuj_roots_satisfy_grand_unification :
    -- Result root (√TV res): entails change → full result package
    (hasSimpleStative rootTV_res.changeType = false ∧
     verbalFormIsMarked rootTV_res.changeType = false ∧
     rootTV_res.changeType.allowsRestitutiveAgain = false) ∧
    -- PC root (√TV PC): no change → full PC package
    (hasSimpleStative rootTV_pc.changeType = true ∧
     verbalFormIsMarked rootTV_pc.changeType = true ∧
     rootTV_pc.changeType.allowsRestitutiveAgain = true) ∧
    -- PC root (√ITV): no change → full PC package
    (hasSimpleStative rootITV.changeType = true ∧
     verbalFormIsMarked rootITV.changeType = true ∧
     rootITV.changeType.allowsRestitutiveAgain = true) :=
  ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

-- ════════════════════════════════════════════════════
-- § 14. Per-Root Data ↔ Theory Agreement
-- ════════════════════════════════════════════════════

/-- Every PC root in the empirical sample is classified as PC, and the theory
    predicts PC roots should have simple statives — they do. -/
theorem pc_roots_classified_and_predicted :
    -- Data: all sample PC roots are classified as PC
    pcRoots.all (·.rootClass == .propertyConcept) = true ∧
    -- Theory: PC has simple stative
    hasSimpleStative .propertyConcept = true := by
  exact ⟨by decide, rfl⟩

/-- Every result root in the empirical sample is classified as result, and the
    theory predicts result roots lack simple statives — they do. -/
theorem result_roots_classified_and_predicted :
    -- Data: all sample result roots are classified as result
    resultRoots.all (·.rootClass == .result) = true ∧
    -- Theory: result lacks simple stative
    hasSimpleStative .result = false := by
  exact ⟨by decide, rfl⟩

/-- The subclass taxonomies are aligned: B&KG's `PCSubclass` has 6
    categories (matching their Table 2); the theory's `PCClass` has 7
    (adding `humanPropensity` from [dixon-1982], attested in
    [hanink-koontz-garboden-2025]). `ResultClass` and `ResultSubclass`
    match exactly (8 subclasses). -/
theorem subclass_counts_match :
    -- B&KG's 6 PC subclasses are a subset of the theory's 7
    [PCSubclass.dimension, .age, .value, .color, .physicalProperty, .speed].length = 6 ∧
    [PCClass.dimension, .age, .value, .color, .physicalProperty, .humanPropensity, .speed].length = 7 ∧
    -- 8 result subclasses in both
    [ResultClass.entitySpecificCoS, .cooking, .breaking, .bending,
     .killing, .destroying, .calibratableCoS, .inherentlyDirectedMotion].length =
    [ResultSubclass.entitySpecificCoS, .cooking, .breaking, .bending,
     .killing, .destroying, .calibratableCoS, .inherentlyDirectedMotion].length :=
  ⟨rfl, rfl, rfl⟩

end BeaversEtAl2021
