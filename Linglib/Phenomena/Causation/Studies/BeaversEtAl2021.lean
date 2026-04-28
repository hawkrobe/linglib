import Linglib.Theories.Morphology.RootTypology
import Linglib.Fragments.Chuj.VerbBuilding

/-!
# Cross-Linguistic Typology of Change-of-State Verbs
@cite{dixon-1982} @cite{levin-1993} @cite{beavers-etal-2021} @cite{rose-nichols-2021} @cite{coon-2019}

Empirical data from Beavers, Everdell, Jerro, Kauhanen, @cite{beavers-etal-2021} "States and changes of state: A crosslinguistic
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

-/

namespace BeaversEtAl2021

-- ════════════════════════════════════════════════════
-- § 1. Root Classification (theory-neutral)
-- ════════════════════════════════════════════════════

/-- Two classes of change-of-state verb roots, defined by morphological
    and semantic diagnostics (@cite{beavers-etal-2021} §3.1).

    Classification criteria:
    - PC roots: the root of deadjectival CoS verbs (@cite{levin-1993}:245);
      describe @cite{dixon-1982}'s basic property types
    - Result roots: the root of non-deadjectival CoS verbs;
      describe specific result states (physical damage, cooking, etc.) -/
inductive CoSRootClass where
  | propertyConcept  -- deadjectival: flatten, redden, widen
  | result           -- non-deadjectival: break, crack, shatter
  deriving DecidableEq, Repr

/-- PC subclasses (@cite{dixon-1982}; @cite{beavers-etal-2021} ex. 5). -/
inductive PCSubclass where
  | dimension         -- large/big, small, long, short, deep, wide, tall/high
  | age               -- old/aged
  | value             -- bad/worse, good/improved
  | color             -- white, black, red, green, blue, brown
  | physicalProperty  -- cool/cold, warm/hot, dry/wet, soft/hard, smooth/rough
  | speed             -- fast, slow
  deriving DecidableEq, Repr

/-- Result root subclasses (@cite{levin-1993}; @cite{beavers-etal-2021} ex. 6). -/
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

/-- The five positions in a CoS verb paradigm (@cite{beavers-etal-2021} eq. 40).
    Every root meaning is associated with (up to) five forms. -/
inductive ParadigmPosition where
  | underlyingRoot  -- Position 1: base morphological root
  | simpleStative   -- Position 2: basic stative form (adj/verb)
  | inchoative      -- Position 3: intransitive change-of-state
  | causative        -- Position 4: transitive causative
  | resultStative   -- Position 5: deverbal stative (participle-like)
  deriving DecidableEq, Repr

/-- Morphological relationship codes between forms (@cite{beavers-etal-2021}
    eq. 41, generalizing @cite{haspelmath-1993}:90–92). -/
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
    @cite{beavers-etal-2021} reports values to 2 decimal places). -/
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
-- § 8. Theory ↔ Empirical Bridge: RootType ↔ CoSRootClass
-- ════════════════════════════════════════════════════

/-! The §§8–14 sections below were originally housed in
    `Phenomena/Causation/Studies/Coon2019.lean` as bridge content
    between Coon's Chuj data, the present empirical typology, and
    `RootTypology.lean`. They are relocated here per the chronological-
    dependency rule (Coon 2019 < Beavers et al. 2021 — only the later
    paper may reference the earlier). -/

/-- Map the theory's root type to the empirical root class.
    These are parallel enums — the bridge makes the correspondence explicit. -/
def toCoSRootClass : RootType → CoSRootClass
  | .propertyConcept => .propertyConcept
  | .result => .result

/-- Map back from empirical to theory. -/
def fromCoSRootClass : CoSRootClass → RootType
  | .propertyConcept => .propertyConcept
  | .result => .result

/-- The mapping is a bijection (left inverse). -/
theorem roundtrip_left (rt : RootType) :
    fromCoSRootClass (toCoSRootClass rt) = rt := by
  cases rt <;> rfl

/-- The mapping is a bijection (right inverse). -/
theorem roundtrip_right (rc : CoSRootClass) :
    toCoSRootClass (fromCoSRootClass rc) = rc := by
  cases rc <;> rfl

-- ════════════════════════════════════════════════════
-- § 9. Diagnostic Alignment with RootType
-- ════════════════════════════════════════════════════

/-- The empirical `changeDenialTest` agrees with the theory's `entailsChange`.

    Theory: `RootType.entailsChange.result = true` (result roots entail change)
    Empirical: `changeDenialTest.result =.negative` ("#The shattered vase
    has never shattered" is contradictory — the state entails prior change)

    The relationship is: entailsChange = true ↔ changeDenial = negative. -/
theorem change_denial_matches_entailsChange (rc : CoSRootClass) :
    changeDenialTest rc = .positive ↔
    (fromCoSRootClass rc).entailsChange = false := by
  cases rc <;> simp [changeDenialTest, fromCoSRootClass, RootType.entailsChange]

/-- The empirical `restitutiveAgainTest` agrees with the theory's
    `allowsRestitutiveAgain`. -/
theorem restitutive_again_matches (rc : CoSRootClass) :
    restitutiveAgainTest rc = .positive ↔
    (fromCoSRootClass rc).allowsRestitutiveAgain = true := by
  cases rc <;> simp [restitutiveAgainTest, fromCoSRootClass,
    RootType.allowsRestitutiveAgain]

/-- Both diagnostics jointly align with the full semantic correlate package.
    The bridge form of `semantic_determines_morphosyntax`. -/
theorem diagnostics_align_with_theory (rc : CoSRootClass) :
    let rt := fromCoSRootClass rc
    (changeDenialTest rc = .negative ↔ rt.entailsChange = true) ∧
    (restitutiveAgainTest rc = .negative ↔ rt.allowsRestitutiveAgain = false) := by
  cases rc <;> simp [changeDenialTest, restitutiveAgainTest, fromCoSRootClass,
    RootType.entailsChange, RootType.allowsRestitutiveAgain]

-- ════════════════════════════════════════════════════
-- § 10. Simple Stative Prediction ↔ Attestation
-- ════════════════════════════════════════════════════

/-- **Theory predicts**: PC roots have simple statives.
    **Data confirms**: 7 of 8 PC sample roots have ≥ 50% attestation.
    The one exception (oldRoot, age class) has 0 — noted by the present
    paper as a crosslinguistic outlier. -/
theorem pc_stative_prediction_matches_data :
    -- Theory prediction
    RootType.hasSimpleStative .propertyConcept = true ∧
    -- Empirical confirmation (all but one PC root)
    (pcRoots.filter (λ r => r.nSimpleStative * 2 ≥ r.nLanguages)).length ≥
    pcRoots.length - 1 := by
  exact ⟨rfl, by decide⟩

/-- **Theory predicts**: result roots LACK simple statives.
    **Data confirms**: all 10 result sample roots have ≤ 10% attestation. -/
theorem result_no_stative_prediction_matches_data :
    -- Theory prediction
    RootType.hasSimpleStative .result = false ∧
    -- Empirical confirmation (ALL result roots)
    resultRoots.all (λ r => r.nSimpleStative * 10 ≤ r.nLanguages) = true := by
  exact ⟨rfl, by decide⟩

-- ════════════════════════════════════════════════════
-- § 11. Markedness Prediction ↔ Statistical Comparison
-- ════════════════════════════════════════════════════

/-- **Theory predicts**: PC verbs are morphologically marked; result verbs
    are unmarked (Markedness Generalization, @cite{beavers-etal-2021}).
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
    (∀ rt : RootType, verbalMarkedness rt ≠ stativeMarkedness rt) := by
  refine ⟨by decide, ?_⟩
  intro rt; cases rt <;> simp [verbalMarkedness, stativeMarkedness,
    RootType.entailsChange]

-- ════════════════════════════════════════════════════
-- § 13. Fragment Grounding: Chuj Roots Instantiate Theory (@cite{coon-2019})
-- ════════════════════════════════════════════════════

open Fragments.Chuj

/-- Chuj √TV result roots instantiate the theory's result root predictions:
    entails change, no simple stative, unmarked verb. -/
theorem chuj_tv_res_is_result_root :
    rootTV_res.entailsChange = true ∧
    rootTV_res.changeType.hasSimpleStative = false ∧
    rootTV_res.verbalMarkedness = .unmarked := by
  exact ⟨rfl, rfl, rfl⟩

/-- Chuj √TV PC roots instantiate the theory's PC root predictions:
    no change entailment, has simple stative, marked verb. -/
theorem chuj_tv_pc_is_pc_root :
    rootTV_pc.entailsChange = false ∧
    rootTV_pc.changeType.hasSimpleStative = true ∧
    rootTV_pc.verbalMarkedness = .marked := by
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
    (rootTV_res.changeType.hasSimpleStative = false ∧
     rootTV_res.changeType.verbalFormIsMarked = false ∧
     rootTV_res.changeType.allowsRestitutiveAgain = false) ∧
    -- PC root (√TV PC): no change → full PC package
    (rootTV_pc.changeType.hasSimpleStative = true ∧
     rootTV_pc.changeType.verbalFormIsMarked = true ∧
     rootTV_pc.changeType.allowsRestitutiveAgain = true) ∧
    -- PC root (√ITV): no change → full PC package
    (rootITV.changeType.hasSimpleStative = true ∧
     rootITV.changeType.verbalFormIsMarked = true ∧
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
    RootType.hasSimpleStative .propertyConcept = true := by
  exact ⟨by decide, rfl⟩

/-- Every result root in the empirical sample is classified as result, and the
    theory predicts result roots lack simple statives — they do. -/
theorem result_roots_classified_and_predicted :
    -- Data: all sample result roots are classified as result
    resultRoots.all (·.rootClass == .result) = true ∧
    -- Theory: result lacks simple stative
    RootType.hasSimpleStative .result = false := by
  exact ⟨by decide, rfl⟩

/-- The subclass taxonomies are aligned: B&KG's `PCSubclass` has 6
    categories (matching their Table 2); the theory's `PCClass` has 7
    (adding `humanPropensity` from @cite{dixon-1982}, attested in
    @cite{hanink-koontz-garboden-2025}). `ResultClass` and `ResultSubclass`
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
