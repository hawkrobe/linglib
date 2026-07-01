import Linglib.Semantics.Quantification.BinominalDefs
import Linglib.Semantics.Quantification.Binominal
import Linglib.Fragments.English.Binominals
import Linglib.Studies.Traugott2010

/-!
# ten Wolde (2023): The English Binominal Noun Phrase
[ten-wolde-2023]

End-to-end study file connecting the core taxonomy, semantic theory,
and English fragment data to the empirical claims in [ten-wolde-2023].

## Key claims formalized

1. **Six-way taxonomy** (Table 2.2): N+PP, head-classifier, pseudo-partitive,
   evaluative BNP, evaluative modifier, binominal intensifier — each with
   distinct diagnostic profiles.

2. **Grammaticalization cline** (Ch. 5–6): N₁ nouns progress through the six
   stages with increasing semantic bleaching, loss of nounhood features
   (plural, number agreement), and reanalysis of [N₁ of a] as a constituent.

3. **Three-way evaluative distinction** (Table 4.2, Ch. 4): EBNP, EM, and BI
   are separate constructions with different semantic composition,
   premodification patterns, and diagnostic properties.

4. **Semantic class predicts path** (Ch. 5): inanimate N₁ nouns develop
   pseudo-partitive readings; animate and abstract N₁ nouns generally
   skip pseudo-partitive and enter evaluative uses directly.
-/

namespace TenWolde2023

open Quantification.Binominal
open Quantification.Binominal
open Semantics.Gradability.GradableNouns (exampleIdiot)
open English.Binominals

-- ═══════════════════════════════════════════════════════════════
-- § 1: Table 4.2 — Diagnostic Profile Verification
-- ═══════════════════════════════════════════════════════════════

/-! ### Table 4.2: Overview of evaluative categories

The three evaluative constructions differ on multiple diagnostics.
These theorems verify the Table 4.2 claims against the formalized
diagnostic functions in `Quantification.Binominal`. -/

/-- EBNP: N₁ allows plural, Det₂ marks number, of replaceable by copula. -/
theorem ebnp_profile :
    OfBinominalType.evaluative.n₁AllowsPlural = true ∧
    OfBinominalType.evaluative.det₂MarksNumber = true ∧
    OfBinominalType.evaluative.ofReplaceableByCopula = true ∧
    OfBinominalType.evaluative.n₁OfAIsConstituent = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- EM: N₁ frozen singular, Det₂ no longer marks number,
    [N₁ of a] is a constituent, of not replaceable by copula. -/
theorem em_profile :
    OfBinominalType.evaluativeModifier.n₁AllowsPlural = false ∧
    OfBinominalType.evaluativeModifier.det₂MarksNumber = false ∧
    OfBinominalType.evaluativeModifier.ofReplaceableByCopula = false ∧
    OfBinominalType.evaluativeModifier.n₁OfAIsConstituent = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- BI: same as EM on these diagnostics — further bleaching is
    syntactic (shifts into AdjP), not visible in these features. -/
theorem bi_profile :
    OfBinominalType.binominalIntensifier.n₁AllowsPlural = false ∧
    OfBinominalType.binominalIntensifier.det₂MarksNumber = false ∧
    OfBinominalType.binominalIntensifier.ofReplaceableByCopula = false ∧
    OfBinominalType.binominalIntensifier.n₁OfAIsConstituent = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- All three evaluative types are N₂-headed. -/
theorem all_evaluative_n₂_headed :
    OfBinominalType.evaluative.head = .n₂ ∧
    OfBinominalType.evaluativeModifier.head = .n₂ ∧
    OfBinominalType.binominalIntensifier.head = .n₂ := by
  exact ⟨rfl, rfl, rfl⟩

/-- Ch. 7, Table 4.2: N₁ premodification distinguishes EBNP from EM/BI.
    EBNP allows descriptive premodification of N₁ (*a total idiot of a
    doctor*); EM and BI block it (*#a total hell of a time*) because
    [N₁ of a] has been reanalyzed as a modifier unit. -/
theorem premod_distinguishes_evaluative_types :
    OfBinominalType.evaluative.n₁AllowsDescriptivePremod = true ∧
    OfBinominalType.evaluativeModifier.n₁AllowsDescriptivePremod = false ∧
    OfBinominalType.binominalIntensifier.n₁AllowsDescriptivePremod = false := by
  exact ⟨rfl, rfl, rfl⟩

/-- Table 4.2: N₂ type restriction distinguishes BI from EBNP/EM.
    EBNP and EM restrict N₂ to count/collective nouns; BI extends to mass. -/
theorem n₂_type_distinguishes_bi :
    OfBinominalType.evaluative.n₂AllowsMass = false ∧
    OfBinominalType.evaluativeModifier.n₂AllowsMass = false ∧
    OfBinominalType.binominalIntensifier.n₂AllowsMass = true := by
  exact ⟨rfl, rfl, rfl⟩

/-- Table 4.2: N₁ & N₂ agreement loosens along the evaluative path. -/
theorem agreement_loosens_on_evaluative_path :
    OfBinominalType.evaluative.n₁N₂Agreement = .agree ∧
    OfBinominalType.evaluativeModifier.n₁N₂Agreement = .usuallyAgree ∧
    OfBinominalType.binominalIntensifier.n₁N₂Agreement = .noAgreement := by
  exact ⟨rfl, rfl, rfl⟩

/-- Table 4.2: *of* becomes optional at the BI stage. -/
theorem of_optional_at_bi :
    OfBinominalType.evaluative.ofObligatory = true ∧
    OfBinominalType.evaluativeModifier.ofObligatory = true ∧
    OfBinominalType.binominalIntensifier.ofObligatory = false := by
  exact ⟨rfl, rfl, rfl⟩

-- ═══════════════════════════════════════════════════════════════
-- § 2: Semantic Class → Grammaticalization Path
-- ═══════════════════════════════════════════════════════════════

/-! ### Ch. 5–6: Diachronic path depends on N₁ semantic class

Inanimate nouns (cake, nub, breeze, husk) develop pseudo-partitive
readings. Animate (beast, whale, snake) and abstract (hell, bitch)
nouns generally skip pseudo-partitive. -/

/-- All inanimate entries have pseudo-partitive in their construction list. -/
theorem inanimate_develop_pseudopartitive :
    cake.constructions.elem .pseudoPartitive = true ∧
    nub.constructions.elem .pseudoPartitive = true ∧
    breeze.constructions.elem .pseudoPartitive = true ∧
    husk.constructions.elem .pseudoPartitive = true := by
  constructor <;> (try constructor) <;> native_decide

/-- Most animate entries skip pseudo-partitive (beast, whale). -/
theorem animate_skip_pseudopartitive :
    beast.constructions.elem .pseudoPartitive = false ∧
    whale.constructions.elem .pseudoPartitive = false := by
  constructor <;> native_decide

/-- Snake is the exception: an animate noun with pseudo-partitive. -/
theorem snake_exception :
    snake.semanticClass = .animate ∧
    snake.constructions.elem .pseudoPartitive = true := by
  constructor <;> native_decide

/-- The semantic class predicate agrees with the entry data for
    all inanimate nouns in the corpus. -/
theorem inanimate_class_predicts :
    cake.semanticClass.developsPseudoPartitive = true ∧
    nub.semanticClass.developsPseudoPartitive = true ∧
    breeze.semanticClass.developsPseudoPartitive = true ∧
    husk.semanticClass.developsPseudoPartitive = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

-- ═══════════════════════════════════════════════════════════════
-- § 2b: Main Grammaticalization Path (Ch. 5–6, Ch. 8)
-- ═══════════════════════════════════════════════════════════════

/-! ### The main grammaticalization path

[ten-wolde-2023] Ch. 8: the main evaluative path is
N+PP → Head-Classifier → EBNP → EM → BI, skipping pseudo-partitive.
Animate and abstract nouns follow this path; inanimate nouns may
develop pseudo-partitive as an intermediate stage. -/

/-- Animate nouns skip pseudo-partitive: beast and whale have evaluative
    uses but no pseudo-partitive attestations. -/
theorem animate_main_path :
    beast.constructions.elem .nPP = true ∧
    beast.constructions.elem .headClassifier = true ∧
    beast.constructions.elem .pseudoPartitive = false ∧
    beast.constructions.elem .evaluative = true ∧
    beast.constructions.elem .evaluativeModifier = true ∧
    beast.constructions.elem .binominalIntensifier = true := by
  constructor <;> (try constructor) <;> native_decide

/-- Abstract nouns also skip pseudo-partitive (except *hell* which
    participates in all six). *bitch* follows the main path. -/
theorem abstract_main_path :
    bitch.constructions.elem .nPP = true ∧
    bitch.constructions.elem .pseudoPartitive = false ∧
    bitch.constructions.elem .evaluative = true ∧
    bitch.constructions.elem .evaluativeModifier = true := by
  constructor <;> (try constructor) <;> native_decide

/-- The semantic class predicate correctly predicts which nouns
    skip pseudo-partitive: animate and abstract predict no PP,
    inanimate predicts PP. -/
theorem semantic_class_predicts_path :
    beast.semanticClass.developsPseudoPartitive = false ∧
    whale.semanticClass.developsPseudoPartitive = false ∧
    bitch.semanticClass.developsPseudoPartitive = false ∧
    cake.semanticClass.developsPseudoPartitive = true ∧
    nub.semanticClass.developsPseudoPartitive = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ═══════════════════════════════════════════════════════════════
-- § 3: Grammaticalization Depth
-- ═══════════════════════════════════════════════════════════════

/-! ### Ch. 5: *hell* is the most grammaticalized N₁ noun

*hell* participates in all six constructions and has developed
reduced forms (*helluva*, *hella*), indicating advanced
grammaticalization. *whale* also has a reduced form (*whaleuva*)
but participates in only five constructions. -/

/-- *hell* is the only N₁ in the dataset that participates in all six types. -/
theorem hell_maximally_grammaticalized :
    hell.constructions.length = 6 ∧ hell.hasReducedForm = true := by
  constructor <;> rfl

/-- *whale* has a reduced form (*whaleuva*) but only five constructions. -/
theorem whale_reduced_not_all_six :
    whale.hasReducedForm = true ∧ whale.constructions.length = 5 := by
  constructor <;> rfl

/-- *hell* is the only entry in the dataset with all six constructions. -/
theorem hell_uniquely_all_six :
    ∀ e ∈ allN₁Entries, e.constructions.length = 6 → e.form = "hell" := by
  native_decide

-- ═══════════════════════════════════════════════════════════════
-- § 4: End-to-End Semantic Chain
-- ═══════════════════════════════════════════════════════════════

/-! ### Semantic composition across the three evaluative stages

Demonstrates the progression from EBNP (full gradable predicate)
to EM (evaluative measure) to BI (degree intensifier) using the
worked examples from `Semantics/Lexical/Noun/Binominal`. -/

/-- The three evaluative semantics form an entailment chain:
    BI → EM (proved), but EBNP is independent of EM. -/
theorem entailment_summary :
    -- BI entails EM (bi_entails_em instantiated)
    (biSemantics (Semantics.Gradability.Intensification.muHorrible 10)
      doctorQuality (Degree.thr 5) (Degree.thr 3) isDoctor .george = true →
     emSemantics (Semantics.Gradability.Intensification.muHorrible 10)
      doctorQuality (Degree.thr 3) isDoctor .george = true) ∧
    -- EBNP and EM have different truth conditions
    (ebnpSemantics exampleIdiot isDoctor .sarah = true ∧
     emSemantics (Semantics.Gradability.Intensification.muHorrible 10)
      doctorQuality (Degree.thr 3) isDoctor .sarah = false) := by
  constructor
  · exact bi_entails_em _ _ _ _ _ _
  · constructor <;> native_decide

-- ═══════════════════════════════════════════════════════════════
-- § 5: Binominal Subjectification
-- ═══════════════════════════════════════════════════════════════

/-! ### The EBNP → EM → BI cline as subjectification

[ten-wolde-2023] §4.5: the EBNP → EM → BI transitions are driven by
subjectification ([traugott-2010]) — N₁ shifts from ascribing
objective/physical properties to expressing the speaker's subjective
evaluation. Steps use `Traugott2010.SubjectificationStep`. -/

open Traugott2010 (SubjectificationStep)

/-- Subjectification steps in the binominal (N₁-of-N₂) domain. -/
def binominalSubjectificationSteps : List SubjectificationStep :=
  [ -- N+PP/HC → EBNP: the key subjectification step in the binominal domain.
    -- N₁ shifts from denoting objective referential properties to expressing
    -- the speaker's evaluative attitude.
    { expression := "N₁ in of-binominals"
      sourceMeaning := "N₁ denotes referential property (N+PP: the beast of the field)"
      targetMeaning := "N₁ ascribes evaluative property (EBNP: that idiot of a doctor)"
      sourceLevel := .nonSubjective
      targetLevel := .subjective
      directed := by decide }
  , -- EBNP → EM: N₁ bleaches from full gradable predicate to pure
    -- speaker evaluation. Subjectivity level maintained but semantics bleached.
    { expression := "[N₁ of a] in of-binominals"
      sourceMeaning := "N₁ ascribes evaluative property (EBNP: a beast of a man)"
      targetMeaning := "N₁ expresses speaker's subjective evaluation (EM: a hell of a game)"
      sourceLevel := .subjective
      targetLevel := .subjective
      directed := by decide }
  , -- EM → BI: N₁ further bleaches to degree intensifier.
    -- Subjectivity level maintained; the change is syntactic (shifts into AdjP).
    { expression := "[N₁ of a] in of-binominals"
      sourceMeaning := "N₁ as evaluative modifier (EM: a hell of a time)"
      targetMeaning := "N₁ as degree intensifier (BI: a hell of a good time)"
      sourceLevel := .subjective
      targetLevel := .subjective
      directed := by decide }
  ]

/-- The N+PP → EBNP step is a genuine subjectification (nonSubjective → subjective);
    the later steps maintain subjectivity while bleaching semantics further. -/
theorem binominal_steps_directed :
    ∀ s ∈ binominalSubjectificationSteps, s.sourceLevel ≤ s.targetLevel :=
  fun s hs => by
    simp [binominalSubjectificationSteps] at hs
    rcases hs with rfl | rfl | rfl <;> decide

end TenWolde2023
