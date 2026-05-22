import Linglib.Core.Relativization.Basic
import Linglib.Fragments.Hebrew.Relativization

/-!
# Landau 2026: Silent Resumption @cite{landau-2026}

A New Test for Ellipsis. *Linguistic Inquiry*, Early Access.

## The EIR Test

The **Ellipsis-Internal Resumption** (EIR) test: a novel diagnostic for
distinguishing deep from surface anaphora (@cite{hankamer-sag-1976}).

The argumentation chain:

1. **BVQ** (@cite{chomsky-1982}): at LF, every Ā-operator must bind
   some variable.
2. A resumptive pronoun inside a null constituent serves as a variable.
3. A resumptive pronoun can only exist inside a constituent with
   LF-visible internal structure.
4. Therefore: an Ā-operator can bind into a null element iff
   it is a surface anaphor (= ellipsis).

The EIR test has a distinctive advantage over the extraction test.
When extraction fails out of a null element, the result is ambiguous:
the element could be a deep anaphor (no structure → BVQ violation),
*or* a surface anaphor where derivational timing bleeds Ā-extraction.
When EIR fails, only the deep-anaphor explanation survives, because
resumptive dependencies are established at LF without intermediate
movement steps that ellipsis could bleed.

## Hebrew Results

Three ellipsis types confirmed via EIR in domains where extraction
is impossible (Hebrew DPs are absolute islands; P-stranding is barred):
- **nP-ellipsis**: previously established; EIR provides additional
  confirmation via EN/ENP contrast
- **DP-ellipsis**: debated; EIR provides novel argument for AE
- **PP-ellipsis**: novel; EIR provides first robust evidence for PPE

## Cross-Linguistic Mixed Anaphors

EIR diagnoses contested "mixed anaphors" as deep:
- English *do so* — fails EIR (cf. VP-ellipsis, which passes)
- Dutch *dat doen* — fails EIR
- Danish *det* — fails EIR
- Korean null objects — fail EIR (supporting *pro* over AE)
-/

namespace Landau2026

open Core

-- ═══════════════════════════════════════════════════════════════
-- § 1: Types
-- ═══════════════════════════════════════════════════════════════

/-- Anaphoric depth: whether a null element has internal syntactic
    structure at LF. @cite{hankamer-sag-1976}

    - Deep: no LF-visible structure; content recovered pragmatically
      or deictically. EN, NCA, *pro*, *do so*, *dat doen*, *det*.
    - Surface: full structure, phonologically deleted under identity
      with a linguistic antecedent. VP-ellipsis, ENP, AE, PPE. -/
inductive AnaphorDepth where
  | deep
  | surface
  deriving DecidableEq, Repr

/-- Syntactic domain of the null element. -/
inductive NullDomain where
  | nP  -- Noun phrase nucleus (complement of Num)
  | DP  -- Full determiner phrase
  | PP  -- Prepositional phrase
  | VP  -- Verb phrase
  deriving DecidableEq, Repr

-- ═══════════════════════════════════════════════════════════════
-- § 2: BVQ and EIR — Derivation Chain
-- ═══════════════════════════════════════════════════════════════

/-- Step 1: A null element has LF-visible internal structure
    iff it is a surface anaphor. -/
def AnaphorDepth.hasStructure : AnaphorDepth → Bool
  | .surface => true
  | .deep => false

/-- Step 2: A resumptive pronoun (= variable) can only be hosted
    inside a constituent with internal structure; there must be a
    syntactic position for it to occupy. -/
def canContainVariable (d : AnaphorDepth) : Bool := d.hasStructure

/-- Step 3: **BVQ** — an Ā-operator binding into a site is
    well-formed iff the site provides a variable to bind. -/
def bvqSatisfied (siteHasVariable : Bool) : Bool := siteHasVariable

/-- **EIR prediction**, derived from the chain:
    structure → can host resumptive → BVQ satisfied → grammatical. -/
def eirPrediction (d : AnaphorDepth) : Bool :=
  bvqSatisfied (canContainVariable d)

/-- The derivation chain collapses: EIR passes iff the null
    element has internal structure. -/
theorem eir_iff_structure (d : AnaphorDepth) :
    eirPrediction d = d.hasStructure := by
  cases d <;> rfl

-- ═══════════════════════════════════════════════════════════════
-- § 3: EIR vs Extraction — Diagnostic Comparison
-- ═══════════════════════════════════════════════════════════════

/-- What can be concluded from a diagnostic test result. -/
inductive Conclusion where
  | definitelySurface
  | definitelyDeep
  | inconclusive
  deriving DecidableEq, Repr

/-- The extraction test. Success is unambiguous (the operator
    binds a trace inside the overt structure → surface anaphor).
    Failure is ambiguous: it could mean the element is deep
    (no structure → BVQ), *or* that it is surface but derivational
    timing bleeds Ā-movement through the ellipsis site. -/
def extractionConclusion (success : Bool) : Conclusion :=
  if success then .definitelySurface else .inconclusive

/-- The EIR test. Both outcomes are unambiguous. Resumptive
    dependencies are established purely at LF (binding, not
    movement), so there is no derivational step for ellipsis
    timing to bleed. EIR is also insensitive to island constraints,
    since resumption freely crosses islands. -/
def eirConclusion (success : Bool) : Conclusion :=
  if success then .definitelySurface else .definitelyDeep

/-- EIR is never inconclusive. -/
theorem eir_always_conclusive (b : Bool) :
    eirConclusion b ≠ .inconclusive := by
  cases b <;> simp [eirConclusion]

/-- Extraction failure is inherently inconclusive. -/
theorem extraction_inconclusive_on_failure :
    extractionConclusion false = .inconclusive := rfl

/-- When extraction succeeds, it agrees with EIR: both conclude
    surface. This means EIR is a strict refinement — it agrees
    where extraction is informative, and resolves the cases where
    extraction is not. -/
theorem eir_refines_extraction (b : Bool) :
    extractionConclusion b = .definitelySurface →
    eirConclusion b = .definitelySurface := by
  cases b <;> simp [extractionConclusion, eirConclusion]

-- ═══════════════════════════════════════════════════════════════
-- § 4: Data
-- ═══════════════════════════════════════════════════════════════

/-- A datum for the Ellipsis-Internal Resumption test. -/
structure EIRDatum where
  language : String
  nullElement : String
  domain : NullDomain
  depth : AnaphorDepth
  /-- Does the null element pass the EIR test?
      (= can it host a resumptive pronoun bound by an Ā-operator?) -/
  eirGrammatical : Bool
  /-- Is extraction from this domain possible in the language?
      When `false`, the extraction test is inapplicable and EIR
      is the only viable syntactic diagnostic. -/
  extractionAvailable : Bool := true
  abarContext : String := ""
  source : String := ""
  deriving Repr

-- ───────────────────────────────────────────────────────────────
-- § 4.1: Hebrew nP Domain
-- ───────────────────────────────────────────────────────────────

/-- Empty noun (EN): deep anaphor. A bare n head; content recovered
    from a restricted deictic set (PERSON, THING, TIME, PLACE).
    No linguistic antecedent required. Fails EIR.
    NP-ellipsis in Hebrew is previously established; EIR provides
    additional confirmation. -/
def hebrewEN : EIRDatum :=
  { language := "Hebrew"
    nullElement := "Empty Noun (EN)"
    domain := .nP
    depth := .deep
    eirGrammatical := false
    extractionAvailable := false
    abarContext := "restrictive relative, interrogative, free relative"
    source := "§2.2, (18a–d)" }

/-- Elided noun phrase (ENP): surface anaphor. Full nP structure
    (root + arguments) deleted under identity with a linguistic
    antecedent; licensed by [E] on Num. Passes EIR: the resumptive
    pronoun inside the elided nP provides a variable. -/
def hebrewENP : EIRDatum :=
  { language := "Hebrew"
    nullElement := "Elided Noun Phrase (ENP)"
    domain := .nP
    depth := .surface
    eirGrammatical := true
    extractionAvailable := false
    abarContext := "restrictive relative, interrogative, maximizing relative"
    source := "§2.2, (19a–d)" }

-- ───────────────────────────────────────────────────────────────
-- § 4.2: Hebrew DP Domain
-- ───────────────────────────────────────────────────────────────

/-- Null complement anaphora (NCA) / *pro*: deep anaphor.
    No internal structure; content recovered pragmatically.
    Fails EIR. The existence of AE in Hebrew was debated;
    the EIR test provides a novel argument. -/
def hebrewNCA_DP : EIRDatum :=
  { language := "Hebrew"
    nullElement := "NCA / pro (null object)"
    domain := .DP
    depth := .deep
    eirGrammatical := false
    extractionAvailable := false
    abarContext := "restrictive relative, interrogative, free relative"
    source := "§3.2, (31a–d)" }

/-- Argument ellipsis (AE) / DP-ellipsis: surface anaphor.
    Full DP structure deleted under identity with a linguistic
    antecedent. Passes EIR. Novel argument for AE in Hebrew. -/
def hebrewAE : EIRDatum :=
  { language := "Hebrew"
    nullElement := "Argument Ellipsis (AE)"
    domain := .DP
    depth := .surface
    eirGrammatical := true
    extractionAvailable := false
    abarContext := "restrictive relative, interrogative, free relative"
    source := "§3.2, (32a–d)" }

-- ───────────────────────────────────────────────────────────────
-- § 4.3: Hebrew PP Domain
-- ───────────────────────────────────────────────────────────────

/-- Null PP via NCA: deep anaphor. PP argument omitted; content
    recovered pragmatically. Fails EIR. -/
def hebrewNCA_PP : EIRDatum :=
  { language := "Hebrew"
    nullElement := "NCA (null PP)"
    domain := .PP
    depth := .deep
    eirGrammatical := false
    extractionAvailable := false
    abarContext := "restrictive relative, interrogative, free relative"
    source := "§4.2, (37a–d)" }

/-- PP-ellipsis (PPE): surface anaphor. Full PP structure deleted
    under identity with a linguistic antecedent. Passes EIR.
    First robust evidence for PP-ellipsis; the paper argues this
    holds cross-linguistically, not only in Hebrew. -/
def hebrewPPE : EIRDatum :=
  { language := "Hebrew"
    nullElement := "PP-Ellipsis (PPE)"
    domain := .PP
    depth := .surface
    eirGrammatical := true
    extractionAvailable := false
    abarContext := "restrictive relative, interrogative, free relative"
    source := "§4.2, (38a–d)" }

-- ───────────────────────────────────────────────────────────────
-- § 4.4: Cross-Linguistic Mixed Anaphors
-- ───────────────────────────────────────────────────────────────

/-- English VP-ellipsis: surface anaphor. Left-dislocated
    constituent binds a resumptive possessive inside the elided VP.
    Passes EIR. Contrastive baseline for *do so*. -/
def englishVPE : EIRDatum :=
  { language := "English"
    nullElement := "VP-ellipsis"
    domain := .VP
    depth := .surface
    eirGrammatical := true
    abarContext := "left-dislocation"
    source := "§5, (44a–b)" }

/-- English *do so*: deep VP anaphor. Left-dislocation with
    resumptive binding into *do so* is ungrammatical.
    Ā-extraction is also impossible, but that is ambiguous between
    deep anaphor and derivational bleeding. EIR resolves the
    ambiguity: *do so* is deep. @cite{bruening-2019} -/
def englishDoSo : EIRDatum :=
  { language := "English"
    nullElement := "do so"
    domain := .VP
    depth := .deep
    eirGrammatical := false
    abarContext := "left-dislocation"
    source := "§5, (44c–d)" }

/-- Dutch *dat doen* 'do that': deep VP anaphor.
    Blocks most Ā-extractions. Fails EIR. -/
def dutchDatDoen : EIRDatum :=
  { language := "Dutch"
    nullElement := "dat doen"
    domain := .VP
    depth := .deep
    eirGrammatical := false
    abarContext := "left-dislocation"
    source := "§5, (45a–b)" }

/-- Danish *det* 'it': deep VP anaphor. Allows A-dependencies
    but not Ā-dependencies. Fails EIR. -/
def danishDet : EIRDatum :=
  { language := "Danish"
    nullElement := "det"
    domain := .VP
    depth := .deep
    eirGrammatical := false
    abarContext := "left-dislocation"
    source := "§5, (46a–b)" }

/-- Korean null objects: deep anaphor (*pro*). Left-dislocation
    mandates a resumptive in Korean, but null objects fail to host
    one — supporting the *pro* analysis over AE. -/
def koreanNullObj : EIRDatum :=
  { language := "Korean"
    nullElement := "null object"
    domain := .DP
    depth := .deep
    eirGrammatical := false
    abarContext := "left-dislocation"
    source := "§5, (47a–b)" }

-- ═══════════════════════════════════════════════════════════════
-- § 5: Data Collections
-- ═══════════════════════════════════════════════════════════════

def hebrewData : List EIRDatum :=
  [hebrewEN, hebrewENP, hebrewNCA_DP, hebrewAE, hebrewNCA_PP, hebrewPPE]

def mixedAnaphorData : List EIRDatum :=
  [englishDoSo, dutchDatDoen, danishDet, koreanNullObj]

def crossLingData : List EIRDatum :=
  [englishVPE] ++ mixedAnaphorData

def allData : List EIRDatum := hebrewData ++ crossLingData

-- ═══════════════════════════════════════════════════════════════
-- § 6: Per-Datum Verification
-- ═══════════════════════════════════════════════════════════════

-- Hebrew nP
theorem en_eir : hebrewEN.eirGrammatical = eirPrediction hebrewEN.depth := rfl
theorem enp_eir : hebrewENP.eirGrammatical = eirPrediction hebrewENP.depth := rfl

-- Hebrew DP
theorem nca_dp_eir :
    hebrewNCA_DP.eirGrammatical = eirPrediction hebrewNCA_DP.depth := rfl
theorem ae_eir : hebrewAE.eirGrammatical = eirPrediction hebrewAE.depth := rfl

-- Hebrew PP
theorem nca_pp_eir :
    hebrewNCA_PP.eirGrammatical = eirPrediction hebrewNCA_PP.depth := rfl
theorem ppe_eir : hebrewPPE.eirGrammatical = eirPrediction hebrewPPE.depth := rfl

-- Cross-linguistic
theorem vpe_eir : englishVPE.eirGrammatical = eirPrediction englishVPE.depth := rfl
theorem do_so_eir :
    englishDoSo.eirGrammatical = eirPrediction englishDoSo.depth := rfl
theorem dat_doen_eir :
    dutchDatDoen.eirGrammatical = eirPrediction dutchDatDoen.depth := rfl
theorem danish_det_eir :
    danishDet.eirGrammatical = eirPrediction danishDet.depth := rfl
theorem korean_null_eir :
    koreanNullObj.eirGrammatical = eirPrediction koreanNullObj.depth := rfl

-- ═══════════════════════════════════════════════════════════════
-- § 7: Summary Properties
-- ═══════════════════════════════════════════════════════════════

/-- All data are consistent: every datum's observed EIR result
    matches the prediction from its depth classification. -/
theorem all_eir_consistent :
    allData.all (λ d => d.eirGrammatical == eirPrediction d.depth) = true := by
  native_decide

/-- Hebrew has both deep and surface strategies in all three
    nominal domains (nP, DP, PP). -/
theorem hebrew_both_depths_all_domains :
    hebrewData.any (λ d => d.depth == .deep && d.domain == .nP) = true ∧
    hebrewData.any (λ d => d.depth == .surface && d.domain == .nP) = true ∧
    hebrewData.any (λ d => d.depth == .deep && d.domain == .DP) = true ∧
    hebrewData.any (λ d => d.depth == .surface && d.domain == .DP) = true ∧
    hebrewData.any (λ d => d.depth == .deep && d.domain == .PP) = true ∧
    hebrewData.any (λ d => d.depth == .surface && d.domain == .PP) = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Extraction is unavailable for all Hebrew domains tested.
    This is precisely why the EIR test is needed: it provides
    syntactic evidence where the extraction test cannot. -/
theorem hebrew_extraction_unavailable :
    hebrewData.all (λ d => !d.extractionAvailable) = true := by
  native_decide

/-- All four cross-linguistic mixed anaphors are diagnosed as deep. -/
theorem mixed_anaphors_deep :
    mixedAnaphorData.all (λ d => d.depth == .deep) = true := by
  native_decide

-- ═══════════════════════════════════════════════════════════════
-- § 8: Integration with Existing Infrastructure
-- ═══════════════════════════════════════════════════════════════

/-- Hebrew has a productive resumptive strategy in relativization
    — the prerequisite for applying the EIR test. The same
    resumptive pronoun type that `Core.NPRelType.resumptive` models
    for relative clauses is what the EIR test probes for inside
    ellipsis sites. -/
theorem hebrew_has_resumptive_strategy :
    Fragments.Hebrew.relSheResumptive.npRel = .resumptive := rfl

/-- The resumptive strategy in Hebrew relativization covers the
    genitive position on the Accessibility Hierarchy, which is
    where possessive resumptive pronouns (the most common type
    in the EIR data) sit. -/
theorem resumptive_covers_genitive :
    Fragments.Hebrew.relSheResumptive.covers .genitive = true := rfl

/-- The gap strategy does NOT cover genitive — this is why
    possessive dependencies in Hebrew require resumption, making
    the EIR test applicable. -/
theorem gap_excludes_genitive :
    Fragments.Hebrew.relSheGap.covers .genitive = false := rfl

end Landau2026
