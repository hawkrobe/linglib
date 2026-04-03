import Linglib.Theories.Syntax.Minimalism.Agreement.GenderResolution
import Linglib.Theories.Morphology.DM.VocabularyInsertion

/-!
# Adamson & Anagnostopoulou 2025 @cite{adamson-anagnostopoulou-2025}

Gender Features and Coordination Resolution in Greek and Other
Three-Gendered Languages: Implications for the Crosslinguistic
Representation of Gender. *Linguistic Inquiry* (Early Access).

## Core result

Cross-linguistic variation in coordination resolution (Table 2) is
derived from three interacting components, without stipulated defaults:

1. **Feature geometry**: language-specific hierarchies of privative
   gender features. In Greek, FEM is a dependent of MASC (= animate),
   so a feminine nominal also bears MASC. In Icelandic, MASC (= male)
   and FEM are independent under CLASS — neither entails the other.

2. **Dual-feature system**: interpretable features (iFs → LF) vs
   uninterpretable features (uFs → PF), linked by a redundancy
   rule that copies iFs to empty uF slots at Transfer.

3. **Percolation + conversion**: universal coordination resolution.
   iFs percolate from conjuncts to &P; shared iFs survive intersection
   (conversion); the Subset Principle selects the inflectional exponent.

**Table 2** — resolution patterns derived from geometry:

| Language  | Humans | Inanimates |
|-----------|--------|------------|
| Greek     | MASC   | NEUT       |
| Icelandic | NEUT   | NEUT       |
| BCS       | MASC   | MASC       |

## Y-model architecture

The derivation follows the Minimalist Y-model:

- **Narrow syntax**: nominals bear both iFs and uFs; percolation
  collects features at &P.
- **Transfer**: conversion intersects iFs; redundancy rule copies
  resolved iFs to empty uF slots.
- **PF**: Vocabulary Insertion (Subset Principle) maps uF sets to
  inflectional exponents.
- **LF**: Lexical Complementarity restricts feature interpretation
  (e.g., iMASC restricted to ⟦MASC⟧ − ⟦FEM⟧).

## Formalization

Resolution uses `GenderResolution.resolve` — the single compositional
endpoint — instantiated with `GenderNode` as the feature type. Each
prediction is a verified theorem.
-/

namespace Phenomena.Agreement.Studies.AdamsonAnagnostopoulou2025

open Theories.Syntax.Minimalism.Agreement.GenderResolution

-- ============================================================================
-- § 1: Gender Feature Nodes
-- ============================================================================

/-- Privative feature nodes in the gender geometry (§2.2).

    @cite{adamson-anagnostopoulou-2025} modifies @cite{harley-ritter-2002}:
    features are organized in language-specific hierarchies where more
    specific features entail broader features. The same labels appear
    across languages, but their geometric arrangement — and hence their
    semantic content — varies.

    Language-specific geometries:
    - **Greek** (17): CLASS > MASC > FEM (linear chain)
    - **Icelandic** (63): CLASS > {MASC, FEM} (independent siblings)
    - **BCS** (74): CLASS > INDIV > {GRP, MASC > ANIM > FEM} -/
inductive GenderNode where
  | cls    -- entity (organizing node CLASS; all languages)
  | masc   -- animate (Greek) / male (Icelandic)
  | fem    -- female/woman
  | indiv  -- individuation (BCS: dominates GRP and MASC)
  | grp    -- group/plural (BCS: under INDIV)
  | anim   -- animate (BCS: under MASC)
  deriving DecidableEq, Repr

open GenderNode

-- ============================================================================
-- § 2: Vocabulary Schemas (Subset Principle)
-- ============================================================================

/-- Inflection class for three-gendered languages. -/
inductive Infl where | fem | masc | neut
  deriving DecidableEq, Repr

/-- Greek vocabulary item schema (21).

    | uF specification | Exponent             |
    |------------------|----------------------|
    | {FEM, MASC}      | "feminine inflection" |
    | {MASC}           | "masculine inflection"|
    | ∅                | "neuter inflection"  |

    The Subset Principle selects the most specific matching item. -/
def greekVI (fs : List GenderNode) : Infl :=
  if fs.contains fem && fs.contains masc then .fem
  else if fs.contains masc then .masc
  else .neut

/-- Icelandic vocabulary schema — identical to Greek.
    The geometry difference, not the vocabulary, drives the divergent
    resolution patterns. -/
abbrev icelandicVI := @greekVI

/-- BCS vocabulary item schema (75).

    | uF specification        | Exponent              |
    |-------------------------|-----------------------|
    | {FEM, ANIM, MASC, INDIV}| "F inflection"        |
    | {ANIM, MASC, INDIV}     | "M animate inflection" |
    | {INDIV}                 | "M inanimate inflection"|
    | ∅                       | "N inflection"        |

    Simplified: FEM ∧ ANIM → F; INDIV present → M; else → N. -/
def bcsVI (fs : List GenderNode) : Infl :=
  if fs.contains fem && fs.contains anim then .fem
  else if fs.contains indiv then .masc
  else .neut

-- ============================================================================
-- § 3: Greek — Noun Data
-- ============================================================================

/-! ### Greek feature geometry (17)

    CLASS > MASC > FEM (linear chain).
    Feature interpretations (18):
    - CLASS: λx. x is an entity
    - MASC: λx. x is animate
    - FEM: λx. x is a woman

    Having FEM entails MASC; having MASC entails CLASS.
    Lexical Complementarity (19) restricts: iMASC picks out ⟦MASC⟧ − ⟦FEM⟧
    (animate non-women); iFEM picks out women; iCLASS picks out entities. -/

/-- Human feminine (*gineka* 'woman'): iFs = {CLASS, MASC, FEM}.
    Conceptual gender — all features interpretable. -/
private abbrev gkHF : FeatureBundle GenderNode :=
  [⟨cls, true⟩, ⟨masc, true⟩, ⟨fem, true⟩]

/-- Human masculine (*andras* 'man'): iFs = {CLASS, MASC}. -/
private abbrev gkHM : FeatureBundle GenderNode :=
  [⟨cls, true⟩, ⟨masc, true⟩]

/-- Inanimate feminine (*karekla* 'chair'): iCLASS + uMASC, uFEM.
    Only CLASS is interpretable; MASC and FEM are arbitrary. -/
private abbrev gkIF : FeatureBundle GenderNode :=
  [⟨cls, true⟩, ⟨masc, false⟩, ⟨fem, false⟩]

/-- Inanimate masculine (*pinakas* 'blackboard'): iCLASS + uMASC. -/
private abbrev gkIM : FeatureBundle GenderNode :=
  [⟨cls, true⟩, ⟨masc, false⟩]

/-- Inanimate neuter (*piruni* 'fork'): iCLASS only. -/
private abbrev gkIN : FeatureBundle GenderNode :=
  [⟨cls, true⟩]

-- ============================================================================
-- § 4: Greek — Resolution Predictions
-- ============================================================================

/-- (25) Uniform humans resolve to their shared gender. -/
theorem gk_uniform_fem :
    resolve gkHF gkHF = some [cls, masc, fem] := by native_decide

theorem gk_uniform_masc :
    resolve gkHM gkHM = some [cls, masc] := by native_decide

/-- (22a) Mismatched humans → {CLASS, MASC} → masculine plural.
    Intersection: {CLASS,MASC,FEM} ∩ {CLASS,MASC} = {CLASS,MASC}.
    FEM is eliminated because only one conjunct bears it. -/
theorem gk_human_mismatch :
    resolve gkHF gkHM = some [cls, masc] := by native_decide

theorem gk_human_mismatch_vi :
    greekVI [cls, masc] = .masc := by native_decide

/-- (22b, 40a-c) All inanimate mismatch combinations → {CLASS} → neuter.
    Percolation extracts only iCLASS from each conjunct (uFs excluded).
    This is NOT default insertion — it is the result of intersecting
    the iF sets, which contain only iCLASS for all inanimates. -/
theorem gk_inanim_MF :
    resolve gkIM gkIF = some [cls] := by native_decide

theorem gk_inanim_NF :
    resolve gkIN gkIF = some [cls] := by native_decide

theorem gk_inanim_NM :
    resolve gkIN gkIM = some [cls] := by native_decide

theorem gk_inanim_mismatch_vi :
    greekVI [cls] = .neut := by native_decide

/-- Mismatch Resolution Hypothesis (24): no default feature insertion.
    All resolution outcomes have non-empty intersection (matching). -/
theorem gk_no_default_human :
    (resolve gkHF gkHM).isSome = true := by native_decide

theorem gk_no_default_inanim :
    (resolve gkIM gkIF).isSome = true := by native_decide

-- ============================================================================
-- § 5: Greek — Fixed-Gender Humans
-- ============================================================================

/-! ### Fixed-gender human nominals (§3.2)

    *megalofiia* 'genius' is **grammatically** feminine (uFs) but its
    **conceptual** gender (iFs) tracks the referent. Resolution operates
    on iFs — crucial evidence for the Mismatch Resolution Hypothesis.

    *thima* 'victim' is grammatically neuter (uF = {CLASS}) but
    conceptually masculine/feminine depending on referent. -/

/-- *megalofiia* 'genius' referring to a man.
    uF = {CLASS, MASC, FEM} (arbitrary feminine), iF = {CLASS, MASC}. -/
private abbrev gkFixedFemMale : FeatureBundle GenderNode :=
  [⟨cls, true⟩, ⟨masc, true⟩,
   ⟨cls, false⟩, ⟨masc, false⟩, ⟨fem, false⟩]

/-- *thima* 'victim' referring to a woman.
    uF = {CLASS} (arbitrary neuter), iF = {CLASS, MASC, FEM}. -/
private abbrev gkFixedNeutFemale : FeatureBundle GenderNode :=
  [⟨cls, true⟩, ⟨masc, true⟩, ⟨fem, true⟩, ⟨cls, false⟩]

/-- (36) *megalofiia* (male referent) + sister → masculine (M♂ + F♀ = M).
    Despite both being grammatically feminine, iF resolution
    yields {CLASS,MASC} ∩ {CLASS,MASC,FEM} = {CLASS,MASC} → MASC. -/
theorem gk_fixed_genius_sister :
    resolve gkFixedFemMale gkHF = some [cls, masc] := by native_decide

theorem gk_fixed_genius_sister_vi :
    (resolve gkFixedFemMale gkHF).map greekVI = some .masc := by native_decide

/-- (37) *thima* (female referent) + her mother → feminine (N♀ + F♀ = F).
    Neuter noun's iFs are feminine (referent is female):
    {CLASS,MASC,FEM} ∩ {CLASS,MASC,FEM} = {CLASS,MASC,FEM} → FEM. -/
theorem gk_fixed_victim_mother :
    resolve gkFixedNeutFemale gkHF = some [cls, masc, fem] := by
  native_decide

theorem gk_fixed_victim_mother_vi :
    (resolve gkFixedNeutFemale gkHF).map greekVI = some .fem := by
  native_decide

-- ============================================================================
-- § 6: Greek — [H + I] Coordination
-- ============================================================================

/-! ### Humans + Inanimates (§3.5)

    When a human (percolating iFs) and an inanimate (percolating uFs)
    are coordinated, PF realization succeeds only if the features map
    to the same inflection class. Otherwise: PF crash → ineffability.

    Y-model significance: the crash happens at **PF**, not in narrow
    syntax. [H + I] coordination is syntactically well-formed; the
    problem is exponence of the resolved features. -/

/-- PF convergence test for [H + I] coordination.
    The human's iFs (→ uFs via redundancy rule at Transfer) must
    map to the same inflection as the inanimate's uFs. -/
def gkHIConverges (humanIFs inanimUFs : List GenderNode) : Bool :=
  greekVI humanIFs == greekVI inanimUFs

/-- (54a) M♂ + M■ → grammatical: both map to MASC.
    *kleftis* 'thief' (M) + *pinakas* 'painting' (M). -/
theorem gk_hi_matched_masc :
    gkHIConverges [cls, masc] [cls, masc] = true := by native_decide

/-- (54b) F♀ + F■ → grammatical: both map to FEM.
    *gineka* 'woman' (F) + *ombrela* 'umbrella' (F). -/
theorem gk_hi_matched_fem :
    gkHIConverges [cls, masc, fem] [cls, masc, fem] = true := by
  native_decide

/-- (47) M♂ + N■ → ineffable: MASC ≠ NEUT → PF crash.
    *kleftis* 'thief' (M♂) + *daxtilidi* 'ring' (N■).
    Human iFs → MASC; inanimate uFs → NEUT. No single exponent. -/
theorem gk_hi_crash :
    gkHIConverges [cls, masc] [cls] = false := by native_decide

/-- (56) Fixed-gender F♂ + M■ → grammatical: iFs match.
    *megalofiia* 'genius' (iF = M♂) + *pinakas* 'painting' (uF = M■).
    Human's iFs = {CLASS,MASC} → MASC; inanimate's uFs = {CLASS,MASC} → MASC.
    PF converges despite different grammatical genders. -/
theorem gk_hi_fixed_converge :
    gkHIConverges [cls, masc] [cls, masc] = true := by native_decide

-- ============================================================================
-- § 7: Greek — Fixed-Gender + Inanimate [H + I]
-- ============================================================================

/-! ### Fixed-gender humans + inanimates (§3.5)

    The paper's strongest evidence for the iF-based analysis. When a
    **fixed-gender human** is coordinated with an inanimate, the PF
    convergence depends on the human's **iFs** (conceptual gender),
    not their **uFs** (grammatical gender). -/

/-- (57a) *thima* (N♀ victim, male referent) + *pinakas* (M■) → MASC.
    iFs of victim (male) = {CLASS, MASC}; uFs of painting = {CLASS, MASC}.
    VI match: MASC = MASC → PF converges. -/
theorem gk_hi_fixed_victim_male :
    gkHIConverges [cls, masc] [cls, masc] = true := by native_decide

/-- (57b) *thima* (N♀ victim, female referent) + *fotografia* (F■) → FEM.
    iFs of victim (female) = {CLASS, MASC, FEM};
    uFs of picture = {CLASS, MASC, FEM}.
    VI match: FEM = FEM → PF converges. -/
theorem gk_hi_fixed_victim_female :
    gkHIConverges [cls, masc, fem] [cls, masc, fem] = true := by
  native_decide

/-- (57a corollary) *thima* (N♀, male ref) + *fotografia* (F■) → PF crash.
    iFs of victim (male) = {CLASS, MASC} → VI → MASC.
    uFs of picture = {CLASS, MASC, FEM} → VI → FEM.
    MASC ≠ FEM → crash. -/
theorem gk_hi_fixed_victim_male_fem_crash :
    gkHIConverges [cls, masc] [cls, masc, fem] = false := by native_decide

-- ============================================================================
-- § 8: Greek — Inanimate Uniform Patterns
-- ============================================================================

/-! ### Uniform inanimate coordination (38a-c)

    When two inanimates share the same grammatical gender, resolved
    agreement matches that gender. Under the paper's analysis, this
    obtains when inanimates percolate **uFs** (the alternative
    derivation in (39)): the &P has a singleton uF set, and PF
    realization succeeds with the shared exponent. -/

/-- (38a) F■ + F■ = F: *fusta* 'skirt' + *bluza* 'T-shirt'. -/
theorem gk_uniform_inanim_fem :
    greekVI [cls, masc, fem] = .fem := by native_decide

/-- (38b) M■ + M■ = M: *anaptiras* 'lighter' + *fakos* 'torch'. -/
theorem gk_uniform_inanim_masc :
    greekVI [cls, masc] = .masc := by native_decide

/-- (38c) N■ + N■ = N: *piruni* 'fork' + *kutali* 'spoon'. -/
theorem gk_uniform_inanim_neut :
    greekVI [cls] = .neut := by native_decide

-- ============================================================================
-- § 9: Greek — Clausal Subjects
-- ============================================================================

/-- (2a, 58) Clausal subjects lack gender features entirely.
    No features to percolate → no vocabulary item matches → neuter
    (the elsewhere exponent, least specified). -/
theorem gk_clausal_default : greekVI [] = .neut := by native_decide

-- ============================================================================
-- § 10: Icelandic
-- ============================================================================

/-! ### Icelandic feature geometry (63)

    ```
    (i/u)CLASS
       / \
    MASC   FEM    ← independent (no entailment)
    ```

    Unlike Greek, FEM is NOT a dependent of MASC. The crucial difference:
    MASC means 'male' (not 'animate'), so gender-mixed groups are excluded
    from both MASC (not all male) and FEM (not all female).
    Lexical Complementarity: no restriction between MASC and FEM
    (neither is a subset of the other). -/

/-- Icelandic human feminine: iFs = {CLASS, FEM}.
    No iMASC — FEM is independent of MASC in this geometry. -/
private abbrev isHF : FeatureBundle GenderNode :=
  [⟨cls, true⟩, ⟨fem, true⟩]

/-- Icelandic human masculine: iFs = {CLASS, MASC}. -/
private abbrev isHM : FeatureBundle GenderNode :=
  [⟨cls, true⟩, ⟨masc, true⟩]

/-- Icelandic inanimate feminine (*skeið* 'spoon'): iCLASS + uFEM.
    Only CLASS is interpretable; FEM is arbitrary. -/
private abbrev isIF : FeatureBundle GenderNode :=
  [⟨cls, true⟩, ⟨fem, false⟩]

/-- Icelandic inanimate masculine (*stóll* 'chair'): iCLASS + uMASC. -/
private abbrev isIM : FeatureBundle GenderNode :=
  [⟨cls, true⟩, ⟨masc, false⟩]

/-- Icelandic inanimate neuter (*epli* 'apple'): iCLASS only. -/
private abbrev isIN : FeatureBundle GenderNode :=
  [⟨cls, true⟩]

/-- (60) Mismatched humans → {CLASS} → neuter.
    {CLASS,MASC} ∩ {CLASS,FEM} = {CLASS}. Because MASC and FEM are
    independent siblings, only CLASS survives intersection. -/
theorem is_human_mismatch :
    resolve isHM isHF = some [cls] := by native_decide

theorem is_human_mismatch_vi :
    icelandicVI [cls] = .neut := by native_decide

/-- (59) Mismatched inanimates → {CLASS} → neuter.
    *frægð* 'fame' (F) + *frami* 'success' (M) → neuter plural.
    All Icelandic inanimates share iFs = {iCLASS} regardless of
    grammatical gender — uFs (uFEM, uMASC) are excluded from resolution. -/
theorem is_inanim_mismatch :
    resolve isIF isIM = some [cls] := by native_decide

/-- The geometry contrast: same labels, different geometry, different outcome.
    Greek {CLASS,MASC,FEM} ∩ {CLASS,MASC} = some {CLASS,MASC}.
    Icelandic {CLASS,FEM} ∩ {CLASS,MASC} = some {CLASS}.
    Same mechanism, different input → different result. -/
theorem geometry_drives_variation :
    resolve gkHF gkHM ≠ resolve isHF isHM := by
  native_decide

-- ============================================================================
-- § 11: BCS (Bosnian/Croatian/Serbian)
-- ============================================================================

/-! ### BCS feature geometry (74)

    ```
    CLASS
      |
    INDIV
     / \
    GRP  MASC
          |
        ANIM
          |
        FEM
    ```

    Key differences from Greek and Icelandic:
    1. MASC is under INDIV (not directly under CLASS)
    2. Neuter ≈ mass (no INDIV) → can't be counted or coordinated as count
    3. All coordinatable nominals have INDIV → resolved features include
       at least {INDIV} → vocabulary maps to masculine

    Vocabulary consequence: masculine is the "default" for coordination
    not by stipulation but because INDIV (required for plural) maps to
    masculine via the Subset Principle. -/

/-- BCS human feminine: iFs = {CLASS, INDIV, MASC, ANIM, FEM}. -/
private abbrev bcsHF : FeatureBundle GenderNode :=
  [⟨cls, true⟩, ⟨indiv, true⟩, ⟨masc, true⟩, ⟨anim, true⟩, ⟨fem, true⟩]

/-- BCS human masculine: iFs = {CLASS, INDIV, MASC, ANIM}. -/
private abbrev bcsHM : FeatureBundle GenderNode :=
  [⟨cls, true⟩, ⟨indiv, true⟩, ⟨masc, true⟩, ⟨anim, true⟩]

/-- BCS inanimate masculine (*pesak* 'sand'): iFs = {CLASS, INDIV, MASC}.
    MASC without ANIM → inanimate interpretation. -/
private abbrev bcsIM : FeatureBundle GenderNode :=
  [⟨cls, true⟩, ⟨indiv, true⟩, ⟨masc, true⟩]

/-- BCS inanimate feminine (*knjiga* 'book'): iFs = {CLASS, INDIV, MASC},
    uFs include ANIM + FEM (arbitrary feminine). -/
private abbrev bcsIF : FeatureBundle GenderNode :=
  [⟨cls, true⟩, ⟨indiv, true⟩, ⟨masc, true⟩,
   ⟨anim, false⟩, ⟨fem, false⟩]

/-- BCS neuter noun (*mleko* 'milk'): iFs = {CLASS} only.
    Neuter = mass in BCS: no INDIV. This is why neuter nouns cannot
    form count plurals — they lack the individuation feature. -/
private abbrev bcsN : FeatureBundle GenderNode :=
  [⟨cls, true⟩]

/-- (68) Mismatched humans → {CLASS, INDIV, MASC, ANIM} → masculine.
    {CLASS,INDIV,MASC,ANIM,FEM} ∩ {CLASS,INDIV,MASC,ANIM}
    = {CLASS,INDIV,MASC,ANIM}. -/
theorem bcs_human_mismatch :
    resolve bcsHF bcsHM =
    some [cls, indiv, masc, anim] := by native_decide

theorem bcs_human_mismatch_vi :
    bcsVI [cls, indiv, masc, anim] = .masc := by native_decide

/-- Mismatched M + F inanimates → {CLASS, INDIV, MASC} → masculine.
    Both conjuncts share {CLASS, INDIV, MASC} as iFs;
    ANIM + FEM on the feminine noun are uFs, excluded from resolution. -/
theorem bcs_inanim_MF :
    resolve bcsIM bcsIF = some [cls, indiv, masc] := by native_decide

/-- (69) Mismatched N + F inanimates → masculine.
    *znanje* 'knowledge' (N) + *intuicija* 'intuition' (F).
    Neuter is mass (iFs = {CLASS}); feminine inanimate has iFs =
    {CLASS, INDIV, MASC}. Intersection = {CLASS}. But coordination
    introduces GRP (entailing INDIV), so the &P bears {CLASS, INDIV}
    at minimum → Subset Principle yields masculine.

    NB: The formalization models this by checking that the gender
    resolution itself yields {CLASS}, and the coordinate structure's
    INDIV (from GRP/plural) independently ensures masculine VI. -/
theorem bcs_inanim_NF_resolved :
    resolve bcsN bcsIF = some [cls] := by native_decide

/-- After coordination introduces INDIV, the combined features
    ({CLASS} from resolution + {INDIV} from GRP) map to masculine. -/
theorem bcs_inanim_NF_vi :
    bcsVI [cls, indiv] = .masc := by native_decide

theorem bcs_inanim_mismatch_vi :
    bcsVI [cls, indiv, masc] = .masc := by native_decide

/-- (70) Even matched neuters → masculine when coordinated.
    *selo* 'village' (N) + *brdo* 'hill' (N).
    Individual neuter DPs are mass (iFs = {CLASS}). Resolution:
    {CLASS} ∩ {CLASS} = {CLASS}. But coordination introduces GRP
    (entailing INDIV). The combined {CLASS, INDIV} at &P maps to
    masculine via VI — INDIV is present → masculine. -/
theorem bcs_neut_resolved :
    resolve bcsN bcsN = some [cls] := by native_decide

theorem bcs_neut_coord_masc :
    bcsVI [cls, indiv] = .masc := by native_decide

-- ============================================================================
-- § 12: Cross-Linguistic Summary (Table 2)
-- ============================================================================

/-- Table 2 verified: all six cells derived from geometry + intersection. -/
theorem table2_greek_humans :
    (resolve gkHF gkHM).map greekVI = some .masc := by native_decide

theorem table2_greek_inanimates :
    (resolve gkIM gkIF).map greekVI = some .neut := by native_decide

theorem table2_icelandic_humans :
    (resolve isHM isHF).map icelandicVI = some .neut := by native_decide

theorem table2_icelandic_inanimates :
    (resolve isIF isIM).map icelandicVI = some .neut := by native_decide

theorem table2_bcs_humans :
    (resolve bcsHF bcsHM).map bcsVI = some .masc := by native_decide

theorem table2_bcs_inanimates :
    (resolve bcsIM bcsIF).map bcsVI = some .masc := by native_decide

-- ============================================================================
-- § 13: Redundancy Rule
-- ============================================================================

/-- Redundancy rule (13): copy iF values to empty uF slots at Transfer.
    If uFs are already filled (arbitrary gender), the rule does not apply.

    Y-model: this operation occurs at **Transfer**, the boundary between
    narrow syntax and the PF/LF interfaces. -/
def redundancyRule (iFs uFs : List GenderNode) : List GenderNode :=
  if uFs.isEmpty then iFs else uFs

/-- Human feminine: uFs empty → redundancy fills from iFs. -/
theorem redundancy_human :
    redundancyRule [cls, masc, fem] [] = [cls, masc, fem] := by
  native_decide

/-- Arbitrary feminine: uFs already filled → preserved. -/
theorem redundancy_arbitrary :
    redundancyRule [cls] [cls, masc, fem] = [cls, masc, fem] := by
  native_decide

-- ============================================================================
-- § 14: ABA Syncretism Prediction
-- ============================================================================

/-! The implicational feature hierarchy (CLASS > MASC > FEM) predicts
    the absence of ABA syncretism patterns (fn. 19). Neuter and feminine
    can never be syncretic to the exclusion of masculine — since the
    masculine feature set {MASC} is a proper subset of feminine {FEM,MASC}
    and a proper superset of neuter ∅, any syncretism of N and F would
    also include M. -/

/-- Greek inflection: M is always "between" N and F in feature specificity.
    This rules out N = F ≠ M syncretism patterns. -/
theorem no_aba_syncretism :
    ¬(greekVI [] = greekVI [cls, masc, fem] ∧
      greekVI [] ≠ greekVI [cls, masc]) := by native_decide

-- ============================================================================
-- § 15: Feature Geometry Functions
-- ============================================================================

/-! ### Geometry → outcome

    The paper's central thesis: cross-linguistic variation in resolution
    follows from differences in feature geometry, not from different
    resolution mechanisms or stipulated defaults. Same labels, same
    mechanism, different geometry → different outcome.

    We formalize each language's geometry as a function from a base
    gender node to the full set of entailed iFs, then prove that
    resolution outcomes follow from geometry alone. -/

/-- Greek geometry (17): CLASS > MASC > FEM (linear chain).
    FEM entails MASC entails CLASS. -/
def greekGeometry : GenderNode → FeatureBundle GenderNode
  | .fem  => [⟨cls, true⟩, ⟨masc, true⟩, ⟨fem, true⟩]
  | .masc => [⟨cls, true⟩, ⟨masc, true⟩]
  | .cls  => [⟨cls, true⟩]
  | _     => []

/-- Icelandic geometry (63): CLASS > {MASC, FEM} (independent siblings).
    Neither FEM nor MASC entails the other. -/
def icelandicGeometry : GenderNode → FeatureBundle GenderNode
  | .fem  => [⟨cls, true⟩, ⟨fem, true⟩]
  | .masc => [⟨cls, true⟩, ⟨masc, true⟩]
  | .cls  => [⟨cls, true⟩]
  | _     => []

/-- The linear chain geometry guarantees that mismatched human
    resolution retains MASC — because both conjuncts bear iMASC
    (FEM entails MASC). -/
theorem greek_geometry_human_mismatch :
    resolve (greekGeometry .fem) (greekGeometry .masc) =
    some [cls, masc] := by native_decide

/-- The independent geometry means human mismatch loses both
    MASC and FEM — only CLASS survives intersection. -/
theorem icelandic_geometry_human_mismatch :
    resolve (icelandicGeometry .fem) (icelandicGeometry .masc) =
    some [cls] := by native_decide

/-- Geometry determines resolution outcome: same mechanism + same
    feature labels → different VI output, entirely from geometry. -/
theorem geometry_determines_resolution :
    (resolve (greekGeometry .fem) (greekGeometry .masc)).map greekVI = some .masc ∧
    (resolve (icelandicGeometry .fem) (icelandicGeometry .masc)).map icelandicVI = some .neut := by
  constructor <;> native_decide

/-- The geometry functions reconstruct the noun data: Greek nouns
    are exactly the geometry applied to their most specific iF. -/
theorem greek_geometry_faithful_fem : greekGeometry .fem = gkHF := by native_decide
theorem greek_geometry_faithful_masc : greekGeometry .masc = gkHM := by native_decide
theorem icelandic_geometry_faithful_fem : icelandicGeometry .fem = isHF := by native_decide
theorem icelandic_geometry_faithful_masc : icelandicGeometry .masc = isHM := by native_decide

/-- Entailment asymmetry: in the linear chain (Greek), FEM's iFs
    are a superset of MASC's iFs. In the independent geometry
    (Icelandic), neither is a superset of the other.
    This is WHY the intersection outcomes differ. -/
theorem greek_fem_entails_masc :
    (percolateI (greekGeometry .masc)).all
      ((percolateI (greekGeometry .fem)).contains ·) = true := by native_decide

theorem icelandic_fem_not_entails_masc :
    (percolateI (icelandicGeometry .masc)).all
      ((percolateI (icelandicGeometry .fem)).contains ·) = false := by native_decide

-- ============================================================================
-- § 16: Subset Principle — Formal Vocabulary Items
-- ============================================================================

/-! ### Vocabulary as FeatureVI items

    The ad-hoc `greekVI` function above implements the Subset Principle
    procedurally. Here we define the same vocabulary as `FeatureVI` items
    (@cite{halle-marantz-1993}) and prove that `subsetPrinciple` selects
    the same exponents. This connects the gender resolution mechanism to
    the formal DM vocabulary insertion framework. -/

open Morphology.DM.VI (FeatureVI subsetPrinciple)

/-- Greek vocabulary items as `FeatureVI` entries (schema 21).
    Most specific first: {FEM,MASC} → F, {MASC} → M, {} → N. -/
def greekVocabItems : List (FeatureVI GenderNode Infl) :=
  [ ⟨[fem, masc], .fem⟩,
    ⟨[masc], .masc⟩,
    ⟨[], .neut⟩ ]

/-- BCS vocabulary items as `FeatureVI` entries (schema 75).
    {FEM,ANIM} → F, {INDIV} → M, {} → N. -/
def bcsVocabItems : List (FeatureVI GenderNode Infl) :=
  [ ⟨[fem, anim], .fem⟩,
    ⟨[indiv], .masc⟩,
    ⟨[], .neut⟩ ]

/-- Subset Principle agrees with ad-hoc `greekVI` for human mismatch. -/
theorem sp_greek_human_mismatch :
    subsetPrinciple greekVocabItems [cls, masc] = some .masc := by native_decide

/-- Subset Principle agrees with `greekVI` for inanimate mismatch. -/
theorem sp_greek_inanim_mismatch :
    subsetPrinciple greekVocabItems [cls] = some .neut := by native_decide

/-- Subset Principle agrees with `greekVI` for uniform feminine. -/
theorem sp_greek_uniform_fem :
    subsetPrinciple greekVocabItems [cls, masc, fem] = some .fem := by native_decide

/-- Subset Principle agrees with `bcsVI` for human mismatch. -/
theorem sp_bcs_human_mismatch :
    subsetPrinciple bcsVocabItems [cls, indiv, masc, anim] = some .masc := by
  native_decide

/-- Same vocabulary + different geometry → different outcome.
    Greek and Icelandic share the vocabulary (both use `greekVocabItems`),
    but the Subset Principle yields different results because the geometry
    produces different intersections. -/
theorem sp_same_vocab_different_geometry :
    subsetPrinciple greekVocabItems [cls, masc] = some .masc ∧
    subsetPrinciple greekVocabItems [cls] = some .neut := by
  constructor <;> native_decide

-- ============================================================================
-- § 17: Feature Geometry as FeatureOrder
-- ============================================================================

/-! ### FeatureOrder instances

    The `FeatureOrder` structure packages a feature geometry — its nodes
    and the bundle function that maps each node to its full set of
    entailed features. This formalizes the paper's central insight that
    cross-linguistic variation is geometry variation. -/

/-- Greek feature order: CLASS > MASC > FEM (linear chain). -/
def greekOrder : FeatureOrder GenderNode :=
  { nodes := [cls, masc, fem]
    bundle := greekGeometry }

/-- Icelandic feature order: CLASS > {MASC, FEM} (independent siblings). -/
def icelandicOrder : FeatureOrder GenderNode :=
  { nodes := [cls, masc, fem]
    bundle := icelandicGeometry }

/-- Greek entailment: FEM entails MASC (FEM's bundle ⊇ MASC's bundle). -/
theorem greek_order_fem_entails_masc :
    greekOrder.entails fem masc = true := by native_decide

/-- Icelandic: FEM does NOT entail MASC (independent siblings). -/
theorem icelandic_order_fem_not_entails_masc :
    icelandicOrder.entails fem masc = false := by native_decide

/-- Greek: MASC entails CLASS. -/
theorem greek_order_masc_entails_cls :
    greekOrder.entails masc cls = true := by native_decide

/-- Greek: CLASS does NOT entail MASC (entailment is asymmetric). -/
theorem greek_order_cls_not_entails_masc :
    greekOrder.entails cls masc = false := by native_decide

-- ============================================================================
-- § 18: Mismatch Resolution Hypothesis — Geometry Property
-- ============================================================================

/-! ### MRH as a property of geometries

    @cite{adamson-anagnostopoulou-2025}'s Mismatch Resolution Hypothesis:
    Greek satisfies MRH because ALL pairwise resolution outcomes produce
    non-empty intersections — no default insertion is ever needed.

    We verify this via the `satisfiesMRH` predicate from
    `GenderResolution`, instantiated with the geometry-derived bundles. -/

/-- Greek satisfies MRH: all pairwise resolutions succeed. -/
theorem greek_satisfies_mrh :
    greekOrder.satisfiesMRH' = true := by native_decide

/-- Icelandic satisfies MRH: all pairwise resolutions succeed.
    Despite different outcomes (neuter for humans instead of masculine),
    no resolution yields an empty intersection. -/
theorem icelandic_satisfies_mrh :
    icelandicOrder.satisfiesMRH' = true := by native_decide

/-- Both satisfy MRH — this is the paper's "no default insertion"
    claim: the difference between Greek and Icelandic is the
    *content* of the intersection, not whether it exists. -/
theorem both_satisfy_mrh :
    greekOrder.satisfiesMRH' = true ∧ icelandicOrder.satisfiesMRH' = true := by
  constructor <;> native_decide

-- ============================================================================
-- § 19: N-ary Coordination
-- ============================================================================

/-! ### Three or more conjuncts

    `resolveN` extends binary resolution to n-ary coordination via
    iterated intersection. The predictions are the same: gender-matching
    agreement emerges iff all conjuncts share a feature (after percolation). -/

/-- Greek: three human feminines → {CLASS,MASC,FEM}. -/
theorem gk_ternary_uniform_fem :
    resolveN [gkHF, gkHF, gkHF] = some [cls, masc, fem] := by native_decide

/-- Greek: three mismatched humans → {CLASS,MASC} (FEM eliminated).
    FEM + MASC + FEM: FEM present in first and third but not second. -/
theorem gk_ternary_human_mismatch :
    resolveN [gkHF, gkHM, gkHF] = some [cls, masc] := by native_decide

/-- Greek: three inanimates → {CLASS} → neuter. -/
theorem gk_ternary_inanim :
    resolveN [gkIF, gkIM, gkIN] = some [cls] := by native_decide

/-- Icelandic: three mismatched humans → {CLASS} → neuter.
    Because MASC and FEM are independent, any mismatch loses both. -/
theorem is_ternary_human_mismatch :
    resolveN [isHF, isHM, isHF] = some [cls] := by native_decide

/-- BCS: three mismatched humans → {CLASS,INDIV,MASC,ANIM} → masculine.
    INDIV guarantees masculine even with mismatched FEM. -/
theorem bcs_ternary_human_mismatch :
    resolveN [bcsHF, bcsHM, bcsHF]
    = some [cls, indiv, masc, anim] := by native_decide

/-- N-ary subsumes binary: resolveN [fs1, fs2] = resolve fs1 fs2. -/
theorem nary_subsumes_binary_greek :
    resolveN [gkHF, gkHM] = resolve gkHF gkHM := by
  exact resolveN_binary gkHF gkHM

end Phenomena.Agreement.Studies.AdamsonAnagnostopoulou2025
