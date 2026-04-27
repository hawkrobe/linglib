import Linglib.Theories.Syntax.Case.Dependent
import Linglib.Theories.Syntax.Minimalist.Voice
import Linglib.Fragments.Georgian.Agreement

/-!
# @cite{marantz-1991} — Case and Licensing
@cite{marantz-1991}

Two central claims:

1. **Abstract Case ≠ morphological case.** NPs are licensed by projection
   and the EPP, not by Case theory. Morphological case is post-syntactic,
   inserted at Morphological Structure.

2. **Burzio's generalization decomposes** into the EPP (sentences need
   subjects) and the **Ergative generalization** (no ERG/ACC on
   non-thematic/derived subjects). The latter concerns morphological
   case realization, not abstract licensing.

## Case Realization Hierarchy

Morphological case obeys a disjunctive hierarchy:

    lexically governed > dependent (ACC/ERG) > unmarked > default

This is formalized in `DependentCase.lean` as `CaseSource`
(lexical > dependent > unmarked). @cite{marantz-1991}'s fourth level,
**default** case (absolute last resort when no other principle applies),
is not modeled separately; it is conceptually distinct from unmarked
(which is environment-sensitive — e.g., GEN inside NPs, NOM inside IPs)
but our current grammar never needs to distinguish them.
@cite{baker-2015} later developed the hierarchy into a full
cross-linguistic algorithm.

## Dependent Case

ACC and ERG are **dependent cases** — assigned relationally:
- ACC: dependent case assigned to the lower of two caseless NPs
- ERG: dependent case assigned to the higher of two caseless NPs
- The two NPs must be *distinct* (not in the same chain); this is
  implicit in our list representation where each `NPInDomain` is a
  distinct structural position.

## Georgian Split Ergativity

Present series INFL selects accusative alignment → surface NOM-DAT pattern
(where DAT is the spell-out of abstract dependent ACC).
Aorist series INFL selects ergative alignment → surface ERG-NOM pattern
(where NOM is the spell-out of abstract unmarked ABS).
Crucially, agreement direction is independent of case direction —
the split in case morphology across tense series does NOT correlate
with any split in agreement (which always targets the same positions).

**Evidential series** (DAT-NOM "inversion") is not derived from the
dependent case algorithm; it reflects a morphological property of
evidential INFL. The algorithm covers present and aorist only.

## Abstract Case vs Morphological Case

The dependent case algorithm produces *abstract* case values (`Core.Case`).
These map to *morphological* surface forms (also `Core.Case`) via
language-specific spell-out at Morphological Structure. In Georgian:
abstract ACC → morphological DAT (dative and accusative case have fallen
together), abstract ABS → morphological NOM (unmarked surface form).

## Case Hierarchy ↔ Agreement Hierarchy

The case realization hierarchy (lexical > dependent > unmarked) parallels
the Moravcsik agreement accessibility hierarchy (formalized below as
`Minimalist.CaseAccessibility` from @cite{preminger-2014}). Both rank
case types identically; the former determines case *assignment* priority,
the latter determines agreement *visibility*. The bridge
`sourceToAccessibility` connects the two.

## Case-Discrimination Apparatus (relocated from `Minimalism/CaseDiscrimination.lean`)

The Moravcsik-hierarchy primitives below come from @cite{preminger-2014}
(with @cite{bobaljik-2008}, @cite{scott-2023}). They are paper-specific
to the case-discrimination tradition that this study is in conversation
with, and are not consumed elsewhere in the library, so they live here
under `namespace Minimalist` for symmetry with other Minimalist apparatus.
-/

namespace Minimalist

/-- Case accessibility for agreement.

    The hierarchy determines which DPs are visible to agreement probes.
    Higher accessibility = more likely to be targeted by a probe. -/
inductive CaseAccessibility where
  /-- Unmarked case: NOM (nom-acc) or ABS (erg-abs). Highest. -/
  | unmarked
  /-- Dependent case: ACC (nom-acc) or ERG (erg-abs). Middle. -/
  | dependent
  /-- Lexical/oblique case: DAT, GEN, PP, etc. Lowest. -/
  | lexical
  deriving DecidableEq, Repr

/-- Numeric rank for ordering. Higher = more accessible. -/
def CaseAccessibility.rank : CaseAccessibility → Nat
  | .unmarked => 2
  | .dependent => 1
  | .lexical => 0

/-- Is a DP with this case level accessible to a probe with the
    given threshold? Contiguity: a DP is accessible iff its level
    is at or above the threshold. -/
def caseAccessible (dpLevel threshold : CaseAccessibility) : Bool :=
  dpLevel.rank ≥ threshold.rank

/-- A case alignment maps argument positions (S, A, P) to case
    accessibility levels.

    - S: intransitive subject (sole argument)
    - A: transitive agent (external argument)
    - P: transitive patient (internal argument) -/
structure CaseAlignment where
  /-- Case accessibility of the intransitive subject. -/
  sLevel : CaseAccessibility
  /-- Case accessibility of the transitive agent. -/
  aLevel : CaseAccessibility
  /-- Case accessibility of the transitive patient. -/
  pLevel : CaseAccessibility
  deriving Repr

/-- Nominative-accusative alignment: S and A both get unmarked (NOM),
    P gets dependent (ACC). -/
def nomAcc : CaseAlignment :=
  ⟨.unmarked, .unmarked, .dependent⟩

/-- Ergative-absolutive alignment: S and P both get unmarked (ABS),
    A gets dependent (ERG). -/
def ergAbs : CaseAlignment :=
  ⟨.unmarked, .dependent, .unmarked⟩

/-- Tripartite alignment: S gets unmarked (ABS), A gets dependent
    (ERG), P gets dependent (ACC). Mam. -/
def tripartite : CaseAlignment :=
  ⟨.unmarked, .dependent, .dependent⟩

/-- Agreement pattern: which argument positions trigger agreement. -/
structure AgreementPattern where
  sAgrees : Bool   -- intransitive subject
  aAgrees : Bool   -- transitive agent
  pAgrees : Bool   -- transitive patient
  deriving DecidableEq, Repr

/-- Given a case alignment and an accessibility threshold, compute
    which argument positions are visible to the probe. -/
def agreementFromThreshold (ca : CaseAlignment) (threshold : CaseAccessibility) :
    AgreementPattern :=
  { sAgrees := caseAccessible ca.sLevel threshold
  , aAgrees := caseAccessible ca.aLevel threshold
  , pAgrees := caseAccessible ca.pLevel threshold }

/-- Is this agreement pattern ergative-absolutive?
    S and P agree, A does not (S=P≠A). -/
def AgreementPattern.isErgAbs (ap : AgreementPattern) : Bool :=
  ap.sAgrees && ap.pAgrees && !ap.aAgrees

/-- Is this agreement pattern nominative-accusative?
    S and A agree, P does not (S=A≠P). -/
def AgreementPattern.isNomAcc (ap : AgreementPattern) : Bool :=
  ap.sAgrees && ap.aAgrees && !ap.pAgrees

/-- The three possible thresholds. -/
def thresholds : List CaseAccessibility :=
  [.unmarked, .dependent, .lexical]

/-- With NOM-ACC case, A always agrees whenever S agrees (both have
    unmarked = NOM). Therefore, the pattern S=P≠A (ergative-absolutive
    agreement) is impossible: you cannot target S without also targeting A.

    This is @cite{bobaljik-2008}'s typological gap: NOM-ACC case + ERG-ABS
    agreement is unattested. -/
theorem nomAcc_a_equals_s (threshold : CaseAccessibility) :
    (agreementFromThreshold nomAcc threshold).aAgrees =
    (agreementFromThreshold nomAcc threshold).sAgrees := by
  cases threshold <;> rfl

/-- Corollary: ERG-ABS agreement is impossible with NOM-ACC case.
    No threshold produces S=P≠A under NOM-ACC alignment. -/
theorem nomAcc_no_ergAbs_agreement (threshold : CaseAccessibility) :
    (agreementFromThreshold nomAcc threshold).isErgAbs = false := by
  cases threshold <;> rfl

/-- With ERG-ABS case, threshold = unmarked yields ABS agreement:
    S and P agree (both have ABS = unmarked), A does not (ERG =
    dependent, below threshold). This is ergative-absolutive agreement. -/
theorem ergAbs_unmarked_yields_abs_agreement :
    (agreementFromThreshold ergAbs .unmarked).isErgAbs = true := rfl

/-- With ERG-ABS case, threshold = dependent yields agreement with
    ALL arguments (S, A, P all accessible). -/
theorem ergAbs_dependent_yields_all :
    let ap := agreementFromThreshold ergAbs .dependent
    ap.sAgrees = true ∧ ap.aAgrees = true ∧ ap.pAgrees = true :=
  ⟨rfl, rfl, rfl⟩

/-- Contiguity: if a DP with dependent case is accessible, then any
    DP with unmarked case is also accessible (unmarked > dependent). -/
theorem contiguity_unmarked_dependent (threshold : CaseAccessibility) :
    caseAccessible .dependent threshold = true →
    caseAccessible .unmarked threshold = true := by
  cases threshold <;> simp [caseAccessible, CaseAccessibility.rank]

/-- Contiguity: if a DP with lexical case is accessible, then DPs
    with dependent and unmarked case are also accessible. -/
theorem contiguity_lexical (threshold : CaseAccessibility) :
    caseAccessible .lexical threshold = true →
    caseAccessible .dependent threshold = true ∧
    caseAccessible .unmarked threshold = true := by
  cases threshold <;> simp [caseAccessible, CaseAccessibility.rank]

/-- Dative intervention: a dative DP blocks the probe's search.

    Components:
    - `dativePresent`: a dative DP intervenes between probe and goal
    - `threshold`: the probe's case accessibility threshold
    - `targetLevel`: the case level of the intended goal -/
structure DativeInterventionContext where
  /-- A dative (lexical case) DP intervenes. -/
  dativePresent : Bool
  /-- The probe's case accessibility threshold. -/
  threshold : CaseAccessibility
  /-- Case level of the intended agreement target. -/
  targetLevel : CaseAccessibility
  deriving Repr

/-- Is the dative visible to the probe? Only if the threshold is
    low enough to include lexical case. -/
def dativeVisibleToProbe (threshold : CaseAccessibility) : Bool :=
  caseAccessible .lexical threshold

/-- Does dative intervention cause agreement failure?

    The dative intervenes (blocks the probe by locality/minimality)
    if it has matching phi-features. But it cannot be a valid goal
    because its case (lexical) is below the threshold. The probe
    fails without crashing.

    This is modeled as: if a dative is present AND the dative's
    case is below the threshold (so the probe can't Agree with it)
    AND the dative blocks access to the real target by minimality,
    then agreement fails. -/
def dativeIntervenes (ctx : DativeInterventionContext) : Bool :=
  ctx.dativePresent &&
  !dativeVisibleToProbe ctx.threshold  -- dative below threshold

/-- With a standard threshold (unmarked or dependent), a dative
    DP causes intervention: it blocks the probe but cannot be
    agreed with. -/
theorem dative_blocks_at_unmarked :
    dativeIntervenes ⟨true, .unmarked, .unmarked⟩ = true := rfl

theorem dative_blocks_at_dependent :
    dativeIntervenes ⟨true, .dependent, .unmarked⟩ = true := rfl

/-- If the threshold includes lexical case, the dative does NOT
    intervene — it becomes a valid agreement target. -/
theorem dative_no_intervention_at_lexical :
    dativeIntervenes ⟨true, .lexical, .unmarked⟩ = false := rfl

/-- Kaqchikel has ergative-absolutive alignment: S and P get ABS
    (unmarked), A gets ERG (dependent). -/
def kaqCaseAlignment : CaseAlignment := ergAbs

/-- Under Kaqchikel's alignment with threshold = unmarked, agreement
    targets S and P (Set B / absolutive agreement) but not A. This is
    consistent with the Set B (ABS) paradigm. -/
theorem kaq_abs_agreement :
    (agreementFromThreshold kaqCaseAlignment .unmarked).sAgrees = true ∧
    (agreementFromThreshold kaqCaseAlignment .unmarked).pAgrees = true ∧
    (agreementFromThreshold kaqCaseAlignment .unmarked).aAgrees = false :=
  ⟨rfl, rfl, rfl⟩

/-- Kaqchikel Set A agreement targets A (ERG): this requires a
    separate probe (Voice/v) with threshold = dependent, which
    sees both unmarked and dependent case DPs. -/
theorem kaq_erg_agreement_threshold :
    (agreementFromThreshold kaqCaseAlignment .dependent).aAgrees = true := rfl

end Minimalist

namespace Marantz1991

open Minimalist
open Syntax.Case
open Fragments.Georgian.Agreement

-- ============================================================================
-- § 1: Bridge from SplitErgativity to Dependent Case
-- ============================================================================

/-- Map alignment family to dependent case language type.
    Bridges the typological description (`Core.SplitErgativity`) to
    the case algorithm (`DependentCase`). -/
def alignmentToLangType : Core.AlignmentFamily → CaseLanguageType
  | .accusative => .accusative
  | .ergative   => .ergative

/-- Georgian language type for a given tense series. -/
def georgianLangType (ts : TenseSeries) : CaseLanguageType :=
  alignmentToLangType (georgianSplit.alignment ts)

theorem present_is_accusative : georgianLangType .present = .accusative := rfl
theorem aorist_is_ergative : georgianLangType .aorist = .ergative := rfl

-- ============================================================================
-- § 2: NP Configurations by Verb Class
-- ============================================================================

/-- NP configuration for each Georgian verb class (present/aorist).

    - Class 1 (transitive): 2 NPs (subject + object), both structural
    - Class 2 (unaccusative): 1 NP (sole argument, raised to Spec-TP)
    - Class 3 (unergative): 2 *positions* — subject + empty object.
      @cite{marantz-1991}: Georgian counts an unfilled object position as
      a distinct position for dependent case, explaining why unergatives
      get ERG despite being intransitive.
    - Class 4 (psych): 2 NPs — DAT subject (lexical/quirky) + NOM object -/
def georgianNPs : VerbClass → List NPInDomain
  | .class1 => [⟨"subj", none⟩, ⟨"obj", none⟩]
  | .class2 => [⟨"subj", none⟩]
  | .class3 => [⟨"subj", none⟩, ⟨"empty", none⟩]  -- phantom object position
  | .class4 => [⟨"subj", some .dat⟩, ⟨"obj", none⟩]  -- quirky DAT

-- ============================================================================
-- § 3: Georgian Case Derivation
-- ============================================================================

/-- Run the dependent case algorithm for a Georgian verb class in a
    given tense series. -/
def georgianCaseResult (vc : VerbClass) (ts : TenseSeries) : List CasedNP :=
  assignCases (georgianLangType ts) (georgianNPs vc)

private def getCase! (label : String) (results : List CasedNP) : Core.Case :=
  match getCaseOf label results with
  | some c => c
  | none   => .dat  -- placeholder; the algorithm always returns every NP

-- ============================================================================
-- § 4: Abstract Case → Morphological Case (Georgian Spell-Out)
-- ============================================================================

/-- Georgian-specific mapping from abstract case (algorithm output) to
    surface morphological case. This is the language-specific spell-out
    at Morphological Structure — the locus of @cite{marantz-1991}'s
    abstract/morphological case distinction.

    - Abstract ACC → morphological DAT (dative and accusative
      morphological case have fallen together in Georgian into what
      is called "the dative case" — @cite{marantz-1991} p. 12)
    - Abstract ABS → morphological NOM (unmarked surface form)
    - Abstract ERG → morphological ERG -/
def georgianSpellout : Core.Case → Core.Case
  | .nom => .nom
  | .acc => .dat   -- Georgian objects surface with the dative suffix
  | .erg => .erg
  | .abs => .nom   -- ABS surfaces as NOM
  | c    => c

theorem acc_surfaces_as_dat : georgianSpellout .acc = .dat := rfl
theorem abs_surfaces_as_nom : georgianSpellout .abs = .nom := rfl

-- ============================================================================
-- § 5: Bridge to Georgian Agreement Fragment
-- ============================================================================

/-! The dependent case algorithm + Georgian spell-out produces exactly
    the surface case frames recorded in `Fragments.Georgian.Agreement`.
    This is the core empirical validation: the algorithm derives all
    8 verb-class × tense combinations for subjects. -/

/-- All subject cases derived from the algorithm match the fragment data. -/
theorem subject_derivation_matches_fragment :
    [VerbClass.class1, .class2, .class3, .class4].all (λ vc =>
      [TenseSeries.present, .aorist].all (λ ts =>
        georgianSpellout (getCase! "subj" (georgianCaseResult vc ts)) ==
        verbClassSubjectCase vc ts)) = true := by native_decide

/-- Object cases for transitive classes also match. -/
theorem object_derivation_matches :
    georgianSpellout (getCase! "obj" (georgianCaseResult .class1 .present)) = .dat ∧
    georgianSpellout (getCase! "obj" (georgianCaseResult .class1 .aorist)) = .nom ∧
    georgianSpellout (getCase! "obj" (georgianCaseResult .class4 .present)) = .nom ∧
    georgianSpellout (getCase! "obj" (georgianCaseResult .class4 .aorist)) = .nom := by
  native_decide

-- ============================================================================
-- § 6: The Ergative Generalization
-- ============================================================================

/-! @cite{marantz-1991}'s Ergative generalization: ergative case may appear
    on the subject of an intransitive clause, but not on a derived subject.

    Under dependent case, this follows from the NP count: ERG requires
    a lower caseless NP as competitor. A derived (raised) unaccusative
    subject has no such competitor — the sole NP gets unmarked case.
    An unergative subject, by contrast, c-commands an (empty) object
    position that Georgian counts as a competitor. -/

/-- Class 1 aorist: transitive subject gets ERG. -/
theorem class1_aorist_erg :
    georgianSpellout (getCase! "subj" (georgianCaseResult .class1 .aorist)) = .erg := by
  native_decide

/-- Class 2 aorist: unaccusative subject does NOT get ERG. -/
theorem class2_aorist_no_erg :
    georgianSpellout (getCase! "subj" (georgianCaseResult .class2 .aorist)) = .nom := by
  native_decide

/-- Class 3 aorist: unergative subject DOES get ERG
    (empty object position serves as competitor). -/
theorem class3_aorist_erg :
    georgianSpellout (getCase! "subj" (georgianCaseResult .class3 .aorist)) = .erg := by
  native_decide

/-- Class 4: quirky DAT takes priority (lexical > dependent). -/
theorem class4_lexical_dat :
    getCase! "subj" (georgianCaseResult .class4 .aorist) = .dat ∧
    getSourceOf "subj" (georgianCaseResult .class4 .aorist) = some .lexical := by
  native_decide

/-- The Ergative generalization follows from NP count:
    1 NP (unaccusative) → no ERG; ≥2 positions → ERG possible. -/
theorem ergative_requires_competitor :
    getSourceOf "sole" (assignCases .ergative [⟨"sole", none⟩]) = some .unmarked ∧
    getSourceOf "higher" (assignCases .ergative [⟨"higher", none⟩, ⟨"lower", none⟩]) =
      some .dependent := by
  native_decide

-- ============================================================================
-- § 7: Burzio's Generalization Decomposed
-- ============================================================================

/-! @cite{marantz-1991}'s key insight: Burzio's generalization
    ("non-thematic subject → no accusative object") splits into:

    1. **EPP**: sentences require subjects (projection + EPP suffice)
    2. **Dependent case**: ACC requires a *distinct* higher caseless NP
       as competitor

    When Voice is non-thematic (unaccusative), no external argument is
    introduced. The sole internal argument raises to Spec-TP. Only one
    NP exists in the domain → no case competitor → no dependent ACC.

    Marantz's counterexamples — adversity passives and "strike" verbs —
    have non-thematic subjects AND accusative objects. Under dependent
    case, this is predicted: the subject and object occupy *distinct*
    structural positions, so the ACC condition IS met. -/

/-- Unaccusative: sole NP, no ACC. The "Burzio effect." -/
theorem burzio_unaccusative_no_acc :
    getCaseOf "theme" (assignCases .accusative [⟨"theme", none⟩]) = some .nom ∧
    getSourceOf "theme" (assignCases .accusative [⟨"theme", none⟩]) = some .unmarked := by
  native_decide

/-- Transitive: external argument provides the case competitor → ACC. -/
theorem burzio_transitive_has_acc :
    getCaseOf "theme" (assignCases .accusative [⟨"agent", none⟩, ⟨"theme", none⟩]) =
      some .acc := by
  native_decide

/-- Marantz's counterexample: non-thematic subject with ACC object.
    Two NPs in distinct chains → dependent case applies despite
    non-thematic subject. Refutes Burzio's abstract-Case version. -/
theorem nonthematic_subject_with_acc :
    getCaseOf "obj" (assignCases .accusative [⟨"derived_subj", none⟩, ⟨"obj", none⟩]) =
      some .acc := by
  native_decide

/-- Voice determines NP count: θ-assigning Voice adds an external argument.
    This bridges Voice theory to the configural case algorithm. -/
def npCount (voice : VoiceHead) (internalArgs : Nat) : Nat :=
  if voice.assignsTheta then 1 + internalArgs else internalArgs

theorem agentive_two_nps : npCount voiceAgent 1 = 2 := rfl
theorem anticausative_one_np : npCount voiceAnticausative 1 = 1 := rfl

-- ============================================================================
-- § 8: Hindi Split Ergativity
-- ============================================================================

/-! Hindi has aspect-conditioned split ergativity: perfective triggers
    ERG on the transitive agent (*-ne*), imperfective has NOM-ACC.
    The dependent case algorithm derives both patterns from the same
    mechanism with different `CaseLanguageType` settings.

    @cite{marantz-1991}: Hindi ERG is prohibited on unaccusative subjects
    (*siitta (\*ne) aayii* 'Sita arrived'), optional on unergatives, and
    obligatory on transitives. The unaccusative prohibition follows from
    dependent case: a sole argument has no competitor. -/

def hindiTransitive (aspect : Core.Aspect) : List CasedNP :=
  assignCases (alignmentToLangType (Core.hindiSplit.alignment aspect))
    [⟨"agent", none⟩, ⟨"theme", none⟩]

theorem hindi_perfective_erg :
    getCaseOf "agent" (hindiTransitive .perfective) = some .erg ∧
    getCaseOf "theme" (hindiTransitive .perfective) = some .abs := by
  native_decide

theorem hindi_imperfective_nom_acc :
    getCaseOf "agent" (hindiTransitive .imperfective) = some .nom ∧
    getCaseOf "theme" (hindiTransitive .imperfective) = some .acc := by
  native_decide

/-- The split is derived from the same algorithm, not stipulated. -/
theorem hindi_split_is_algorithmic :
    hindiTransitive .perfective ≠ hindiTransitive .imperfective := by
  native_decide

/-- Hindi perfective unaccusative: sole NP, no ERG.
    Derives *siitta (\*ne) aayii* — ERG is prohibited on unaccusatives
    because there is no caseless competitor for dependent case. -/
theorem hindi_perfective_unaccusative_no_erg :
    let result := assignCases (alignmentToLangType (Core.hindiSplit.alignment .perfective))
      [⟨"theme", none⟩]
    getCaseOf "theme" result = some .abs ∧
    getSourceOf "theme" result = some .unmarked := by
  native_decide

/-- Hindi unergative in the perfective: the unfilled object position
    may or may not count as a competitor, yielding optional ERG.
    With a phantom position (Georgian-style), ERG appears. -/
theorem hindi_perfective_unergative_with_phantom :
    let result := assignCases (alignmentToLangType (Core.hindiSplit.alignment .perfective))
      [⟨"subj", none⟩, ⟨"empty", none⟩]
    getCaseOf "subj" result = some .erg := by
  native_decide

/-- Without a phantom position, the unergative subject gets unmarked ABS
    (= no ERG). This models the optionality as a parameter: does the
    language count unfilled positions for dependent case? -/
theorem hindi_perfective_unergative_without_phantom :
    let result := assignCases (alignmentToLangType (Core.hindiSplit.alignment .perfective))
      [⟨"subj", none⟩]
    getCaseOf "subj" result = some .abs ∧
    getSourceOf "subj" result = some .unmarked := by
  native_decide

/-- Cross-linguistic contrast: Georgian obligatorily counts unfilled
    positions (Class 3 always gets ERG), while Hindi optionally does
    (unergative ERG is optional). Both patterns are derived from the
    same algorithm — the only parameter is whether a phantom NP is
    included in the domain. -/
theorem phantom_np_parameter :
    -- Georgian: Class 3 aorist with phantom → ERG
    georgianSpellout (getCase! "subj" (georgianCaseResult .class3 .aorist)) = .erg ∧
    -- Hindi: unergative perfective without phantom → no ERG (ABS)
    getCaseOf "subj" (assignCases .ergative [⟨"subj", none⟩]) = some .abs := by
  native_decide

-- ============================================================================
-- § 9: All Three Levels of the Hierarchy in One Language
-- ============================================================================

/-! Georgian demonstrates all three levels of @cite{marantz-1991}'s
    case realization hierarchy within a single language:

    | Level     | `CaseSource` | Georgian example |
    |-----------|-------------|------------------|
    | Lexical   | `.lexical`  | Class 4 DAT (quirky) |
    | Dependent | `.dependent`| Class 1 aorist ERG, present ACC |
    | Unmarked  | `.unmarked` | Class 2 NOM, Class 1 present NOM | -/

theorem all_three_sources_attested :
    getSourceOf "subj" (georgianCaseResult .class4 .present) = some .lexical ∧
    getSourceOf "subj" (georgianCaseResult .class1 .aorist) = some .dependent ∧
    getSourceOf "subj" (georgianCaseResult .class2 .aorist) = some .unmarked := by
  native_decide

/-- Lexical case bleeds dependent case: Class 4's DAT subject prevents
    ACC on the object (no caseless competitor above it). -/
theorem lexical_bleeds_dependent_georgian :
    getSourceOf "obj" (georgianCaseResult .class4 .present) = some .unmarked ∧
    getSourceOf "obj" (georgianCaseResult .class1 .present) = some .dependent := by
  native_decide

-- ============================================================================
-- § 10: Case Hierarchy ↔ Agreement Hierarchy Bridge
-- ============================================================================

/-! @cite{marantz-1991}'s case realization hierarchy (lexical > dependent >
    unmarked) parallels the Moravcsik agreement accessibility hierarchy
    (@cite{preminger-2014}, formalized in `CaseDiscrimination.lean`). Both
    rank case types identically — the same hierarchy governs which case
    "wins" in realization and which DPs are visible to agreement probes.

    The bridge `sourceToAccessibility` connects the two domains. -/

/-- Map case assignment source to agreement accessibility level.
    The hierarchies are isomorphic: lexical→lexical, dependent→dependent,
    unmarked→unmarked. Agree-based case (@cite{baker-vinokurova-2010})
    behaves like unmarked for accessibility — once T values NOM, the NP
    is fully visible to higher probes, just like an unmarked-NOM NP. -/
def sourceToAccessibility : CaseSource → CaseAccessibility
  | .lexical   => CaseAccessibility.lexical
  | .dependent => CaseAccessibility.dependent
  | .unmarked  => CaseAccessibility.unmarked
  | .agree     => CaseAccessibility.unmarked

/-- The mapping preserves the rank ordering. -/
theorem accessibility_preserves_rank (s : CaseSource) :
    (sourceToAccessibility s).rank = match s with
      | .lexical => 0 | .dependent => 1 | .unmarked => 2 | .agree => 2 := by
  cases s <;> rfl

/-- Georgian Class 4's quirky DAT subject has lexical case, which maps to
    the lowest agreement accessibility. This connects the case algorithm's
    output to the agreement hierarchy: lexical case DPs are the hardest
    for agreement probes to target. -/
theorem class4_lexical_low_accessibility :
    sourceToAccessibility CaseSource.lexical = CaseAccessibility.lexical ∧
    caseAccessible CaseAccessibility.lexical CaseAccessibility.dependent = false := ⟨rfl, rfl⟩

/-- Class 1 aorist subject has dependent case (ERG), which maps to
    middle accessibility. A probe with threshold = unmarked cannot
    see ERG-marked DPs. -/
theorem class1_aorist_dependent_accessibility :
    sourceToAccessibility CaseSource.dependent = CaseAccessibility.dependent ∧
    caseAccessible CaseAccessibility.dependent CaseAccessibility.unmarked = false := ⟨rfl, rfl⟩

/-- Class 2 aorist subject has unmarked case (NOM), which maps to
    highest accessibility. Unmarked-case DPs are always visible. -/
theorem class2_unmarked_highest_accessibility :
    sourceToAccessibility CaseSource.unmarked = CaseAccessibility.unmarked ∧
    caseAccessible CaseAccessibility.unmarked CaseAccessibility.unmarked = true := ⟨rfl, rfl⟩

-- ============================================================================
-- § 11: Voice → NP Count → Case (End-to-End)
-- ============================================================================

/-! The full argumentation chain from Voice to surface case:

    Voice (θ-assigning?) → NP count → dependent case algorithm → spell-out

    Agentive Voice introduces an external argument (1 internal + 1 external
    = 2 NPs), enabling dependent case. Non-thematic Voice introduces no
    external argument (1 internal only), so no case competitor exists and
    the sole NP gets unmarked case.

    This is @cite{marantz-1991}'s decomposition of Burzio made explicit:
    the "Burzio effect" (no ACC without a thematic subject) follows from
    Voice's argument structure, not from Case theory. -/

/-- Build NP list from Voice: if Voice assigns θ, include both subject
    and object; otherwise include only the theme. -/
def npsFromVoice (voice : VoiceHead) : List NPInDomain :=
  if voice.assignsTheta then [⟨"subj", none⟩, ⟨"obj", none⟩]
  else [⟨"theme", none⟩]

/-- End-to-end: agentive Voice → 2 NPs → object gets dependent ACC. -/
theorem voice_to_case_transitive :
    getCaseOf "obj" (assignCases .accusative (npsFromVoice voiceAgent)) = some .acc ∧
    getSourceOf "obj" (assignCases .accusative (npsFromVoice voiceAgent)) = some .dependent := by
  native_decide

/-- End-to-end: anticausative Voice → 1 NP → theme gets unmarked NOM. -/
theorem voice_to_case_unaccusative :
    getCaseOf "theme" (assignCases .accusative (npsFromVoice voiceAnticausative)) = some .nom ∧
    getSourceOf "theme" (assignCases .accusative (npsFromVoice voiceAnticausative)) = some .unmarked := by
  native_decide

/-- The Burzio effect derived end-to-end: ACC presence tracks Voice's
    θ-assignment. This is the full chain: Voice → NP count → case. -/
theorem burzio_from_voice :
    -- Agentive Voice: ACC on object
    getCaseOf "obj" (assignCases .accusative (npsFromVoice voiceAgent)) = some .acc ∧
    -- Non-thematic Voice: no ACC (sole NP gets NOM)
    getCaseOf "theme" (assignCases .accusative (npsFromVoice voiceAnticausative)) = some .nom := by
  native_decide

-- ============================================================================
-- § 12: Agreement–Case Independence (§7 Core Insight)
-- ============================================================================

/-! @cite{marantz-1991}'s central insight about Georgian split ergativity:
    case direction changes by tense series, but agreement does NOT.

    Case: present = accusative (ACC downward), aorist = ergative (ERG upward).
    Agreement: `pIsIndexed` (object agreement conditioned by person) is the
    SAME function regardless of tense series. There is no correlation between
    the "directional" features of INFL for case and the "directional" features
    of Agr for agreement.

    "Split ergativity of the Georgian sort simply exploits this lack of
    correlation." This connects to the agreement data formalized in
    `Fragments.Georgian.Agreement` and verified in
    `Aissen2003` and
    `BejarRezac2009`. -/

/-- Case direction changes between present and aorist. -/
theorem case_direction_changes :
    georgianLangType .present ≠ georgianLangType .aorist := by native_decide

/-- Agreement conditioning does NOT change between present and aorist.
    `pIsIndexed` — the function determining which objects trigger agreement
    prefixes — is defined once for all tense series, not parameterized by
    tense. This is the formal content of agreement-case independence. -/
theorem agreement_invariant_across_series :
    -- The SAME pIsIndexed function applies in both series:
    -- SAP objects are indexed regardless of case direction
    pIsIndexed .p1sg = true ∧ pIsIndexed .p2sg = true ∧
    pIsIndexed .p3sg = false ∧
    -- And case direction differs:
    georgianLangType .present = .accusative ∧
    georgianLangType .aorist = .ergative := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Subject agreement is non-differential regardless of tense series. -/
theorem subject_agreement_invariant :
    allPersonNumbers.all subjectIsIndexed = true := by native_decide

/-- The split is in case only, not in agreement.
    Case patterns differ across tense series (all 4 verb classes checked),
    but the agreement function `pIsIndexed` is a single, tense-independent
    definition — there is no `pIsIndexedForSeries`. -/
theorem case_splits_but_agreement_does_not :
    -- Case patterns differ: at least one class shows different subject case
    verbClassSubjectCase .class1 .present ≠ verbClassSubjectCase .class1 .aorist ∧
    -- All 6 person-number values give the same pIsIndexed result
    -- regardless of which series we're in (it's not parameterized)
    allPersonNumbers.all (λ pn => pIsIndexed pn == pn.isSAP) = true := by
  constructor
  · decide
  · native_decide

end Marantz1991
