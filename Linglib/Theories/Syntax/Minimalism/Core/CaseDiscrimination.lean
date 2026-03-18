/-!
# Case Discrimination in Agreement @cite{preminger-2014}
@cite{bobaljik-2008} @cite{scott-2023}

@cite{preminger-2014} formalizes the **Moravcsik hierarchy**: agreement is case-discriminating —
probes are sensitive to the case of their potential targets.

## The Moravcsik Hierarchy

Case accessibility for agreement is ordered:

    unmarked > dependent > lexical/oblique

Where:
- **Unmarked**: NOM (in nom-acc systems) or ABS (in erg-abs systems)
- **Dependent**: ACC (in nom-acc) or ERG (in erg-abs)
- **Lexical**: DAT, GEN, PP-governed, etc.

Agreement targets DPs at or above a threshold in this hierarchy. The
threshold is a contiguous prefix: {unmarked}, {unmarked, dependent},
or {all}. Crucially, a probe CANNOT target dependent-case DPs without
also targeting unmarked-case DPs.

## The Typological Gap

The hierarchy predicts an asymmetry:
- NOM-ACC case + NOM-ACC agreement: ✓ (English, French)
- ERG-ABS case + ERG-ABS agreement: ✓ (Basque, Georgian)
- ERG-ABS case + NOM-ACC agreement: ✓ (Hindi split-ERG)
- **NOM-ACC case + ERG-ABS agreement: ✗ (UNATTESTED)**

The gap follows from contiguity: in a NOM-ACC system, A and S both
receive NOM (unmarked). Any probe that sees P (ACC = dependent) also
sees A (NOM = unmarked ≥ dependent). So you cannot target S and P
(= ABS-like) without also targeting A — ruling out ERG-ABS agreement.

## Dative Intervention as Failed Agreement (§8.4)

When a dative DP intervenes between a probe and its intended target:
1. The probe encounters the dative's phi-features (minimality)
2. But the dative bears lexical case (below the threshold)
3. The probe cannot successfully Agree with the dative
4. The probe also cannot "look past" the dative (locality)
5. Result: the probe FAILS → default agreement surfaces

This unifies dative intervention with Kichean AF: both are instances
of **obligatory agreement failing without crashing** (Ch. 5).

-/

namespace Minimalism

-- ============================================================================
-- § 1: Case Accessibility Levels
-- ============================================================================

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
  deriving DecidableEq, BEq, Repr

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

-- ============================================================================
-- § 2: Case Alignment
-- ============================================================================

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

-- ============================================================================
-- § 3: Agreement From Threshold
-- ============================================================================

/-- Agreement pattern: which argument positions trigger agreement. -/
structure AgreementPattern where
  sAgrees : Bool   -- intransitive subject
  aAgrees : Bool   -- transitive agent
  pAgrees : Bool   -- transitive patient
  deriving DecidableEq, BEq, Repr

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

-- ============================================================================
-- § 4: The Typological Gap
-- ============================================================================

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

-- ============================================================================
-- § 5: Contiguity
-- ============================================================================

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

-- ============================================================================
-- § 6: Dative Intervention
-- ============================================================================

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

-- ============================================================================
-- § 7: Kaqchikel Case Alignment
-- ============================================================================

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

end Minimalism
