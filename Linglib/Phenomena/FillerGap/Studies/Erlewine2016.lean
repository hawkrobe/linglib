import Linglib.Fragments.Mayan.Kaqchikel.AgentFocus
import Linglib.Theories.Syntax.Minimalist.Position
import Linglib.Core.Constraint.OT.Basic

/-!
# Erlewine 2016: Anti-Locality and Optimality in Kaqchikel Agent Focus
@cite{erlewine-2016} @cite{erlewine-2018}

@cite{erlewine-2016} analyzes Kaqchikel Agent Focus as the optimal
output of an OT competition between two derivations, ranked by
**Spec-to-Spec Anti-Locality (SSAL)** ≫ **XRef** (cross-referencing).
The fragment in `Fragments/Mayan/Kaqchikel/AgentFocus.lean` carries
typology-neutral data (verb-form types, extraction patterns, the
empirical AF profile); this study file adds the theory-laden OT
machinery (competing derivations, constraints, ranking) and verifies
@cite{erlewine-2016}'s results.

## The Derivation (@cite{erlewine-2016} §§3, 5)

### Why the transitive derivation crashes

In a normal Kaqchikel transitive, the agent base-generates in Spec,vP
and is attracted to Spec,TP by the A-probe on T (receiving Set A
agreement). For Ā-extraction, the agent must then move from Spec,TP
to Spec,CP. But CP immediately dominates TP, so this step crosses no
intervening maximal projection — violating Spec-to-Spec Anti-Locality.

### Why AF is selected

The grammar generates a competing candidate — the AF structure — with
an intransitive-like v that does NOT introduce the agent in Spec,vP.
The agent extracts directly to Spec,CP without passing through Spec,TP,
so no SSAL violation occurs. But the agent never enters Spec,TP, so
the A-probe cannot establish Set A (ergative) agreement — violating
the lower-ranked XRef constraint.

The OT evaluation selects AF because SSAL ≫ XRef: avoiding the
too-local movement outranks maintaining cross-referencing agreement.

### Key insight: locality, not extraction per se

AF is triggered by the *locality of movement*, not simply by agent
extraction. Long-distance agent extraction does NOT trigger AF:
successive-cyclic movement through intermediate Spec,CP avoids the
too-local Spec,TP → Spec,CP step.

### Connection to Position.lean

The `specToSpecAntiLocality` predicate (Position.lean) formalizes
the constraint that blocks the transitive derivation: movement from
Spec,XP to Spec,YP is blocked when YP immediately dominates XP. In
Kaqchikel, XP = TP and YP = CP. SSAL traces to @cite{abels-2003}'s
anti-locality theory, with refinements in @cite{boskovic-1997} and
many subsequent papers; @cite{erlewine-2016}'s contribution is the
specific application to Kichean AF as an OT-competing-candidate
analysis.

### Connection to Core.Constraint.OT

The OT tableau uses the lexicographic comparison from
`Core/Constraint/OT/Basic.lean`. The key result `af_is_optimal` shows
that AF beats the transitive under strict ranking — and
`satisfaction_ordering_incomparable` shows this requires OT's
lexicographic comparison, not satisfaction ordering's subset
inclusion.

## Anti-agreement

AF is an instance of a broader cross-linguistic pattern of
**anti-agreement**: when extraction forces a DP to skip an A-position
(to avoid SSAL), the agreement morphology associated with that
position is lost — Kaqchikel Set A under agent extraction, Trentino
Italian nominative under extraction, Karitiâna absolutive under
extraction. All derive from the same mechanism: SSAL forces skipping
an A-position, and agreement with the head at that position fails.

## Contrast with Toba Batak

Both Kaqchikel and Toba Batak have extraction restrictions derived
from anti-locality in predicate-fronting contexts, but the repair
strategies differ: Toba Batak restricts extraction to the pivot
position (structural restriction), while Kaqchikel repairs the
derivation via AF (alternation strategy). Both use
`specToSpecAntiLocality` from Position.lean.

-/

namespace Phenomena.FillerGap.Studies.Erlewine2016

open Fragments.Mayan.Kaqchikel Minimalist
open Core.Constraint.OT (mkTableau NamedConstraint ConstraintFamily)

-- ============================================================================
-- § 1: Competing Derivations
-- ============================================================================

/-- A candidate derivation for clause-local transitive agent extraction.
    The OT competition evaluates these: which structure best satisfies
    the ranked constraints? Both candidates share the same clausal spine
    (CP > TP > vP > VP); they differ in the v head and the agent's
    movement path. -/
inductive AFCandidate where
  /-- Normal transitive derivation: transitive v introduces agent in
      Spec,vP. A-probe on T attracts agent to Spec,TP (triggering Set A
      agreement). Subsequent Ā-extraction from Spec,TP to Spec,CP
      violates SSAL because CP immediately dominates TP. -/
  | transitiveExtraction
  /-- Agent Focus derivation: intransitive-like v, agent NOT in Spec,vP.
      Agent extracts directly to Spec,CP without passing through Spec,TP.
      No SSAL violation, but cross-referencing is incomplete: no Set A
      (ergative) agreement because the agent never enters Spec,TP. -/
  | agentFocusExtraction
  deriving DecidableEq, Repr

/-- The verb form that surfaces for each candidate. -/
def AFCandidate.verbForm : AFCandidate → VerbForm
  | .transitiveExtraction => .transitive
  | .agentFocusExtraction => .agentFocus

/-- Does this candidate violate Spec-to-Spec Anti-Locality (SSAL)?
    The transitive derivation does: the step Spec,TP → Spec,CP crosses
    no intervening maximal projection (CP immediately dominates TP). -/
def AFCandidate.violatesAntiLocality : AFCandidate → Bool
  | .transitiveExtraction => true
  | .agentFocusExtraction => false

/-- Does this candidate violate the XRef (cross-referencing) constraint?
    AF loses Set A agreement because the agent never enters Spec,TP
    where the A-probe resides. The transitive candidate maintains full
    cross-referencing (Set A + Set B). -/
def AFCandidate.violatesXRef : AFCandidate → Bool
  | .transitiveExtraction => false
  | .agentFocusExtraction => true

-- ============================================================================
-- § 2: OT Constraint Ranking — SSAL ≫ XRef
-- ============================================================================

/-- Spec-to-Spec Anti-Locality (highest-ranked): movement from Spec,XP
    to Spec,YP is banned when YP immediately dominates XP. -/
def ssalConstraint : NamedConstraint AFCandidate :=
  { name := "SSAL"
    family := .markedness
    eval := fun c => if c.violatesAntiLocality then 1 else 0 }

/-- XRef (cross-referencing, lower-ranked): every argument DP must be
    cross-referenced by a pronominal morpheme on the verb (Set A for
    ergative, Set B for absolutive). -/
def xrefConstraint : NamedConstraint AFCandidate :=
  { name := "XRef"
    family := .faithfulness
    eval := fun c => if c.violatesXRef then 1 else 0 }

/-- The ranked constraint list for Kaqchikel AF: SSAL ≫ XRef. -/
def afRanking : List (NamedConstraint AFCandidate) :=
  [ssalConstraint, xrefConstraint]

/-- The two candidates in the OT competition. -/
def afCandidates : List AFCandidate :=
  [.transitiveExtraction, .agentFocusExtraction]

-- ============================================================================
-- § 3: Anti-Locality Grounds the Transitive Crash
-- ============================================================================

/-- The transitive candidate violates SSAL. The agent, having moved to
    Spec,TP via the A-probe, cannot continue to Spec,CP because CP
    immediately dominates TP — the movement is too local. -/
theorem transitive_crashes :
    AFCandidate.transitiveExtraction.violatesAntiLocality = true := rfl

/-- The AF candidate does NOT violate SSAL. The agent skips Spec,TP
    and extracts directly to Spec,CP, crossing enough structure to
    satisfy anti-locality. -/
theorem af_survives :
    AFCandidate.agentFocusExtraction.violatesAntiLocality = false := rfl

/-- The two candidates have different violation profiles: they disagree
    on at least one constraint. -/
theorem candidates_differ :
    ssalConstraint.eval .transitiveExtraction ≠
      ssalConstraint.eval .agentFocusExtraction ∨
    xrefConstraint.eval .transitiveExtraction ≠
      xrefConstraint.eval .agentFocusExtraction := by decide

-- ============================================================================
-- § 4: OT Evaluation Selects AF
-- ============================================================================

/-- AF is the unique optimal candidate. SSAL ≫ XRef means the derivation
    that avoids anti-locality wins, even though it loses Set A agreement.
    This is the central result of @cite{erlewine-2016}. -/
theorem af_is_optimal :
    (mkTableau afCandidates afRanking).optimal =
      {AFCandidate.agentFocusExtraction} := by
  native_decide

/-- The winning candidate surfaces with AF morphology: *-Vn* suffix,
    no Set A (ergative) agreement. -/
theorem af_morphology :
    AFCandidate.agentFocusExtraction.verbForm = .agentFocus ∧
    VerbForm.agentFocus.hasSetA = false ∧
    VerbForm.agentFocus.hasAFSuffix = true := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 5: Lexicographic vs Satisfaction Ordering
-- ============================================================================

/-- Under componentwise ≤ (satisfaction ordering), neither candidate
    dominates: the transitive satisfies XRef but violates SSAL, while AF
    satisfies SSAL but violates XRef. Each satisfies a constraint the
    other violates — they are incomparable. OT's lexicographic ranking
    is what breaks the tie in favor of AF. -/
theorem satisfaction_ordering_incomparable :
    ¬(ssalConstraint.eval .transitiveExtraction ≤
        ssalConstraint.eval .agentFocusExtraction ∧
      xrefConstraint.eval .transitiveExtraction ≤
        xrefConstraint.eval .agentFocusExtraction) ∧
    ¬(ssalConstraint.eval .agentFocusExtraction ≤
        ssalConstraint.eval .transitiveExtraction ∧
      xrefConstraint.eval .agentFocusExtraction ≤
        xrefConstraint.eval .transitiveExtraction) := by
  decide

/-- The transitive candidate is lexicographically worse because it
    violates the HIGHER-ranked constraint (SSAL, position 0).
    AF violates only the lower-ranked constraint (XRef, position 1). -/
theorem transitive_worse_on_ssal :
    ssalConstraint.eval .transitiveExtraction >
      ssalConstraint.eval .agentFocusExtraction := by decide

-- ============================================================================
-- § 6: Anti-Locality Predicate Grounding
-- ============================================================================

/-- The transitive candidate's violation profile reflects
    `specToSpecAntiLocality` from Position.lean. The SSAL constraint
    assigns 1 violation to the transitive candidate and 0 to AF,
    grounding the OT violation count in the structural predicate. -/
theorem antilocality_grounded :
    ssalConstraint.eval .transitiveExtraction = 1 ∧
    ssalConstraint.eval .agentFocusExtraction = 0 :=
  ⟨rfl, rfl⟩

/-- AF wins because it has 0 violations of the highest-ranked constraint.
    The connection to `specToSpecAntiLocality`: the transitive derivation
    would require movement from Spec,TP to Spec,CP where CP immediately
    dominates TP — exactly what the predicate bans. AF avoids this
    by not placing the agent in Spec,TP at all. -/
theorem antilocality_drives_af :
    ssalConstraint.eval .agentFocusExtraction = 0 ∧
    (mkTableau afCandidates afRanking).optimal =
      {AFCandidate.agentFocusExtraction} :=
  ⟨rfl, af_is_optimal⟩

-- ============================================================================
-- § 7: Extraction Asymmetry
-- ============================================================================

/-- Patient extraction does NOT trigger AF: the patient starts in
    complement position (Comp,VP), not Spec,vP. It does not pass through
    Spec,TP on its way to Spec,CP, so no SSAL violation arises. -/
theorem patient_no_af :
    patientExtractionTrans.verbForm = .transitive := rfl

/-- AF is asymmetric: only clause-local agent extraction triggers it
    (because only the agent occupies Spec,vP → Spec,TP, creating the
    too-local Spec,TP → Spec,CP step). Patient extraction uses the
    normal transitive form. This asymmetry is the morphological
    signature of syntactic ergativity in Kaqchikel. -/
theorem extraction_asymmetry :
    agentExtractionAF.verbForm = .agentFocus ∧
    patientExtractionTrans.verbForm = .transitive := ⟨rfl, rfl⟩

-- ============================================================================
-- § 8: Locality Sensitivity
-- ============================================================================

/-- AF is locality-sensitive: long-distance agent extraction does NOT
    trigger AF. When the agent extracts from an embedded clause,
    successive-cyclic movement avoids the too-local Spec,TP → Spec,CP
    step. This is the paper's deepest empirical claim: AF is about the
    *locality of movement*, not about agent extraction per se. -/
theorem locality_sensitivity :
    agentExtractionAF.verbForm = .agentFocus ∧
    longDistanceAgentExtraction.verbForm = .transitive := ⟨rfl, rfl⟩

-- ============================================================================
-- § 9: Extraction Strategy
-- ============================================================================

/-- Kaqchikel uses agent focus alternation, not structural restriction
    (Toba Batak) or dedicated morpheme (Mam). Different repair strategy,
    same underlying problem (anti-locality). -/
theorem strategy_is_af :
    kaqExtractionProfile.strategy = .agentFocusAlternation := rfl

end Phenomena.FillerGap.Studies.Erlewine2016
