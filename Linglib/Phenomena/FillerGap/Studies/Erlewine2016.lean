import Linglib.Fragments.Mayan.Kaqchikel.AgentFocus
import Linglib.Theories.Syntax.Minimalism.Core.Position

/-!
# Minimalism Bridge: Kaqchikel Agent Focus @cite{erlewine-2016}
@cite{erlewine-2018}

Connects the Kaqchikel Agent Focus fragment to the Minimalist analysis:
anti-locality (Position.lean) drives OT competition (ConstraintEvaluation.lean),
and the AF derivation emerges as optimal.

## The Derivation (@cite{erlewine-2016}, §§3, 5)

### Why the transitive derivation crashes

In a normal Kaqchikel transitive, the agent base-generates in Spec,vP
and is attracted to Spec,TP by the A-probe on T (receiving Set A
agreement). For Ā-extraction, the agent must then move from Spec,TP
to Spec,CP. But CP immediately dominates TP, so this step crosses no
intervening maximal projection — violating **Spec-to-Spec Anti-Locality
(SSAL)**.

### Why AF is selected

The grammar generates a competing candidate — the AF structure — with
an intransitive-like v that does NOT introduce the agent in Spec,vP.
The agent extracts directly to Spec,CP without passing through Spec,TP,
so no SSAL violation occurs. But the agent never enters Spec,TP, so
the A-probe cannot establish Set A (ergative) agreement — violating
the lower-ranked **XRef** (cross-referencing) constraint.

The OT evaluation selects AF because SSAL >> XRef: avoiding the
too-local movement outranks maintaining cross-referencing agreement.

### Key insight: locality, not extraction per se

AF is triggered by the *locality of movement*, not simply by agent
extraction. Long-distance agent extraction does NOT trigger AF:
successive-cyclic movement through intermediate Spec,CP avoids the
too-local Spec,TP → Spec,CP step.

### Connection to Position.lean

The `specToSpecAntiLocality` predicate (Position.lean) formalizes
exactly the constraint that blocks the transitive derivation: movement
from Spec,XP to Spec,YP is blocked when YP immediately dominates XP.
In Kaqchikel, XP = TP and YP = CP.

### Connection to ConstraintEvaluation.lean

The OT tableau in `Fragments/Kaqchikel/AgentFocus.lean` uses the
lexicographic comparison from `Core/Logic/ConstraintEvaluation.lean`.
The key result `af_is_optimal` shows that AF beats the transitive under
strict ranking — and `satisfaction_ordering_incomparable` shows this
requires OT's lexicographic comparison, not satisfaction ordering's
subset inclusion.

## Anti-agreement

AF is an instance of a broader cross-linguistic pattern: **anti-agreement**.
When extraction forces a DP to skip an A-position (to avoid SSAL),
the agreement morphology associated with that position is lost:

- Kaqchikel: Set A (ergative) lost when agent skips Spec,TP
- Trentino Italian: nominative agreement lost under extraction
- Karitiâna: absolutive agreement lost under extraction

All are derived by the same mechanism: SSAL forces skipping an
A-position, and agreement with the head at that position fails.

## Contrast with Toba Batak

Both Kaqchikel and Toba Batak have extraction
restrictions derived from anti-locality in predicate-fronting contexts.
But the repair strategies differ:

- **Toba Batak**: Voice alternation determines the pivot; extraction is
  *restricted* to the pivot position (structural restriction strategy).
- **Kaqchikel**: Anti-locality blocks agent extraction entirely; the
  grammar *repairs* the derivation via AF (agent focus alternation
  strategy).

Both use `specToSpecAntiLocality` from Position.lean, but Toba Batak's
pivot restriction is about nominal licensing while Kaqchikel's AF is
about OT candidate competition.

-/

namespace Erlewine2016

open Fragments.Mayan.Kaqchikel Minimalism
open Core.Constraint.OT (mkTableau)

-- ============================================================================
-- § 1: Anti-Locality Grounds the Transitive Crash
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

-- ============================================================================
-- § 2: OT Evaluation Selects AF
-- ============================================================================

/-- AF is the unique optimal candidate. SSAL >> XRef means the derivation
    that avoids anti-locality wins, even though it loses Set A agreement. -/
theorem af_wins :
    (mkTableau afCandidates afRanking).optimal =
      {AFCandidate.agentFocusExtraction} :=
  af_is_optimal

/-- The winning candidate surfaces with AF morphology: *-Vn* suffix,
    no Set A (ergative) agreement. -/
theorem af_morphology :
    AFCandidate.agentFocusExtraction.verbForm = .agentFocus ∧
    VerbForm.agentFocus.hasSetA = false ∧
    VerbForm.agentFocus.hasAFSuffix = true := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 3: Lexicographic vs Satisfaction Ordering
-- ============================================================================

/-- Under satisfaction ordering, neither candidate dominates: the
    transitive satisfies XRef but violates SSAL, while AF satisfies
    SSAL but violates XRef. Each satisfies a constraint the other
    violates — they are incomparable.

    This is why OT's lexicographic comparison (strict ranking) is
    necessary: it breaks the tie by giving priority to the higher-ranked
    constraint. Satisfaction ordering cannot select a winner. -/
theorem lex_needed :
    ¬(ssalConstraint.eval .transitiveExtraction ≤
        ssalConstraint.eval .agentFocusExtraction ∧
      xrefConstraint.eval .transitiveExtraction ≤
        xrefConstraint.eval .agentFocusExtraction) ∧
    ¬(ssalConstraint.eval .agentFocusExtraction ≤
        ssalConstraint.eval .transitiveExtraction ∧
      xrefConstraint.eval .agentFocusExtraction ≤
        xrefConstraint.eval .transitiveExtraction) :=
  satisfaction_ordering_incomparable

/-- The transitive candidate is lexicographically worse because it
    violates the HIGHER-ranked constraint (SSAL, position 0).
    AF violates only the lower-ranked constraint (XRef, position 1). -/
theorem transitive_worse_on_ssal :
    ssalConstraint.eval .transitiveExtraction >
      ssalConstraint.eval .agentFocusExtraction := by decide

-- ============================================================================
-- § 4: Anti-Locality Predicate Grounding
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
-- § 5: Extraction Asymmetry
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
-- § 6: Locality Sensitivity
-- ============================================================================

/-- AF is locality-sensitive: long-distance agent extraction does NOT
    trigger AF. When the agent extracts from an
    embedded clause, successive-cyclic movement avoids the too-local
    Spec,TP → Spec,CP step.

    This is the paper's deepest empirical claim: AF is about the
    *locality of movement*, not about agent extraction per se. -/
theorem locality_sensitivity :
    agentExtractionAF.verbForm = .agentFocus ∧
    longDistanceAgentExtraction.verbForm = .transitive := ⟨rfl, rfl⟩

-- ============================================================================
-- § 7: Extraction Strategy
-- ============================================================================

/-- Kaqchikel uses agent focus alternation, not structural restriction
    (Toba Batak) or dedicated morpheme (Mam). Different repair strategy,
    same underlying problem (anti-locality). -/
theorem strategy_is_af :
    kaqExtractionProfile.strategy = .agentFocusAlternation := rfl

end Erlewine2016
