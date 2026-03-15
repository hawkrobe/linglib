import Linglib.Phenomena.Ergativity.Basic
import Linglib.Phenomena.Ergativity.Studies.CoonMateoPedroPreminger2014
import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Core.Case
import Linglib.Fragments.Mayan.Kaqchikel.Agreement
import Linglib.Fragments.Mayan.Chol.Agreement
import Linglib.Fragments.Mayan.Qanjobal.Agreement

/-!
# Imanishi (2020): Parameterizing Split Ergativity in Mayan
@cite{imanishi-2020}

Explains the alignment puzzle in the accusative (non-perfective) side of
Mayan split-ergative systems.

## The Alignment Puzzle

Kaqchikel, Chol, and Q'anjob'al all have (nearly) identical biclausal
structures for non-perfective clauses — an aspectual predicate embedding
a nominalized clause `[Asp ... [vP_NMLZ]]`. Yet:

- **Kaqchikel**: S/A = ABS (set B), O = ERG/GEN (set A)
- **Chol/Q'anjob'al**: S/A = ERG/GEN (set A), O = ABS (set B)

## The Analysis

Two parameters explain the contrast:

1. **Restriction on Nominalization (RON)**: The nominalizing head *n* in
   Kaqchikel obligatorily selects a vP lacking an external argument.
   In Chol and Q'anjob'al, *n* does not impose this restriction.

2. **Mayan Absolutive Parameter** (@cite{coon-mateo-pedro-preminger-2014}):
   High absolutive languages (Kaqchikel, Q'anjob'al) have Infl as the
   locus of absolutive Case; low absolutive languages (Chol) have Voice.

The RON alone determines the alignment type: it controls which argument
is the highest DP inside the nominalized clause and thus which receives
genitive Case from D.

## Intransitivization Strategies

The RON forces nominalized verbs in Kaqchikel to be intransitive.
Three strategies satisfy this:
- **Passivization**: Voice[PASSIVE] suppresses the external argument
- **Antipassivization**: internal argument demoted to oblique
- **Pseudo noun incorporation**: object Case-licensed by adjacency
-/

namespace Phenomena.Ergativity.Studies.Imanishi2020

open Minimalism
open Phenomena.Ergativity

-- ============================================================================
-- § 1: The Restriction on Nominalization (RON)
-- ============================================================================

/-- The Restriction on Nominalization (RON):
    "Nominalized verbs must lack a syntactically projected external argument."

    A property of the nominalizing head *n* in a given language. When active,
    *n* obligatorily selects for a vP without an external argument (i.e., no
    specifier of VoiceP projected inside the nominalized clause). -/
structure RON where
  active : Bool
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Mayan Absolutive Parameter
-- ============================================================================

-- Reuses `ABSPosition` from `Basic.lean` directly.

-- ============================================================================
-- § 3: Language Parameterization
-- ============================================================================

/-- Parameters for a Mayan language's split-ergative system. -/
structure MayanParams where
  ron : RON
  absPos : ABSPosition
  deriving DecidableEq, BEq, Repr

/-- Kaqchikel: RON active, high absolutive. -/
def kaqchikelParams : MayanParams :=
  { ron := ⟨true⟩, absPos := .high }

/-- Chol: RON inactive, low absolutive. -/
def cholParams : MayanParams :=
  { ron := ⟨false⟩, absPos := .low }

/-- Q'anjob'al: RON inactive, high absolutive. -/
def qanjobalParams : MayanParams :=
  { ron := ⟨false⟩, absPos := .high }

-- ============================================================================
-- § 4: Nominalized Clause Structure
-- ============================================================================

/-- Structure of the nominalized clause embedded under the aspectual
    predicate on the accusative side. The clause is
    `[DP [nP [vP [VoiceP [VP]]]]]` — verbal projections dominated by
    nominal projections.

    The key structural variable: whether an external argument is
    syntactically projected inside the nominalized clause.
    Determined by the RON. -/
structure NomClause where
  hasExternalArg : Bool
  hasInternalArg : Bool
  deriving DecidableEq, BEq, Repr

/-- Build the nominalized clause from the RON and transitivity. -/
def nomClauseFromRON (ron : RON) (transitive : Bool) : NomClause :=
  { hasExternalArg := !ron.active && transitive
  , hasInternalArg := transitive }

-- ============================================================================
-- § 5: Deriving the Accusative-Side Alignment
-- ============================================================================

/-- Derive the accusative-side alignment pattern from language parameters.

    The D head of the nominalized clause assigns genitive Case to the
    structurally closest (highest) DP. Since ERG and GEN are homophonous
    in Mayan (both realized as set A markers), the DP receiving GEN is
    cross-referenced by set A.

    - RON active → no external arg → internal arg is highest DP → set A on O
    - RON inactive → external arg present → external arg is highest → set A on S -/
def deriveAccPattern (params : MayanParams) : AccSidePattern :=
  let nc := nomClauseFromRON params.ron true
  match nc.hasExternalArg with
  | true  => { sMarker := .setA, oMarker := .setB }
  | false => { sMarker := .setB, oMarker := .setA }

-- ============================================================================
-- § 6: Correctness Theorems
-- ============================================================================

/-- Kaqchikel's parameters derive the Kaqchikel alignment pattern. -/
theorem kaqchikel_alignment :
    deriveAccPattern kaqchikelParams = kaqchikelPattern := rfl

/-- Chol's parameters derive the Chol alignment pattern. -/
theorem chol_alignment :
    deriveAccPattern cholParams = cholPattern := rfl

/-- Q'anjob'al's parameters derive the Chol pattern (same as Chol). -/
theorem qanjobal_alignment :
    deriveAccPattern qanjobalParams = cholPattern := rfl

/-- The RON alone determines the alignment type, regardless of ABSPosition.
    This is the paper's central result: the alignment puzzle reduces to
    a single binary parameter on the nominalizing head. -/
theorem ron_determines_alignment (abs : ABSPosition) :
    deriveAccPattern { ron := ⟨true⟩, absPos := abs } = kaqchikelPattern ∧
    deriveAccPattern { ron := ⟨false⟩, absPos := abs } = cholPattern :=
  ⟨rfl, rfl⟩

/-- Q'anjob'al and Kaqchikel share ABSPosition but differ in alignment —
    confirming that ABSPosition alone does not determine the accusative-side
    alignment. -/
theorem absPos_insufficient :
    kaqchikelParams.absPos = qanjobalParams.absPos ∧
    deriveAccPattern kaqchikelParams ≠ deriveAccPattern qanjobalParams :=
  ⟨rfl, by decide⟩

-- ============================================================================
-- § 7: RON and Intransitivization
-- ============================================================================

/-- Passive Voice satisfies the RON: no θ-role assignment means no
    external argument is projected. -/
theorem passive_satisfies_ron :
    voicePassive.assignsTheta = false := rfl

/-- Agentive Voice violates the RON: it projects an external argument. -/
theorem agentive_violates_ron :
    voiceAgent.assignsTheta = true := rfl

/-- A Voice head is compatible with the RON iff it does not assign a
    θ-role (and hence does not project an external argument). -/
def ronCompatibleVoice (v : VoiceHead) : Bool :=
  !v.assignsTheta

theorem passive_ron_compatible :
    ronCompatibleVoice voicePassive = true := rfl

theorem agentive_ron_incompatible :
    ronCompatibleVoice voiceAgent = false := rfl

theorem anticausative_ron_compatible :
    ronCompatibleVoice voiceAnticausative = true := rfl

-- ============================================================================
-- § 8: Bridge to Existing Fragments
-- ============================================================================

/-- Kaqchikel's perfective (ergative) case assignment from the existing
    fragment: A = ERG, S = P = ABS. Confirms the ergative side is
    shared across all three languages. -/
theorem kaqchikel_perfective_bridge :
    Fragments.Mayan.Kaqchikel.KaqArgPosition.agent.case = .erg ∧
    Fragments.Mayan.Kaqchikel.KaqArgPosition.patient.case = .abs ∧
    Fragments.Mayan.Kaqchikel.KaqArgPosition.intranS.case = .abs := ⟨rfl, rfl, rfl⟩

/-- Chol's perfective alignment matches the same ergative pattern. -/
theorem chol_perfective_bridge :
    Fragments.Mayan.Chol.ArgPosition.agent.ergCase = .erg ∧
    Fragments.Mayan.Chol.ArgPosition.patient.ergCase = .abs ∧
    Fragments.Mayan.Chol.ArgPosition.intranS.ergCase = .abs := ⟨rfl, rfl, rfl⟩

/-- Q'anjob'al's perfective alignment matches the same ergative pattern. -/
theorem qanjobal_perfective_bridge :
    Fragments.Mayan.Qanjobal.ArgPosition.agent.ergCase = .erg ∧
    Fragments.Mayan.Qanjobal.ArgPosition.patient.ergCase = .abs ∧
    Fragments.Mayan.Qanjobal.ArgPosition.intranS.ergCase = .abs := ⟨rfl, rfl, rfl⟩

/-- All three languages share ergative alignment in the perfective. -/
theorem shared_ergative :
    Fragments.Mayan.Kaqchikel.KaqArgPosition.agent.case =
      Fragments.Mayan.Chol.ArgPosition.agent.ergCase ∧
    Fragments.Mayan.Chol.ArgPosition.agent.ergCase =
      Fragments.Mayan.Qanjobal.ArgPosition.agent.ergCase := ⟨rfl, rfl⟩

-- ============================================================================
-- § 9: Case-to-Marker Bridge
-- ============================================================================

/-- Map Minimalist case values to the Mayan marker set that realizes them.
    ERG and GEN are both realized by set A (they are homophonous in Mayan).
    ABS is realized by set B. The wildcard maps non-Mayan cases (NOM, ACC,
    DAT, etc.) to set A — these should never appear in Mayan fragments. -/
def caseToMarker : CaseVal → MarkerSet
  | .erg => .setA
  | .gen => .setA
  | .abs => .setB
  | _    => .setA

/-- ERG/GEN homophony: both map to set A. -/
theorem erg_gen_homophonous :
    caseToMarker .erg = caseToMarker .gen := rfl

/-- Chol's fragment case values, mapped through the Mayan marker bridge,
    yield the predicted accusative-side pattern. -/
theorem chol_case_to_marker_bridge :
    caseToMarker (Fragments.Mayan.Chol.ArgPosition.agent.accCase) = cholPattern.sMarker ∧
    caseToMarker (Fragments.Mayan.Chol.ArgPosition.patient.accCase) = cholPattern.oMarker :=
  ⟨rfl, rfl⟩

/-- Q'anjob'al's fragment case values yield the same pattern as Chol. -/
theorem qanjobal_case_to_marker_bridge :
    caseToMarker (Fragments.Mayan.Qanjobal.ArgPosition.agent.accCase) = cholPattern.sMarker ∧
    caseToMarker (Fragments.Mayan.Qanjobal.ArgPosition.patient.accCase) = cholPattern.oMarker :=
  ⟨rfl, rfl⟩

/-- Kaqchikel's fragment accusative-side case values, mapped through the
    Mayan marker bridge, yield the predicted Kaqchikel alignment pattern. -/
theorem kaqchikel_case_to_marker_bridge :
    caseToMarker (Fragments.Mayan.Kaqchikel.KaqArgPosition.agent.accCase) = kaqchikelPattern.sMarker ∧
    caseToMarker (Fragments.Mayan.Kaqchikel.KaqArgPosition.patient.accCase) = kaqchikelPattern.oMarker :=
  ⟨rfl, rfl⟩

/-- The accusative-side case contrast between Kaqchikel and Chol is a
    true mirror image: agent and patient cases are swapped. -/
theorem acc_case_mirror :
    Fragments.Mayan.Kaqchikel.KaqArgPosition.agent.accCase =
      Fragments.Mayan.Chol.ArgPosition.patient.accCase ∧
    Fragments.Mayan.Kaqchikel.KaqArgPosition.patient.accCase =
      Fragments.Mayan.Chol.ArgPosition.agent.accCase := ⟨rfl, rfl⟩

/-- End-to-end: for all three languages, the fragment case data (mapped
    through the marker bridge) matches the parametrically derived pattern.
    This closes the argumentation chain from parameters → alignment → case → markers. -/
theorem end_to_end_all_languages :
    -- Kaqchikel: fragment cases match derived pattern
    (caseToMarker (Fragments.Mayan.Kaqchikel.KaqArgPosition.agent.accCase) =
      (deriveAccPattern kaqchikelParams).sMarker ∧
     caseToMarker (Fragments.Mayan.Kaqchikel.KaqArgPosition.patient.accCase) =
      (deriveAccPattern kaqchikelParams).oMarker) ∧
    -- Chol: fragment cases match derived pattern
    (caseToMarker (Fragments.Mayan.Chol.ArgPosition.agent.accCase) =
      (deriveAccPattern cholParams).sMarker ∧
     caseToMarker (Fragments.Mayan.Chol.ArgPosition.patient.accCase) =
      (deriveAccPattern cholParams).oMarker) ∧
    -- Q'anjob'al: fragment cases match derived pattern
    (caseToMarker (Fragments.Mayan.Qanjobal.ArgPosition.agent.accCase) =
      (deriveAccPattern qanjobalParams).sMarker ∧
     caseToMarker (Fragments.Mayan.Qanjobal.ArgPosition.patient.accCase) =
      (deriveAccPattern qanjobalParams).oMarker) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

-- ============================================================================
-- § 10: Split Ergativity as Aspect-Conditioned
-- ============================================================================

/-- The Mayan split is aspect-conditioned: perfective → ergative,
    non-perfective → accusative. Instantiates the same `SplitErgativity`
    infrastructure as the Hindi example in `Core.Case.SplitConditions`. -/
def mayanSplit : Core.SplitErgativity Core.Aspect :=
  { ergCondition := λ a => a == .perfective }

theorem mayan_perfective_erg :
    mayanSplit.alignment .perfective = .ergative := rfl

theorem mayan_imperfective_acc :
    mayanSplit.alignment .imperfective = .accusative := rfl

/-- Mayan and Hindi have the same aspect-conditioned split direction:
    perfective triggers ergativity in both language families. -/
theorem mayan_hindi_same_split : mayanSplit = Core.hindiSplit := rfl

-- ============================================================================
-- § 11: Cross-Study Bridge (@cite{coon-mateo-pedro-preminger-2014})
-- ============================================================================

open CoonMateoPedroPreminger2014 (hasSyntacticErgativity)
open Fragments.Mayan (toCaseLocus)

/-- Imanishi's RON determines the accusative-side alignment (this study),
    while CMP2014's CaseLocus determines syntactic ergativity (ergative side).
    Together they form the full Mayan parameterization: RON for the
    accusative side, ABSPosition→CaseLocus for the ergative side. -/
theorem cmp2014_ergativity_from_params (p : MayanParams) :
    hasSyntacticErgativity (toCaseLocus p.absPos) = (p.absPos == .high) := by
  cases p.absPos <;> rfl

/-- The two studies agree on Kaqchikel: RON active + HIGH-ABS = syntactic
    ergativity + Kaqchikel-type accusative alignment. -/
theorem kaqchikel_full_profile :
    deriveAccPattern kaqchikelParams = kaqchikelPattern ∧
    hasSyntacticErgativity (toCaseLocus kaqchikelParams.absPos) = true :=
  ⟨rfl, rfl⟩

/-- The two studies agree on Chol: RON inactive + LOW-ABS = no syntactic
    ergativity + Chol-type accusative alignment. -/
theorem chol_full_profile :
    deriveAccPattern cholParams = cholPattern ∧
    hasSyntacticErgativity (toCaseLocus cholParams.absPos) = false :=
  ⟨rfl, rfl⟩

/-- Q'anjob'al shows that the two dimensions are independent: HIGH-ABS
    (like Kaqchikel) but RON inactive (like Chol). Syntactic ergativity
    yes, but Chol-type accusative alignment. -/
theorem qanjobal_cross_cutting :
    hasSyntacticErgativity (toCaseLocus qanjobalParams.absPos) = true ∧
    deriveAccPattern qanjobalParams = cholPattern :=
  ⟨rfl, rfl⟩

end Phenomena.Ergativity.Studies.Imanishi2020
