import Linglib.Studies.CoonMateoPedroPreminger2014
import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Features.Case.Basic
import Linglib.Syntax.Case.Alignment
import Linglib.Fragments.Mayan.Kaqchikel.Agreement
import Linglib.Fragments.Mayan.Chol.Agreement
import Linglib.Fragments.Mayan.Qanjobal.Agreement

/-!
# Imanishi (2020): Parameterizing Split Ergativity in Mayan
[imanishi-2020]

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

2. **Mayan Absolutive Parameter** ([coon-mateo-pedro-preminger-2014]):
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

namespace Imanishi2020

open Minimalist Minimalist.Voice
open Mayan (MarkerSet ABSPosition)

-- ============================================================================
-- § 0: Accusative-Side Alignment Patterns
-- ============================================================================

/-- Alignment pattern in the accusative (non-perfective) side of the Mayan
    split. Records which marker set cross-references S (= A on the
    accusative side) and which cross-references O.

    **Kaqchikel type** (S = ABS, O = ERG/GEN): S and A are
    cross-referenced by absolutive (set B) markers; the transitive object
    by ergative/genitive (set A). **Chol/Q'anjob'al type**: the mirror
    image. -/
structure AccSidePattern where
  /-- Marker set cross-referencing S (intransitive subject) and
      A (transitive subject) — these pattern together on the accusative side. -/
  sMarker : MarkerSet
  /-- Marker set cross-referencing O (transitive object). -/
  oMarker : MarkerSet
  deriving DecidableEq, Repr

/-- Kaqchikel-type accusative alignment: S/A = set B (ABS), O = set A (ERG/GEN). -/
def kaqchikelPattern : AccSidePattern :=
  { sMarker := .setB, oMarker := .setA }

/-- Chol/Q'anjob'al-type accusative alignment: S/A = set A (ERG/GEN), O = set B (ABS). -/
def cholPattern : AccSidePattern :=
  { sMarker := .setA, oMarker := .setB }

/-- The two accusative-side patterns are distinct. -/
theorem patterns_distinct : kaqchikelPattern ≠ cholPattern := by decide

/-- The two patterns are mirror images: the marker sets are swapped. -/
theorem patterns_mirror :
    kaqchikelPattern.sMarker = cholPattern.oMarker ∧
    kaqchikelPattern.oMarker = cholPattern.sMarker := ⟨rfl, rfl⟩

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
  deriving DecidableEq, Repr

-- ============================================================================
-- § 2: Mayan Absolutive Parameter
-- ============================================================================

-- Reuses `Mayan.ABSPosition` from `Fragments/Mayan/Params.lean` directly.

-- ============================================================================
-- § 3: Language Parameterization
-- ============================================================================

/-- Parameters for a Mayan language's split-ergative system. -/
structure MayanParams where
  ron : RON
  absPos : ABSPosition
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

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
    ¬ passive.AssignsTheta := by decide

/-- Agentive Voice violates the RON: it projects an external argument. -/
theorem agentive_violates_ron :
    agentive.AssignsTheta := by decide

/-- A Voice head is compatible with the RON iff it does not assign a
    θ-role (and hence does not project an external argument). -/
def RonCompatibleVoice (v : Head) : Prop :=
  ¬ v.AssignsTheta

instance (v : Head) : Decidable (RonCompatibleVoice v) := by
  unfold RonCompatibleVoice; infer_instance

theorem passive_ron_compatible : RonCompatibleVoice passive := by decide

theorem agentive_ron_incompatible : ¬ RonCompatibleVoice agentive := by decide

theorem anticausative_ron_compatible :
    RonCompatibleVoice anticausative := by decide

-- ============================================================================
-- § 8: Bridge to Existing Fragments
-- ============================================================================

/-- Kaqchikel's perfective (ergative) case assignment from the existing
    fragment: A = ERG, S = P = ABS. Confirms the ergative side is
    shared across all three languages. -/
theorem kaqchikel_perfective_bridge :
    Kaqchikel.ArgPosition.case .A = .erg ∧
    Kaqchikel.ArgPosition.case .P = .abs ∧
    Kaqchikel.ArgPosition.case .S = .abs := ⟨rfl, rfl, rfl⟩

/-- Chol's perfective alignment matches the same ergative pattern. -/
theorem chol_perfective_bridge :
    Chol.ArgPosition.case .A = .erg ∧
    Chol.ArgPosition.case .P = .abs ∧
    Chol.ArgPosition.case .S = .abs := ⟨rfl, rfl, rfl⟩

/-- Q'anjob'al's perfective alignment matches the same ergative pattern. -/
theorem qanjobal_perfective_bridge :
    Qanjobal.ArgPosition.case .A = .erg ∧
    Qanjobal.ArgPosition.case .P = .abs ∧
    Qanjobal.ArgPosition.case .S = .abs := ⟨rfl, rfl, rfl⟩

/-- All three languages share ergative alignment in the perfective. -/
theorem shared_ergative :
    Kaqchikel.ArgPosition.case .A =
      Chol.ArgPosition.case .A ∧
    Chol.ArgPosition.case .A =
      Qanjobal.ArgPosition.case .A := ⟨rfl, rfl⟩

-- ============================================================================
-- § 9: Case-to-Marker Bridge
-- ============================================================================

/-- Map Minimalist case values to the Mayan marker set that realizes them.
    ERG and GEN are both realized by set A (they are homophonous in Mayan).
    ABS is realized by set B. The wildcard maps non-Mayan cases (NOM, ACC,
    DAT, etc.) to set A — these should never appear in Mayan fragments. -/
def caseToMarker : Case → MarkerSet
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
    caseToMarker (Chol.ArgPosition.accCase .A) = cholPattern.sMarker ∧
    caseToMarker (Chol.ArgPosition.accCase .P) = cholPattern.oMarker :=
  ⟨rfl, rfl⟩

/-- Q'anjob'al's fragment case values yield the same pattern as Chol. -/
theorem qanjobal_case_to_marker_bridge :
    caseToMarker (Qanjobal.ArgPosition.accCase .A) = cholPattern.sMarker ∧
    caseToMarker (Qanjobal.ArgPosition.accCase .P) = cholPattern.oMarker :=
  ⟨rfl, rfl⟩

/-- Kaqchikel's fragment accusative-side case values, mapped through the
    Mayan marker bridge, yield the predicted Kaqchikel alignment pattern. -/
theorem kaqchikel_case_to_marker_bridge :
    caseToMarker (Kaqchikel.ArgPosition.accCase .A) = kaqchikelPattern.sMarker ∧
    caseToMarker (Kaqchikel.ArgPosition.accCase .P) = kaqchikelPattern.oMarker :=
  ⟨rfl, rfl⟩

/-- The accusative-side case contrast between Kaqchikel and Chol is a
    true mirror image: agent and patient cases are swapped. -/
theorem acc_case_mirror :
    Kaqchikel.ArgPosition.accCase .A =
      Chol.ArgPosition.accCase .P ∧
    Kaqchikel.ArgPosition.accCase .P =
      Chol.ArgPosition.accCase .A := ⟨rfl, rfl⟩

/-- End-to-end: for all three languages, the fragment case data (mapped
    through the marker bridge) matches the parametrically derived pattern.
    This closes the argumentation chain from parameters → alignment → case → markers. -/
theorem end_to_end_all_languages :
    -- Kaqchikel: fragment cases match derived pattern
    (caseToMarker (Kaqchikel.ArgPosition.accCase .A) =
      (deriveAccPattern kaqchikelParams).sMarker ∧
     caseToMarker (Kaqchikel.ArgPosition.accCase .P) =
      (deriveAccPattern kaqchikelParams).oMarker) ∧
    -- Chol: fragment cases match derived pattern
    (caseToMarker (Chol.ArgPosition.accCase .A) =
      (deriveAccPattern cholParams).sMarker ∧
     caseToMarker (Chol.ArgPosition.accCase .P) =
      (deriveAccPattern cholParams).oMarker) ∧
    -- Q'anjob'al: fragment cases match derived pattern
    (caseToMarker (Qanjobal.ArgPosition.accCase .A) =
      (deriveAccPattern qanjobalParams).sMarker ∧
     caseToMarker (Qanjobal.ArgPosition.accCase .P) =
      (deriveAccPattern qanjobalParams).oMarker) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

-- ============================================================================
-- § 10: Split Ergativity as Aspect-Conditioned
-- ============================================================================

/-- The Mayan split is aspect-conditioned: perfective → ergative,
    non-perfective → accusative. Instantiates the same `SplitErgativity`
    infrastructure as the Hindi example in `Alignment.SplitErgativity`. -/
def mayanSplit : Alignment.SplitErgativity Alignment.Aspect :=
  { ergCondition := λ a => a == .perfective }

theorem mayan_perfective_erg :
    mayanSplit.alignment .perfective = .ergative := rfl

theorem mayan_imperfective_acc :
    mayanSplit.alignment .imperfective = .accusative := rfl

/-- Mayan and Hindi have the same aspect-conditioned split direction:
    perfective triggers ergativity in both language families. -/
theorem mayan_hindi_same_split : mayanSplit = Alignment.hindiSplit := rfl

-- ============================================================================
-- § 11: Cross-Study Bridge ([coon-mateo-pedro-preminger-2014])
-- ============================================================================

open CoonMateoPedroPreminger2014 (hasSyntacticErgativity)
open Mayan (toCaseLocus)

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

end Imanishi2020
