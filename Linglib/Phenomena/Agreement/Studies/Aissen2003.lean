import Linglib.Phenomena.Agreement.DifferentialIndexing
import Linglib.Phenomena.Case.Typology
import Linglib.Theories.Syntax.Minimalist.PersonGeometry
import Linglib.Fragments.Mayan.Kaqchikel.Agreement
import Linglib.Fragments.Basque.Agreement
import Linglib.Fragments.Georgian.Agreement
import Linglib.Fragments.Hungarian.Predicates

/-!
Differential Indexing ↔ DOM, PersonGeometry, Kaqchikel
@cite{aissen-2003} @cite{just-2024} @cite{preminger-2014}

Connects @cite{just-2024} differential indexing to three existing formalizations:

1. **@cite{aissen-2003} DOM profiles** (`Phenomena/Case/Typology`): DOM is the
   P-flagging specialization of the general differential marking framework.
   This bridge proves that DOM profiles and P-indexing profiles share the
   same monotonicity constraint over the same scales.

2. **@cite{preminger-2014} PersonGeometry** (`Theories/Syntax/Minimalism/`):
   Just's binary person split (SAP vs 3rd) is precisely Preminger's
   [±participant] feature. This bridge makes the connection explicit.

3. **Kaqchikel Agreement** (`Fragments/Kaqchikel/`): Kaqchikel indexes both
   A and P arguments (Set A for agent, Set B for patient). This is a
   non-differential system — all person-number combinations are indexed —
   which serves as the baseline against which differential systems are
   defined.

-/

namespace Aissen2003

open Features.Prominence
open Phenomena.Agreement.DifferentialIndexing
open Phenomena.Case.Typology
open Minimalist
open Fragments.Mayan.Kaqchikel

-- ============================================================================
-- § 1: DOM ↔ DifferentialMarkingProfile Structural Isomorphism
-- ============================================================================

/-! `DOMProfile` is an abbreviation for `DifferentialMarkingProfile`
    (specialized to role P + channel flagging), and `IndexingFragment`
    extends `DifferentialMarkingProfile` (with channel = `.indexing`).
    Both DOM profiles and indexing fragments inherit all DMP infrastructure
    (monotonicity, dimensionality, cutoff constructors, mirror image)
    directly — no conversion or bridge theorems needed. -/

-- ============================================================================
-- § 2: PersonGeometry ↔ IndexingPersonLevel Connection
-- ============================================================================

/-! Just's binary person split (SAP vs 3rd) is exactly Preminger's
    [±participant] feature decomposition. -/

/-- Map a PersonLevel to Just's IndexingPersonLevel.
    1st/2nd → SAP, 3rd → third. -/
def personToLevel : PersonLevel → IndexingPersonLevel
  | .first  => .sap
  | .second => .sap
  | .third  => .third

/-- personToLevel agrees with decomposePerson on the participant split:
    SAP ↔ [+participant], third ↔ [−participant]. -/
theorem personLevel_matches_participant :
    (personToLevel .first == .sap) = (decomposePerson .first).hasParticipant ∧
    (personToLevel .second == .sap) = (decomposePerson .second).hasParticipant ∧
    (personToLevel .third == .sap) = (decomposePerson .third).hasParticipant := by
  exact ⟨rfl, rfl, rfl⟩

/-- SAP has higher prominence rank than 3rd, just as [+participant]
    gives higher probe resolution rank. -/
theorem personLevel_rank_matches_probe_rank :
    (IndexingPersonLevel.sap.rank > IndexingPersonLevel.third.rank) ∧
    (probeResolutionRank .first false > probeResolutionRank .third false) ∧
    (probeResolutionRank .second false > probeResolutionRank .third false) := by decide

-- ============================================================================
-- § 3: Kaqchikel as Non-Differential Baseline
-- ============================================================================

/-! Kaqchikel indexes both A and P arguments uniformly across all
    person-number combinations. This is a NON-differential system: there is
    no prominence-based asymmetry in which arguments get indexed.

    @cite{just-2024} defines differential indexing against this kind of
    baseline: a differential system is one where indexing depends on
    prominence properties. -/

/-- Kaqchikel indexes all three argument positions (agent, patient, intranS).
    This makes it non-differential: no prominence condition gates indexing. -/
theorem kaqchikel_indexes_all (p : ArgPosition) (h : p ∈ kaqArgPositions) :
    ArgPosition.IsPhiAgreed p :=
  Fragments.Mayan.Kaqchikel.all_positions_agreed p h

/-- Both A (agent) and P (patient) are indexed in Kaqchikel:
    agent via Set A on Voice/v, patient via Set B on Infl/T. -/
theorem kaqchikel_A_and_P_indexed :
    ArgPosition.IsPhiAgreed .A ∧
    ArgPosition.IsPhiAgreed .P := ⟨trivial, trivial⟩

/-- The A marker paradigm (Set A) and P marker paradigm (Set B) are
    distinct: every person-number combination gets a unique marker in
    each set (except 3SG which is ∅ in Set B). -/
theorem kaqchikel_dual_paradigms :
    setAExponent .p1sg ≠ setBExponent .p1sg ∧
    setAExponent .p2sg ≠ setBExponent .p2sg := by decide

-- ============================================================================
-- § 4: Kaqchikel Argument Roles ↔ Just's ArgumentRole
-- ============================================================================

/-- Map Kaqchikel argument positions to Just's A/P roles. The
    absolutive collapse: S patterns with P, A stays distinct;
    ditransitive R/T default to P (consistent with absolutive
    grouping). -/
def kaqArgToRole : ArgPosition → ArgumentRole
  | .A => .A
  | .S | .P | .R | .T => .P  -- S patterns with P (absolutive alignment)

/-- Identity on A and P; the load-bearing structure is the S → P
    collapse encoded in `kaqArgToRole`. -/
theorem kaqArg_role_mapping :
    kaqArgToRole .A = .A ∧
    kaqArgToRole .P = .P ∧
    kaqArgToRole .S = .P := ⟨rfl, rfl, rfl⟩

/-- Ergative-absolutive alignment: A is distinguished (ERG) while P and S
    pattern together (ABS). This parallels Just's A/P split. -/
theorem erg_abs_matches_AP :
    ArgPosition.case .A ≠ ArgPosition.case .P ∧
    ArgPosition.case .P = ArgPosition.case .S := ⟨by decide, rfl⟩

-- ============================================================================
-- § 5: Cross-Framework — Person Dominance
-- ============================================================================

/-! Person is the dominant conditioning factor for both P indexing and
    A indexing. The structural correlate is that the [participant]
    probe (π⁰) takes priority over the [plural] probe (#⁰) under the
    two-probe relativized-probing system @cite{bejar-rezac-2003} —
    NOT a salience hierarchy. @cite{preminger-2014} Ch. 7 explicitly
    argues against direct salience-scale primitives; the rank
    ordering below is a surface effect of probe priority, not a
    hierarchy-as-grammatical-primitive. See
    `Phenomena/Agreement/Studies/Preminger2014.lean` for the
    anti-hierarchy theorems. -/

/-- Person dominates for both P and A indexing (derived from fragments). -/
theorem person_dominates_both :
    pPersonConditioned.length > pAnimacyConditioned.length ∧
    pPersonConditioned.length > pDefinitenessConditioned.length ∧
    aPersonConditioned.length >
      (aIndexingLanguages.filter (·.animacyConditioned)).length ∧
    aPersonConditioned.length >
      (aIndexingLanguages.filter (·.definitenessConditioned)).length := by
  native_decide

/-- Two-probe surface ranking @cite{bejar-rezac-2003}: [+participant]
    cells outrank [+plural,−participant] cells, which outrank 3SG. The
    typological frequency hierarchy (person > animacy > definiteness)
    parallels this — person features are both structurally privileged
    at the probe level and typologically dominant in indexing systems. -/
theorem two_probe_surface_ranking :
    probeResolutionRank .first false > probeResolutionRank .third true ∧
    probeResolutionRank .third true > probeResolutionRank .third false := by decide

-- ============================================================================
-- § 6: Basque Fragment ↔ Just's IndexingFragment
-- ============================================================================

/-! The Basque agreement fragment (`Fragments.Basque.Agreement`) encodes
    the same person-conditioned P indexing that @cite{just-2024} reports.
    We prove that the Fragment's `pIsIndexed` matches the survey data. -/

/-- Basque Fragment's P indexing matches the Just survey: SAP → indexed,
    3rd → not indexed, exactly as `basque.personIndexed`. -/
theorem basque_fragment_matches_survey :
    Fragments.Basque.Agreement.pIsIndexed .p1sg =
      basque.personIndexed .sap ∧
    Fragments.Basque.Agreement.pIsIndexed .p2sg =
      basque.personIndexed .sap ∧
    Fragments.Basque.Agreement.pIsIndexed .p3sg =
      basque.personIndexed .third := ⟨rfl, rfl, rfl⟩

/-- Basque Fragment confirms differential P indexing: some indexed, some not. -/
theorem basque_fragment_is_differential :
    Fragments.Basque.Agreement.allPersonNumbers.any
      Fragments.Basque.Agreement.pIsIndexed = true ∧
    !(Fragments.Basque.Agreement.allPersonNumbers.all
      Fragments.Basque.Agreement.pIsIndexed) = true :=
  ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- § 7: Georgian Fragment ↔ Just's IndexingFragment
-- ============================================================================

/-! The Georgian agreement fragment (`Fragments.Georgian.Agreement`) derives
    P indexing from the presence of object agreement prefixes (m-, g-, gv-).
    The indexed/not-indexed split aligns with SAP vs 3rd — same as the
    Just survey data. -/

/-- Georgian Fragment's P indexing matches the Just survey. -/
theorem georgian_fragment_matches_survey :
    Fragments.Georgian.Agreement.pIsIndexed .p1sg =
      georgian.personIndexed .sap ∧
    Fragments.Georgian.Agreement.pIsIndexed .p2sg =
      georgian.personIndexed .sap ∧
    Fragments.Georgian.Agreement.pIsIndexed .p3sg =
      georgian.personIndexed .third := ⟨rfl, rfl, rfl⟩

/-- Georgian Fragment's P indexing is grounded in object prefix morphology:
    indexed iff has overt prefix. Not stipulated — follows from the data. -/
theorem georgian_indexing_grounded :
    Fragments.Georgian.Agreement.allPersonNumbers.all (λ pn =>
      Fragments.Georgian.Agreement.pIsIndexed pn ==
      (Fragments.Georgian.Agreement.objectPrefix pn).isSome) = true := by
  native_decide

-- ============================================================================
-- § 8: Hungarian Fragment ↔ Just's IndexingFragment
-- ============================================================================

/-! The Hungarian predicate fragment (`Fragments.Hungarian.Predicates`)
    models the definite/indefinite conjugation split. This IS Just's
    differential P indexing by definiteness: the verb's agreement paradigm
    changes depending on whether the object is definite.

    The fragment's `formPastDef ≠ formPastIndef` encodes the same claim
    as the Just survey entry `hungarian.definitenessConditioned`. -/

/-- Hungarian verbs have distinct definite vs indefinite conjugation forms.
    This IS the morphological reflex of differential P indexing by
    definiteness. -/
theorem hungarian_conjugation_split :
    Fragments.Hungarian.Predicates.tud.formPastDef ≠
      Fragments.Hungarian.Predicates.tud.formPastIndef ∧
    Fragments.Hungarian.Predicates.mond.formPastDef ≠
      Fragments.Hungarian.Predicates.mond.formPastIndef ∧
    Fragments.Hungarian.Predicates.hisz.formPastDef ≠
      Fragments.Hungarian.Predicates.hisz.formPastIndef := by decide

/-- Hungarian is definiteness-conditioned (derived from the marking
    predicate), confirming the Fragment's conjugation split. -/
theorem hungarian_definiteness_conditioned :
    hungarian.definitenessConditioned = true := by native_decide

/-- Hungarian is NOT person-conditioned — all persons can trigger
    both conjugation types. -/
theorem hungarian_not_person_conditioned :
    hungarian.personConditioned = false := by native_decide

end Aissen2003
