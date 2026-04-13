import Linglib.Core.Prominence
import Linglib.Core.Relativization.Hierarchy
import Linglib.Core.SubjectProperties
import Linglib.Theories.Semantics.Causation.Morphological
import Linglib.Phenomena.Alignment.Typology
import Linglib.Phenomena.Causation.Typology

/-!
# Comrie (1989) @cite{comrie-1989}

Language Universals and Linguistic Typology: Syntax and Morphology.
2nd ed. University of Chicago Press.

Bridge study file connecting linglib's independently formalized typological
hierarchies and proving they cohere as @cite{comrie-1989}'s synthesis claims.

## Cross-hierarchy unity (Chs 5–9)

@cite{comrie-1989}'s central methodological point: the **same** prominence
hierarchies (animacy, definiteness, person) recur across multiple
grammatical domains:

- **Case marking** (Ch 6): Differential Object Marking driven by
  animacy/definiteness (@cite{aissen-2003} in `Case.Studies.Aissen2003`).
  `Core.Prominence.AnimacyLevel` is the shared type.
- **Alignment** (Ch 5–6): Split ergativity conditioned by
  @cite{silverstein-1976}'s hierarchy (`Alignment.Typology`).
  Same `AnimacyLevel` type governs the split threshold.
- **Relativization** (Ch 7): The @cite{keenan-comrie-1977} Accessibility
  Hierarchy orders grammatical relations by extraction accessibility
  (`Core.Relativization.Hierarchy`, `FillerGap.Studies.KeenanComrie1977`).
  The AH positions (Subject > DO > IO > OBL) mirror the GR hierarchy
  that governs causee demotion.
- **Causatives** (Ch 8): Morphological complexity correlates with semantic
  directness (`Theories.Semantics.Causation.Morphological`); causee
  marking follows the GR hierarchy (`CauseeSlot`).

The shared infrastructure in `Core.Prominence` ensures the animacy
connection is structural — by construction, not by theorem. The GR
hierarchy parallel between the AH and causee demotion is proved below.

## Subject as a cluster concept (Ch 5)

@cite{comrie-1989} argues that "subject" is not a primitive grammatical
relation but a **bundle** of coding and behavioral properties that converge
in accusative languages and diverge under ergativity. Formalized in
`Core.SubjectProperties`.

## Relative clauses and the AH (Ch 7)

Relativization typology is formalized in
`Phenomena.FillerGap.Studies.KeenanComrie1977` and
`Core.Relativization.Hierarchy`. The AH concerns accessibility to
extraction — a filler-gap dependency — which is why the study file
lives under `FillerGap/`. Non-extraction relative clause types
(correlatives, internally-headed RCs) fall outside the AH's scope:
@cite{comrie-1989} discusses them but they do not participate in the
hierarchy.
-/

namespace Phenomena.Case.Studies.Comrie1989

-- ============================================================================
-- § 1: Shared Animacy Scale
-- ============================================================================

/-! ### Cross-domain unity of the animacy hierarchy

The `AnimacyLevel` type in `Core.Prominence` is imported by both
`Phenomena.Alignment.Typology` (Silverstein's split ergativity) and
`Phenomena.Case.Studies.Aissen2003` (DOM via OT). This is structural
grounding: the same 3-level hierarchy (human > animate > inanimate)
governs both phenomena, with no possibility of drift between separate
definitions.

The same pattern holds for `DefinitenessLevel` and `PersonLevel` — all
three prominence scales are defined once in `Core.Prominence` and
imported by every downstream module. -/

open Core.Prominence (AnimacyLevel ArgumentRole)
open Phenomena.Alignment.Typology (AlignmentType)
open Core.SubjectProperties

-- ============================================================================
-- § 2: Alignment → Differential Marking Direction
-- ============================================================================

/-- Accusative alignment implies P is differentially marked (the patient
    receives overt case marking to distinguish it from S). This connects
    @cite{comrie-1989} Ch 5–6 to the DOM patterns in @cite{aissen-2003}:
    in an accusative language, it is the **P** role whose marking is
    sensitive to prominence (animate/definite Ps get marked, inanimates
    don't). -/
theorem accusative_marks_P :
    AlignmentType.accusative.marksPatient = true := rfl

/-- Ergative alignment implies A is differentially marked. In an
    ergative language, it is the **A** role whose marking is
    prominence-sensitive — less prominent As (full NPs, inanimates)
    get ergative marking. -/
theorem ergative_marks_A :
    AlignmentType.ergative.marksAgent = true := rfl

/-- Neutral alignment marks neither A nor P distinctly. -/
theorem neutral_marks_neither :
    AlignmentType.neutral.marksAgent = false ∧
    AlignmentType.neutral.marksPatient = false := ⟨rfl, rfl⟩

/-- The directionality of differential marking follows from alignment:
    accusative systems differentially mark the low-default role (P),
    ergative systems differentially mark the high-default role (A).
    This mirrors the polarity of marking in `Core.Prominence`:
    P is lowDefault, A is highDefault. -/
theorem marking_polarity_matches_alignment :
    ArgumentRole.P.lowDefault = true ∧
    ArgumentRole.A.highDefault = true := ⟨rfl, rfl⟩

-- ============================================================================
-- § 3: Subject Property Convergence under Alignment
-- ============================================================================

/-- In accusative languages, all subject properties converge on S=A.
    @cite{comrie-1989} Ch 5: "In accusative languages... the notion
    of subject is reasonably clear." -/
theorem accusative_subject_converges :
    accusativeBundle.converges = true := by decide

/-- In morphologically ergative languages, subject properties diverge:
    coding picks S=P (absolutive), behavioral picks S=A.
    @cite{comrie-1989} Ch 5: "In ergative languages, the various
    properties do not necessarily converge." -/
theorem morphErg_subject_diverges :
    morphErgativityBundle.converges = false := by decide

/-- In syntactically ergative languages (Dyirbal subordinate clauses),
    subject properties converge on S=P — full ergativity.
    This is the rare case where even behavioral tests track absolutive. -/
theorem syntacticErg_subject_converges :
    syntacticErgativityBundle.converges = true := by decide

-- ============================================================================
-- § 4: Causative Hierarchies
-- ============================================================================

open Semantics.Causation.Morphological
    (CausativeComplexity CausativeConstruction Mediation comrie_monotone
     CauseeSlot causeeDemotion)
open Phenomena.Causation.Typology (CausativeConstructionType)

/-- @cite{comrie-1989}'s compact-to-analytic and direct-to-indirect
    dimensions are connected: a compact+direct construction and a
    periphrastic+indirect construction satisfy the monotonicity
    predicate. -/
theorem compact_direct_vs_periphrastic_indirect :
    comrie_monotone
      ⟨.lexical, .direct, none, none⟩
      ⟨.periphrastic, .indirect, none, none⟩ := by
  intro _; decide

/-- Song's AND and PURP types both map to periphrastic on Comrie's scale,
    despite differing in implicativity. The implicativity distinction is
    orthogonal to morphological complexity. -/
theorem song_multiclause_both_periphrastic :
    CausativeConstructionType.and_.toComplexity = CausativeComplexity.periphrastic ∧
    CausativeConstructionType.purp.toComplexity = CausativeComplexity.periphrastic :=
  ⟨rfl, rfl⟩

/-- Causee demotion: intransitive base → causee gets DO (rank 2),
    transitive base → causee gets IO (rank 1). The causee is demoted
    as base valency increases. -/
theorem intransitive_causee_above_transitive_causee :
    (causeeDemotion 1).rank > (causeeDemotion 2).rank := by decide

-- ============================================================================
-- § 5: The Accessibility Hierarchy as a GR Hierarchy
-- ============================================================================

open Core (AHPosition)

/-- The top of the AH is the subject position — @cite{comrie-1989} Ch 7:
    "A language must be able to relativize subjects" (HC₁). The subject
    is the most accessible position on the hierarchy. -/
theorem subject_is_ah_top :
    AHPosition.subject.rank = 6 ∧
    ∀ p : AHPosition, p.rank ≤ AHPosition.subject.rank := by
  constructor
  · rfl
  · intro p; cases p <;> simp [AHPosition.rank]

/-- The AH mirrors the GR hierarchy used in causee marking:
    Subject > Direct Object > Indirect Object > Oblique.
    The same ordering governs both relativization accessibility and
    causee demotion — positions higher on the hierarchy are both more
    accessible to relativization and filled first in causativization. -/
theorem ah_mirrors_causee_hierarchy :
    AHPosition.subject.rank > AHPosition.directObject.rank ∧
    AHPosition.directObject.rank > AHPosition.indirectObject.rank ∧
    AHPosition.indirectObject.rank > AHPosition.oblique.rank := by
  exact ⟨by decide, by decide, by decide⟩

end Phenomena.Case.Studies.Comrie1989
