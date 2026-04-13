import Linglib.Core.Prominence
import Linglib.Core.Relativization.Hierarchy
import Linglib.Core.SubjectProperties
import Linglib.Theories.Semantics.Causation.Morphological
import Linglib.Phenomena.Alignment.Typology
import Linglib.Phenomena.Causation.Typology
import Linglib.Fragments.Dargwa.ComplexPredicates

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
-- § 2a: Deriving Subject Properties from Alignment
-- ============================================================================

/-! ### Alignment predicts subject property convergence

@cite{comrie-1989} Ch 5: alignment type predicts whether subject
properties converge. In accusative languages, all properties pick S=A.
In ergative languages, coding properties pick S=P; whether behavioral
properties also pick S=P (**syntactic** ergativity, rare) or S=A
(**morphological** ergativity, common) is a parametric dimension.

The `toSubjectBundle` function derives the predicted subject property
bundle from alignment type, so the three stipulated bundles in
`Core.SubjectProperties` become consequences of alignment classification
rather than independent definitions. -/

/-- Derive the predicted subject property bundle from alignment type.
    Non-ergative alignment → all properties S=A (accusative bundle).
    Ergative → coding S=P, behavioral parametric. -/
def toSubjectBundle (a : AlignmentType)
    (syntacticErg : Bool := false) : SubjectPropertyBundle :=
  match a with
  | .ergative =>
    if syntacticErg then syntacticErgativityBundle
    else morphErgativityBundle
  | _ => accusativeBundle

/-- Accusative alignment derives the accusative bundle. -/
theorem accusative_derives_bundle :
    toSubjectBundle .accusative = accusativeBundle := rfl

/-- Ergative alignment (default) derives morphological ergativity bundle. -/
theorem morphErg_derives_bundle :
    toSubjectBundle .ergative = morphErgativityBundle := rfl

/-- Ergative alignment with syntacticErg=true derives syntactic ergativity. -/
theorem syntacticErg_derives_bundle :
    toSubjectBundle .ergative (syntacticErg := true)
    = syntacticErgativityBundle := rfl

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
-- § 3a: Per-Language Subject Property Predictions
-- ============================================================================

/-! ### Alignment profiles predict subject property convergence

Each language's alignment profile (from `Phenomena.Alignment.Typology`)
generates a predicted subject property bundle via `toSubjectBundle`.
These theorems verify the predictions against the known typological
facts for each language:

- **Accusative** languages (English, Japanese): derived bundle converges.
- **Morphologically ergative** languages (Basque, Dargwa, Hindi-Urdu):
  derived bundle diverges (coding ≠ behavioral).
- **Syntactically ergative** languages (Dyirbal): must set
  `syntacticErg := true` to get a converging bundle.

The `syntacticErg` parameter captures the rare/common ergativity
distinction that @cite{comrie-1989} Ch 5 identifies as central. -/

open Phenomena.Alignment.Typology
  (english dyirbal basque hindiUrdu dargwa japanese)

/-- English: accusative NP alignment → derived bundle converges. -/
theorem english_subject_from_alignment :
    (toSubjectBundle english.npAlignment).converges = true := by decide

/-- Japanese: accusative NP alignment → derived bundle converges. -/
theorem japanese_subject_from_alignment :
    (toSubjectBundle japanese.npAlignment).converges = true := by decide

/-- Basque: ergative alignment → default (morphological) derived bundle
    diverges, correctly predicting that coding and behavioral properties
    pick different NPs. -/
theorem basque_morphErg_diverges :
    (toSubjectBundle basque.npAlignment).converges = false := by decide

/-- Basque's derived bundle is exactly the morphological ergativity
    bundle: coding picks S=P, behavioral picks S=A. -/
theorem basque_bundle_is_morphErg :
    toSubjectBundle basque.npAlignment = morphErgativityBundle := rfl

/-- Dargwa: consistently ergative → morphological ergativity predicted. -/
theorem dargwa_bundle_is_morphErg :
    toSubjectBundle dargwa.npAlignment = morphErgativityBundle := rfl

/-- Hindi-Urdu: ergative NP alignment → morphological ergativity predicted.
    The split-ergative conditioning (perfective → ERG) is orthogonal to
    subject property convergence: even in perfective clauses, behavioral
    properties track S=A. -/
theorem hindiUrdu_morphErg_diverges :
    (toSubjectBundle hindiUrdu.npAlignment).converges = false := by decide

/-- Dyirbal: ergative NP alignment → default (morphological) prediction
    diverges. But Dyirbal is one of the rare **syntactically ergative**
    languages (@cite{dixon-1972}): even behavioral properties
    (coordination deletion) track S=P. -/
theorem dyirbal_default_diverges :
    (toSubjectBundle dyirbal.npAlignment).converges = false := by decide

/-- Dyirbal with syntacticErg=true → derived bundle converges,
    correctly predicting full syntactic ergativity. -/
theorem dyirbal_syntacticErg_converges :
    (toSubjectBundle dyirbal.npAlignment (syntacticErg := true)).converges
    = true := by decide

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

-- ============================================================================
-- § 5a: CauseeSlot ↔ AHPosition — Shared GR Hierarchy
-- ============================================================================

/-! ### The GR hierarchy underlying both causee demotion and relativization

@cite{comrie-1989} observes that the **same** grammatical relation
hierarchy governs both causee demotion (Ch 8) and relativization
accessibility (Ch 7):

    Subject > Direct Object > Indirect Object > Oblique

`CauseeSlot` (in `Theories.Semantics.Causation.Morphological`) and
`AHPosition` (in `Core.Relativization.Hierarchy`) encode overlapping
portions of this hierarchy independently. The bridge function
`causeeToAH` maps causee slots to their corresponding AH positions,
and the order-preservation theorem proves the mapping is monotone —
confirming that the two hierarchies are structurally the same. -/

/-- Map causee slots to their corresponding AH positions.
    Both encode the same GR hierarchy; this bridge makes the
    connection explicit. -/
def causeeToAH : CauseeSlot → AHPosition
  | .directObject   => .directObject
  | .indirectObject => .indirectObject
  | .oblique        => .oblique

/-- The mapping preserves ordering: higher causee rank ↔ higher AH rank. -/
theorem causee_ah_order_preserved (s1 s2 : CauseeSlot) :
    s1.rank > s2.rank ↔ (causeeToAH s1).rank > (causeeToAH s2).rank := by
  cases s1 <;> cases s2 <;> simp [CauseeSlot.rank, causeeToAH, AHPosition.rank]

/-- Causee demotion follows the AH: the slots assigned by `causeeDemotion`
    correspond to exactly the AH positions below subject. -/
theorem causeeDemotion_maps_to_ah :
    causeeToAH (causeeDemotion 1) = .directObject ∧
    causeeToAH (causeeDemotion 2) = .indirectObject ∧
    causeeToAH (causeeDemotion 3) = .oblique := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 6: Dargwa Causee Data — Fragment Bridge
-- ============================================================================

/-! ### Dargwa causative system bridges to Comrie's causee hierarchy

Dargwa (Tanti) has a productive causative morpheme *-aq*
(@cite{sumbatova-2021} §4.5.7). The Dargwa fragment
(`Fragments.Dargwa.ComplexPredicates`) records:

- Intransitive base: causee appears in **absolutive** = direct object slot
- Transitive base: causee appears in **elative** = oblique slot

Comrie's hierarchy predicts IO for transitive bases, but Dargwa
skips the IO position and demotes directly to oblique (elative).
This is consistent with monotonicity — the actual slot is at most
as high as the predicted slot — but represents a language-specific
choice to use a spatial case rather than a dative/IO. -/

open Fragments.Dargwa.ComplexPredicates (causStandUp causDig CausativeEntry)

/-- Map Dargwa causee case to CauseeSlot based on base verb transitivity.
    Intransitive base → DO (absolutive in Dargwa);
    transitive base → OBL (elative in Dargwa). -/
def dargwaCauseeSlot (e : CausativeEntry) : CauseeSlot :=
  if e.baseTransitive then .oblique else .directObject

/-- Dargwa intransitive causative: causee = DO, exactly matching
    Comrie's prediction (`causeeDemotion 1`). -/
theorem dargwa_intr_matches_prediction :
    dargwaCauseeSlot causStandUp = causeeDemotion 1 := rfl

/-- Dargwa transitive causative: causee = OBL, one step below
    Comrie's prediction of IO (`causeeDemotion 2`). Dargwa uses elative
    (a spatial/oblique case) rather than dative/IO. -/
theorem dargwa_tr_more_demoted :
    (dargwaCauseeSlot causDig).rank < (causeeDemotion 2).rank := by decide

/-- Dargwa preserves Comrie's monotonicity: intransitive causee
    outranks transitive causee on the GR hierarchy. -/
theorem dargwa_causee_monotone :
    (dargwaCauseeSlot causStandUp).rank >
    (dargwaCauseeSlot causDig).rank := by decide

/-- Dargwa causee slots map to the same AH positions as the
    cross-linguistic generalization. -/
theorem dargwa_causee_on_ah :
    causeeToAH (dargwaCauseeSlot causStandUp) = .directObject ∧
    causeeToAH (dargwaCauseeSlot causDig) = .oblique := ⟨rfl, rfl⟩

end Phenomena.Case.Studies.Comrie1989
