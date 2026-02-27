import Linglib.Fragments.Mam.ExtractionMorphology
import Linglib.Fragments.Kiche.ExtractionMorphology

/-!
# Mayan Extraction Morphology: Parametric Comparison

@cite{elkins-imanishi-coon-2026}

Cross-linguistic comparison of extraction morphology in two Mayan
language groups: SJO Mam (=(y)a') and K'ichean (*wi*). Both mark
oblique extraction with a dedicated morpheme, but the underlying
mechanisms and distributional properties differ.

## Shared Properties

- Both mark oblique extraction (spatial, instrumental)
- Both exempt temporal obliques ('when')
- Neither marks subject extraction (Agent Focus instead)
- Neither marks object extraction

## Parametric Differences

| Property                      | Mam =(y)a'          | K'ichean *wi*         |
|-------------------------------|---------------------|-----------------------|
| Locus                         | On probe (Voice⁰)  | At extraction site    |
| Mechanism                     | Agree reflex        | Copy spellout         |
| Reason obliques ('why')       | =(y)a' ✓            | *wi* ✗                |
| Fronting Particle Generalization | Does not hold    | Holds                 |
| Conditioned by clause size    | Yes (Voice project.)| No                    |
| Multiple spellout in LD       | Yes (per Voice/Dir) | Unclear               |

## References

- Elkins, N., Y. Imanishi & J. Coon (2026). Wh-movement and oblique
  extraction in SJO Mam.
- Mondloch, J. & S. Romero (2022). Clause structure and movement in
  K'ichean.
- Henderson, R. (2008). Extraction and word order in K'iche'.
- Imanishi, Y. (2020). Parameterizing split ergativity in Mayan.
-/

namespace Phenomena.FillerGap.Bridge.MayanExtractionComparison

open Fragments.Mam Fragments.Kiche

-- ============================================================================
-- § 1: Shared Properties
-- ============================================================================

/-- Both Mam and K'ichean use dedicated morphemes for oblique extraction. -/
theorem both_mark_oblique :
    mamExtractionProfile.strategy = .dedicatedMorpheme ∧
    kicheanExtractionProfile.strategy = .dedicatedMorpheme := ⟨rfl, rfl⟩

/-- Both exempt temporal obliques from extraction marking. -/
theorem both_exempt_temporal :
    (Fragments.Mam.temporalOblExtraction.isTemporal = true ∧
     Fragments.Mam.temporalOblExtraction.judgment = .blocked) ∧
    Fragments.Kiche.temporalOblExtraction.wiLicensed = false :=
  ⟨⟨rfl, rfl⟩, rfl⟩

/-- Neither marks subject extraction (Agent Focus instead). -/
theorem neither_marks_subject :
    transSubjExtraction.judgment = .blocked ∧
    Fragments.Kiche.subjectExtraction.wiLicensed = false := ⟨rfl, rfl⟩

/-- Neither marks object extraction. -/
theorem neither_marks_object :
    transObjExtraction.judgment = .blocked ∧
    Fragments.Kiche.objectExtraction.wiLicensed = false := ⟨rfl, rfl⟩

-- ============================================================================
-- § 2: Parametric Differences
-- ============================================================================

/-- KEY CONTRAST — Reason obliques ('why'):
    Mam =(y)a' IS licensed with reason extraction; K'ichean *wi* is NOT.
    This is one of the strongest arguments that =(y)a' and *wi* have
    different underlying mechanisms.

    Under the Agree analysis: Voice's [uOblique] Agrees with any oblique
    (including reason), so =(y)a' appears.
    Under copy spellout: reason obliques may lack the relevant syntactic
    structure for *wi* to appear at the extraction site.

    Elkins et al. §8.1. -/
theorem reason_oblique_contrast :
    -- Mam: reason oblique triggers =(y)a' (same as spatial)
    transOblExtraction.judgment = .licensed ∧
    -- K'ichean: reason oblique does NOT trigger *wi*
    Fragments.Kiche.reasonOblExtraction.wiLicensed = false := ⟨rfl, rfl⟩

/-- Mam =(y)a' is conditioned by clause size (Voice must project);
    K'ichean *wi* is not (it appears at the extraction site regardless
    of clause size — the relevant condition is whether phrasal movement
    occurred, per the Fronting Particle Generalization).
    Elkins et al. §8.2. -/
theorem clause_size_sensitivity :
    MamClauseType.fullCP.projectsVoice = true ∧
    MamClauseType.aspectless.projectsVoice = true ∧
    MamClauseType.infinitival.projectsVoice = false ∧
    Fragments.Kiche.frontingParticleGeneralization = true := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 3: Theoretical Implications
-- ============================================================================

/-- The parametric differences follow from the locus difference:

    - **Agree reflex** (Mam): morpheme appears on the probe head (Voice/Dir).
      Conditioned by whether Voice projects. Sensitive to what Voice probes
      for (oblique feature). Not sensitive to movement type.

    - **Copy spellout** (K'ichean): morpheme appears at the extraction site.
      Conditioned by whether movement is phrasal (Fronting Particle Gen.).
      Not conditioned by clause size. Different oblique subtypes may have
      different copy structures.

    These are genuinely different mechanisms producing superficially similar
    morphological patterns. -/
inductive ExtractionMorphologyMechanism where
  | agreeReflex     -- Morpheme on probe head (Mam =(y)a')
  | copySpellout    -- Morpheme at extraction site (K'ichean *wi*)
  deriving DecidableEq, BEq, Repr

def mamMechanism : ExtractionMorphologyMechanism := .agreeReflex
def kicheanMechanism : ExtractionMorphologyMechanism := .copySpellout

theorem different_mechanisms :
    mamMechanism ≠ kicheanMechanism := by decide

end Phenomena.FillerGap.Bridge.MayanExtractionComparison
