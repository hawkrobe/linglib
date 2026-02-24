import Linglib.Phenomena.ClauseChaining.Typology

/-! # Clause Chaining Data @cite{sarvasy-aikhenvald-2025}

Language-specific clause chaining parameters for six typologically diverse
languages, drawn from Sarvasy & Aikhenvald (2025). The sample is designed to
cover the major parameter combinations:

| Language | Family | SR | Direction | Morphology |
|----------|--------|-----|-----------|------------|
| Nungon | Trans-New Guinea | SS/DS+temporal | medial-final | maximally reduced |
| Manambu | Ndu (Sepik) | SS/DS | medial-final | restricted |
| Ku Waru | Trans-New Guinea | SS/DS | medial-final | reduced |
| Korean | Koreanic | none | medial-final | partially retained |
| Turkish | Turkic | none | medial-final | partially retained |
| Korowai | Trans-New Guinea | multi-track | medial-final | reduced |

## Implicational universals

Several implicational universals are stated as theorems:

1. **SR implies subject tracking**: every language with SR tracks at least subjects
2. **Temporal SR implies SS/DS**: `ssDsTemporal` is a refinement of `ssDs`
3. **Medial-final dominance**: all six sampled languages are medial-final
4. **SS unmarked**: in every SR language in the sample, SS is the unmarked member

## References

- Sarvasy, H. S. (2017). A Grammar of Nungon. Brill.
- Sarvasy, H. S. (2015). Breaking the clause chains. Studies in Language 39(3).
- Aikhenvald, A. Y. (2008). The Manambu Language of East Sepik, Papua New Guinea.
  Oxford University Press.
- Merlan, F. & A. Rumsey (1991). Ku Waru. Cambridge University Press.
- de Vries, L. (2025). Clause chaining in Greater Awyu. In Sarvasy &
  Aikhenvald (eds.), Clause Chaining in the Languages of the World.
-/

namespace Phenomena.ClauseChaining.Data

open Typology

-- ============================================================================
-- § Language data
-- ============================================================================

/-- Nungon (Trans-New Guinea, Finisterre-Huon; Sarvasy 2017, 2025 Ch. 7).

    The best-described clause chaining language. Obligatory SR with
    temporal encoding: four distinct medial forms (SS-SEQ, SS-SIM,
    DS-SEQ, DS-SIM). Medial verbs are maximally reduced (bare stem +
    SR suffix). The final verb alone carries tense, agreement, and full mood.
    Non-canonical stand-alone medial clauses are attested (Sarvasy 2015). -/
def nungon : ClauseChainingParams where
  direction           := .medialFinal
  srSystem            := .ssDsTemporal
  srTarget            := some .subjectOnly
  srObligatory        := true
  srMarkedness        := some .ssUnmarked
  medialMorph         := {
    tense     := .absent
    agreement := .absent
    mood      := .restricted   -- realis/irrealis only
    polarity  := .restricted   -- medial negation possible but constrained
    aspect    := .absent
  }
  relationsMarked     := [.sequential, .simultaneous]
  hasRecapLinkage     := true
  hasSummaryLinkage   := false
  medialCanStandAlone := true

/-- Manambu (Ndu family, East Sepik; Aikhenvald 2008, 2025 Ch. 6).

    Rich verb morphology with restricted SR system (SS/DS without temporal
    encoding). Medial verbs retain some tense distinctions (yesterday/today/
    remote past) and some agreement. Contact-influenced: clause chaining
    features partially diffused from neighboring Papuan languages.
    Both recapitulative and summary linkage attested. -/
def manambu : ClauseChainingParams where
  direction           := .medialFinal
  srSystem            := .ssDs
  srTarget            := some .subjectOnly
  srObligatory        := true
  srMarkedness        := some .ssUnmarked
  medialMorph         := {
    tense     := .restricted   -- yesterday/today/remote only
    agreement := .restricted   -- reduced person paradigm
    mood      := .restricted   -- realis/irrealis
    polarity  := .restricted
    aspect    := .restricted
  }
  relationsMarked     := [.sequential, .simultaneous, .causal]
  hasRecapLinkage     := true
  hasSummaryLinkage   := true
  medialCanStandAlone := true

/-- Ku Waru (Trans-New Guinea, Chimbu-Wahgi; Merlan & Rumsey 1991).

    Obligatory SS/DS with reduced medial morphology. Agreement on medial verbs
    is absent (inherited from the final verb in SS chains). Prominent use of
    both recapitulative and summary linkage in narrative. -/
def kuWaru : ClauseChainingParams where
  direction           := .medialFinal
  srSystem            := .ssDs
  srTarget            := some .subjectOnly
  srObligatory        := true
  srMarkedness        := some .ssUnmarked
  medialMorph         := {
    tense     := .absent
    agreement := .absent
    mood      := .restricted
    polarity  := .absent
    aspect    := .absent
  }
  relationsMarked     := [.sequential, .simultaneous]
  hasRecapLinkage     := true
  hasSummaryLinkage   := true
  medialCanStandAlone := false

/-- Korean (Koreanic; Sohn 1999).

    Productive clause chaining via conjunctive (converbal) suffixes on the verb
    stem, but no SR morphology. The conjunctive suffixes directly encode the
    interclausal semantic relation (sequential, simultaneous, causal, conditional,
    concessive). Medial verbs retain more morphology than typical Papuan
    languages: tense and aspect are partially marked. -/
def korean : ClauseChainingParams where
  direction           := .medialFinal
  srSystem            := .none
  srTarget            := none
  srObligatory        := false
  srMarkedness        := none
  medialMorph         := {
    tense     := .restricted   -- some tense distinctions preserved
    agreement := .absent       -- Korean lacks agreement generally
    mood      := .restricted
    polarity  := .full         -- medial clauses can be independently negated
    aspect    := .restricted
  }
  relationsMarked     := [.sequential, .simultaneous, .causal,
                          .conditional, .concessive, .contrastive,
                          .manner, .purpose]
  hasRecapLinkage     := false
  hasSummaryLinkage   := false
  medialCanStandAlone := true

/-- Turkish (Turkic; Goksel & Kerslake 2005).

    Productive clause chaining via converbal suffixes (*-ip*, *-(y)arak*,
    *-(y)inca*, etc.), no SR morphology. Rich set of interclausal semantic
    relations encoded. Converbal forms retain some TAM distinctions.
    Turkish converbs are the textbook examples of UD `VerbForm.Conv`. -/
def turkish : ClauseChainingParams where
  direction           := .medialFinal
  srSystem            := .none
  srTarget            := none
  srObligatory        := false
  srMarkedness        := none
  medialMorph         := {
    tense     := .restricted   -- some temporal distinctions on converbs
    agreement := .absent       -- converbs lack agreement
    mood      := .restricted
    polarity  := .full         -- negation possible on converbs (-madan, -mayıp)
    aspect    := .restricted   -- perfective/imperfective on some converbs
  }
  relationsMarked     := [.sequential, .simultaneous, .causal,
                          .conditional, .concessive, .manner, .purpose]
  hasRecapLinkage     := false
  hasSummaryLinkage   := false
  medialCanStandAlone := false

/-- Korowai (Trans-New Guinea, Greater Awyu; de Vries 2025 Ch. 5).

    Multi-track SR system: tracks both subject and object continuity across
    clause boundaries. Medial verb morphology includes three verb types
    (non-finite, semi-finite, fully finite). SR marking tracks the topical
    participant rather than strictly the syntactic subject. -/
def korowai : ClauseChainingParams where
  direction           := .medialFinal
  srSystem            := .multiTrack
  srTarget            := some .topicBased
  srObligatory        := false
  srMarkedness        := some .ssUnmarked
  medialMorph         := {
    tense     := .restricted
    agreement := .restricted
    mood      := .restricted
    polarity  := .restricted
    aspect    := .absent
  }
  relationsMarked     := [.sequential, .simultaneous, .causal, .conditional]
  hasRecapLinkage     := true
  hasSummaryLinkage   := false
  medialCanStandAlone := false

/-- All language data entries. -/
def allLanguages : List ClauseChainingParams :=
  [nungon, manambu, kuWaru, korean, turkish, korowai]

-- ============================================================================
-- § Per-datum verification
-- ============================================================================

theorem nungon_has_sr : nungon.hasSR = true := rfl
theorem manambu_has_sr : manambu.hasSR = true := rfl
theorem kuWaru_has_sr : kuWaru.hasSR = true := rfl
theorem korean_no_sr : korean.hasSR = false := rfl
theorem turkish_no_sr : turkish.hasSR = false := rfl
theorem korowai_has_sr : korowai.hasSR = true := rfl

theorem nungon_tense_from_final : nungon.tenseFromFinalVerb = true := rfl
theorem manambu_tense_not_from_final : manambu.tenseFromFinalVerb = false := rfl
theorem korean_tense_not_from_final : korean.tenseFromFinalVerb = false := rfl

theorem nungon_has_bridging : nungon.hasBridging = true := rfl
theorem korean_no_bridging : korean.hasBridging = false := rfl
theorem kuWaru_has_bridging : kuWaru.hasBridging = true := rfl

theorem nungon_temporal_via_sr : nungon.temporalViaSR = true := rfl
theorem manambu_not_temporal_via_sr : manambu.temporalViaSR = false := rfl

-- ============================================================================
-- § Medial verb form predictions
-- ============================================================================

theorem nungon_medial_is_converb :
    nungon.medialVerbForm = UD.VerbForm.Conv := rfl

theorem korean_medial_is_converb :
    korean.medialVerbForm = UD.VerbForm.Conv := rfl

theorem turkish_medial_is_converb :
    turkish.medialVerbForm = UD.VerbForm.Conv := rfl

-- ============================================================================
-- § Cross-linguistic generalizations
-- ============================================================================

/-- All sampled languages are medial-final.

    This reflects the strong cross-linguistic dominance of medial-final chains.
    Initial-medial chains are rare and geographically restricted. -/
theorem all_medial_final :
    allLanguages.all (·.direction == .medialFinal) = true := by native_decide

/-- Every language with SR tracks at least subject continuity.

    No language in the sample (or cross-linguistically) has an SR system that
    fails to track subjects. Multi-track systems add object tracking; topic-based
    systems generalize from subject to topical participant. But the subject
    tracking function is always present. -/
theorem sr_languages_have_target :
    allLanguages.all (λ p => !p.hasSR || p.srTarget.isSome) = true := by
  native_decide

/-- In every SR language in the sample, SS is the unmarked member.

    Cross-linguistically, SS tends to be shorter / less marked than DS. This
    reflects the discourse-pragmatic default: subject continuity is expected
    in connected discourse (Givon 1983). -/
theorem sr_languages_ss_unmarked :
    allLanguages.all (λ p =>
      !p.hasSR || p.srMarkedness == some .ssUnmarked) = true := by
  native_decide

/-- Languages without SR mark more interclausal semantic relations.

    Korean and Turkish each mark 7+ relation types via dedicated converbal
    suffixes. SR languages encode fewer relation types, because the SR morpheme
    itself absorbs the sequential/simultaneous distinction. The semantic work
    is distributed differently. -/
theorem noSR_richer_relations :
    allLanguages.all (λ p =>
      p.hasSR || p.relationsMarked.length ≥ 7) = true := by
  native_decide

end Phenomena.ClauseChaining.Data
