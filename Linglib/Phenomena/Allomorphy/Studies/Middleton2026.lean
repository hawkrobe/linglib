import Linglib.Theories.Morphology.DM.PostsyntacticDerivation
import Linglib.Theories.Morphology.DM.VocabularyInsertion
import Linglib.Fragments.Taos.Agreement

/-!
# Middleton (2026) — Ordering of Impoverishment Rules in Taos
@cite{middleton-2026} @cite{arregi-nevins-2012} @cite{halle-marantz-1993}
@cite{harbour-2014} @cite{harbour-2016} @cite{kontak-kunkel-1987}
@cite{watkins-1984} @cite{harbour-middleton-2026}

This file formalises the architectural argument of @cite{middleton-2026}.
Working within Distributed Morphology (@cite{halle-marantz-1993}),
@cite{arregi-nevins-2012} propose a strict modular postsyntax in
which paradigmatic Impoverishment applies *as a block* before
syntagmatic Impoverishment, and Metathesis follows all
Impoverishment. Middleton shows from Taos verbal agreement that the
second claim survives but the first does not: paradigmatic and
syntagmatic Impoverishment must be allowed to interleave.

## Scope

The full Taos paradigm involves dozens of Vocabulary Insertion rules
and a large family of impoverishment / metathesis rules. We do not
re-derive the entire paradigm. What lives here:

* The architectural pipelines (`runStrict`, `runInterleaved`) live in
  `Theories/Morphology/DM/PostsyntacticDerivation.lean`.
* This file gives one **schematic** pair of rules
  `paraAtomicRule` / `synMinimalRule` that exhibits the divergence
  predicted by the paper at a real-shaped Taos witness neighborhood.
  The conditioning features (`[+author]`, `[+atomic]`, `[+minimal]`)
  are drawn from the Harbour decomposition the paper uses, but the
  rules themselves are not literal transcriptions of paper rules —
  they are minimal witnesses to the para-vs-syn ordering interaction
  in @cite{middleton-2026} §4.2.1–§4.2.4.
* The general claim — that `runStrict` is strictly less expressive
  than `runInterleaved` whenever a syntagmatic rule needs to feed a
  paradigmatic one — is `runStrict_forces_paraSyn_order` /
  `runInterleaved_admits_synPara` in the theory file; here we
  instantiate it on the witness.
* §6 demonstrates how the postsyntactic output feeds Vocabulary
  Insertion (Subset Principle, @cite{halle-marantz-1993}), again
  schematically.

What is **not** modeled:

* The full Taos paradigm and the literal rule statements of
  @cite{middleton-2026} (rule numbers and conditioning environments
  vary across the four §4.2 cases).
* Harbour's Reciprocal Containment constraints on feature bundles.
* Real Taos VI competition — only enough VIs to demonstrate the
  pipeline.
-/

namespace Middleton2026

open Minimalism Morphology.DM.Impoverishment Morphology.DM.Metathesis
     Morphology.DM.PostsyntacticDerivation Morphology.DM.VI
     Fragments.Taos.Agreement

-- ============================================================================
-- § 1: Two Schematic Rules in Distinct Phases
-- ============================================================================

/-- A **paradigmatic** rule: deletes `[+atomic]` whenever the focus
    contains both `[+author]` and `[+minimal]`. The condition refers
    only to the focus, so the rule is paradigmatic by construction
    (`paradigmatic_isParadigmatic`).

    This is a minimal stand-in for the paradigmatic rules involved in
    @cite{middleton-2026} §4.2.1–§4.2.4 — it is not a transcription of
    any specific paper rule. -/
def paraAtomicRule : ImpoverishmentRule :=
  paradigmatic
    (λ fb =>
      fb.any (λ f => f.featureType.sameType (fAuthor true)) &&
      fb.any (λ f => f.featureType.sameType (fMinimal true)))
    (fAtomic true)

theorem paraAtomicRule_isParadigmatic : Paradigmatic paraAtomicRule :=
  paradigmatic_isParadigmatic _ _

/-- A **syntagmatic** rule: deletes `[+minimal]` when the focus
    contains `[+atomic]` *and* there is at least one bundle of
    object-context to the right (the schematic `[O 3i]` condition,
    weakened to bare presence — sufficient for the bleeding/feeding
    interaction the paper diagnoses). The dependence on `rightCtx`
    is what makes the rule syntagmatic, and `synMinimalRule_isSyntagmatic`
    proves it. -/
def synMinimalRule : ImpoverishmentRule where
  condition n :=
    (n.focus.any (λ f => f.featureType.sameType (fAtomic true)) = true)
    ∧ (n.rightCtx.length > 0)
  decCond _ := inferInstance
  target := fMinimal true

/-- The two rules are genuinely in distinct phases: `synMinimalRule`
    actually depends on its right-context (it is *not* paradigmatic).
    Witness: two neighborhoods that share a focus but differ on
    `rightCtx`. -/
theorem synMinimalRule_isSyntagmatic : Syntagmatic synMinimalRule := by
  intro hPara
  let fb : FeatureBundle := [.valued (fAtomic true), .valued (fMinimal true)]
  let n₁ : Neighborhood :=
    { focus := fb, leftCtx := [], rightCtx := [argBundle person3 numSg] }
  let n₂ : Neighborhood := { focus := fb, leftCtx := [], rightCtx := [] }
  have hfoc : n₁.focus = n₂.focus := rfl
  have h := hPara n₁ n₂ hfoc
  have h₁ : synMinimalRule.condition n₁ := by decide
  have h₂ : ¬ synMinimalRule.condition n₂ := by decide
  exact h₂ (h.mp h₁)

-- ============================================================================
-- § 2: A Real-Shaped Taos Witness
-- ============================================================================

/-- Witness focus: a 1s-style bundle `[+author, +atomic, +minimal]`
    (suppressing `[+participant]`, which is irrelevant to either rule). -/
def witnessFocus : FeatureBundle :=
  [.valued (fAuthor true),
   .valued (fAtomic true),
   .valued (fMinimal true)]

/-- Witness neighborhood: the 1s-style focus, with a real 3s
    bundle to the right standing in for the Taos object slot
    that conditions `synMinimalRule`. -/
def witness : Neighborhood :=
  { focus := witnessFocus,
    leftCtx := [],
    rightCtx := [argBundle person3 numSg] }

/-- Run para-then-syn (the order A&N's strict pipeline forces). -/
def stripParaSyn : FeatureBundle :=
  applyImpoverishmentChain [paraAtomicRule, synMinimalRule] witness

/-- Run syn-then-para (the order Middleton's interleaved pipeline can
    choose). -/
def stripSynPara : FeatureBundle :=
  applyImpoverishmentChain [synMinimalRule, paraAtomicRule] witness

-- ============================================================================
-- § 3: The Two Orderings Yield Different Outputs
-- ============================================================================

/-- Para-then-syn (= A&N): `paraAtomicRule` deletes `[+atomic]` first;
    `synMinimalRule` then can't fire (no `[+atomic]` left in focus).
    The `[+minimal]` survives. -/
theorem stripParaSyn_eq :
    stripParaSyn =
      [.valued (fAuthor true), .valued (fMinimal true)] := by
  decide

/-- Syn-then-para (= Middleton): `synMinimalRule` fires first (focus
    has `[+atomic]`, rightCtx non-empty), deleting `[+minimal]`;
    `paraAtomicRule` then can't fire (no `[+minimal]` left in focus).
    The `[+atomic]` survives instead. -/
theorem stripSynPara_eq :
    stripSynPara =
      [.valued (fAuthor true), .valued (fAtomic true)] := by
  decide

/-- The two orders produce different feature bundles at this
    neighborhood. -/
theorem orderings_diverge : stripParaSyn ≠ stripSynPara := by
  rw [stripParaSyn_eq, stripSynPara_eq]
  decide

-- ============================================================================
-- § 4: A&N's Strict Pipeline Cannot Reach the Syn-First Output
-- ============================================================================

/-- The schematic A&N postsyntax that contains exactly `paraAtomicRule`
    in the paradigmatic phase and `synMinimalRule` in the syntagmatic
    phase, with no metathesis. -/
def arregiNevinsPostsyntax : ModularPostsyntax :=
  { paradigmatic := [paraAtomicRule]
    syntagmatic  := [synMinimalRule]
    metathesis   := [] }

/-- The schematic Middleton interleaved postsyntax, with the
    syntagmatic rule scheduled first — the order required by the
    §4.2.1–§4.2.4 Taos cases. -/
def middletonPostsyntax : InterleavedPostsyntax :=
  { impoverishment := [synMinimalRule, paraAtomicRule]
    metathesis     := [] }

/-- A&N's pipeline computes the para-first answer at the witness. -/
theorem arregiNevins_witness :
    runStrict arregiNevinsPostsyntax witness =
      [.valued (fAuthor true), .valued (fMinimal true)] := by
  show runStrict { paradigmatic := [paraAtomicRule]
                   syntagmatic := [synMinimalRule]
                   metathesis := [] } witness = _
  rw [runStrict_forces_paraSyn_order paraAtomicRule synMinimalRule witness]
  exact stripParaSyn_eq

/-- Middleton's pipeline computes the (different) syn-first answer. -/
theorem middleton_witness :
    runInterleaved middletonPostsyntax witness =
      [.valued (fAuthor true), .valued (fAtomic true)] := by
  show runInterleaved { impoverishment := [synMinimalRule, paraAtomicRule]
                        metathesis := [] } witness = _
  rw [runInterleaved_admits_synPara paraAtomicRule synMinimalRule witness]
  exact stripSynPara_eq

/-- **Architectural inadequacy of `runStrict` for Taos.** At the
    witness neighborhood, the strict A&N pipeline and Middleton's
    interleaved one return different feature bundles. Hence no
    `ModularPostsyntax` built from `paraAtomicRule` (paradigmatic) and
    `synMinimalRule` (syntagmatic) — and no extension that adds
    further rules to the same phases — can yield the syn-first output
    that Taos requires in @cite{middleton-2026} §4.2.1–§4.2.4. -/
theorem arregiNevins_neq_middleton_at_witness :
    runStrict arregiNevinsPostsyntax witness ≠
      runInterleaved middletonPostsyntax witness := by
  rw [arregiNevins_witness, middleton_witness]
  decide

-- ============================================================================
-- § 5: Metathesis Still Follows Impoverishment (the Uphold)
-- ============================================================================

/-- A metathesis rule that swaps `[+author]` with `[+atomic]` when the
    focus contains all three of `[+author]`, `[+atomic]`, `[+minimal]`.
    Schematic of @cite{middleton-2026}'s metathesis rules: a metathesis
    triggered in the presence of a particular number feature. The
    dependence on `[+minimal]` is what couples this rule to
    `synMinimalRule` (which deletes `[+minimal]`), so that the IM/MI
    orders diverge — the empirically motivated witness of "metathesis
    after impoverishment, not before." -/
def authorAtomicMetathesis : MetathesisRule :=
  focusRule
    (λ fb =>
      fb.any (λ f => f.featureType.sameType (fAuthor true)) &&
      fb.any (λ f => f.featureType.sameType (fAtomic true)) &&
      fb.any (λ f => f.featureType.sameType (fMinimal true)))
    (fAuthor true)
    (fAtomic true)

/-- Impoverishment-then-metathesis (Middleton's and A&N's shared
    order). -/
def derivIM : FeatureBundle :=
  applyMetathesisChain [authorAtomicMetathesis]
    { witness with focus := applyImpoverishmentChain [synMinimalRule] witness }

/-- Metathesis-then-impoverishment (the order both authors reject). -/
def derivMI : FeatureBundle :=
  applyImpoverishmentChain [synMinimalRule]
    { witness with focus := applyMetathesisChain [authorAtomicMetathesis] witness }

/-- The two orders of impoverishment vs. metathesis genuinely diverge
    at the witness, witnessing the architectural fact that metathesis
    must follow impoverishment. -/
theorem impov_before_meta_diverges_from_meta_before_impov :
    derivIM ≠ derivMI := by
  decide

-- ============================================================================
-- § 6: Postsyntax Feeds Vocabulary Insertion
-- ============================================================================

/-- The post-postsyntactic focus bundle from A&N's strict pipeline at
    the witness — extracted as a top-level def so it is the input to
    Vocabulary Insertion below. -/
def arregiNevinsOutput : FeatureBundle :=
  runStrict arregiNevinsPostsyntax witness

/-- The post-postsyntactic focus bundle from Middleton's interleaved
    pipeline at the witness. -/
def middletonOutput : FeatureBundle :=
  runInterleaved middletonPostsyntax witness

/-- A small schematic Vocabulary Item set keyed on `FeatureVal`. The
    Subset Principle (@cite{halle-marantz-1993}) selects the longest
    matching entry. We use `Morpheme.surface` for the exponents to
    keep the connection to the Taos morpheme inventory in the
    Fragment. -/
def viSet : List (FeatureVI FeatureVal String) :=
  [ -- specific: 1st-person + minimal (surfaces with `n` per @cite{middleton-2026} rule 21)
    ⟨[fAuthor true, fMinimal true], Morpheme.n.surface⟩
  , -- specific: 1st-person + atomic
    ⟨[fAuthor true, fAtomic true], Morpheme.o.surface⟩
  , -- elsewhere: empty feature spec, matches anything
    ⟨[], Morpheme.ô.surface⟩ ]

/-- A&N's output feeds VI as `[+author, +minimal]`; the Subset
    Principle selects the `[+author, +minimal]` entry over the
    elsewhere `ô`. Surface form: `n`. -/
theorem arregiNevinsOutput_inserts_n :
    subsetPrinciple viSet (arregiNevinsOutput.map GramFeature.featureType) =
      some Morpheme.n.surface := by
  decide

/-- Middleton's output feeds VI as `[+author, +atomic]`; the Subset
    Principle selects the `[+author, +atomic]` entry. Surface form:
    `o`. The two architectures predict *different surface forms* at
    the same input — the empirical bite of the architectural
    divergence. -/
theorem middletonOutput_inserts_o :
    subsetPrinciple viSet (middletonOutput.map GramFeature.featureType) =
      some Morpheme.o.surface := by
  decide

/-- The architectural divergence shows up at the level of surface
    exponents, not just feature bundles: the same input neighborhood
    yields different morphemes under the two pipelines. -/
theorem arregiNevins_vs_middleton_surface :
    subsetPrinciple viSet (arregiNevinsOutput.map GramFeature.featureType) ≠
      subsetPrinciple viSet (middletonOutput.map GramFeature.featureType) := by
  rw [arregiNevinsOutput_inserts_n, middletonOutput_inserts_o]
  decide

end Middleton2026
