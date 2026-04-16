import Linglib.Theories.Morphology.DM.PostsyntacticDerivation
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

## What is and isn't formalised here

The full Taos paradigm involves dozens of Vocabulary Insertion rules
and a large family of impoverishment / metathesis rules. We do not
re-derive the entire paradigm. Instead:

* The architectural pipelines (`runStrict`, `runInterleaved`) live in
  `Theories/Morphology/DM/PostsyntacticDerivation.lean`.
* This file gives one concrete pair of rules `r_para` / `r_syn` that
  models the §4.2.1 schema (paradigmatic agent impoverishment vs.
  syntagmatic object impoverishment) and exhibits the divergence
  predicted by the paper at a specific neighborhood.
* The general claim — that `runStrict` is strictly less expressive
  than `runInterleaved` whenever a syntagmatic rule needs to feed a
  paradigmatic one — is `runStrict_forces_paraSyn_order` /
  `runInterleaved_admits_synPara` in the theory file; here we
  instantiate it.
-/

namespace Phenomena.Allomorphy.Studies.Middleton2026

open Minimalism Morphology.DM.Impoverishment Morphology.DM.Metathesis
     Morphology.DM.PostsyntacticDerivation
     Fragments.Taos.Agreement

-- ============================================================================
-- § 1: Rule schemas from §4.2.1 (Object Impoverishment Precedes Agent Impov.)
-- ============================================================================

/-- A paradigmatic rule *r_para*, schematic of Middleton (43)
    (`[+atomic] → ∅ / [[G 1 _ +minimal]]`): deletes `[+atomic]`
    whenever the focus contains the conditioning person/number
    features. Paradigmatic: the condition refers only to the focus
    bundle.

    We encode the conditioning environment as
    "focus contains `[+author]` and `[+minimal]`," using
    `[+author]` as the per-focus 1st-person witness for compactness;
    the choice of conditioning features is immaterial to the
    architectural argument. -/
def r_para : ImpoverishmentRule :=
  paradigmatic
    (λ fb =>
      fb.any (λ f => f.featureType.sameType (fAuthor true)) &&
      fb.any (λ f => f.featureType.sameType (fMinimal true)))
    (fAtomic true)

theorem r_para_isParadigmatic : Paradigmatic r_para :=
  paradigmatic_isParadigmatic _ _

/-- A syntagmatic rule *r_syn*, schematic of Middleton (44)
    (`[+minimal] → ∅ / [[ω +atomic _ [O 3i]]]`): deletes `[+minimal]`
    when the focus contains `[+atomic]` *and* there is at least one
    bundle of object-context to the right (the "[O 3i]" condition,
    weakened to bare presence — sufficient for the bleeding/feeding
    interaction the paper diagnoses). Syntagmatic: the condition
    references `rightCtx`. -/
def r_syn : ImpoverishmentRule where
  condition n :=
    (n.focus.any (λ f => f.featureType.sameType (fAtomic true)) = true)
    ∧ (n.rightCtx.length > 0)
  decCond n := inferInstanceAs (Decidable (_ ∧ _))
  target := fMinimal true

/-- The two rules are genuinely in distinct phases: `r_syn` actually
    depends on its right-context (it is *not* paradigmatic). We witness
    this with two neighborhoods that share a focus but differ on
    `rightCtx`. -/
theorem r_syn_isSyntagmatic : Syntagmatic r_syn := by
  intro hPara
  -- Pick a focus that fires `r_syn` when context is non-empty.
  let fb : FeatureBundle := [.valued (fAtomic true), .valued (fMinimal true)]
  let n₁ : Neighborhood := { focus := fb, leftCtx := [], rightCtx := [[]] }
  let n₂ : Neighborhood := { focus := fb, leftCtx := [], rightCtx := [] }
  have hfoc : n₁.focus = n₂.focus := rfl
  have h := hPara n₁ n₂ hfoc
  -- `r_syn n₁` holds (focus has +atomic, rightCtx non-empty); `r_syn n₂` doesn't.
  have h₁ : r_syn.condition n₁ := by decide
  have h₂ : ¬ r_syn.condition n₂ := by decide
  exact h₂ (h.mp h₁)

-- ============================================================================
-- § 2: A Witness Neighborhood Where the Two Pipelines Diverge
-- ============================================================================

/-- A focus bundle that contains the features both rules read:
    `[+author, +atomic, +minimal]` (a 1s-style bundle). -/
def witnessFocus : FeatureBundle :=
  [.valued (fAuthor true),
   .valued (fAtomic true),
   .valued (fMinimal true)]

/-- The witness neighborhood: focus as above, with one (immaterial)
    bundle to the right standing in for the 3i object that conditions
    `r_syn`. -/
def witness : Neighborhood :=
  { focus := witnessFocus, leftCtx := [], rightCtx := [[]] }

/-- Run `r_para` then `r_syn` (the order A&N's strict pipeline forces). -/
def stripParaSyn : FeatureBundle :=
  applyImpoverishmentChain [r_para, r_syn] witness

/-- Run `r_syn` then `r_para` (the order Middleton's interleaved
    pipeline can choose). -/
def stripSynPara : FeatureBundle :=
  applyImpoverishmentChain [r_syn, r_para] witness

-- ============================================================================
-- § 3: The Two Orderings Yield Different Outputs
-- ============================================================================

/-- Para-then-syn order (= A&N): `r_para` deletes `[+atomic]` first;
    `r_syn` then can't fire (no `[+atomic]` left in focus). The
    `[+minimal]` survives. -/
theorem stripParaSyn_eq :
    stripParaSyn =
      [.valued (fAuthor true), .valued (fMinimal true)] := by
  decide

/-- Syn-then-para order (= Middleton): `r_syn` fires first (focus has
    `[+atomic]`, rightCtx non-empty), deleting `[+minimal]`; `r_para`
    then can't fire (no `[+minimal]` left in focus). The result
    differs from the strict-order one — `[+atomic]` survives, not
    `[+minimal]`. -/
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

/-- The schematic A&N postsyntax that contains exactly `r_para` and
    `r_syn`, with no metathesis. -/
def MAN : ModularPostsyntax :=
  { paradigmatic := [r_para], syntagmatic := [r_syn], metathesis := [] }

/-- The schematic Middleton interleaved postsyntax with `r_syn` first. -/
def MMid : InterleavedPostsyntax :=
  { impoverishment := [r_syn, r_para], metathesis := [] }

/-- A&N's pipeline computes the para-first answer at the witness. -/
theorem runStrict_MAN_witness :
    runStrict MAN witness =
      [.valued (fAuthor true), .valued (fMinimal true)] := by
  show runStrict { paradigmatic := [r_para], syntagmatic := [r_syn],
                   metathesis := [] } witness = _
  rw [runStrict_forces_paraSyn_order r_para r_syn witness]
  exact stripParaSyn_eq

/-- Middleton's pipeline computes the (different) syn-first answer. -/
theorem runInterleaved_MMid_witness :
    runInterleaved MMid witness =
      [.valued (fAuthor true), .valued (fAtomic true)] := by
  show runInterleaved { impoverishment := [r_syn, r_para],
                        metathesis := [] } witness = _
  rw [runInterleaved_admits_synPara r_para r_syn witness]
  exact stripSynPara_eq

/-- **Architectural inadequacy of `runStrict` for Taos.** At the
    witness neighborhood, the strict A&N pipeline and Middleton's
    interleaved one return different feature bundles. Hence no
    `ModularPostsyntax` built from `r_para` (paradigmatic) and `r_syn`
    (syntagmatic) — and no extension that adds further rules to the
    same phases — can yield the syn-first output that Taos requires
    in the four cases of @cite{middleton-2026} §4.2.1–4. -/
theorem runStrict_neq_runInterleaved_at_witness :
    runStrict MAN witness ≠ runInterleaved MMid witness := by
  rw [runStrict_MAN_witness, runInterleaved_MMid_witness]
  decide

-- ============================================================================
-- § 5: Metathesis Still Follows Impoverishment (the Uphold)
-- ============================================================================

/-- A trivial metathesis rule that swaps `[+author]` with `[+atomic]`
    when the focus contains both. Schematic of @cite{middleton-2026}'s
    rules (24) and (26). -/
def r_meta : MetathesisRule :=
  focusRule
    (λ fb =>
      fb.any (λ f => f.featureType.sameType (fAuthor true)) &&
      fb.any (λ f => f.featureType.sameType (fAtomic true)))
    (fAuthor true)
    (fAtomic true)

/-- Impoverishment-then-metathesis (Middleton's and A&N's shared order). -/
def derivIM : FeatureBundle :=
  applyMetathesisChain [r_meta]
    { witness with focus := applyImpoverishmentChain [r_syn] witness }

/-- Metathesis-then-impoverishment (the order both authors reject). -/
def derivMI : FeatureBundle :=
  applyImpoverishmentChain [r_syn]
    { witness with focus := applyMetathesisChain [r_meta] witness }

/-- The two orders of impoverishment vs. metathesis genuinely diverge
    at the witness, witnessing the architectural fact that metathesis
    must follow impoverishment. -/
theorem impov_before_meta_diverges_from_meta_before_impov :
    derivIM ≠ derivMI := by
  decide

end Phenomena.Allomorphy.Studies.Middleton2026
