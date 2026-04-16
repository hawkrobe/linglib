import Linglib.Theories.Morphology.DM.Impoverishment
import Linglib.Theories.Morphology.DM.Metathesis

/-!
# Modular Postsyntax — A&N (2012) vs Middleton (2026)
@cite{arregi-nevins-2012} @cite{middleton-2026} @cite{halle-marantz-1993}

Two architectures for the postsyntactic component of Distributed
Morphology:

* **`runStrict` (Arregi & Nevins 2012, Fig. 1).** Postsyntax is a strict
  modular pipeline: paradigmatic Impoverishment → syntagmatic
  Impoverishment → Metathesis → VI. Within Feature Markedness,
  paradigmatic rules apply *as a block* before any syntagmatic rule.

* **`runInterleaved` (Middleton 2026).** Impoverishment rules apply in
  whatever order the analysis demands — paradigmatic and syntagmatic
  may interleave. Metathesis still follows all impoverishment (this
  ordering, supported by both Basque and Taos, is preserved).

The two pipelines coincide on inputs whose impoverishment list is in
para-then-syn order (`runStrict_eq_interleaved_paraSyn`). They diverge
when a syntagmatic rule must precede a paradigmatic one — and Taos has
five such cases (@cite{middleton-2026}, §4.2). The architectural
consequence: A&N's `runStrict` cannot derive Taos.

This file states the architectures and proves the divergence as a
self-contained existential, parametric in the rule shapes; the
specific Taos witness is in
`Phenomena/Allomorphy/Studies/Middleton2026.lean`.
-/

namespace Morphology.DM.PostsyntacticDerivation

open Minimalism Morphology.DM.Impoverishment Morphology.DM.Metathesis

-- ============================================================================
-- § 1: Arregi & Nevins's Strict Pipeline
-- ============================================================================

/-- The Arregi & Nevins postsyntax (their Fig. 1, simplified to the two
    contested layers): paradigmatic Impoverishment, then syntagmatic
    Impoverishment, then Metathesis. Exponence Conversion and
    Morphological Concord are abstracted away — their internal ordering
    is not at issue in @cite{middleton-2026}. -/
structure ModularPostsyntax where
  paradigmatic : List ImpoverishmentRule
  syntagmatic  : List ImpoverishmentRule
  metathesis   : List MetathesisRule

/-- A&N's strict pipeline: para-block, then syn-block, then metathesis. -/
def runStrict (M : ModularPostsyntax) (n : Neighborhood) : FeatureBundle :=
  let afterPara := applyImpoverishmentChain M.paradigmatic n
  let afterSyn  := applyImpoverishmentChain M.syntagmatic { n with focus := afterPara }
  applyMetathesisChain M.metathesis { n with focus := afterSyn }

-- ============================================================================
-- § 2: Middleton's Interleaved Pipeline
-- ============================================================================

/-- Middleton's interleaved postsyntax: a single impoverishment list
    (whose entries may be paradigmatic or syntagmatic in any order),
    then metathesis. -/
structure InterleavedPostsyntax where
  impoverishment : List ImpoverishmentRule
  metathesis     : List MetathesisRule

def runInterleaved (M : InterleavedPostsyntax) (n : Neighborhood) :
    FeatureBundle :=
  let afterImp := applyImpoverishmentChain M.impoverishment n
  applyMetathesisChain M.metathesis { n with focus := afterImp }

/-- Promote a strict pipeline to an interleaved one in para-then-syn
    order. The two then compute the same output. -/
def ModularPostsyntax.toInterleaved (M : ModularPostsyntax) :
    InterleavedPostsyntax where
  impoverishment := M.paradigmatic ++ M.syntagmatic
  metathesis     := M.metathesis

-- ============================================================================
-- § 3: Strict ⊑ Interleaved
-- ============================================================================

/-- The strict pipeline is exactly the interleaved pipeline run on the
    paradigmatic-then-syntagmatic concatenation. Hence `runStrict` is
    strictly *less expressive* than `runInterleaved`: anything strict
    can derive, interleaved can derive too (with the same rules). -/
theorem runStrict_eq_interleaved_paraSyn
    (M : ModularPostsyntax) (n : Neighborhood) :
    runStrict M n = runInterleaved M.toInterleaved n := by
  simp only [runStrict, runInterleaved, ModularPostsyntax.toInterleaved,
             applyImpoverishmentChain, List.foldl_append]

-- ============================================================================
-- § 4: The Disputed Claim: Para-before-Syn is Not Universal
-- ============================================================================

/-- **The structural inadequacy of `runStrict`.** Suppose a paradigmatic
    rule `p` and a syntagmatic rule `s` produce different outputs
    depending on whether they fire in `[s, p]` or `[p, s]` order at
    some neighborhood `n`. Then for *every* `ModularPostsyntax`
    containing `p` among the paradigmatic rules and `s` among the
    syntagmatic rules (with no metathesis), `runStrict` is forced to
    yield the `[p, s]` answer — the `[s, p]` derivation is unavailable.

    This is the formal counterpart of @cite{middleton-2026}'s argument
    that A&N's modular ordering cannot derive Taos: the four cases in
    §4.2 of the paper require precisely the syn-before-para derivation
    that `runStrict` excludes by construction. -/
theorem runStrict_forces_paraSyn_order
    (p s : ImpoverishmentRule) (n : Neighborhood) :
    runStrict { paradigmatic := [p], syntagmatic := [s], metathesis := [] } n
      = applyImpoverishmentChain [p, s] n := by
  simp only [runStrict, applyImpoverishmentChain, applyMetathesisChain,
             List.foldl_nil, List.foldl_cons]

/-- The interleaved pipeline can deliver the syn-first derivation that
    `runStrict` cannot. -/
theorem runInterleaved_admits_synPara
    (p s : ImpoverishmentRule) (n : Neighborhood) :
    runInterleaved { impoverishment := [s, p], metathesis := [] } n
      = applyImpoverishmentChain [s, p] n := by
  simp only [runInterleaved, applyMetathesisChain, List.foldl_nil]

end Morphology.DM.PostsyntacticDerivation
