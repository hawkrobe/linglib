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
when a syntagmatic rule must precede a paradigmatic one
(@cite{middleton-2026} §4.2.1–§4.2.4) *or* when a paradigmatic rule
must precede a syntagmatic one and one cannot guarantee the strict
block ordering (@cite{middleton-2026} §4.2.5). Together these five
cases force *interleaving*: neither a fixed para-then-syn ordering
(A&N) nor its reverse can satisfy all five witnesses simultaneously.

This file states the architectures and proves the divergence as a
self-contained existential, parametric in the rule shapes; the
Taos witnesses are in
`Phenomena/Allomorphy/Studies/Middleton2026.lean`.
-/

namespace Morphology.DM.PostsyntacticDerivation

open Minimalist Morphology.DM.Impoverishment Morphology.DM.Metathesis

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
    can derive, interleaved can derive too (with the same rules).

    Proof: `applyImpoverishmentChain_append` reduces the strict pipeline's
    two-block fold to a single fold on the concatenation. -/
theorem runStrict_eq_interleaved_paraSyn
    (M : ModularPostsyntax) (n : Neighborhood) :
    runStrict M n = runInterleaved M.toInterleaved n := by
  simp only [runStrict, runInterleaved, ModularPostsyntax.toInterleaved,
             applyImpoverishmentChain_append]

-- ============================================================================
-- § 4: Reduction Lemmas for Singleton Pipelines
-- ============================================================================

/-- A two-rule strict pipeline (one paradigmatic, one syntagmatic, no
    metathesis) reduces to applying `[p, s]` in order. This is the
    workhorse equation behind `runStrict_forces_paraSyn_order` and
    its consumers in study files. -/
@[simp] theorem runStrict_singleton (p s : ImpoverishmentRule)
    (n : Neighborhood) :
    runStrict ⟨[p], [s], []⟩ n = applyImpoverishmentChain [p, s] n := by
  simp only [runStrict, applyImpoverishmentChain, runChain,
             applyMetathesisChain, List.foldl_nil, List.foldl_cons]

/-- An interleaved pipeline with no metathesis reduces to the
    impoverishment chain. -/
@[simp] theorem runInterleaved_no_metathesis (rs : List ImpoverishmentRule)
    (n : Neighborhood) :
    runInterleaved ⟨rs, []⟩ n = applyImpoverishmentChain rs n := by
  simp only [runInterleaved, applyMetathesisChain, runChain, List.foldl_nil]

-- ============================================================================
-- § 5: The Disputed Claim: Para-before-Syn is Not Universal
-- ============================================================================

/-- **The structural inadequacy of `runStrict`.** Whenever a paradigmatic
    rule `p` and a syntagmatic rule `s` produce different outputs depending
    on whether they fire in `[s, p]` or `[p, s]` order at some neighborhood
    `n`, the strict pipeline ⟨[p], [s], []⟩ is *forced* to yield the
    `[p, s]` answer — the `[s, p]` derivation is unreachable.

    This is the formal counterpart of @cite{middleton-2026}'s argument
    that A&N's modular ordering cannot derive Taos: the four cases in
    §4.2.1–§4.2.4 require precisely the syn-before-para derivation that
    `runStrict` excludes by construction. -/
theorem runStrict_forces_paraSyn_order
    (p s : ImpoverishmentRule) (n : Neighborhood) :
    runStrict ⟨[p], [s], []⟩ n = applyImpoverishmentChain [p, s] n :=
  runStrict_singleton p s n

/-- The interleaved pipeline can deliver the syn-first derivation that
    `runStrict` cannot. -/
theorem runInterleaved_admits_synPara
    (p s : ImpoverishmentRule) (n : Neighborhood) :
    runInterleaved ⟨[s, p], []⟩ n = applyImpoverishmentChain [s, p] n :=
  runInterleaved_no_metathesis _ _

/-- **Inadequacy theorem.** If `[p, s]` and `[s, p]` give different focuses
    at `n`, then the strict pipeline ⟨[p], [s], []⟩ cannot match the
    interleaved pipeline ⟨[s, p], []⟩ at `n`. This packages
    `runStrict_forces_paraSyn_order` and `runInterleaved_admits_synPara`
    into the actual divergence claim. -/
theorem runStrict_neq_runInterleaved_of_diverges
    (p s : ImpoverishmentRule) (n : Neighborhood)
    (h : applyImpoverishmentChain [p, s] n ≠ applyImpoverishmentChain [s, p] n) :
    runStrict ⟨[p], [s], []⟩ n ≠ runInterleaved ⟨[s, p], []⟩ n := by
  rw [runStrict_singleton, runInterleaved_no_metathesis]
  exact h

-- ============================================================================
-- § 6: Metathesis Follows Impoverishment (the Upheld Claim)
-- ============================================================================

/-- A two-step pipeline that runs impoverishment then metathesis at a
    neighborhood (the order both A&N and Middleton endorse). -/
def runImpovThenMeta (rs : List ImpoverishmentRule) (ms : List MetathesisRule)
    (n : Neighborhood) : FeatureBundle :=
  applyMetathesisChain ms { n with focus := applyImpoverishmentChain rs n }

/-- The reversed two-step pipeline: metathesis first, then impoverishment
    (the order both A&N and Middleton reject — supported by Basque in §3.1
    and by Taos in §3.2 of @cite{middleton-2026}). -/
def runMetaThenImpov (rs : List ImpoverishmentRule) (ms : List MetathesisRule)
    (n : Neighborhood) : FeatureBundle :=
  applyImpoverishmentChain rs { n with focus := applyMetathesisChain ms n }

/-- **Metathesis-after-impoverishment is non-trivial.** If a single
    impoverishment rule `r` and a single metathesis rule `m` produce
    different focuses depending on order at `n`, then `runImpovThenMeta`
    and `runMetaThenImpov` differ — i.e., the architectural choice has
    empirical content. -/
theorem runImpov_neq_runMeta_of_diverges
    (r : ImpoverishmentRule) (m : MetathesisRule) (n : Neighborhood)
    (h : applyMetathesisChain [m] { n with focus := applyImpoverishment r n } ≠
         applyImpoverishment r { n with focus := applyMetathesis m n }) :
    runImpovThenMeta [r] [m] n ≠ runMetaThenImpov [r] [m] n := by
  intro heq
  apply h
  simp only [runImpovThenMeta, runMetaThenImpov, applyImpoverishmentChain,
             runChain, List.foldl_cons, List.foldl_nil] at heq
  exact heq

end Morphology.DM.PostsyntacticDerivation
