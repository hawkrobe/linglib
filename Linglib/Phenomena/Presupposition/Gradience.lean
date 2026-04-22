import Linglib.Core.Semantics.Presupposition

/-!
# Gradient Projection in Inference Judgments
@cite{degen-tonhauser-2021} @cite{degen-tonhauser-2022}
@cite{tonhauser-beaver-roberts-simons-2018}

Theory-neutral empirical observations about gradient patterns in
presupposition projection and inference judgments.

## Core Observations

1. **Projection is gradient across predicates.** Aggregate inference judgments
   for clause-embedding predicates vary continuously — there is no categorical
   gap separating "factive" from "nonfactive" predicates in projection strength.

2. **Prior beliefs modulate projection.** Higher prior probability of the
   complement content leads to stronger projection, at both the group level
   and the individual participant level (@cite{degen-tonhauser-2021}).

3. **The gradient pattern is robust.** The by-predicate ranking of projection
   strength replicates across experiments with Spearman's r = .991
   (@cite{degen-tonhauser-2021}, Exp 1 vs Tonhauser & Degen 2020).

4. **Optionally factive predicates overlap with canonically factive ones.**
   Some "optionally factive" predicates (e.g., *inform*) project more strongly
   than some "canonically factive" predicates (e.g., *reveal*)
   (@cite{degen-tonhauser-2022}).

## Sources of Gradience

Gradience in inference judgments may arise from multiple sources:

- **Resolved (type-level) indeterminacy**: Different occasions of use resolve
  an ambiguity differently (lexical ambiguity, structural ambiguity, QUD).
  This produces gradience at the experiment level but discreteness at the
  trial level.

- **Unresolved (token-level) indeterminacy**: Uncertainty persists even after
  fixing the interpretation — vagueness, world knowledge, task effects,
  response error. This produces genuine gradience at every level.

Whether gradient projection reflects resolved or unresolved indeterminacy is
a theoretical question addressed by study files, not settled by the data alone.
-/

namespace Phenomena.Presupposition.Gradience

/-- Sources of gradience in inference judgment tasks. -/
inductive GradienceSource where
  /-- Resolved on each occasion but varying across occasions (type-level). -/
  | resolved
  /-- Persists even after fixing the interpretation (token-level). -/
  | unresolved
  deriving DecidableEq, Repr

/-- A specific application of `GradienceSource` to factivity. The
    @cite{grove-white-2025} paper frames the choice between the discrete
    (FDH) and gradient (FGH) hypotheses as a binary choice of source for
    the gradient projection observations.

    Defined as `@[reducible] def` rather than `abbrev` so the unfolding is
    explicit (mathlib convention). -/
@[reducible] def FactivityHypothesis : Type := GradienceSource

/-- The Fundamental Discreteness Hypothesis (@cite{grove-white-2025}):
    factivity is a discrete property of an expression on each occasion
    of use. Observed gradience arises from resolved indeterminacy. -/
def FactivityHypothesis.FDH : FactivityHypothesis := .resolved

/-- The Fundamental Gradience Hypothesis (@cite{grove-white-2025}):
    there is no property distinguishing factive from non-factive
    occurrences. Gradient distinctions reflect gradient inference
    contributions. -/
def FactivityHypothesis.FGH : FactivityHypothesis := .unresolved

/-- Mechanisms by which resolved indeterminacy may be cashed out.
    Catalogue from @cite{grove-white-2025} (Sect. 6, p. 10). The FDH
    is neutral among them. -/
inductive ResolvedMechanism where
  /-- Polysemy: a predicate has multiple senses, at least one factive and
      at least one nonfactive (conventionalist account, Sect. 6.1). -/
  | polysemy
  /-- Structural ambiguity: a predicate occurs in multiple structures, at
      least one implicated in triggering projection and one not. -/
  | structuralAmbiguity
  /-- Discourse sensitivity: the predicate's complement content may or may
      not be entailed by a discourse construct like the QUD
      (conversationalist account, Sect. 6.2). -/
  | discourseSensitivity
  deriving DecidableEq, Repr

/-- Subtypes of unresolved indeterminacy. -/
inductive UnresolvedSource where
  | vagueness
  | worldKnowledge
  | responseStrategy
  | responseError
  deriving DecidableEq, Repr

/-- A projection profile records how strongly a predicate's complement
    projects, separated by prior probability condition. -/
structure ProjectionProfile where
  /-- Mean certainty rating with higher-probability background fact. -/
  highPrior : Float
  /-- Mean certainty rating with lower-probability background fact. -/
  lowPrior : Float
  deriving Repr

/-- The prior belief effect: higher prior → stronger projection. -/
def ProjectionProfile.priorEffect (p : ProjectionProfile) : Float :=
  p.highPrior - p.lowPrior

/-- Prior beliefs modulate projection: the effect is positive for
    every predicate studied. This is the core finding of
    @cite{degen-tonhauser-2021}. -/
def priorBeliefModulatesProjection (profile : ProjectionProfile) : Prop :=
  profile.highPrior > profile.lowPrior

/-- A predicate's projection variability across contexts, collapsing
    over prior probability. The mean and range characterize how
    "reliably factive" a predicate is. -/
structure ProjectionVariability where
  /-- Mean projection across all contexts. -/
  mean : Float
  /-- Whether the predicate shows bimodal responses (modes near 0 and 1). -/
  bimodal : Bool
  deriving Repr

/-- The key empirical observation: no categorical gap between traditional
    classes in projection strength. Formalized as: for any threshold that
    separates "factive" from "nonfactive" by projection rating, at least
    one predicate from each traditional class falls on the wrong side. -/
structure NoCategoricalGap where
  /-- An "optionally factive" predicate that projects more strongly than
      some "canonically factive" predicate. -/
  optFactivePred : String
  canonFactivePred : String
  optFactiveRating : Float
  canonFactiveRating : Float
  overlap : optFactiveRating > canonFactiveRating

/-- Witnessed by inform (0.81) > reveal (0.70) in @cite{degen-tonhauser-2022}
    Experiment 1a (sliding scale, collapsing over facts). -/
def noCategoricalGap_witness : NoCategoricalGap :=
  { optFactivePred := "inform"
    canonFactivePred := "reveal"
    optFactiveRating := 0.81
    canonFactiveRating := 0.70
    overlap := by native_decide }

end Phenomena.Presupposition.Gradience
