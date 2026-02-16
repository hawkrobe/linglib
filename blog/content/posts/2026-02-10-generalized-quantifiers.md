---
title: "Generalized Quantifiers as a Case Study in Cross-Module Verification"
date: 2026-02-10
summary: "How Barwise & Cooper's generalized quantifier theory threads through all three layers of Linglib — from abstract properties to lexical entries to scalar implicature predictions — and what the formalization reveals about the convergence of independent characterizations."
tags: ["quantifiers", "GQ", "Barwise-Cooper", "formalization", "RSA", "architecture"]
---

## Introduction

Scalar implicature — the inference from "some of the students passed" to "not all of them did" — is one of the most studied phenomena in pragmatics. Deriving this inference requires infrastructure that spans multiple theoretical modules: a semantics for *some* (existential quantification over the restrictor-scope intersection), a semantics for *all* (universal quantification), an alternative relation connecting the two (the Horn scale ⟨some, all⟩), and a pragmatic reasoning engine that exploits the alternative to strengthen the literal meaning. These four modules are tightly coupled, and the couplings cross the semantics-pragmatics boundary.

This cross-module dependency structure is precisely what Linglib's three-layer architecture is designed to make explicit and machine-checkable. This post uses generalized quantifier (GQ) theory as a case study, tracing the dependency chain from Barwise and Cooper's (1981) abstract GQ properties through concrete denotations and lexical entries to RSA implicature predictions. The case study illustrates both the mechanics of the architecture and the kind of convergence results that formalization makes visible.

## Abstract properties (Core layer)

Barwise and Cooper's insight was that natural language determiners — *every*, *some*, *no*, *most*, *few* — share a common semantic type: each takes two properties (a restrictor and a scope) and returns a truth value. In Lean:

```lean
abbrev GQ (α : Type*) := (α → Bool) → (α → Bool) → Bool
```

The space of logically possible GQs is large — any function from two sets to a truth value qualifies — but natural languages use only a small corner of it. Barwise and Cooper identified three properties that constrain the attested region: *conservativity* ($Q(A,B) = Q(A, A \cap B)$: only the part of B overlapping with A matters), *quantity* (invariance under domain permutations), and *monotonicity* (preservation of truth under subset or superset operations on the arguments). These are empirical generalizations about human languages, not logical necessities.

In Linglib, these properties live in `Core/Quantification.lean`, defined as predicates over any function of the GQ type. The Core layer also defines the algebraic operations relating quantifiers to each other: outer negation ($\neg Q(A,B)$), inner negation ($Q(A, \neg B)$), and the dual ($\check{Q} = \neg Q(A, \neg B)$). These operations interact with conservativity in predictable ways — if $Q$ is conservative, so are its negations and dual — and the interactions are proved once, abstractly, rather than re-derived for each concrete quantifier.

One theorem at this layer is especially consequential for downstream work: `conserv_symm_iff_int` establishes that a conservative quantifier is symmetric if and only if it satisfies the intersection condition (its truth value depends only on $A \cap B$). This is the formal basis for the weak/strong distinction — *some* is symmetric and hence weak; *every* is not symmetric and hence strong — which predicts definiteness effects, *there*-insertion, and related phenomena. A single abstract theorem, stated once in the Core layer, does work across multiple empirical domains.

## Concrete denotations (TruthConditional layer)

`TruthConditional/Determiner/Quantifier.lean` defines the denotations — `every_sem`, `some_sem`, `no_sem`, `most_sem` — and proves they satisfy the Core properties. The proofs use a `FiniteModel` class with a computable domain, so the verifications are computational: `every_conservative` establishes that for any finite model, $⟦\text{every}⟧(A,B) = ⟦\text{every}⟧(A, A \cap B)$ by exhaustive case analysis over model elements.

At this layer, the semantic universals become theorems (for the implemented denotations): `every_sem` is conservative, quantity-invariant, and monotone; `some_sem` is conservative, symmetric, and upward-monotone. The concrete layer also establishes duality relationships: `innerNeg(every) = no`, `dualQ(every) = some`. These are consequences of the denotations, not definitions, verified by the type checker.

The file includes a non-conservative counterexample — a GQ defined as $|A| > |B|$, which demonstrably violates conservativity — establishing that the property is non-trivial. Natural languages could in principle have determiners of this form.

## Lexical entries and RSA domains (Fragment layer)

`Fragments/English/Determiners.lean` assigns each English determiner a `QuantifierEntry` specifying its force (universal, existential, negative, proportional), monotonicity class, strength, and threshold parameters for proportional semantics. The Fragment layer also defines `QuantityWord`, a six-word scale ($\text{none} < \text{few} < \text{some} < \text{half} < \text{most} < \text{all}$) used in RSA scalar implicature models. Each `QuantityWord` maps back to a `QuantifierEntry`, which maps back to the GQ denotations in the layer below. Bridge theorems verify that the monotonicity field of the lexical entry agrees with the monotonicity proved for the corresponding denotation.

This is where the dependency chain reaches the pragmatics. `RSA/Domains/Quantities.lean` defines parameterized quantity domains — worlds indexed by how many entities have a property (0 through $n$), utterances drawn from the `QuantityWord` scale, and meaning functions derived from the Fragment entries. The literal listener L₀ updates a uniform prior on the utterance's literal meaning; the pragmatic speaker S₁ chooses utterances to be informative; the pragmatic listener L₁ reasons about the speaker's choice.

## The full dependency chain

The scalar implicature of *some* can be traced through all three layers:

1. **Core**: `Conservative` and `ScopeUpwardMono` defined as abstract GQ properties. The ⟨some, all⟩ Horn scale is defined in `Core/HornScale.lean`.

2. **TruthConditional**: `some_sem` defined as existential quantification, proved conservative and upward-monotone. `every_sem` defined as universal quantification. The entailment `every ⊨ some` follows from the denotations.

3. **Fragments**: `QuantityWord.some_` and `QuantityWord.all` map to these denotations. The meaning function `meaning n .some_ w = (w.val ≥ 1)` is the lower-bounded (weak) reading — true whenever at least one entity has the property, including the case where all do.

4. **RSA**: L₀ hears "some" and assigns equal probability to all worlds where at least one entity qualifies (including the world where all qualify). S₁, choosing between "some" and "all," prefers "all" when all qualify (it is more informative). L₁ reasons: if the speaker chose "some" over "all," the all-world is less likely. Result: *some* is strengthened to *some but not all*.

5. **Phenomena**: `Phenomena/ScalarImplicatures/` records that adult English speakers reliably draw this inference, and verification theorems confirm that the RSA model's predictions match the behavioral data.

At no step does the RSA model stipulate a meaning function. The literal semantics of "some" derives from the compositional semantics via the Fragment layer. If `some_sem` were changed to a bilateral meaning (some but not all), the RSA model would automatically inherit the change, the scalar implicature would disappear (L₁ would have nothing to strengthen), and the bridge theorem against the Phenomena data would fail. The grounding theorem `some_meaning_from_montague` makes this dependency explicit.

## Knowledge and quality

The dependency chain becomes more interesting when extended to speaker knowledge. Goodman and Stuhlmuller (2013) showed that scalar implicatures are sensitive to the listener's beliefs about what the speaker knows. If the speaker has observed only one of three students' exams, the listener should not draw the "not all" inference — the speaker may not know whether all passed.

In Linglib, this is modeled with a quality-filtered pragmatic speaker. The speaker's utility includes a log-probability term $\ln P_{\text{lex}}(u|w)$, where $P_{\text{lex}}$ is the literal truth of the utterance at the speaker's believed worlds. When $\ln(0) = -\infty$ — the utterance is false at some world the speaker considers possible — the speaker's probability of choosing that utterance drops to zero. An uncertain speaker who has not seen all the exams cannot say "all," not because of a Gricean maxim, but because "all" is literally false at some worlds in her belief state. The listener, reasoning about this constraint, correctly infers uncertainty rather than "not all."

The quality filter operates on the same GQ denotations that the basic model uses. The knowledge-sensitivity falls out of the interaction between the denotations and the belief-state machinery, without additional stipulation. Changing the denotations changes the knowledge predictions.

## Leveraging Mathlib

GQ monotonicity and polarity (in the Ladusaw/Fauconnier sense) are the same concept — a function that preserves entailment direction. The formalization makes this identification literal: `scopeUpMono_iff_monotone` proves that `ScopeUpwardMono q` is equivalent to Mathlib's `Monotone (q R)`, and `Polarity.lean` defines `IsUpwardEntailing` as `Monotone`. Once these are connected, Mathlib's library of composition lemmas transfers directly.

The polarity composition table — UE∘DE = DE, DE∘DE = UE, and so on — follows from four applications of `Monotone.comp`, `Antitone.comp_antitone`, and their siblings. The Montagovian individual $I_a = \{P : a \in P\}$ is a principal ultrafilter; `individual_upward_closed` and `individual_meet_closed` are the ultrafilter axioms. GQ meet and join (`gqMeet`, `gqJoin`) form a Boolean algebra. These identifications are individually straightforward, but they guarantee that the linguistic definitions are consistent with the mathematical structures they instantiate, and they provide the full library of existing lemmas about those structures for free.

## Convergence of three characterizations of weak determiners

The formalization reveals a convergence result that is worth stating explicitly. The weak/strong distinction for determiners has three independent characterizations from three different theoretical traditions:

**Symmetry** (Peters and Westerståhl). A conservative quantifier is weak iff it is symmetric: $Q(A,B) = Q(B,A)$. The theorem `conserv_symm_iff_int` proves that under conservativity, symmetry is equivalent to the intersection condition.

**Existential property** (Keenan and Stavi 1986). A quantifier is weak iff it satisfies the existential property: $Q(A,B) = Q(A \cap B, \text{everything})$. The restrictor-scope pair can be compressed to just the intersection.

**Persistence** (Barwise and Cooper). A quantifier is weak iff it is restrictor-upward-monotone: if $A \subseteq A'$ and $Q(A,B)$, then $Q(A',B)$.

Each characterization involves different formal machinery. In Linglib, all three are verified for the concrete denotations: `some_symmetric`, `some_existential`, and `some_restrictor_up` all hold; `every_not_symmetric`, `every_not_existential`, and `every_restrictor_down` are their mirror images. The equivalences (under conservativity) are proved at the abstract level, so that establishing any one of the three properties for a new determiner immediately yields the other two. "Weak" is not a primitive category — it is a point where three independent properties converge, and the convergence is a theorem.

## What the architecture buys

The three-layer separation enforces a distinction between formal results and empirical claims that is easy to blur in informal exposition. That `every_sem` is conservative is a theorem — it follows from the definition. That all attested natural language determiners are conservative is an empirical observation, recorded in `Phenomena/Quantification/Universals.lean`. These are different kinds of claims, and the architecture locates them in different places: proofs in `TruthConditional/`, data in `Phenomena/`, connections mediated by `Fragments/`.

When the formalization reveals that three theoretical traditions — GQ theory, polarity, and abstract order theory — are provably the same structure, or that three independent characterizations of weak determiners converge to the same class, it is doing something that informal exposition cannot: turning implicit connections into explicit theorems and making the dependency structure of the field machine-checkable.
