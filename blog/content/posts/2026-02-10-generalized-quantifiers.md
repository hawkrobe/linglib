---
title: "Generalized Quantifiers as a Case Study"
date: 2026-02-10
summary: "How Barwise & Cooper's generalized quantifier theory threads through all three layers of Linglib — from abstract properties to lexical entries to scalar implicature predictions."
tags: ["quantifiers", "GQ", "Barwise-Cooper", "formalization", "RSA", "architecture"]
---

"Some of the students passed the exam." Did all of them pass? Probably not — if they had, the speaker would have said "all." This is a scalar implicature, and it is one of the most studied phenomena in pragmatics. But notice the infrastructure required to derive it. You need a semantics for *some* (existential quantification over the restrictor-scope intersection). You need a semantics for *all* (universal quantification). You need an alternative relation connecting the two (the Horn scale ⟨some, all⟩). And you need a pragmatic reasoning engine — whether neo-Gricean or RSA — that exploits the alternative to strengthen the literal meaning. Four modules, tightly coupled, spanning semantics and pragmatics.

This is exactly the kind of cross-module dependency that Linglib is designed to make explicit. In this post, I want to use generalized quantifier theory as a case study for how the library's three-layer architecture works in practice. Barwise and Cooper's (1981) GQ framework is a natural starting point: it provides the semantic foundation that everything downstream depends on, and tracing the dependency chain from abstract GQ properties all the way to RSA implicature predictions illustrates why the layered design matters.

## What a generalized quantifier is

Barwise and Cooper's insight was that natural language determiners — *every*, *some*, *no*, *most*, *few* — all have the same semantic type. Each one takes two properties (a restrictor and a scope) and returns a truth value. In Lean:

```lean
abbrev GQ (α : Type*) := (α → Bool) → (α → Bool) → Bool
```

"Every student passed" is `⟦every⟧ student passed`, where `student` and `passed` are characteristic functions. This is Montague's `(e→t) → ((e→t) → t)` in type-theoretic clothing. The move is simple but powerful: once you have determiners as functions of this type, you can study their properties algebraically — asking which logical constraints they satisfy, how they compose, and what operations relate them to each other.

The space of logically possible GQs is enormous. Any function from two sets to a truth value qualifies. But natural languages use only a tiny corner of this space, and Barwise and Cooper conjectured that three properties carve out the relevant region: *conservativity* (`Q(A,B) = Q(A, A∩B)` — only the part of B that overlaps with A matters), *quantity* (the denotation is invariant under permutations of the domain), and *monotonicity* (the truth value is preserved under subset or superset operations on the arguments). These semantic universals are empirical claims about human languages, not logical necessities, and they raise a question that the field has been working on ever since: why these constraints?

## Layer 1: abstract properties

In Linglib, the GQ properties live in `Core/Quantification.lean`, which is deliberately model-agnostic. It defines conservativity, monotonicity (upward and downward, for both restrictor and scope), symmetry, duality, and strength — all as predicates over any function of the GQ type. No model infrastructure, no specific quantifiers, no language-particular data. If you have a function `(α → Bool) → (α → Bool) → Bool`, you can ask whether it's conservative. The definitions are purely logical.

This layer also defines the operations that relate quantifiers to each other. Outer negation (`¬Q(A,B)`) and inner negation (`Q(A, ¬B)`) reverse monotonicity in predictable ways. The *dual* of a quantifier (`Q̌ = ¬Q(A, ¬B)`) is involutive: the dual of *every* is *some*, and the dual of *some* is *every*. These operations interact with conservativity — if `Q` is conservative, so are its negations and dual — and the interaction is worth proving once, abstractly, rather than re-deriving for each concrete quantifier.

One theorem here is especially important for connecting GQ theory to the rest of linguistics: `conserv_symm_iff_int`, which establishes that a conservative quantifier is symmetric if and only if it satisfies the intersection condition (its truth value depends only on `A ∩ B`). This is the formal basis for Barwise and Cooper's weak/strong distinction — *some* is symmetric and hence weak; *every* is not symmetric and hence strong — which in turn predicts definiteness effects, *there*-insertion, and related phenomena. A single abstract theorem, stated once in the Core layer, does work across multiple empirical domains.

## Layer 2: concrete denotations

`TruthConditional/Determiner/Quantifier.lean` defines the actual denotations — `every_sem`, `some_sem`, `no_sem`, `most_sem` — and proves they satisfy the Core properties. The proofs use a `FiniteModel` class with a computable domain, so the verifications are computational: `every_conservative` establishes that for any finite model, `⟦every⟧(A,B) = ⟦every⟧(A, A∩B)` by exhaustive case analysis over model elements.

This is where the three semantic universals become theorems rather than conjectures (for our denotations, at least). `every_sem` is conservative, quantity-invariant, and monotone — proved. `some_sem` is conservative, symmetric, and upward-monotone — proved. The concrete layer also establishes duality relationships: `innerNeg(every) = no`, `dualQ(every) = some`. These aren't definitions; they're consequences of the denotations, verified by the type checker.

The file also includes a non-conservative counterexample — a GQ defined as `|A| > |B|`, which demonstrably violates conservativity — showing that the property is non-trivial. Natural languages could, in principle, have determiners like this. They don't, and that's the empirical puzzle.

## Layer 3: lexical entries and RSA domains

`Fragments/English/Determiners.lean` is the lexical layer. Each English determiner gets a `QuantifierEntry` specifying its force (universal, existential, negative, proportional), monotonicity class, strength, and a threshold parameter for proportional semantics. There are entries for *none*, *few*, *some*, *half*, *most*, *all*, *every*, *each*, *many*, *both*, *neither*, plus numerical determiners (*at least n*, *at most n*, *exactly n*).

The Fragment layer also defines `QuantityWord`, a six-word scale (`none < few < some < half < most < all`) used in RSA scalar implicature models. Each `QuantityWord` maps back to a `QuantifierEntry`, which maps back to the GQ denotations in the layer below. Bridge theorems verify that the monotonicity field of the lexical entry agrees with the monotonicity proved for the corresponding denotation. If you change `some_sem`'s denotation so that it's no longer upward-monotone, the bridge theorem breaks.

This is where the chain reaches RSA. `RSA/Domains/Quantities.lean` defines parameterized quantity domains — worlds indexed by how many entities have a property (0 through *n*), utterances drawn from the `QuantityWord` scale, and meaning functions derived from the Fragment entries. The RSA agents (L₀, S₁, L₁) operate over these domains. The literal listener L₀ updates a uniform prior on the utterance's literal meaning. The pragmatic speaker S₁ chooses utterances to be informative. The pragmatic listener L₁ reasons about the speaker's choice.

## The full chain: from conservativity to "some but not all"

Here is the dependency chain for the scalar implicature of *some*, traced through all three layers:

1. **Core**: `Conservative` and `ScopeUpwardMono` defined as abstract GQ properties. The ⟨some, all⟩ Horn scale is defined in `Core/HornScale.lean`.

2. **TruthConditional**: `some_sem` defined as existential quantification. Proved conservative and upward-monotone. `every_sem` defined as universal quantification. The entailment `every ⊨ some` (every context where *all* is true is one where *some* is true) follows from the denotations.

3. **Fragments**: `QuantityWord.some_` and `QuantityWord.all` map to these denotations. The meaning function `meaning n .some_ w = (w.val ≥ 1)` is the *lower-bounded* (weak) reading — true whenever at least one entity has the property, including the case where all do.

4. **RSA**: L₀ hears "some" and assigns equal probability to all worlds where at least one entity qualifies (including the world where all qualify). S₁, choosing between "some" and "all," prefers "all" when all qualify (it's more informative). L₁ reasons: if the speaker chose "some" over "all," the all-world is less likely. Result: *some* is strengthened to *some but not all*.

5. **Phenomena**: `Phenomena/ScalarImplicatures/` records that adult English speakers reliably draw this inference, and verification theorems confirm that the RSA model's predictions match the behavioral data.

The key architectural point: at no step does the RSA model *stipulate* a meaning function. The literal semantics of "some" comes from the compositional semantics via the Fragment layer. If you changed `some_sem` to a bilateral meaning (some but not all), the RSA model would automatically inherit the change — and the scalar implicature would disappear, because L₁ would have nothing to strengthen. The grounding theorem `some_meaning_from_montague` makes this dependency explicit and machine-checkable.

## Knowledge and quality

The dependency chain gets more interesting when you add speaker knowledge. Goodman and Stuhlmuller (2013) showed that scalar implicatures are sensitive to the listener's beliefs about *what the speaker knows*. If the speaker has only seen one of three students' exams, the listener should not draw the "not all" inference — the speaker might simply not know whether all passed.

In Linglib, this is modeled with a quality-filtered pragmatic speaker. The key idea: the speaker's utility includes a log-probability term `ln P_lex(u|w)`, where `P_lex` is the literal truth of the utterance at the speaker's believed worlds. When `ln(0) = -∞` — the utterance is false at some world the speaker considers possible — the speaker's probability of choosing that utterance drops to zero. An uncertain speaker who hasn't seen all the exams *cannot say "all"*, not because of a Gricean maxim, but because "all" is literally false at some worlds in her belief state. She is forced to use the weaker "some," and the listener, reasoning about this constraint, correctly infers uncertainty rather than "not all."

This is exactly the kind of result where grounding matters. The quality filter operates on the *same* GQ denotations that the basic model uses — `some_sem` and `every_sem` from the TruthConditional layer. The knowledge-sensitivity falls out of the interaction between the denotations and the belief-state machinery, without any additional stipulation about what scalar implicatures should do under uncertainty. Change the denotations, and the knowledge predictions change too.

## Borrowing from Mathlib

Everyone knows that GQ monotonicity and polarity (in the Ladusaw/Fauconnier sense) are the same thing — a function that preserves entailment direction. The nice part of formalizing in Lean is that you can make this identification literal: `scopeUpMono_iff_monotone` proves that `ScopeUpwardMono q` is equivalent to Mathlib's `Monotone (q R)`, and `Polarity.lean` defines `IsUpwardEntailing` as `Monotone`. Once these are connected, Mathlib's library of composition lemmas comes along for free.

The polarity composition table — UE∘DE = DE, DE∘DE = UE, and so on — is the kind of thing that every semantics textbook states and every student re-derives. In Linglib, the whole table is four applications of `Monotone.comp`, `Antitone.comp_antitone`, and their siblings. Double negation as an upward-entailing context is a one-liner. We don't prove these facts about language; we inherit them from order theory.

This is a small example of a broader pattern. Mathlib has thousands of lemmas about ordered structures, lattices, and filters. Every time a linguistic concept can be identified with a Mathlib concept — and monotonicity is the easiest case — we get that infrastructure without re-deriving it. The Montagovian individual `I_a = {P : a ∈ P}` is a principal ultrafilter; `individual_upward_closed` and `individual_meet_closed` are just the ultrafilter axioms. GQ meet and join (`gqMeet`, `gqJoin`) form a Boolean algebra. These identifications aren't deep, but they save work and — more importantly — they guarantee that our linguistic definitions are consistent with the mathematical structures they're supposed to instantiate.

## Three paths to weak and strong

Here is a different kind of payoff: a convergence result that the formalization makes visible. The weak/strong distinction for determiners — *some* is weak, *every* is strong — is one of the most empirically productive classifications in GQ theory. It predicts which determiners can appear in *there*-sentences ("There are some/*every cats on the mat"), which take partitive complements naturally, and how they interact with focus. But what *is* the weak/strong distinction? It turns out there are three independent characterizations, and the formalization proves they are equivalent (under conservativity):

**Path 1 — Symmetry.** A conservative quantifier is weak iff it is symmetric: `Q(A,B) = Q(B,A)`. *Some* is symmetric (overlap is symmetric); *every* is not (inclusion is not). The theorem `conserv_symm_iff_int` proves that under conservativity, symmetry is equivalent to the intersection condition — the quantifier's truth value depends only on `A ∩ B`.

**Path 2 — Existential property.** A quantifier is weak iff it satisfies the existential property: `Q(A,B) = Q(A∩B, everything)`. This is Keenan and Stavi's (1986) characterization — the restrictor-scope pair can be "compressed" to just the intersection. `some_existential` and `every_not_existential` verify this for the concrete denotations.

**Path 3 — Persistence.** A quantifier is weak iff it is restrictor-upward-monotone (persistent): if `A ⊆ A'` and `Q(A,B)`, then `Q(A',B)`. Barwise and Cooper connected this to *there*-insertion: persistent quantifiers allow existential constructions.

Each path comes from a different theoretical tradition — symmetry from Peters and Westerstahl, the existential property from Keenan and Stavi, persistence from Barwise and Cooper. Each involves different formal machinery. And yet they carve out exactly the same class of quantifiers. The formalization makes this convergence explicit: `some_symmetric`, `some_existential`, and `some_restrictor_up` all hold; `every_not_symmetric`, `every_not_existential`, and `every_restrictor_down` are their mirror images.

The interesting implication is structural: if you discover a new determiner and establish that it's symmetric, you get the existential property and persistence *for free* (under conservativity). If any one path fails, all three must fail. "Weak" is not a primitive category — it is a hub where three independent properties converge, and that convergence is a theorem, not a coincidence.

## What the architecture buys you

The GQ case study illustrates a general pattern. The three-layer separation — abstract properties, concrete denotations, lexical entries — isn't just organizational tidiness. It enforces a distinction between formal results and empirical claims that is easy to blur on paper.

That `every_sem` is conservative is a *theorem* — it follows from the definition. That *all attested natural language determiners* are conservative is an *empirical observation*, recorded in `Phenomena/Quantification/Universals.lean`. These are different kinds of claims, and they belong in different places. The library's architecture makes the boundary explicit: proofs in `TruthConditional/`, data in `Phenomena/`, and the connection between them mediated by `Fragments/`.

And when the formalization reveals that three traditions — GQ theory, polarity, and abstract order theory — are provably the same thing, or that three independent characterizations of weak determiners converge to the same class, it is doing something that prose alone cannot. It is turning implicit connections into explicit theorems, and making the dependency structure of the field machine-checkable.
