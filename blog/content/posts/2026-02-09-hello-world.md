---
title: "A Tour of Linglib"
date: 2026-02-09
summary: "Introducing Linglib, a Lean 4 library for cumulative, machine-checkable formal linguistics."
tags: ["vision", "formalization", "RSA", "Montague", "architecture"]
---

Linguistics produces formal fragments at an extraordinary rate. A paper on scalar implicature defines a speaker model, a set of alternatives, a pragmatic reasoning procedure, and a meaning function — then derives predictions from them. A paper on modal semantics defines accessibility relations, ordering sources, conversational backgrounds, and compositional rules — then derives predictions from those. Each fragment is self-contained, each is carefully worked out, and each re-derives from scratch the infrastructure it needs. The fragments do not accumulate.

This is not because the work is bad. It is because the field lacks shared infrastructure. There is no common repository of formal definitions that a new paper can import and build on. If you want to study how modal semantics interacts with scalar implicature, you formalize both from the ground up, in whatever notation suits the paper, and hope that the implicit assumptions you have made in each fragment are compatible. Often they are. Sometimes they are not, and the incompatibility surfaces only years later, when someone tries to combine results from two traditions and finds that the definitions do not quite match.

The mathematics community solved this problem with [mathlib](https://leanprover-community.github.io/), a unified Lean 4 library containing thousands of definitions and theorems in a shared type system. Mathlib is cumulative: each new contribution imports what it needs from the existing library, and the type checker ensures consistency. Connections emerge across subfields — between topology and algebra, between measure theory and combinatorics — that no one anticipated when the individual components were formalized. The library is more than the sum of its parts.

Linglib is an attempt to build the same kind of infrastructure for linguistics. It is a Lean 4 library that formalizes linguistic theories — Montague semantics, Rational Speech Acts, neo-Gricean pragmatics, Kratzer-style modality, question semantics, and others — in a shared type-theoretic language. The goal is to make linguistic theory cumulative: you formalize a semantics for quantifiers once, and every downstream module that needs quantifier meanings — RSA models, scope ambiguity, polarity licensing — imports and builds on the same definitions. Change the quantifier semantics, and the type checker tells you exactly what breaks downstream.

## What a proof assistant adds

Formalization in a proof assistant is not the same as implementation in a programming language. When you implement an RSA model in Python, you can run it and check that it produces the right numbers. But you cannot prove that it produces the right numbers for all possible inputs, or that its meaning function is consistent with a particular compositional semantics. A proof assistant lets you state and verify these relationships as theorems.

This matters for linguistics because so much of the interesting theoretical work lives in the connections between modules. Does the RSA literal listener's meaning function actually correspond to the Montague denotation of the utterance? Does the neo-Gricean EXH operator produce the same truth conditions as the RSA pragmatic listener in the limit? When Kennedy's exact numeral semantics is embedded in Goodman & Stuhlmuller's knowledge-state RSA model, does the quality filter select between type-shifted interpretations in the way the theory predicts? These are the kinds of questions that are easy to pose informally and hard to answer rigorously. Formalization makes them answerable — and when the answer is "no," it tells you exactly where the two accounts diverge.

But linguistics faces a challenge that mathematics does not: we are an empirical field. Our theories are accountable to behavioral data in a way that pure math is not. This means we need an architecture that treats empirical phenomena as first-class citizens, not afterthoughts.

## The three-layer architecture

Linglib is organized around a strict dependency hierarchy with three layers. The layers mirror the logic of empirical science: you have theories that make predictions, those predictions are mediated by concrete lexical and grammatical configurations, and the predictions are ultimately tested against observed phenomena.

**Theories** are the library code — types, operators, predicates, and proof infrastructure. `Theories/TruthConditional/` defines compositional denotations for determiners, adjectives, and verbs. `Theories/RSA/` defines the literal listener, pragmatic speaker, and pragmatic listener. `Theories/NeoGricean/` defines the EXH operator and alternative generation. Theories do not know about any particular language or any particular experiment. They are pure formal machinery.

**Fragments** are configurations — concrete lexical entries parameterized by Theory types. `Fragments/English/Determiners.lean` assigns each English determiner a monotonicity class, a strength classification, and a generalized quantifier denotation. `Fragments/Quantities.lean` sets up the scalar quantity domain (some/all) that RSA implementations use. Fragments import Theories but never import Phenomena. They are pure lexical data: they know about the formal categories but not about what any experiment found.

**Phenomena** are the test suite. `Phenomena/ScalarImplicatures/` records that adult English speakers typically strengthen "some" to "not all." `Phenomena/Quantification/Universals.lean` records that all attested natural language determiners are conservative. Each Phenomena file imports the relevant Fragment entries and Theory predicates, and then proves — via bridge theorems — that the Theory's predictions match the empirical observations.

The dependency arrow always points upstream: Phenomena import Fragments and Theories, Fragments import Theories, and never the reverse. This means the Theories are maximally reusable. The same `RSAScenario` type supports reference games (Frank & Goodman, 2012), scalar implicature (Goodman & Stuhlmuller, 2013), hyperbole (Kao et al., 2014), politeness (Yoon et al., 2020), and scope ambiguity (Scontras & Pearl, 2021) — all through different Fragment configurations, without modifying the core RSA machinery.

## Grounding pragmatics in semantics

The central architectural commitment is that RSA models should *derive* their meaning functions from Montague compositional semantics, not stipulate them. A standard RSA implementation defines a literal listener L₀ with a meaning function mapping utterances to truth values — but where does that function come from? In a typical Python implementation, it comes from a hand-written dictionary. In Linglib, it comes from the compositional semantics: quantifier denotations from `TruthConditional/Quantifiers`, adjective denotations from `Adjective/Theory`, modal semantics from `IntensionalSemantics/Modal/`. Grounding theorems prove the connection explicitly.

This matters because it lets you pose a question that is otherwise difficult to ask precisely: *what happens to pragmatic inference when you change the underlying semantics?* If the meaning function is stipulated, the question does not arise — you just change the dictionary. If it is derived, you can swap in a different semantics (say, bilateral numerals instead of lower-bounded) and trace the consequences through the entire pragmatic pipeline. The type checker propagates the change automatically.

## Interconnection density

The point of putting everything in one library is not convenience — it is to maximize what we call *interconnection density*. We want changes to break things. If you modify the denotation of `every_sem` in `TruthConditional/Determiner/Quantifier.lean`, the bridge theorems in `Fragments/English/Determiners.lean` should fail. If you change the alternative generation algorithm in `NeoGricean/Core/`, the scalar implicature predictions in `Phenomena/` should update. The type checker enforces these dependencies automatically.

This is the formalization counterpart of a familiar scientific virtue: we want our theoretical commitments to be tightly coupled to our empirical predictions, so that when something goes wrong, we know exactly where. Linglib makes the coupling explicit and machine-checkable.

## What's here so far

The library currently includes:

- **14 RSA paper implementations**, each with grounding theorems connecting the RSA meaning function to the underlying compositional semantics
- **Generalized quantifier theory** covering Barwise & Cooper (1981), van Benthem's (1984) relational characterization, and the Peters & Westerståhl symmetry results
- **Intensional semantics** for modals (Kratzer-style and simple), attitudes (doxastic, preferential, parasitic), conditionals, and causatives
- **Question semantics** spanning Hamblin denotations, partition semantics, inquisitive semantics, and decision-theoretic answerhood
- **Multiple syntactic frameworks** (CCG, HPSG, Minimalism) with cross-theory comparison infrastructure
- **50+ Phenomena files** recording empirical data from the experimental literature

This blog will document design decisions, surprising connections, and lessons learned as the library grows.
