---
title: "A Tour of Linglib"
date: 2026-02-09
summary: "Why formalize linguistics in a proof assistant, and how Linglib's three-layer architecture — Theories, Fragments, Phenomena — turns the type checker into an empirical testing harness."
tags: ["vision", "formalization", "RSA", "Montague", "architecture"]
---

Consider two theories of scalar implicature. The neo-Gricean account says that when a speaker says "some students passed," a grammatical exhaustivity operator EXH strengthens the literal meaning to "some but not all." The RSA account says the same enrichment falls out of recursive social reasoning: a literal listener updates on the utterance, a pragmatic speaker chooses utterances to be informative, and a pragmatic listener reasons about the speaker's choice. Both theories predict the same basic inference. Both have been enormously productive. And yet it has proved surprisingly difficult to say precisely when they agree and when they come apart — because each framework bakes in its own notation, its own implicit assumptions, and its own way of sweeping edge cases under the rug.

Linglib is an attempt to make these comparisons routine. It is a Lean 4 library that formalizes linguistic theories — Montague semantics, RSA, neo-Gricean pragmatics, CCG, HPSG, and others — in a shared type-theoretic language. The type checker doesn't care about notational tradition. It forces you to be explicit about every implicit assumption, and it tells you immediately when two formalizations are inconsistent with each other or with the data. The goal is infrastructure: a library where adding a new theory or a new phenomenon automatically generates testable connections to everything already there.

## Why a proof assistant?

Formalization in a proof assistant like Lean is not the same as implementation in a programming language. When you implement an RSA model in Python, you can run it and check that it produces the right numbers. But you can't *prove* that it produces the right numbers for all possible inputs, or that its meaning function is consistent with a particular compositional semantics. A proof assistant lets you state and verify these relationships as theorems.

This matters for linguistics because so much of the interesting theoretical work lives in the *connections* between modules. Does the RSA literal listener's meaning function actually correspond to the Montague denotation of the utterance? Does the neo-Gricean EXH operator produce the same truth conditions as the RSA pragmatic listener in the limit? These are the kinds of questions that are easy to pose informally and hard to answer rigorously. Formalization makes them answerable — and when the answer is "no," it tells you exactly where the two accounts diverge.

The math community demonstrated with [mathlib](https://leanprover-community.github.io/) that a unified formal library can be much more than the sum of its parts. Connections emerge across subfields that no one anticipated. But linguistics faces a challenge that mathematics does not: we are an empirical field. Our theories are accountable to behavioral data in a way that pure math is not. This means we need an architecture that treats empirical phenomena as first-class citizens, not afterthoughts.

## The three-layer architecture

Linglib is organized around a strict dependency hierarchy with three layers. The crucial insight is that the layers mirror the logic of empirical science: you have theories that make predictions, those predictions are mediated by concrete lexical and grammatical configurations, and the predictions are ultimately tested against observed phenomena.

**Theories** are the library code — types, operators, predicates, and proof infrastructure. `Theories/TruthConditional/` defines compositional denotations for determiners, adjectives, and verbs. `Theories/RSA/` defines the literal listener, pragmatic speaker, and pragmatic listener. `Theories/NeoGricean/` defines the EXH operator and alternative generation. Theories don't know about any particular language or any particular experiment. They are pure formal machinery.

**Fragments** are configurations — concrete lexical entries parameterized by Theory types. `Fragments/English/Determiners.lean` assigns each English determiner a monotonicity class, a strength classification, and a GQ denotation. `Fragments/Quantities.lean` sets up the scalar quantity domain (some/all) that RSA implementations use. Fragments import Theories but never import Phenomena. They are "pure" lexical data: they know about the formal categories but not about what any experiment found.

**Phenomena** are the test suite. `Phenomena/ScalarImplicatures/` records that adult English speakers typically strengthen "some" to "not all." `Phenomena/Quantification/Universals.lean` records that all attested natural language determiners are conservative. Each Phenomena file imports the relevant Fragment entries and Theory predicates, and then proves — via bridge theorems — that the Theory's predictions match the empirical observations.

The dependency arrow always points upstream: Phenomena import Fragments and Theories, Fragments import Theories, and never the reverse. This means the Theories are maximally reusable. The same `RSAScenario` type supports reference games (Frank & Goodman, 2012), scalar implicature (Goodman & Stuhlmuller, 2013), hyperbole (Kao et al., 2014), politeness (Yoon et al., 2020), and scope ambiguity (Scontras & Pearl, 2021) — all through different Fragment configurations, without modifying the core RSA machinery.

## Interconnection density

The point of putting everything in one library is not just convenience — it is to maximize what we call *interconnection density*. We want changes to break things. If you modify the denotation of `every_sem` in `TruthConditional/Determiner/Quantifier.lean`, the bridge theorems in `Fragments/English/Determiners.lean` should fail. If you change the alternative generation algorithm in `NeoGricean/Core/`, the scalar implicature predictions in `Phenomena/` should update. The type checker enforces these dependencies automatically.

This is the formalization counterpart of a familiar scientific virtue: we want our theoretical commitments to be tightly coupled to our empirical predictions, so that when something goes wrong, we know exactly where. Linglib makes the coupling explicit and machine-checkable.

## Grounding pragmatics in semantics

The central architectural commitment is that RSA models should *derive* their meaning functions from Montague compositional semantics, not stipulate them. A standard RSA implementation defines a literal listener L₀ with a meaning function mapping utterances to truth values — but where does that function come from? In a typical Python implementation, it comes from a hand-written dictionary. In Linglib, it comes from the compositional semantics: quantifier denotations from `TruthConditional/Quantifiers`, adjective denotations from `Adjective/Theory`, modal semantics from `IntensionalSemantics/Modal/`. Grounding theorems prove the connection explicitly.

This matters because it lets you pose a question that is otherwise difficult to ask precisely: *what happens to pragmatic inference when you change the underlying semantics?* If the meaning function is stipulated, the question doesn't arise — you just change the dictionary. If it's derived, you can swap in a different semantics (say, bilateral numerals instead of lower-bounded) and trace the consequences through the entire pragmatic pipeline.

## What's here so far

The library currently includes:

- **14 RSA paper implementations**, each with grounding theorems connecting the RSA meaning function to the underlying compositional semantics
- **Generalized quantifier theory** covering Barwise & Cooper (1981), van Benthem's (1984) relational characterization, and the Peters & Westerstahl symmetry results
- **Intensional semantics** for modals (Kratzer-style and simple), attitudes (doxastic, preferential, parasitic), conditionals, and causatives
- **Question semantics** spanning Hamblin denotations, partition semantics, inquisitive semantics, and decision-theoretic answerhood
- **Multiple syntactic frameworks** (CCG, HPSG, Minimalism) with cross-theory comparison infrastructure
- **50+ Phenomena files** recording empirical data from the experimental literature

The [overview](/overview/) has the full map; the [API docs](/docs/) have the detail. This blog will document design decisions, surprising connections, and lessons learned as the library grows.
