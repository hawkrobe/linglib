---
title: "Why Formalize Linguistics?"
date: 2026-02-09
summary: "The case for a unified formal library connecting linguistic theories in Lean 4."
tags: ["vision", "formalization", "RSA", "Montague"]
---

Linguistics has dozens of mature theoretical frameworks — Montague semantics, RSA, CCG, HPSG, Minimalism, DRT, neo-Gricean pragmatics — each with its own notation, assumptions, and community. They frequently make claims about the same phenomena, but it is surprisingly hard to tell when two theories genuinely disagree versus when they are saying the same thing in different notation. Linglib is an attempt to find out. It is a Lean 4 library that formalizes linguistic theories in a shared type-theoretic language, so their predictions can be directly compared.

The project's north star is: *for phenomenon P with behavioral data D, prove that theory T₁ predicts D and theory T₂ doesn't* — or prove that they both do, and identify exactly which assumptions differ. There are a few early examples of this in the library already (RSA vs. grammatical exhaustification on scalar implicatures, CCG vs. Minimalism on scope freezing), but the point is to build infrastructure that makes these comparisons routine rather than heroic.

## What formalization forces

A proof assistant is unforgiving about implicit assumptions. When a paper says "the speaker chooses the utterance that maximizes informativity," formalization forces you to specify: informativity with respect to what? Over which set of alternatives? With what prior? These questions often turn out to be where the real theoretical action is, and it is easy to gloss over them in prose.

The same discipline applies when connecting theories. We try to maximize what might be called *interconnection density*: hooking modules together so that changing one thing breaks others. When we recently formalized Elbourne (2013) on situation semantics, for instance, the type checker immediately flagged whether his situation-relative definite article was consistent with the presupposition types already in the library. When it is, you get a bridge theorem. When it isn't, you learn something. Either way, the dependency is explicit rather than implicit.

## Grounding pragmatics in semantics

The central architectural commitment in Linglib is that RSA models should *derive* their meaning functions from Montague compositional semantics, not stipulate them. A standard RSA model defines a literal listener L₀ with a meaning function mapping utterances to truth values — but where does that function come from? In Linglib, it comes from the compositional semantics: quantifier denotations from `TruthConditional/Quantifiers`, adjective denotations from `Adjective/Theory`, and so on. Grounding theorems prove the connection explicitly.

This matters because it lets you ask a question that is otherwise difficult to pose precisely: what happens to pragmatic inference when you change the underlying semantics? If the meaning function is stipulated, the question doesn't arise. If it's derived, you can swap in a different semantics and trace the consequences.

## Precedent

The Lean math community demonstrated with mathlib that a unified formal library can be more than the sum of its parts — connections emerge across subfields that no one anticipated. Baanen et al. (CICM 2025) document how writing down the "unwritten knowledge" of a formalization project lowers the barrier to contribution. Linguistics seems well-suited to the same approach. Many of the interesting results live in the connections between subfields, and those connections are exactly what is hardest to maintain on paper.

This blog will document design decisions and make the library's structure legible. Browse the [overview](/overview/) for a map of the library, or the [API docs](/docs/) for the full detail.
