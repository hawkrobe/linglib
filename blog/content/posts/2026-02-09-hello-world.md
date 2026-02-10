---
title: "Hello World: Introducing Linguistics in Lean"
date: 2026-02-09
summary: "Why Linglib has a blog now, and what we've been up to."
tags: ["meta", "situation-semantics", "definiteness", "pronouns"]
---

Linglib is a Lean 4 library for formalizing linguistic theories and connecting them to computational pragmatics. We've been building it for a while, but until now the only public-facing documentation has been auto-generated API docs. This blog — **Linguistics in Lean** — is meant to fill the gap: documenting design decisions, summarizing new modules, and lowering the barrier to contribution.

The idea is borrowed from the Lean math community. Baanen et al. (CICM 2025) make a convincing case that writing down unwritten knowledge about a formalization project is one of the most effective things you can do to help others contribute.

## Recent work

The last few releases (v0.129–v0.133) focused on three interconnected areas:

1. **Situation semantics** — A new `Elbourne.lean` module formalizes Elbourne (2013), deriving the referential/attributive distinction from situation binding rather than ambiguity, and connecting donkey anaphora to minimal situations.

2. **Pronoun typology** — `PronounTypology.lean` encodes Patel-Grosz & Grosz (2017) with data from 11 languages, verified generalizations (Minimize DP!, DEM-subset-PER implicational universal), and bridges to coreference, demonstratives, and direct reference modules.

3. **Core/Definiteness refactoring** — Definiteness vocabulary (`DefPresupType`, `ArticleType`, `BridgingSubtype`, etc.) was consolidated from scattered Phenomena files into a single `Core/Definiteness.lean` module, eliminating redundant Bool encodings and fixing an inverted Theories-to-Phenomena dependency.

All three connect: Elbourne's situation-relative definite article bridges to `Core/Definiteness.lean`'s presupposition types, and PG&G's pronoun classification bridges to both.

Check out the [API docs](/docs/) for the full details, or browse the [overview](/overview/) for a map of the library.
