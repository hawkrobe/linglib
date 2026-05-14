---
title: "Linglib"
description: "A community library for formal linguistics in Lean 4."
---

## Why formalize linguistics?

Formal linguistics has accumulated decades of careful work — generative
syntax, model-theoretic semantics, optimality theory, distributed
morphology, dynamic semantics, rational speech-act pragmatics. The
results live in prose scattered across thousands of papers, with
assumptions often left implicit. Linglib is an attempt to gather the
machinery in one place so a proof assistant can do the bookkeeping.

Three things become possible when the bookkeeping is mechanical.
First, **breakage becomes detectable.** Change your semantics for
attitude verbs and Lean tells you exactly which downstream theorems
about conditionals, questions, or pragmatic inference no longer
follow — no more discovering an inconsistency from a reviewer.

Second, **predictions can be checked.** Theories are often stated in
notation ambiguous enough to hide gaps between what is claimed and
what actually follows from the definitions. Lean won't let a proof go
through unless the prediction genuinely follows from the theory.

Third, **theories become comparable.** When two accounts both claim to
handle the same data, we can formally characterize where they agree
and where they diverge, rather than arguing past each other in
different formalisms. The library is organized so that the same
phenomenon is often formalized under multiple competing frameworks —
not as a contest, but to make the interconnections visible.

{{< pillars >}}

## How it's organized

Linglib separates **phenomena** (what we observe) from **theories**
(what explains it). Theory-neutral observations — judgments,
experimental results, distributional patterns — live under
`Phenomena/` and are written so any framework can consume them.
Frameworks live under `Theories/`. Each `Studies/` file connects a
specific paper's account to the phenomenon, proving the predictions
the paper makes.

The connection across files is made by **import**, not stipulation:
when a study about scope freezing needs c-command, it imports the
same `Core/` definition that every other study uses. We call this
**interconnection density** — and the [dependency map]({{< relref "map.md" >}})
shows it visually: a small number of mathematical foundations, with
most of the interesting linguistic theory living on the bridges
between them.

## Contribute

Linglib is a community library. There's room for many people in many
roles, and most contributions don't require deep Lean expertise to
start. Four good entry points:

1. **Formalize a paper from your subfield.** Pick a paper you know
   well, write a study file under
   `Phenomena/X/Studies/AuthorYear.lean`, and prove the predictions
   it makes. The
   [contributor guide](https://github.com/hawkrobe/linglib/blob/main/CONTRIBUTING.md#formalize-a-paper)
   walks through what a study file looks like.
2. **Add a Fragment for an undercovered language.** We have entries
   for over a hundred languages, but most are sparse. If you work on
   a language whose typological profile isn't well represented, even
   a small fragment is valuable.
   ([Guide](https://github.com/hawkrobe/linglib/blob/main/CONTRIBUTING.md#add-a-fragment))
3. **Pick something off the wishlist.** The
   [wishlist]({{< relref "wishlist.md" >}}) is a curated list of
   theorems, papers, languages, and tools we'd love to see
   formalized — modeled on Lean's
   [1000+ theorems](https://leanprover-community.github.io/1000.html).
   Items are tagged by difficulty.
4. **Write a post or report a problem.** Critical readings are
   welcome — if a definition seems wrong, or a theorem trivializes
   the empirical content,
   [open an issue](https://github.com/hawkrobe/linglib/issues). The
   [blog]({{< relref "posts" >}}) is open to contributors.

Whether you're an undergrad working through your first formal-semantics
course, a postdoc with strong opinions about CCG, a computational
linguist with a probabilistic framework to formalize, or a Lean
enthusiast looking for a domain to apply theorem proving — there's
something here you can do.
