---
title: "Wishlist"
description: "Things we'd love help formalizing. A curated list — open a PR to add yours."
---

This is a curated list of theorems, papers, languages, and tools we'd
love to see formalized in linglib. It's modeled on Lean's
[1000+ theorems](https://leanprover-community.github.io/1000.html)
project: a public scoreboard of work-wanted, organized by category.

If you're looking for a place to start contributing, pick an item from
below, [open an issue](https://github.com/hawkrobe/linglib/issues) so
others know you're working on it, and read the
[contributor guide](https://github.com/hawkrobe/linglib/blob/main/CONTRIBUTING.md).

**Status legend**: <code>open</code> — nobody has started ·
<code>wip</code> — work in progress · <code>done</code> — landed.
**Difficulty**: <code>A</code> quick win · <code>B</code> moderate ·
<code>C</code> hard · <code>D</code> blocked on upstream work.

> *This page is being curated manually. The list is short on purpose
> — items are added as they're triaged, not generated speculatively.
> To propose a wish, send a PR editing
> [`blog/content/wishlist.md`](https://github.com/hawkrobe/linglib/blob/main/blog/content/wishlist.md).*

---

## Books and longer programs

| Status | Difficulty | Item |
|---|---|---|
| wip | C | **Marcolli, Chomsky & Berwick (2025), *Mathematical Structure of Syntactic Merge: An Algebraic Model for Generative Linguistics*** ([MIT Press](https://mitpress.mit.edu/9780262552523/mathematical-structure-of-syntactic-merge/)). Formalize the algebraic model of Merge developed in the book. Substantial substrate is already in place — see the in-flight Phase E.3 work in `Linglib/Theories/Syntax/Minimalist/Merge/` and the surrounding Hopf-algebra machinery. Contributors are welcome at any of the open sub-phases; ping the maintainers via an issue for a current status snapshot. |

---

## Adding a wish

To propose a new wishlist item, edit
[`blog/content/wishlist.md`](https://github.com/hawkrobe/linglib/blob/main/blog/content/wishlist.md)
on a branch and send a PR. Each item should be:

- Concrete enough to start on (a theorem name, a paper, a language, a tool).
- Honest about difficulty (`A`–`D`).
- Pointed at where it would live in the codebase, if that's known.

To claim an item before starting work,
[open a tracking issue](https://github.com/hawkrobe/linglib/issues/new)
linking back to the wishlist line. We'll update the status here.
