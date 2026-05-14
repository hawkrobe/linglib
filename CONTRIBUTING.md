# Contributing to Linglib

Linglib is a community library for formal linguistics in Lean 4. This
guide describes the most common ways to contribute, with the
conventions you'll need to know inlined. The codebase is also
extensively documented in module docstrings — when in doubt, look at
existing files in the same area.

## Getting set up

1. Install [Lean 4 via elan](https://leanprover-community.github.io/get_started.html).
2. Clone the repo and fetch the mathlib cache:
   ```bash
   git clone https://github.com/hawkrobe/linglib
   cd linglib
   lake exe cache get
   lake build
   ```
3. Build takes ~5 minutes on a warm cache. `sorry`s in the codebase
   are intentional placeholders for in-progress proofs.

## Four entry points

### Formalize a paper

Most contributions start by picking a paper from a subfield you know
and writing a study file under `Linglib/Phenomena/{Phenomenon}/Studies/{AuthorYear}.lean`.

A study file typically:
- Imports the relevant theory from `Linglib/Theories/`.
- Imports any cross-linguistic data needed from `Linglib/Fragments/`.
- Encodes the paper's model — definitions, denotations, constraint
  ranking, whatever the paper specifies — in Lean syntax.
- Proves the predictions the paper claims, using the encoded model.
- Cites the paper in the module docstring with `@cite{key}` (add the
  BibTeX entry to `blog/data/references.bib` first).

Look at any existing file under `Linglib/Phenomena/*/Studies/` for a
template. `Phenomena/Definiteness/Studies/Jenks2018.lean` and
`Phenomena/Implicatures/Studies/` are reasonable starting points.

### Add a Fragment

A Fragment under `Linglib/Fragments/{Language}/` exposes the lexical
entries and typological metadata for one language. Even a sparse
fragment — say, a handful of pronouns and a tense paradigm — is
useful, because it lets phenomena studies cite real cross-linguistic
data instead of toy examples.

If you work on a language whose typological profile is poorly
represented (most non-Indo-European languages outside our existing
sample), a small contribution here goes a long way. See an existing
fragment (e.g. `Fragments/Mayan/Tseltalan.lean`) for the schema.

### Pick something off the wishlist

The [wishlist](https://hawkrobe.github.io/linglib/wishlist/) is a
curated list of theorems, papers, languages, and tools we'd love to
see formalized — modeled on Lean's
[1000+ theorems](https://leanprover-community.github.io/1000.html).
Items are tagged by difficulty (A: quick win · B: moderate · C: hard ·
D: blocked on upstream).

To claim an item before starting,
[open a tracking issue](https://github.com/hawkrobe/linglib/issues/new)
linking the wishlist line so others know you're working on it. To
add a new wish, send a PR editing
[`blog/content/wishlist.md`](blog/content/wishlist.md).

If you find a stub whose statement seems wrong (the underlying claim
doesn't hold, or the formalization mis-states the empirical claim),
that's also a valuable contribution — open an issue explaining the
problem.

### Write a post or report a problem

The [`blog/`](blog/) directory accepts posts on formalization
decisions, comparisons of frameworks, write-ups of completed work,
or critical readings of existing files.

If a definition seems wrong, a theorem trivializes the empirical
content, or you spot an inconsistency between two theories that
should agree, [open an issue](https://github.com/hawkrobe/linglib/issues).
Critical readings are welcome — formalization makes mistakes visible,
and we want them caught.

## Code conventions

A few conventions are worth knowing before your first PR. Look at
existing files in the same area for full context — the codebase is
the canonical reference.

**File structure.** Every `.lean` file should have a `/-! ... -/`
module docstring placed *after* the `import` statements (Lean
requires imports to come first).

**Citations.** Cite papers with `@cite{key}`; never inline
`Author (Year)`. Add the BibTeX entry to `blog/data/references.bib`
first using `lastname-lastname-year` keys, then regenerate the
rendered bibliography via `python3 blog/scripts/gen_bibliography.py`.

**Proof style.** Prefer structural tactics (`exact`, `simp only`,
`decide`, `omega`, `linarith`) over bare `simp` or `native_decide`.
Bare `simp` is fragile under simp-set changes; `native_decide`
bypasses kernel verification.

**`sorry` over weakening.** State the full theorem and use `sorry`
to mark it incomplete — a `sorry` warning is explicit, while a
weakened-but-proved theorem can be silently forgotten as not having
captured the intended claim.

**Lean style.** `autoImplicit` is disabled (declare type parameters
explicitly). Use `Type*` not `Type 0`. Prefer `Prop` with
`[DecidablePred]` over `Bool` for predicate-shape data. Use
`lowerCamelCase` for lemma names.

**Imports.** Only import what's needed — no `import Mathlib`
blanket. Cite the leaf file. Unnecessary imports slow builds and
create false dependency edges.

**Changelog.** Bump `CHANGELOG.md` via
`python3 scripts/changelog_add.py` (not direct edits — the file is
large and concurrent edits race).

## Pull requests

- Branch from `main`, push to a fork, open a PR.
- One coherent change per PR. Small is good.
- Keep commit messages short (~50–120 chars).
- The CHANGELOG entry tells the longer story (10–30 lines).

If you're not sure whether a contribution makes sense, open an issue
first to discuss. Substantive feedback on direction is welcome before
you've written code.

## Scope of welcome

Contributions are welcome from undergraduates working through their
first formal-semantics course, postdocs with strong opinions about
particular frameworks, computational linguists with probabilistic
models to formalize, and Lean enthusiasts looking for a domain. You
do not need to be a working academic linguist to contribute, and you
do not need to know mathlib internals to start.
