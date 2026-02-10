---
title: "Generalized Quantifiers in Three Layers"
date: 2026-02-10
summary: "How linglib organizes generalized quantifier theory — from model-agnostic properties to concrete denotations to lexical entries — and what van Benthem's 'Aristotle reversed' tells us about the structure."
tags: ["quantifiers", "GQ", "van Benthem", "formalization", "Barwise-Cooper"]
---

"Every student passed." The sentence feels simple, but the word *every* is doing remarkable work. It takes two properties — being a student and having passed — and returns a truth value. Barwise and Cooper (1981) called this a *generalized quantifier*: a function from two sets to a truth value. Their insight was that natural language determiners (every, some, no, most, few) are all GQ denotations, and that the space of logically possible GQs is vastly larger than what any language actually uses. The question is: why these quantifiers and not others?

Linglib formalizes the theory of generalized quantifiers in Lean 4. This post explains how we organize the infrastructure and what we've learned from the formalization — particularly from van Benthem's (1984) characterization of the classical quantifiers through their inferential properties.

## The type

A generalized quantifier has type `(α → Bool) → (α → Bool) → Bool`: restrictor, scope, truth value. In Lean:

```lean
abbrev GQ (α : Type*) := (α → Bool) → (α → Bool) → Bool
```

"Every student passed" is `⟦every⟧ student passed`, where `student` and `passed` are characteristic functions. This is Montague's `(e→t) → ((e→t) → t)` in type-theoretic clothing.

## Three layers

The library organizes GQ theory across three layers, each with a distinct role:

**Core.Quantification** defines properties that hold for *any* GQ denotation, without reference to models or specific quantifiers. Conservativity (`Q(A,B) = Q(A, A∩B)`), monotonicity, duality, symmetry, and the van Benthem relational properties all live here. The definitions are purely logical: if you have a function of the right type, you can ask whether it's conservative. No model infrastructure needed.

**TruthConditional.Determiner.Quantifier** defines concrete denotations — `every_sem`, `some_sem`, `no_sem`, `most_sem` — and *proves* they satisfy the Core properties. These proofs use a `FiniteModel` class with a computable finite domain. The proofs are computational: `every_conservative` establishes that for any model, `⟦every⟧(A,B) = ⟦every⟧(A, A∩B)` by exhaustive case analysis over model elements.

**Fragments.English.Determiners** is the lexical layer. Each English determiner gets a `QuantityWord` entry specifying its monotonicity class, strength (weak/strong), inferential class, and double-monotonicity type. Bridge theorems connect these classifications to the proofs in the layer below: `all_inferential_bridge` proves that `QuantityWord.all`'s inferential class agrees with the relational properties proved for `every_sem`.

Changes at any layer propagate. If you modify `every_sem`'s denotation, the bridge theorems in Fragments break. If you weaken a Core definition, the concrete proofs in TruthConditional may no longer apply. This is by design — interconnection density is how we detect mistakes.

## The semantic universals

Barwise and Cooper conjectured that all simple determiners satisfy three properties: conservativity, quantity (isomorphism closure), and monotonicity. Van de Pol et al. (2023) showed that quantifiers satisfying these universals have lower Lempel-Ziv complexity — they are computationally simpler. The universals might reflect a cognitive simplicity bias rather than a logical necessity.

In linglib, we record these findings in `Phenomena.Quantification.Universals` as empirical observations, separate from the formal proofs. The boundary between "proved for our denotations" and "observed cross-linguistically" stays explicit.

## Aristotle reversed

Van Benthem (1984) turned the classical question on its head. Instead of asking "what properties does *every* have?", he asked: "if a quantifier is reflexive and antisymmetric, what *must* it be?" The answer: inclusion. The unique conservative quantifier satisfying reflexivity and antisymmetry is `∀x. A(x) → B(x)`.

This is formalized as `vanBenthem_refl_antisym_is_inclusion` in Core.Quantification. The proof is short. Conservativity gives `Q(A,B) = Q(A, A∩B)`. Reflexivity gives `Q(A∩B, A∩B)`. Conservativity again gives `Q(A∩B, A)`. Antisymmetry on `Q(A, A∩B)` and `Q(A∩B, A)` forces `A = A∩B`, i.e., `A ⊆ B`.

Each corner of the Square of Opposition gets a similar characterization. *Some* (overlap) is the unique symmetric quasi-reflexive quantifier. *No* (disjointness) is the unique symmetric quasi-universal one. *Not all* (non-inclusion) is almost-connected and irreflexive. The quantifiers are *determined* by their inferential behavior — you don't need to look at their denotations.

## The Zwarts bridge

The relational properties connect to monotonicity through what we call the Zwarts bridge (after Zwarts, via van Benthem 1984 §4.1). If a conservative quantifier is reflexive and transitive, it is scope-upward-monotone *and* restrictor-downward-monotone. This is the `↓MON↑` pattern — the double-monotonicity type of *every*.

```lean
theorem zwarts_refl_trans_scopeUp (q : GQ α)
    (hCons : Conservative q) (hRefl : PositiveStrong q)
    (hTrans : QTransitive q) : ScopeUpwardMono q
```

The proof is two lines. `Q(A,B)` and `B ⊆ B'` give `Q(B,B')` by conservativity and reflexivity. Then transitivity gives `Q(A,B')`. The restrictor direction is symmetric.

This means `every_restrictor_down` doesn't need its own proof from scratch — it follows from `every_conservative`, `every_positive_strong`, and `every_transitive` via the Zwarts bridge. Three layers meet in one theorem.

## What's next

The GQ infrastructure now covers the core of Barwise and Cooper (1981), the van Benthem (1984) relational characterization, and the Peters and Westerståhl symmetry/strength results. Open directions include formalizing van Benthem's impossibility theorems as full proofs rather than axioms (no asymmetric, no Euclidean quantifiers under CONSERV + QUANT + VAR), and connecting the double-monotonicity classification to NPI licensing patterns more tightly.

The [source](https://github.com/rxdh/linglib) is available. The relevant files are `Core/Quantification.lean`, `TruthConditional/Determiner/Quantifier.lean`, `Fragments/English/Determiners.lean`, and `Phenomena/Quantification/Universals.lean`.
