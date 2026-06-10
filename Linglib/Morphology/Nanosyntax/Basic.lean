/-!
# Nanosyntax: Basic Definitions
[caha-2009] [starke-2009]

Nanosyntax is a non-lexicalist, post-syntactic, piece-based,
realizational theory of morphology — identical to Distributed
Morphology on all four of [kalin-bjorkman-etal-2026]'s dimensions, but
distinguished by two mechanism-level differences: **phrasal spellout**
(lexical items spell out subtrees, not just terminals) and the
**Superset Principle** (an entry matches a node its stored constituent
contains; the Elsewhere Condition selects the smallest match,
[caha-2009] §2.2).

The proved selection-rule core — Superset matching and Minimize Junk
over `ExponenceRule` vocabularies on a linear fseq, with *ABA
(`isContiguous_spellout`), completeness, gap monotonicity, and
DM-equigenerativity theorems — lives in
`Morphology/Containment/Superset.lean`. Tree-based phrasal spellout for
branching structures lives in `Morphology/Nanosyntax/TreeSpellout.lean`.
This file holds the framework's remaining shared vocabulary.
-/

namespace Morphology.Nanosyntax

/-- Morphological type of an exponent derived from nanosyntactic
    spellout. Suffixes arise from spellout-driven movement (roll-up,
    unary foot); prefixes arise from subderivation (binary foot) —
    [dekier-2021] for this diagnostic on indefinite markers. -/
inductive MorphType where
  | suffix | prefix
  deriving DecidableEq, Repr

end Morphology.Nanosyntax
