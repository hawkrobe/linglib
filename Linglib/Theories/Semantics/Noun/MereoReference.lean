import Linglib.Theories.Semantics.Events.Mereology

/-!
# Nominal Reference Predicates (Mass / Count / Bare Plural)
@cite{krifka-1989} @cite{link-1983} @cite{champollion-2017}

The mereological classification of nominal predicates: mass nouns
have cumulative reference (CUM), count nouns have quantized reference
(QUA), bare plurals are algebraic closures (AlgClosure → CUM).
These are the foundational nominal-side primitives of the
Krifka-Link-Champollion algebraic semantics tradition.

Topic-named (not paper-named): defines the deep substrate that
@cite{krifka-1989} §1, @cite{link-1983}, and any modern
algebraic-noun account uses. Specific paper replications import
this file and instantiate the predicates on paper-specific data.

## Sections

1. `MassNoun` (= CUM): mass nouns are cumulative
2. `CountNoun` (= QUA): count nouns are quantized
3. `BarePlural` (= AlgClosure): bare plurals are *P, the closure of P
4. `barePlural_cum`: bare plurals are cumulative (chains to `algClosure_cum`)

-/

namespace Semantics.Noun.MereoReference

open Mereology
open Semantics.Events.Mereology

/-- Mass nouns have cumulative reference: water ⊕ water = water.
    @cite{krifka-1989} §2: mass nouns denote predicates satisfying CUM. -/
abbrev MassNoun {α : Type*} [SemilatticeSup α] (P : α → Prop) : Prop := CUM P

/-- Count nouns have quantized reference: no proper part of a cat is a cat.
    @cite{krifka-1989} §2: count nouns denote predicates satisfying QUA. -/
abbrev CountNoun {α : Type*} [PartialOrder α] (P : α → Prop) : Prop := QUA P

/-- Bare plurals are algebraic closures: *CAT = the closure of CAT under ⊕.
    @cite{krifka-1989} §2: bare plurals denote *P, the smallest superset of P
    closed under sum formation. -/
abbrev BarePlural {α : Type*} [SemilatticeSup α] (P : α → Prop) : α → Prop :=
  AlgClosure P

/-- Bare plurals are cumulative (reuses `algClosure_cum` from
    `Core/Mereology.lean`). -/
theorem barePlural_cum {α : Type*} [SemilatticeSup α] {P : α → Prop} :
    CUM (BarePlural P) :=
  algClosure_cum

end Semantics.Noun.MereoReference
