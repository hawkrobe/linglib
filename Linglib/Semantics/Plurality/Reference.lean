import Linglib.Core.Order.Mereology

/-!
# Nominal Reference Predicates (Mass / Count / Bare Plural)
[krifka-1989] [link-1983] [champollion-2017]

The classical mereological classification of nominal predicates: mass
nouns satisfy `CUM` (cumulative reference), count nouns satisfy `QUA`
(quantized reference), bare plurals are algebraic closures (so are
also `CUM`). These are the foundational nominal-side primitives of
the Krifka–Link–Champollion algebraic semantics tradition.

## Main declarations

* `MassNoun` (= `CUM`) — mass nouns have cumulative reference.
* `CountNoun` (= `QUA`) — count nouns have quantized reference.
* `BarePlural` (= `AlgClosure`) — bare plurals as `*P`.
* `barePlural_cum` — bare plurals are cumulative.

## Implementation notes

Thin re-exports of `Core/Order/Mereology.lean` primitives under nominal-
reference names. The `CUM`/`QUA` definitional criteria are classical
([krifka-1989] §1) and widely known to be inadequate for the
modern mass/count picture — [chierchia-1998] argues mass nouns
can have atomic extensions; Sutton & Filip's overlap-based account
rejects `CUM` as definitional. The file is intentionally minimal:
it gives the Krifka–Link baseline; richer treatments live in
phenomenon-specific Studies files.

## Todo

* Bridge to [chierchia-1998] type-shifting / kind-denoting bare
  plurals (`∩P`).
* Bridge to Sutton & Filip overlap-based individuation (substrate
  not yet present).
* Bridge to classifier-language coercion (`Semantics/Classifier/`).
-/

namespace Semantics.Plurality.Reference

open _root_.Mereology

/-- Mass nouns have cumulative reference: water ⊕ water = water.
    [krifka-1989] §2: mass nouns denote predicates satisfying CUM. -/
abbrev MassNoun {α : Type*} [SemilatticeSup α] (P : α → Prop) : Prop := CUM P

/-- Count nouns have quantized reference: no proper part of a cat is a cat.
    [krifka-1989] §2: count nouns denote predicates satisfying QUA. -/
abbrev CountNoun {α : Type*} [PartialOrder α] (P : α → Prop) : Prop := QUA P

/-- Bare plurals are algebraic closures: *CAT = the closure of CAT under ⊕.
    [krifka-1989] §2: bare plurals denote *P, the smallest superset of P
    closed under sum formation. -/
abbrev BarePlural {α : Type*} [SemilatticeSup α] (P : α → Prop) : α → Prop :=
  AlgClosure P

/-- Bare plurals are cumulative (reuses `algClosure_cum` from `Core/Order/Mereology.lean`). -/
theorem barePlural_cum {α : Type*} [SemilatticeSup α] {P : α → Prop} :
    CUM (BarePlural P) :=
  algClosure_cum

end Semantics.Plurality.Reference
