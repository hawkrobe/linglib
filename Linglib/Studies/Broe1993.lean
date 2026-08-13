import Mathlib.Data.Finset.Basic

/-!
# Broe (1993) [broe-1993]

*Specification theory: the treatment of redundancy in generative phonology*
replaces underspecified matrices and redundancy rules with **structured
specification**: the descriptions supported by a feature set, ordered by
inclusion of their denotations, form a lattice, and redundancy is read off
its dominance relation (§5.2's three-stage construction, an instance of
formal concept analysis). `naturalClasses` computes the stage-two lattice's
nonempty extents — the natural classes of an inventory — as the closure of
the attribute extents under intersection; the Quileute and reduced-Quileute
vowel systems of §5.2 are the thesis's worked examples.
-/

namespace Broe1993

variable {α : Type*} [DecidableEq α]

/-- The extents of the stage-two lattice of representations ([broe-1993]
§5.2): every intersection of `base` with attribute extents drawn from
`attrs`, deduplicated. Descriptions with the same denotation collapse to
one class; a description with empty denotation collapses to `∅`, the
lattice's bottom. -/
def naturalClasses (base : Finset α) (attrs : List (Finset α)) : List (Finset α) :=
  attrs.foldr (λ a acc => (acc ++ acc.map (a ∩ ·)).dedup) [base]

/-- The four-vowel Quileute system of §5.2, exhaustively classified by
[high] and [back]: /i a ɑ u/. -/
inductive Quileute where
  /-- /i/ — [+high, −back]. -/
  | i
  /-- /a/ — [−high, −back]. -/
  | a
  /-- /ɑ/ — [−high, +back]. -/
  | aBack
  /-- /u/ — [+high, +back]. -/
  | u
  deriving DecidableEq

/-- The Quileute attribute extents: [+hi], [−hi], [+ba], [−ba]. -/
def quileuteContext : List (Finset Quileute) :=
  [{.i, .u}, {.a, .aBack}, {.u, .aBack}, {.i, .a}]

/-- Every feature combination is attested and every description is
informative: the lattice of Broe's diagram (6) — all four two-vowel
classes, all four singletons, top, and bottom. -/
theorem quileute_classes :
    (naturalClasses {.i, .a, .aBack, .u} quileuteContext).toFinset =
      {{.i, .a, .aBack, .u}, {.i, .u}, {.a, .aBack}, {.u, .aBack}, {.i, .a},
       {.i}, {.a}, {.aBack}, {.u}, ∅} := by decide

/-- The reduced system without /a/ (Broe's Quileuteʹ): the same four
descriptions, with /a/ removed from the extents. -/
def quileutePrimeContext : List (Finset Quileute) :=
  [{.i, .u}, {.aBack}, {.u, .aBack}, {.i}]

/-- With the [−hi, −ba] gap, the lattice collapses to Broe's diagram (9):
[−hi] and [−hi, +ba] become synonymous (one class `{ɑ}`), and the
incompatible description [−hi, −ba] falls to bottom. -/
theorem quileutePrime_classes :
    (naturalClasses {.i, .aBack, .u} quileutePrimeContext).toFinset =
      {{.i, .aBack, .u}, {.i, .u}, {.u, .aBack}, {.i}, {.aBack}, {.u}, ∅} := by
  decide

/-- The redundancy rules Broe reads off the collapsed lattice's dominance
relation (p. 104): [−back] → [+high] and [−high] → [+back], as extent
inclusions. -/
theorem quileutePrime_redundancy :
    ({.i} : Finset Quileute) ⊆ {.i, .u} ∧ ({.aBack} : Finset Quileute) ⊆ {.u, .aBack} := by
  decide

end Broe1993
