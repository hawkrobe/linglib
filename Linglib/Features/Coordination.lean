/-!
# Conjunction Strategy ([mitrovic-sauerland-2014])

The cross-linguistic conjunction-strategy typology: languages vary in which of the
[mitrovic-sauerland-2014] semantic pieces (J, MU, type-shifter) are overtly realized.

(The coordinator marking — `Coordinator` / `Coordinator.Role` — now lives in
`Semantics/Coordination/Defs.lean`; this file retains only the M&S strategy enum, pending
its relocation to `Studies/MitrovicSauerland2016` when `Typology/Coordination` dissolves.)
-/

namespace Features.Coordination

/--
Cross-linguistic conjunction strategy.

[mitrovic-sauerland-2014] decompose DP conjunction into three semantic pieces:
J (set intersection), MU (subset), and a type-shifter. Languages vary in which
pieces are overtly realized.
-/
inductive ConjunctionStrategy where
  /-- Only J particle overt (e.g., English "and", Hungarian "es", Georgian "da") -/
  | jOnly
  /-- Only MU particles overt (e.g., Japanese "mo...mo", Hungarian "is...is",
      Georgian "-c...-c") -/
  | muOnly
  /-- Both J and MU overt (e.g., Hungarian "is es...is", Georgian "-c da...-c") -/
  | jMu
  deriving DecidableEq, Repr

/--
Number of overt functional morphemes per strategy.

Under [mitrovic-sauerland-2016], the underlying structure always has 3 semantic pieces
(J + MU1 + MU2). What varies is how many are pronounced.
-/
def ConjunctionStrategy.overtMorphemeCount : ConjunctionStrategy → Nat
  | .jOnly  => 1  -- only J pronounced
  | .muOnly => 2  -- both MUs pronounced
  | .jMu    => 3  -- J + both MUs pronounced

/--
Under [mitrovic-sauerland-2016], there are always 3 semantic pieces.
The transparency ratio measures how many are overtly realized.
-/
def ConjunctionStrategy.semanticPieceCount : Nat := 3

/--
[mitrovic-sauerland-2016] + Transparency Principle predicts: more overt morphemes -> easier
to acquire (closer to 1-to-1 form-meaning mapping).
-/
def ConjunctionStrategy.predictedTransparency : ConjunctionStrategy → Nat :=
  ConjunctionStrategy.overtMorphemeCount

end Features.Coordination
