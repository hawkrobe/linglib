/-!
# Austinian propositions
[barwise-perry-1983] [ginzburg-2012]

An Austinian proposition pairs a situation with a situation type and is
true iff the situation satisfies the type ([barwise-perry-1983];
[ginzburg-2012] Ch. 4, `[sit = s, sit-type = T]`). Separating the
situation from the classifying predicate — rather than carrying a
witness by construction — yields propositions that can be *false*,
which is what discourse needs: an asserted content enters FACTS as a
checkable claim.

## Main declarations

* `CheckableAustinian` — situation + classifying predicate; truth is
  `isTrue`, falsity `isFalse`
* `BCheckableAustinian` — the Bool-valued variant for computational
  use; `toBProp` evaluates the classifier as an `S → Bool`
-/

namespace Intensional

/-- A checkable Austinian proposition: a situation paired with a
classifying predicate ([ginzburg-2012] Ch. 4). Truth requires the
situation to satisfy the type, but need not hold — unlike a
witness-carrying situation–type pair, this proposition can be false. -/
structure CheckableAustinian (S : Type) where
  /-- The situation being classified -/
  sit : S
  /-- The classifying predicate (situation type) -/
  sitType : S → Prop

/-- A checkable Austinian proposition is true iff the situation satisfies
the type. -/
def CheckableAustinian.isTrue {S : Type} (p : CheckableAustinian S) : Prop :=
  p.sitType p.sit

/-- A checkable Austinian proposition is false iff the situation doesn't
satisfy the type. -/
def CheckableAustinian.isFalse {S : Type} (p : CheckableAustinian S) : Prop :=
  ¬p.sitType p.sit

/-- Decidable variant of `CheckableAustinian` for computational use. -/
structure BCheckableAustinian (S : Type) where
  sit : S
  sitType : S → Bool

/-- Decidable truth check. -/
def BCheckableAustinian.isTrue {S : Type} (p : BCheckableAustinian S) : Bool :=
  p.sitType p.sit

/-- Convert a decidable Austinian to `S → Bool`: evaluate the classifier
at each situation. -/
def BCheckableAustinian.toBProp {S : Type} (p : BCheckableAustinian S) :
    (S → Bool) :=
  p.sitType

/-- A true Austinian proposition's `toBProp` holds at its situation. -/
theorem BCheckableAustinian.toBProp_at_sit {S : Type} (p : BCheckableAustinian S)
    (h : p.isTrue = true) : p.toBProp p.sit = true := h

end Intensional
