import Linglib.Theories.Pragmatics.Expressives.Basic

/-!
# Maier 2014a: Mixed quotation as syntactic chameleonism
@cite{maier-2014a}

Maier, E. (2014). Mixed quotation: The grammar of apparently transparent
opacity. *Semantics & Pragmatics* 7:7, 1–67.

## Defining commitment

A SINGLE mixed-quotation operator `mq` can be inserted into a syntactic
tree above any node, creating a new node of the SAME syntactic category.
The operator is type-polymorphic: applied to a DP, it returns a DP;
applied to a VP, a VP; etc. K-G calls this Cappelen & Lepore's
"syntactic chameleonism" (paper p.11).

This is the architectural alternative K-G argues against in Section 2
(paper p.11): K-G holds that mixed quotation arises from a compositional
INTERACTION between pure quotation (which DOES change syntactic type, to
QDP/QVP/etc.) and a covert mixed-quotation operator 𝔐. Maier's
single-operator architecture is simpler but cannot account for K-G's §3
prediction that the strip-then-mix pipeline blocks original CI projection.

## Note on scope

This is a stub formalisation: enough of Maier's commitment to host
inequality theorems against K-G's strip-then-mix architecture in
`KirkGiannini2024.lean`. A fuller treatment would also formalize Maier's
DRT semantics for the peripheral content (which differs from K-G's
multidimensional approach) but is out of scope for the present
cross-framework comparison.
-/

set_option autoImplicit false

namespace Maier2014

open Pragmatics.Expressives (TwoDimProp)

/-- Maier's syntactic categories. Mixed-quoted expressions inherit the
    category of their daughter unchanged. -/
inductive Cat where
  | DP | VP | NP | AP | S
  deriving DecidableEq, Repr

/-- A typed expression: an item paired with its syntactic category. -/
structure TypedExpr (W : Type) where
  cat : Cat
  meaning : TwoDimProp W

/-- **Maier's mixed-quotation operator.** Type-polymorphic: takes a typed
    expression of any category and returns a typed expression of the SAME
    category, with a peripheral attribution layer added (the speaker
    produced the quoted material).

    Note: Maier's operator does NOT first pure-quote its input. The
    daughter's at-issue and CI content both pass through unchanged
    (modulo the new attribution). This is the architectural divergence
    from K-G: K-G's 𝔐 takes a `QDP/QVP`-typed pure-quoted input, not a
    same-category input. -/
def mq {W : Type} (attrib : W → Prop) (e : TypedExpr W) : TypedExpr W :=
  { cat := e.cat
  , meaning :=
    { atIssue := e.meaning.atIssue
    , ci := λ w => e.meaning.ci w ∧ attrib w } }

/-- **Maier's syntactic chameleonism (paper §3.1).** The operator
    preserves syntactic category exactly. -/
@[simp] theorem mq_inherits_syntactic_type_directly {W : Type}
    (attrib : W → Prop) (e : TypedExpr W) :
    (mq attrib e).cat = e.cat := rfl

/-- **Maier's CI passthrough.** The daughter's CI content survives
    inside `mq`'s output, conjoined with the new attribution. This is
    the K-G-disputed behavior: under K-G's strip-then-mix pipeline, the
    daughter's CI is destroyed by pure quotation BEFORE 𝔐 applies, so
    the original CI does not propagate. -/
theorem mq_ci_passes_daughter_ci_through {W : Type}
    (attrib : W → Prop) (e : TypedExpr W) (w : W) :
    (mq attrib e).meaning.ci w ↔ e.meaning.ci w ∧ attrib w := Iff.rfl

end Maier2014
