import Mathlib.Logic.Basic

/-!
# Composition Rules for Layered ⟨A, N⟩ Propositions
@cite{potts-2005} @cite{anderbois-brasoveanu-henderson-2015}
@cite{martinez-vera-2026}

Two-layered propositions ⟨at-issue, not-at-issue⟩ admit three canonical
composition rules. The at-issue layer addresses the question under
discussion and is challengeable by direct denial; the not-at-issue layer
projects past negation and questions, hosting presuppositions,
conventional implicatures, and evidential meanings.

The three rules formalised here are @cite{martinez-vera-2026}'s
Composition I/II/III, but the pattern is older — they instantiate the
percolation discipline implicit in @cite{potts-2005}'s multi-dimensional
semantics and @cite{anderbois-brasoveanu-henderson-2015}'s at-issue
proposal/appositive imposition split.

| Rule | When to use | At-issue layer | Not-at-issue layer |
|------|-------------|----------------|--------------------|
| I    | β has trivial NAI; α brings NAI | `α.A β.A` | `α.N β.A` |
| II   | both α and β bring NAI | `α.A β.A` | `α.N β.A ∧ β.N` |
| III  | α is illocutionary, takes the full ⟨A, N⟩ pair | (full pair handed to α) | (full pair handed to α) |

The substrate stays propositional (`W → Prop` rather than `W → Bool`)
because the consumers — verum studies, evidential illocution, biased polar
questions — operate over `Set W` already and never reduce to a
truth-table.

## Relation to `Core/Semantics/ContentLayer.LayeredProp`

`Core/Semantics/ContentLayer.lean` defines a 3-layer `LayeredProp W`
(`presupposition / atIssue / implicature`, all `W → Bool`) anchored on
@cite{van-der-sandt-maier-2003}'s LDRT, with offensive-layer machinery
for the Off-computation. `BiLayered` here is a 2-layer `W → Prop`-valued
sibling: it collapses presupposition + implicature into an
undifferentiated `notAtIssue` (matching the @cite{martinez-vera-2026}
⟨A, N⟩ pair shape) and stays in `Prop` to compose cleanly with `Set W`
consumers.

The two are deliberately **not unified into a single parameterised
`Layered (n : ℕ)`** at this stage: LDRT's `Off`-targeting machinery
needs the 3-way `presupposition` vs `implicature` discrimination, while
the verum / evidential illocution literature uses the 2-way A vs N split
without that discrimination. A future `Layered n` typeclass refactor
would consolidate both, with `LayeredProp = Layered 3 W (W → Bool)` and
`BiLayered = Layered 2 W (W → Prop)`. Mirrors the mathlib pattern of
`Probability.Kernel.Defs` (general) + `Probability.Kernel.Deterministic`
(specialised) connected by an equivalence rather than re-stipulation.
-/

namespace Semantics.Composition.Layered

/-- A 2-layer ⟨A, N⟩ proposition. The at-issue layer is the proffered
    content; the not-at-issue layer collects everything backgrounded
    (presuppositions, conventional implicatures, evidential commitments).

    Trivially-true `notAtIssue` is the default — most expressions add no
    not-at-issue content, so the empty case should be cheap to construct. -/
@[ext]
structure BiLayered (W : Type*) where
  /-- Proffered, at-issue content. -/
  atIssue : W → Prop
  /-- Backgrounded, not-at-issue content. Defaults to trivially true. -/
  notAtIssue : W → Prop := fun _ => True

namespace BiLayered

variable {W : Type*}

/-- Lift a single proposition to a `BiLayered` with trivial NAI. -/
def ofProp (p : W → Prop) : BiLayered W :=
  { atIssue := p }

@[simp] theorem ofProp_atIssue (p : W → Prop) :
    (ofProp p : BiLayered W).atIssue = p := rfl

@[simp] theorem ofProp_notAtIssue (p : W → Prop) :
    (ofProp p : BiLayered W).notAtIssue = fun _ => True := rfl

end BiLayered

variable {W : Type*}

/-- @cite{martinez-vera-2026} Composition rule I: β has empty NAI; α brings
    NAI. The new at-issue layer is `α.A β.A`; the new NAI is `α.N β.A`. -/
def composeI (atFn naiFn : (W → Prop) → (W → Prop)) (β : BiLayered W) :
    BiLayered W :=
  { atIssue := atFn β.atIssue, notAtIssue := naiFn β.atIssue }

/-- @cite{martinez-vera-2026} Composition rule II: both α and β bring NAI.
    The new NAI accumulates `α.N β.A ∧ β.N`. -/
def composeII (atFn naiFn : (W → Prop) → (W → Prop)) (β : BiLayered W) :
    BiLayered W :=
  { atIssue := atFn β.atIssue
  , notAtIssue := fun w => naiFn β.atIssue w ∧ β.notAtIssue w }

/-- @cite{martinez-vera-2026} Composition rule III: an illocutionary operator
    takes the full ⟨A, N⟩ pair from β and returns a new pair. This is the
    composition rule used for `assert` and `present` in
    `Theories/Discourse/EvidentialIllocution.lean`. -/
def composeIII (op : BiLayered W → BiLayered W) (β : BiLayered W) : BiLayered W :=
  op β

@[simp] theorem composeI_atIssue (atFn naiFn : (W → Prop) → (W → Prop))
    (β : BiLayered W) : (composeI atFn naiFn β).atIssue = atFn β.atIssue := rfl

@[simp] theorem composeI_notAtIssue (atFn naiFn : (W → Prop) → (W → Prop))
    (β : BiLayered W) : (composeI atFn naiFn β).notAtIssue = naiFn β.atIssue := rfl

@[simp] theorem composeII_atIssue (atFn naiFn : (W → Prop) → (W → Prop))
    (β : BiLayered W) : (composeII atFn naiFn β).atIssue = atFn β.atIssue := rfl

@[simp] theorem composeII_notAtIssue (atFn naiFn : (W → Prop) → (W → Prop))
    (β : BiLayered W) :
    (composeII atFn naiFn β).notAtIssue =
      fun w => naiFn β.atIssue w ∧ β.notAtIssue w := rfl

@[simp] theorem composeIII_apply (op : BiLayered W → BiLayered W)
    (β : BiLayered W) : composeIII op β = op β := rfl

/-- Composition I subsumes Composition II when β.N is trivially true: the
    extra `∧ True` conjunct collapses. This is the formal sense in which
    rule II generalises rule I. -/
theorem composeI_eq_composeII_on_trivial_naiFn {W : Type*}
    (atFn naiFn : (W → Prop) → (W → Prop)) (β : BiLayered W)
    (hβ : β.notAtIssue = fun _ => True) :
    composeI atFn naiFn β = composeII atFn naiFn β := by
  ext w
  · rfl
  · simp [composeI, composeII, hβ]

end Semantics.Composition.Layered
