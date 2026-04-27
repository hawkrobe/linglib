import Linglib.Theories.Syntax.Minimalism.Derivation
import Linglib.Theories.Syntax.Minimalism.HeadFunction

/-!
# C-Selection and Derivation Well-Formedness
@cite{adger-2003} @cite{marcolli-chomsky-berwick-2025}

Implements Adger's c-selectional checking system over linglib's Minimalism
substrate. `Theories/Syntax/Minimalism/Derivation.lean` defines free Merge
(`Step.apply`); this file adds the orthogonal layer of feature checking
that filters which derivations satisfy Full Interpretation.

## Adger's apparatus

- (104) **Full Interpretation**: the structure at the semantic interface
  contains no uninterpretable features
- (105) **Checking Requirement**: uninterpretable features must be checked,
  then they delete
- (106) **Checking under Sisterhood**: an uninterpretable feature [uF] on a
  syntactic object Y is checked when Y is sister to another syntactic object
  Z which bears a matching feature F
- (110) `kiss [V, uN]`: an interpretable [V] feature plus an uninterpretable
  c-selectional [uN] feature
- (132) Merge applies to two SOs forming a new SO; only at the root
- (133) **Definition of Head**: the head is the SO that selects in any
  Merge operation
- (137) **Headedness**: the item that projects is the item that selects

## M-C-B alignment: head info lives in the derivation

Per @cite{marcolli-chomsky-berwick-2025} §1.13.3 / §1.15, NEW Minimalism
keeps `SyntacticObject` label-free (= `FreeMagma LIToken` here) and treats
head functions as **external partial maps** `Dom(h) ⊂ SO → LIToken`.
linglib follows this discipline:

- For derivation-based code, the head is **tracked through the derivation
  history** in `SelectionalState.head`. `Derivation.headLI?` and
  `Derivation.outerCat?` are then **total** for leaf-initial derivations
  (no heuristic involved).
- For arbitrary `FreeMagma LIToken` values not coming from a derivation,
  the leftmost-leaf heuristic in `Basic.lean`'s `outerCat` provides a
  partial extension. This is `HeadFunction.leftSpine` in
  `HeadFunction.lean`.

`Step.emR item` is **first Merge** (complement): the head's outermost
selectional feature is checked against `item.outerCat`, and the complement
itself must be saturated (no remaining unchecked features). The projecting
head does not change. `Step.emL item` is **second Merge** (specifier): no
consumption — in linglib's flat encoding, specifiers are added by an
operation distinct from c-selection-driven first Merge (Adger's split
between V and little v puts the subject in spec,vP via EPP rather than via
V's c-selection). The projecting head does not change.

## Key definitions

- `SelectionalState` — bundles a `SyntacticObject` with the projecting
  head's `LIToken` and its remaining unchecked selectional features
- `SyntacticObject.checkedSel?` — recursively checks a built tree for
  internal c-selection consistency, returning the head's residual pending
  stack (heuristic-based, used internally for complex `emR` items)
- `Step.applyChecked` — applies a step under c-selection, returning `none`
  when checking fails (eq. 134 Checking Requirement); preserves head info
- `Derivation.checkedFinal?` — runs the derivation through `applyChecked`,
  seeding head from the initial leaf
- `Derivation.headLI?` / `Derivation.outerCat?` — **total** head accessors
  for derivation-based code (M-C-B §1.13.3 head function via derivation
  tracking)
- `Derivation.WellFormed` — Adger's Full Interpretation: derivation
  completes with empty pending stack
- `nullD` / `nullDWrap` — Adger ch. 7 (DP): silent D head wrapping a bare N
  to project a DP that satisfies a verb's [uD] c-selection

## Design notes

- **`Step.apply` is unchanged.** Free Merge and feature checking are
  separated, mirroring Adger's split between Merge as a structural
  operation (Ch 3 §3.2) and the Checking Requirement as a separate
  constraint (§3.5.3).
- **Complex complements are checked recursively** via `checkedSel?`, which
  enforces (a) internal saturation of the complement and (b) match between
  the head's pending feature and the complement's `outerCat`. This handles
  null-D-wrapped DPs (Adger ch. 7) where the complement is `(∅, NP)` with
  `∅`'s [uN] checked internally before the whole DP is offered to the verb.
- **Leftmost-leaf head heuristic** survives only for the partial extension
  to arbitrary `FreeMagma`s (in `outerCat` and `checkedSel?`). For
  derivation-based head info, see `Derivation.headLI?` / `outerCat?` —
  these are total via M-C-B §1.13.3 derivation tracking.
-/

namespace Minimalism

/-- A `SyntacticObject` paired with the projecting head's `LIToken` (per
    @cite{marcolli-chomsky-berwick-2025} §1.13.3) and its remaining
    uninterpretable c-selectional features.

    Convention: features are consumed left-to-right by sister `emR`
    (complement Merge). The state is empty (`pending = []`) iff the head's
    selectional requirements have all been checked (Adger's Full
    Interpretation). -/
structure SelectionalState where
  /-- The current syntactic object. -/
  so : SyntacticObject
  /-- The projecting head's lexical item, tracked through the derivation
      (M-C-B §1.13.3 head function evaluated at the root vertex). -/
  head : LIToken
  /-- Remaining uninterpretable c-selectional features on the projecting
      head, in the order they will be checked. -/
  pending : List Cat
  deriving Repr, DecidableEq

/-- Recursively check that an SO is built consistent with Adger 2003
    c-selection (eq. 106 Checking under Sisterhood, eq. 132 Merge at root).
    Returns the head's residual pending features after all internal
    checking, or `none` if the structure is ill-built.

    For a leaf, returns the leaf's `outerSel` untouched.

    For a node `(l, r)`, the convention is: `l` is the projecting head,
    the complement `r` must be saturated (its `checkedSel? = some []`),
    `l`'s first pending feature is consumed by matching against
    `r.outerCat`, and the residual is `l`'s remaining stack.

    **Caveat**: relies on the leftmost-leaf head heuristic from
    `Basic.lean`'s `outerCat` (= `HeadFunction.leftSpine` in
    `HeadFunction.lean`). Sound for left-headed trees built via
    `Step.emR`-style complement Merge or direct `merge` with the
    projecting head on the left. -/
def SyntacticObject.checkedSel? : SyntacticObject → Option (List Cat)
  | .leaf tok => some tok.item.outerSel
  | .node l r =>
    match l.checkedSel?, r.checkedSel? with
    | some (c :: rest), some [] =>
      if r.outerCat = c then some rest else none
    | _, _ => none

/-- Apply a `Step` under c-selection (@cite{adger-2003} eq. 134 Checking
    Requirement, eq. 106 Checking under Sisterhood). The projecting head
    is preserved across all step constructors — this matches M-C-B §1.15
    (the labeling algorithm assigns the same head to a node and its head
    daughter) and Adger eq. 137 ("Headedness").

    - `emR item` (complement Merge) requires (a) the head's `pending` to
      be non-empty and its head category to match `item.outerCat`, and
      (b) `item` to be saturated (`item.checkedSel? = some []`). The
      matched feature is consumed; head unchanged.
    - `emL item` (specifier Merge) does not consume selectional features;
      head unchanged.
    - `im` and `wlm` propagate without consumption; head unchanged.

    Returns `none` when checking fails (no pending feature, category
    mismatch, or unsaturated complement). -/
def Step.applyChecked : Step → SelectionalState → Option SelectionalState
  | .emR item, ⟨so, head, c :: rest⟩ =>
    match item.checkedSel? with
    | some [] =>
      if item.outerCat = c then some ⟨.node so item, head, rest⟩ else none
    | _ => none
  | .emR _, ⟨_, _, []⟩ => none
  | .emL item, ⟨so, head, sel⟩ => some ⟨.node item so, head, sel⟩
  | .im mover traceId, ⟨so, head, sel⟩ =>
    some ⟨(Step.im mover traceId).apply so, head, sel⟩
  | .wlm restrictor target, ⟨so, head, sel⟩ =>
    some ⟨(Step.wlm restrictor target).apply so, head, sel⟩

/-- Run a derivation through `applyChecked`. Seeds the head from the
    initial leaf (M-C-B §1.13.3: leaves are always in `Dom(h)`); for
    node-initial derivations falls back to the leftmost-leaf heuristic.
    Returns `none` if the initial is ill-built or any step violates
    c-selection. -/
def Derivation.checkedFinal? (d : Derivation) : Option SelectionalState := do
  let pending ← d.initial.checkedSel?
  d.steps.foldl
    (fun st? step => st?.bind (Step.applyChecked step))
    (some ⟨d.initial, d.initial.leftmostLeaf, pending⟩)

/-- A derivation is **well-formed** (Adger's Full Interpretation,
    @cite{adger-2003} eq. 104+161) iff it completes with no unchecked
    selectional features remaining on the projecting head. -/
def Derivation.WellFormed (d : Derivation) : Prop :=
  d.checkedFinal?.map (·.pending) = some []

instance (d : Derivation) : Decidable d.WellFormed := by
  unfold Derivation.WellFormed; infer_instance

/-! ## M-C-B-aligned head accessors

For derivation-based code, head info is **tracked** through the derivation
rather than recovered via heuristics. These accessors implement M-C-B
§1.13.3's head function for the leaf-initial case (which covers all
canonical Minimalist derivations). -/

/-- The projecting head's lexical item, computed by tracking through the
    derivation. Returns `some tok` for derivations whose initial seed is
    `.leaf tok` and whose step sequence is well-formed under
    `applyChecked`; `none` otherwise.

    This is the M-C-B §1.13.3 head function specialized to derivation
    history — **total** for leaf-initial well-formed derivations, with no
    leftmost-leaf heuristic. -/
def Derivation.headLI? (d : Derivation) : Option LIToken :=
  d.checkedFinal?.map (·.head)

/-- The projecting head's outer categorial feature (Adger eq. 110 [F]),
    derived from the tracked head. Total for leaf-initial well-formed
    derivations. -/
def Derivation.outerCat? (d : Derivation) : Option Cat :=
  d.headLI?.map (·.item.outerCat)

/-! ## Adger ch. 7: silent D for bare nominal arguments

@cite{adger-2003} ch. 7 (Functional Categories II — the DP) treats every
argumental nominal as a DP. Bare common nouns (mass nouns, generic plurals)
are headed by a phonologically silent D that projects DP and consumes the
noun's [N] feature.

`nullD id` builds a silent D leaf with selectional feature [N] (so that it
checks against an N complement); `nullDWrap n id` is the canonical
"null-D-wraps-a-bare-N" construction, returning `(nullD, n)` whose
`outerCat` is .D and whose `checkedSel?` is `some []` (saturated). -/

/-- A silent D head bearing the c-selectional feature [N], used by
    `nullDWrap` to project a DP from a bare common noun (Adger ch. 7).
    The `id` argument should be unique within the derivation. -/
def nullD (id : Nat) : SyntacticObject :=
  mkLeafPhon .D [.N] "" id

/-- Wrap a bare N (or any N-projecting SO) under a silent D, yielding a
    saturated DP suitable for use as a verb's [uD] complement.
    @cite{adger-2003} ch. 7. -/
def nullDWrap (n : SyntacticObject) (id : Nat) : SyntacticObject :=
  .node (nullD id) n

/-! ## Step-level lemmas

Destructor lemmas describing how `applyChecked` interacts with each `Step`
constructor. Front-loaded so consumers (paper-replication study files) can
reason about specific derivations without unfolding `foldl`. -/

/-- `emR` with a saturated, category-matching item consumes the first
    selectional feature; head is preserved. -/
@[simp] theorem applyChecked_emR_match
    (so item : SyntacticObject) (head : LIToken) (c : Cat) (rest : List Cat)
    (hsat : item.checkedSel? = some [])
    (hcat : item.outerCat = c) :
    Step.applyChecked (.emR item) ⟨so, head, c :: rest⟩
      = some ⟨.node so item, head, rest⟩ := by
  simp [Step.applyChecked, hsat, hcat]

/-- `emR` on an empty pending stack fails (no feature to check). -/
theorem applyChecked_emR_empty (so item : SyntacticObject) (head : LIToken) :
    Step.applyChecked (.emR item) ⟨so, head, []⟩ = none := rfl

/-- `emL` (specifier Merge) preserves both pending stack and head. -/
theorem applyChecked_emL
    (so item : SyntacticObject) (head : LIToken) (sel : List Cat) :
    Step.applyChecked (.emL item) ⟨so, head, sel⟩
      = some ⟨.node item so, head, sel⟩ := rfl

/-- A leaf-initial derivation with empty `outerSel` and no steps is
    well-formed (Adger eq. 104: vacuously satisfies Full Interpretation). -/
theorem wellFormed_initial_no_sel (tok : LIToken)
    (h : tok.item.outerSel = []) :
    Derivation.WellFormed ⟨.leaf tok, []⟩ := by
  simp [Derivation.WellFormed, Derivation.checkedFinal?,
        SyntacticObject.checkedSel?, h]

/-- `nullDWrap` of any leaf whose `outerCat = .N` is saturated. -/
theorem checkedSel_nullDWrap_leaf (n : SyntacticObject) (id : Nat)
    (hN : n.outerCat = .N) (hsat : n.checkedSel? = some []) :
    (nullDWrap n id).checkedSel? = some [] := by
  simp [nullDWrap, nullD, SyntacticObject.checkedSel?,
        hsat, hN, mkLeafPhon, LexicalItem.outerSel, LexicalItem.simple]

end Minimalism
