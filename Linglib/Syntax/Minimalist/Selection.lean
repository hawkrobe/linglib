import Linglib.Syntax.Minimalist.Derivation
import Linglib.Syntax.Minimalist.HeadFunction

/-!
# C-Selection and Derivation Well-Formedness
[adger-2003] [marcolli-chomsky-berwick-2025]

Implements Adger's c-selectional checking system over linglib's Minimalism
substrate. `Syntax/Minimalism/Derivation.lean` defines free Merge
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

Per [marcolli-chomsky-berwick-2025] §1.13.3 / §1.15, NEW Minimalism
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

namespace Minimalist

/-- A `SyntacticObject` paired with the projecting head's `LIToken` (per
    [marcolli-chomsky-berwick-2025] §1.13.3) and its remaining
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

/-! ### `checkedSel?` — parameterized over a head function

`checkedSel? h so` recursively checks an SO is built consistent with Adger 2003
c-selection (eq. 106 Checking under Sisterhood, eq. 132 Merge at root).
Returns the head's residual pending features after all internal checking,
or `none` if the structure is ill-built.

For a leaf, returns the leaf's `outerSel` untouched.

For a node `(l, r)` of `h.section_.σ so`, the convention is: `l` is the
projecting head (under harmonic head-initial), the complement `r` must be
saturated (its `checkedSelPlanar = some []`), `l`'s first pending feature is
consumed by matching against `r`'s outer category, and the residual is `l`'s
remaining stack. -/

/-- Underlying parameterized `checkedSel?` on a planar `FreeMagma`
    representative.

    For a binary node `(l, r)`, computes the right child's outer category
    by `leftmostLeafPlanar r |>.item.outerCat` (or `rightmostLeafPlanar r`
    under head-final), staying entirely in the planar world. This avoids
    the `externalize ∘ mk ≠ id` round-trip bug: re-applying `h.section_.σ`
    to `FreeCommMagma.mk r` would target a potentially DIFFERENT
    representative than the `r` we already have in hand. -/
def checkedSelWithPlanar (h : HeadFunction) :
    FreeMagma (LIToken ⊕ Nat) → Option (List Cat)
  | .of (.inl tok) => some tok.item.outerSel
  | .of (.inr _) => some []
  | .mul l r =>
    match checkedSelWithPlanar h l, checkedSelWithPlanar h r with
    | some (c :: rest), some [] =>
      let rHeadLeaf := match h.headSide with
        | .initial => leftmostLeafPlanar r
        | .final   => rightmostLeafPlanar r
      if rHeadLeaf.item.outerCat = c then some rest else none
    | _, _ => none

/-- Parameterized `checkedSel?`: under head function `h` (with externalize
    section), recursively check c-selection consistency on the planar
    representative `h.section_.σ so`. Computable when `h.section_.σ` is.

    Not given as a `SyntacticObject.checkedSelWith?` dot-notation method
    because `SyntacticObject := Quot _` doesn't admit dot-method projection
    through the quotient. Call as `checkedSelWith? h so`. -/
def checkedSelWith? (h : HeadFunction) (so : SyntacticObject) :
    Option (List Cat) :=
  checkedSelWithPlanar h (h.section_.σ so)

/-- For a leaf SO, `checkedSelWith?` returns the leaf's outer selection list
    (independent of head function). Routes through `Section.σ_of`. -/
@[simp] theorem checkedSelWith?_leaf (h : HeadFunction) (tok : LIToken) :
    checkedSelWith? h (.leaf tok) = some tok.item.outerSel := by
  show checkedSelWithPlanar h (h.section_.σ (FreeCommMagma.of (.inl tok))) = _
  rw [h.section_.σ_of]
  rfl

/-- For a trace SO, `checkedSelWith?` returns `some []`. -/
@[simp] theorem checkedSelWith?_trace (h : HeadFunction) (n : Nat) :
    checkedSelWith? h (.trace n) = some [] := by
  show checkedSelWithPlanar h (h.section_.σ (FreeCommMagma.of (.inr n))) = _
  rw [h.section_.σ_of]
  rfl

-- Legacy `SyntacticObject.checkedSel?_trace` deleted in Phase 3.A.4 cleanup.
-- The parameterized `checkedSelWith?_trace` above (h : HeadFunction) subsumes it
-- via the keystone `Section.σ_of` helper.

/-! ### Computable selection-driven head function (MCB `Dom(h)`)

`selCheck` is the order-independent, fully **computable** counterpart of
`checkedSelWith?`. It identifies the projecting head by c-selection
([adger-2003] eq. 133 "the head is the SO that selects"; eq. 137 "the item that
projects is the item that selects" = [marcolli-chomsky-berwick-2025] Lemma
1.13.7) rather than by planar position, so it needs **no** `section_`/`Quot.out`.
It returns `some (head, residual)` on the endocentric domain `Dom(h)`
([marcolli-chomsky-berwick-2025] Def 1.13.6) and `none` at exocentric/symmetric
nodes where neither sister uniquely selects the other — exactly MCB's
partial-domain restriction (book p. 128, p. 131). This is what makes
`Derivation.WellFormed` genuinely `Decidable` without `classical`. -/

/-- Combine two sisters' selection-check results. Order-independent (symmetric,
    `selStep_comm`): whichever sister's head c-selects the *saturated* other
    projects, yielding its residual stack; `none` at exocentric nodes (neither
    or both qualify). -/
def selStep : Option (LIToken × List Cat) → Option (LIToken × List Cat) →
    Option (LIToken × List Cat)
  | some (ha, c :: rest), some (hb, []) =>
      if hb.item.outerCat = c then some (ha, rest) else none
  | some (ha, []), some (hb, c :: rest) =>
      if ha.item.outerCat = c then some (hb, rest) else none
  | _, _ => none

theorem selStep_comm (x y : Option (LIToken × List Cat)) :
    selStep x y = selStep y x := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some py => cases py with | mk hy sy => cases sy <;> rfl
  | some px =>
    cases px with
    | mk hx sx =>
      cases y with
      | none => cases sx <;> rfl
      | some py =>
        cases py with
        | mk hy sy => cases sx <;> cases sy <;> rfl

/-- Underlying selection check on a planar `FreeMagma` representative. -/
def selCheckAux : FreeMagma (LIToken ⊕ Nat) → Option (LIToken × List Cat)
  | .of (.inl tok) => some (tok, tok.item.outerSel)
  | .of (.inr n) => some (mkTraceToken n, [])
  | .mul l r => selStep (selCheckAux l) (selCheckAux r)

theorem selCheckAux_respects (a b : FreeMagma (LIToken ⊕ Nat))
    (h : FreeMagma.CommRel a b) : selCheckAux a = selCheckAux b := by
  induction h with
  | swap a b => exact selStep_comm _ _
  | mul_left _ _ ih => simp only [selCheckAux, ih]
  | mul_right _ _ ih => simp only [selCheckAux, ih]

/-- Computable selection-driven head function ([marcolli-chomsky-berwick-2025]
    Def 1.13.6 on `Dom(h)`): `some (projecting head, residual pending features)`,
    or `none` outside the endocentric domain. No `section_`/`Quot.out`. -/
def selCheck : SyntacticObject → Option (LIToken × List Cat) :=
  FreeCommMagma.lift selCheckAux selCheckAux_respects

@[simp] theorem selCheck_leaf (tok : LIToken) :
    selCheck (.leaf tok) = some (tok, tok.item.outerSel) := rfl

@[simp] theorem selCheck_trace (n : Nat) :
    selCheck (.trace n) = some (mkTraceToken n, []) := rfl

@[simp] theorem selCheck_mul (l r : SyntacticObject) :
    selCheck (l * r) = selStep (selCheck l) (selCheck r) := by
  induction l, r using FreeCommMagma.inductionOn₂ with | _ a b => rfl

/-- Residual pending selectional features under `selCheck` (`some []` =
    saturated). The computable counterpart of `checkedSelWith?`. -/
def checkedSel (so : SyntacticObject) : Option (List Cat) := (selCheck so).map (·.2)

/-- The projecting head's lexical item on `Dom(h)`, computed by c-selection.
    Computable counterpart of `HeadFunction.head` for the endocentric case. -/
def selHead (so : SyntacticObject) : Option LIToken := (selCheck so).map (·.1)

@[simp] theorem checkedSel_leaf (tok : LIToken) :
    checkedSel (.leaf tok) = some tok.item.outerSel := rfl

@[simp] theorem selHead_leaf (tok : LIToken) : selHead (.leaf tok) = some tok := rfl

/-- Computable, section-free c-selection between SOs: `a` selects `b` iff `a`'s
    projecting head c-selects `b`'s (both on `Dom(h)`). The computable
    counterpart of `HeadFunction.selects` — no `Quot.out`/`classical`. -/
def selectsC (a b : SyntacticObject) : Prop :=
  match selHead a, selHead b with
  | some ha, some hb => ha.selects hb
  | _, _ => False

instance (a b : SyntacticObject) : Decidable (selectsC a b) := by
  unfold selectsC; split <;> infer_instance

@[simp] theorem selectsC_leaf (s t : LIToken) :
    selectsC (.leaf s) (.leaf t) ↔ s.selects t := by
  simp only [selectsC, selHead_leaf]

/-- The head of `selStep x y` (when defined) is one of `x`/`y`'s heads. -/
theorem selStep_fst {x y : Option (LIToken × List Cat)} {r : LIToken}
    (h : (selStep x y).map (·.1) = some r) :
    x.map (·.1) = some r ∨ y.map (·.1) = some r := by
  unfold selStep at h
  split at h
  · split_ifs at h <;> simp_all
  · split_ifs at h <;> simp_all
  · simp at h

/-- Head Feature Principle (computable): a Merge node's head is one of its
    daughters' heads ([adger-2003] eq. 137 / [marcolli-chomsky-berwick-2025]
    Lemma 1.13.7). Holds for `selHead` because it projects the *selector* by
    construction — cf. the deliberately-absent unconditional version for a
    general section in `HeadFunction.lean`. -/
theorem selHead_mul {a b : SyntacticObject} {h : LIToken}
    (hab : selHead (a * b) = some h) :
    selHead a = some h ∨ selHead b = some h := by
  simp only [selHead, selCheck_mul] at hab ⊢
  exact selStep_fst hab

/-- Apply a `Step` under c-selection ([adger-2003] eq. 134 Checking
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
    match selCheck item with
    | some (ihead, []) =>
      if ihead.item.outerCat = c then some ⟨.node so item, head, rest⟩ else none
    | _ => none
  | .emR _, ⟨_, _, []⟩ => none
  | .emL item, ⟨so, head, sel⟩ => some ⟨.node item so, head, sel⟩
  | .im mover traceId, ⟨so, head, sel⟩ =>
    some ⟨(Step.im mover traceId).apply so, head, sel⟩

/-- Run a derivation through `applyChecked`. Seeds the head from the
    initial leaf (M-C-B §1.13.3: leaves are always in `Dom(h)`); for
    node-initial derivations falls back to `HeadFunction.leftSpine.head`.
    Returns `none` if the initial is ill-built or any step violates
    c-selection. -/
def Derivation.checkedFinal? (d : Derivation) : Option SelectionalState := do
  let (h0, pending) ← selCheck d.initial
  d.steps.foldl
    (fun st? step => st?.bind (Step.applyChecked step))
    (some ⟨d.initial, h0, pending⟩)

/-- A derivation is **well-formed** (Adger's Full Interpretation,
    [adger-2003] eq. 104+161) iff it completes with no unchecked
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

[adger-2003] ch. 7 (Functional Categories II — the DP) treats every
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
    [adger-2003] ch. 7. -/
def nullDWrap (n : SyntacticObject) (id : Nat) : SyntacticObject :=
  .node (nullD id) n

/-! ## Angelopoulos 2026: silent light noun for [n]-feature checking

[angelopoulos-2026] §3.1 (following [arsenijevic-2009],
[moltmann-2019]) analyses Greek *oti*/*pu* as bearing an
uninterpretable [n]-feature checked by a silent light noun in their
specifier. The light noun is then licensed by incorporation
([hale-keyser-1993]) into a higher *lexical* head (`v_State` or
`v_Event`); incorporation into a *functional* head (`T`) is impossible.

`nullN id` builds a saturated silent little-n leaf, parallel to
`nullD`. It carries no further selectional features — its role is to
be Merged into Spec,CP, where it checks the C head's [n]-feature, and
subsequently to head-move into a hosting v. Uses the existing `Cat.n`
constructor (Marantz 2001 / Distributed Morphology nominal categorizer);
no new `Cat` constructor required. -/

/-- A silent light noun (n head) with no selectional features, used for
    checking a complementizer's [n]-feature in its specifier per
    [angelopoulos-2026] §3.1. The `id` argument should be unique
    within the derivation. Mirrors `nullD`. -/
def nullN (id : Nat) : SyntacticObject :=
  mkLeafPhon .n [] "" id

@[simp] theorem nullN_outerCat_leftSpine (id : Nat) :
    HeadFunction.leftSpine.outerCat (nullN id) = .n := by
  simp [nullN, mkLeafPhon, LexicalItem.outerCat, LexicalItem.simple]

@[simp] theorem nullN_checkedSel_leftSpine (id : Nat) :
    checkedSelWith? HeadFunction.leftSpine (nullN id) = some [] := by
  simp [nullN, mkLeafPhon, LexicalItem.outerSel, LexicalItem.simple]

/-! ## Step-level lemmas

Destructor lemmas describing how `applyChecked` interacts with each `Step`
constructor. Front-loaded so consumers (paper-replication study files) can
reason about specific derivations without unfolding `foldl`. -/

/-- `emR` with a saturated, category-matching item consumes the first
    selectional feature; head is preserved. Stated against
    `HeadFunction.leftSpine` (the default head function used by
    `Step.applyChecked`). -/
@[simp] theorem applyChecked_emR_match
    (so item : SyntacticObject) (head ihead : LIToken) (c : Cat) (rest : List Cat)
    (hsel : selCheck item = some (ihead, []))
    (hcat : ihead.item.outerCat = c) :
    Step.applyChecked (.emR item) ⟨so, head, c :: rest⟩
      = some ⟨.node so item, head, rest⟩ := by
  simp [Step.applyChecked, hsel, hcat]

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
  unfold Derivation.WellFormed Derivation.checkedFinal?
  rw [selCheck_leaf, h]
  rfl

/-- `nullDWrap` of any `selCheck`-saturated SO whose projecting head is category
    N is itself saturated under the computable `checkedSel` (Adger ch. 7: silent
    D wraps a saturated N to yield a saturated DP). Discharges the former
    `checkedSelWith?`/`Quot.out`-bound `sorry` — the selection-driven `selCheck`
    reduces structurally through the binary node. -/
theorem checkedSel_nullDWrap (n : SyntacticObject) (id : Nat) (nhead : LIToken)
    (hsel : selCheck n = some (nhead, [])) (hcat : nhead.item.outerCat = .N) :
    checkedSel (nullDWrap n id) = some [] := by
  show (selCheck (nullD id * n)).map (·.2) = some []
  rw [selCheck_mul, hsel,
      show selCheck (nullD id) = some (⟨.simple .D [.N] "", id⟩, [.N]) from rfl]
  simp [selStep, hcat]

end Minimalist
