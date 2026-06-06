import Linglib.Semantics.Presupposition.Basic

/-!
# Content Layers
[van-der-sandt-maier-2003]

Semantic content is stratified into layers that determine its discourse
behavior: how it projects, what denial can target, and whether it
addresses the QUD.

[van-der-sandt-maier-2003] propose Layered DRT (LDRT), where every DRS
condition carries a label — `pr` (presupposition), `fr` (at-issue), or
`imp` (implicature) — that determines how it behaves in denial. This
module extracts the layer system as a standalone type that unifies several
existing linglib distinctions:

- `PrProp` (presup + assertion) is the 2-layer special case (`pr` + `fr`)
- `Challengeability` (directDenial vs hwamChallenge) identifies which layer
  is targeted by a discourse challenge
- `AtIssueness` (atIssue vs notAtIssue) classifies content by whether it
  addresses the QUD — correlating with `fr` vs `pr`/`imp`
- `TraditionalCategory` (presupposition vs conventionalImplicature vs
  supplementary) is a coarser, partially overlapping taxonomy

## The Three Layers

| Layer | Label | Denial example |
|-------|-------|----------------|
| Presupposition | `pr` | "The king of France is NOT bald — there is no king" (30b) |
| At-issue | `fr` | "Mary is NOT happy — she's miserable" (5) |
| Implicature | `imp` | "It's not POSSIBLE — it's NECESSARY" (29b) |

## Design Note

`ContentLayer` lives in `Semantics/` because it generalizes `PrProp`.
Bridges to `Discourse/AtIssueness` and `Phenomena/Presupposition/
ProjectiveContent.Challengeability` live downstream in bridge files,
preserving the independence of `Semantics/` and `Discourse/`.

## Scope

This module captures the layer taxonomy and the `Off` function (which
layers are offensive = inconsistent with a correction). The directed
reverse anaphora (RA*) mechanism that uses `Off` to selectively retract
conditions is defined in `Studies/VanDerSandtMaier2003.lean` as
`LDRS.directedRA`.

## See also: `Semantics/Composition/Layered.BiLayered`

`Semantics/Composition/Layered.lean` defines a 2-layer Prop-valued
sibling `BiLayered W` (atIssue / notAtIssue, both `W → Prop`) with
[martinez-vera-2026]'s composition rules I/II/III. Use `LayeredProp`
when LDRT's offensive-layer machinery is needed; use `BiLayered` when
the analysis only distinguishes at-issue from not-at-issue and operates
over `Set W` (verum, evidential illocution, biased polar questions). A
future `Layered n` parameterised refactor would consolidate the two.
-/

set_option linter.dupNamespace false

namespace Semantics.ContentLayer

/-- The layer of a semantic contribution, determining its discourse behavior.

    [van-der-sandt-maier-2003] introduce this three-way distinction in
    Layered DRT, but the classification is framework-independent: it captures
    a difference in how content projects, how it can be challenged, and what
    denial can target. -/
inductive ContentLayer where
  /-- Backgrounded precondition. Projects past negation, questions, modals.
      Targeted by "Hey wait a minute!" challenge.
      Example: "stop" presupposes prior state; "the king" presupposes existence. -/
  | presupposition
  /-- Free/assertoric content. Addresses the QUD directly.
      Targeted by direct denial ("No, that's not true").
      Example: "The king is bald" asserts baldness. -/
  | atIssue
  /-- Enrichment beyond literal truth conditions.
      Covers both scalar implicature (category D: "possible" implicates "not
      necessary") and connotation/register (category E: "steed" connotes
      formality). The paper groups both under `imp` as non-truth-conditional
      material targetable by denial.
      Example: "It's not POSSIBLE — it's NECESSARY" (29b). -/
  | implicature
  deriving DecidableEq, Repr, Inhabited

-- ════════════════════════════════════════════════════
-- § Layered Propositions
-- ════════════════════════════════════════════════════

/-- A full layered proposition: content at each layer.

    Generalizes `PrProp` from 2 layers to 3. When `implicature` is trivially
    true, a `LayeredProp` degenerates to a `PrProp`. -/
structure LayeredProp (W : Type*) where
  /-- Presuppositional content (must hold for definedness). -/
  presupposition : W → Bool
  /-- At-issue/assertoric content. -/
  atIssue : W → Bool
  /-- Implicature content (enrichment beyond truth conditions). Trivially
      true by default: most utterances carry no relevant implicature, just
      as `PrProp.ofProp` sets presupposition to `λ _ => True`. -/
  implicature : W → Bool := λ _ => true

/-- Access a layer's content by its tag. -/
def LayeredProp.get {W : Type*} (lp : LayeredProp W) : ContentLayer → (W → Bool)
  | .presupposition => lp.presupposition
  | .atIssue => lp.atIssue
  | .implicature => lp.implicature

-- ════════════════════════════════════════════════════
-- § Bridge to PrProp
-- ════════════════════════════════════════════════════

open Semantics.Presupposition in
/-- Project a `LayeredProp` to a `PrProp` by discarding the implicature layer.

    This is the canonical projection: `PrProp` is the 2-layer special case
    where implicature is invisible. -/
def LayeredProp.toPrProp {W : Type*} (lp : LayeredProp W) : PrProp W :=
  { presup := fun w => lp.presupposition w = true
  , assertion := fun w => lp.atIssue w = true }

open Semantics.Presupposition Classical in
/-- Lift a `PrProp` to a `LayeredProp` with trivially true implicature.

    This is the canonical embedding: every `PrProp` is a `LayeredProp` with
    no implicature content. Noncomputable because Prop → Bool requires
    classical decidability. -/
noncomputable def LayeredProp.ofPrProp {W : Type*} (p : PrProp W) : LayeredProp W :=
  { presupposition := fun w => if p.presup w then true else false
  , atIssue := fun w => if p.assertion w then true else false
  , implicature := λ _ => true }

open Semantics.Presupposition Classical in
/-- The round-trip `PrProp → LayeredProp → PrProp` is the identity.

    This confirms that `PrProp` embeds faithfully into `LayeredProp`:
    no information is lost or added in the embedding. -/
theorem LayeredProp.roundtrip_prprop {W : Type*} (p : PrProp W) :
    (LayeredProp.ofPrProp p).toPrProp = p := by
  ext w
  · simp only [ofPrProp, toPrProp]
    by_cases h : p.presup w <;> simp [h]
  · simp only [ofPrProp, toPrProp]
    by_cases h : p.assertion w <;> simp [h]

-- ════════════════════════════════════════════════════
-- § Offensive Layers (Denial Targeting)
-- ════════════════════════════════════════════════════

/-- Layer `l` of `φ` is offensive with respect to a correction when no world
    satisfies both the layer's content and the correction.

    Off(φ, K) from [van-der-sandt-maier-2003]: the offensive layers are
    those whose content is inconsistent with the correction context. In
    propositional denial, only `fr` is offensive; in presuppositional denial,
    `pr` (and `fr`) are offensive; in implicature denial, `imp` is offensive. -/
def isOffensive {W : Type*} (φ : LayeredProp W) (l : ContentLayer)
    (correction : W → Bool) (worlds : List W) : Bool :=
  !(worlds.any λ w => φ.get l w && correction w)

/-- Collect all offensive layers of `φ` with respect to a correction. -/
def offensiveLayers {W : Type*} (φ : LayeredProp W)
    (correction : W → Bool) (worlds : List W) : List ContentLayer :=
  [.presupposition, .atIssue, .implicature].filter λ l =>
    isOffensive φ l correction worlds

/-- A non-offensive layer's content is consistent with the correction:
    some world satisfies both. -/
def isConsistent {W : Type*} (φ : LayeredProp W) (l : ContentLayer)
    (correction : W → Bool) (worlds : List W) : Bool :=
  worlds.any λ w => φ.get l w && correction w

/-- Consistency is the negation of offensiveness. -/
theorem consistent_iff_not_offensive {W : Type*} (φ : LayeredProp W)
    (l : ContentLayer) (correction : W → Bool) (worlds : List W) :
    isConsistent φ l correction worlds = !isOffensive φ l correction worlds := by
  simp only [isConsistent, isOffensive, Bool.not_not]

-- ════════════════════════════════════════════════════
-- § Worked Examples: Off in Action
-- ════════════════════════════════════════════════════

/-! ### Example 1: King of France (30)

"The king of France is bald" has:
- `pr`: France has a king (definite presupposition)
- `fr`: The king is bald (at-issue content)
- `imp`: trivially true (no implicature)

Two corrections disambiguate the denial:
- "He has a full head of hair" → propositional denial (only `fr` offensive)
- "France does not have a king" → presuppositional denial (`pr` and `fr` both offensive)
-/

private inductive KFWorld | kingBald | kingHairy | noKing1 | noKing2
  deriving DecidableEq, Repr

private def kfPresup : KFWorld → Bool
  | .kingBald | .kingHairy => true | _ => false

private def kfAssert : KFWorld → Bool
  | .kingBald => true | _ => false

private def kfProp : LayeredProp KFWorld :=
  { presupposition := kfPresup, atIssue := kfAssert }

private def kfWorlds : List KFWorld := [.kingBald, .kingHairy, .noKing1, .noKing2]

/-- Propositional denial: correction "he has hair" conflicts with `fr` only.

    The presupposition (king exists) is consistent with the correction
    (world `kingHairy` satisfies both), so `pr` is NOT offensive. But no
    world is both bald and hairy, so `fr` IS offensive.

    Corresponds to the standard propositional-denial reading of (30). -/
theorem kf_propositional_denial :
    offensiveLayers kfProp (λ w => w == .kingHairy) kfWorlds = [.atIssue] := by
  native_decide

/-- Presuppositional denial: correction "no king exists" conflicts with
    both `pr` and `fr`.

    No world has both "king exists" and "no king exists," so `pr` is
    offensive. No world is both "bald" and "no king," so `fr` is ALSO
    offensive — the assertion "falls with" the presupposition.

    Corresponds to (30b): "The king of France is NOT bald — France does
    not have a king." -/
theorem kf_presuppositional_denial :
    offensiveLayers kfProp (λ w => w == .noKing1 || w == .noKing2) kfWorlds
    = [.presupposition, .atIssue] := by
  native_decide

/-! ### Example 2: Possibility → Necessity (29)

"It is possible that the pope is right" has:
- `pr`: trivially true
- `fr`: ◇p (it is possible)
- `imp`: ¬□p (not necessary — the scalar implicature of "possible")

Correction: "It is NECESSARY that the pope is right" (□p).
Only `imp` is offensive: ◇p is consistent with □p (necessity entails
possibility), but ¬□p contradicts □p.
-/

private inductive ModalW | possNotNec | nec
  deriving DecidableEq, Repr

private def modalProp : LayeredProp ModalW :=
  { presupposition := λ _ => true
  , atIssue := λ _ => true         -- ◇p holds in both worlds
  , implicature := λ              -- ¬□p: "merely possible, not necessary"
      | .possNotNec => true
      | .nec => false }

private def modalWorlds : List ModalW := [.possNotNec, .nec]

/-- Implicature denial: correction "it is necessary" conflicts with `imp` only.

    The presupposition (trivially true) and at-issue content (◇p) are both
    consistent with the correction (□p entails ◇p). Only the scalar
    implicature (¬□p) conflicts.

    Corresponds to (29b): "It is not POSSIBLE, it is NECESSARY that the
    pope is right." -/
theorem modal_implicature_denial :
    offensiveLayers modalProp (λ w => w == .nec) modalWorlds
    = [.implicature] := by
  native_decide

/-! ### `BiLayered`: 2-layer ⟨A, N⟩ Prop-valued sibling

A `Prop`-valued 2-layer sibling of `LayeredProp` ([martinez-vera-2026],
inheriting the percolation discipline of [potts-2005] and the at-issue
proposal / appositive imposition split of [anderbois-brasoveanu-henderson-2015]):
the at-issue layer is the proffered content, the not-at-issue layer
backgrounds presuppositions, conventional implicatures, and evidential
commitments — collapsing `LayeredProp`'s `presupposition` and
`implicature` layers into a single `notAtIssue`. The substrate stays
propositional (`W → Prop`) because the consumers (verum studies,
evidential illocution, biased polar questions) operate over `Set W`.

| Rule | When to use | At-issue layer | Not-at-issue layer |
|------|-------------|----------------|--------------------|
| I    | β has trivial NAI; α brings NAI | `α.A β.A` | `α.N β.A` |
| II   | both α and β bring NAI | `α.A β.A` | `α.N β.A ∧ β.N` |
| III  | α is illocutionary, takes the full ⟨A, N⟩ pair | (full pair handed to α) | (full pair handed to α) |
-/

/-- A 2-layer ⟨A, N⟩ proposition. Trivially-true `notAtIssue` is the
default — most expressions add no not-at-issue content, so the empty
case should be cheap to construct. -/
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

/-- [martinez-vera-2026] Composition rule I: β has empty NAI; α brings
NAI. The new at-issue layer is `α.A β.A`; the new NAI is `α.N β.A`. -/
def composeI (atFn naiFn : (W → Prop) → (W → Prop)) (β : BiLayered W) :
    BiLayered W :=
  { atIssue := atFn β.atIssue, notAtIssue := naiFn β.atIssue }

/-- [martinez-vera-2026] Composition rule II: both α and β bring NAI.
The new NAI accumulates `α.N β.A ∧ β.N`. -/
def composeII (atFn naiFn : (W → Prop) → (W → Prop)) (β : BiLayered W) :
    BiLayered W :=
  { atIssue := atFn β.atIssue
  , notAtIssue := fun w => naiFn β.atIssue w ∧ β.notAtIssue w }

/-- [martinez-vera-2026] Composition rule III: an illocutionary operator
takes the full ⟨A, N⟩ pair from β and returns a new pair. -/
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

/-- Composition I subsumes Composition II when β.N is trivially true:
the extra `∧ True` conjunct collapses. The formal sense in which
rule II generalises rule I. -/
theorem composeI_eq_composeII_on_trivial_naiFn {W : Type*}
    (atFn naiFn : (W → Prop) → (W → Prop)) (β : BiLayered W)
    (hβ : β.notAtIssue = fun _ => True) :
    composeI atFn naiFn β = composeII atFn naiFn β := by
  ext w
  · rfl
  · simp [composeI, composeII, hβ]

end Semantics.ContentLayer
