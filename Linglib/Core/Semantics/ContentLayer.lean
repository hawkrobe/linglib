import Linglib.Core.Semantics.Presupposition

/-!
# Content Layers
@cite{van-der-sandt-maier-2003}

Semantic content is stratified into layers that determine its discourse
behavior: how it projects, what denial can target, and whether it
addresses the QUD.

@cite{van-der-sandt-maier-2003} propose Layered DRT (LDRT), where every DRS
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

`ContentLayer` lives in `Core/Semantics/` because it generalizes `PrProp`.
Bridges to `Core/Discourse/AtIssueness` and `Phenomena/Presupposition/
ProjectiveContent.Challengeability` live downstream in bridge files,
preserving the independence of `Core/Semantics/` and `Core/Discourse/`.

## Scope

This module captures the layer taxonomy and the `Off` function (which
layers are offensive = inconsistent with a correction). It does NOT
capture the full directed reverse anaphora (RA*) mechanism, which
requires DRT resolution infrastructure (binding, accommodation,
subordination) that is not yet implemented.
-/

set_option linter.dupNamespace false

namespace Core.Semantics.ContentLayer

/-- The layer of a semantic contribution, determining its discourse behavior.

    @cite{van-der-sandt-maier-2003} introduce this three-way distinction in
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
  deriving DecidableEq, Repr, BEq, Inhabited

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
      as `PrProp.ofBProp` sets presupposition to `λ _ => true`. -/
  implicature : W → Bool := λ _ => true

/-- Access a layer's content by its tag. -/
def LayeredProp.get {W : Type*} (lp : LayeredProp W) : ContentLayer → (W → Bool)
  | .presupposition => lp.presupposition
  | .atIssue => lp.atIssue
  | .implicature => lp.implicature

-- ════════════════════════════════════════════════════
-- § Bridge to PrProp
-- ════════════════════════════════════════════════════

open Core.Presupposition in
/-- Project a `LayeredProp` to a `PrProp` by discarding the implicature layer.

    This is the canonical projection: `PrProp` is the 2-layer special case
    where implicature is invisible. -/
def LayeredProp.toPrProp {W : Type*} (lp : LayeredProp W) : PrProp W :=
  { presup := lp.presupposition
  , assertion := lp.atIssue }

open Core.Presupposition in
/-- Lift a `PrProp` to a `LayeredProp` with trivially true implicature.

    This is the canonical embedding: every `PrProp` is a `LayeredProp` with
    no implicature content. -/
def LayeredProp.ofPrProp {W : Type*} (p : PrProp W) : LayeredProp W :=
  { presupposition := p.presup
  , atIssue := p.assertion
  , implicature := λ _ => true }

open Core.Presupposition in
/-- The round-trip `PrProp → LayeredProp → PrProp` is the identity.

    This confirms that `PrProp` embeds faithfully into `LayeredProp`:
    no information is lost or added in the embedding. -/
theorem LayeredProp.roundtrip_prprop {W : Type*} (p : PrProp W) :
    (LayeredProp.ofPrProp p).toPrProp = p := rfl

-- ════════════════════════════════════════════════════
-- § Offensive Layers (Denial Targeting)
-- ════════════════════════════════════════════════════

/-- Layer `l` of `φ` is offensive with respect to a correction when no world
    satisfies both the layer's content and the correction.

    Off(φ, K) from @cite{van-der-sandt-maier-2003}: the offensive layers are
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
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

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

end Core.Semantics.ContentLayer
