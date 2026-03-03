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

| Layer | Label | Projection | Denial target | QUD-relevant |
|-------|-------|------------|---------------|--------------|
| Presupposition | `pr` | Projects by default | "Hey wait a minute!" | No |
| At-issue | `fr` | Does not project | "No, that's not true" | Yes |
| Implicature | `imp` | Cancelable | "No, I didn't mean..." | Derived |

## Design Note

`ContentLayer` lives in `Core/Semantics/` because it generalizes `PrProp`.
Bridges to `Core/Discourse/AtIssueness` and `Phenomena/Presupposition/
ProjectiveContent.Challengeability` live downstream in bridge files,
preserving the independence of `Core/Semantics/` and `Core/Discourse/`.
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
  /-- Pragmatically derived enrichment. Cancelable, does not project.
      Targeted by corrective denial ("No, I didn't mean to imply...").
      Example: "bachelor" implicates eligible/available (not just unmarried). -/
  | implicature
  deriving DecidableEq, Repr, BEq, Inhabited

-- ════════════════════════════════════════════════════
-- § Layered Propositions
-- ════════════════════════════════════════════════════

/-- A proposition tagged with its content layer.
    The basic building block of layered semantic representations. -/
structure Layered (W : Type*) where
  layer : ContentLayer
  content : W → Bool

/-- A full layered proposition: content at each layer.

    Generalizes `PrProp` from 2 layers to 3. When `implicature` is trivially
    true, a `LayeredProp` degenerates to a `PrProp`. -/
structure LayeredProp (W : Type*) where
  /-- Presuppositional content (must hold for definedness). -/
  presupposition : W → Bool
  /-- At-issue/assertoric content. -/
  atIssue : W → Bool
  /-- Implicature content (pragmatic enrichment). Trivially true by default,
      reflecting the fact that most utterances don't carry conventional
      implicatures relevant to their truth conditions. -/
  implicature : W → Bool := λ _ => true

/-- Access a layer's content by its tag. -/
def LayeredProp.get {W : Type*} (lp : LayeredProp W) : ContentLayer → (W → Bool)
  | .presupposition => lp.presupposition
  | .atIssue => lp.atIssue
  | .implicature => lp.implicature

/-- Decompose a layered proposition into its tagged components. -/
def LayeredProp.layers {W : Type*} (lp : LayeredProp W) : List (Layered W) :=
  [ ⟨.presupposition, lp.presupposition⟩
  , ⟨.atIssue, lp.atIssue⟩
  , ⟨.implicature, lp.implicature⟩ ]

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
    `pr` is offensive; in implicature denial, `imp` is offensive. -/
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

end Core.Semantics.ContentLayer
