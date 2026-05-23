import Linglib.Theories.Pragmatics.Expressives.Basic
import Mathlib.Data.Set.Basic

/-!
# Mixed Quotation
@cite{kirk-giannini-2024}

Formal apparatus for overt and covert mixed quotation, following
Kirk-Giannini 2024 "Covert mixed quotation" (Semantics & Pragmatics 17).

## Core Idea

Mixed quotation is a compositional interaction between pure quotation
and a covert mixed quotation operator 𝔐. A mixed-quoted expression
simultaneously:
1. **Used**: contributes its at-issue semantic value to composition
2. **Mentioned**: peripherally entails that some salient speaker produced
   an utterance of that expression

The theory introduces four covert operators:
- **𝔐** (mixed quotation): at-issue ⟨*⟩ meaning + peripheral R attribution
- **↓** (shunting): moves peripheral content to the at-issue dimension
- **†** (diagonalizer): shifts ⟨*⟩ to evaluate at the world of evaluation
- **𝔄** (appropriateness): modalizes peripheral content via ◆

These operators unify five phenomena: CI projection failure, c-monsters,
metalinguistic negation, metalinguistic negotiation, and "in a sense"
constructions.

## Connection to Existing Infrastructure

The `TwoDimProp` type from @cite{potts-2005} provides the at-issue ×
peripheral carrier. `pureQuote` (added to `TwoDimProp`) blocks CI
projection under quotation. The operators here compose over `TwoDimProp`.

The quotative interpretation function ⟨*⟩ — implemented as `QuotInterp`
below — is from @cite{shan-2010}. K-G writes (paper p.12, p.15):
"Drawing on Shan, I implement this proposal about the at-issue
contribution of mixed-quoted items using a purpose-built quotative
interpretation function ⟨*⟩." `(∗)` is therefore Shan's; K-G's
contribution is the covert apparatus 𝔐, ↓, †, 𝔄 layered on top.

## Flat (`TwoDimProp`) vs. Layered (`MQProp`) Model

Two carriers are exposed:

- **Flat `TwoDimProp`** (at-issue × ci): Potts 2005's original
  bi-dimensional architecture. `applyApprop` REPLACES the ci dimension
  with appropriateness content — the original R-attribution from 𝔐
  is overwritten when 𝔄 fires. Sufficient for at-issue truth-conditional
  predictions; cannot record that the utterance attribution survives
  embedding.

- **Layered `MQProp`** (at-issue × R-content × appropContent): refines
  the peripheral dimension into two distinct layers. `applyMQ` writes
  to R; `applyApprop` writes to ◆; `shunt` moves ◆ to at-issue; `neg`
  preserves both peripheral layers. Crown theorem
  `full_chain_preserves_rContent`: R survives the full
  𝔐 → 𝔄 → ↓ → ¬ chain.

**When to use which.** Flat for at-issue-truth-conditional predictions
where R is irrelevant (e.g. LoGuercio2025's CI work). Layered when the
prediction is about R-survival or when both peripheral dimensions
matter independently (K-G §3 metalinguistic negation, §1 strip-then-mix
observation that 𝔐 introduces R-attribution while 𝔄 leaves it intact).

Bridge: `MQProp.toFlat` projects the layered model down by discarding
R-content and using ◆-content as the flat ci. `flat_agreement_atIssue`
and `flat_loses_rContent` quantify the agreement and the information
loss of the projection.
-/

set_option autoImplicit false

namespace Semantics.Quotation

open Pragmatics.Expressives (TwoDimProp)

-- ════════════════════════════════════════════════════
-- § Quotative Interpretation
-- ════════════════════════════════════════════════════

/-- The quotative interpretation function ⟨*⟩.

    Maps an expression `q`, a world of utterance `w₁`, and a speaker `s`
    to the extension of `q` as uttered by `s` at `w₁`, evaluated at
    world of evaluation `w₂`.

    `⟦⟨*⟩⟧(q, w₁, s, w₂) = χ` where `χ` is the extension at `w₂` of
    the intension contributed by an utterance of `q` by `s` at `w₁`. -/
abbrev QuotInterp (Expr Speaker W : Type) := Expr → W → Speaker → W → Prop

/-- The utterance relation R.

    `R(s, u, q, w)` holds iff speaker `s` produced utterance `u` of
    expression `q` at world `w`. Introduced peripherally by 𝔐 and
    resolved as a discourse anaphor. -/
abbrev UttRel (Speaker Utt Expr W : Type) := Speaker → Utt → Expr → W → Prop

-- ════════════════════════════════════════════════════
-- § The Mixed Quotation Operator 𝔐
-- ════════════════════════════════════════════════════

/-- A mixed quotation context: the discourse-anaphoric parameters and
    interpretation functions needed to evaluate mixed quotation.

    The speaker `sx` and utterance `ux` are free variables resolved by
    discourse anaphora — they pick out the salient individual who produced
    the quoted material and the utterance event in which they did so. -/
structure MQContext (W Expr Speaker Utt : Type) where
  /-- Quotative interpretation function ⟨*⟩ -/
  interp : QuotInterp Expr Speaker W
  /-- Utterance relation R -/
  uttRel : UttRel Speaker Utt Expr W
  /-- Anaphorically retrieved speaker -/
  sx : Speaker
  /-- Anaphorically retrieved utterance -/
  ux : Utt
  /-- World of context -/
  wc : W

/-- Apply the mixed quotation operator 𝔐 to an expression.

    Returns a `TwoDimProp` with:
    - at-issue: `⟨q⟩(wc)(sx)` — the extension as used by the speaker
      at the world of context
    - peripheral: `R(sx, ux, q)` — the speaker produced this utterance

    This is the core of the theory: mixed quotation arises compositionally
    from these two semantic contributions of 𝔐. -/
def MQContext.applyMQ {W Expr Speaker Utt : Type} (ctx : MQContext W Expr Speaker Utt)
    (q : Expr) : TwoDimProp W :=
  { atIssue := ctx.interp q ctx.wc ctx.sx
  , ci := ctx.uttRel ctx.sx ctx.ux q }

/-- Projection of `applyMQ` onto the at-issue dimension: ⟨*⟩(q)(wc)(sx). -/
@[simp] theorem MQContext.applyMQ_atIssue {W Expr Speaker Utt : Type}
    (ctx : MQContext W Expr Speaker Utt) (q : Expr) :
    (ctx.applyMQ q).atIssue = ctx.interp q ctx.wc ctx.sx := rfl

/-- Projection of `applyMQ` onto the peripheral dimension: R(sx, ux, q). -/
@[simp] theorem MQContext.applyMQ_ci {W Expr Speaker Utt : Type}
    (ctx : MQContext W Expr Speaker Utt) (q : Expr) :
    (ctx.applyMQ q).ci = ctx.uttRel ctx.sx ctx.ux q := rfl

-- ════════════════════════════════════════════════════
-- § The Shunting Operator ↓
-- ════════════════════════════════════════════════════

/-- The shunting operator ↓: moves peripheral content to the at-issue
    dimension by conjoining it with at-issue content.

    After shunting, the at-issue content becomes `p.atIssue ∧ p.ci`
    and peripheral content becomes trivial.

    This operator is independently motivated (@cite{potts-2007},
    McCready 2010) and is what allows peripheral content from mixed
    quotation to interact with higher at-issue operators like negation
    and conditionals. In the Writer monad architecture for CI effects
    (see `Semantics.Composition.Effects.twoDimToWriter`),
    shunting corresponds to running the Writer by folding the CI log
    into the value via conjunction (see `runCIWriter` and
    `runCIWriter_twoDim` in `Semantics.Composition.Effects`). -/
def shunt {W : Type} (p : TwoDimProp W) : TwoDimProp W :=
  { atIssue := λ w => p.atIssue w ∧ p.ci w
  , ci := λ _ => True }

/-- Shunting conjoins both dimensions into at-issue. -/
@[simp] theorem shunt_atIssue {W : Type} (p : TwoDimProp W) (w : W) :
    (shunt p).atIssue w ↔ (p.atIssue w ∧ p.ci w) := Iff.rfl

/-- Shunting trivializes peripheral content. -/
@[simp] theorem shunt_ci {W : Type} (p : TwoDimProp W) (w : W) :
    (shunt p).ci w := trivial

/-- Shunting is idempotent on the at-issue dimension: once peripheral
    content has been consumed, shunting again has no effect. -/
theorem shunt_atIssue_idempotent {W : Type} (p : TwoDimProp W) (w : W) :
    (shunt (shunt p)).atIssue w ↔ (shunt p).atIssue w := by
  simp [shunt]

-- ════════════════════════════════════════════════════
-- § The Diagonalizer †
-- ════════════════════════════════════════════════════

/-- The diagonalizer †: shifts the quotative interpretation so that at
    the world of evaluation `w`, the expression's meaning is what it
    would be as uttered by the speaker at `w` (rather than at `wc`).

    This captures c-monstrous behavior without positing actual context
    monsters. "If Pluto were a planet" accesses the meaning 'planet'
    would have if conventions were different — because the diagonalizer
    evaluates `⟨planet⟩(w)(s)` at the counterfactual world `w` where
    conventions still classify Pluto as a planet.

    Formally: `†(f) = f*` where `f*(q)(w) = ⟨q⟩(w)(s)(w)` — the world
    of utterance and world of evaluation collapse. -/
def diagonalize {W Expr Speaker : Type}
    (interp : QuotInterp Expr Speaker W)
    (s : Speaker) (q : Expr) : W → Prop :=
  λ w => interp q w s w

/-- Diagonalization collapses world of utterance and evaluation. -/
@[simp] theorem diag_collapses_worlds {W Expr Speaker : Type}
    (interp : QuotInterp Expr Speaker W)
    (s : Speaker) (q : Expr) (w : W) :
    diagonalize interp s q w = interp q w s w := rfl

/--
**K-G's diagonalizer † with the ∃-over-speakers.**

The bare `diagonalize` above is parameterized on a single speaker — it
captures only the world-collapse half of K-G's footnote 22 definition
(paper p.26):

  † ⤳ λf. ∃s : f = λq. ⟨*⟩(q)(w_c)(s).f*

The `∃s` quantifies over speakers/communities producing the variant
function `f*` (the world-of-evaluation form `f*(s) := λq. ⟨*⟩(q)(w)(s)`).
This existential is what makes c-monsters work: "Pluto could have been a
planet" is true when there EXISTS a speaker whose use of 'planet'
includes Pluto under the diagonalized reading — not just when the actual
speaker's use does.

The bare `diagonalize` is the per-speaker witness; `diagonalizeKG` adds
the existential. Bridge: `diagonalizeKG_iff_exists_diagonalize`.
-/
def diagonalizeKG {W Expr Speaker : Type}
    (interp : QuotInterp Expr Speaker W) (q : Expr) : W → Prop :=
  λ w => ∃ s : Speaker, interp q w s w

/-- `diagonalizeKG` is the existential closure of `diagonalize` over speakers. -/
@[simp] theorem diagonalizeKG_iff_exists_diagonalize
    {W Expr Speaker : Type} (interp : QuotInterp Expr Speaker W)
    (q : Expr) (w : W) :
    diagonalizeKG interp q w ↔ ∃ s : Speaker, diagonalize interp s q w := Iff.rfl

/--
**K-G's footnote 22 well-definedness condition.**

For `f*` to be well-defined as a function (rather than a relation), no two
speakers may agree on extensions of all expressions at the world of
context `wc` while disagreeing on extensions at some other world.

Paper p.26 footnote: "I assume here that there are no two speakers or
linguistic communities which assign the same extensions to all expressions
in `w_c` but assign different extensions to some expressions in other
worlds."

This is a global structural property of `interp` — it's about how speakers
relate across worlds. Without it, the existential in `diagonalizeKG`
overgenerates (any two speakers can act as witnesses for incompatible
diagonal contents at the same world). K-G accepts this assumption to keep
the semantics deterministic; it is independently violable.
-/
def QuotInterp.fn22Wellformed {W Expr Speaker : Type}
    (interp : QuotInterp Expr Speaker W) (wc : W) : Prop :=
  ∀ s s' : Speaker, (∀ q w, interp q wc s w ↔ interp q wc s' w) →
    (∀ q w, interp q w s w ↔ interp q w s' w)

/--
Under fn22-wellformedness, speakers who agree on extensions at `wc`
across the entire vocabulary agree on diagonal extensions everywhere.
This is the substantive use of `fn22Wellformed`: it lifts wc-extensional
agreement to global agreement, which is what makes the existential in
`diagonalizeKG` deterministic.
-/
theorem diagonalizeKG_deterministic_under_fn22 {W Expr Speaker : Type}
    (interp : QuotInterp Expr Speaker W) (wc : W)
    (h : interp.fn22Wellformed wc) (s s' : Speaker)
    (hAgree : ∀ q w, interp q wc s w ↔ interp q wc s' w) :
    ∀ q w, diagonalize interp s q w ↔ diagonalize interp s' q w := by
  intro q w
  exact h s s' hAgree q w

-- ════════════════════════════════════════════════════
-- § The Appropriateness Operator 𝔄
-- ════════════════════════════════════════════════════

/-- An appropriateness standard: given a speaker and expression at a world,
    whether it is or would be appropriate for that speaker to use that
    expression.

    This is the semantic content of the appropriateness modal ◆ in
    Kirk-Giannini's system. The modal quantifies over an accessibility
    relation, but for finite models we represent the result directly. -/
abbrev AppropStandard (Speaker Expr W : Type) := Speaker → Expr → W → Prop

/-- The appropriateness operator 𝔄: replaces the peripheral content of a
    mixed-quoted expression with appropriateness content.

    In the paper's compositional chain, 𝔄 operates on 𝔐's output:
    𝔐(q) → 𝔄 → ↓ → ¬. The at-issue content from 𝔐 passes through
    unchanged; only the peripheral dimension is replaced with the
    proposition that the verbatim use of the expression is or would be
    appropriate. This is the key ingredient for metalinguistic negation:
    when ↓ shunts this appropriateness content to at-issue and negation
    scopes over the result, we get "not (p ∧ appropriate-to-say-q)". -/
def applyApprop {W Expr Speaker : Type}
    (approp : AppropStandard Speaker Expr W)
    (sx : Speaker) (q : Expr)
    (p : TwoDimProp W) : TwoDimProp W :=
  { atIssue := p.atIssue, ci := approp sx q }

/-- 𝔄 preserves at-issue content: it only replaces the peripheral dimension. -/
@[simp] theorem approp_preserves_atIssue {W Expr Speaker : Type}
    (approp : AppropStandard Speaker Expr W)
    (sx : Speaker) (q : Expr) (p : TwoDimProp W) :
    (applyApprop approp sx q p).atIssue = p.atIssue := rfl

/-- 𝔄 replaces the peripheral dimension with appropriateness content. -/
@[simp] theorem applyApprop_ci {W Expr Speaker : Type}
    (approp : AppropStandard Speaker Expr W)
    (sx : Speaker) (q : Expr) (p : TwoDimProp W) :
    (applyApprop approp sx q p).ci = approp sx q := rfl

-- ════════════════════════════════════════════════════
-- § Composition Theorems
-- ════════════════════════════════════════════════════

/-- Metalinguistic negation truth conditions.

    Negating a shunted appropriateness-enhanced mixed quotation yields:
    `¬(at-issue-meaning ∧ appropriate-to-use-expression)`.

    This is the core prediction for metalinguistic negation: "I didn't
    manage to trap two MONGEESE" is true iff it's not the case that
    (I managed to trap two mongooses AND it's appropriate to call them
    'mongeese'). Since the second conjunct is false (it's not appropriate),
    the negation is true even though I did manage to trap two mongooses. -/
theorem metalinguistic_neg_truth_conditions {W Expr Speaker Utt : Type}
    (ctx : MQContext W Expr Speaker Utt)
    (approp : AppropStandard Speaker Expr W)
    (q : Expr) (w : W) :
    (TwoDimProp.neg (shunt (applyApprop approp ctx.sx q (ctx.applyMQ q)))).atIssue w
    ↔ ¬(ctx.interp q ctx.wc ctx.sx w ∧ approp ctx.sx q w) := Iff.rfl

/-- The affirmed conjunct in metalinguistic negation.

    In "I didn't trap two MONGEESE — I trapped two MONGOOSES", the
    second clause entails the at-issue content of the first. So the
    negation is understood as targeting the appropriateness conjunct:
    it's not appropriate to use 'mongeese'. -/
theorem metalinguistic_neg_targets_appropriateness {W Expr Speaker Utt : Type}
    (ctx : MQContext W Expr Speaker Utt)
    (approp : AppropStandard Speaker Expr W)
    (q : Expr) (w : W)
    (h_true : ctx.interp q ctx.wc ctx.sx w)
    (h_inapprop : ¬approp ctx.sx q w) :
    (TwoDimProp.neg (shunt (applyApprop approp ctx.sx q (ctx.applyMQ q)))).atIssue w := by
  intro ⟨_, h⟩
  exact h_inapprop h

/-- Pure quotation composes with 𝔐: the expression is first purely
    quoted (stripping its original CI content), then 𝔐 re-introduces
    peripheral content attributing the utterance to the speaker.

    This explains why CI items (expressives, slurs, NRRCs) don't project
    out of indirect speech reports: the material is first pure-quoted
    (stripping CIs) before being mixed-quoted (adding speaker attribution). -/
theorem mixed_quot_strips_original_ci {W Expr Speaker Utt : Type}
    (ctx : MQContext W Expr Speaker Utt) (q : Expr)
    (originalCI : W → Prop) (w : W) :
    let quoted := TwoDimProp.pureQuote (TwoDimProp.withCI (ctx.interp q ctx.wc ctx.sx) originalCI)
    quoted.ci w := trivial

-- ════════════════════════════════════════════════════
-- § Two-Layer Peripheral Content
-- ════════════════════════════════════════════════════

/-! ## Two-Layer Peripheral Content

The flat `TwoDimProp` model has a single peripheral dimension, which
forces 𝔄 to *replace* the R-content with ◆-content. This breaks
Writer monotonicity: the log is overwritten rather than appended.

The non-monotonicity is an artifact of collapsing two genuinely distinct
peripheral layers into one field:

- **R-peripheral**: utterance attribution `R(s,u,q)`. Always projects
  to the discourse root. Never shunted. Never targeted by negation.
  Resolved as a discourse anaphor.
- **◆-peripheral**: appropriateness `◆(s,q)`. Can be shunted by ↓
  into the at-issue dimension. Targetable by negation after shunting.

In the two-layer model, 𝔐 writes to the R-layer and 𝔄 writes to the
◆-layer. No replacement — both layers are independently append-only.
The key structural results:

1. **Layer preservation**: each operator preserves the layer it doesn't
   target (R persists through 𝔄, ↓, ¬)
2. **Shunting conservation**: ↓ is information-conservative — total
   content across all layers is invariant under shunting
3. **Flat agreement**: the flat `TwoDimProp` model is a projection of
   the two-layer model that agrees on at-issue content
4. **Per-layer monotonicity**: each layer satisfies Writer-style
   append-only behavior
-/

/-- Mixed quotation proposition with two distinct peripheral layers.

    Refines `TwoDimProp` by separating the R-dimension (utterance
    attribution) from the ◆-dimension (appropriateness), each with
    different projection and interaction behavior. -/
private theorem and_comm_middle :
    ∀ (a b c : Prop), ((a ∧ c) ∧ b ∧ True) ↔ (a ∧ b ∧ c) := by intros; tauto

structure MQProp (W : Type) where
  /-- At-issue (truth-conditional) content -/
  atIssue : W → Prop
  /-- R-peripheral: utterance attribution. Projects universally. -/
  rContent : W → Prop
  /-- ◆-peripheral: appropriateness. Shuntable into at-issue. -/
  appropContent : W → Prop

namespace MQProp

variable {W Expr Speaker Utt : Type}

-- ────────────────────────────────────────────────────
-- Operators
-- ────────────────────────────────────────────────────

/-- 𝔐 on the two-layer type: at-issue ← ⟨*⟩(q), R-layer ← R(s,u,q),
    ◆-layer trivial (no appropriateness content yet). -/
@[reducible] def applyMQ (ctx : MQContext W Expr Speaker Utt) (q : Expr) : MQProp W :=
  { atIssue := ctx.interp q ctx.wc ctx.sx
  , rContent := ctx.uttRel ctx.sx ctx.ux q
  , appropContent := λ _ => True }

/-- 𝔄 on the two-layer type: writes to the ◆-layer only. R-content
    and at-issue are preserved — no log replacement. -/
@[reducible] def applyApprop (approp : AppropStandard Speaker Expr W)
    (sx : Speaker) (q : Expr) (p : MQProp W) : MQProp W :=
  { atIssue := p.atIssue
  , rContent := p.rContent
  , appropContent := λ w => p.appropContent w ∧ approp sx q w }

/-- ↓ on the two-layer type: conjoins ◆-content into at-issue.
    R-content is preserved — shunting is selective. -/
@[reducible] def shunt (p : MQProp W) : MQProp W :=
  { atIssue := λ w => p.atIssue w ∧ p.appropContent w
  , rContent := p.rContent
  , appropContent := λ _ => True }

/-- Negation on the two-layer type: negates at-issue only.
    Both peripheral layers are preserved. -/
@[reducible] def neg (p : MQProp W) : MQProp W :=
  { atIssue := λ w => ¬p.atIssue w
  , rContent := p.rContent
  , appropContent := p.appropContent }

-- ────────────────────────────────────────────────────
-- Layer preservation (per-layer monotonicity)
-- ────────────────────────────────────────────────────

/-- 𝔄 preserves R-content. -/
@[simp] theorem applyApprop_preserves_rContent (approp : AppropStandard Speaker Expr W)
    (sx : Speaker) (q : Expr) (p : MQProp W) :
    (p.applyApprop approp sx q).rContent = p.rContent := rfl

/-- 𝔄 preserves at-issue content. -/
@[simp] theorem applyApprop_preserves_atIssue (approp : AppropStandard Speaker Expr W)
    (sx : Speaker) (q : Expr) (p : MQProp W) :
    (p.applyApprop approp sx q).atIssue = p.atIssue := rfl

/-- 𝔄 appends appropriateness to ◆-content (no replacement). -/
@[simp] theorem applyApprop_appropContent (approp : AppropStandard Speaker Expr W)
    (sx : Speaker) (q : Expr) (p : MQProp W) (w : W) :
    (p.applyApprop approp sx q).appropContent w ↔ p.appropContent w ∧ approp sx q w :=
  Iff.rfl

/-- ↓ preserves R-content: shunting is selective. -/
@[simp] theorem shunt_preserves_rContent (p : MQProp W) :
    p.shunt.rContent = p.rContent := rfl

/-- ↓ conjoins ◆-content into at-issue. -/
@[simp] theorem shunt_atIssue (p : MQProp W) (w : W) :
    p.shunt.atIssue w ↔ p.atIssue w ∧ p.appropContent w := Iff.rfl

/-- ↓ trivializes ◆-content (the layer is "drained"). -/
@[simp] theorem shunt_appropContent (p : MQProp W) (w : W) :
    p.shunt.appropContent w := trivial

/-- ¬ preserves R-content. -/
@[simp] theorem neg_preserves_rContent (p : MQProp W) :
    p.neg.rContent = p.rContent := rfl

/-- ¬ preserves ◆-content. -/
@[simp] theorem neg_preserves_appropContent (p : MQProp W) :
    p.neg.appropContent = p.appropContent := rfl

/-- ¬ preserves both peripheral dimensions (combined ergonomic lemma
    bundling `neg_preserves_rContent` and `neg_preserves_appropContent`). -/
theorem neg_preserves_both_peripherals (p : MQProp W) :
    p.neg.rContent = p.rContent ∧ p.neg.appropContent = p.appropContent :=
  ⟨rfl, rfl⟩

/-- ¬ negates the at-issue dimension. -/
@[simp] theorem neg_atIssue (p : MQProp W) (w : W) :
    p.neg.atIssue w ↔ ¬ p.atIssue w := Iff.rfl

/-- 𝔐 produces ⟨*⟩(q)(wc)(sx) on the at-issue dimension. -/
@[simp] theorem applyMQ_atIssue (ctx : MQContext W Expr Speaker Utt) (q : Expr) :
    (MQProp.applyMQ ctx q).atIssue = ctx.interp q ctx.wc ctx.sx := rfl

/-- 𝔐 produces R(sx, ux, q) on the R-layer. -/
@[simp] theorem applyMQ_rContent (ctx : MQContext W Expr Speaker Utt) (q : Expr) :
    (MQProp.applyMQ ctx q).rContent = ctx.uttRel ctx.sx ctx.ux q := rfl

/-- 𝔐 leaves the ◆-layer trivial — appropriateness has not been written yet. -/
@[simp] theorem applyMQ_appropContent (ctx : MQContext W Expr Speaker Utt)
    (q : Expr) (w : W) :
    (MQProp.applyMQ ctx q).appropContent w := trivial

/-- R-content persists through the full metalinguistic negation chain
    𝔐 → 𝔄 → ↓ → ¬. The utterance attribution is never lost. -/
theorem full_chain_preserves_rContent
    (ctx : MQContext W Expr Speaker Utt)
    (approp : AppropStandard Speaker Expr W) (q : Expr) :
    ((MQProp.applyMQ ctx q).applyApprop approp ctx.sx q |>.shunt |>.neg).rContent
    = ctx.uttRel ctx.sx ctx.ux q := rfl

/-- **Metalinguistic negation truth conditions in the layered model.**
    The MQProp-side counterpart of the flat-model
    `Semantics.Quotation.metalinguistic_neg_truth_conditions`
    (line 219 above). At-issue content of the full chain is
    `¬(at-issue ∧ appropriate)`, identical to the flat model — but
    the layered model ALSO retains the R-attribution
    (per `full_chain_preserves_rContent`), which the flat model
    discards. -/
theorem metalinguistic_neg_truth_conditions
    (ctx : MQContext W Expr Speaker Utt)
    (approp : AppropStandard Speaker Expr W) (q : Expr) (w : W) :
    ((MQProp.applyMQ ctx q).applyApprop approp ctx.sx q |>.shunt |>.neg).atIssue w
    ↔ ¬(ctx.interp q ctx.wc ctx.sx w ∧ approp ctx.sx q w) := by
  -- The MQProp chain accumulates `True ∧ approp` in the ◆-layer;
  -- after shunt and neg, this differs from the flat target by a
  -- `True ∧ X ↔ X` simplification.
  simp [MQProp.applyMQ, MQProp.applyApprop, MQProp.shunt, MQProp.neg]

-- ────────────────────────────────────────────────────
-- Shunting conservation
-- ────────────────────────────────────────────────────

/-- **Shunting conservation.** The total information content — the
    conjunction of all three layers — is invariant under ↓.

    Shunting doesn't destroy ◆-content; it *relocates* it from the
    ◆-layer to the at-issue layer. The ◆-layer becomes trivial, but the
    information is preserved in the at-issue conjunction. No content is
    created or destroyed — only moved.

    This is the crown theorem of the two-layer analysis: it shows that
    the apparent non-monotonicity of the flat model is an illusion. When
    the layers are properly separated, every operation preserves total
    information (negation inverts at-issue, but that's intentional
    semantic content, not information loss). -/
theorem shunt_conserves (p : MQProp W) (w : W) :
    (p.shunt.atIssue w ∧ p.shunt.rContent w ∧ p.shunt.appropContent w)
    ↔ (p.atIssue w ∧ p.rContent w ∧ p.appropContent w) :=
  Semantics.Quotation.and_comm_middle
    (p.atIssue w) (p.rContent w) (p.appropContent w)

-- ────────────────────────────────────────────────────
-- Agreement with the flat model
-- ────────────────────────────────────────────────────

/-- Project the two-layer model to the flat `TwoDimProp` by discarding
    R-content and using ◆-content as the CI dimension.

    This projection is exact after 𝔄: the flat model's "replaced" CI
    is the ◆-layer of the two-layer model. The R-content, discarded
    here, is the information that the flat model loses. -/
def toFlat (p : MQProp W) : TwoDimProp W :=
  { atIssue := p.atIssue, ci := p.appropContent }

/-- The flat projection preserves at-issue content. -/
@[simp] theorem toFlat_atIssue (p : MQProp W) : p.toFlat.atIssue = p.atIssue := rfl

/-- The flat projection uses ◆-content as the CI dimension (R-content discarded). -/
@[simp] theorem toFlat_ci (p : MQProp W) : p.toFlat.ci = p.appropContent := rfl

/-- The full chain on the two-layer model agrees with the flat model
    on at-issue content. The two models diverge only in what happens
    to R-content: the layered model preserves it, the flat model
    discards it. -/
theorem flat_agreement_atIssue
    (ctx : MQContext W Expr Speaker Utt)
    (approp : AppropStandard Speaker Expr W) (q : Expr) (w : W) :
    ((MQProp.applyMQ ctx q).applyApprop approp ctx.sx q |>.shunt |>.neg).atIssue w
    ↔ (TwoDimProp.neg (Semantics.Quotation.shunt
        (Semantics.Quotation.applyApprop approp ctx.sx q
          (ctx.applyMQ q)))).atIssue w := by
  simp [TwoDimProp.neg, Semantics.Quotation.shunt,
        Semantics.Quotation.applyApprop, MQContext.applyMQ]

/-- What the flat model loses: R-content is present in the layered
    model but absent in the flat projection.

    After metalinguistic negation ("I didn't trap two MONGEESE"),
    the layered model records that the utterance 'mongeese' was produced
    (R is true). The flat model has no trace of this — the R-content
    was overwritten by ◆-content when 𝔄 was applied. -/
theorem flat_loses_rContent
    (ctx : MQContext W Expr Speaker Utt)
    (approp : AppropStandard Speaker Expr W) (q : Expr) :
    -- Layered model: R-content survives
    ((MQProp.applyMQ ctx q).applyApprop approp ctx.sx q |>.shunt |>.neg).rContent
      = ctx.uttRel ctx.sx ctx.ux q
    -- Flat model: no R-content field at all (only ci, which is now trivial after shunting)
    ∧ (TwoDimProp.neg (Semantics.Quotation.shunt
        (Semantics.Quotation.applyApprop approp ctx.sx q
          (ctx.applyMQ q)))).ci = (Semantics.Quotation.shunt
        (Semantics.Quotation.applyApprop approp ctx.sx q
          (ctx.applyMQ q))).ci := ⟨rfl, rfl⟩

end MQProp

end Semantics.Quotation
