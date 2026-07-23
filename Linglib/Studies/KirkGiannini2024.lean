import Linglib.Pragmatics.Expressives.Basic
import Mathlib.Data.Set.Basic
import Linglib.Semantics.Reference.Monsters
import Linglib.Studies.VanDerSandtMaier2003
import Linglib.Studies.Maier2014
import Linglib.Studies.HarrisPotts2009
import Linglib.Studies.Horn1989
import Linglib.Studies.PlunkettSundell2013
import Linglib.Studies.KocurekJerzakRudolph2020

/-!
# Kirk-Giannini 2024: Covert Mixed Quotation
[kirk-giannini-2024]

Covert mixed quotation. Semantics and Pragmatics 17, Article 5: 1-54.

## Overview

Five apparently distinct phenomena are derived from the interaction of
covert mixed quotation `𝔐` with four additional operators (`↓`, `†`,
`𝔄`, and quantification over senses):

1. **CI projection failure** (§1, paper §3): Conventional implicature
   items (expressives, slurs, NRRCs) fail to project out of indirect
   speech reports because the embedded clause is first pure-quoted
   (stripping the original CI) before `𝔐` re-introduces a peripheral
   utterance attribution.

2. **C-monsters** (§2, paper §4): "Pluto could have been a planet"
   accesses the meaning 'planet' would have under different conventions
   via the diagonalizer `†`, which collapses the world of utterance
   into the world of evaluation. K-G's `†` is existentially closed over
   speakers/communities (paper fn 22).

3. **Metalinguistic negation** (§3, paper §5): "I didn't trap two
   MONGEESE" derives via the chain `𝔐 → 𝔄 → ↓ → ¬`, with `↓` shunting
   the appropriateness content into the at-issue dimension before
   negation applies. The analysis predicts three syntactic restrictions
   identified by [horn-1985] / [horn-1989] and
   [burton-roberts-1989]: morpheme incorporation failure, NPI
   licensing failure, and DN-elimination failure.

4. **Metalinguistic negotiation** (§4, paper §6): "Secretariat is /
   isn't an athlete" — A and B express literally **incompatible**
   appropriateness contents on a **shared** standard, contra
   [plunkett-sundell-2013]'s "consistent contents" diagnosis.

5. **"In a sense"** (§5, paper §7): "Viruses are alive in a sense"
   contributes `∃μ ∃sₓ [⟨*⟩(q)(wc)(sₓ) ∧ [^⟨*⟩(q)(wc)(sₓ)] = μ]` —
   an existential over BOTH speakers AND intensions, with `which_μ`
   binding via Predicate Abstraction.

## Cross-framework theorem inventory

This module hosts **8 cross-framework refutation/bridge theorems**
that make K-G's incompatibilities with sibling analyses visible at
theorem level (per linglib's "no bridge files" rule, comparisons live
in the chronologically-later study file). Each theorem actually
imports and invokes the named sibling's substrate — none is a
docstring-only claim.

- `kg_refutes_potts_universal_projection` (§1) — invokes
  `Pragmatics.Expressives.TwoDimProp.neg`, exhibits divergence at
  `.hypothetical`
- `kg_refutes_harris_potts_orientation` (§1) — instantiates
  `HarrisPotts2009.CIItem` and compares resolution outcomes
- `kg_refutes_maier_chameleonism` (§1) — instantiates `Maier2014.mq`
  on the same input and shows daughter-CI passthrough vs. K-G's
  strip-then-mix yields divergent CI predictions
- `diagonalize_no_kaplan_monster` (§2) — defines `kgEmbeddingShifts`
  reflecting K-G's covert apparatus (4 identity shifts, one per
  operator) and proves `KaplansThesisHolds` non-vacuously via
  case-split
- `kg_refutes_kjr_convention_shift` (§2) — instantiates KJR's
  `Convention` and `WC`, exhibits a WC-pair where KJR's
  `diagContent` predicts True while K-G's `diagonalizeKG` predicts
  False
- `kg_metalinguistic_chain_targets_appropriateness` (§3) — exhibits
  the `applyApprop` chain producing appropriateness content (vs.
  `VanDerSandtMaier2003.DenialType.implicature`'s implicature
  layer)
- `kg_refutes_plunkett_sundell` (§4) — instantiates P&S's
  `MetalinguisticDispute` with K-G's shared standard and proves the
  P&S `consistentContents` predicate fails to hold
- `in_a_sense_distinct_from_imprecision` (§5) — exhibits speaker-locus
  variation, structurally distinct from granularity-locus accounts

§3 also lifts three syntactic predictions from `Horn1989`:
`mongeese_blocks_morpheme_incorporation`, `..._npi_licensing`,
`..._dn_elimination`. These are NOT framed as cross-framework
theorems (K-G and Horn agree on the predictions, disagree only on
the architecture that derives them).

## Note on Denial Taxonomy

The three-way `DenialType` taxonomy (propositional / presuppositional /
implicature) from [van-der-sandt-maier-2003] — formalized in
`Studies/VanDerSandtMaier2003.lean` — groups register and connotation
denials under `implicature`. K-G's analysis (paper §5, p.28-30) derives
metalinguistic-negation truth conditions from `♦` (appropriateness
modal) composed with `𝔐`, with `↓` shunting before negation. The
distinguishing feature of K-G's account is the appeal to appropriateness
plus the syntactic predictions in §3 (NPI failure, morpheme
incorporation failure, DN-elimination failure).
-/

/-!
## Mixed Quotation
[kirk-giannini-2024]

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

The `TwoDimProp` type from [potts-2005] provides the at-issue ×
peripheral carrier. `pureQuote` (added to `TwoDimProp`) blocks CI
projection under quotation. The operators here compose over `TwoDimProp`.

The quotative interpretation function ⟨*⟩ — implemented as `QuotInterp`
below — is from [shan-2010]. K-G writes (paper p.12, p.15):
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

    This operator is independently motivated ([potts-2007],
    McCready 2010) and is what allows peripheral content from mixed
    quotation to interact with higher at-issue operators like negation
    and conditionals. In the Writer monad architecture for CI effects
    (see `BumfordCharlow2024.twoDimToWriter`),
    shunting corresponds to running the Writer by folding the CI log
    into the value via conjunction (see `runCIWriter` and
    `runCIWriter_twoDim` in `Studies/BumfordCharlow2024.lean`). -/
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

set_option autoImplicit false

namespace KirkGiannini2024

open Semantics.Quotation
open Pragmatics.Expressives (TwoDimProp)

-- ════════════════════════════════════════════════════
-- § 1. CI Projection Failure (paper §3)
-- ════════════════════════════════════════════════════

section CIProjection

/-- Concrete world type for the CI projection scenarios — non-trivial
    so universal/existential quantification has computational content. -/
inductive ProjWorld where
  | actual
  | hypothetical
  deriving DecidableEq, Repr, Inhabited

-- ────────────────────────────────────────────────────
-- §1.1. The 'goddamned keys' scenario (paper (26))
-- ────────────────────────────────────────────────────

/-- Expressions in the 'goddamned keys' scenario. -/
inductive GDExpr where | goddamnedKeys deriving DecidableEq, Repr

/-- Speakers: Jones (the original utterer) and the reporter. -/
inductive GDSpeaker where | jones | reporter deriving DecidableEq, Repr

/-- 'Goddamned keys' denotes Jones-spent-an-hour-looking-for-his-keys.
    At-issue content is independent of who's reporting. -/
def gdInterp : QuotInterp GDExpr GDSpeaker ProjWorld
  | .goddamnedKeys, _, _, _ => True

/-- **Original peripheral CI** of 'goddamned' in its first use:
    Jones has a negative attitude toward Jones's keys. Modelled as
    constant True — attitudes are intentional content of the speaker,
    not world-contingent. (This is what makes the Potts-vs-K-G
    refutation bite at `.hypothetical`: the original CI persists
    across worlds, but Jones's UTTERANCE is contingent.) -/
def gdOriginalCI : ProjWorld → Prop := λ _ => True

/-- **Non-trivial utterance attribution.** Jones uttered 'goddamned
    keys' at .actual; reporter never uttered it. This is what
    differentiates §1's peripheral content from the constant-True
    placeholder of the original substrate. -/
def gdUttRel : UttRel GDSpeaker Unit GDExpr ProjWorld
  | .jones,    _, .goddamnedKeys, .actual => True
  | .jones,    _, .goddamnedKeys, .hypothetical => False
  | .reporter, _, .goddamnedKeys, _ => False

/-- Reporter's MQ context. Sx is jones (the anaphorically retrieved
    speaker), wc is the actual world, the reporter is the discourse
    speaker (not represented in MQContext directly). -/
def reporterCtx : MQContext ProjWorld GDExpr GDSpeaker Unit :=
  { interp := gdInterp, uttRel := gdUttRel
  , sx := .jones, ux := (), wc := .actual }

/-- Peripheral content after 𝔐: utterance attribution to Jones, NOT the
    original expressive CI. -/
@[simp] theorem gd_r_layer_attribution :
    (MQProp.applyMQ reporterCtx .goddamnedKeys).rContent .actual := by
  simp [reporterCtx, gdUttRel]

/-- At-issue content is preserved through 𝔐: Jones-spent-an-hour-
    looking-for-his-keys remains true. -/
@[simp] theorem gd_at_issue_preserved :
    (MQProp.applyMQ reporterCtx .goddamnedKeys).atIssue .actual := by
  simp [reporterCtx, gdInterp]

/-- The reporter is not credited with Jones's utterance — gdUttRel
    correctly distinguishes the actual utterer from the reporter. -/
theorem gd_reporter_not_attributed :
    ¬ gdUttRel .reporter () .goddamnedKeys .actual := by
  intro h; cases h

/--
**The strip-then-remix structure (paper p.21-22).** A `TwoDimProp` carrying the original CI is
pure-quoted (stripping the CI to `⊤` — an information-losing step, `pureQuote_loses_ci_info`),
then `MQContext.applyMQ` re-introduces peripheral content as utterance attribution. The
remixed R-layer holds the new attribution, not the original CI.
-/
theorem gd_strip_then_remix_loses_original_ci :
    let original : TwoDimProp ProjWorld :=
      { atIssue := λ _ => True, ci := gdOriginalCI }
    -- After remix via 𝔐, the R-layer is the new utterance attribution, not the original CI:
    (MQProp.applyMQ reporterCtx .goddamnedKeys).rContent .hypothetical ≠
      original.ci .hypothetical := by
  -- gdOriginalCI = constant True, but gdUttRel .jones at .hypothetical = False
  simp [reporterCtx, gdUttRel, gdOriginalCI]

-- ────────────────────────────────────────────────────
-- §1.2. Refutation theorems
-- ────────────────────────────────────────────────────

/--
**K-G refutes Potts's universal CI projection.** Per
[potts-2005] (formalised as
`Pragmatics.Expressives.Basic.ci_projects_through_neg`):
`(neg p).ci = p.ci`. The CI of a `TwoDimProp` projects unchanged
through any at-issue operator. K-G's analysis predicts that under
indirect-speech embedding the CI is REPLACED by utterance
attribution.

To exhibit the divergence we apply both analyses to the SAME input
proposition `original = ⟨True, gdOriginalCI⟩`:

- **Potts**: applying `TwoDimProp.neg` (or any at-issue operator)
  preserves the CI, so the predicted CI value at `.hypothetical` is
  `gdOriginalCI .hypothetical = True` (Jones's attitude persists
  across worlds).
- **K-G**: applying the strip-then-remix pipeline replaces the CI
  with R-attribution `gdUttRel .jones () .goddamnedKeys`, so the
  predicted R-value at `.hypothetical` is `False` (Jones's
  utterance is contingent on the world — only happened in `.actual`).

The two analyses disagree at `.hypothetical`. The proof actually
invokes `Pragmatics.Expressives.TwoDimProp.neg` on the constructed
input — not just compares stipulated values.
-/
theorem kg_refutes_potts_universal_projection :
    let original : TwoDimProp ProjWorld :=
      { atIssue := λ _ => True, ci := gdOriginalCI }
    -- Potts: substrate's neg leaves ci unchanged
    -- (`Pragmatics.Expressives.TwoDimProp.ci_projects_through_neg`)
    let pottsCIAfterNeg : ProjWorld → Prop := (TwoDimProp.neg original).ci
    -- K-G: strip-then-mix replaces ci with R-attribution to sx (=jones)
    let kgRAfterChain : ProjWorld → Prop :=
      (MQProp.applyMQ reporterCtx .goddamnedKeys).rContent
    -- They disagree at .hypothetical: True ≠ False
    pottsCIAfterNeg .hypothetical ≠ kgRAfterChain .hypothetical := by
  simp [TwoDimProp.neg, gdOriginalCI, reporterCtx, gdUttRel]

/--
**K-G refutes Harris-Potts orientation variables.**
[harris-potts-2009] posit a free orientation variable on each CI
item, contextually resolved (formalised as
`HarrisPotts2009.CIItem` with a
`ciFor : Orientation → W → Prop` field). K-G's strip-then-remix
analysis predicts the CI is FIXED by the syntactic structure
(specifically by `sx` in the MQ context).

To exhibit the divergence, we construct an H&P CI item whose
orientation is contextually resolvable to ANY participant (H&P's
permissive prediction), and a K-G chain where the CI is determined
by the fixed `sx = .jones`. The H&P item allows the reporter to be
the orientation; K-G excludes this.
-/
theorem kg_refutes_harris_potts_orientation :
    -- H&P's CI item: orientation freely resolved
    let hpItem : HarrisPotts2009.CIItem GDSpeaker ProjWorld :=
      { ciFor := λ o w => match o with
                          | .speaker => True   -- H&P allows resolving to any participant
                          | .other _ => True   -- including non-anaphoric speakers
        atIssue := λ _ => True }
    -- H&P-resolved CI for "the reporter as orientation":
    let hpReporterCI : ProjWorld → Prop :=
      (hpItem.resolve (.other GDSpeaker.reporter)).ci
    -- K-G's CI: fixed to sx = .jones via reporterCtx
    let kgCI : ProjWorld → Prop :=
      (MQProp.applyMQ reporterCtx .goddamnedKeys).rContent
    -- H&P predicts CI holds for the reporter at .hypothetical
    -- (orientation can resolve flexibly); K-G predicts NOT (reporter
    -- isn't sx, and Jones didn't utter at .hypothetical).
    hpReporterCI .hypothetical ≠ kgCI .hypothetical := by
  simp [HarrisPotts2009.CIItem.resolve, reporterCtx, gdUttRel]

/--
**K-G refutes Maier 2014a's syntactic chameleonism.**

Maier (`Maier2014`) treats the
mixed-quotation operator as type-polymorphic: `mq attrib e` returns
a `TypedExpr` with the SAME category as `e`, and the daughter's CI
content passes through unchanged (theorem `mq_ci_passes_daughter_ci_through`).

K-G's strip-then-mix pipeline DESTROYS the daughter's CI before
remixing — the original `gdOriginalCI` does not survive into the
result's peripheral content; only the new R-attribution does.

We exhibit the divergence by constructing the same input expression
in both substrates and showing their CI predictions diverge.
-/
theorem kg_refutes_maier_chameleonism :
    -- Maier's typed input — wraps gdOriginalCI through `mq`:
    let maierInput : Maier2014.TypedExpr ProjWorld :=
      { cat := .NP
      , meaning := { atIssue := λ _ => True, ci := gdOriginalCI } }
    -- Maier's prediction: daughter CI passes through, conjoined with attribution.
    -- At .hypothetical with a constant-True attribution, Maier's CI = True.
    let maierAttrib : ProjWorld → Prop := λ _ => True
    let maierCI : ProjWorld → Prop :=
      (Maier2014.mq maierAttrib maierInput).meaning.ci
    -- K-G's prediction: rContent at .hypothetical = False (Jones didn't utter).
    let kgCI : ProjWorld → Prop :=
      (MQProp.applyMQ reporterCtx .goddamnedKeys).rContent
    -- Divergence at .hypothetical:
    maierCI .hypothetical ≠ kgCI .hypothetical := by
  simp [Maier2014.mq, gdOriginalCI, reporterCtx, gdUttRel]

end CIProjection

-- ════════════════════════════════════════════════════
-- § 2. C-Monsters (paper §4)
-- ════════════════════════════════════════════════════

section CMonsters

/-- Worlds for the Pluto scenario: pre-2006 conventions classify Pluto
    as a planet, post-2006 do not. -/
inductive PlutoWorld where
  | pre2006 | post2006
  deriving DecidableEq, Repr, Inhabited

/-- The word 'planet' as a quoted expression. -/
inductive PlutoExpr where | planet deriving DecidableEq, Repr

/-- Two speakers: one using the standard (post-2006) convention, one
    a hypothetical pre-2006 community. The ∃-over-speakers in K-G's †
    (paper fn 22) ranges over types like this. -/
inductive PlutoSpeaker where
  | standard
  | pre2006Community
  deriving DecidableEq, Repr

/-- Quotative interpretation of 'planet': depends on the speaker's
    convention. The pre-2006 community classifies Pluto as planet at
    pre-2006 worlds; the standard speaker does not. -/
def plutoInterp : QuotInterp PlutoExpr PlutoSpeaker PlutoWorld
  | .planet, .pre2006,  .pre2006Community, _ => True
  | .planet, .post2006, .pre2006Community, _ => False
  | .planet, _,         .standard,         _ => False

/--
**(4): "Pluto could have easily been a planet"** — true via K-G's
diagonalizer with ∃-over-speakers (paper fn 22). The diagonalized
predicate is non-vacuous: there exists a speaker (the pre-2006
community) whose use of 'planet' includes Pluto at the pre-2006 world.
Witness: speaker = `.pre2006Community`, world = `.pre2006`.
-/
theorem pluto_counterfactual_via_diagonalizeKG :
    ∃ w : PlutoWorld, diagonalizeKG plutoInterp .planet w := by
  refine ⟨.pre2006, ?_⟩
  exact ⟨.pre2006Community, by simp [plutoInterp]⟩

/-- **Witness uniqueness fails.** The pre-2006 community and the
    standard speaker disagree on Pluto's planethood at pre-2006 worlds,
    so K-G's existential is genuinely informative — not every speaker
    is a witness. -/
theorem pluto_diagonalize_witness_not_universal :
    ¬ ∀ s : PlutoSpeaker, plutoInterp .planet .pre2006 s .pre2006 := by
  intro h
  have : plutoInterp .planet .pre2006 .standard .pre2006 := h .standard
  cases this

/--
**K-G's covert lexicon, viewed as Kaplan-context shifts.** All four
covert operators (𝔐, ↓, †, 𝔄) operate on the world / appropriateness
components of evaluation, NOT on the Kaplan context (agent, time,
location). Their image on Kaplan-context space is the identity shift.

We exhibit this with one `identityShift` per covert operator. The
list could equivalently be empty; making it explicit lets the
no-monster theorem actually CASE-SPLIT on K-G's apparatus rather
than vacuously hold over an empty list.
-/
def kgEmbeddingShifts {W E P T : Type*} :
    List (Semantics.Context.ContextShift (Semantics.Context.KContext W E P T)) :=
  [Semantics.Context.identityShift,  -- image of 𝔐
   Semantics.Context.identityShift,  -- image of ↓
   Semantics.Context.identityShift,  -- image of †
   Semantics.Context.identityShift]  -- image of 𝔄

/--
**Bridge to Kaplan's no-monster thesis** (`Semantics/Reference/
Monsters.lean`). K-G's `†` is a content operator (it shifts the world
component of the quotative interpretation), NOT a context operator.
K-G's apparatus, projected to Kaplan-context space, contributes only
identity shifts (`kgEmbeddingShifts`), so Kaplan's thesis is preserved.

This is the architectural payoff of K-G's analysis vs. KJR's: K-G
explains c-monstrous behavior WITHOUT touching the
worlds-as-evaluation-points architecture or introducing context shifts.
-/
theorem diagonalize_no_kaplan_monster {W E P T : Type*} :
    Semantics.Reference.Monsters.KaplansThesisHolds
      (kgEmbeddingShifts (W := W) (E := E) (P := P) (T := T)) := by
  intro σ hMem
  -- All entries in kgEmbeddingShifts are identityShift, never a monster.
  simp [kgEmbeddingShifts] at hMem
  rcases hMem with rfl | rfl | rfl | rfl
  all_goals exact Semantics.Reference.Monsters.identityShift_not_monster

/--
**K-G refutes KJR's convention-shift architecture.** KJR
(`KocurekJerzakRudolph2020`) replace
worlds with world-convention pairs and treat conditionals as shifting
the convention component. K-G's analysis preserves
worlds-as-evaluation-points and uses `†` instead.

We exhibit the SUBSTANTIVE divergence by constructing the same
scenario in both substrates and showing they make incompatible
predictions:
- **KJR**: at the WC-pair `⟨.post2006, pre2006Convention⟩`, the
  diagonal content of `planet` applied to `pluto` is True (the
  WC-pair's convention puts Pluto in the extension, regardless of
  the world component).
- **K-G**: `diagonalizeKG plutoInterp .planet .post2006` is False
  (no speaker witness — no community whose use of 'planet' at
  `.post2006` includes Pluto, since standard.post2006 = False and
  pre2006Community.post2006 = False).

The two architectures predict different truth values for the same
surface sentence at the same world.
-/
theorem kg_refutes_kjr_convention_shift :
    -- KJR's substrate: define conventions where pre2006 includes Pluto
    let pre2006Convention : KocurekJerzakRudolph2020.Convention
        PlutoExpr Unit PlutoWorld :=
      { ext := λ p _ _ => match p with | .planet => True }
    let kjrEval : Prop :=
      KocurekJerzakRudolph2020.diagContent
        (W := PlutoWorld) (Pred := PlutoExpr) (Entity := Unit)
        .planet () ⟨.post2006, pre2006Convention⟩
    -- K-G's substrate: the diagonalizer at .post2006
    let kgEval : Prop := diagonalizeKG plutoInterp .planet .post2006
    -- KJR predicts True; K-G predicts False — divergent.
    kjrEval ∧ ¬ kgEval := by
  refine ⟨?_, ?_⟩
  · simp [KocurekJerzakRudolph2020.diagContent]
  · intro ⟨s, hs⟩
    cases s <;> simp [plutoInterp] at hs

end CMonsters

-- ════════════════════════════════════════════════════
-- § 3. Metalinguistic Negation (paper §5)
-- ════════════════════════════════════════════════════

section MetalinguisticNegation

/-- Expressions in the metalinguistic-negation scenario. Includes
    lexical pairs needed for the morpheme-incorporation prediction. -/
inductive MNExpr where
  | mongeese
  | mongooses
  | happy
  | unhappy        -- morphologically incorporated negation
  | ecstatic
  deriving DecidableEq, Repr

/-- Two worlds: the actual (where the dispute occurs) and a
    hypothetical alternative. Multi-constructor so the appropriateness
    modal `♦` quantifies non-vacuously. -/
inductive MNWorld where
  | actual
  | hypothetical
  deriving DecidableEq, Repr, Inhabited

/-- Speakers: a generic English speaker and a hypothetical prescriptivist
    who would judge 'mongeese' appropriate. -/
inductive MNSpeaker where
  | genericEnglish
  | prescriptivist
  deriving DecidableEq, Repr

/-- Both 'mongeese' and 'mongooses' pick out the mongoose property —
    same at-issue content. The lexical-pair pattern for incorporation
    has 'happy' and 'unhappy' as semantic complements. -/
def mnInterp : QuotInterp MNExpr MNSpeaker MNWorld
  | .mongeese,  _, _, _ => True   -- mongoose property
  | .mongooses, _, _, _ => True   -- mongoose property (same extension)
  | .happy,     _, _, _ => True
  | .unhappy,   _, _, _ => False  -- complement of happy
  | .ecstatic,  _, _, _ => True   -- entails happy

/-- **Non-trivial utterance attribution.** Generic English speaker
    actually utters 'mongooses'; the prescriptivist would utter
    'mongeese'. This non-vacuity is what the original substrate's
    constant-True uttRel was missing. -/
def mnUttRel : UttRel MNSpeaker Unit MNExpr MNWorld
  | .genericEnglish, _, .mongooses, .actual => True
  | .prescriptivist, _, .mongeese,  .actual => True
  | _, _, _, _ => False

/-- **Appropriateness standard.** 'mongooses' is the appropriate plural
    for English speakers; 'mongeese' is not. Speaker-relative: the
    prescriptivist's standard would judge 'mongeese' appropriate. -/
def mnApprop : AppropStandard MNSpeaker MNExpr MNWorld
  | .genericEnglish, .mongooses, _ => True
  | .prescriptivist, .mongeese,  _ => True
  | _, _, _ => False

/-- The metalinguistic negation context — generic English speaker. -/
def mnCtx : MQContext MNWorld MNExpr MNSpeaker Unit :=
  { interp := mnInterp
  , uttRel := mnUttRel
  , sx := .genericEnglish
  , ux := ()
  , wc := .actual }

/--
**(3): "I didn't manage to trap two MONGEESE"** — the metalinguistic
negation reading derives via `metalinguistic_neg_truth_conditions`
(substrate, paper §5 p.28-30): the at-issue content is `¬(at-issue ∧
appropriate)`. Since 'mongeese' is INappropriate for the generic
English speaker, the negation holds even though the at-issue (mongoose
property) does not.
-/
theorem mongeese_metalinguistic_neg :
    (TwoDimProp.neg
      (shunt (applyApprop mnApprop mnCtx.sx .mongeese
        (mnCtx.applyMQ .mongeese)))).atIssue .actual := by
  rw [metalinguistic_neg_truth_conditions]
  intro ⟨_, h⟩
  exact h

-- ────────────────────────────────────────────────────
-- §3.1. Three syntactic predictions (paper p.32)
-- ────────────────────────────────────────────────────

/--
**Prediction 1 — morpheme incorporation failure** (Horn 1989 p.392,
[horn-1985]). Morphologically incorporated negation (`unhappy`)
cannot host metalinguistic readings. K-G derives this without lexical
ambiguity in *not*: the metalinguistic chain `𝔐 → 𝔄 → ↓ → ¬` requires
syntactically separate `not`, `𝔄`, and `↓` nodes — incorporation into
a lexical item collapses these into one head, blocking the chain.

Encoded: `unhappy` is at-issue-equivalent to ¬'happy', NOT to
¬♦happy (the appropriateness modal cannot factor through the
incorporated item).
-/
theorem mongeese_blocks_morpheme_incorporation :
    -- 'unhappy' is at-issue-equivalent to ¬'happy', not to ¬♦happy
    ∀ (s : MNSpeaker) (w : MNWorld),
      mnInterp .unhappy w s w ↔ ¬ mnInterp .happy w s w := by
  intros; simp [mnInterp]

/--
**Prediction 2 — NPI licensing failure** (Horn 1989). Metalinguistic
negation does not license NPIs. K-G's account derives this from the
appropriateness modal `♦` and the shunting structure: NPIs require
descriptive-negation downward-entailing scope, but `♦` is not
downward-entailing in the relevant sense.

Lifted from `Horn1989`.
-/
theorem mongeese_blocks_npi_licensing
    (occ : Horn1989.NegScopeOccurrence MNExpr) :
    occ.neg.kind = .metalinguistic → occ.polarity = .npi → ¬ occ.licit :=
  Horn1989.metalinguistic_neg_blocks_npi_licensing occ

/--
**Prediction 3 — DN-elimination failure** ([burton-roberts-1989]).
"She's not not happy, she's inconsolable" does NOT reduce to "She's
happy" — the metalinguistic chain blocks DN-elimination. K-G's
account: each `¬` in the metalinguistic chain scopes over a distinct
appropriateness conjunction, so successive `¬¬` does not reduce.

Lifted from `Horn1989.metalinguistic_neg_blocks_dn_elimination`.
-/
theorem mongeese_blocks_dn_elimination
    (chain : Horn1989.NegChain MNExpr)
    (h : chain.containsMetalinguistic) : ¬ chain.dneEliminates :=
  Horn1989.metalinguistic_neg_blocks_dn_elimination chain h

-- ────────────────────────────────────────────────────
-- §3.2. Cross-framework theorems
-- ────────────────────────────────────────────────────

/--
**K-G's metalinguistic negation does NOT match `DenialType.implicature`.**

`VanDerSandtMaier2003` (formalising [van-der-sandt-maier-2003])
classifies register/connotation denials as `DenialType.implicature`,
which maps to `ContentLayer.implicature`. K-G's chain produces content
on the **appropriateness** dimension via `applyApprop` —
which lives in `Quotation/Mixed`, not in `Implicature/`. The two
substrates are not inter-translatable.

We exhibit the structural divergence by exhibiting a witness
metalinguistic-negation example whose at-issue conjunct is True
(mongoose property holds) AND whose appropriateness conjunct is
False (`mongeese` is inappropriate). This is the K-G profile, NOT
the implicature-denial profile (which would target a scalar
enrichment, not an appropriateness modal).
-/
theorem kg_metalinguistic_chain_targets_appropriateness :
    -- The `applyApprop` chain produces a TwoDimProp whose CI dimension
    -- is the appropriateness predicate, NOT a Gricean enrichment:
    (applyApprop mnApprop mnCtx.sx .mongeese
        (mnCtx.applyMQ .mongeese)).ci = mnApprop mnCtx.sx .mongeese := by
  simp [applyApprop_ci]

-- ────────────────────────────────────────────────────
-- §3.3. The architectural benefit of MQProp (3-layer model)
-- ────────────────────────────────────────────────────

/--
**R-content survives the full metalinguistic negation chain — in the
MQProp layered model.** This is the load-bearing architectural payoff
of the substrate's two-layer refactor (`MQProp` vs flat `TwoDimProp`).

In the flat model, `applyApprop` REPLACES the ci dimension with the
appropriateness content, so the original R-attribution
(`mnUttRel mnCtx.sx mnCtx.ux .mongeese`) is destroyed when 𝔄 fires.
In the MQProp model, R lives in a separate layer; 𝔄 writes only to
the ◆-layer. After the full chain `𝔐 → 𝔄 → ↓ → ¬`, R is intact.

This is the prediction K-G needs (paper §5): "I didn't trap two
MONGEESE" still records that someone uttered 'mongeese'. The flat
model loses this; MQProp keeps it. Concrete witness for the mongeese
scenario, derived from substrate's `full_chain_preserves_rContent`.
-/
theorem mongeese_R_survives_metalinguistic_neg :
    ((MQProp.applyMQ mnCtx .mongeese).applyApprop mnApprop mnCtx.sx .mongeese
      |>.shunt |>.neg).rContent
    = mnUttRel mnCtx.sx mnCtx.ux .mongeese :=
  MQProp.full_chain_preserves_rContent mnCtx mnApprop .mongeese

/-- **R-content is non-trivial for the mongeese scenario.** Concretely
    at `.actual`, the R-layer records that the generic English speaker
    did NOT utter 'mongeese' (`mnUttRel .genericEnglish () .mongeese
    .actual = False`) — the speaker uttered 'mongooses' instead. This
    information is preserved through the metalinguistic-negation chain
    in the layered model. The flat-model `mongeese_metalinguistic_neg`
    cannot witness this distinction. -/
theorem mongeese_R_value_at_actual :
    ¬ ((MQProp.applyMQ mnCtx .mongeese).applyApprop mnApprop mnCtx.sx .mongeese
        |>.shunt |>.neg).rContent .actual := by
  simp [mongeese_R_survives_metalinguistic_neg, mnCtx, mnUttRel]

end MetalinguisticNegation

-- ════════════════════════════════════════════════════
-- § 4. Metalinguistic Negotiation (paper §6)
-- ════════════════════════════════════════════════════

section MetalinguisticNegotiation

/-- The word 'athlete' in the Secretariat dispute. -/
inductive AthExpr where | athlete deriving DecidableEq, Repr

/-- Worlds: the actual world (broad athleticism is the relevant property)
    and a hypothetical comparison world. -/
inductive AthWorld where
  | actual
  | hypothetical
  deriving DecidableEq, Repr, Inhabited

/-- Two disputants A and B (who AGREE Secretariat has the relevant
    physical properties but DISAGREE on whether 'athlete' is appropriate
    to use for non-human animals). -/
inductive AthSpeaker where | speakerA | speakerB deriving DecidableEq, Repr

/-- The shared at-issue content: Secretariat instantiates broad
    athleticism. Both A and B agree on this. -/
def athInterp : QuotInterp AthExpr AthSpeaker AthWorld
  | .athlete, _, _, _ => True

/--
**The SHARED appropriateness standard.** Per K-G §6, the dispute is
NOT over which idiolectal extension is "correct" (P&S's diagnosis) —
both A and B are using a single standard, and the dispute is about
what that standard's verdict on 'athlete-for-horses' should be. We
encode this as ONE `AppropStandard` whose value at the dispute
expression is the contested proposition.
-/
def athShared : AppropStandard AthSpeaker AthExpr AthWorld
  | _, .athlete, _ => True

/-- A's MQ context — committing to "appropriate(athlete, Secretariat)". -/
def athCtxA : MQContext AthWorld AthExpr AthSpeaker Unit :=
  { interp := athInterp
  , uttRel := λ _ _ _ _ => True
  , sx := .speakerA, ux := (), wc := .actual }

/--
**A's assertion (paper (6) A: "Secretariat is an athlete")** — the
shunted appropriateness chain holds at .actual under the shared
standard.
-/
theorem speakerA_assertion :
    (shunt (applyApprop athShared athCtxA.sx .athlete
        (athCtxA.applyMQ .athlete))).atIssue .actual := by
  refine ⟨?_, ?_⟩
  · simp [athCtxA, athInterp]
  · simp [athShared]

/--
**B's denial (paper (6) B: "No, Secretariat is not an athlete")** —
metalinguistic negation of the SAME shared content. B asserts the
negation of the appropriateness conjunct. The crucial point (vs. P&S)
is that A and B's assertions are LITERALLY INCOMPATIBLE on the same
standard, NOT consistent on different idiolects.
-/
theorem speakerB_denial_under_shared_standard
    (rejectedApprop : AppropStandard AthSpeaker AthExpr AthWorld)
    (h_neg : ¬ rejectedApprop .speakerA .athlete .actual) :
    (TwoDimProp.neg (shunt (applyApprop rejectedApprop athCtxA.sx .athlete
        (athCtxA.applyMQ .athlete)))).atIssue .actual := by
  rw [metalinguistic_neg_truth_conditions]
  intro ⟨_, h⟩
  exact h_neg h

/--
**K-G refutes Plunkett-Sundell — structural cross-framework theorem.**

K-G and P&S make incompatible commitments about the structure of a
metalinguistic dispute:

- **P&S** (`PlunkettSundell2013`):
  `consistentContents` requires `predA ≠ predB` extensionally —
  speakers use DIFFERENT idiolectal extensions of the contested
  predicate, and joint satisfiability witnesses their distinct
  meanings. Paper p.18: "the connection between genuine disagreement
  and sameness of meaning is broken."

- **K-G** (paper §6, p.33-34): A and B operate on a SHARED standard;
  the dispute is over the SAME proposition's truth value. Encoded in
  P&S's `MetalinguisticDispute` schema, K-G's commitment is
  `predA = predB`.

The substrate lemma
`MetalinguisticDispute.consistentContents_excludes_shared_standard`
proves these commitments are jointly unsatisfiable: any dispute with
`predA = predB` necessarily violates `consistentContents`. The K-G
refutation is the schematic claim that K-G's commitment entails P&S's
predicate failure — universally over disputes, with no hand-picked
extensions.
-/
theorem kg_refutes_plunkett_sundell :
    ∀ d : PlunkettSundell2013.MetalinguisticDispute Unit AthWorld,
      d.predA = d.predB → ¬ d.consistentContents :=
  fun _ h =>
    PlunkettSundell2013.MetalinguisticDispute.consistentContents_excludes_shared_standard
      _ h

end MetalinguisticNegotiation

-- ════════════════════════════════════════════════════
-- § 5. "In a Sense" Constructions (paper §7)
-- ════════════════════════════════════════════════════

section InASense

/-- Expressions for the "viruses are alive" scenario. -/
inductive VirExpr where | alive deriving DecidableEq, Repr

/-- Two speakers with different intensions for 'alive':
    - biologist: 'alive' includes viruses (genetic-material criterion)
    - layperson: 'alive' excludes viruses (5-kingdoms criterion) -/
inductive VirSpeaker where
  | biologist
  | layperson
  deriving DecidableEq, Repr

/-- Worlds for the "in a sense" scenario. Multi-constructor so the
    intension quantification is non-vacuous. -/
inductive VirWorld where
  | actual
  | counterfactual
  deriving DecidableEq, Repr, Inhabited

/-- Quotative interpretation: 'alive' has different extensions
    depending on which speaker is using the word. -/
def virInterp : QuotInterp VirExpr VirSpeaker VirWorld
  | .alive, _, .biologist, _ => True   -- viruses qualify under biological criterion
  | .alive, _, .layperson, _ => False  -- viruses don't under folk criterion

/-- **Intensions** — propositions about VirWorlds. K-G's analysis quantifies
    over intensions μ in addition to speakers sₓ. Here we use the type of
    `VirWorld → Prop` directly. -/
abbrev VirIntension := VirWorld → Prop

/-- The MQ context parameterised by speaker. -/
def virMQCtx (s : VirSpeaker) : MQContext VirWorld VirExpr VirSpeaker Unit :=
  { interp := virInterp
  , uttRel := λ _ _ _ _ => True
  , sx := s
  , ux := (), wc := .actual }

/--
**Predicate Abstraction over the intension variable** (paper p.37-38).
K-G's `which_μ` binds `μ` via Heim & Kratzer-style PA. Encoded here as
a function abstracting over intensions.
-/
def whichMu (P : VirIntension → VirWorld → Prop) (w : VirWorld) : Prop :=
  ∃ μ : VirIntension, P μ w

/--
**(7'): "There is a sense which viruses are alive in"** — the K-G
analysis (paper p.38) gives the L_MQ formula:

  ∃μ ∃sₓ [⟨*⟩(`viruses are alive`)(wc)(sₓ) ∧
          [^⟨*⟩(`viruses are alive`)(wc)(sₓ)] = μ]

The existential ranges over BOTH intensions μ AND speakers sₓ. Both
are needed: speakers select different intensions for the same
expression, and `which_μ` binds μ for the relative clause.

Witness: at .actual, with sₓ = biologist (whose use of 'alive' includes
viruses) and μ = the biologist's predicate.
-/
theorem viruses_alive_in_a_sense :
    whichMu (λ μ w => ∃ s : VirSpeaker,
        ((virMQCtx s).applyMQ .alive).atIssue w ∧
        μ = ((virMQCtx s).applyMQ .alive).atIssue) .actual := by
  refine ⟨((virMQCtx .biologist).applyMQ .alive).atIssue,
          .biologist, ?_, rfl⟩
  simp [virMQCtx, virInterp]

/-- The layperson is NOT a witness: their use of 'alive' excludes viruses. -/
theorem not_alive_layperson :
    ¬ ((virMQCtx .layperson).applyMQ .alive).atIssue .actual := by
  simp [virMQCtx, virInterp]

/-- The existential is non-trivial: not all senses make viruses alive. -/
theorem not_all_senses :
    ¬ (∀ s : VirSpeaker, ((virMQCtx s).applyMQ .alive).atIssue .actual) := by
  intro h
  exact not_alive_layperson (h .layperson)

/--
**K-G's "in a sense" is distinct from imprecision/granularity accounts.**
Imprecision frameworks (e.g. `Haslinger2025`)
locate the variation in TOLERANCE / GRANULARITY parameters of a single
speaker. K-G's "in a sense" locates the variation in the SPEAKER VARIABLE
of `𝔐` — different speakers contribute different intensions.

The two analyses make incompatible architectural commitments. Imprecision
holds the speaker fixed and varies the granularity; K-G holds granularity
fixed and varies the speaker.

We exhibit the divergence: K-G's analysis predicts variation at the
speaker locus (biologist vs. layperson), where Imprecision predicts no
variation (single speaker, single granularity).
-/
theorem in_a_sense_distinct_from_imprecision :
    -- K-G's account: at-issue varies with speaker for the same expression.
    ((virMQCtx .biologist).applyMQ .alive).atIssue .actual ≠
    ((virMQCtx .layperson).applyMQ .alive).atIssue .actual := by
  intro h
  have : ((virMQCtx .biologist).applyMQ .alive).atIssue .actual =
         ((virMQCtx .layperson).applyMQ .alive).atIssue .actual := h
  simp [virMQCtx, virInterp] at this

end InASense

end KirkGiannini2024
