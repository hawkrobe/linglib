import Linglib.Semantics.Questions.Bias.Defs
import Linglib.Semantics.Modality.Kratzer.Flavor
import Linglib.Discourse.CommonGround
import Linglib.Discourse.SpeechAct
import Linglib.Discourse.Commitment.Basic
import Mathlib.Data.Set.Basic

/-!
# Biased Polar Questions — VERUM/FALSUM and the evidential-bias modal
[bring-gunlogson-2000] [ladd-1981] [repp-2013] [romero-2019] [romero-2024] [romero-han-2004] [simik-2024] [stankova-2025]

The modal machinery for polar question bias, building on the form and bias
vocabulary in `Semantics.Questions.Bias.Defs`. Formalizes VERUM and FALSUM
(line b of [romero-2020]'s clustering — [romero-han-2004]) and the
evidential-bias necessity modal □_ev using Kratzer modal and CommonGround
infrastructure, the line adopted by Staňková (2026) for Czech.

## Main definitions

* `verum`, `FalsumContent`/`mkFalsum`, `FalsumCZ`/`mkFalsumCZ` — VERUM and FALSUM.
* `EvidentialBiasFlavor`, `evidentialNecessity`/`evidentialPossibility` — □_ev.
* `innerBias`/`medialBias`, `falsumAlternatives` — scope interactions and focus.
-/

namespace Semantics.Questions.Bias

open Semantics.Modality.Kratzer
open CommonGround

variable {W : Type*}

/-! ### VERUM ([romero-han-2004]) -/

/-- VERUM operator ([romero-han-2004], line b).

⟦VERUM_x⟧ = λp. λw. ∀w' ∈ Epi_x(w). ∀w'' ∈ Conv_x(w'). [p ∈ CommonGround]

"x is sure that p should be added to the Common Ground."

We model this as: in all epistemically accessible worlds where the speaker's
conversational goals are fulfilled, p is in the CommonGround. This is a double universal:
necessity over epistemic alternatives, then necessity over conversational goals. -/
def verum (epistemic : ModalBase W) (conversational : OrderingSource W)
    (cg p : Set W) (w : W) : Prop :=
  -- For all best epistemic worlds w': in the CommonGround induced at w', p holds
  ∀ w' ∈ bestWorlds epistemic conversational w, cg w' ∧ p w'

/-- FALSUM operator ([repp-2013], [romero-2019], [romero-2024] def. 33).

At-issue content: ¬p
CommonGround-management content: ∀w' ∈ Epi(w). ∀w'' ∈ Conv(w'). [p ∉ CommonGround]

"x is sure that p should NOT be added to the Common Ground."

FALSUM is the CommonGround-management negation of VERUM. The at-issue content
is simply ¬p, while the non-at-issue content (CommonGround-management) expresses
that p is not to become common ground. -/
structure FalsumContent (W : Type*) where
  /-- At-issue content: ¬p -/
  atIssue : Set W
  /-- CommonGround-management: p should not be added to CommonGround.
      Modeled as: the speaker considers it epistemically possible that p,
      but p is not CommonGround-entailed. -/
  cgManagement : Set W

/-- Construct FALSUM content for a proposition p. -/
def mkFalsum (epistemic : ModalBase W) (conversational : OrderingSource W)
    (cg p : Set W) : FalsumContent W where
  atIssue := fun w => ¬ p w
  cgManagement := fun w =>
    -- Speaker considers p epistemically possible
    (∃ w' ∈ bestWorlds epistemic conversational w, p w') ∧
    -- But p is not entailed by the CommonGround
    ¬(∀ w', cg w' → p w')

/-- FALSUM's at-issue content is propositional negation. -/
theorem falsum_atIssue_is_negation (ep : ModalBase W) (cv : OrderingSource W)
    (cg p : Set W) (w : W) :
    (mkFalsum ep cv cg p).atIssue w ↔ ¬ p w := Iff.rfl

/-! ### Czech FALSUM, FALSUM^CZ ([simik-2024]) -/

/-- Czech FALSUM ([simik-2024] eq. 44), weaker than standard FALSUM.

⟦FALSUM_1^CZ⟧^g(p) = λw : ∃w' ∈ EPI_{g(1)}(w)[p(w') = 1]. p ∉ CG_w

Key differences from Repp's FALSUM:
1. **Weak commitment**: epistemic *possibility* rather than necessity/belief
2. **Not tied to speaker/addressee**: attitude holder g(1) can be anyone
3. **Commitment not at issue**: it is a presupposition/conventional implicature
4. **Not conventionally tied to conversational goals**: the commitment need
   not be at stake in the conversation

This weaker version accounts for the broader distribution of Czech
InterNPQs compared to English high negation PQs: Czech FALSUM^CZ
is compatible with more bias configurations because it only requires
epistemic possibility, not belief. -/
structure FalsumCZ (W : Type*) where
  /-- At-issue content: ¬p (same as standard FALSUM) -/
  atIssue : Set W
  /-- Presupposition: attitude holder considers p epistemically possible.
      This is the definedness condition — the question is defined only if
      the attitude holder considers the positive prejacent possible. -/
  definedness : Set W
  /-- CommonGround-management: p is not part of the common ground at w. -/
  cgContent : Set W

/-- Construct [simik-2024]'s FALSUM^CZ for a proposition p.

The attitude holder's epistemic state is modeled via the modal base
(their epistemic alternatives). -/
def mkFalsumCZ (attitudeEpi : ModalBase W) (ordering : OrderingSource W)
    (cg p : Set W) : FalsumCZ W where
  atIssue := fun w => ¬ p w
  definedness := fun w =>
    -- ∃w' ∈ EPI(w). p(w') — epistemic possibility
    ∃ w' ∈ bestWorlds attitudeEpi ordering w, p w'
  cgContent := fun _ =>
    -- p ∉ CG_w
    ¬(∀ w', cg w' → p w')

/-- FALSUM^CZ at-issue content is still propositional negation. -/
theorem falsumCZ_atIssue_is_negation (ep : ModalBase W) (cv : OrderingSource W)
    (cg p : Set W) (w : W) :
    (mkFalsumCZ ep cv cg p).atIssue w ↔ ¬ p w := Iff.rfl

/-- Standard FALSUM entails FALSUM^CZ definedness: if the speaker *believes* p
is possible (necessity over goals), then they certainly *consider* it possible.
This captures why standard FALSUM is a special case of FALSUM^CZ. -/
theorem standard_falsum_entails_CZ_definedness
    (ep : ModalBase W) (cv : OrderingSource W) (cg p : Set W) (w : W)
    (hStd : ∃ w' ∈ bestWorlds ep cv w, p w') :
    (mkFalsumCZ ep cv cg p).definedness w :=
  hStd

/-! ### Náhodou as ordering-source modifier ([simik-2024]) -/

/-- *Náhodou* 'by chance' loosens the stereotypical ordering source of
FALSUM^CZ to include more remote (less stereotypical) possibilities.

[simik-2024] §5.1: "its function is to 'loosen' the default stereotypical
ordering source of the epistemic modal contributed by FALSUM so as to
include more remote (less likely) possibilities in the quantification domain
of the modal."

Formally, náhodou replaces the ordering source g with a weaker g' such that
Best(f, g', w) ⊇ Best(f, g, w). The resulting proposition is stronger because
ruling out p in less likely worlds entails ruling it out in more likely worlds. -/
def loosenOrderingSource (_ : OrderingSource W) (loosened : OrderingSource W) :
    OrderingSource W := loosened

/-- With náhodou, FALSUM^CZ quantifies over a larger set of worlds,
making the epistemic possibility condition easier to satisfy.
This is why náhodou is licensed in contexts where the speaker's evidence
is weaker — it signals willingness to explore remote possibilities. -/
theorem nahodou_widens_domain (ep : ModalBase W) (cv cvLoose : OrderingSource W)
    (cg p : Set W) (w : W)
    (hSubset : ∀ w', w' ∈ bestWorlds ep cv w → w' ∈ bestWorlds ep cvLoose w) :
    (mkFalsumCZ ep cv cg p).definedness w →
    (mkFalsumCZ ep cvLoose cg p).definedness w := by
  intro h
  simp only [mkFalsumCZ] at h ⊢
  -- If some world in Best(cv) satisfies p, and Best(cv) ⊆ Best(cvLoose),
  -- then some world in Best(cvLoose) satisfies p.
  obtain ⟨w', hw', hp⟩ := h
  exact ⟨w', hSubset w' hw', hp⟩

/-! ### Evidential-bias modal □_ev -/

/-- Evidential bias flavor (Staňková 2026 §3.1).

□_ev is a Kratzer necessity modal where:
- **Modal base**: the context set (what is established in the discourse)
- **Ordering source**: stereotypical/evidential (how "normal" a world is)
- **Force**: necessity

This captures evidential bias in PQs: the speaker's expectation about the
answer, derived from contextual evidence rather than prior epistemic state.
It corresponds to Romero's "contextual evidence bias" dimension. -/
structure EvidentialBiasFlavor (W : Type*) where
  contextBase : ModalBase W
  stereotypical : OrderingSource W

def EvidentialBiasFlavor.toKratzerParams (f : EvidentialBiasFlavor W) : KratzerParams W where
  base := f.contextBase
  ordering := f.stereotypical

/-- Evidential necessity: ∀w' ∈ Best(f,g,w). p(w'). -/
def evidentialNecessity (f : EvidentialBiasFlavor W) (p : Set W) (w : W) : Prop :=
  necessity f.contextBase f.stereotypical p w

/-- Evidential possibility: ∃w' ∈ Best(f,g,w). p(w'). -/
def evidentialPossibility (f : EvidentialBiasFlavor W) (p : Set W) (w : W) : Prop :=
  possibility f.contextBase f.stereotypical p w

/-- □_ev satisfies modal duality. One of five sibling `theorem duality`s — the
    box–diamond duality underlying the modal square of opposition
    (`Core.Logic.Modal.modalSquare_relations`). -/
theorem evidentialBias_duality (f : EvidentialBiasFlavor W) (p : Set W) (w : W) :
    evidentialNecessity f p w ↔ ¬ evidentialPossibility f (fun w' => ¬ p w') w := by
  unfold evidentialNecessity evidentialPossibility
  exact duality f.contextBase f.stereotypical p w

/-! ### Scope interactions: inner vs medial negation -/

/-- **Inner negation** scopes under □_ev: □_ev(¬p).

Strong evidential bias: based on the context, it must be that ¬p. -/
def innerBias (f : EvidentialBiasFlavor W) (p : Set W) (w : W) : Prop :=
  evidentialNecessity f (fun w' => ¬ p w') w

/-- **Medial negation** scopes over □_ev: ¬□_ev(p).

Weak evidential bias: it's not the case that p must hold. -/
def medialBias (f : EvidentialBiasFlavor W) (p : Set W) (w : W) : Prop :=
  ¬ evidentialNecessity f p w

/-- Inner bias entails medial bias given seriality (D axiom):
□_ev(¬p) → ¬□_ev(p), provided Best(f,g,w) is non-empty.

TODO: The seriality condition holds whenever the modal base is realistic
(cf. `Kratzer.realistic_is_serial`). -/
theorem inner_entails_medial (f : EvidentialBiasFlavor W) (p : Set W) (w : W)
    (hSerial : (bestWorlds f.contextBase f.stereotypical w).Nonempty)
    (hInner : innerBias f p w) :
    medialBias f p w := by
  simp only [medialBias, evidentialNecessity]
  rw [necessity_iff_all]
  simp only [innerBias, evidentialNecessity] at hInner
  rw [necessity_iff_all] at hInner
  intro hAll
  -- Best worlds is non-empty, so pick an element
  obtain ⟨w', hw'⟩ := hSerial
  exact hInner w' hw' (hAll w' hw')

/-! ### Focus requirement on FALSUM ([romero-2024])

Outer negation (FALSUM) is obligatorily focused.

FALSUM targets discourse polarity — whether p *is* or *is not* in the CommonGround.
Focus on FALSUM generates Rooth alternatives on polarity. The focus
semantic value of FALSUM is `{λw[p ∉ CommonGround], λw[p ∈ CommonGround]}`, computed by
`falsumAlternatives` below. -/

/-- FALSUM generates exactly two alternatives (polarity contrast). -/
def falsumAlternatives (cg p : Set W) :
    List (Set W) :=
  [ fun _ => ¬(∀ w', cg w' → p w')
  , fun _ => ∀ w', cg w' → p w' ]

theorem falsum_binary_alternatives (cg p : Set W) :
    (falsumAlternatives cg p).length = 2 := rfl

end Semantics.Questions.Bias
