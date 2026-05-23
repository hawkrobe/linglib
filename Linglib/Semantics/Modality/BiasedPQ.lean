import Linglib.Semantics.Modality.Kratzer.Flavor
import Linglib.Discourse.CommonGround
import Linglib.Core.Discourse.IllocutionaryForce
import Linglib.Core.Discourse.Intentionality
import Linglib.Core.Discourse.Commitment
import Mathlib.Data.Set.Basic

/-!
# Biased Polar Questions
@cite{bring-gunlogson-2000} @cite{ladd-1981} @cite{repp-2013} @cite{romero-2019} @cite{romero-2024} @cite{romero-han-2004} @cite{simik-2024} @cite{stankova-2025}

Cross-linguistic framework for polar question bias, following @cite{romero-2024}.
Polar questions come in three forms — PosQ, LoNQ, HiNQ — which differ in
sensitivity to two independent bias dimensions: original speaker bias and
contextual evidence bias.

## Two Bias Dimensions

1. **Original speaker bias**: The speaker's prior epistemic state
   (belief/expectation) about p *before* the current exchange.
2. **Contextual evidence bias**: Expectation about p
   induced by evidence that becomes available *during* the current exchange.

## Three Theoretical Lines for High Negation

@cite{romero-2020} clusters analyses into three lines:
- **Line a**: Σ_neg at the expressed proposition level
- **Line b**: VERUM/FALSUM
- **Line c**: ¬ASSERT at the speech act level

We formalize VERUM and FALSUM (line b) using existing Kratzer modal and
CommonGround infrastructure, as this is the line adopted by Staňková (2026)
for Czech.

-/

namespace Semantics.Modality.BiasedPQ

open Semantics.Modality.Kratzer
open Discourse.CommonGround

variable {W : Type*}

-- ============================================================================
-- §1: PQ Form Typology (@cite{romero-2024} §1)
-- ============================================================================

/-- The three polar question forms (@cite{romero-2024} §1, exx. 1–3).

These forms are cross-linguistically attested and constitute the fundamental
typology for polar question bias research. -/
inductive PQForm where
  /-- Positive question: [p?]. "Is Jane coming?" -/
  | PosQ
  /-- Low negation question: [not p?]. "Is Jane not coming?" -/
  | LoNQ
  /-- High negation question: [n't p?]. "Isn't Jane coming?"
      In Czech: interrogative (VSO) word order. -/
  | HiNQ
  deriving DecidableEq, Repr

-- ============================================================================
-- §2: Bias Typology (@cite{romero-2024} §2)
-- ============================================================================

/-- Original speaker bias.

Belief or expectation of the speaker that p is true, based on her epistemic
state *prior to* the current situational context and conversational exchange. -/
inductive OriginalBias where
  /-- Speaker originally expected/believed p. -/
  | forP
  /-- Speaker had no prior expectation about p. -/
  | neutral
  /-- Speaker originally expected/believed ¬p. -/
  | againstP
  deriving DecidableEq, Repr

-- Re-export `ContextualEvidence` from Core so that downstream files
-- opening `Semantics.Modality.BiasedPQ` still find it here.
export Core.Discourse.Commitment (ContextualEvidence)

-- ============================================================================
-- §3: Romero's Table 1 — Original Speaker Bias (@cite{ladd-1981}, @cite{romero-han-2004})
-- ============================================================================

/-- Original speaker bias conditions on PQ forms (@cite{romero-2024} Table 1).

Only HiNQ *mandatorily* conveys original speaker bias for p. LoNQ can convey
bias for p but can also be neutral. PosQ is compatible with bias for ¬p or
neutrality but was not tested for bias for p. -/
def originalBiasOK : PQForm → OriginalBias → Bool
  | .PosQ, .forP     => true   -- not tested by R&H but compatible
  | .PosQ, .neutral   => true
  | .PosQ, .againstP  => true
  | .LoNQ, .forP      => true
  | .LoNQ, .neutral   => true
  | .LoNQ, .againstP  => false -- not tested
  | .HiNQ, .forP      => true  -- mandatory: HiNQ conveys bias for p
  | .HiNQ, .neutral   => false -- HiNQ is infelicitous without bias
  | .HiNQ, .againstP  => false

/-- HiNQs mandatorily convey original speaker bias for p (@cite{ladd-1981}, @cite{romero-han-2004}). -/
theorem hiNQ_requires_bias_for_p :
    originalBiasOK .HiNQ .neutral = false ∧
    originalBiasOK .HiNQ .againstP = false ∧
    originalBiasOK .HiNQ .forP = true := ⟨rfl, rfl, rfl⟩

/-- PosQs can be used in neutral contexts. -/
theorem posQ_neutral_ok : originalBiasOK .PosQ .neutral = true := rfl

/-- LoNQs can be neutral. -/
theorem loNQ_neutral_ok : originalBiasOK .LoNQ .neutral = true := rfl

-- ============================================================================
-- §4: Romero's Table 2 — Contextual Evidence Bias (@cite{bring-gunlogson-2000})
-- ============================================================================

/-- Contextual evidence bias conditions on PQ forms (@cite{romero-2024} Table 2,
@cite{bring-gunlogson-2000}).

PosQ requires evidence for p (or neutral). LoNQ requires evidence against p.
Outer-HiNQ is felicitous with neutral or against-p evidence. -/
def evidenceBiasOK : PQForm → ContextualEvidence → Bool
  | .PosQ, .forP      => true
  | .PosQ, .neutral    => true
  | .PosQ, .againstP   => false
  | .LoNQ, .forP       => false
  | .LoNQ, .neutral    => false
  | .LoNQ, .againstP   => true
  | .HiNQ, .forP       => false
  | .HiNQ, .neutral    => true
  | .HiNQ, .againstP   => true

/-- LoNQs require contextual evidence against p (@cite{bring-gunlogson-2000}). -/
theorem loNQ_requires_evidence_against_p :
    evidenceBiasOK .LoNQ .forP = false ∧
    evidenceBiasOK .LoNQ .neutral = false ∧
    evidenceBiasOK .LoNQ .againstP = true := ⟨rfl, rfl, rfl⟩

/-- HiNQs are felicitous with evidence against p (contradiction scenarios). -/
theorem hiNQ_evidence_against_ok :
    evidenceBiasOK .HiNQ .againstP = true := rfl

/-- HiNQs are also felicitous with neutral evidence (suggestion scenarios). -/
theorem hiNQ_evidence_neutral_ok :
    evidenceBiasOK .HiNQ .neutral = true := rfl

-- ============================================================================
-- §5: VERUM (@cite{romero-han-2004}, @cite{romero-2024} def. 30)
-- ============================================================================

/-- VERUM operator (@cite{romero-han-2004}, line b).

⟦VERUM_x⟧ = λp. λw. ∀w' ∈ Epi_x(w). ∀w'' ∈ Conv_x(w'). [p ∈ CG]

"x is sure that p should be added to the Common Ground."

We model this as: in all epistemically accessible worlds where the speaker's
conversational goals are fulfilled, p is in the CG. This is a double universal:
necessity over epistemic alternatives, then necessity over conversational goals. -/
def verum (epistemic : ModalBase W) (conversational : OrderingSource W)
    (cg p : Set W) (w : W) : Prop :=
  -- For all best epistemic worlds w': in the CG induced at w', p holds
  ∀ w' ∈ bestWorlds epistemic conversational w, cg w' ∧ p w'

/-- FALSUM operator (@cite{repp-2013}, @cite{romero-2019}, @cite{romero-2024} def. 33).

At-issue content: ¬p
CG-management content: ∀w' ∈ Epi(w). ∀w'' ∈ Conv(w'). [p ∉ CG]

"x is sure that p should NOT be added to the Common Ground."

FALSUM is the CG-management negation of VERUM. The at-issue content
is simply ¬p, while the non-at-issue content (CG-management) expresses
that p is not to become common ground. -/
structure FalsumContent (W : Type*) where
  /-- At-issue content: ¬p -/
  atIssue : Set W
  /-- CG-management: p should not be added to CG.
      Modeled as: the speaker considers it epistemically possible that p,
      but p is not CG-entailed. -/
  cgManagement : Set W

/-- Construct FALSUM content for a proposition p. -/
def mkFalsum (epistemic : ModalBase W) (conversational : OrderingSource W)
    (cg p : Set W) : FalsumContent W where
  atIssue := fun w => ¬ p w
  cgManagement := fun w =>
    -- Speaker considers p epistemically possible
    (∃ w' ∈ bestWorlds epistemic conversational w, p w') ∧
    -- But p is not entailed by the CG
    ¬(∀ w', cg w' → p w')

/-- FALSUM's at-issue content is propositional negation. -/
theorem falsum_atIssue_is_negation (ep : ModalBase W) (cv : OrderingSource W)
    (cg p : Set W) (w : W) :
    (mkFalsum ep cv cg p).atIssue w ↔ ¬ p w := Iff.rfl

-- ============================================================================
-- §5b: FALSUM^CZ (@cite{simik-2024} §5, eq. 44)
-- ============================================================================

/-- Czech FALSUM (@cite{simik-2024} eq. 44), weaker than standard FALSUM.

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
  /-- CG-management: p is not part of the common ground at w. -/
  cgContent : Set W

/-- Construct @cite{simik-2024}'s FALSUM^CZ for a proposition p.

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

-- ============================================================================
-- §5c: Náhodou as Ordering Source Modifier (@cite{simik-2024} §5.1)
-- ============================================================================

/-- *Náhodou* 'by chance' loosens the stereotypical ordering source of
FALSUM^CZ to include more remote (less stereotypical) possibilities.

@cite{simik-2024} §5.1: "its function is to 'loosen' the default stereotypical
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

-- ============================================================================
-- §6: Evidential Bias Modal □_ev (Staňková 2026 §3.1)
-- ============================================================================

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

/-- □_ev satisfies modal duality. One of five sibling `theorem duality`s
    (see `Modality/Kratzer/Operators.lean::duality` for the unification
    opportunity via `Core.Logic.Opposition.Square.fromBox`). -/
theorem evidentialBias_duality (f : EvidentialBiasFlavor W) (p : Set W) (w : W) :
    evidentialNecessity f p w ↔ ¬ evidentialPossibility f (fun w' => ¬ p w') w := by
  unfold evidentialNecessity evidentialPossibility
  exact duality f.contextBase f.stereotypical p w

-- ============================================================================
-- §7: Scope Interactions (Staňková 2026 §3.1)
-- ============================================================================

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

-- ============================================================================
-- §8: Focus Requirement on FALSUM (@cite{romero-2024} §3.2, Staňková 2026 §4)
-- ============================================================================

/-! Outer negation (FALSUM) is obligatorily focused (Staňková 2026 §3.2, §4).

FALSUM targets discourse polarity — whether p *is* or *is not* in the CG.
Focus on FALSUM generates Rooth alternatives on polarity. The focus
semantic value of FALSUM is `{λw[p ∉ CG], λw[p ∈ CG]}`, computed by
`falsumAlternatives` below. -/

/-- FALSUM generates exactly two alternatives (polarity contrast). -/
def falsumAlternatives (cg p : Set W) :
    List (Set W) :=
  [ fun _ => ¬(∀ w', cg w' → p w')
  , fun _ => ∀ w', cg w' → p w' ]

theorem falsum_binary_alternatives (cg p : Set W) :
    (falsumAlternatives cg p).length = 2 := rfl

-- ============================================================================
-- §9: Cross-Linguistic Bridge
-- ============================================================================

/-- Strength of evidential bias associated with a negation scope configuration.

This bridges Romero's two-dimensional bias typology to Staňková's
three-way Czech distinction:
- Inner neg → strong contextual evidence bias (must be ¬p)
- Medial neg → weak contextual evidence bias (doesn't have to be p)
- Outer neg (FALSUM) → original speaker bias, no □_ev involvement -/
inductive EvidentialBiasStrength where
  | strong  -- Inner: □_ev(¬p)
  | weak    -- Medial: ¬□_ev(p)
  | none_   -- Outer: FALSUM, not □_ev-based
  deriving DecidableEq, Repr

end Semantics.Modality.BiasedPQ
