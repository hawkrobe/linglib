import Linglib.Theories.Semantics.Modality.Kratzer
import Linglib.Core.CommonGround
import Linglib.Core.InformationStructure

/-!
# Biased Polar Questions

Cross-linguistic framework for polar question bias, following Romero (2024).
Polar questions come in three forms — PosQ, LoNQ, HiNQ — which differ in
sensitivity to two independent bias dimensions: original speaker bias and
contextual evidence bias.

## Two Bias Dimensions

1. **Original speaker bias** (Ladd 1981): The speaker's prior epistemic state
   (belief/expectation) about p *before* the current exchange.
2. **Contextual evidence bias** (Büring & Gunlogson 2000): Expectation about p
   induced by evidence that becomes available *during* the current exchange.

## Three Theoretical Lines for High Negation

Romero (2020) clusters analyses into three lines:
- **Line a** (AnderBois 2011, 2019): Σ_neg at the expressed proposition level
- **Line b** (Repp 2013, Romero 2015, Frana & Rawlins 2019): VERUM/FALSUM
- **Line c** (Goodhue 2018, 2022c): ¬ASSERT at the speech act level

We formalize VERUM and FALSUM (line b) using existing Kratzer modal and
CommonGround infrastructure, as this is the line adopted by Staňková (2026)
for Czech.

## References

- Romero, M. (2024). Biased Polar Questions. Annual Review of Linguistics 10:279–302.
- Ladd, R. (1981). A first look at the semantics and pragmatics of negative
  questions and tag questions. CLS 17.
- Büring, D. & Gunlogson, C. (2000). Aren't positive and negative polar questions
  the same? UCSC/UCLA.
- Romero, M. & Han, C. (2004). On negative yes/no questions. L&P 27.
- Repp, S. (2013). Common ground management. In Beyond Expressives.
- Romero, M. (2015). High negation in subjunctive conditionals and polar questions.
- Frana, I. & Rawlins, K. (2019). Attitudes in compositional alternative semantics.
- Goodhue, D. (2022). It's not just what you say, it's how you say it. L&P.
- AnderBois, S. (2019). Negation, alternatives, and negative polar questions. In SALT 29.
- Domaneschi, F. et al. (2017). N-words and sentential negation: Evidence from
  polarity, scope and discourse. LI 48(3).
- Staňková, V. (2026). A three-way distinction of negation interpretation in Czech.
- Šimík, R. (2024). Polar question semantics and bias: Lessons from Slavic/Czech.
  In B. Gehrke & R. Šimík (eds.), Topics in the semantics of Slavic languages. Language Science Press.
-/

namespace Semantics.Modality.BiasedPQ

open Semantics.Modality.Kratzer
open Semantics.Attitudes.Intensional
open Core.CommonGround
open Core.Proposition

-- ============================================================================
-- §1: PQ Form Typology (Romero 2024 §1)
-- ============================================================================

/-- The three polar question forms (Romero 2024 §1, exx. 1–3).

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
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- §2: Bias Typology (Romero 2024 §2)
-- ============================================================================

/-- Original speaker bias (Ladd 1981, Romero & Han 2004).

Belief or expectation of the speaker that p is true, based on her epistemic
state *prior to* the current situational context and conversational exchange
(Domaneschi et al. 2017). -/
inductive OriginalBias where
  /-- Speaker originally expected/believed p. -/
  | forP
  /-- Speaker had no prior expectation about p. -/
  | neutral
  /-- Speaker originally expected/believed ¬p. -/
  | againstP
  deriving DecidableEq, BEq, Repr

/-- Contextual evidence bias (Büring & Gunlogson 2000).

Expectation that p is true induced by evidence that has just become mutually
available to the participants in the current discourse situation. May
contradict the speaker's original belief. -/
inductive ContextualEvidence where
  /-- Current context provides evidence for p. -/
  | forP
  /-- No contextual evidence either way. -/
  | neutral
  /-- Current context provides evidence against p. -/
  | againstP
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- §3: Romero's Table 1 — Original Speaker Bias (Ladd 1981, R&H 2004)
-- ============================================================================

/-- Original speaker bias conditions on PQ forms (Romero 2024 Table 1).

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

/-- HiNQs mandatorily convey original speaker bias for p (Ladd 1981, R&H 2004). -/
theorem hiNQ_requires_bias_for_p :
    originalBiasOK .HiNQ .neutral = false ∧
    originalBiasOK .HiNQ .againstP = false ∧
    originalBiasOK .HiNQ .forP = true := ⟨rfl, rfl, rfl⟩

/-- PosQs can be used in neutral contexts. -/
theorem posQ_neutral_ok : originalBiasOK .PosQ .neutral = true := rfl

/-- LoNQs can be neutral. -/
theorem loNQ_neutral_ok : originalBiasOK .LoNQ .neutral = true := rfl

-- ============================================================================
-- §4: Romero's Table 2 — Contextual Evidence Bias (B&G 2000)
-- ============================================================================

/-- Contextual evidence bias conditions on PQ forms (Romero 2024 Table 2,
Büring & Gunlogson 2000).

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

/-- LoNQs require contextual evidence against p (B&G 2000). -/
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
-- §5: VERUM (Romero & Han 2004, Romero 2024 def. 30)
-- ============================================================================

/-- VERUM operator (Romero & Han 2004, line b).

⟦VERUM_x⟧ = λp. λw. ∀w' ∈ Epi_x(w). ∀w'' ∈ Conv_x(w'). [p ∈ CG]

"x is sure that p should be added to the Common Ground."

We model this as: in all epistemically accessible worlds where the speaker's
conversational goals are fulfilled, p is in the CG. This is a double universal:
necessity over epistemic alternatives, then necessity over conversational goals. -/
def verum (epistemic : ModalBase) (conversational : OrderingSource)
    (cg : BContextSet World) (p : BProp World) (w : World) : Bool :=
  -- For all best epistemic worlds w': in the CG induced at w', p holds
  (bestWorlds epistemic conversational w).all λ w' =>
    -- p is entailed by the context set at w'
    cg w' && p w'

/-- FALSUM operator (Repp 2013, Romero 2015, Romero 2024 def. 33).

At-issue content: ¬p
CG-management content: ∀w' ∈ Epi(w). ∀w'' ∈ Conv(w'). [p ∉ CG]

"x is sure that p should NOT be added to the Common Ground."

FALSUM is the CG-management negation of VERUM. The at-issue content
is simply ¬p, while the non-at-issue content (CG-management) expresses
that p is not to become common ground. -/
structure FalsumContent where
  /-- At-issue content: ¬p -/
  atIssue : BProp World
  /-- CG-management: p should not be added to CG.
      Modeled as: the speaker considers it epistemically possible that p,
      but p is not CG-entailed. -/
  cgManagement : World → Prop

/-- Construct FALSUM content for a proposition p. -/
def mkFalsum (epistemic : ModalBase) (conversational : OrderingSource)
    (cg : BContextSet World) (p : BProp World) : FalsumContent where
  atIssue := λ w => !p w
  cgManagement := λ w =>
    -- Speaker considers p epistemically possible
    (bestWorlds epistemic conversational w).any p = true ∧
    -- But p is not entailed by the CG
    ¬(∀ w', cg w' = true → p w' = true)

/-- FALSUM's at-issue content is propositional negation. -/
theorem falsum_atIssue_is_negation (ep : ModalBase) (cv : OrderingSource)
    (cg : BContextSet World) (p : BProp World) (w : World) :
    (mkFalsum ep cv cg p).atIssue w = !p w := rfl

-- ============================================================================
-- §5b: FALSUM^CZ (Šimík 2024 §5, eq. 44)
-- ============================================================================

/-- Czech FALSUM (Šimík 2024 eq. 44), weaker than standard FALSUM (Repp 2013).

⟦FALSUM_1^CZ⟧^g(p) = λw : ∃w' ∈ EPI_{g(1)}(w)[p(w') = 1] . p ∉ CG_w

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
structure FalsumCZ where
  /-- At-issue content: ¬p (same as standard FALSUM) -/
  atIssue : BProp World
  /-- Presupposition: attitude holder considers p epistemically possible.
      This is the definedness condition — the question is defined only if
      the attitude holder considers the positive prejacent possible. -/
  definedness : World → Prop
  /-- CG-management: p is not part of the common ground at w. -/
  cgContent : World → Prop

/-- Construct Šimík's FALSUM^CZ for a proposition p.

The attitude holder's epistemic state is modeled via the modal base
(their epistemic alternatives). -/
def mkFalsumCZ (attitudeEpi : ModalBase) (ordering : OrderingSource)
    (cg : BContextSet World) (p : BProp World) : FalsumCZ where
  atIssue := λ w => !p w
  definedness := λ w =>
    -- ∃w' ∈ EPI(w). p(w') = true — epistemic possibility
    (bestWorlds attitudeEpi ordering w).any p = true
  cgContent := λ w =>
    -- p ∉ CG_w
    ¬(∀ w', cg w' = true → p w' = true)

/-- FALSUM^CZ at-issue content is still propositional negation. -/
theorem falsumCZ_atIssue_is_negation (ep : ModalBase) (cv : OrderingSource)
    (cg : BContextSet World) (p : BProp World) (w : World) :
    (mkFalsumCZ ep cv cg p).atIssue w = !p w := rfl

/-- Standard FALSUM entails FALSUM^CZ definedness: if the speaker *believes* p
is possible (necessity over goals), then they certainly *consider* it possible.
This captures why standard FALSUM is a special case of FALSUM^CZ. -/
theorem standard_falsum_entails_CZ_definedness
    (ep : ModalBase) (cv : OrderingSource) (cg : BContextSet World) (p : BProp World) (w : World)
    (hStd : (bestWorlds ep cv w).any p = true) :
    (mkFalsumCZ ep cv cg p).definedness w :=
  hStd

-- ============================================================================
-- §5c: Náhodou as Ordering Source Modifier (Šimík 2024 §5.1)
-- ============================================================================

/-- *Náhodou* 'by chance' loosens the stereotypical ordering source of
FALSUM^CZ to include more remote (less stereotypical) possibilities.

Šimík (2024 §5.1): "its function is to 'loosen' the default stereotypical
ordering source of the epistemic modal contributed by FALSUM so as to
include more remote (less likely) possibilities in the quantification domain
of the modal."

Formally, náhodou replaces the ordering source g with a weaker g' such that
Best(f, g', w) ⊇ Best(f, g, w). The resulting proposition is stronger because
ruling out p in less likely worlds entails ruling it out in more likely worlds. -/
def loosenOrderingSource (_ : OrderingSource) (loosened : OrderingSource) :
    OrderingSource := loosened

/-- With náhodou, FALSUM^CZ quantifies over a larger set of worlds,
making the epistemic possibility condition easier to satisfy.
This is why náhodou is licensed in contexts where the speaker's evidence
is weaker — it signals willingness to explore remote possibilities. -/
theorem nahodou_widens_domain (ep : ModalBase) (cv cvLoose : OrderingSource)
    (cg : BContextSet World) (p : BProp World) (w : World)
    (hSubset : ∀ w', w' ∈ bestWorlds ep cv w → w' ∈ bestWorlds ep cvLoose w) :
    (mkFalsumCZ ep cv cg p).definedness w →
    (mkFalsumCZ ep cvLoose cg p).definedness w := by
  intro h
  simp only [mkFalsumCZ] at h ⊢
  -- If some world in Best(cv) satisfies p, and Best(cv) ⊆ Best(cvLoose),
  -- then some world in Best(cvLoose) satisfies p.
  rw [List.any_eq_true] at h ⊢
  obtain ⟨w', hw', hp⟩ := h
  exact ⟨w', List.mem_of_subset hSubset hw', hp⟩
  where
    List.mem_of_subset {α : Type} {l1 l2 : List α} {x : α}
        (h : ∀ y, y ∈ l1 → y ∈ l2) (hx : x ∈ l1) : x ∈ l2 :=
      h x hx

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
structure EvidentialBiasFlavor where
  contextBase : ModalBase
  stereotypical : OrderingSource

def EvidentialBiasFlavor.toKratzerParams (f : EvidentialBiasFlavor) : KratzerParams where
  base := f.contextBase
  ordering := f.stereotypical

/-- Evidential necessity: ∀w' ∈ Best(f,g,w). p(w'). -/
def evidentialNecessity (f : EvidentialBiasFlavor) (p : BProp World) (w : World) : Bool :=
  necessity f.contextBase f.stereotypical p w

/-- Evidential possibility: ∃w' ∈ Best(f,g,w). p(w'). -/
def evidentialPossibility (f : EvidentialBiasFlavor) (p : BProp World) (w : World) : Bool :=
  possibility f.contextBase f.stereotypical p w

/-- □_ev satisfies modal duality. -/
theorem evidentialBias_duality (f : EvidentialBiasFlavor) (p : BProp World) (w : World) :
    (evidentialNecessity f p w == !evidentialPossibility f (λ w' => !p w') w) = true :=
  duality f.contextBase f.stereotypical p w

-- ============================================================================
-- §7: Scope Interactions (Staňková 2026 §3.1)
-- ============================================================================

/-- **Inner negation** scopes under □_ev: □_ev(¬p).

Strong evidential bias: based on the context, it must be that ¬p. -/
def innerBias (f : EvidentialBiasFlavor) (p : BProp World) (w : World) : Bool :=
  evidentialNecessity f (λ w' => !p w') w

/-- **Medial negation** scopes over □_ev: ¬□_ev(p).

Weak evidential bias: it's not the case that p must hold. -/
def medialBias (f : EvidentialBiasFlavor) (p : BProp World) (w : World) : Bool :=
  !evidentialNecessity f p w

/-- Inner bias entails medial bias given seriality (D axiom):
□_ev(¬p) → ¬□_ev(p), provided Best(f,g,w) is non-empty.

TODO: The seriality condition holds whenever the modal base is realistic
(cf. `Kratzer.realistic_is_serial`). -/
theorem inner_entails_medial (f : EvidentialBiasFlavor) (p : BProp World) (w : World)
    (hSerial : (bestWorlds f.contextBase f.stereotypical w).length > 0)
    (hInner : innerBias f p w = true) :
    medialBias f p w = true := by
  simp only [medialBias, Bool.not_eq_true']
  simp only [innerBias, evidentialNecessity, necessity] at hInner
  simp only [evidentialNecessity, necessity]
  -- hInner: best.all (λ w' => !p w') = true. Goal: best.all p = false.
  -- If best is non-empty, some w' satisfies !p w', so p w' = false, so best.all p = false.
  match hBest : bestWorlds f.contextBase f.stereotypical w with
  | [] => simp only [hBest, List.length_nil, gt_iff_lt, Nat.lt_irrefl] at hSerial
  | w' :: ws =>
    simp only [hBest, List.all_cons] at hInner
    -- hInner : ((!p w') && (ws.all fun w' => !p w')) = true
    -- We need: (p w' && ws.all p) = false
    simp only [hBest, List.all_cons]
    -- Goal: (p w' && ws.all p) = false
    -- From hInner, !p w' = true (first conjunct), so p w' = false
    cases hp : p w'
    · -- p w' = false
      simp only [hp, Bool.false_and]
    · -- p w' = true, but hInner says p w' = false — contradiction
      simp [hp] at hInner

-- ============================================================================
-- §8: Focus Requirement on FALSUM (Romero 2024 §3.2, Staňková 2026 §4)
-- ============================================================================

/-- Outer negation (FALSUM) is obligatorily focused (Staňková 2026 §3.2, §4).

FALSUM targets discourse polarity — whether p *is* or *is not* in the CG.
Focus on FALSUM generates Rooth alternatives on polarity.

The focus semantic value of FALSUM: {λw[p ∉ CG], λw[p ∈ CG]}. -/
def falsumFocusRequirement : Core.InformationStructure.DiscourseStatus :=
  .focused

/-- FALSUM generates exactly two alternatives (polarity contrast). -/
def falsumAlternatives (cg : BContextSet World) (p : BProp World) :
    List (World → Prop) :=
  [ λ _ => ¬(∀ w', cg w' = true → p w' = true)
  , λ _ => ∀ w', cg w' = true → p w' = true ]

theorem falsum_binary_alternatives (cg : BContextSet World) (p : BProp World) :
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
  deriving DecidableEq, BEq, Repr

end Semantics.Modality.BiasedPQ
