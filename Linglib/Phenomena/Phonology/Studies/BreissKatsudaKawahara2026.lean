import Linglib.Fragments.Japanese.Prosody
import Linglib.Theories.Phonology.LexicalFrequency.Defs
import Linglib.Theories.Phonology.LexicalFrequency.ScaledWeights
import Linglib.Theories.Phonology.LexicalFrequency.RepresentationStrength
import Linglib.Theories.Phonology.LexicalFrequency.IndexedConstraints
import Linglib.Theories.Phonology.LexicalFrequency.UseListed
import Linglib.Theories.Phonology.ParadigmUniformity.Defs
import Linglib.Theories.Phonology.ParadigmUniformity.LexicalConservatism
import Linglib.Theories.Phonology.ParadigmUniformity.OptimalParadigms
import Linglib.Paradigms.WugTest

/-!
# Breiss, Katsuda & Kawahara (2026): Token frequency modulates optional paradigm uniformity in Japanese voiced velar nasalisation
@cite{breiss-katsuda-kawahara-2026} @cite{mccarthy-2005} @cite{steriade-2000}
@cite{ito-mester-1996} @cite{ito-mester-2003} @cite{hibiya-1995}
@cite{coetzee-pater-2008} @cite{paster-2019}

The Japanese velar /g/ → [ŋ] alternation in N1+N2 nominal compounds is
*optional*: speakers vacillate between [g] and [ŋ] for many compounds,
and the rate of nasalisation varies across compounds, items, and
speakers. The paper's central architectural claim is that this
optionality is **modulated by token frequency** through **two
opposite-sign channels**:

- High token frequency of **N2 as a free wordform** *decreases* the
  rate of nasalisation (negative regression coefficient on N2 token
  frequency). The free-form [g] is a more accessible paradigm exemplar;
  paradigm-uniformity pressure preserves it, suppressing [ŋ].
- High token frequency of **the compound itself** *increases* the rate
  of nasalisation (positive regression coefficient on compound token
  frequency). More-attested compounds drift further from their
  constituent forms.

Both effects only apply when N2 is morphologically **free**. When N2 is
**bound** (occurs only inside compounds — no surface [g] paradigm
exemplar to anchor to), nasalisation is categorically obligatory. The
two-channel frequency story collapses to a single-channel (markedness-
only) story in the bound case.

## Examples from the paper

Taken verbatim from @cite{breiss-katsuda-kawahara-2026}:

- (1a) /haigan/ ~ /haiŋan/ "lung cancer" — N2 'cancer' (癌) is free.
- (1b) /noogeka/ ~ /nooŋeka/ "brain surgery" — N2 'surgery' (外科) is free.
- (2a) /dokuga/ ~ /dokuŋa/ "poison moth" — N2 'moth' (蛾) is free.
- (2b) /dokuŋa/ \*[dokuga] "poison fang" — N2 'fang' (牙) is **bound**.
- (3) /gaʒoo/ "main castle" — initial-position [g] never nasalises.

The minimal pair (2a)/(2b) is the paper's central piece of evidence:
two compounds with identical surface form */dokuga/* but different
free/bound status of the segmentally-identical N2 yield categorically
different nasalisation behaviour.

## Connection to Paradigm Uniformity

The architecture is **paradigm uniformity (PU) + frequency-conditioned
strength**. The compound and its free N2 stand in a paradigm relation;
PU prefers their shared segments to be alike. The PU pressure is
*modulated* — not just on/off — by the token frequency of the N2.
This puts the paper at the intersection of:

- @cite{mccarthy-2005} (PU as the symmetric pairwise lift over members;
  see `ParadigmUniformity/OptimalParadigms.lean`).
- @cite{steriade-2000} *Lexical Conservatism* (PU pressure is anchored
  on attested wordforms; see
  `ParadigmUniformity/LexicalConservatism.lean`).
- @cite{coetzee-pater-2008} *Frequency-scaled weights* (the modulation
  channel — token-frequency drives a continuous weight; see
  `LexicalFrequency/ScaledWeights.lean`).

The previous constraint-based account of @cite{ito-mester-1996} /
@cite{ito-mester-2003} treats nasalisation as the result of a
high-ranked markedness constraint; @cite{hibiya-1995}'s sociolinguistic
study established the variable, lexically-modulated character of the
alternation. BKK 2026's contribution is the **sign of the two
frequency channels** and the **architectural commitment** that the
two-direction story collapses to one direction in the bound case.

## Connection to LexicalFrequency theories

The companion modelling paper (Breiss, Katsuda & Kawahara,
lingbuzz/009508) fits a MaxEnt grammar with @cite{steriade-2000}'s
Lexical Conservatism. We do not formalise the fitting routine here.
The discrimination this study makes against the four siblings in
`Theories/Phonology/LexicalFrequency/`:

- **ScaledWeights** (@cite{coetzee-pater-2008}): consistent with the
  data, with separate slopes per channel (positive on cpd freq,
  negative on N2 freq).
- **RepresentationStrength** (@cite{moore-cantwell-2021}): consistent —
  high N2 activation preserves the boundary segment.
- **UseListed** (@cite{zuraw-2000}): **ruled out** by Experiment 2
  (novel compounds show the same N2-frequency gradient as familiar
  ones) — see `novel_compounds_show_n2_gradient` below.
- **Indexed constraints** (@cite{pater-2010}): in principle a
  multi-stratum approximation could fit, but parsimony favours the
  continuous accounts.

@cite{paster-2019}'s critique of "counting" patterns in phonology is
relevant to BKK Experiment 2's finding that **N2 length** (not total
compound length) matters — undermining a mora-counting analysis and
favouring a paradigm-anchored account.

## Boundary

- We formalise the qualitative direction-of-effect predictions, not
  numerical fits, sample sizes, or specific corpus statistics.
- "Optional" is taken at face value as variable surface realisation;
  we do not commit to a stochastic OT vs. MaxEnt vs. mixed-effects
  encoding of the variation. The relevant fact for downstream theory
  is only that nasalisation rate is monotonic in the relevant
  log-frequency, with the appropriate sign per channel.
- The wug-test methodological contract lives in
  `Paradigms/WugTest.lean`; this file consumes that paradigm via the
  `novel_compounds_show_n2_gradient` discriminator.
-/

namespace Phenomena.Phonology.Studies.BreissKatsudaKawahara2026

open Fragments.Japanese.Prosody
open Phonology.LexicalFrequency
open Phonology.LexicalFrequency.Scaled (scaledWeight)
open Phonology.ParadigmUniformity (liftPairwise lcParadigm mkLCFaith lc_unanchored_zero)
open Paradigms.WugTest (Attestation HasFactor HasAttestation HasFrequency Rate
  NovelShowsFreqGradient NovelInvariantInFrequency
  novelGradient_inconsistent_with_invariance)
open Core.Constraint.OT (NamedConstraint ConstraintFamily)

-- ============================================================================
-- § 1: Real lexical entries from the paper
-- ============================================================================

/-- *hai* 'lung' (肺) — N1 of /haigan/ "lung cancer", example (1a). -/
def n1_hai : JLexicalEntry :=
  { form := "hai", gloss := "lung",
    accentMora := some 0, nMorae := 2,
    tokenLogFreq := 5, canStandAlone := true }

/-- *gan* 'cancer' (癌) — high-token-frequency free N2.
    Free-form [g] is well-attested; PU pressure should be strong,
    suppressing nasalisation. Example (1a). -/
def n2_gan : JLexicalEntry :=
  { form := "gan", gloss := "cancer",
    accentMora := some 0, nMorae := 2,
    tokenLogFreq := 9, canStandAlone := true }

/-- *noo* 'brain' (脳) — N1 of /noogeka/ "brain surgery", example (1b). -/
def n1_noo : JLexicalEntry :=
  { form := "noo", gloss := "brain",
    accentMora := some 0, nMorae := 2,
    tokenLogFreq := 5, canStandAlone := true }

/-- *geka* 'surgery' (外科) — free N2, mid-frequency. Example (1b). -/
def n2_geka : JLexicalEntry :=
  { form := "geka", gloss := "surgery",
    accentMora := some 0, nMorae := 3,
    tokenLogFreq := 6, canStandAlone := true }

/-- *doku* 'poison' (毒) — N1 of both /dokuga/ "poison moth" and
    /dokuŋa/ "poison fang" — the minimal pair (2a)/(2b). -/
def n1_doku : JLexicalEntry :=
  { form := "doku", gloss := "poison",
    accentMora := some 0, nMorae := 2,
    tokenLogFreq := 5, canStandAlone := true }

/-- *ga* 'moth' (蛾) — low-frequency *free* N2. The free /ga/ standalone
    supplies the PU anchor. Example (2a). -/
def n2_ga_moth : JLexicalEntry :=
  { form := "ga", gloss := "moth",
    accentMora := some 0, nMorae := 1,
    tokenLogFreq := 1, canStandAlone := true }

/-- *ga* 'fang' (牙) — *bound* N2; never appears as a free wordform.
    With no /ga/ anchor, PU pressure is null and nasalisation is
    categorical. The minimal-pair partner of `n2_ga_moth`. Example (2b). -/
def n2_ga_fang : JLexicalEntry :=
  { form := "ga", gloss := "fang",
    accentMora := some 0, nMorae := 1,
    tokenLogFreq := 0, canStandAlone := false }

-- ============================================================================
-- § 2: Real compounds from the paper
-- ============================================================================

/-- /haigan/ "lung cancer" — example (1a). High-frequency free N2. -/
def cpd_haigan : JCompound :=
  { n1 := n1_hai, n2 := n2_gan, compoundLogFreq := 4 }

/-- /noogeka/ "brain surgery" — example (1b). Mid-frequency free N2. -/
def cpd_noogeka : JCompound :=
  { n1 := n1_noo, n2 := n2_geka, compoundLogFreq := 3 }

/-- /dokuga/ "poison moth" — example (2a). Low-frequency free N2;
    optional nasalisation. -/
def cpd_dokuga : JCompound :=
  { n1 := n1_doku, n2 := n2_ga_moth, compoundLogFreq := 2 }

/-- /dokuŋa/ "poison fang" — example (2b). Bound N2 → categorical [ŋ]. -/
def cpd_dokunga : JCompound :=
  { n1 := n1_doku, n2 := n2_ga_fang, compoundLogFreq := 2 }

-- ============================================================================
-- § 3: Bound vs. free split — the categorical/gradient boundary
-- ============================================================================

/-- The bound case: `JCompound.nasalisationObligatory` returns `true`. -/
theorem dokunga_obligatory :
    cpd_dokunga.nasalisationObligatory = true := rfl

/-- The free cases: `JCompound.nasalisationObligatory` returns `false`
    — the compound is in the gradient/optional zone. -/
theorem dokuga_optional :
    cpd_dokuga.nasalisationObligatory = false := rfl

theorem haigan_optional : cpd_haigan.nasalisationObligatory = false := rfl
theorem noogeka_optional : cpd_noogeka.nasalisationObligatory = false := rfl

/-- The minimal pair (2a)/(2b) has identical surface forms but opposite
    obligatoriness — the paper's central piece of evidence that bound
    vs. free is the right dimension. -/
theorem minimal_pair_diverges :
    cpd_dokuga.nasalisationObligatory ≠ cpd_dokunga.nasalisationObligatory := by
  decide

/-- Two free-N2 compounds are *both* in the optional zone, regardless
    of their N2's frequency. The frequency story is *within* the
    optional zone, not at its boundary. -/
theorem free_zone_freq_independent :
    cpd_dokuga.nasalisationObligatory = cpd_haigan.nasalisationObligatory := rfl

-- ============================================================================
-- § 4: PU as `liftPairwise` — paradigm membership encodes anchoring
-- ============================================================================

/-- The PU paradigm of a compound: the candidate compound surface form
    plus the attested free N2, when N2 is free; just the compound,
    when N2 is bound. The free/bound split is encoded as **paradigm
    membership** (1 vs. 2 elements), not a separate predicate guard
    on the constraint — that is what makes the bound-case zero
    structural rather than stipulated.

    Built via `lcParadigm` from
    `Theories/Phonology/ParadigmUniformity/LexicalConservatism.lean`,
    making this file a downstream consumer of the LC anchored-paradigm
    primitive. The anchor-presence channel is exactly what
    @cite{steriade-2000} introduced, and BKK's bound/free split is the
    same architectural channel applied to a new domain. -/
def n2Paradigm (c : JCompound) : List String :=
  lcParadigm c.form (if c.n2.canStandAlone then some c.n2.form else none)

/-- Surface mismatch between two strings: 0 on the diagonal, 1
    off-diagonal. A whole-string identity check; **not** a velar-
    feature comparison. The architecturally faithful version would
    be a tier-restricted segment-by-segment comparison at the velar
    position routed through `Theories/Phonology/Featural/Geometry.lean`,
    but the qualitative architectural claims (sign of the channel,
    bound/free split) do not depend on the specific mismatch metric. -/
def stringMismatch (a b : String) : Nat := if a = b then 0 else 1

@[simp] theorem stringMismatch_self (a : String) : stringMismatch a a = 0 := by
  unfold stringMismatch; exact if_pos rfl

/-- The PU constraint **as a `NamedConstraint`** — derived from
    `mkLCFaith` from
    `Theories/Phonology/ParadigmUniformity/LexicalConservatism.lean`.
    The structural connection to @cite{steriade-2000} is by
    *construction*: BKK's PU pressure IS LC-FAITH on the
    `lcParadigm`-built paradigm. The architectural difference from
    @cite{mccarthy-2005} (OP) is that LC's paradigm is anchored on
    attestation; OP's is symmetric over all members. § 10 below makes
    that contrast explicit. -/
def puFaith : NamedConstraint (List String) :=
  mkLCFaith "PU-N2-FAITH" stringMismatch

/-- Number of PU-FAITH violations on a compound's paradigm. -/
def cpdPuViolations (c : JCompound) : Nat :=
  puFaith.eval (n2Paradigm c)

/-- **Bound case is structurally zero.** A bound N2 produces a singleton
    paradigm `[c.form]`; the only ordered pair is `(c.form, c.form)`
    whose mismatch is 0 by definition. The categorical nasalisation in
    bound compounds is the structural consequence of the PU channel
    contributing nothing. -/
theorem bound_cpdPuViolations_zero (c : JCompound)
    (hbound : c.n2.canStandAlone = false) :
    cpdPuViolations c = 0 := by
  have hpar : n2Paradigm c = lcParadigm c.form none := by
    unfold n2Paradigm; simp [hbound]
  show puFaith.eval (n2Paradigm c) = 0
  rw [hpar]
  exact lc_unanchored_zero "PU-N2-FAITH" stringMismatch stringMismatch_self c.form

/-- A free-N2 paradigm with distinct compound and N2 forms produces
    exactly two off-diagonal pairs, each contributing 1, for a total
    of 2 violations. The compound and N2 forms differ whenever N1 is
    non-empty — an empirically generic precondition. -/
theorem free_cpdPuViolations_eq_two (c : JCompound)
    (hfree : c.n2.canStandAlone = true)
    (hdiff : c.form ≠ c.n2.form) :
    cpdPuViolations c = 2 := by
  have hpar : n2Paradigm c = [c.form, c.n2.form] := by
    show lcParadigm c.form (if c.n2.canStandAlone then some c.n2.form else none) = _
    rw [if_pos hfree]; rfl
  show puFaith.eval (n2Paradigm c) = 2
  rw [hpar]
  show ((List.product [c.form, c.n2.form] [c.form, c.n2.form]).map
         (fun p => stringMismatch p.1 p.2)).sum = 2
  simp only [List.product, List.flatMap_cons, List.flatMap_nil, List.map_cons,
             List.map_nil, List.append_nil, List.cons_append, List.nil_append,
             stringMismatch, if_true, if_neg hdiff, if_neg hdiff.symm,
             List.sum_cons, List.sum_nil]
  rfl

/-- The bound /dokuŋa/ case has zero PU violations — concrete witness. -/
theorem dokunga_zero_puviolations : cpdPuViolations cpd_dokunga = 0 :=
  bound_cpdPuViolations_zero _ rfl

/-- The free /dokuga/ case has two PU violations — concrete witness. -/
theorem dokuga_two_puviolations : cpdPuViolations cpd_dokuga = 2 :=
  free_cpdPuViolations_eq_two _ rfl (by decide)

-- ============================================================================
-- § 5: Two opposite-sign frequency channels
-- ============================================================================

/-- The **N2-frequency-weighted PU pressure** on a compound: PU-FAITH
    violations multiplied by `scaledWeight` of the N2 token
    log-frequency. Higher N2 frequency → stronger weight → stronger
    preservation of [g] → less nasalisation. This is the
    *negative-on-nasalisation* channel (negative regression coefficient
    on N2 token frequency in @cite{breiss-katsuda-kawahara-2026}). -/
noncomputable def puPressure (slope : ℝ) (c : JCompound) : ℝ :=
  (cpdPuViolations c : ℝ) * scaledWeight (baseWeight := 0) (slope := slope) c.n2

/-- The **compound-frequency-weighted markedness pressure** *for*
    nasalisation: linear in compound log-frequency. Higher compound
    frequency → stronger drift away from constituent forms → more
    nasalisation. This is the *positive-on-nasalisation* channel
    (positive regression coefficient on compound token frequency in
    @cite{breiss-katsuda-kawahara-2026}).

    Modelled as a one-parameter linear function of the compound's own
    log-frequency, parallel to `Scaled.scaledWeight` but on the
    compound (not lexical-entry) channel. -/
noncomputable def cpdMarkednessPressure (slope : ℝ) (c : JCompound) : ℝ :=
  slope * (c.compoundLogFreq : ℝ)

/-- The predicted **nasalisation log-odds** of a compound: markedness
    pressure (positive sign on nasalisation) minus PU pressure
    (negative sign on nasalisation). The sign-inversion of the PU
    channel is *built into the difference* — increasing PU
    monotonically decreases the log-odds. -/
noncomputable def nasLogOdds (n2Slope cpdSlope : ℝ) (c : JCompound) : ℝ :=
  cpdMarkednessPressure cpdSlope c - puPressure n2Slope c

-- ============================================================================
-- § 6: Architectural theorems — the load-bearing predictions
-- ============================================================================

/-- **Sign-inversion lemma.** PU pressure enters `nasLogOdds` with a
    negative sign: holding compound markedness fixed, an increase in
    PU pressure strictly decreases the log-odds. This is the formal
    source of the *negative* regression coefficient on N2 token
    frequency reported in @cite{breiss-katsuda-kawahara-2026}. -/
theorem nasLogOdds_antitone_in_puPressure (n2Slope cpdSlope : ℝ)
    (c1 c2 : JCompound) (hcpd : c1.compoundLogFreq = c2.compoundLogFreq)
    (hpu : puPressure n2Slope c1 ≤ puPressure n2Slope c2) :
    nasLogOdds n2Slope cpdSlope c2 ≤ nasLogOdds n2Slope cpdSlope c1 := by
  unfold nasLogOdds cpdMarkednessPressure
  rw [show (c2.compoundLogFreq : ℝ) = (c1.compoundLogFreq : ℝ) by rw [hcpd]]
  linarith

/-- **N2-frequency channel monotonicity** (the *negative*-sign channel).
    For two free-N2 compounds with the same compound frequency and
    matched PU-violation counts, a higher N2 token log-frequency
    yields strictly *higher* PU pressure (when slope is positive). -/
theorem puPressure_monotone_in_n2_freq (slope : ℝ) (hSlope : 0 ≤ slope)
    (c1 c2 : JCompound) (hviol : cpdPuViolations c1 = cpdPuViolations c2)
    (hfreq : tokenLogFreq c1.n2 ≤ tokenLogFreq c2.n2) :
    puPressure slope c1 ≤ puPressure slope c2 := by
  unfold puPressure scaledWeight
  rw [hviol]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  linarith [mul_le_mul_of_nonneg_left hfreq hSlope]

/-- **Compound-frequency channel monotonicity** (the *positive*-sign
    channel). For two compounds with identical PU pressure but
    different compound log-frequencies, the higher-compound-frequency
    compound has strictly higher nasalisation log-odds (when slope is
    positive). -/
theorem nasLogOdds_monotone_in_cpd_freq (n2Slope cpdSlope : ℝ)
    (hSlope : 0 ≤ cpdSlope) (c1 c2 : JCompound)
    (hpu : puPressure n2Slope c1 = puPressure n2Slope c2)
    (hfreq : c1.compoundLogFreq ≤ c2.compoundLogFreq) :
    nasLogOdds n2Slope cpdSlope c1 ≤ nasLogOdds n2Slope cpdSlope c2 := by
  unfold nasLogOdds cpdMarkednessPressure
  rw [hpu]
  have h : cpdSlope * (c1.compoundLogFreq : ℝ) ≤ cpdSlope * (c2.compoundLogFreq : ℝ) :=
    mul_le_mul_of_nonneg_left (Rat.cast_le.mpr hfreq) hSlope
  linarith

/-- **Bound case: nasLogOdds collapses to pure markedness.** Because
    the PU channel is structurally zero on bound paradigms, the
    bound-case prediction depends only on the compound-frequency
    channel — i.e. the bound case has **one** frequency channel, not
    two. This is the architectural collapse the paper highlights. -/
theorem bound_nasLogOdds_eq_markedness (n2Slope cpdSlope : ℝ) (c : JCompound)
    (hbound : c.n2.canStandAlone = false) :
    nasLogOdds n2Slope cpdSlope c = cpdMarkednessPressure cpdSlope c := by
  unfold nasLogOdds puPressure
  rw [bound_cpdPuViolations_zero c hbound]
  ring

-- ============================================================================
-- § 7: Anti-UseListed discriminator (Experiment 2)
-- ============================================================================

/-- **Anti-UseListed discriminator.** Even on **novel** compounds (no
    listing entry), the N2-frequency gradient on PU pressure persists,
    because PU pressure depends on the N2's free-form attestation, not
    the compound's listing status. UseListed (@cite{zuraw-2000})
    predicts no frequency-dependent modulation on novel items;
    `puPressure` and hence `nasLogOdds` show one. This is the formal
    content of Experiment 2 of @cite{breiss-katsuda-kawahara-2026}.

    Concretely: two novel free-N2 compounds with the same compound
    log-frequency and matched PU-violation counts have *strictly*
    different `puPressure` values when their N2 token frequencies
    differ and the slope is strictly positive. -/
theorem novel_compounds_show_n2_gradient (slope : ℝ) (hSlope : 0 < slope)
    (c1 c2 : JCompound) (hviol : cpdPuViolations c1 = cpdPuViolations c2)
    (hviol_pos : 0 < cpdPuViolations c1)
    (hfreq : tokenLogFreq c1.n2 < tokenLogFreq c2.n2) :
    puPressure slope c1 < puPressure slope c2 := by
  unfold puPressure scaledWeight
  have hpos2 : (0 : ℝ) < (cpdPuViolations c2 : ℝ) := by
    rw [← hviol]; exact_mod_cast hviol_pos
  rw [hviol]
  apply mul_lt_mul_of_pos_left _ hpos2
  linarith [mul_lt_mul_of_pos_left hfreq hSlope]

-- ============================================================================
-- § 8: Wug paradigm cell — BKK as a `Paradigms/WugTest.lean` consumer
-- ============================================================================

/-! Experiment 2 of @cite{breiss-katsuda-kawahara-2026} is a wug-style
study: subjects rate nasalisation on **novel** compounds whose N2 has
real attestation as a free wordform. The N2-frequency gradient in
their results is the key evidence against UseListed
@cite{zuraw-2000}: a novel compound has no listing entry, so any
frequency-driven modulation must come from the *N2's* lexical
attestation, not the compound's.

This section wires BKK to the methodological contract in
`Paradigms/WugTest.lean` (anchored on @cite{berko-1958} and
@cite{albright-hayes-2003}). The cell type carries:

- a compound (the stimulus),
- a structural proof that N2 is **free** (so that the LC paradigm has
  the anchor and PU pressure is non-zero),
- a structural proof that compound and N2 forms differ (so that
  `cpdPuViolations = 2` is forced),
- the wug `Attestation` factor (attested vs. novel),
- and the N2 token log-frequency.

The first two fields make the cell type non-vacuous in a way that
discharges the `cpdPuViolations` precondition without per-cell
hypotheses. Concretely: for every `WugBKKCell`, we *prove* (not
assume) that PU violations equal 2. -/

structure WugBKKCell where
  compound : JCompound
  freeN2 : compound.n2.canStandAlone = true
  formDistinct : compound.form ≠ compound.n2.form
  attestation : Attestation
  n2LogFreq : ℝ

namespace WugBKKCell

/-- Every `WugBKKCell` has exactly two PU violations — a derived
    consequence of the structural fields, not a stipulation. This is
    the load-bearing fact that lets `wugBkkRate` exhibit a strict
    frequency gradient on novel cells without per-cell side
    conditions. -/
theorem cpdPuViolations_eq_two (c : WugBKKCell) :
    cpdPuViolations c.compound = 2 :=
  free_cpdPuViolations_eq_two c.compound c.freeN2 c.formDistinct

instance : HasAttestation WugBKKCell where
  factorOf c := c.attestation
  setFactor a c := { c with attestation := a }
  factorOf_setFactor := by intros; rfl
  setFactor_factorOf := by intros; rfl
  setFactor_setFactor := by intros; rfl

instance : HasFrequency WugBKKCell where
  factorOf c := c.n2LogFreq
  setFactor f c := { c with n2LogFreq := f }
  factorOf_setFactor := by intros; rfl
  setFactor_factorOf := by intros; rfl
  setFactor_setFactor := by intros; rfl

end WugBKKCell

-- ============================================================================
-- § 9: Wug-paradigm rate observable + anti-UseListed discriminator
-- ============================================================================

/-! `wugBkkRate` is BKK's per-cell numeric prediction expressed in the
shape `Paradigms/WugTest.lean` requires (`Rate Cell ℝ`). It exhibits
the N2-frequency gradient on novel cells, satisfying the WugTest
predicate `NovelShowsFreqGradient` — and hence (by
`novelGradient_inconsistent_with_invariance`) excluding the UseListed
prediction `NovelInvariantInFrequency`.

The sign of `wugBkkRate` is monotone increasing in N2 log-frequency
because it tracks the **PU pressure**, not the surface nasalisation
rate. PU pressure pushes toward [g] preservation; nasalisation rate
falls as PU pressure rises. The discriminator from `WugTest` only
cares about *non-flatness* of the rate function in the frequency
factor, so the sign is irrelevant to the structural exclusion of
UseListed. -/

/-- The wug-paradigm rate observable for BKK: PU pressure on the
    cell's compound, computed via `cpdPuViolations` (= 2 for every
    `WugBKKCell`) times the N2's frequency-scaled weight. -/
noncomputable def wugBkkRate (n2Slope : ℝ) (c : WugBKKCell) : ℝ :=
  (cpdPuViolations c.compound : ℝ) * (n2Slope * c.n2LogFreq)

/-- **BKK satisfies `NovelShowsFreqGradient`.** For any positive
    N2-frequency slope, `wugBkkRate` is strictly monotone in the
    frequency factor on novel cells. The proof uses
    `WugBKKCell.cpdPuViolations_eq_two` to discharge the violation
    count without per-cell hypotheses.

    This is the structural form of BKK Experiment 2's central
    finding: even on novel compounds, varying N2 token frequency
    produces a gradient in the predicted PU pressure. -/
theorem bkk_satisfies_NovelShowsFreqGradient (n2Slope : ℝ) (hSlope : 0 < n2Slope) :
    NovelShowsFreqGradient (wugBkkRate n2Slope) := by
  intro c f₁ f₂ hf
  unfold wugBkkRate
  -- The lens `setFactor` calls preserve the structural fields
  -- freeN2/formDistinct, so cpdPuViolations remains 2.
  have h1 : cpdPuViolations
      (HasFactor.setFactor f₁
        (HasFactor.setFactor Attestation.novel c)).compound = 2 :=
    WugBKKCell.cpdPuViolations_eq_two _
  have h2 : cpdPuViolations
      (HasFactor.setFactor f₂
        (HasFactor.setFactor Attestation.novel c)).compound = 2 :=
    WugBKKCell.cpdPuViolations_eq_two _
  rw [h1, h2]
  -- Both lens-applied cells have the freshly-set frequency.
  show ((2 : ℕ) : ℝ) * (n2Slope * f₁) < ((2 : ℕ) : ℝ) * (n2Slope * f₂)
  have h2pos : (0 : ℝ) < ((2 : ℕ) : ℝ) := by norm_num
  exact mul_lt_mul_of_pos_left
    (mul_lt_mul_of_pos_left hf hSlope) h2pos

/-- A concrete non-vacuous `WugBKKCell` witness: /haigan/ "lung
    cancer" used as a wug stimulus. The structural fields are
    discharged by `rfl` / `decide`. Required for the discriminator
    corollary below — `novelGradient_inconsistent_with_invariance`
    needs distinct frequencies, which it gets from `0 < 1`. -/
def cell_haigan : WugBKKCell where
  compound := cpd_haigan
  freeN2 := rfl
  formDistinct := by decide
  attestation := .novel
  n2LogFreq := 0

/-- **Anti-UseListed discriminator (final form).** Wired through
    `Paradigms/WugTest.lean`'s structural impossibility theorem: BKK's
    `wugBkkRate` cannot satisfy `NovelInvariantInFrequency` (the
    UseListed prediction). Any account on which novel forms have flat
    PU pressure across N2 frequencies is ruled out by Experiment 2.

    This is `novel_compounds_show_n2_gradient` re-expressed at the
    paradigm-contract level: instead of a per-pair `puPressure`
    inequality, we get a structural impossibility on the rate
    function itself. -/
theorem bkk_excludes_useListed (n2Slope : ℝ) (hSlope : 0 < n2Slope) :
    ¬ NovelInvariantInFrequency (wugBkkRate n2Slope) := by
  intro h_inv
  exact novelGradient_inconsistent_with_invariance
    (wugBkkRate n2Slope)
    (bkk_satisfies_NovelShowsFreqGradient n2Slope hSlope)
    h_inv cell_haigan 0 1 (by norm_num)

-- ============================================================================
-- § 10: Engagement with Optimal Paradigms — McCarthy 2005
-- ============================================================================

/-! BKK's docstring cites OP (@cite{mccarthy-2005}) as a sister PU
theory; the architectural choice is LC over OP because LC's anchor
primitive structurally encodes the bound/free split.

**Caveat on the analog.** @cite{mccarthy-2005}'s OP, narrowly
construed, ranges over the inflected wordforms of a single lexeme —
not over a compound and its N2 constituent. Applying OP to N1+N2
compound paradigms is an *extended application* not licensed by the
2005 paper itself. The point of this section is precisely that
extending OP straightforwardly to the compound case loses the
bound/free distinction: a compound and its (free or bound) N2 are not
in an OP-style inflectional relationship, so the architectural handle
LC supplies via attestation-anchored paradigm membership has no
natural OP counterpart. This is part of why BKK choose LC rather than
OP for the compound domain.

The OP-on-compounds straw-figure formalised below predicts
**identical** PU violations on bound and free compounds with distinct
N2 surface forms — losing BKK's categorical bound-case nasalisation as
a structural prediction. To recover the empirical pattern, an
extended-OP account would need an auxiliary stipulation (a separate
constraint, a stratum, or a guard predicate). LC gets it from
paradigm membership alone. -/

/-- The OP paradigm of a compound: symmetric over all members, no
    distinguished anchor. Because OP does not condition on
    attestation, both bound and free N2 contribute to the paradigm. -/
def n2OpParadigm (c : JCompound) : List String :=
  [c.form, c.n2.form]

/-- The OP-flavoured PU constraint, built from the same `liftPairwise`
    combinator. Differs from `puFaith` only in the *paradigm
    construction* (cf. `lcParadigm` vs. unconditional pair). -/
def opPuFaith : NamedConstraint (List String) :=
  liftPairwise "OP-PU-FAITH" .faithfulness stringMismatch

/-- OP-flavoured violation count on a compound. -/
def cpdOpPuViolations (c : JCompound) : Nat :=
  opPuFaith.eval (n2OpParadigm c)

/-- **OP gives identical violation counts on bound and free
    compounds.** Whenever `c.form ≠ c.n2.form`, the OP paradigm
    `[c.form, c.n2.form]` has two off-diagonal pairs each contributing
    1, regardless of N2 attestation. This is the structural
    consequence of OP's anchor-blindness. -/
theorem op_paradigm_uniform_in_bound_free (c : JCompound)
    (hdiff : c.form ≠ c.n2.form) :
    cpdOpPuViolations c = 2 := by
  show opPuFaith.eval (n2OpParadigm c) = 2
  show ((List.product [c.form, c.n2.form] [c.form, c.n2.form]).map
         (fun p => stringMismatch p.1 p.2)).sum = 2
  simp only [List.product, List.flatMap_cons, List.flatMap_nil, List.map_cons,
             List.map_nil, List.append_nil, List.cons_append, List.nil_append,
             stringMismatch, if_true, if_neg hdiff, if_neg hdiff.symm,
             List.sum_cons, List.sum_nil]
  rfl

/-- **Extended-OP and LC structurally disagree on bound compounds.**
    For any bound-N2 compound with distinct compound and N2 forms, the
    OP-on-compounds analog predicts 2 violations while LC predicts 0.
    This is the formal incompatibility motivating BKK's choice of LC
    over an OP-style account in the compound domain — *structural*, not
    parameter-dependent. The empirical categorical bound-case
    nasalisation supports LC.

    NB: see the §10 caveat. McCarthy's OP, narrowly construed, is over
    inflectional paradigms of one lexeme; the disagreement here is
    with an *extended-OP* that applies the symmetric-paradigm
    architecture to N1+N2 compounds, which BKK take to be the natural
    OP-style competitor in this domain. -/
theorem op_lc_disagree_on_bound (c : JCompound)
    (hbound : c.n2.canStandAlone = false)
    (hdiff : c.form ≠ c.n2.form) :
    cpdOpPuViolations c ≠ cpdPuViolations c := by
  rw [op_paradigm_uniform_in_bound_free c hdiff,
      bound_cpdPuViolations_zero c hbound]
  decide

/-- Concrete witness: /dokuŋa/ "poison fang" instantiates the
    OP/LC disagreement. OP says 2 violations; LC says 0. -/
theorem dokunga_op_vs_lc :
    cpdOpPuViolations cpd_dokunga ≠ cpdPuViolations cpd_dokunga :=
  op_lc_disagree_on_bound cpd_dokunga rfl (by decide)

end Phenomena.Phonology.Studies.BreissKatsudaKawahara2026
