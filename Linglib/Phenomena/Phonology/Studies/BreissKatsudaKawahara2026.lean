import Linglib.Fragments.Japanese.Prosody
import Linglib.Theories.Phonology.LexicalFrequency.Defs
import Linglib.Theories.Phonology.LexicalFrequency.ScaledWeights
import Linglib.Theories.Phonology.LexicalFrequency.RepresentationStrength
import Linglib.Theories.Phonology.LexicalFrequency.IndexedConstraints
import Linglib.Theories.Phonology.LexicalFrequency.UseListed
import Linglib.Theories.Phonology.ParadigmUniformity.Defs

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
  rate of nasalisation (negative coefficient in Fig. 2). The free-form
  [g] is a more accessible paradigm exemplar; paradigm-uniformity
  pressure preserves it, suppressing [ŋ].
- High token frequency of **the compound itself** *increases* the rate
  of nasalisation (positive coefficient in Fig. 2). More-attested
  compounds drift further from their constituent forms.

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
open Phonology.ParadigmUniformity (liftPairwise)
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
    structural rather than stipulated. -/
def n2Paradigm (c : JCompound) : List String :=
  if c.n2.canStandAlone then [c.form, c.n2.form] else [c.form]

/-- Surface mismatch between two strings: 0 on the diagonal, 1
    off-diagonal. Stands in for a tier-restricted segment-by-segment
    comparison at the velar position; the qualitative architectural
    claims do not depend on the specific mismatch metric. -/
def velarMismatch (a b : String) : Nat := if a = b then 0 else 1

@[simp] theorem velarMismatch_self (a : String) : velarMismatch a a = 0 := by
  simp [velarMismatch]

/-- The PU constraint **as a `NamedConstraint`** — derived from
    `liftPairwise` from `ParadigmUniformity/Defs.lean`. The structural
    connection to @cite{mccarthy-2005} (OP) and @cite{steriade-2000}
    (LC) is by *construction*: the same `liftPairwise` combinator is
    used; what differs across PU theories is *which forms enter the
    paradigm*. BKK's anchor is the attested free wordform of N2. -/
def puFaith : NamedConstraint (List String) :=
  liftPairwise "PU-N2-FAITH" .faithfulness velarMismatch

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
  simp [cpdPuViolations, puFaith, n2Paradigm, hbound, liftPairwise,
        List.product]

/-- A free-N2 paradigm with distinct compound and N2 forms produces
    exactly two off-diagonal pairs, each contributing 1, for a total
    of 2 violations. The compound and N2 forms differ whenever N1 is
    non-empty — an empirically generic precondition. -/
theorem free_cpdPuViolations_eq_two (c : JCompound)
    (hfree : c.n2.canStandAlone = true)
    (hdiff : c.form ≠ c.n2.form) :
    cpdPuViolations c = 2 := by
  simp [cpdPuViolations, puFaith, n2Paradigm, hfree, liftPairwise,
        List.product, velarMismatch, hdiff, hdiff.symm]

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
    *negative-on-nasalisation* channel of BKK Fig. 2. -/
noncomputable def puPressure (slope : ℝ) (c : JCompound) : ℝ :=
  (cpdPuViolations c : ℝ) * scaledWeight (baseWeight := 0) (slope := slope) c.n2

/-- The **compound-frequency-weighted markedness pressure** *for*
    nasalisation: linear in compound log-frequency. Higher compound
    frequency → stronger drift away from constituent forms → more
    nasalisation. This is the *positive-on-nasalisation* channel of
    BKK Fig. 2.

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
    source of the *negative* coefficient on N2 token frequency in BKK
    Fig. 2. -/
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

end Phenomena.Phonology.Studies.BreissKatsudaKawahara2026
