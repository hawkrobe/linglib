import Linglib.Core.ChannelCapacity

/-!
# Zaslavsky, Kemp, Tishby & Regier (2019)
@cite{zaslavsky-etal-2019}

Color Naming Reflects Both Perceptual Structure and Communicative Need.
Topics in Cognitive Science 11(1), 207–219.

## Core Contributions

@cite{zaslavsky-etal-2019} adjudicate between two explanations of
cross-linguistic color naming patterns: perceptual structure (the geometry
of CIELAB space) and communicative need (how often colors must be
communicated). Their key finding is that *both* matter.

1. **Perceptual structure partly explains the warm–cool asymmetry.**
   K-means clustering on CIELAB coordinates produces artificial naming
   systems that already show lower expected surprisal S(c) for warm
   colors — without any communicative pressure.

2. **Communicative need contributes beyond perceptual structure.**
   The salience-weighted prior (from natural image statistics) exhibits
   a linear −log p(c) vs S(c) relationship predicted by the CAP theorem,
   while the perceptually-derived KM-CAP prior does not.

3. **The CAP theorem links need and precision.**
   At a capacity-achieving prior, −log p(c) = S(c) + log Z. This
   information-theoretic identity is the paper's central theoretical
   contribution, formalized in `Core.ChannelCapacity.cap_linear`.

## Integration

- Theory layer: `Core.ChannelCapacity` (NamingChannel, CAP, cap_linear)
- The RSA connection: a NamingChannel is an RSA literal speaker S₀,
  and the posterior is the literal listener L₀.
-/

set_option autoImplicit false

namespace Phenomena.LexicalTypology.Studies.ZaslavskyEtAl2019

open Core.ChannelCapacity

-- ============================================================================
-- §1. The WCS Color Domain
-- ============================================================================

/-- The 80 WCS color chips analyzed by @cite{zaslavsky-etal-2019}.
    These are the standard Munsell chips from the World Color Survey,
    excluding achromatic chips. Each chip has coordinates in CIELAB
    perceptual color space. -/
abbrev WCSChip := Fin 80

/-- Temperature classification: warm vs cool.
    The warm–cool asymmetry in communicative precision is the paper's
    central empirical finding. Warm colors (reds, yellows) have
    lower S(c) than cool colors (blues, greens) across languages. -/
inductive Temperature where
  | warm   -- reds, yellows
  | cool   -- blues, greens
  deriving DecidableEq, Repr

-- ============================================================================
-- §2. Communicative Precision and the Warm–Cool Asymmetry
-- ============================================================================

/-- The paper's main empirical finding: across languages,
    warm colors have lower expected surprisal (= higher communicative
    precision) than cool colors, regardless of prior choice.

    We state this as a property of a naming channel and temperature
    classification rather than as a concrete computation (which would
    require the full WCS dataset). -/
def WarmCoolAsymmetry {W : Type} [Fintype W] (nc : NamingChannel WCSChip W) (prior : WCSChip → ℝ)
    (temp : WCSChip → Temperature) : Prop :=
  let warmChips := Finset.univ.filter (λ c => temp c == .warm)
  let coolChips := Finset.univ.filter (λ c => temp c == .cool)
  (∑ c ∈ warmChips, commPrecision nc prior c) / warmChips.card <
  (∑ c ∈ coolChips, commPrecision nc prior c) / coolChips.card

-- ============================================================================
-- §3. Perceptual Structure (CIELAB)
-- ============================================================================

/-- CIELAB coordinates for a WCS chip. L* = lightness, a* = red-green,
    b* = yellow-blue. Euclidean distance in CIELAB approximates
    perceptual dissimilarity.

    The irregular distribution of the 80 WCS chips in CIELAB reveals
    perceptual asymmetries between warm and cool colors that partly
    explain the communicative precision asymmetry. -/
structure CIELABCoord where
  L : Float   -- lightness (0 = black, 100 = white)
  a : Float   -- red-green axis (+ = red, − = green)
  b : Float   -- yellow-blue axis (+ = yellow, − = blue)
  deriving Repr

/-- Perceptual distance between two colors in CIELAB (Euclidean). -/
def cielabDist (p q : CIELABCoord) : Float :=
  ((p.L - q.L)^2 + (p.a - q.a)^2 + (p.b - q.b)^2).sqrt

/-- A perceptually-derived naming system: k-means clustering on CIELAB
    assigns each chip to the nearest centroid, creating a hard partition.
    The paper shows these systems *also* exhibit warm–cool asymmetry in
    S(c), demonstrating that perceptual structure alone partially accounts
    for the effect. -/
structure KMeansSystem where
  /-- Number of clusters (= number of color terms in the language). -/
  k : Nat
  /-- Cluster assignment for each chip. -/
  assignment : WCSChip → Fin k

/-- Convert a hard k-means partition to a NamingChannel.
    A hard partition assigns p(w|c) = 1 if w = assignment(c), else 0.
    This is a deterministic channel (zero conditional entropy). -/
noncomputable def KMeansSystem.toChannel (km : KMeansSystem) :
    NamingChannel WCSChip (Fin km.k) where
  encode c w := if km.assignment c = w then 1 else 0
  encode_nonneg _ _ := by split <;> norm_num
  encode_sum_one c := by simp [Finset.mem_univ]

-- ============================================================================
-- §4. Averaging CAPs across Languages
-- ============================================================================

/-! The paper infers a universal need distribution by averaging per-language
capacity-achieving priors (eq. 7): p̄(c) = 1/L Σ_l p_l(c), where each
p_l is the CAP for language l's naming system p_l(w|c), found via
Blahut-Arimoto.

Crucially, averaging CAPs does NOT in general preserve the CAP condition
(footnote 4 of @cite{zaslavsky-etal-2019}): each p_l satisfies IsCAP for
its own channel, but the averaged p̄ need not be a CAP for any single
channel. The paper's key empirical finding is a *dissociation*:

- **WCS-CAP** (averaged from actual WCS+ languages): empirically
  approximates a CAP — −log p̄(c) vs S̄(c) is approximately linear.
- **KM-CAP** (averaged from k-means systems): does NOT approximate
  a CAP (r = 0.32) — suggesting real naming systems encode communicative
  structure beyond perceptual clustering.
- **Salience-weighted prior** (from natural image statistics,
  @cite{gibson-etal-2017}): exhibits both the linear CAP relation AND the
  warm–cool asymmetry — evidence for communicative need beyond perceptual
  structure. -/

/-- Average a collection of per-language priors to obtain a universal
    need distribution (eq. 7 of @cite{zaslavsky-etal-2019}). -/
noncomputable def averageCAP {L : Nat}
    (priors : Fin L → (WCSChip → ℝ)) : WCSChip → ℝ :=
  fun c => (∑ l : Fin L, priors l c) / L

-- ============================================================================
-- §5. CAP Predictions
-- ============================================================================

/-- Any TRUE capacity-achieving prior exhibits the linear relation
    −log p(c) = S(c) + log Z (eq. 6 of @cite{zaslavsky-etal-2019}).

    This applies to each per-language CAP p_l found via Blahut-Arimoto.
    However, the paper tests *averaged* priors (see `averageCAP`), not
    individual ones. The empirical finding that WCS-CAP approximately
    satisfies this relation despite averaging is evidence that the CAP
    condition is robust across languages. KM-CAP's failure to satisfy
    it (r = 0.32) shows that perceptual structure alone does not yield
    the same robustness. -/
theorem cap_implies_linearity {W : Type} [Fintype W]
    (nc : NamingChannel WCSChip W) (prior : WCSChip → ℝ)
    (hCAP : IsCAP nc prior) {c : WCSChip} (hc : prior c > 0) :
    ∃ Z > 0, -Real.log (prior c) = commPrecision nc prior c + Real.log Z :=
  cap_linear' nc prior hCAP hc

-- ============================================================================
-- §6. The RSA Connection
-- ============================================================================

/-! A naming channel p(w|c) is exactly an RSA literal speaker S₀ evaluated
at each world c. The posterior p(c|w) is the RSA literal listener L₀.
Channel capacity `channelCapacity nc` = max_{p(c)} I(W;C) is the maximum
informativity achievable under any world prior.

The paper shows that natural color naming systems operate near capacity:
the salience-weighted prior exhibits the linear CAP relation with high
correlation. This means color naming systems are approximately
information-theoretically optimal — a prediction that RSA makes for
any rational communication system.

The key difference from standard RSA: this paper analyzes the *prior*
p(c), not the speaker/listener strategies. RSA typically takes the prior
as given and derives speaker/listener behavior. The CAP framework goes
one level up: it asks what prior would make the entire system optimally
informative, and shows that natural priors approximate this optimum.

This "prior optimization" perspective connects to @cite{zaslavsky-hu-levy-2020}'s
rate-distortion view of RSA, where the rationality parameter α trades off
compression rate against distortion. -/

end Phenomena.LexicalTypology.Studies.ZaslavskyEtAl2019
