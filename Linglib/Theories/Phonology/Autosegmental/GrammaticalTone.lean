import Linglib.Theories.Phonology.Autosegmental.RegisterTier

/-!
# Grammatical Tone
@cite{rolle-2018} @cite{hyman-etal-2021}

Grammatical tone (GT) is a tonological operation "restricted to a specific
morpheme or construction... and not attributable to the general tonal
phonology" (@cite{lionnet-etal-2022}:386). More precisely, GT is a
tonological operation which is not general across the phonological grammar,
and is restricted to the context of a specific morpheme or construction, or
a natural class of morphemes or constructions (@cite{rolle-2018} Def 5).

## GT components (@cite{rolle-2018} §2.1.4, Defs 10–15)

@cite{rolle-2018} proposes a formal framework with five components for
cross-linguistic classification:

1. **Grammatical tune** (Def 10): the unique tone sequence (or set of
   tone sequences) which covaries with the GT construction
2. **Trigger** (Def 13): the morpheme or construction licensing the
   tonological operation
3. **Target** (Def 14): the morpheme(s) undergoing the tonal operation
4. **Host** (Def 12): the morpheme(s) on which the tune is phonetically
   realized
5. **Valuation window** (Def 15): the portion of the target-host
   evaluated for whether TBUs are valued or unvalued

The **sponsor** (Def 11) is the morpheme (or natural class of morphemes)
which covaries with the grammatical tune. In most cases, the trigger is
coextensive with the sponsor and the target with the host.

## GT dominance effects (@cite{rolle-2018} Ch 3, §3.1)

Interactions between the trigger-sponsor and the target-host based on
their morphosyntactic identity and tonal value are **GT dominance effects**
(à la @cite{kiparsky-halle-1977}, @cite{kiparsky-1982},
@cite{inkelas-1998}). These split into:

- **Dominant GT**: the trigger imposes its pattern regardless of the
  target's tonal content
  - *Replacive-dominant* (Def 1): underlying tone of target-host is
    replaced by the grammatical tune
  - *Subtractive-dominant* (Def 2): underlying tone of target-host is
    deleted WITHOUT revaluation by a grammatical tune
- **Non-dominant GT**: the trigger's effect depends on whether the target
  is tonally valued
  - *Recessive* (Def 3): the grammatical tune applies only when the
    target-host is unvalued within its valuation window
  - *Neutral* (Def 4): the trigger concatenates with the target-host
    without automatic replacement, deletion, or non-application

@cite{hyman-etal-2021} distinguish two broad categories of GT:
- **Word-level**: tone is the sole exponent of inflectional or derivational
  morphology (e.g., Kalabari imperative: H-L melody)
- **Phrase-level**: a phrasal construction triggers tonal modification of
  its complement (e.g., Kalabari associative: L-H melody on nouns)

This module provides the core types and operations. Language-specific
instantiations live in `Fragments/`; empirical applications in `Phenomena/`.
-/

namespace Theories.Phonology.Autosegmental.GrammaticalTone

open Theories.Phonology.Autosegmental.RegisterTier (ToneFeature)

-- ============================================================================
-- § 1: Tone-Bearing Units
-- ============================================================================

/-- A tone-bearing unit carrying a tonal specification. Parameterized over
    the segmental content type `S` (syllables, moras, etc.). -/
structure TBU (S : Type) where
  seg  : S
  tone : ToneFeature
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Tonal Values (@cite{rolle-2018} §2.1.1, Table 1)
-- ============================================================================

/-- Whether a TBU is tonally **valued** (has a linked toneme T) or
    **unvalued** (a 'free TBU' — @cite{clements-goldsmith-1984}).

    The distinction between valued and unvalued targets is critical for
    defining GT dominance effects: dominant triggers impose their pattern
    regardless of tonal value, while recessive triggers only apply to
    unvalued targets (@cite{rolle-2018} §3.1, Table 2). -/
inductive TonalValue where
  | valued    -- TBU τ is linked to a toneme T
  | unvalued  -- TBU τ has no linked toneme (free TBU)
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 3: Tonological Operations (@cite{rolle-2018} §2.1.3, Table 3)
-- ============================================================================

/-- The inventory of grammatically-conditioned tonological operations
    (@cite{rolle-2018} Table 3). Each variant represents a distinct type
    of input→output tonal mapping that can be triggered by a specific
    morpheme or construction. -/
inductive GTOperation where
  /-- Floating tone docks to an unvalued TBU without replacing any
      existing tone. -/
  | floatingToneDocking
  /-- Toneme of the target is deleted, leaving the TBU unvalued. -/
  | deletion
  /-- Underlying tone of the target is replaced by a new tone
      (the grammatical tune). -/
  | replacement
  /-- Tone shifts from one TBU to an adjacent one (e.g., rightward
      shift in Jita — @cite{downing-2014}). -/
  | shifting
  /-- Target tone changes to avoid identity with an adjacent tone
      (e.g., L→H next to L). -/
  | dissimilation
  /-- Target acquires the opposite value of an adjacent tone
      (e.g., L→H regardless of distance). -/
  | polarization
  /-- A contour tone on the target loses one component (e.g., HL→H). -/
  | absorption
  /-- Target assimilates to the pitch level of an adjacent tone on the
      same tier (horizontal spreading — @cite{hyman-2007}). -/
  | horizontalAssimilation
  /-- Target shifts to a nearby pitch level (e.g., L→M next to H). -/
  | verticalAssimilation
  /-- A tone spreads from the sponsor to one or more TBUs of the
      target (e.g., H spreading in Bantu). -/
  | toneSpreading
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 4: GT Dominance Effects (@cite{rolle-2018} Ch 3, Defs 1–4)
-- ============================================================================

/-- The four-way typology of GT dominance effects, based on the
    interaction between trigger-sponsor and target-host tonal values
    (@cite{rolle-2018} §3.1, Table 2).

    Dominance is a **lexical idiosyncrasy** of the trigger: it cannot
    be predicted from segmental or prosodic properties, the markedness
    of the grammatical tune, or the morphosyntactic position of the
    trigger relative to the target (@cite{inkelas-1998}:128). -/
inductive GTDominance where
  /-- **Replacive-dominant**: automatic replacement of the underlying
      tone within the valuation window of the target-host, revalued
      with the grammatical tune (whether via floating tone, spreading
      from the sponsor, etc.).

      Neutralizes the distinction between valued and unvalued targets:
      both receive the same output tone pattern. This neutralization
      is "intentional" in the sense of @cite{hyman-2018a}.

      Examples: Hausa plural -óoCíí (@cite{inkelas-1998}),
      Kalabari demonstrative /mí/ (@cite{harry-hyman-2014}),
      Mwaghavul verbalisers (@cite{akinbo-fwangwar-2026}). -/
  | replaciveDominant
  /-- **Subtractive-dominant**: automatic deletion of the underlying
      tone within the valuation window, WITHOUT revaluation by a
      grammatical tune. The surface form receives a default pattern
      at a later stage.

      Examples: Japanese -teki (@cite{kawahara-2015}),
      Baka 3sg/1pl/3pl inflection (@cite{waag-phodunze-2013}). -/
  | subtractiveDominant
  /-- **Recessive-non-dominant**: the grammatical tune applies only
      when the target-host is unvalued within its valuation window.
      If the target is valued, the tune does not dock.

      Found primarily in privative-culminative systems where the
      tonal contrast is presence vs. absence (e.g., /H/ vs. Ø).

      Examples: Japanese -si 'Mr.' (@cite{kawahara-2015}),
      Giphende floating tones (@cite{hyman-2017}). -/
  | recessive
  /-- **Neutral-non-dominant**: the trigger-sponsor concatenates
      with the target-host without automatic replacement, deletion,
      or non-application of the grammatical tune. The output is
      determined by the general phonological grammar (e.g., OCP
      resolution, markedness constraints).

      Most cases of "floating tones" in the literature are neutral.

      Examples: Hausa referential -ⁿn (@cite{newman-1986}),
      Igbo associative construction (@cite{hyman-schuh-1974}). -/
  | neutral
  deriving DecidableEq, BEq, Repr

/-- Dominant GT neutralizes the lexical tonal contrast of the target:
    whether the target is valued or unvalued, the output is the same.
    This property is what @cite{rolle-2018} calls **dominance as
    transparadigmatic uniformity**. -/
def GTDominance.isDominant : GTDominance → Bool
  | .replaciveDominant   => true
  | .subtractiveDominant => true
  | .recessive           => false
  | .neutral             => false

/-- Non-dominant GT preserves the lexical tonal contrast: the output
    differs depending on whether the target is valued or unvalued. -/
def GTDominance.isNonDominant (d : GTDominance) : Bool := !d.isDominant

-- ============================================================================
-- § 5: GT Level (@cite{hyman-etal-2021})
-- ============================================================================

/-- The morphosyntactic level at which the GT construction operates.
    @cite{hyman-etal-2021} distinguish word-level from phrase-level GT. -/
inductive GTLevel where
  /-- Tone is the sole exponent of word-level (inflectional or
      derivational) morphology. -/
  | word
  /-- A phrasal construction triggers tonal modification of its
      complement. -/
  | phrase
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 6: Exponence Types (@cite{rolle-2018} §2.2.1, Defs 16–18)
-- ============================================================================

/-- How the GT construction relates to segmental exponence of
    grammatical meaning (@cite{rolle-2018} Defs 16–18). -/
inductive ExponenceType where
  /-- **Independent prosodic exponence** (Def 16): the grammatical
      category is exponed only by prosodic units of contrast (tonemes,
      accent, etc.) with no segmental material. Also called 'tonal
      morpheme', 'tonal affix', 'tonal overlay', etc. -/
  | independent
  /-- **Auxiliary prosodic exponence** (Def 17): the grammatical
      category is exponed by segmental units AND co-occurring prosodic
      units separately. -/
  | auxiliary
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 7: Valuation Window and Grammatical Tone Specification
-- ============================================================================

/-- A tonal melody: a sequence of tones to be associated with TBUs. -/
abbrev TonalMelody := List ToneFeature

/-- Valuation window: the portion of the host that the grammatical tune
    targets. Determines which TBUs are overwritten.

    @cite{rolle-2018} (Def 15): the portion of the target-host which
    is evaluated with respect to whether its TBUs are valued or unvalued;
    this can be coextensive with the target-host, or strictly a local
    subconstituent. -/
inductive ValuationWindow where
  /-- The entire host (every TBU). Coextensive valuation window. -/
  | whole
  /-- All nonfinal TBUs get one tone, the final TBU gets another.
      Used for melodies like M-H where the last TBU is special. -/
  | nonfinalFinal
  /-- A local subconstituent of the host (e.g., only the final mora,
      only the TBU adjacent to the trigger). Used in
      subtractive-dominant GT with local scope, e.g., Japanese
      genitive -no (@cite{kawahara-2015}). -/
  | local
  deriving DecidableEq, BEq, Repr

/-- A grammatical tone specification following @cite{rolle-2018}.

    Captures the tonal exponent of a morpheme or construction:
    what tonal melody it imposes, and on which portion of the host. -/
structure Spec where
  /-- Label for the morpheme (e.g., "VBZ-M", "VBZ-MH") -/
  name : String
  /-- The tonal melody imposed. For `whole`, the single tone spreads
      to all TBUs. For `nonfinalFinal`, the first tone targets nonfinal
      TBUs and the second targets the final TBU. -/
  melody : TonalMelody
  /-- Which portion of the host is targeted. -/
  window : ValuationWindow
  deriving Repr

/-- Full GT specification extending `Spec` with the dominance type,
    morphosyntactic level, and exponence type from @cite{rolle-2018}'s
    typological framework. This bundles all five GT components plus the
    typological classification into a single record. -/
structure GTSpec extends Spec where
  /-- The dominance type of this GT trigger. -/
  dominance : GTDominance
  /-- Word-level or phrase-level GT (@cite{hyman-etal-2021}). -/
  level : GTLevel
  /-- Whether the tonal exponent is the sole exponent (independent)
      or co-occurs with segmental material (auxiliary). -/
  exponence : ExponenceType
  deriving Repr

-- ============================================================================
-- § 8: Tonal Overwrite (Replacive-Dominant GT)
-- ============================================================================

/-- Apply a grammatical tone to a host word, overwriting lexical tones
    in the valuation window. This implements **replacive-dominant GT**
    (@cite{rolle-2018} Def 1): the underlying tones of the target-host
    are automatically replaced by the grammatical tune.

    - `whole` + `[t]`: every TBU gets tone `t`
    - `nonfinalFinal` + `[t₁, t₂]`: nonfinal TBUs get `t₁`, final gets `t₂`

    Returns the input unchanged if the melody is empty or the window
    is `local` (local valuation requires language-specific logic). -/
def tonalOverwrite {S : Type} [DecidableEq S] [BEq S] [Repr S]
    (host : List (TBU S)) (spec : Spec) : List (TBU S) :=
  match spec.window, spec.melody with
  | .whole, [t] =>
    host.map (λ tbu => { tbu with tone := t })
  | .nonfinalFinal, [tNonfin, tFin] =>
    match host.reverse with
    | [] => []
    | last :: init =>
      (init.reverse.map (λ tbu => { tbu with tone := tNonfin }))
        ++ [{ last with tone := tFin }]
  | _, _ => host  -- no change if melody doesn't match window pattern

-- ============================================================================
-- § 9: Dominant GT Asymmetry (@cite{rolle-2018} §1.5.1, §3.3.1)
-- ============================================================================

/-- The **dominant GT asymmetry**: within a multi-morphemic constituent,
    dominant GT triggers are always **dependents** (affixes, modifiers,
    clitics), and the target is always the **lexical head** (root, stem,
    noun). Lexical heads do not impose dominant GT on their dependents.

    @cite{rolle-2018} derives this from the CoP-scope hierarchy (§6):
    VIs within specifiers scope over heads, and VIs within heads scope
    over complements. Since dependents are structurally outer relative
    to the head, the outer dominance principle (Def 5) guarantees that
    dominant triggers are always dependents.

    We encode this as a predicate over GT specifications: if the
    trigger is dominant, then by the asymmetry, the trigger must be
    a dependent morpheme. Outward dominance — a lexical head imposing
    dominant GT on its dependents — would falsify the theory. -/
structure DominantGTAsymmetry where
  /-- The trigger morpheme's structural role. -/
  triggerIsDependent : Bool
  /-- The target morpheme's structural role. -/
  targetIsHead : Bool

/-- The dominant GT asymmetry holds when all dominant triggers are
    dependents and all dominant targets are heads. -/
def DominantGTAsymmetry.holds (a : DominantGTAsymmetry) : Bool :=
  a.triggerIsDependent && a.targetIsHead

-- ============================================================================
-- § 10: GT Indomitability (@cite{rolle-2018} §3.3.2, Def 6)
-- ============================================================================

/-- Types of GT indomitability: exceptional targets that fail to undergo
    a tonological operation despite being within the scope of the trigger
    (@cite{rolle-2018} §3.3.2). -/
inductive IndomitabilityType where
  /-- **Morphemic**: specific morphemes or morpheme classes resist
      the GT operation (e.g., Jita -lí NEG.DIST.FUT —
      @cite{downing-2014}). -/
  | morphemic
  /-- **Morphosyntactic**: certain syntactic constituents are
      transparent or opaque to the GT operation (e.g., Tommo So
      alienable possessors — @cite{mcpherson-heath-2016}). -/
  | morphosyntactic
  /-- **Tonological**: targets with specific input tone melodies
      resist (e.g., Nzadi /LH/ targets — @cite{crane-etal-2011}). -/
  | tonological
  /-- **Phonological**: targets with specific phonological properties
      resist (e.g., monomoraic targets with Japanese -no genitive —
      @cite{kawahara-2015}). -/
  | phonological
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 11: Repairs in GT Application (@cite{rolle-2018} §3.3.3)
-- ============================================================================

/-- Repair strategies when a grammatical tune cannot dock to its
    intended target (@cite{rolle-2018} §3.3.3). -/
inductive GTRepair where
  /-- The grammatical tune is deleted (the most common repair). -/
  | tuneDeactivation
  /-- The tune docks to the trigger-sponsor itself. -/
  | selfDocking
  /-- The tune docks to a non-local host, skipping the intended
      target. -/
  | nonLocalDocking
  /-- The underlying tone of the target is undocked from TBUs within
      the valuation window (but not deleted), and may redock outside
      the window or remain floating. -/
  | tonalDefenestration
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 12: Verification
-- ============================================================================

/-- Whole-word overwrite with a single tone produces uniform output. -/
theorem tonalOverwrite_whole_uniform {S : Type} [DecidableEq S] [BEq S] [Repr S]
    (host : List (TBU S)) (t : ToneFeature) :
    (tonalOverwrite host ⟨"", [t], .whole⟩).map TBU.tone =
    host.map (λ _ => t) := by
  simp [tonalOverwrite, List.map_map]

/-- Overwrite of an empty host is empty. -/
theorem tonalOverwrite_nil {S : Type} [DecidableEq S] [BEq S] [Repr S]
    (spec : Spec) : tonalOverwrite ([] : List (TBU S)) spec = [] := by
  simp [tonalOverwrite]
  split <;> simp_all

/-- Replacive-dominant GT is dominant (sanity check on the classification). -/
theorem replaciveDominant_isDominant :
    GTDominance.isDominant .replaciveDominant = true := rfl

/-- Subtractive-dominant GT is dominant. -/
theorem subtractiveDominant_isDominant :
    GTDominance.isDominant .subtractiveDominant = true := rfl

/-- Recessive GT is non-dominant. -/
theorem recessive_isNonDominant :
    GTDominance.isNonDominant .recessive = true := rfl

/-- Neutral GT is non-dominant. -/
theorem neutral_isNonDominant :
    GTDominance.isNonDominant .neutral = true := rfl

/-- The dominant GT asymmetry holds for a typical case: dependent trigger
    targeting a lexical head. -/
theorem dominant_asymmetry_typical :
    DominantGTAsymmetry.holds ⟨true, true⟩ = true := rfl

/-- Outward dominance — a lexical head targeting its dependent — violates
    the asymmetry. -/
theorem outward_dominance_violates :
    DominantGTAsymmetry.holds ⟨false, true⟩ = false := rfl

end Theories.Phonology.Autosegmental.GrammaticalTone
