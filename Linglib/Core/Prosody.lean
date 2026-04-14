import Mathlib.Order.Nat

/-!
# Core.Prosody
@cite{pierrehumbert-1980} @cite{beckman-pierrehumbert-1986}

Theory-neutral prosodic types: pitch accents, phrase accents, boundary
tones, and the prosodic hierarchy, following the autosegmental-metrical
(AM) framework established by @cite{pierrehumbert-1980} for English and
extended cross-linguistically by @cite{beckman-pierrehumbert-1986}.

@cite{steedman-2000} uses these types to connect prosodic structure to
CCG derivations and information structure.

## Overview

These types are used across multiple theories:
- CCG/Intonation: prosodic CCG derivations
- Information Structure: spellout constraints
- Focus theory: prosodic realization of focus/givenness
- Autosegmental phonology: tone and register systems

-/

namespace Core.Prosody

-- ============================================================================
-- § 1: Pitch Accents
-- ============================================================================

/--
Pitch accent types (@cite{pierrehumbert-1980}, ToBI conventions).

The full inventory of English pitch accents. A starred tone (*) is
phonologically linked to the stressed syllable; an unstarred tone in a
bitonal accent precedes or follows it at some given space in time.

@cite{pierrehumbert-1980} identified seven possible pitch accent shapes;
the H*+H accent was eliminated as a possible pattern, leaving six
(@cite{beckman-pierrehumbert-1986} §2.1).

In Japanese, by contrast, the single possible pitch accent shape is a
lexically linked H, analyzed as H*+L. The accent *location* is lexically
distinctive, but the *shape* is fixed. English uses the full inventory
to contrast different intonational meanings (e.g., declarative vs.
surprise-redundancy vs. impatient reassertion on the same word *orange*
in *an orange ballgown*; @cite{beckman-pierrehumbert-1986} Fig. 1).
-/
inductive PitchAccent where
  | H_star        -- H*: default declarative accent
  | L_star        -- L*: low target on stressed syllable
  | H_star_plus_L -- H*+L: fall from stressed syllable (downstepping)
  | H_plus_L_star -- H+L*: peak precedes stressed syllable (scooped)
  | L_star_plus_H -- L*+H: rise from stressed syllable
  | L_plus_H_star -- L+H*: rise to stressed syllable (theme accent)
  | null          -- No accent (deaccented/background material)
  deriving Repr, DecidableEq, Inhabited

/-- Is this a bitonal accent (two tones)?
    Bitonal accents trigger catathesis
    (@cite{beckman-pierrehumbert-1986} §3.2). -/
def PitchAccent.isBitonal : PitchAccent → Bool
  | .H_star_plus_L | .H_plus_L_star | .L_star_plus_H | .L_plus_H_star => true
  | _ => false

-- ============================================================================
-- § 2: Phrase Accents and Boundary Tones
-- ============================================================================

/--
Phrase accent: terminal tone of the intermediate phrase.

@cite{beckman-pierrehumbert-1986} §4.2–4.3 decompose what
@cite{pierrehumbert-1980} called the "phrase accent" into a tone that
spreads from the last pitch accent to the edge of the intermediate
phrase. The phrase accent is H or L, independent of the boundary tone.

In Japanese, the accentual phrase boundary L is always L; the only
variation is whether an optional H boundary tone follows at the
intonation phrase edge.
-/
inductive PhraseAccent where
  | H  -- High phrase accent (continuation rise within ip)
  | L  -- Low phrase accent (default)
  deriving Repr, DecidableEq, Inhabited

/--
Boundary tone: terminal tone of the intonation phrase.

@cite{beckman-pierrehumbert-1986} distinguish the boundary tone (edge
of the intonation phrase) from the phrase accent (edge of the intermediate
phrase). Together, the phrase accent and boundary tone produce four
terminal configurations: LL%, LH%, HL%, HH%.

In Japanese, the boundary tone at an intonation phrase edge is always L
except in yes/no questions, where H is optional
(@cite{beckman-pierrehumbert-1986} §4.2).
-/
inductive BoundaryTone where
  | L_pct  -- L%: low boundary (falling, finality)
  | H_pct  -- H%: high boundary (rising, continuation/question)
  deriving Repr, DecidableEq, Inhabited

/-- Full terminal contour of an intonation phrase: phrase accent +
    boundary tone. @cite{pierrehumbert-1980}: four possible combinations. -/
structure TerminalContour where
  phraseAccent : PhraseAccent
  boundaryTone : BoundaryTone
  deriving Repr, DecidableEq

/-- Standard declarative terminal: L L% -/
def TerminalContour.declarative : TerminalContour := ⟨.L, .L_pct⟩

/-- Continuation rise terminal: L H% (theme boundary) -/
def TerminalContour.continuation : TerminalContour := ⟨.L, .H_pct⟩

/-- Yes/no question terminal: H H% -/
def TerminalContour.ynQuestion : TerminalContour := ⟨.H, .H_pct⟩

/-- Calling contour / plateau terminal: H L% -/
def TerminalContour.calling : TerminalContour := ⟨.H, .L_pct⟩

-- ============================================================================
-- § 3: Prosodic Hierarchy
-- ============================================================================

/-- Prosodic hierarchy levels.

    σ < f < ω < AP < φ < ι

    @cite{beckman-pierrehumbert-1986} establish the accentual phrase (AP)
    as the domain of pitch accent distribution (at most one accent per AP,
    §2.2) and the phonological phrase (φ, equivalent to the intermediate
    phrase / ip in ToBI notation) as the domain of catathesis (§3–4).

    Used by @cite{kratzer-selkirk-2020} spellout constraints. -/
inductive ProsodicLevel where
  | σ   -- syllable
  | f   -- foot
  | ω   -- prosodic word
  | AP  -- accentual phrase (@cite{beckman-pierrehumbert-1986})
  | φ   -- phonological phrase / intermediate phrase (ip)
  | ι   -- intonational phrase
  deriving DecidableEq, Repr

/-- Numeric encoding for the prosodic hierarchy ordering. -/
def ProsodicLevel.toNat : ProsodicLevel → Nat
  | .σ => 0 | .f => 1 | .ω => 2 | .AP => 3 | .φ => 4 | .ι => 5

instance : LinearOrder ProsodicLevel :=
  LinearOrder.lift' ProsodicLevel.toNat
    (fun a b h => by cases a <;> cases b <;> simp_all [ProsodicLevel.toNat])

/-- Head-prominence: each prosodic constituent has exactly one
    prominent daughter (its head). K&S (32). -/
structure ProsodicConstituent where
  level : ProsodicLevel
  /-- Whether this constituent is the head (most prominent) of its parent -/
  isHead : Bool
  deriving Repr

-- ============================================================================
-- § 4: Accent Specification Typology
-- ============================================================================

/--
How pitch accents relate to the lexicon
(@cite{beckman-pierrehumbert-1986} §2.5).

- `lexical`: accent location specified in lexicon, shape fixed.
  Japanese: H*+L at lexically specified mora. Swedish: accent 1 vs 2.
  The accent shape cannot signal different intonational meanings.
- `postlexical`: accent shape chosen by intonation, location by prominence.
  English: 6 pitch accent shapes, location determined by focus/stress.
  The shape contrasts different intonational meanings (declarative,
  surprise, impatience, etc.).
-/
inductive AccentSpecification where
  | lexical      -- location lexically distinctive, shape fixed
  | postlexical  -- shape intonationally distinctive, location by prominence
  deriving Repr, DecidableEq

-- ============================================================================
-- § 5: Morpheme-Level Prosodic Dominance
-- ============================================================================

/--
How a morpheme interacts with the prosodic specification of its base.
@cite{kiparsky-halle-1977} @cite{rolle-2018}

Orthogonal to `AccentSpecification`, which classifies word-level accent
determination (how is the accent *location* decided?). `ProsodicDominance`
classifies morpheme-level prosodic *interaction* (does this morpheme
override the base's accent/tone, or respect it?).

The dominant/recessive distinction originates in the accentual morpheme
classes of @cite{kiparsky-halle-1977} (deaccenting vs non-deaccenting
suffixes in IE) and was generalized to tonal morphology by
@cite{rolle-2018} as the GT dominance typology.

- `dominant`: overrides the prosodic specification of the base.
  Accent: Japanese *-teki* removes stem accent (@cite{kawahara-2015}).
  Tone: Mwaghavul verbalisers replace base melody
  (@cite{akinbo-fwangwar-2026}).
- `recessive`: applies only when the base is prosodically unmarked.
  Accent: Japanese *-si* 'Mr.' preserves stem accent.
  Tone: Giphende floating tones dock only to unvalued TBUs.
- `neutral`: concatenates without prosodic interaction; the general
  phonological grammar determines the output.
  Tone: Hausa referential *-ⁿn* (@cite{rolle-2018}).
-/
inductive ProsodicDominance where
  | dominant   -- overrides base prosody
  | recessive  -- respects base prosody when present
  | neutral    -- no prosodic interaction
  deriving Repr, DecidableEq

/-- Dominant morphemes override the prosodic specification of their base. -/
def ProsodicDominance.isDominant : ProsodicDominance → Bool
  | .dominant => true
  | .recessive | .neutral => false

/-- Combine a base accent with a suffix's prosodic dominance.

    The accent position (`Option Nat`) represents a mora- or
    syllable-indexed accent; `none` = unaccented.

    - `dominant`: accent is removed regardless of input.
    - `recessive` / `neutral`: base accent is preserved. -/
def ProsodicDominance.combineAccent
    (baseAccent : Option Nat) : ProsodicDominance → Option Nat
  | .dominant  => none
  | .recessive => baseAccent
  | .neutral   => baseAccent

/-- **Transparadigmatic uniformity** (@cite{rolle-2018}): dominant
    morphemes produce the same output regardless of whether the base
    is accented or unaccented. This is the defining property of
    dominance — it neutralizes the base contrast. -/
theorem ProsodicDominance.dominant_neutralizes (a₁ a₂ : Option Nat) :
    ProsodicDominance.combineAccent a₁ .dominant =
    ProsodicDominance.combineAccent a₂ .dominant := rfl

/-- Recessive morphemes preserve the base contrast: an accented base
    stays accented, an unaccented base stays unaccented. -/
theorem ProsodicDominance.recessive_preserves (a : Option Nat) :
    ProsodicDominance.combineAccent a .recessive = a := rfl

-- ============================================================================
-- § 6: Affix Accent Typology
-- ============================================================================

/--
Fine-grained affix accent classification (@cite{kawahara-2015} §6).

The 3-way `ProsodicDominance` (dominant/recessive/neutral) captures only
one axis of morpheme–accent interaction. @cite{kawahara-2015}, building
on @cite{poser-1984} and @cite{vance-1987}, identifies eight distinct
affix accent behaviors in Japanese, differing in whether the affix
carries its own accent, whether it deletes or preserves root accent,
and whether it inserts a new accent at a particular position.

`toProsodicDominance` projects back to the coarser 3-way classification:
types that preserve root accent when present map to `recessive`; types
that override root accent map to `dominant`.
-/
inductive AffixAccentType where
  /-- Suffix bears accent; loses to root accent when root is accented.
      E.g., Japanese `-tara` (conditional): accented root → root accent
      preserved; unaccented root → suffix accent surfaces. -/
  | recessive
  /-- Suffix bears accent; always overrides root accent.
      E.g., Japanese `-ppoi` (-ish): root accent deleted, suffix accent
      surfaces regardless. -/
  | dominant
  /-- No own accent; inserts accent on root-final syllable only when
      root is unaccented. Preserves root accent when present.
      E.g., Japanese `-si` (Mr.): `ono → ono'+si`; `u'ra → u'ra+si`. -/
  | recessivePreAccent
  /-- No own accent; always inserts accent on root-final syllable,
      deleting root accent.
      E.g., Japanese `-ke` (family of): `ono → ono'+ke`; `mu'raki →
      muraki'+ke`. -/
  | dominantPreAccent
  /-- No own accent; shifts existing root accent to pre-suffix position.
      Unaccented roots remain unaccented.
      E.g., Japanese `-mono` (thing): `ka'k(+u) → kaki'+mono`;
      `nor(+u) → nori+mono`. -/
  | accentShifting
  /-- Inserts accent immediately after the affix (typically a prefix).
      E.g., Japanese `o-` (honorific): `huro' → o+hu'ro`. -/
  | postAccenting
  /-- No own accent; deletes root accent. Output is unaccented.
      E.g., Japanese `-teki` (的 -like): `ke'izai → keizai+teki`. -/
  | deaccenting
  /-- No own accent; inserts accent on root-initial syllable.
      E.g., Japanese `-zu` (group/plural): `okamoto → o'kamoto+zu`. -/
  | initialAccenting
  deriving DecidableEq, Repr

/-- Project the fine-grained 8-way classification to the coarser 3-way
    `ProsodicDominance`. Types that preserve root accent when present
    map to `recessive`; types that override it map to `dominant`. -/
def AffixAccentType.toProsodicDominance : AffixAccentType → ProsodicDominance
  | .recessive | .recessivePreAccent | .accentShifting => .recessive
  | .dominant | .dominantPreAccent | .postAccenting
  | .deaccenting | .initialAccenting => .dominant

/-- All recessive-class affixes preserve root accent when present. -/
theorem AffixAccentType.recessive_preserves_root :
    AffixAccentType.recessive.toProsodicDominance = .recessive := rfl

/-- All dominant-class affixes override root accent. -/
theorem AffixAccentType.dominant_overrides_root :
    AffixAccentType.dominant.toProsodicDominance = .dominant := rfl

/-- Deaccenting is a special case of dominance (overrides root accent). -/
theorem AffixAccentType.deaccenting_is_dominant :
    AffixAccentType.deaccenting.toProsodicDominance = .dominant := rfl

end Core.Prosody
