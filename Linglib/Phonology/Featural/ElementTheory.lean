/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Featural.Bundle
import Linglib.Phonology.OCP

/-!
# Element Theory — vowels, glides, and gutturals as elemental bundles
[kaye-lowenstamm-vergnaud-1985] [backley-2011]
[kaye-lowenstamm-1984] [backley-nasukawa-2010]

Element Theory (ET) builds segments from a small inventory of
**privative** primes called *elements*. Three **resonance elements**
suffice for the vowel/glide system:

* **|I|** — palatality (front quality); surfaces as [i] in a nucleus,
  as [j] elsewhere (onset/coda/offglide).
* **|U|** — labiality (rounding); surfaces as [u] in a nucleus, as
  [w] elsewhere.
* **|A|** — aperture (lowness/openness); surfaces as [a]/[ʌ] in a
  nucleus, and — per [angoujard-1995] and [faust-lampitelli-2026]
  — as the resonance element of *gutturals* when associated to a
  C-slot. Two further elements, **|ʔ|** (occlusion, glottal closure)
  and **|h|** (noise, frication), specify the consonantal "stop" or
  "fricative" character of laryngeals/pharyngeals/uvulars.

Following [backley-2011] ch. 2, each element in a segment may be
the **head** (most prominent contributor) or an **operator** (modifier).
The contrast between [ʌ] and [a] in the paper (eq. 21) is precisely a
headedness contrast: [ʌ] = bare |A|, [a] = headed |A|. The contrast
between pharyngeals (ħ, ʕ) and laryngeals/uvulars (ʔ, h, χ, ʁ) is
analogously a headedness contrast on the |A| element (eq. 20).

## ET as a FeatureBundle instance, not a parallel framework

Per the design of `Phonology/Featural/Bundle.lean`, `FeatureBundle F V`
is parametric over feature index `F` and value type `V`. ET is the
instantiation **`F := Element`, `V := Headedness`**:

* `none` at element `e` means *absent from this segment*.
* `some .bare` at element `e` means *present as operator*.
* `some .headed` at element `e` means *present as head*.

Lionnet's Subtonal feature bundle in
`Phonology/Autosegmental/RegisterTier.lean` is the
binary-feature instantiation `F := Subtonal`, `V := Bool`. Hayes-style
binary features in `Phonology/Featural/Features.lean` are
the instantiation `F := Feature`, `V := Bool` (after a thin
`Segment` wrapper).

The shared OCP-merger operation lives at the tier level
(`OCP.collapse`) and works
uniformly for all three instantiations. The framework-divergence
between Hayes binary, Lionnet subtonal, and ET privative-with-head
lives at the *segment representation* level — different `(F, V)`
choices commit to different theories of what makes two segments
"the same".

## Scope

This file provides the substrate. Per CLAUDE.md fragment-schema
discipline, ET decompositions of specific languages (Tigrinya
gutturals, Tigre vowels) are *paper-specific projections* and live in
study files (e.g. `Studies/FaustLampitelli2026.lean`),
not in fragment files.

The full Backley 2011 inventory adds tonal elements |H| and |L|
(omitted here — they belong with `Tone`'s
TRN substrate when needed). Charm ([kaye-lowenstamm-vergnaud-1985])
is omitted following [backley-2011]'s textbook synthesis, which
abandoned charm in favour of headedness as the prominence-encoding
device.
-/

namespace Phonology.ElementTheory

open Phonology.Featural

-- ============================================================================
-- § 1: Elements and Headedness
-- ============================================================================

/-- The five primes of Element Theory needed for the
    vowel/glide/guttural system [kaye-lowenstamm-vergnaud-1985]
    [backley-2011]. Tonal elements (H, L) are omitted; they
    belong with `Autosegmental.RegisterTier`'s TRN substrate. -/
inductive Element where
  /-- Palatality / front quality. Vowel realization [i], glide [j]. -/
  | I
  /-- Labiality / rounding. Vowel realization [u], glide [w]. -/
  | U
  /-- Aperture / lowness. Vowel realizations [a]/[ʌ]; consonantal
      realization is the `[A]`-bearing component of gutturals. -/
  | A
  /-- Glottal closure / occlusion (|ʔ|). Distinguishes [ʔ] and the
      stop component of pharyngeals from continuants. -/
  | glottal
  /-- Noise / frication (|h|). Distinguishes the fricative component
      of [h, ħ, χ, ʁ] from pure stops. -/
  | noise
  deriving DecidableEq, Repr, Hashable

/-- Headedness [backley-2011] ch. 2: each element in a segment
    can be the *head* (most prominent) or an *operator* (modifier).

    In the [faust-lampitelli-2026] analysis (eq. 21), the contrast
    between [ʌ] (bare |A|) and [a] (headed |A|) is the headedness
    contrast. Eq. (20) extends the same contrast to gutturals:
    pharyngeals [ħ, ʕ] are headed by |A|, laryngeals [ʔ, h] and uvulars
    [χ, ʁ] are not. -/
inductive Headedness where
  /-- Operator: present in the segment but not the head. -/
  | bare
  /-- Head: the most prominent element of the segment. -/
  | headed
  deriving DecidableEq, Repr

/-- **Element-Theory bundle**: an instance of the parametric
    `FeatureBundle F V` substrate at `F := Element`, `V := Headedness`.

    A bundle assigns each element either `none` (absent) or
    `some .bare` (present as operator) or `some .headed`
    (present as head). The set of headed elements is at most a
    singleton in canonical Element-Theory analyses (the head is
    unique), though this file does not enforce that constraint at
    the type level. -/
abbrev ETBundle : Type := FeatureBundle Element Headedness

-- ============================================================================
-- § 2: Constructors for Bundles
-- ============================================================================

namespace ETBundle

/-- The empty ET bundle: no elements. The phonetic realization of an
    empty bundle in a vocalic position is the language's epenthetic
    vowel — [ɨ] in Tigrinya/Tigre per [faust-lampitelli-2026]
    eq. (22). -/
def empty : ETBundle := FeatureBundle.empty

/-- A bundle with one headed element and no operators. -/
def headOnly (e : Element) : ETBundle :=
  FeatureBundle.single e .headed

/-- A bundle with one bare-operator element and no head. -/
def bareOnly (e : Element) : ETBundle :=
  FeatureBundle.single e .bare

/-- A bundle with a head and a single operator. -/
def headPlusOp (head : Element) (op : Element) : ETBundle :=
  fun f =>
    if f = head then some .headed
    else if f = op then some .bare
    else none

/-- Element `e` is *present* in the bundle (head or operator),
    regardless of headedness status. -/
def HasElement (b : ETBundle) (e : Element) : Prop := (b e).isSome = true

instance (b : ETBundle) (e : Element) : Decidable (HasElement b e) :=
  inferInstanceAs (Decidable ((b e).isSome = true))

/-- Element `e` is the *head* of the bundle. -/
def IsHead (b : ETBundle) (e : Element) : Prop :=
  b e = some .headed

instance (b : ETBundle) (e : Element) : Decidable (IsHead b e) :=
  inferInstanceAs (Decidable (b e = some .headed))

end ETBundle

-- ============================================================================
-- § 3: Resonance-Tier vs A-Tier Projections
-- ============================================================================

/-- Following the textual paper (paper §3.3.2 + eq. 34) and
    [angoujard-1995]: in ET, the |A| element is on a different
    tier from |I, U|. The A-tier registers only |A|-presence (with
    headedness); the I/U-tier registers |I|/|U| presence.

    This is exactly the parametric tier-projection idea of
    `Rolle2018.tonalTier` (the tonal tier, via `Tier.total`)
    for tones, instantiated for ET. -/
def aTier (b : ETBundle) : Option Headedness := b .A

/-- The I/U-tier [kaye-lowenstamm-vergnaud-1985]: a pair
    `(Option Headedness, Option Headedness)` for whether |I| and |U|
    are specified, and how. Most segments specify at most one of the
    two (front vs back); the type-level pair allows for the rare
    diphthongs that specify both. -/
def iuTier (b : ETBundle) : Option Headedness × Option Headedness :=
  (b .I, b .U)

/-- Project a bundle to its A-only stratum: keep |A| (with
    headedness), erase everything else. The output bundle is the
    "A-tier projection" of the original. -/
def projectA (b : ETBundle) : ETBundle :=
  fun e => match e with
    | .A => b .A
    | _  => none

/-- Project a bundle to its I/U-only stratum: keep |I| and |U|,
    erase everything else. -/
def projectIU (b : ETBundle) : ETBundle :=
  fun e => match e with
    | .I => b .I
    | .U => b .U
    | _  => none

/-! ### OCP-merger of element tiers -/

/-- The element-tier OCP merger lands in the OCP-clean set: collapsing runs of
    identical `Headedness` markers (the |A|+|A| guttural fusion of
    [faust-lampitelli-2026]) leaves no two adjacent identicals. ET's instantiation of
    `OCP.collapse_clean`. -/
theorem element_tier_collapse_clean (xs : List Headedness) :
    OCP.IsClean (OCP.collapse xs) :=
  OCP.collapse_clean xs

end Phonology.ElementTheory
