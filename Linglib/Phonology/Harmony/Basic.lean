/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

/-!
# Vowel harmony: pattern-level vocabulary

The theory-neutral typological vocabulary of vowel harmony, anchored on
[ritter-vanderhulst-2024-themes], the framing chapter of
[ritter-vanderhulst-2024]: participation roles, directionality, control type,
domain, and the harmonic feature types. Mechanisms — subregular transduction
(`Phonology/Subregular/Harmony.lean`), autosegmental spreading, constraint
ranking — consume this vocabulary; rival analyses of one pattern differ in
mechanism, not in these descriptors.

## Main definitions

* `Participation`: how a segment participates — full participant, transparent,
  opaque (blocker), or icy target.
* `Direction`: the direction of the agreement relation.
* `ControlType`: root-controlled vs dominant-recessive vs affix-controlled,
  parameterized by the harmonic value type.
* `Domain`: the morphological or prosodic domain delimiting harmony.
* `HarmonyType`: the attested harmonic feature types.
-/

namespace Phonology.Harmony

universe u

/-- How a segment participates in harmony ([ritter-vanderhulst-2024-themes]
    §1.3): full participants alternate and propagate; transparent (neutral)
    vowels are skipped harmlessly; opaque vowels (blockers) impose their own
    value on subsequent targets; icy targets (absorbing vowels) undergo harmony
    without passing it on. -/
inductive Participation where
  | participating
  | transparent
  | opaque
  | icyTarget
  deriving DecidableEq, Repr

/-- Direction of the harmonic agreement relation
    ([ritter-vanderhulst-2024-themes] §1.2.3): prototypical harmony is
    bidirectional, moving outward from the root; unidirectional cases are
    either stipulated or derived from target criteria or domain exclusions. -/
inductive Direction where
  | rightward
  | leftward
  | bidirectional
  deriving DecidableEq, Repr

/-- Who determines the harmonic value ([ritter-vanderhulst-2024-themes]
    §1.2.4): the root (morphologically determined trigger; affixes alternate,
    roots do not), a designated dominant value regardless of morphological
    position (phonologically determined, typical of ATR systems), or affixes
    (metaphony and umlaut). Parameterized by the harmonic value type `V`. -/
inductive ControlType (V : Type u) where
  | rootControlled
  | dominantRecessive (dominant : V)
  | affixControlled
  deriving DecidableEq, Repr

/-- The domain delimiting harmony ([ritter-vanderhulst-2024-themes] §1.2.2):
    morphological (root, stem, word) or prosodic (foot, as in metaphony and
    umlaut; phrase, in post-lexical harmony); `stemAndFirstAffix` is the
    bounded bisyllabic agreement the chapter singles out. -/
inductive Domain where
  | root
  | stem
  | stemAndFirstAffix
  | word
  | foot
  | phrase
  deriving DecidableEq, Repr

/-- The harmonic feature types surveyed in [ritter-vanderhulst-2024-themes]
    §1.5: palatal and labial harmony occur frequently; height, tongue-root
    ([ATR]/[RTR] — `Phonology/Harmony/TongueRoot.lean`), tense-lax, nasal,
    emphasis (post-velar), retroflexion, and total (echo) harmony are attested.
    Tonal harmony is unattested. -/
inductive HarmonyType where
  | palatal
  | labial
  | height
  | tongueRoot
  | tenseLax
  | nasal
  | emphasis
  | retroflex
  | total
  deriving DecidableEq, Repr

end Phonology.Harmony
