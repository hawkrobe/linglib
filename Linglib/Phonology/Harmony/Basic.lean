/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Chain

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
* `Pattern`: a harmony pattern over a segment type — valuation, participation,
  direction, domain, control. `Pattern.Harmonic` is its surface semantics:
  within every opaque-delimited span, participating segments agree in value.

## Main results

* `harmonic_insert_transparent`: transparent segments interrupt harmlessly —
  inserting one never changes harmonicity.
* `agreeOn_iff_chain'`: pairwise agreement equals adjacent agreement on the
  participating tier — the interface of the tier-based agreement machinery
  (`Phonology/Subregular/Agree.lean`).
-/

namespace Phonology.Harmony

universe u v

variable {α : Type u} {V : Type v}

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

/-! ### Patterns and their surface semantics

The descriptive object every mechanism must derive
([ritter-vanderhulst-2024-themes] (2)): harmony creates likeness among the
participating vowels of a domain. Transparent segments are skipped; opaque
segments delimit the spans within which agreement holds. -/

/-- A harmony pattern over segment type `α` with harmonic values in `V`: the
    feature valuation (`none` = no harmonic counterpart), the participation
    classification, and the typological descriptors. -/
structure Pattern (α : Type u) (V : Type v) where
  value         : α → Option V
  participation : α → Participation
  direction     : Direction := .bidirectional
  domain        : Domain := .word
  control       : ControlType V := .rootControlled

/-- Pairwise agreement in harmonic value. -/
def AgreeOn (p : Pattern α V) (w : List α) : Prop :=
  w.Pairwise fun a b => p.value a = p.value b

/-- The harmonic tier: participating and opaque segments. Transparent and icy
    segments project out; opaque segments stay because they delimit spans. -/
def Pattern.tier (p : Pattern α V) (w : List α) : List α :=
  w.filter fun s =>
    decide (p.participation s = .participating ∨ p.participation s = .opaque)

/-- Adjacent harmonic compatibility: two neighbouring tier segments agree in
    value unless either is an opaque blocker
    ([ritter-vanderhulst-2024-themes] (8c)). -/
def Pattern.Compatible (p : Pattern α V) (a b : α) : Prop :=
  p.participation a = .opaque ∨ p.participation b = .opaque ∨
    p.value a = p.value b

/-- Surface harmonicity: the tier is a chain of compatible segments — within
    every opaque-delimited span, participating segments agree in value. -/
def Pattern.Harmonic (p : Pattern α V) (w : List α) : Prop :=
  (p.tier w).IsChain p.Compatible

/-- **Transparency is harmless interruption** ([ritter-vanderhulst-2024-themes]
    §1.3.2): inserting a non-participating, non-opaque segment never changes
    harmonicity. -/
theorem Pattern.harmonic_insert_transparent {p : Pattern α V} {t : α}
    (w₁ w₂ : List α) (hp : p.participation t ≠ .participating)
    (ho : p.participation t ≠ .opaque) :
    p.Harmonic (w₁ ++ t :: w₂) ↔ p.Harmonic (w₁ ++ w₂) := by
  unfold Pattern.Harmonic Pattern.tier
  simp [List.filter_append, hp, ho]

/-- Without opaque segments, harmonicity is pairwise agreement on the whole
    tier: adjacent compatibility is plain value-agreement, which is transitive,
    so the local (chain) and global (pairwise) formulations coincide. The chain
    formulation is the interface of the tier-based agreement machinery
    (`Phonology/Subregular/Agree.lean`). -/
theorem Pattern.harmonic_iff_agreeOn {p : Pattern α V} {w : List α}
    (h : ∀ s ∈ w, p.participation s ≠ .opaque) :
    p.Harmonic w ↔ AgreeOn p (p.tier w) := by
  have hmem : ∀ s ∈ p.tier w, p.participation s ≠ .opaque :=
    fun s hs => h s (List.mem_of_mem_filter hs)
  haveI : Trans (fun a b => p.value a = p.value b)
      (fun a b => p.value a = p.value b) (fun a b => p.value a = p.value b) :=
    ⟨fun h₁ h₂ => h₁.trans h₂⟩
  unfold Pattern.Harmonic AgreeOn
  rw [← List.isChain_iff_pairwise]
  suffices key : ∀ l : List α, (∀ s ∈ l, p.participation s ≠ .opaque) →
      (l.IsChain p.Compatible ↔ l.IsChain fun a b => p.value a = p.value b) from
    key _ hmem
  intro l hl
  induction l with
  | nil => exact iff_of_true .nil .nil
  | cons a l ih =>
    cases l with
    | nil => exact iff_of_true (.singleton _) (.singleton _)
    | cons b l =>
      have ha := hl a (by simp)
      have hb := hl b (by simp)
      simp only [List.isChain_cons_cons, Pattern.Compatible, ha, hb, false_or,
        ih fun s hs => hl s (List.mem_cons_of_mem a hs)]

end Phonology.Harmony
