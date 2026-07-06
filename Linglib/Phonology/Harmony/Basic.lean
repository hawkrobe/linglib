/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Chain

/-!
# Vowel harmony: pattern-level vocabulary

The theory-neutral vocabulary of vowel harmony, anchored on
[ritter-vanderhulst-2024-themes]: the typological enums and `Pattern`, the
descriptive object mechanisms derive. At a finite alphabet a pattern presents
a TSL₂ grammar (`Pattern.harmonic_iff_mem_tsl`). Segment-level participation
cannot express parasitic harmony ((8b)) or configuration-dependent blocking
(Yakut); those need the general forbidden-pairs machinery.

## Main definitions

* `Participation`, `Direction`, `ControlType`, `Domain`, `HarmonyType`: the
  typological enums.
* `Pattern`: valuation, participation, descriptors; `Pattern.Harmonic` is the
  surface semantics — tier-adjacent compatibility with blocker imposition and
  icy absorption.

## Main results

* `Pattern.harmonic_insert_transparent`: transparency interrupts harmlessly.
* `Pattern.harmonic_iff_agreeOn`: with all segments participating, the chain
  and pairwise formulations coincide.
-/

namespace Phonology.Harmony

universe u v

variable {α : Type u} {V : Type v}

/-- How a segment participates in harmony ([ritter-vanderhulst-2024-themes] §1.3). -/
inductive Participation where
  /-- Alternates and propagates. -/
  | participating
  /-- Skipped harmlessly (neutral). -/
  | transparent
  /-- Does not undergo; imposes its value on what follows ((8c)). -/
  | opaque
  /-- Undergoes without passing on ([jurgec-2011]'s absorbing vowels). -/
  | icyTarget
  deriving DecidableEq, Repr

/-- Direction of the agreement relation ([ritter-vanderhulst-2024-themes] §1.2.3). -/
inductive Direction where
  | rightward
  | leftward
  /-- The prototype: outward from the root, no stipulated direction. -/
  | bidirectional
  deriving DecidableEq, Repr

/-- Who determines the harmonic value ([ritter-vanderhulst-2024-themes] §1.2.4). -/
inductive ControlType (V : Type u) where
  /-- Roots do not alternate; affixes harmonize to them (morphologically determined). -/
  | rootControlled
  /-- A designated value wins regardless of position (phonologically determined). -/
  | dominantRecessive (dominant : V)
  /-- Posed as an open question by the chapter: metaphony and umlaut, where
      stress attracts the harmonic value. -/
  | affixControlled
  deriving DecidableEq, Repr

/-- The domain delimiting harmony ([ritter-vanderhulst-2024-themes] §1.2.2). -/
inductive Domain where
  | root
  | stem
  /-- Bounded bisyllabic agreement: the stem-final vowel and first suffix vowel only. -/
  | stemAndFirstAffix
  | word
  /-- As in metaphony and umlaut. -/
  | foot
  /-- Post-lexical harmony. -/
  | phrase
  deriving DecidableEq, Repr

/-- The feature types of [ritter-vanderhulst-2024-themes] §1.5; tonal harmony
    is unattested. -/
inductive HarmonyType where
  | palatal
  | labial
  | height
  /-- [ATR]/[RTR]; see `Phonology/Harmony/TongueRoot.lean`. -/
  | tongueRoot
  | tenseLax
  | nasal
  /-- Post-velar harmony. -/
  | emphasis
  | retroflex
  /-- Echo/copy harmony: all features. -/
  | total
  deriving DecidableEq, Repr

/-! ### Patterns and their surface semantics

The descriptive object every mechanism must derive: harmony creates likeness
among the participating vowels of a domain ((2) of
[ritter-vanderhulst-2024-themes]). The undergoer/blocker/transparent
decomposition follows [aksenova-rawski-graf-heinz-2024]: transparent segments
are skipped; opaque blockers do not undergo but impose their transmitted value
on what follows ((8c)); icy targets undergo without passing on
([jurgec-2011]). -/

/-- A harmony pattern over segment type `α` with harmonic values in `V`. -/
structure Pattern (α : Type u) (V : Type v) where
  /-- The valuation; `none` = no harmonic counterpart. For opaque and icy
      segments, the value transmitted (not necessarily the phonetic one). -/
  value         : α → Option V
  /-- Stored independently of the valuation: neutral vowels' transparent-vs-opaque
      behavior is not predictable (§1.3.2). Discipline:
      `value s = none → participation s ≠ .participating`. -/
  participation : α → Participation
  direction     : Direction := .bidirectional
  domain        : Domain := .word
  control       : ControlType V := .rootControlled

/-- Pairwise agreement in harmonic value. -/
def Pattern.AgreeOn (p : Pattern α V) (w : List α) : Prop :=
  w.Pairwise fun a b => p.value a = p.value b

/-- Tier membership: everything but transparent segments. -/
def Pattern.OnTier (p : Pattern α V) (s : α) : Prop :=
  p.participation s ≠ .transparent

instance (p : Pattern α V) : DecidablePred p.OnTier := fun s => by
  unfold Pattern.OnTier; infer_instance

/-- The harmonic tier of a string. -/
def Pattern.tier (p : Pattern α V) (w : List α) : List α :=
  w.filter fun s => decide (p.OnTier s)

/-- Adjacent compatibility, left to right: an opaque right member is exempt
    (blockers do not undergo), an icy left member is exempt (no passing on);
    otherwise the values agree. Deliberately asymmetric. -/
def Pattern.Compatible (p : Pattern α V) (a b : α) : Prop :=
  p.participation a = .icyTarget ∨ p.participation b = .opaque ∨
    p.value a = p.value b

instance [DecidableEq V] (p : Pattern α V) : DecidableRel p.Compatible :=
  fun a b => by unfold Pattern.Compatible; infer_instance

/-- Surface harmonicity: the tier is a chain of compatible segments. -/
def Pattern.Harmonic (p : Pattern α V) (w : List α) : Prop :=
  (p.tier w).IsChain p.Compatible

instance [DecidableEq V] (p : Pattern α V) (w : List α) :
    Decidable (p.Harmonic w) := by
  unfold Pattern.Harmonic; infer_instance

/-- Transparency interrupts harmlessly ([ritter-vanderhulst-2024-themes] §1.3.2). -/
theorem Pattern.harmonic_insert_transparent {p : Pattern α V} {t : α}
    (w₁ w₂ : List α) (ht : p.participation t = .transparent) :
    p.Harmonic (w₁ ++ t :: w₂) ↔ p.Harmonic (w₁ ++ w₂) := by
  unfold Pattern.Harmonic Pattern.tier
  simp [List.filter_append, Pattern.OnTier, ht]

/-- With all segments participating, the chain and pairwise formulations
    coincide (value-agreement is transitive). -/
theorem Pattern.harmonic_iff_agreeOn {p : Pattern α V} {w : List α}
    (h : ∀ s ∈ w, p.participation s = .participating) :
    p.Harmonic w ↔ p.AgreeOn (p.tier w) := by
  have hmem : ∀ s ∈ p.tier w, p.participation s = .participating :=
    fun s hs => h s (List.mem_of_mem_filter hs)

  haveI : Trans (fun a b => p.value a = p.value b)
      (fun a b => p.value a = p.value b) (fun a b => p.value a = p.value b) :=
    ⟨fun h₁ h₂ => h₁.trans h₂⟩
  unfold Pattern.Harmonic Pattern.AgreeOn
  rw [← List.isChain_iff_pairwise]
  suffices key : ∀ l : List α, (∀ s ∈ l, p.participation s = .participating) →
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
      simp only [List.isChain_cons_cons, Pattern.Compatible, ha, hb,
        reduceCtorEq, false_or,
        ih fun s hs => hl s (List.mem_cons_of_mem a hs)]

end Phonology.Harmony
