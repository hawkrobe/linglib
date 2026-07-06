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
  At a finite alphabet a pattern presents a TSL₂ grammar
  (`Pattern.harmonic_iff_mem_tsl`) — a small DFA on the tier.

## Main results

* `harmonic_insert_transparent`: transparent segments interrupt harmlessly —
  inserting one never changes harmonicity.
* `Pattern.harmonic_iff_agreeOn`: with all segments participating, harmonicity
  is pairwise agreement — the local (chain) and global (pairwise) formulations
  coincide.
-/

namespace Phonology.Harmony

universe u v

variable {α : Type u} {V : Type v}

/-- How a segment participates in harmony ([ritter-vanderhulst-2024-themes]
    §1.3): full participants alternate and propagate; transparent (neutral)
    vowels are skipped harmlessly; opaque vowels (blockers) impose their own
    value on subsequent targets; icy targets (absorbing vowels, [jurgec-2011])
    undergo harmony without passing it on. -/
inductive Participation where
  | participating
  | transparent
  | opaque
  | icyTarget
  deriving DecidableEq, Repr

/-- Direction of the harmonic agreement relation
    ([ritter-vanderhulst-2024-themes] §1.2.3): prototypical harmony may have no
    direction, being bidirectional (moving outward from the root); unidirectional
    cases are either stipulated or derived from target criteria or domain
    exclusions. -/
inductive Direction where
  | rightward
  | leftward
  | bidirectional
  deriving DecidableEq, Repr

/-- Who determines the harmonic value ([ritter-vanderhulst-2024-themes]
    §1.2.4): the root (morphologically determined trigger; affixes alternate,
    roots do not), a designated dominant value regardless of morphological
    position (phonologically determined, typical of ATR systems), or affixes —
    a class the chapter poses as an open question, instanced by metaphony and
    umlaut where stress acts as an attractor of the harmonic value.
    Parameterized by the harmonic value type `V`. -/
inductive ControlType (V : Type u) where
  | rootControlled
  | dominantRecessive (dominant : V)
  | affixControlled
  deriving DecidableEq, Repr

/-- The domain delimiting harmony ([ritter-vanderhulst-2024-themes] §1.2.2):
    morphological (root, stem, word) or prosodic (foot, as in metaphony and
    umlaut; phrase, in post-lexical harmony); `stemAndFirstAffix` is the bounded
    bisyllabic agreement the chapter singles out — the stem-final vowel and the
    first suffix vowel only. -/
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

The descriptive object every mechanism must derive: harmony creates likeness
among the participating vowels of a domain ((2) of
[ritter-vanderhulst-2024-themes]). The undergoer/blocker/transparent
decomposition follows [aksenova-rawski-graf-heinz-2024]: transparent segments
are skipped; opaque blockers do not undergo but impose their transmitted value
on what follows ((8c)); icy targets undergo without passing on
([jurgec-2011]). -/

/-- A harmony pattern over segment type `α` with harmonic values in `V`: the
    feature valuation (`none` = no harmonic counterpart), the participation
    classification, and the typological descriptors. Participation is stored
    independently of the valuation because the behavior of neutral vowels as
    transparent or opaque is not predictable ([ritter-vanderhulst-2024-themes]
    §1.3.2); intended discipline: `value s = none → participation s ≠
    .participating` (allophonic undergoing of neutral vowels lives in a
    separate valuation). For an opaque or icy segment, `value` is the value it
    transmits, which may differ from its phonetic specification. -/
structure Pattern (α : Type u) (V : Type v) where
  value         : α → Option V
  participation : α → Participation
  direction     : Direction := .bidirectional
  domain        : Domain := .word
  control       : ControlType V := .rootControlled

/-- Pairwise agreement in harmonic value. -/
def Pattern.AgreeOn (p : Pattern α V) (w : List α) : Prop :=
  w.Pairwise fun a b => p.value a = p.value b

/-- Tier membership: everything but transparent segments. Opaque blockers stay
    on the tier because they impose values; icy targets stay because they
    undergo ([aksenova-rawski-graf-heinz-2024]'s Yakut keeps its harmonizing
    blockers on the tier). -/
def Pattern.OnTier (p : Pattern α V) (s : α) : Prop :=
  p.participation s ≠ .transparent

instance (p : Pattern α V) : DecidablePred p.OnTier := fun s => by
  unfold Pattern.OnTier; infer_instance

/-- The harmonic tier of a string. -/
def Pattern.tier (p : Pattern α V) (w : List α) : List α :=
  w.filter fun s => decide (p.OnTier s)

/-- Adjacent harmonic compatibility, read left to right: the right member is
    exempt if it is an opaque blocker (blockers do not undergo, but as left
    member they impose their transmitted `value` on what follows —
    [ritter-vanderhulst-2024-themes] (8c)); the left member is exempt if it is
    an icy target (undergoes without passing on, [jurgec-2011]). Otherwise the
    pair agrees in value. Deliberately asymmetric — blocking is directional
    (Buryat's `*[+high][−high,+round]`, [aksenova-rawski-graf-heinz-2024]);
    imposition is encoded left-to-right, mirroring for leftward systems. -/
def Pattern.Compatible (p : Pattern α V) (a b : α) : Prop :=
  p.participation a = .icyTarget ∨ p.participation b = .opaque ∨
    p.value a = p.value b

instance [DecidableEq V] (p : Pattern α V) : DecidableRel p.Compatible :=
  fun a b => by unfold Pattern.Compatible; infer_instance

/-- Surface harmonicity: the tier is a chain of compatible segments —
    agreement propagates left to right, blockers impose their transmitted
    value, icy targets absorb. -/
def Pattern.Harmonic (p : Pattern α V) (w : List α) : Prop :=
  (p.tier w).IsChain p.Compatible

instance [DecidableEq V] (p : Pattern α V) (w : List α) :
    Decidable (p.Harmonic w) := by
  unfold Pattern.Harmonic; infer_instance

/-- **Transparency is harmless interruption** ([ritter-vanderhulst-2024-themes]
    §1.3.2): inserting a non-participating, non-opaque segment never changes
    harmonicity. -/
theorem Pattern.harmonic_insert_transparent {p : Pattern α V} {t : α}
    (w₁ w₂ : List α) (ht : p.participation t = .transparent) :
    p.Harmonic (w₁ ++ t :: w₂) ↔ p.Harmonic (w₁ ++ w₂) := by
  unfold Pattern.Harmonic Pattern.tier
  simp [List.filter_append, Pattern.OnTier, ht]

/-- Without opaque segments, harmonicity is pairwise agreement on the whole
    tier: adjacent compatibility is plain value-agreement, which is transitive,
    so the local (chain) and global (pairwise) formulations coincide. The chain
    formulation is the interface of the tier-based agreement machinery
    (`Phonology/Subregular/Agree.lean`). -/
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
