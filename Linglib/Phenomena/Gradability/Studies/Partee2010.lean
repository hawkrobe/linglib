import Linglib.Theories.Semantics.Lexical.Adjective.Classification

/-!
# Partee (2010): Privative Adjectives: Subsective plus Coercion @cite{partee-2010}
@cite{kamp-1975} @cite{kamp-partee-1995}

In R. Bäuerle, U. Reyle, & T. E. Zimmermann (eds.), *Presuppositions and
Discourse: Essays Offered to Hans Kamp*, 273–292. Brill.

(Circulated as a manuscript since 2001.)

## Overview

@cite{partee-2010} argues that there are **no genuinely privative adjectives**.
What @cite{kamp-1975} classified as "privative" (fake, counterfeit, fictitious)
are actually **subsective** — they trigger **coercion of the noun's denotation**.

## Core Argument

- Traditional: `⟦fake gun⟧ ∩ ⟦gun⟧ = ∅` (privative, Kamp definition 5)
- Partee's revision: `⟦fake gun⟧ ⊆ ⟦gun*⟧` where `gun* = gun ∪ fake-gun`
  (subsective within the coerced noun)

Key evidence:

1. "Is that gun real or fake?" — the noun "gun" must include both real and
   fake guns for this question to be well-formed (§ 1, ex. 10b)
2. Polish NP-splitting data (Nowak 2000): intersective, subsective, AND
   "privative" adjectives can all participate in NP-splitting, but
   non-subsective/modal adjectives (alleged, potential) cannot (§ 2)

## Result

The traditional 4-class hierarchy collapses to three classes:

    intersective > subsective > non-subsective (modal)

The "privative" class is eliminated. The mathematical basis is
`any_adj_subsective_under_selfcoercion`: ANY adjective is subsective
when the noun is coerced to include the adjective's own extension.
The empirical question is whether this coercion is linguistically real —
the Polish data argues it is.

## Structure

- § 1: Noun coercion and the core subsectivity theorem
- § 2: The revised hierarchy (3 classes, not 4)
- § 3: Polish NP-splitting evidence (Nowak 2000)
-/

namespace Phenomena.Gradability.Studies.Partee2010

open Semantics.Lexical.Adjective.Classification

-- ════════════════════════════════════════════════════
-- § 1. Noun Coercion
-- ════════════════════════════════════════════════════

/-! @cite{partee-2010}'s central mechanism: when a "privative" adjective
    combines with a noun N, the noun's denotation is coerced to
    N* = N ∪ adj(N). The adjective is then subsective within N*. -/

variable {W E : Type*}

/-- Noun coercion: expand the noun's denotation to include entities in
    an additional extension. `coerceNoun N ext` = N ∪ ext.

    In @cite{partee-2010}'s analysis, `ext` is the adjective's own
    extension for that noun: "gun" → "gun*" = guns ∪ fake-guns. -/
def coerceNoun (N ext : Property W E) : Property W E :=
  λ w x => N w x || ext w x

/-- **Core theorem.** Any adjective is affirmative (subsective) when the
    noun is coerced to include the adjective's own extension. This is
    the mathematical content of @cite{partee-2010}'s argument: the
    privative class is not a genuine semantic class but an artifact of
    ignoring noun coercion.

    The proof is trivially true — `adj(N)(w)(x) → N(w)(x) ∨ adj(N)(w)(x)` —
    which is exactly Partee's point: the "privative" classification can
    always be dissolved by acknowledging that the noun's denotation shifts.
    The substantive claim is that this coercion is linguistically real,
    not ad hoc (see § 3). -/
theorem any_adj_subsective_under_selfcoercion (adj : AdjMeaning W E) :
    ∀ (N : Property W E) (w : W) (x : E),
      adj N w x = true → coerceNoun N (adj N) w x = true := by
  intro N w x h
  simp only [coerceNoun, Bool.or_eq_true]
  exact Or.inr h

/-- Coercion is monotone: the coerced noun always extends the original. -/
theorem coerceNoun_extends (N ext : Property W E) (w : W) (x : E)
    (h : N w x = true) : coerceNoun N ext w x = true := by
  simp only [coerceNoun, h, Bool.true_or]

-- ════════════════════════════════════════════════════
-- § 2. The Revised Hierarchy
-- ════════════════════════════════════════════════════

/-! Under @cite{partee-2010}'s analysis, the adjective hierarchy collapses
    from four classes to three. The privative class is absorbed into the
    subsective class (via noun coercion). -/

/-- The revised three-class hierarchy. -/
inductive RevisedClass where
  /-- `⟦AN⟧ = ⟦A⟧ ∩ ⟦N⟧` (Kamp's intersective) -/
  | intersective
  /-- `⟦AN⟧ ⊆ ⟦N*⟧` — includes former "privatives" via coercion
      (Kamp's subsective, generalized) -/
  | subsective
  /-- No entailment: alleged, potential, putative (Kamp's non-subsective) -/
  | nonSubsective
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 3. Polish NP-Splitting Evidence (Nowak 2000)
-- ════════════════════════════════════════════════════

/-! @cite{partee-2010} § 2 uses Polish NP-splitting data (Nowak 2000) as
    evidence for the reclassification. In Polish, Adj+N phrases can be
    "split" across the sentence (Adj sentence-initial, N sentence-final).

    The critical observation: the split does NOT track the traditional
    4-class boundary. Instead, intersective, subsective, AND traditionally
    "privative" adjectives can all split, but non-subsective/modal
    adjectives (alleged, potential, predicted) cannot.

    This patterns exactly as the 3-class hierarchy predicts: the split
    tracks subsectivity (with coercion), not the traditional privative/
    non-privative distinction. -/

/-- Which adjective classes allow Polish NP-splitting (Nowak 2000, cited
    in @cite{partee-2010} § 2).

    CAN split: rozległy "large" (intersective), biedny "poor/not rich"
    (intersective), Chinese/generous/pretty (intersective), skillful/
    recent/good/typical (subsective), counterfeit/past/spurious/imaginary/
    fictitious (traditionally "privative").

    CANNOT split: biedny "pitiful" (non-subsective), Polish translations
    of alleged/potential/predicted/disputed (non-subsective/modal). -/
def canSplitNP : RevisedClass → Bool
  | .intersective  => true
  | .subsective    => true   -- includes traditionally "privative" adjectives
  | .nonSubsective => false  -- alleged, potential, predicted cannot split

/-- The NP-splitting data supports the revised hierarchy: the split
    tracks the 3-class boundary (subsective vs non-subsective), not the
    traditional 4-class boundary (privative vs non-privative). -/
theorem splitting_tracks_revised_hierarchy :
    canSplitNP .intersective = true ∧
    canSplitNP .subsective = true ∧
    canSplitNP .nonSubsective = false := ⟨rfl, rfl, rfl⟩

/-- The traditional 4-class analysis wrongly predicts that "privative"
    adjectives should NOT be able to split (since they share a class
    boundary with non-subsective adjectives). The revised 3-class analysis
    correctly predicts they CAN split (since they are subsective). -/
theorem traditional_mispredicts_privative_splitting :
    -- Under the revised analysis, "privative" = subsective, so can split
    canSplitNP .subsective = true := rfl

end Phenomena.Gradability.Studies.Partee2010
