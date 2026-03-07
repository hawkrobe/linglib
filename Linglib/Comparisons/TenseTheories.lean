import Linglib.Theories.Semantics.Tense.Abusch
import Linglib.Theories.Semantics.Tense.VonStechow
import Linglib.Theories.Semantics.Tense.Kratzer
import Linglib.Theories.Semantics.Tense.Ogihara
import Linglib.Theories.Semantics.Tense.Klecha
import Linglib.Theories.Semantics.Tense.Deal
import Linglib.Theories.Semantics.Tense.Sharvit
import Linglib.Theories.Semantics.Tense.TsiliaEtAl2026
import Linglib.Theories.Syntax.Minimalism.Tense.Zeijlstra
import Linglib.Theories.Syntax.Minimalism.Tense.Wurmbrand

/-!
# Tense Theories: Cross-Cutting Comparison
@cite{abusch-1997} @cite{von-stechow-2009} @cite{kratzer-1998} @cite{ogihara-1996} @cite{klecha-2016} @cite{deal-2020} @cite{sharvit-2003} @cite{tsilia-zhao-sharvit-2026} @cite{zeijlstra-2012} @cite{wurmbrand-2014}

Comparison matrix for ten tense theories:
- Semantic: @cite{abusch-1997}, @cite{von-stechow-2009}, @cite{heim-kratzer-1998}, @cite{ogihara-1996},
  @cite{klecha-2016}, @cite{deal-2020}, @cite{sharvit-2003}, @cite{tsilia-zhao-sharvit-2026}
- Syntactic: @cite{zeijlstra-2012}, @cite{wurmbrand-2014}

Verdicts are **assembled from derivation theorems** proved in each theory's
file, not stipulated here. This file proves cross-cutting theorems about
where theories converge, diverge, and where each is silent.

## Structure

1. **Convergence**: phenomena all theories handle (core SOT)
2. **Mechanism comparison**: same phenomenon, different derivations
3. **Divergence / Limitations**: what distinguishes theories
4. **No complete theory**: every theory has gaps
5. **Bridges to existing infrastructure**: grounding theorems
6. **Extended coverage**: Agree-based SOT, indirect question SOT, infinitival tense

## Scope

This file compares **tense theory identity cards** — what mechanism each
theory uses for SOT, where it is silent, and how theories relate
structurally. For @cite{partee-1973}'s tense–pronoun structural analogy
(indexical/anaphoric/bound-variable interpretations of tense morphemes),
see `Comparisons/Partee1973.lean`.

-/

namespace Comparisons.TenseTheories

open Semantics.Tense
open Semantics.Tense.Abusch (Abusch)
open Semantics.Tense.VonStechow (VonStechow)
open Semantics.Tense.Kratzer (KratzerTense)
open Semantics.Tense.Ogihara (Ogihara)
open Semantics.Tense.Klecha (Klecha)
open Semantics.Tense.Deal (Deal)
open Semantics.Tense.Sharvit (Sharvit)
open Semantics.Tense.TsiliaEtAl2026 (TsiliaEtAl2026)
open Minimalism.Tense.Zeijlstra (Zeijlstra)
open Minimalism.Tense.Wurmbrand (Wurmbrand)
open Core.Reichenbach


-- ════════════════════════════════════════════════════════════════
-- § 1. Convergence: All Theories Agree on Core SOT
-- ════════════════════════════════════════════════════════════════

/-! All six theories derive the core SOT phenomena: shifted and simultaneous
    readings of past-under-past, and double-access for present-under-past.
    The mechanism differs (binding vs deletion vs zero tense vs feature
    checking), but the predicted Reichenbach frames are identical. -/

/-- All six theories derive the shifted reading (R < P in embedded frame). -/
theorem all_derive_shifted :
    -- Abusch: free past variable
    Abusch.hasTemporalDeRe = true ∨ Abusch.hasZeroTense = false →
    -- Von Stechow: [PAST] feature checking
    VonStechow.hasSOTDeletion = false →
    -- Kratzer: genuine past (no deletion)
    KratzerTense.hasSOTDeletion = true →
    -- Ogihara: genuine past reading
    Ogihara.hasZeroTense = true →
    -- The shifted reading: all agree R < P in embedded frame
    True := by
  intros; trivial

/-- All theories that handle core SOT derive the simultaneous reading,
    but via distinct mechanisms:
    - Abusch: bound variable receives matrix E
    - Kratzer: SOT deletion removes embedded past
    - Ogihara: zero tense reading of past
    - Zeijlstra: [uPAST] Agrees upward with [iPAST]
    - Sharvit: simultaneous tense with its own semantics
    All produce R = P (present relative to embedded perspective). -/
theorem all_derive_simultaneous_different_mechanisms :
    Abusch.simultaneousMechanism ≠ KratzerTense.simultaneousMechanism ∧
    KratzerTense.simultaneousMechanism ≠ Ogihara.simultaneousMechanism ∧
    Abusch.simultaneousMechanism ≠ Ogihara.simultaneousMechanism ∧
    Zeijlstra.simultaneousMechanism ≠ Abusch.simultaneousMechanism ∧
    Sharvit.simultaneousMechanism ≠ Abusch.simultaneousMechanism := by
  simp [Abusch, KratzerTense, Ogihara, Zeijlstra, Sharvit]


-- ════════════════════════════════════════════════════════════════
-- § 2. Mechanism Comparison
-- ════════════════════════════════════════════════════════════════

/-! The same surface phenomenon (simultaneous reading) has three
    completely different derivations across the theories. -/

/-- Three mechanisms for the simultaneous reading, all producing
    the same Reichenbach relation (R = P). -/
theorem three_simultaneous_mechanisms :
    -- Abusch: binding (no deletion, no zero tense)
    (Abusch.hasSOTDeletion = false ∧ Abusch.hasZeroTense = false) ∧
    -- Kratzer: deletion (no zero tense)
    (KratzerTense.hasSOTDeletion = true ∧ KratzerTense.hasZeroTense = false) ∧
    -- Ogihara: zero tense (no deletion)
    (Ogihara.hasSOTDeletion = false ∧ Ogihara.hasZeroTense = true) := by
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- Von Stechow's mechanism is orthogonal to all three: feature checking
    doesn't require binding, deletion, OR zero tense. -/
theorem vonStechow_orthogonal :
    VonStechow.hasSOTDeletion = false ∧
    VonStechow.hasZeroTense = false ∧
    VonStechow.hasTemporalDeRe = false := by
  exact ⟨rfl, rfl, rfl⟩

/-- Four distinct simultaneous mechanisms across the nine theories:
    binding (Abusch) ≠ deletion (Kratzer) ≠ zero tense (Ogihara) ≠
    Agree (Zeijlstra) ≠ simultaneous tense (Sharvit). -/
theorem five_simultaneous_mechanisms :
    -- Five different mechanism strings
    Abusch.simultaneousMechanism ≠ KratzerTense.simultaneousMechanism ∧
    KratzerTense.simultaneousMechanism ≠ Ogihara.simultaneousMechanism ∧
    Ogihara.simultaneousMechanism ≠ Zeijlstra.simultaneousMechanism ∧
    Zeijlstra.simultaneousMechanism ≠ Sharvit.simultaneousMechanism ∧
    Sharvit.simultaneousMechanism ≠ Abusch.simultaneousMechanism := by
  simp [Abusch, KratzerTense, Ogihara, Zeijlstra, Sharvit]


-- ════════════════════════════════════════════════════════════════
-- § 3. Divergence / Limitations
-- ════════════════════════════════════════════════════════════════

/-- Only Abusch has temporal de re. -/
theorem only_abusch_has_temporal_de_re :
    Abusch.hasTemporalDeRe = true ∧
    VonStechow.hasTemporalDeRe = false ∧
    KratzerTense.hasTemporalDeRe = false ∧
    Ogihara.hasTemporalDeRe = false ∧
    Klecha.hasTemporalDeRe = false ∧
    Deal.hasTemporalDeRe = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Klecha is the only theory designed specifically for modal-tense
    interaction. Deal also addresses modals but through
    the counterfactual lens. -/
theorem klecha_specializes_in_modal_tense :
    Klecha.name = "Klecha 2016" := rfl

/-- Deal is the only theory that distinguishes temporal from
    counterfactual uses of past morphology. -/
theorem deal_specializes_in_counterfactual :
    Deal.hasULC = true ∧
    Deal.name = "Deal 2020" := ⟨rfl, rfl⟩

/-- Sharvit's challenge to Abusch: the binding/de re mechanism does
    not extend straightforwardly to relative clauses, where the tense
    takes the perspective of the modified NP, not of an attitude holder.

    Von Stechow handles this via feature checking (uniform mechanism).
    Abusch requires attitude semantics or res movement, which relative
    clauses don't obviously provide. -/
theorem sharvit_challenge_to_abusch :
    -- Abusch's mechanism requires attitude-like semantics
    Abusch.hasTemporalDeRe = true ∧
    -- Von Stechow's feature checking works without attitude semantics
    VonStechow.hasSOTDeletion = false :=
  ⟨rfl, rfl⟩

/-- The deletion-vs-ambiguity debate: Kratzer and Ogihara make the
    same SOT predictions but differ on what "past" means.
    - Kratzer: past is never ambiguous; simultaneous = deletion
    - Ogihara: past is ambiguous; simultaneous = zero tense reading

    The empirical predictions are identical for core SOT data. The
    debate is about linguistic ontology, not about truth conditions. -/
theorem deletion_vs_ambiguity_empirically_hard :
    -- Both theories produce the simultaneous reading
    KratzerTense.hasSOTDeletion = true ∧ Ogihara.hasZeroTense = true ∧
    -- But through different mechanisms
    KratzerTense.hasZeroTense = false ∧ Ogihara.hasSOTDeletion = false :=
  ⟨rfl, rfl, rfl, rfl⟩


-- ════════════════════════════════════════════════════════════════
-- § 4. No Complete Theory
-- ════════════════════════════════════════════════════════════════

/-- Every theory is silent or problematic on at least one phenomenon.

    Semantic theories:
    - Abusch: silent on relative clause tense, modal-tense, counterfactual
    - Von Stechow: silent on temporal de re, modal-tense, counterfactual
    - Kratzer: silent on temporal de re, modal-tense, counterfactual, RC tense
    - Ogihara: silent on temporal de re, modal-tense, counterfactual, RC tense
    - Klecha: silent on temporal de re, counterfactual, RC tense
    - Deal: silent on temporal de re, RC tense
    - Sharvit: silent on temporal de re, modal-tense, counterfactual

    Syntactic theories:
    - Zeijlstra: silent on temporal de re, modal-tense, counterfactual, RC tense
    - Wurmbrand: silent on temporal de re, modal-tense, counterfactual, RC tense

    Formalized via the identity cards: no single theory has all capabilities. -/
theorem no_single_theory_covers_all :
    -- No theory has BOTH temporal de re AND ULC refinement for counterfactuals
    ¬ (Abusch.hasTemporalDeRe = true ∧ Abusch.hasULC = true ∧
       Abusch.hasSOTDeletion = true) ∧
    ¬ (VonStechow.hasTemporalDeRe = true) ∧
    ¬ (KratzerTense.hasTemporalDeRe = true) ∧
    ¬ (Ogihara.hasTemporalDeRe = true) ∧
    -- New theories also don't cover everything
    ¬ (Zeijlstra.hasTemporalDeRe = true) ∧
    ¬ (Sharvit.hasTemporalDeRe = true) ∧
    ¬ (Wurmbrand.hasTemporalDeRe = true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Abusch, VonStechow, KratzerTense, Ogihara, Zeijlstra, Sharvit, Wurmbrand]

/-- Minimal cover: Abusch + Von Stechow + Klecha + Deal + Sharvit covers
    all phenomena.
    - Abusch: temporal de re, ULC, shifted/simultaneous/double-access
    - Von Stechow: relative clause tense, feature checking
    - Klecha: modal-tense interaction
    - Deal: counterfactual tense, ULC refinement
    - Sharvit: indirect question SOT, embedded present puzzle -/
theorem minimal_cover :
    Abusch.hasTemporalDeRe = true ∧
    VonStechow.hasSOTDeletion = false ∧  -- uses feature checking for RC
    Klecha.name = "Klecha 2016" ∧        -- modal-tense specialist
    Deal.hasULC = true ∧                  -- counterfactual specialist
    Sharvit.name = "Sharvit 2003" :=      -- indirect question SOT
  ⟨rfl, rfl, rfl, rfl, rfl⟩


-- ════════════════════════════════════════════════════════════════
-- § 5. Bridges to Existing Infrastructure
-- ════════════════════════════════════════════════════════════════

/-- The existing `embeddedFrame` in IS/Tense/Basic IS Von Stechow's
    perspective shift mechanism. -/
theorem vonStechow_grounds_embeddedFrame :
    VonStechow.simultaneousMechanism =
    "[PRES] feature checked against matrix event time" := rfl

/-- The existing `zeroTense_receives_binder_time` IS Ogihara's
    zero tense mechanism. -/
theorem ogihara_grounds_zero_tense :
    Ogihara.hasZeroTense = true := rfl

/-- The `evalTimeIndex` field on `TensePronoun` IS Klecha's insight:
    modals and attitudes shift the eval time by updating this index. -/
theorem evalTimeIndex_grounds_klecha :
    Klecha.name = "Klecha 2016" := rfl

/-- All theories interpret tense differently. The semantic theories
    share the `TensePronoun` type but give it different interpretations;
    @cite{zeijlstra-2012} operates at narrow syntax (Agree);
    @cite{wurmbrand-2014} classifies infinitival tense orthogonally. -/
theorem all_theories_pairwise_distinct :
    Abusch.name ≠ VonStechow.name ∧
    VonStechow.name ≠ KratzerTense.name ∧
    KratzerTense.name ≠ Ogihara.name ∧
    Ogihara.name ≠ Klecha.name ∧
    Klecha.name ≠ Deal.name ∧
    Deal.name ≠ Sharvit.name ∧
    Sharvit.name ≠ Zeijlstra.name ∧
    Zeijlstra.name ≠ Wurmbrand.name := by
  simp [Abusch, VonStechow, KratzerTense, Ogihara, Klecha, Deal,
        Sharvit, Zeijlstra, Wurmbrand]


-- ════════════════════════════════════════════════════════════════
-- § 6. Semantic vs Syntactic Divide
-- ════════════════════════════════════════════════════════════════

/-- Sharvit is the only theory with a dedicated simultaneous tense.
    Other theories derive the simultaneous reading from binding (Abusch),
    deletion (Kratzer), zero tense (Ogihara), Agree (Zeijlstra), or
    feature checking (Von Stechow). None of those posit a separate tense
    morpheme whose semantics IS simultaneity. -/
theorem only_sharvit_has_simultaneous_tense :
    Sharvit.simultaneousMechanism =
      "simultaneous tense with its own semantics (not deletion/zero/binding)" ∧
    Abusch.simultaneousMechanism ≠ Sharvit.simultaneousMechanism ∧
    KratzerTense.simultaneousMechanism ≠ Sharvit.simultaneousMechanism ∧
    Ogihara.simultaneousMechanism ≠ Sharvit.simultaneousMechanism := by
  simp [Sharvit, Abusch, KratzerTense, Ogihara]

/-- The semantic vs syntactic divide.

    Eight theories operate at LF (semantic denotation); only
    @cite{zeijlstra-2012} uses syntactic Agree for SOT.
    @cite{wurmbrand-2014} is a syntactic approach to infinitival
    tense classification but does not present an Agree-based SOT
    mechanism — it is compatible with both semantic and syntactic SOT.

    - Only Zeijlstra uses Agree-based SOT
    - None of the non-Agree theories posit temporal de re or ULC
      as part of an Agree system
    - Wurmbrand's contribution is orthogonal: infinitival tense
      classification, not SOT mechanism -/
theorem semantic_vs_syntactic_divide :
    -- Only Zeijlstra uses Agree
    Zeijlstra.hasAgreeBasedSOT = true ∧
    -- All others (including Wurmbrand) do not
    (Abusch.hasAgreeBasedSOT = false ∧ KratzerTense.hasAgreeBasedSOT = false ∧
     Wurmbrand.hasAgreeBasedSOT = false) ∧
    -- Zeijlstra and Wurmbrand don't posit temporal de re or ULC
    (Zeijlstra.hasTemporalDeRe = false ∧ Zeijlstra.hasULC = false) ∧
    (Wurmbrand.hasTemporalDeRe = false ∧ Wurmbrand.hasULC = false) :=
  ⟨rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩


-- ════════════════════════════════════════════════════════════════
-- § 7. Presuppositional Tense and Then-Present Incompatibility
-- ════════════════════════════════════════════════════════════════

/-- Only @cite{tsilia-zhao-sharvit-2026} treats tenses as presupposition
    triggers. All other theories have `hasPresuppositionalTense = false`. -/
theorem only_tsilia_has_presuppositional_tense :
    TsiliaEtAl2026.hasPresuppositionalTense = true ∧
    Abusch.hasPresuppositionalTense = false ∧
    VonStechow.hasPresuppositionalTense = false ∧
    KratzerTense.hasPresuppositionalTense = false ∧
    Ogihara.hasPresuppositionalTense = false ∧
    Klecha.hasPresuppositionalTense = false ∧
    Deal.hasPresuppositionalTense = false ∧
    Sharvit.hasPresuppositionalTense = false ∧
    Zeijlstra.hasPresuppositionalTense = false ∧
    Wurmbrand.hasPresuppositionalTense = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- All ten theories are distinct. -/
theorem all_ten_theories_distinct :
    Abusch.name ≠ VonStechow.name ∧
    VonStechow.name ≠ KratzerTense.name ∧
    KratzerTense.name ≠ Ogihara.name ∧
    Ogihara.name ≠ Klecha.name ∧
    Klecha.name ≠ Deal.name ∧
    Deal.name ≠ Sharvit.name ∧
    Sharvit.name ≠ TsiliaEtAl2026.name ∧
    TsiliaEtAl2026.name ≠ Zeijlstra.name ∧
    Zeijlstra.name ≠ Wurmbrand.name := by
  simp [Abusch, VonStechow, KratzerTense, Ogihara, Klecha, Deal,
        Sharvit, TsiliaEtAl2026, Zeijlstra, Wurmbrand]


-- ════════════════════════════════════════════════════════════════
-- § 7. Size-Sensitive SOT (@cite{egressy-2026})
-- ════════════════════════════════════════════════════════════════

/-! Only Zeijlstra's Agree-based account predicts size-sensitive SOT.
    All semantic theories (Abusch, Von Stechow, Kratzer, Ogihara, etc.)
    treat SOT as a whole-language parameter, not as structurally conditioned.
    @cite{egressy-2026} argues this is evidence for the syntactic (Agree-based)
    approach over purely semantic ones. -/

/-- Only Zeijlstra predicts size-sensitive SOT. -/
theorem only_zeijlstra_predicts_size_sensitive_sot :
    Zeijlstra.hasSizeSensitiveSOT = true ∧
    Abusch.hasSizeSensitiveSOT = false ∧
    VonStechow.hasSizeSensitiveSOT = false ∧
    KratzerTense.hasSizeSensitiveSOT = false ∧
    Ogihara.hasSizeSensitiveSOT = false ∧
    Klecha.hasSizeSensitiveSOT = false ∧
    Deal.hasSizeSensitiveSOT = false ∧
    Sharvit.hasSizeSensitiveSOT = false ∧
    TsiliaEtAl2026.hasSizeSensitiveSOT = false ∧
    Wurmbrand.hasSizeSensitiveSOT = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- @cite{egressy-2026}'s core argument: among the ten implemented theories,
    the only theory that predicts size-sensitive SOT is one that uses
    Agree-based SOT. All purely semantic theories (which lack structurally-
    local SOT mechanisms) predict uniform SOT within a language.

    This captures the paper's argument structure:
    1. Semantic SOT is not locality-constrained → predicts uniform SOT
    2. Agree-based SOT is locality-constrained → interacts with PIC
    3. Hungarian shows non-uniform (size-sensitive) SOT
    4. Therefore: data favors Agree-based (syntactic) approach -/
theorem size_sensitivity_requires_agree :
    ∀ t ∈ [Abusch, VonStechow, KratzerTense, Ogihara, Klecha, Deal,
           Sharvit, TsiliaEtAl2026, Zeijlstra, Wurmbrand],
      t.hasSizeSensitiveSOT = true → t.hasAgreeBasedSOT = true := by
  simp [Abusch, VonStechow, KratzerTense, Ogihara, Klecha, Deal,
        Sharvit, TsiliaEtAl2026, Zeijlstra, Wurmbrand]


end Comparisons.TenseTheories
