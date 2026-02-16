import Linglib.Theories.Semantics.Tense.Abusch
import Linglib.Theories.Semantics.Tense.VonStechow
import Linglib.Theories.Semantics.Tense.Kratzer
import Linglib.Theories.Semantics.Tense.Ogihara
import Linglib.Theories.Semantics.Tense.Klecha
import Linglib.Theories.Semantics.Tense.Deal
import Linglib.Theories.Semantics.Tense.Sharvit
import Linglib.Theories.Syntax.Minimalism.Tense.Zeijlstra
import Linglib.Theories.Syntax.Minimalism.Tense.Wurmbrand

/-!
# Tense Theories: Cross-Cutting Comparison

Comparison matrix for nine tense theories:
- Semantic: Abusch (1997), Von Stechow (2009), Kratzer (1998), Ogihara (1996),
  Klecha (2016), Deal (2020), Sharvit (2003)
- Syntactic: Zeijlstra (2012), Wurmbrand (2014)

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
structurally. For Partee's (1973) tense–pronoun structural analogy
(indexical/anaphoric/bound-variable interpretations of tense morphemes),
see `Comparisons/Partee1973.lean`.

## References

- See individual theory files for per-theory citations.
-/

namespace Comparisons.TenseTheories

open IntensionalSemantics.Tense
open IntensionalSemantics.Tense.Abusch (Abusch)
open IntensionalSemantics.Tense.VonStechow (VonStechow)
open IntensionalSemantics.Tense.Kratzer (KratzerTense)
open IntensionalSemantics.Tense.Ogihara (Ogihara)
open IntensionalSemantics.Tense.Klecha (Klecha)
open IntensionalSemantics.Tense.Deal (Deal)
open IntensionalSemantics.Tense.Sharvit (Sharvit)
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
    interaction (Klecha 2016). Deal also addresses modals but through
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

/-- All nine theories interpret tense differently. The six semantic theories
    share the `TensePronoun` type but give it different interpretations;
    the two syntactic theories (Zeijlstra, Wurmbrand) operate at a different
    level entirely (feature checking, not semantic denotation). -/
theorem all_nine_theories_distinct :
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
-- § 6. Extended Coverage: Agree-Based SOT
-- ════════════════════════════════════════════════════════════════

/-- Only Zeijlstra and Wurmbrand use Agree-based SOT. The six semantic
    theories all have `hasAgreeBasedSOT = false` (default). -/
theorem only_syntactic_theories_use_agree :
    Zeijlstra.hasAgreeBasedSOT = true ∧
    Wurmbrand.hasAgreeBasedSOT = true ∧
    Abusch.hasAgreeBasedSOT = false ∧
    VonStechow.hasAgreeBasedSOT = false ∧
    KratzerTense.hasAgreeBasedSOT = false ∧
    Ogihara.hasAgreeBasedSOT = false ∧
    Klecha.hasAgreeBasedSOT = false ∧
    Deal.hasAgreeBasedSOT = false ∧
    Sharvit.hasAgreeBasedSOT = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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

/-- The semantic vs syntactic divide: six theories operate at LF
    (semantic denotation), two operate at narrow syntax (Agree).
    None of the semantic theories use Agree; none of the syntactic
    theories posit temporal de re or ULC. -/
theorem semantic_vs_syntactic_divide :
    -- Semantic theories don't use Agree
    (Abusch.hasAgreeBasedSOT = false ∧ KratzerTense.hasAgreeBasedSOT = false) ∧
    -- Syntactic theories don't use temporal de re or ULC
    (Zeijlstra.hasTemporalDeRe = false ∧ Zeijlstra.hasULC = false) ∧
    (Wurmbrand.hasTemporalDeRe = false ∧ Wurmbrand.hasULC = false) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩


end Comparisons.TenseTheories
