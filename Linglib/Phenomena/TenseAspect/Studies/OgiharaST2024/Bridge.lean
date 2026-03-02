import Linglib.Phenomena.TenseAspect.Studies.OgiharaST2024.Data
import Linglib.Theories.Semantics.Tense.TemporalConnectives.OST
import Linglib.Theories.Semantics.Tense.TemporalConnectives.EventBridge
import Linglib.Fragments.English.TemporalExpressions
import Linglib.Fragments.Japanese.TemporalConnectives

/-!
# @cite{ogihara-steinert-threlkeld-2024} — Bridge
@cite{ogihara-steinert-threlkeld-2024}

Connects the empirical veridicality data to:

1. **Fragment entries**: `TemporalExprEntry.complementVeridical` matches data
2. **Theory predictions**: O&ST's `after_veridical` / `before_nonveridical` theorems
   derive the Fragment properties from the quantificational structure
3. **Cross-level comparison**: O&ST (Level 3) projects to Anscombe (Level 1) via
   `eventDenotation`, with provable divergence on overlapping runtimes
4. **Logical properties**: Antisymmetry, transitivity, and their failures verified
   on concrete scenarios matching B&C (2003) §1

## Derivation Pipeline

```
Theory: OST.after_veridical (∃∃ structure entails complement)
    ↓ derives
Fragment: after_.complementVeridical = true
    ↓ matches
Data: after_veridical.complementEntailed = true
```

The same pipeline for *before*, in the non-veridical direction:

```
Theory: OST.before_nonveridical (∀ over complement is vacuously true)
    ↓ derives
Fragment: before_.complementVeridical = false
    ↓ matches
Data: before_nonveridical.complementEntailed = false
```
-/

namespace Phenomena.TenseAspect.Studies.OgiharaST2024.Bridge

open Semantics.Tense.TemporalConnectives
open Semantics.Events
open Fragments.English.TemporalExpressions

-- ════════════════════════════════════════════════════════════════
-- § 1: Fragment ↔ Data Agreement
-- ════════════════════════════════════════════════════════════════

/-- The Fragment entry for *after* matches the empirical datum:
    both record complement veridicality as true. -/
theorem after_fragment_matches_datum :
    after_.complementVeridical = after_veridical.complementEntailed := rfl

/-- The Fragment entry for *before* matches the empirical datum:
    both record complement veridicality as false. -/
theorem before_fragment_matches_datum :
    before_.complementVeridical = before_nonveridical.complementEntailed := rfl

/-- The veridicality asymmetry is reflected in the Fragment entries. -/
theorem fragment_veridicality_asymmetry :
    after_.complementVeridical = true ∧ before_.complementVeridical = false :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 2: Theory → Fragment Derivation
-- ════════════════════════════════════════════════════════════════

/-- O&ST's theory derives *after*'s veridicality from the double-existential
    quantificational structure: ∃e₁∃e₂[P(e₁) ∧ Q(e₂) ∧...] entails ∃e₂, Q(e₂).

    This is not a stipulation in the Fragment — it follows from the semantics. -/
theorem after_veridicality_derived :
    ∀ (P Q : EvPred ℤ), OST.after P Q → ∃ e : Ev ℤ, Q e :=
  fun P Q h => OST.after_veridical P Q h

/-- O&ST's theory derives *before*'s non-veridicality from the universal
    quantification over the complement: ∃e₁[P(e₁) ∧ ∀e₂[Q(e₂) →...]] is
    vacuously true when Q has no witnesses.

    Concretely: any P-event with an empty Q yields `before(P, Q)`. -/
theorem before_nonveridicality_derived :
    ∃ (P Q : EvPred ℤ), OST.before P Q ∧ ¬∃ e : Ev ℤ, Q e :=
  OST.before_nonveridical

-- ════════════════════════════════════════════════════════════════
-- § 3: Concrete Scenario Verification
-- ════════════════════════════════════════════════════════════════

/-- Scenario: "He left₁ after she arrived₀" with punctual events.
    - leaving event at time 1
    - arriving event at time 0
    O&ST predicts: after(leave, arrive) holds (τ(arrive) ≺ τ(leave)). -/
theorem scenario_after_punctual :
    let leave : Ev ℤ := ⟨⟨1, 1, le_refl _⟩, .action⟩
    let arrive : Ev ℤ := ⟨⟨0, 0, le_refl _⟩, .action⟩
    OST.after (· = leave) (· = arrive) := by
  refine ⟨⟨⟨1, 1, le_refl _⟩, .action⟩, ⟨⟨0, 0, le_refl _⟩, .action⟩, rfl, rfl, ?_⟩
  simp [Core.Time.Interval.precedes, Ev.τ]

/-- Scenario: "He left₁ before she arrived₃" with punctual events.
    - leaving event at time 1
    - arriving event at time 3
    O&ST predicts: before(leave, arrive) holds (τ(leave) ≺ τ(arrive)). -/
theorem scenario_before_punctual :
    let leave : Ev ℤ := ⟨⟨1, 1, le_refl _⟩, .action⟩
    let arrive : Ev ℤ := ⟨⟨3, 3, le_refl _⟩, .action⟩
    OST.before (· = leave) (· = arrive) := by
  refine ⟨⟨⟨1, 1, le_refl _⟩, .action⟩, rfl, ?_⟩
  intro e₂ rfl
  simp [Core.Time.Interval.precedes, Ev.τ]

/-- Scenario: "The bomb exploded₅ before anyone defused it" (nobody defused it).
    O&ST predicts: before(explode, defuse) holds vacuously (no defuse-events). -/
theorem scenario_before_counterfactual :
    let explode : Ev ℤ := ⟨⟨5, 5, le_refl _⟩, .action⟩
    OST.before (· = explode) (fun _ => False) := by
  exact ⟨⟨⟨5, 5, le_refl _⟩, .action⟩, rfl, fun _ h => h.elim⟩

-- ════════════════════════════════════════════════════════════════
-- § 4: Cross-Level Projection Verification
-- ════════════════════════════════════════════════════════════════

/-- The punctual after-scenario projects correctly through eventDenotation:
    O&ST.after implies Anscombe.after on the projected interval sets. -/
theorem scenario_after_projects :
    let leave : Ev ℤ := ⟨⟨1, 1, le_refl _⟩, .action⟩
    let arrive : Ev ℤ := ⟨⟨0, 0, le_refl _⟩, .action⟩
    Anscombe.after (eventDenotation (· = leave)) (eventDenotation (· = arrive)) :=
  OST.after_implies_anscombe _ _ scenario_after_punctual

/-- The punctual before-scenario projects correctly through eventDenotation. -/
theorem scenario_before_projects :
    let leave : Ev ℤ := ⟨⟨1, 1, le_refl _⟩, .action⟩
    let arrive : Ev ℤ := ⟨⟨3, 3, le_refl _⟩, .action⟩
    Anscombe.before (eventDenotation (· = leave)) (eventDenotation (· = arrive)) :=
  OST.before_implies_anscombe _ _ scenario_before_punctual

-- ════════════════════════════════════════════════════════════════
-- § 5: Logical Properties (B&C 2003, §1)
-- ════════════════════════════════════════════════════════════════

/-! The logical properties of *before* and *after* noted by B&C follow
    directly from the quantificational structure. We verify each on
    concrete interval scenarios over ℤ, matching the B&C diagrams. -/

private def i_cleo_b : Core.Time.Interval ℤ := ⟨1, 5, by omega⟩
private def i_david_b : Core.Time.Interval ℤ := ⟨8, 12, by omega⟩

/-- *Before* is antisymmetric on non-overlapping statives: if A before B,
    then ¬(B before A). (B&C 2003, exx. 3-4)

    Scenario: Cleo [1,5], David [8,12]. Cleo before David holds;
    David before Cleo does not.

    The ∀-quantifier in Anscombe.before enforces this: if all of B
    follows some point in A, then no point in B precedes all of A. -/
theorem before_antisymmetric_scenario :
    Anscombe.before (stativeDenotation i_cleo_b) (stativeDenotation i_david_b) ∧
    ¬Anscombe.before (stativeDenotation i_david_b) (stativeDenotation i_cleo_b) := by
  simp only [Anscombe.before, timeTrace_stativeDenotation, Core.Time.Interval.contains,
    i_cleo_b, i_david_b, Set.mem_setOf_eq]
  constructor
  · exact ⟨1, ⟨le_refl _, by omega⟩, fun t' ⟨h, _⟩ => by omega⟩
  · intro ⟨t, ⟨ht1, ht2⟩, hall⟩
    have := hall 1 ⟨le_refl _, by omega⟩; omega

private def i_cleo_a : Core.Time.Interval ℤ := ⟨1, 8, by omega⟩
private def i_david_a : Core.Time.Interval ℤ := ⟨5, 12, by omega⟩

/-- *After* is NOT antisymmetric: overlapping intervals allow both
    after(A,B) and after(B,A). (B&C 2003, exx. 5-7, diagram 7)

    Scenario: Cleo [1,8], David [5,12]. Both Cleo-after-David and
    David-after-Cleo hold because ∃ requires only one witness. -/
theorem after_not_antisymmetric_scenario :
    Anscombe.after (stativeDenotation i_cleo_a) (stativeDenotation i_david_a) ∧
    Anscombe.after (stativeDenotation i_david_a) (stativeDenotation i_cleo_a) := by
  simp only [Anscombe.after, timeTrace_stativeDenotation, Core.Time.Interval.contains,
    i_cleo_a, i_david_a, Set.mem_setOf_eq]
  exact ⟨⟨8, ⟨by omega, le_refl _⟩, 5, ⟨le_refl _, by omega⟩, by omega⟩,
         ⟨12, ⟨by omega, le_refl _⟩, 1, ⟨le_refl _, by omega⟩, by omega⟩⟩

/-- Helper intervals for the transitivity scenarios. Using top-level defs
    so `simp` can unfold interval fields for `omega`. -/
private def i_delores_t : Core.Time.Interval ℤ := ⟨1, 3, by omega⟩
private def i_ginger_t : Core.Time.Interval ℤ := ⟨6, 8, by omega⟩
private def i_fred_t : Core.Time.Interval ℤ := ⟨11, 13, by omega⟩

/-- *Before* is transitive: A before B ∧ B before C → A before C.
    (B&C 2003, exx. 12-14)

    Scenario: Delores [1,3], Ginger [6,8], Fred [11,13]. -/
theorem before_transitive_scenario :
    Anscombe.before (stativeDenotation i_delores_t) (stativeDenotation i_ginger_t) ∧
    Anscombe.before (stativeDenotation i_ginger_t) (stativeDenotation i_fred_t) ∧
    Anscombe.before (stativeDenotation i_delores_t) (stativeDenotation i_fred_t) := by
  simp only [Anscombe.before, timeTrace_stativeDenotation, Core.Time.Interval.contains,
    i_delores_t, i_ginger_t, i_fred_t, Set.mem_setOf_eq]
  exact ⟨⟨1, ⟨le_refl _, by omega⟩, fun t' ⟨h, _⟩ => by omega⟩,
         ⟨6, ⟨le_refl _, by omega⟩, fun t' ⟨h, _⟩ => by omega⟩,
         ⟨1, ⟨le_refl _, by omega⟩, fun t' ⟨h, _⟩ => by omega⟩⟩

private def i_fred_a : Core.Time.Interval ℤ := ⟨1, 3, by omega⟩
private def i_ginger_a : Core.Time.Interval ℤ := ⟨2, 5, by omega⟩
private def i_delores_a : Core.Time.Interval ℤ := ⟨4, 7, by omega⟩

/-- *After* is NOT transitive: overlapping intervals allow
    after(A,B) ∧ after(B,C) ∧ ¬after(A,C). (B&C 2003, exx. 8-11)

    Scenario: Fred [1,3], Ginger [2,5], Delores [4,7].
    Fred after Ginger: t=3, t'=2. ✓
    Ginger after Delores: t=5, t'=4. ✓
    Fred after Delores: need t ∈ [1,3], t' ∈ [4,7], t' < t — impossible
    since max(Fred)=3 < 4=min(Delores). ✗ -/
theorem after_not_transitive_scenario :
    Anscombe.after (stativeDenotation i_fred_a) (stativeDenotation i_ginger_a) ∧
    Anscombe.after (stativeDenotation i_ginger_a) (stativeDenotation i_delores_a) ∧
    ¬Anscombe.after (stativeDenotation i_fred_a) (stativeDenotation i_delores_a) := by
  simp only [Anscombe.after, timeTrace_stativeDenotation, Core.Time.Interval.contains,
    i_fred_a, i_ginger_a, i_delores_a, Set.mem_setOf_eq]
  refine ⟨⟨3, ⟨by omega, by omega⟩, 2, ⟨by omega, by omega⟩, by omega⟩,
          ⟨5, ⟨by omega, by omega⟩, 4, ⟨by omega, by omega⟩, by omega⟩, ?_⟩
  rintro ⟨t, ⟨h1, h2⟩, t', ⟨h3, h4⟩, hlt⟩; omega

-- ════════════════════════════════════════════════════════════════
-- § 6: Logical Properties — General Theorems
-- ════════════════════════════════════════════════════════════════

/-- *Before* is antisymmetric in general: `before(A,B) → ¬before(B,A)`.

    From the ∀ in Anscombe's *before*: if ∃t ∈ A, ∀t' ∈ B, t < t',
    then for any s ∈ B we get t < s. But before(B,A) gives ∀ t ∈ A, s < t,
    so s < t and t < s — contradiction.

    Note: no non-emptiness assumption needed. -/
theorem before_antisymmetric_general {Time : Type*} [LinearOrder Time]
    (A B : SentDenotation Time) :
    Anscombe.before A B → ¬Anscombe.before B A := by
  intro ⟨t, ht, hall_B⟩ ⟨s, hs, hall_A⟩
  exact lt_asymm (hall_A t ht) (hall_B s hs)

/-- *Before* is transitive in general: `before(A,B) → before(B,C) → before(A,C)`.

    From `before(A,B)`: ∃t ∈ A, ∀t' ∈ B, t < t'.
    From `before(B,C)`: ∃s ∈ B, ∀s' ∈ C, s < s'.
    Then t < s (from the first, since s ∈ B), and for any u ∈ C, s < u
    (from the second). So t < u by transitivity of <. Witness: t ∈ A.

    Note: no non-emptiness assumption needed — `s ∈ timeTrace B` is
    provided by the second hypothesis. -/
theorem before_transitive_general {Time : Type*} [LinearOrder Time]
    (A B C : SentDenotation Time) :
    Anscombe.before A B → Anscombe.before B C → Anscombe.before A C := by
  intro ⟨t, ht, hall_B⟩ ⟨s, hs, hall_C⟩
  exact ⟨t, ht, fun u hu => lt_trans (hall_B s hs) (hall_C u hu)⟩

-- ════════════════════════════════════════════════════════════════
-- § 7: NPI Licensing Bridge
-- ════════════════════════════════════════════════════════════════

/-- The NPI datum matches the Fragment entry: *before* licenses NPIs. -/
theorem npi_datum_matches_fragment :
    before_.licensesNPI = before_licenses_npis.holds := rfl

-- ════════════════════════════════════════════════════════════════
-- § 8: Cross-Linguistic Bridge (Japanese)
-- ════════════════════════════════════════════════════════════════

open Fragments.Japanese.TemporalConnectives in
/-- The Japanese Fragment entry for *mae* agrees with the cross-linguistic
    datum: both record that *mae* supports the non-veridicality analysis. -/
theorem japanese_mae_matches_datum :
    mae.complementVeridical = false ∧
    japanese_mae.supportsNonveridicality = true :=
  ⟨rfl, rfl⟩

open Fragments.Japanese.TemporalConnectives in
/-- The Japanese Fragment entry for *ato* agrees with the cross-linguistic
    datum: *ato* is veridical and does not support non-veridicality. -/
theorem japanese_ato_matches_datum :
    ato.complementVeridical = true ∧
    japanese_ato.supportsNonveridicality = false :=
  ⟨rfl, rfl⟩

end Phenomena.TenseAspect.Studies.OgiharaST2024.Bridge
