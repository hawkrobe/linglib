import Linglib.Phenomena.Gradability.Imprecision.Studies.BeltramaSchwarz2024.Data
import Linglib.Core.SocialMeaning
import Linglib.Core.Roundness
import Linglib.Theories.Pragmatics.RSA.Core.CombinedUtility
import Linglib.Theories.Semantics.Lexical.Numeral.Precision
import Mathlib.Tactic.Linarith

/-!
# Beltrama & Schwarz (2024): RSA Bridge @cite{beltrama-schwarz-2024}

Connects Beltrama & Schwarz's experimental findings to the RSA framework
following Henderson & McCready (2019), who add a persona component to the
speaker's utility function. B&S endorse this architecture in §6 as a
promising route for formally capturing their findings.

## Model structure

The speaker's utility combines two components (Henderson & McCready 2019,
as discussed in B&S §6):
1. **Informational**: how accurately does the utterance describe the world?
2. **Persona**: how consistent is the utterance with the speaker's persona?

These combine via `RSA.CombinedUtility.combined`:

    U(u; w, persona) = (1−λ) · U_info(u, w) + λ · U_persona(persona, u)

The pragmatic listener inverts this model: given the utterance AND the
speaker's persona (provided by the experimental vignette), the listener
infers the likely world state. A nerdy speaker's use of "$200" is
interpreted more exactly; a chill speaker's use is interpreted more
loosely.

## Key results

1. **Nerdy speakers increase exactness** (`nerdy_favors_exact`):
   follows from persona match + `combined_mono_B`.
2. **Chill speakers increase tolerance** (`chill_favors_approximate`):
   follows from persona match + `combined_mono_B`.
3. **Stimuli use round numerals** (`stimuli_are_round`):
   all items use round dollar amounts, connecting to `Core.Roundness`.
4. **Dual function of roundness** (`roundness_dual_function`):
   roundness drives both truth-conditional tolerance and the availability
   of persona-dependent interpretation.
5. **Structural parallel** (`persona_utility_is_combined`):
   the model instantiates the same `combined` framework as
   Yoon et al. (2020) for politeness.

## References

* Beltrama, A. & Schwarz, F. (2024). Social stereotypes affect
  imprecision resolution across different tasks.
  *Semantics & Pragmatics* 17(10): 1–34.
* Henderson, R. & McCready, E. (2019). How dogwhistles work.
  *Proceedings of the 22nd Amsterdam Colloquium*.
* Burnett, H. (2017). Sociolinguistic interaction and identity
  construction: A formal approach.
* Yoon, E. J. et al. (2020). Polite Speech Emerges From Competing
  Social Goals.
-/

namespace RSA.Implementations.BeltramaSchwarz2024

open Phenomena.Gradability.Imprecision.Studies.BeltramaSchwarz2024
open Core.SocialMeaning
open RSA.CombinedUtility

-- ============================================================================
-- Persona utility (Henderson & McCready 2019, as cited in B&S §6)
-- ============================================================================

/-- Persona match: how consistent is a given precision level with the
    speaker's persona.

    This operationalizes U_persona from Henderson & McCready (2019),
    as endorsed by B&S in §6. A nerdy speaker's persona is reinforced
    by exact language; a chill speaker's persona is reinforced by casual/
    approximate language.

    The `isExact` parameter represents whether the listener resolves
    the round numeral exactly (true) or approximately (false). -/
def personaMatch : PersonaCondition → Bool → ℚ
  | .nerdy,     true  => 1   -- nerdy + exact = consistent
  | .nerdy,     false => 0   -- nerdy + approximate = inconsistent
  | .chill,     false => 1   -- chill + approximate = consistent
  | .chill,     true  => 0   -- chill + exact = inconsistent
  | .noPersona, _     => 0   -- no persona = no social utility

-- ============================================================================
-- Core predictions (from combined utility monotonicity)
-- ============================================================================

/-- A nerdy speaker with positive persona weight favors exact interpretation:
    combined utility is higher when the round numeral is interpreted exactly.

    Matches Exp 1: Nerdy β = 0.77 on COVERED (exact interpretation). -/
theorem nerdy_favors_exact (wId : ℚ) (hw : 0 < wId) (uInfo : ℚ) :
    combined wId uInfo (personaMatch .nerdy false) <
    combined wId uInfo (personaMatch .nerdy true) := by
  apply combined_mono_B _ hw
  simp only [personaMatch]
  norm_num

/-- A chill speaker with positive persona weight favors approximate
    interpretation: combined utility is higher when the round numeral
    is interpreted loosely.

    Matches Exp 1: Chill β = −0.67 on COVERED (= less exact). -/
theorem chill_favors_approximate (wId : ℚ) (hw : 0 < wId) (uInfo : ℚ) :
    combined wId uInfo (personaMatch .chill true) <
    combined wId uInfo (personaMatch .chill false) := by
  apply combined_mono_B _ hw
  simp only [personaMatch]
  norm_num

/-- Persona match is symmetric: swapping persona swaps the preferred
    interpretation. This is the structural source of the bi-directional
    persona effect in Experiment 1. -/
theorem persona_symmetry :
    personaMatch .nerdy true = personaMatch .chill false ∧
    personaMatch .nerdy false = personaMatch .chill true := by
  constructor <;> rfl

/-- No persona = no social utility component (baseline condition).
    Matches the No Persona condition serving as regression intercept. -/
theorem noPersona_neutral (isExact : Bool) :
    personaMatch .noPersona isExact = 0 := by
  cases isExact <;> rfl

-- ============================================================================
-- Stimuli grounding (connects to Core.Roundness)
-- ============================================================================

/-- The stimulus numerals are round: high roundness grade.
    All critical items use round dollar amounts like $200 (§3.1). -/
theorem stimuli_are_round :
    Core.Roundness.roundnessGrade exampleStatedAmount = .high := by native_decide

/-- Roundness score of $200 = 6 (maximum on the k-ness scale). -/
theorem stimulus_roundness_score :
    Core.Roundness.roundnessScore exampleStatedAmount = 6 := by native_decide

open Semantics.Lexical.Numeral.Precision in
/-- The stimulus numeral $200 infers approximate precision mode,
    which is why imprecise readings are available at all (§3.1). -/
theorem stimulus_permits_imprecision :
    inferPrecisionMode exampleStatedAmount = .approximate := by native_decide

-- ============================================================================
-- Dual function of roundness
-- ============================================================================

open Semantics.Lexical.Numeral.Precision in
/-- Roundness has a dual function: the same `Core.Roundness` infrastructure
    determines both truth-conditional tolerance (via `inferPrecisionMode`)
    and the availability of persona-driven interpretation effects.

    * $200 (stated amount, round) → approximate mode → imprecise reading
      available → persona can modulate resolution
    * $193 (actual screen value, non-round) → exact mode → no imprecise
      reading → persona effect would not arise

    The two functions derive from the same underlying property (roundness
    score) but operate on different dimensions of meaning. -/
theorem roundness_dual_function :
    -- Truth-conditional: $200 → approximate, $193 → exact
    inferPrecisionMode 200 = .approximate ∧
    inferPrecisionMode 193 = .exact ∧
    -- Roundness scores differ
    Core.Roundness.roundnessScore 200 > Core.Roundness.roundnessScore 193 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ============================================================================
-- Structural parallel: B&S ↔ Yoon et al. ↔ Henderson & McCready
-- ============================================================================

/-- The persona utility model instantiates `CombinedUtility.combined`.

    The endpoint properties apply: at λ=0, only informational utility
    matters (no persona effect — the baseline condition); at λ=1, only
    persona matters (pure stereotype-driven interpretation).

    This is the same architecture as Yoon et al. (2020), where U_B is
    social utility (face-saving), and Henderson & McCready (2019), where
    U_B is persona projection. -/
theorem persona_utility_is_combined (uInfo uPersona : ℚ) :
    combined 0 uInfo uPersona = uInfo ∧
    combined 1 uInfo uPersona = uPersona :=
  combined_endpoints uInfo uPersona

/-- When persona weight is interior (0 < λ < 1), combined utility
    increases in BOTH informational utility AND persona match. This is
    the formal basis for the trade-off: a listener reasoning about a
    nerdy speaker must weigh informational evidence for imprecision
    against the persona-driven expectation of exactness.

    The same trade-off structure drives Yoon et al.'s politeness model
    (informativity vs. face-saving). -/
theorem persona_informativity_tradeoff
    (wId : ℚ) (hw1 : wId < 1)
    (uInfo₁ uInfo₂ uPersona : ℚ) (hInfo : uInfo₁ < uInfo₂) :
    combined wId uInfo₁ uPersona < combined wId uInfo₂ uPersona :=
  combined_mono_A wId hw1 uInfo₁ uInfo₂ uPersona hInfo

-- ============================================================================
-- Task asymmetry: formal characterization
-- ============================================================================

/-- The key empirical asymmetry: both personae affect Exp 1 (inference),
    but only Chill affects Exp 2 (judgment).

    B&S's explanation (§7): in the TVJ task, participants judge truth
    against a VISIBLE referent. A nerdy speaker is expected to be exact,
    but this expectation does not make a true-but-imprecise statement
    FALSE. A chill speaker, by contrast, makes the imprecise reading
    more salient, shifting the truth judgment toward RIGHT. -/
theorem task_asymmetry :
    -- Exp 1: both personae significant
    exp1_chill.significant = true ∧ exp1_nerdy.significant = true ∧
    -- Exp 2: only Chill significant
    exp2_chill.significant = true ∧ exp2_nerdy.significant = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Effect directions are opposite for the two personae in Exp 1:
    Chill β < 0 (less exact) while Nerdy β > 0 (more exact). -/
theorem exp1_opposite_directions :
    exp1_chill.beta < 0 ∧ exp1_nerdy.beta > 0 := by
  refine ⟨?_, ?_⟩ <;> native_decide

-- ============================================================================
-- Persona ↔ social dimension mapping
-- ============================================================================

open Core.SocialMeaning in
/-- Nerdy maps to the Competence dimension; Chill to Warmth.
    This connects to Fiske et al.'s (2007) Stereotype Content Model,
    as cited in B&S §2. -/
theorem persona_aligns_with_scm :
    personaDimension .nerdy = some .competence ∧
    personaDimension .chill = some .warmth := by
  exact ⟨rfl, rfl⟩

end RSA.Implementations.BeltramaSchwarz2024
