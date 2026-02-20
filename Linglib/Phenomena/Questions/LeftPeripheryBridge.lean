import Linglib.Theories.Semantics.Questions.LeftPeriphery
import Linglib.Phenomena.Questions.Embedding
import Linglib.Phenomena.Questions.Typology
import Linglib.Phenomena.Questions.TypologyBridge

/-!
# Bridge: Left Periphery Theory -> Embedding/Typology Data

Connects the left-peripheral selection class theory from
`Theories.Semantics.Questions.LeftPeriphery` to the empirical embedding
data in `Phenomena.Questions.Embedding` and cross-linguistic typology
data in `Phenomena.Questions.Typology`.

Sections F and G from the original LeftPeriphery module: per-datum
verification against embedding judgments, shiftiness predictions, and
cross-linguistic Q-particle predictions.

## References

- Dayal, V. (2025). The Interrogative Left Periphery.
- McCloskey, J. (2006). Questions and questioning in a local English.
-/

namespace Phenomena.Questions.LeftPeripheryBridge

open Semantics.Questions.LeftPeriphery
open Phenomena.Questions.Embedding
open Phenomena.Questions.Typology
open Phenomena.Questions.TypologyBridge

-- ============================================================================
-- F. Verification against empirical data
-- ============================================================================

/-- Classify each empirical datum from Phenomena.Questions.Embedding. -/
def classifyVerb : String → SelectionClass
  | "investigate" => .rogativeCP
  | "depend on"   => .rogativeCP
  | "wonder"      => .rogativePerspP
  | "ask"         => .rogativeSAP
  | "know"        => .responsive
  | "believe"     => .uninterrogative
  | _             => .uninterrogative

/-- The theory correctly predicts all embedding judgments from the data. -/
theorem theory_predicts_embedding :
    ∀ d ∈ allEmbeddingData,
      allowsEmbedding (classifyVerb d.verb) Semantics.Questions.LeftPeriphery.EmbedType.subordination false false = d.subordination ∧
      allowsEmbedding (classifyVerb d.verb) Semantics.Questions.LeftPeriphery.EmbedType.quasiSubordination false false = d.quasiSubordination ∧
      allowsEmbedding (classifyVerb d.verb) Semantics.Questions.LeftPeriphery.EmbedType.quotation false false = d.quotation := by
  intro d hd
  simp only [allEmbeddingData, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

/-- Shiftiness predictions match McCloskey's data for remember (responsive). -/
theorem shiftiness_predicted :
    allowsQuasiSub .responsive remember_bare.negated remember_bare.questioned
      = remember_bare.quasiSubOk ∧
    allowsQuasiSub .responsive remember_negated.negated remember_negated.questioned
      = remember_negated.quasiSubOk ∧
    allowsQuasiSub .responsive remember_questioned.negated remember_questioned.questioned
      = remember_questioned.quasiSubOk := by
  simp [allowsQuasiSub, perspPConsistent, effectiveKnowledge, entailsKnowledge,
        remember_bare, remember_negated, remember_questioned]

-- ============================================================================
-- G. Cross-linguistic predictions
-- ============================================================================

/-- Classify Hindi-Urdu verbs from the cross-linguistic shiftiness data. -/
def classifyCrossLingVerb : String → SelectionClass
  | "ja:n-na: ca:h-na: (want to know)" => .rogativePerspP
  | "ja:n-na: (know)" => .responsive
  | _ => .responsive

/-- Hindi-Urdu shiftiness follows the same derivation as English:
    responsive predicates reject quasi-sub in bare form, allow under
    negation/questioning. The theory predicts ALL cross-linguistic data. -/
theorem cross_linguistic_shiftiness_predicted :
    ∀ d ∈ allCrossLingShiftinessData,
      allowsQuasiSub (classifyCrossLingVerb d.verb) d.negated d.questioned
        = d.quasiSubOk := by
  intro d hd
  simp [allCrossLingShiftinessData] at hd
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp [allowsQuasiSub, perspPConsistent, effectiveKnowledge, entailsKnowledge,
          classifyCrossLingVerb,
          hindi_urdu_want_to_know, hindi_urdu_know_bare,
          hindi_urdu_know_negated, hindi_urdu_know_questioned]

/-- Q-particle embedding follows from which left-peripheral layer they occupy.
    CP-layer particles appear in subordination; PerspP and SAP particles do not. -/
theorem particle_layer_predicts_embedding :
    ∀ d ∈ allQParticleData,
      (d.layer = .cp → d.inSubordinated = true) ∧
      (d.layer = .perspP → d.inSubordinated = false) ∧
      (d.layer = .sap → d.inQuasiSub = false) := by
  intro d hd
  simp [allQParticleData] at hd
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp [japanese_ka, hindi_urdu_kya, japanese_kke, english_quick]

-- ============================================================================
-- H. Cross-layer agreement (moved from LeftPeriphery sections H-I)
-- ============================================================================

open Fragments.English.Predicates.Verbal

/-- The structurally derived classification matches the manually-assigned
    string-based classification for all verbs in the embedding data. -/
theorem derived_class_matches_manual :
    deriveSelectionClass Fragments.English.Predicates.Verbal.know = classifyVerb "know" ∧
    deriveSelectionClass Fragments.English.Predicates.Verbal.wonder = classifyVerb "wonder" ∧
    deriveSelectionClass Fragments.English.Predicates.Verbal.ask = classifyVerb "ask" ∧
    deriveSelectionClass Fragments.English.Predicates.Verbal.investigate = classifyVerb "investigate" ∧
    deriveSelectionClass Fragments.English.Predicates.Verbal.believe = classifyVerb "believe" := by
  decide

/-- String-based classification matches field-based derivation. -/
theorem classifyVerb_agrees_with_selectionClass :
    classifyVerb "know" = fieldSelectionClass Fragments.English.Predicates.Verbal.know ∧
    classifyVerb "wonder" = fieldSelectionClass Fragments.English.Predicates.Verbal.wonder ∧
    classifyVerb "ask" = fieldSelectionClass Fragments.English.Predicates.Verbal.ask ∧
    classifyVerb "investigate" = fieldSelectionClass Fragments.English.Predicates.Verbal.investigate ∧
    classifyVerb "depend on" = fieldSelectionClass Fragments.English.Predicates.Verbal.depend_on ∧
    classifyVerb "believe" = fieldSelectionClass Fragments.English.Predicates.Verbal.believe := by native_decide

end Phenomena.Questions.LeftPeripheryBridge
