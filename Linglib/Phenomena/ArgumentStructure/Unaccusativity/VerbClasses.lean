import Linglib.Core.Lexical.VerbClass
import Linglib.Core.Lexical.DiathesisAlternation
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Levin verb classes and unaccusativity
@cite{levin-1993} @cite{levin-hovav-1995} @cite{storment-2026}

How @cite{levin-1993}'s lexical-semantic verb classes (§37–§51) align
with the syntactic unaccusativity diagnostic. This file is the
formalizer's synthesis: @cite{storment-2026} doesn't run a Levin-class
analysis, and Levin 1993 predates the QI diagnostic. The interaction
is what we're after.

The general pattern: most Levin classes align with the predicted
unaccusativity status. Inherently directed motion (§51.1), existence
(§47), appearance (§48), and emission classes (§43) predict and obtain
unaccusative status; manner of motion (§51.3), body-internal motion
(§49), and contact (§18.1) predict and obtain unergative/transitive.
The interesting fault line is manner-of-speaking (§37.3): the class
predicts unergative, but @cite{storment-2026}'s QI diagnostic
classifies the verbs as unaccusative — and the class is internally
split (`whisper` unaccusative, `speak` unergative on QI).

The within-class split is the strongest evidence that Levin-class
membership alone cannot determine unaccusativity for §37.3 verbs.

## Files
- `LevinClass.PredictsUnaccusative` lives in `Core/Lexical/VerbClass.lean`.
- `LevinClass.participatesIn .causativeInchoative` lives in
  `Core/Lexical/DiathesisAlternation.lean`.
-/

namespace Phenomena.ArgumentStructure.Unaccusativity.VerbClasses

open Fragments.English.Predicates.Verbal
open Core.Verbs

/-! ## §1. Aligned classes

Verbs whose Fragment annotation matches the Levin-class prediction.
Collapsed from per-verb theorems into a quantified table. Each row:
verb's Levin class, the class's prediction, the empirical annotation. -/

/-- Verbs where the Levin class predicts unaccusative AND the Fragment
    annotation agrees. -/
def alignedUnaccusatives : List VerbEntry := [arrive, exist, appear, glow, buzz, bleed, rust]

/-- Verbs where the Levin class predicts non-unaccusative AND the
    Fragment annotation agrees. -/
def alignedNonUnaccusatives : List VerbEntry := [run, fidget, kick]

theorem aligned_unaccusatives_levin_agrees :
    ∀ v ∈ alignedUnaccusatives,
      ∃ c, v.levinClass = some c ∧ LevinClass.PredictsUnaccusative c ∧ v.unaccusative = true := by
  intro v hv
  fin_cases hv <;>
    refine ⟨_, rfl, ?_, rfl⟩ <;> decide

theorem aligned_nonunaccusatives_levin_agrees :
    ∀ v ∈ alignedNonUnaccusatives,
      ∃ c, v.levinClass = some c ∧ ¬ LevinClass.PredictsUnaccusative c ∧ v.unaccusative = false := by
  intro v hv
  fin_cases hv <;>
    refine ⟨_, rfl, ?_, rfl⟩ <;> decide

/-! ## §2. The MoS divergence

Manner-of-speaking (§37.3) is the cleanest fault line. The class
predicts non-unaccusative (it's an agentive activity class), but the
Fragment annotates the verbs as unaccusative on the basis of
@cite{storment-2026}'s QI diagnostic. -/

/-- Levin's `mannerOfSpeaking` does not predict unaccusative status. -/
theorem mannerOfSpeaking_predicts_nonunaccusative :
    ¬ LevinClass.PredictsUnaccusative .mannerOfSpeaking := by decide

/-- Yet `whisper` is annotated unaccusative — divergence. -/
theorem whisper_diverges_from_levin :
    whisper.levinClass = some .mannerOfSpeaking ∧ whisper.unaccusative = true :=
  ⟨rfl, rfl⟩

/-! ## §3. The within-class split

Both `whisper` and `speak` are Levin §37.3 (mannerOfSpeaking), yet they
diverge on the QI diagnostic. Levin-class membership cannot be the
deciding factor for this class. -/

theorem mos_within_class_split :
    whisper.levinClass = speak.levinClass ∧
    whisper.unaccusative = true ∧
    speak.unaccusative = false :=
  ⟨rfl, rfl, rfl⟩

/-! ## §4. Causative-inchoative classes

For verbs in classes participating in the causative-inchoative
alternation (§45), the *class* predicts unaccusative for the inchoative
variant, but the Fragment may store the transitive (causative) variant.
The alternation is the bridge between the stored form and the predicted
unaccusativity of the inchoative. -/

theorem break_class_supports_causativeInchoative :
    break_.levinClass = some .break_ ∧
    LevinClass.break_.participatesIn .causativeInchoative = true ∧
    LevinClass.PredictsUnaccusative .break_ ∧
    break_.unaccusative = false :=  -- Fragment stores the transitive form
  ⟨rfl, rfl, by decide, rfl⟩

end Phenomena.ArgumentStructure.Unaccusativity.VerbClasses
