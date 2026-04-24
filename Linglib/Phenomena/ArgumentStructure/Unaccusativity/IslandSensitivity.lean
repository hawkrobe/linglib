import Linglib.Phenomena.Islands.MannerOfSpeaking
import Linglib.Phenomena.Islands.Studies.Ross1967
import Linglib.Phenomena.ArgumentStructure.Unaccusativity.Data
import Linglib.Theories.Interfaces.SyntaxSemantics.VerbSmuggling
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Unaccusativity and extraction-island sensitivity
@cite{lu-pan-degen-2025} @cite{storment-2026}

How the unaccusativity classification of manner-of-speaking verbs
interacts with their participation in extraction-island effects. This
file is the formalizer's synthesis: @cite{storment-2026} doesn't
discuss MoS islands, and @cite{lu-pan-degen-2025} doesn't run a
syntactic unaccusativity diagnostic. Each paper studies a different
property of the same verb class.

## The two operations on MoS verbs

@cite{lu-pan-degen-2025}: wh-extraction *from within* the complement
of an MoS verb is degraded — `*Who did Mary whisper that John kissed __?`
The constraint is **discourse-sourced** (ameliorated by prosodic focus,
unrelated to verb-frame frequency, replicable with `say+adverb` framing
that has no structural change).

@cite{storment-2026}: A-movement *of the entire VP* containing the
quote operator is grammatical — `"I'm tired," whispered Mary`. The
operation is VP-smuggling to Spec,VoiceP, licensed by the verb's
non-phase Voice (anticausative).

## Compatibility, not contradiction

The two observations are consistent. They concern different operations:
- Sub-extraction (@cite{lu-pan-degen-2025}): wh-movement out of the
  complement, blocked by a discourse-sourced backgroundedness island
- VP-smuggling (@cite{storment-2026}): A-movement of the whole VP,
  licensed by syntactic Voice properties

The asymmetry confirms both analyses simultaneously: MoS islands are
discourse-sourced (so they don't block syntactic VP-smuggling that
produces QI). If MoS islands were syntactic (PIC, subjacency), they
would be predicted to block QI as well — they don't.
-/

namespace Phenomena.ArgumentStructure.Unaccusativity.IslandSensitivity

open Phenomena.Islands.MannerOfSpeaking (mosIslandSources)
open Fragments.English.Predicates.Verbal
open Core.Verbs

/-! ## §1. The two empirical observations

`mosIslandSources` is from @cite{lu-pan-degen-2025} (`Phenomena/Islands/
MannerOfSpeaking.lean`); `derivedQI` is the syntactic prediction from
@cite{storment-2026} (`Theories/Interfaces/SyntaxSemantics/VerbSmuggling.lean`).
For every MoS verb the Fragment lists as unaccusative, both observations
hold simultaneously. -/

/-- The MoS verbs that pass QI (per @cite{storment-2026}) and
    participate in MoS islands (per @cite{lu-pan-degen-2025}). -/
def mosUnaccusatives : List VerbEntry :=
  [whisper, murmur, shout, cry, scream, mumble, mutter,
   shriek, yell, groan, grumble, hiss, sigh, whimper, snap]

/-- @cite{lu-pan-degen-2025}'s finding: MoS islands are discourse-
    sourced. -/
theorem mos_islands_discourse_sourced : mosIslandSources = [.discourse] := rfl

/-- @cite{storment-2026}'s prediction: every MoS unaccusative licenses
    QI. Quantified version of the per-verb theorems. -/
theorem mos_unaccusatives_license_qi :
    ∀ v ∈ mosUnaccusatives, v.toVerbCore.derivedQI = true := by
  intro v hv; fin_cases hv <;> rfl

/-! ## §2. Compatibility theorem

Stating both observations together: each MoS verb in the list is
extraction-island-sensitive (sub-extraction blocked) AND smuggling-
licensed (whole-VP A-movement OK). Different operations, different
sources, both true. -/

theorem mos_extraction_smuggling_asymmetry :
    mosIslandSources = [.discourse] ∧
    ∀ v ∈ mosUnaccusatives, v.toVerbCore.derivedQI = true :=
  ⟨rfl, mos_unaccusatives_license_qi⟩

/-! ## §3. The diagnostic value

Were MoS islands syntactically sourced (e.g., PIC, subjacency), they
would be predicted to block VP-smuggling as well — A-movement of an
opaque domain is no easier than wh-movement out of one. The fact that
QI is grammatical is *evidence* that MoS islands are not syntactic,
independent of @cite{lu-pan-degen-2025}'s direct experimental tests.
The two literatures converge on the same conclusion. -/

end Phenomena.ArgumentStructure.Unaccusativity.IslandSensitivity
