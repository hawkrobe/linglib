import Linglib.Theories.Semantics.Attitudes.ContextQuantification
import Linglib.Theories.Semantics.Reference.ShiftedIndexicals
import Linglib.Theories.Semantics.Reference.Kaplan
import Linglib.Theories.Semantics.Reference.Monsters
import Linglib.Theories.Semantics.Reference.PersonFeatures

/-!
# Schlenker (2003): A Plea for Monsters
@cite{schlenker-2003}

End-to-end verification of @cite{schlenker-2003}'s core argument:

1. Kaplan's thesis (no monsters) holds for English: "I" always refers
   to the actual speaker, even under attitude verbs
2. Amharic violates the thesis: "I" shifts to the attitude holder
3. Context quantification (`ctxBox`) captures both patterns:
   - With world-only meaning → reduces to standard `boxAt` (Fixity holds)
   - With agent-reading meaning → strictly more expressive (Fixity fails)
4. Person features as presuppositions derive logophoric pronouns

## Derivation Chain

```
Core.Context.Tower (ContextTower, push, origin, innermost)
    ↓
Core.Context.Shifts (attitudeShift)
    ↓
Theories.Semantics.Reference.Kaplan (pronI_access, origin-reading)
    ↓
Theories.Semantics.Reference.ShiftedIndexicals (amharic_pronI, local-reading)
    ↓
Theories.Semantics.Attitudes.ContextQuantification (ctxBox, Fixity)
    ↓
Theories.Semantics.Reference.PersonFeatures (logophoric pronouns)
    ↓
This file: concrete end-to-end verification
```
-/

namespace Schlenker2003

open Core.Context
open Semantics.Attitudes.ContextQuantification
open Semantics.Attitudes.Doxastic (AccessRel boxAt)
open Semantics.Reference.ShiftedIndexicals (amharic_pronI)
open Semantics.Reference.Kaplan (pronI_access)

-- ════════════════════════════════════════════════════════════════
-- § Concrete Setup
-- ════════════════════════════════════════════════════════════════

inductive Person | alice | bob
  deriving DecidableEq, Repr

inductive World | w0 | w1
  deriving DecidableEq, Repr

abbrev Ctx := KContext World Person Unit Unit

/-- Speech-act context: Alice speaking to Bob at world w0. -/
def speechCtx : Ctx :=
  { agent := .alice, addressee := .bob, world := .w0,
    time := (), position := () }

def rootT : ContextTower Ctx := ContextTower.root speechCtx

/-- Bob's doxastic accessibility: both worlds are compatible with
    what Bob believes. -/
def bobBel : AccessRel World Person
  | .bob, _, _ => True
  | .alice, _, w' => w' = .w0

instance : ∀ a w w', Decidable (bobBel a w w') := by
  intro a w w'; cases a <;> simp [bobBel] <;> infer_instance

/-- Tower after attitude shift: "Bob said that ..." pushes Bob as
    agent and w1 as the attitude world. -/
def shiftedT : ContextTower Ctx :=
  rootT.push (attitudeShift .bob .w1)

-- ════════════════════════════════════════════════════════════════
-- § English vs Amharic "I" Under Attitude Shift
-- ════════════════════════════════════════════════════════════════

/-- English "I" = Alice (actual speaker), even under Bob's attitude verb. -/
theorem english_I_is_speaker :
    pronI_access.resolve shiftedT = .alice := rfl

/-- Amharic "I" = Bob (attitude holder), shifted by the attitude verb. -/
theorem amharic_I_is_holder :
    amharic_pronI.resolve shiftedT = .bob := rfl

/-- English and Amharic "I" diverge under the same attitude shift. -/
theorem indexicals_diverge :
    pronI_access.resolve shiftedT ≠ amharic_pronI.resolve shiftedT := by
  decide

-- ════════════════════════════════════════════════════════════════
-- § Context Quantification: English vs Amharic Truth Conditions
-- ════════════════════════════════════════════════════════════════

/-- Happiness predicate: Alice is happy in w0 only; Bob is happy in both. -/
def isHappy : Person → World → Prop
  | .alice, .w0 => True
  | .alice, .w1 => False
  | .bob, _ => True

instance : ∀ p w, Decidable (isHappy p w) := by
  intro p w; cases p <;> cases w <;> simp [isHappy] <;> infer_instance

/-- English: "Bob said that I am happy" = "Bob said that Alice is happy."
    The meaning is world-only (Alice is fixed by origin-reading "I"),
    so context quantification reduces to standard world quantification. -/
theorem english_reduces_to_boxAt :
    ctxBox bobBel .bob (fun c => isHappy .alice c.world) rootT .w0 [.w0, .w1] =
    boxAt bobBel .bob .w0 [.w0, .w1] (isHappy .alice) :=
  ctxBox_world_only bobBel .bob (isHappy .alice) rootT .w0 [.w0, .w1]

/-- English version is false: Alice is NOT happy in all of Bob's
    belief worlds (she's unhappy in w1). -/
theorem english_result :
    ¬ ctxBox bobBel .bob (fun c => isHappy .alice c.world)
      rootT .w0 [.w0, .w1] := by
  decide

/-- Amharic: "Bob said that I am happy" = "Bob said that Bob is happy."
    The meaning reads the agent from the shifted context (Bob),
    so ctxBox does NOT reduce to boxAt. -/
theorem amharic_result :
    ctxBox bobBel .bob (fun c => isHappy c.agent c.world)
      rootT .w0 [.w0, .w1] := by
  decide

/-- The English and Amharic versions have different truth values:
    English fails, Amharic holds. This is the formal content of
    @cite{schlenker-2003}'s argument that context quantification is
    strictly more expressive than world quantification. -/
theorem english_amharic_differ :
    ¬ ctxBox bobBel .bob (fun c => isHappy .alice c.world)
      rootT .w0 [.w0, .w1] ∧
    ctxBox bobBel .bob (fun c => isHappy c.agent c.world)
      rootT .w0 [.w0, .w1] :=
  ⟨english_result, amharic_result⟩

-- ════════════════════════════════════════════════════════════════
-- § Fixity Thesis
-- ════════════════════════════════════════════════════════════════

/-- World-only meanings satisfy Fixity (Claim 2): the truth value of
    "Alice is happy" is tower-independent. -/
theorem fixity_english :
    SatisfiesFixity (W := World) (E := Person) (P := Unit) (T := Unit)
      (fun _ w => isHappy .alice w) :=
  fixity_world_only (isHappy .alice)

-- ════════════════════════════════════════════════════════════════
-- § Context Quantification ↔ Shifted Indexicals Bridge
-- ════════════════════════════════════════════════════════════════

/-- The agent of the accessible context (from `ctxFromShift`) is exactly
    what Amharic "I" (`amharic_pronI`) resolves to. -/
theorem bridge_ctxFromShift_amharic :
    (ctxFromShift rootT .bob .w1).agent =
    amharic_pronI.resolve shiftedT := by
  native_decide

/-- English "I" gives the same result with or without the shift:
    both return Alice (the origin agent). -/
theorem bridge_english_invariant :
    pronI_access.resolve shiftedT =
    pronI_access.resolve rootT :=
  english_I_invariant rootT .bob .w1

-- ════════════════════════════════════════════════════════════════
-- § Person Features: Logophoric Pronouns
-- ════════════════════════════════════════════════════════════════

open Semantics.Reference.PersonFeatures

/-- Bob is logophoric under the attitude shift: he is +author(local)
    (agent of the embedded context) but −author* (not the actual
    speaker Alice). -/
theorem bob_is_logophoric :
    isLogophoric .bob shiftedT .local = true := by
  native_decide

/-- Alice (the speaker) is never logophoric: +author* blocks it. -/
theorem alice_not_logophoric :
    isLogophoric .alice shiftedT .local = false := by
  native_decide

end Schlenker2003
