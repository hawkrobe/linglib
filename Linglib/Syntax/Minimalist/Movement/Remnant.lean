/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject.Derivation
import Linglib.Syntax.Minimalist.SyntacticObject.Subterm

/-!
# Remnant movement

A constituent moves after part of it has moved out, so what fronts is a remnant carrying the
trace of what left it: [koopman-1997]'s predicate clefts in Vata and Nweh, where the VP fronts
after the verb has raised, the Gungbe and Kwa predicate doubling of [aboh-dyakonova-2009], the
constraints on predicate fronting [van-urk-2024] surveys, Toba Batak's VoiceP raising after the
goal and the subject have evacuated it ([cole-hermon-2008], `Studies/ColeHermon2008.lean`), and
Guébie's particle fronting after the verb has left the VP ([sande-clem-dabkowski-2026],
`Studies/SandeClemDabkowski2026.lean`). On a derivation
the notion is exact: step `i` fronts a remnant when its mover contains the trace the head of an
earlier mover left. Whether the evacuee's lower copy is pronounced inside the remnant, the verb
doubling of predicate clefts, is a matter of chain pronunciation, phonological for
[landau-2006] and syntactic for [koopman-1997] and [harizanov-gribanova-2017]; the carrier
pronounces no trace and does not decide it. Remnant movement is the converse of smuggling
(`Movement/Smuggling.lean`, [collins-2005]), in which the larger constituent moves with the
smaller one still inside it.

## Main definitions

* `Minimalist.SyntacticObject.Derivation.IsRemnantStep`

## Main results

* `Minimalist.SyntacticObject.Derivation.IsRemnantStep.append`: a remnant step of a derivation
  is one of every extension.

## References

* [koopman-1997]
* [aboh-dyakonova-2009]
* [van-urk-2024]
* [landau-2006]
* [harizanov-gribanova-2017]
* [collins-2005]
* [cole-hermon-2008]
* [sande-clem-dabkowski-2026]
-/

namespace Minimalist.SyntacticObject.Derivation

variable {d : Derivation} {steps : List Step} {i : Nat}

/-- Step `i` of `d` fronts a remnant: its mover contains the trace left by an earlier mover. -/
def IsRemnantStep (d : Derivation) (i : Nat) : Prop :=
  ∃ m ∈ d.steps[i]? >>= Step.mover?, ∃ x ∈ (d.take i).movedItems, contains m x.headTrace

instance (d : Derivation) (i : Nat) : Decidable (d.IsRemnantStep i) := by
  unfold IsRemnantStep; infer_instance

/-- A remnant step of a derivation is one of every extension. -/
theorem IsRemnantStep.append (h : d.IsRemnantStep i) : (d.append steps).IsRemnantStep i := by
  obtain ⟨m, hm, x, hx, hc⟩ := h
  have hi := lt_length_of_mem_mover? hm
  refine ⟨m, ?_, x, ?_, hc⟩
  · rwa [Derivation.append, List.getElem?_append_left hi]
  · rwa [take_append_of_le hi.le]

end Minimalist.SyntacticObject.Derivation
