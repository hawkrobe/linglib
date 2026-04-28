import Linglib.Phenomena.ScalarImplicatures.Embedded.Basic
import Linglib.Phenomena.ScalarImplicatures.Basic
import Linglib.Phenomena.ScalarImplicatures.Studies.GeurtsPouscoulous2009

/-!
# Geurts 2010 — *Quantity Implicatures* @cite{geurts-2010}

The textbook successor to @cite{geurts-pouscoulous-2009}. Geurts 2010
(Cambridge UP) consolidates the Standard-Recipe / competence-based
neo-Gricean account whose §8 sketch in GP 2009 this file extends. The
DE-blocking / UE-allowing core pattern documented in
`Phenomena.ScalarImplicatures.Basic.someAllBlocking` and refined into
the four-experiment program of GP 2009 anchors the textbook's Ch. 2–3.

## Connection to GP 2009

`empirical_pattern_documented` records the qualitative DE-blocks /
UE-allows pattern that the textbook's §3.2 takes as the empirical
explanandum. `gp2009_data_anchors_pattern` shows the GP 2009
∅-condition data (93%/94% endorsement of the *some*→*not all*
inference) is the quantitative grounding.
-/

namespace Geurts2010

open Phenomena.ScalarImplicatures.Embedded.Simplified
open Phenomena.ScalarImplicatures
open Phenomena.ScalarImplicatures.Studies.GeurtsPouscoulous2009

/-- The empirical DE-blocking / UE-allowing pattern that grounds the
textbook's neo-Gricean account. The simplified LU model predicts the
opposite; the full @cite{potts-etal-2016} model derives the correct
pattern via lexical uncertainty. -/
theorem empirical_pattern_documented :
    someAllBlocking.implicatureInDE = false ∧
    someAllBlocking.implicatureInUE = true := by
  decide

/-- The GP 2009 ∅-condition (unembedded *some*) endorsement rates
anchor the textbook's UE-pattern claim quantitatively: 93% (Exp 1a,
n=30) and 94% (Exp 1b, n=31) endorse the *some*→*not all* inference. -/
theorem gp2009_data_anchors_pattern :
    lookupRate exp1aResults .simple = 93 ∧
    lookupRate exp1bResults .simple = 94 := by decide

end Geurts2010
