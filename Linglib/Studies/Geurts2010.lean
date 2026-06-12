import Linglib.Studies.GeurtsPouscoulous2009

/-!
# Geurts 2010 — *Quantity Implicatures* [geurts-2010]

The textbook successor to [geurts-pouscoulous-2009]. Geurts 2010
(Cambridge UP) consolidates the Standard-Recipe / competence-based
neo-Gricean account whose §8 sketch in GP 2009 this file extends. The
core empirical pattern anchoring the textbook's Ch. 2–3 — scalar
implicatures blocked in downward-entailing contexts but available in
upward-entailing ones — is the explanandum of GP 2009's four-experiment
program; the [potts-etal-2016] LU model derives the correct pattern
(see `Studies/PottsEtAl2016`).

## Connection to GP 2009

`gp2009_data_anchors_pattern` shows the GP 2009 ∅-condition data
(93%/94% endorsement of the *some*→*not all* inference) is the
quantitative grounding for the textbook's UE-pattern claim.
-/

namespace Geurts2010

open GeurtsPouscoulous2009

/-- The GP 2009 ∅-condition (unembedded *some*) endorsement rates
anchor the textbook's UE-pattern claim quantitatively: 93% (Exp 1a,
n=30) and 94% (Exp 1b, n=31) endorse the *some*→*not all* inference. -/
theorem gp2009_data_anchors_pattern :
    lookupRate exp1aResults .simple = 93 ∧
    lookupRate exp1bResults .simple = 94 := by decide

end Geurts2010
