import Linglib.Theories.Pragmatics.Bias
import Linglib.Theories.Semantics.Modality.BiasedPQ

/-!
# Romero (2024): Biased Polar Questions
@cite{romero-2024}

## Cross-construction unification: the bias predicate is shared

@cite{romero-2024}'s HiNQ ("Isn't Jane coming?") *mandatorily* conveys
the speaker's prior bias for p — the same `contradictsPriorBelief`
condition @cite{napoli-nespor-1976} identified for Italian *non₂*
comparatives. The licensing *predicate* is shared even though the two
constructions differ in illocutionary force (declarative vs interrogative);
the bridge is at the condition-level, not at the form-level.

This study file is the home for that cross-construction bridge. It was
formerly inlined into `Theories/Pragmatics/Bias.lean` §7, but the
`BiasedPQ` import (with its CommonGround/InformationStructure/Discourse
transitive stack) dominated the build cost of `Bias.lean`. Hosting the
bridge here keeps `Bias.lean` lean and concentrates Romero-2024-specific
content under its primary phenomenon (polar question bias).

An earlier draft had a `toRomeroForm : BiasLicensingProfile → Option (PQForm × OriginalBias)`
function that mapped declarative profiles to interrogative HiNQ forms;
that was a category error masquerading as a structural map. The
predicate-level bridge below is the right granularity.
-/

namespace Phenomena.Questions.Studies.Romero2024

open Pragmatics.Bias
open Semantics.Modality.BiasedPQ

/-- HiNQ's original-bias filter requires speaker bias for p. The
    licensed bias profile's `contradictsPriorBelief` axis is the
    @cite{napoli-nespor-1976} analogue of exactly that bias condition. -/
theorem licensed_contradictsPriorBelief_matches_hiNQ_bias :
    licensedProfile.licenses → originalBiasOK .HiNQ .forP = true := by
  intro _
  rfl

end Phenomena.Questions.Studies.Romero2024
