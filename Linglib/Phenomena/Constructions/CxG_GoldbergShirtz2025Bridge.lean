import Linglib.Theories.Syntax.ConstructionGrammar.Studies.GoldbergShirtz2025
import Linglib.Phenomena.Constructions.Studies.GoldbergShirtz2025

/-!
# Bridge: PAL Construction Theory → GoldbergShirtz2025 Phenomena

Connects the PAL construction theoretical analysis in
`ConstructionGrammar.Studies.GoldbergShirtz2025` to the empirical data in
`Phenomena.Constructions.Studies.GoldbergShirtz2025`.

Claims 3 and 4 reference empirical study results (effect sizes from
Studies 2/3, cross-linguistic attestation data) and so belong here
rather than in the pure theory file.

## Reference

Goldberg, A. E., & Shirtz, S. (2025). PAL constructions: How phrases can act
like words. To appear in Language.
-/

namespace ConstructionGrammar.Studies.GoldbergShirtz2025.Bridge

/-- **Claim 3**: PALs produce rhetorical effects (wit, sarcasm).

Supported by Studies 2 (wittiness) and 3 (sarcasm):
PALs are judged wittier and more sarcastic than paraphrases.

We record this as the empirical observation that effect sizes are positive
and significant across both studies. -/
def claim_rhetorical_effects : Prop :=
  _root_.Phenomena.Constructions.Studies.GoldbergShirtz2025.study2.beta > 0 ∧
  _root_.Phenomena.Constructions.Studies.GoldbergShirtz2025.study3.beta > 0

/-- Claim 3 holds: β > 0 in both Studies 2 and 3. -/
theorem claim_rhetorical_effects_holds : claim_rhetorical_effects := by
  unfold claim_rhetorical_effects
  constructor <;> native_decide

/-- **Claim 4**: PAL-like constructions exist in unrelated language families.

Attested in Germanic (German, Dutch, Afrikaans), Turkic (Turkish),
Semitic (Hebrew), and Romance (Brazilian Portuguese). -/
def claim_crosslinguistic : Prop :=
  (_root_.Phenomena.Constructions.Studies.GoldbergShirtz2025.crossLinguisticData.map
    (·.family)).eraseDups.length ≥ 3

/-- Claim 4 holds: 4 distinct families attested. -/
theorem claim_crosslinguistic_holds : claim_crosslinguistic := by
  unfold claim_crosslinguistic
  native_decide

end ConstructionGrammar.Studies.GoldbergShirtz2025.Bridge
