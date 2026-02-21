import Linglib.Core.InformationStructure
import Linglib.Theories.Semantics.Questions.QParticleLayer

/-!
# Turkish Question Particle Fragment

Turkish polar question particle *mI* (with vowel-harmony allomorphs
mı/mi/mu/mü). Following Turk, Hirsch & İnce (2026), *mI* heads PolP
and bears focus (Σ_F). Its UPOS category is `PART`, which is
crucial for category-match alternative computation (Fox & Katzir 2011):
modals are `AUX`, so category match excludes them from mI's alternatives.

## References

- Turk, E., Hirsch, A. & İnce, A. (2026). Constraining Alternatives
  in Turkish Polar Questions.
- Fox, D. & Katzir, R. (2011). On the characterization of alternatives.
-/

namespace Fragments.Turkish.QuestionParticles

open Semantics.Questions

/-- Turkish question particle entry. -/
structure TurkishQParticle where
  /-- Citation form -/
  form : String
  /-- Vowel-harmony allomorphs -/
  allomorphs : List String
  /-- UPOS category (particle) -/
  cat : UD.UPOS
  /-- Position in the left periphery -/
  layer : QParticleLayer
  /-- Semantic contribution: identity on propositions (Σ) -/
  isIdentity : Bool
  deriving Repr

/-- Turkish *mI*: polarity head with identity semantics.
    Heads PolP, bears focus (Σ_F). Category `PART` restricts
    alternatives to {Σ, NEG} under category match, excluding
    `AUX`-tagged modals. -/
def mi : TurkishQParticle where
  form := "mI"
  allomorphs := ["mı", "mi", "mu", "mü"]
  cat := .PART
  layer := .polP
  isIdentity := true

/-- *mI* is a particle. -/
theorem mi_is_part : mi.cat = .PART := rfl

/-- *mI* resides in PolP. -/
theorem mi_is_polP : mi.layer = .polP := rfl

end Fragments.Turkish.QuestionParticles
