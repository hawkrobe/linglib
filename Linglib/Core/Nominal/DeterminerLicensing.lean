import Linglib.Core.Nominal.Determiner
import Linglib.Core.Nominal.Description

/-!
# Determiner licensing

`Determiner.licenses`: does a declared `List Determiner.Entry` have the surface
form needed to realize a given `NominalKind` constructor? Kept separate from
`Determiner.lean` so that marking-only Fragments do not transitively import the
Frame-parameterized `NominalKind` substrate.
-/

open Core.Logic.Intensional (Frame)
open Core.Nominal (NominalKind)

namespace Determiner

/-- Does the declared determiner set have the surface form needed to realize the
given `NominalKind` constructor? Bare nominals are always licensed; unique and
anaphoric definites need a determiner exponing the corresponding presupposition
type (`MarksPresup`); indefinite/demonstrative/possessive need a determiner of
that kind. -/
def licenses {F : Frame} (ds : List Entry) : NominalKind F → Prop
  | .bare _           => True
  | .indefinite _     => ∃ e ∈ ds, e.IsIndefiniteArticle
  | .unique _ _       => MarksPresup ds .uniqueness
  | .anaphoric _ _    => MarksPresup ds .familiarity
  | .demonstrative .. => ∃ e ∈ ds, e.IsDemonstrative
  | .possessive ..    => ∃ e ∈ ds, e.IsPossessive

instance {F : Frame} (ds : List Entry) (k : NominalKind F) : Decidable (licenses ds k) := by
  cases k <;> unfold licenses <;> infer_instance

end Determiner
