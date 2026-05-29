import Linglib.Typology.Pronoun.Basic
import Linglib.Semantics.Reference.Nominal
import Linglib.Semantics.Presupposition.PhiFeatures
import Linglib.Core.Logic.Intensional.Variables
import Linglib.Core.Assignment

/-!
# The denotation of a pronoun

Gives the `Pronoun.Entry` lexical record a meaning, as a `NominalDenot`: the
selector is the project-canonical variable denotation `interpPronoun`
(`g ↦ g i`), so the pronoun-as-object and the bare assignment-indexed
variable are the same individual *by construction* — not via a bridge
theorem. The intrinsic presupposition is the φ-feature presupposition read
off the entry's person/number/gender via the @cite{sauerland-2003}-style
cells in `Semantics.Presupposition.PhiFeatures`.

This follows @cite{buring-2012}'s survey: the assignment lookup (his (14)), the
feature presuppositions (his (49)/(50)), and the absence-of-features treatment
of unmarked values. The same `interpPronoun` selector serves bound, anaphoric,
and deictic uses (his §2.1.1); binding is the external β-operator
(`Semantics.Reference.Binding`).

## Main definitions

* `Pronoun.Entry.phiPresup` — the conjoined φ-feature presupposition of an
  entry (absent or featurally-uncovered values contribute `PrProp.top`).
* `Pronoun.Entry.denote` — the pronoun's `NominalDenot` (static case).

## Implementation notes

Number values beyond singular/plural (dual, trial, …) and the non-sex-based
surface genders contribute the vacuous cell here; the principled route is the
`Features.Number.Category.fromUD`/`Features.Gender.Features.fromSurfaceGender`
bridges plus `PhiFeatures.toPair`, deferred until a study needs them.
-/

set_option autoImplicit false

namespace Pronoun

open Semantics.Presupposition (PrProp)
open Semantics.Presupposition.PhiFeatures
open Semantics.Reference (NominalDenot)
open Core (Assignment)
open Core.Logic.Intensional (Frame)
open Core.Logic.Intensional.Variables (interpPronoun)

/-- The conjoined φ-feature presupposition of a pronoun entry, over an entity
domain `E`. The model supplies the entity-level predicates the cells need
(`speaker`/`addressee` for person, `isFemale`/`isInanimate` for gender;
number atomicity comes from the `PartialOrder`). A feature that is absent —
or present but outside the cells' coverage — contributes `PrProp.top`. -/
def Entry.phiPresup {E : Type*} [PartialOrder E] (e : Entry)
    (speaker addressee : E) (isFemale isInanimate : E → Prop) : PrProp E :=
  PrProp.and
    (match e.person with
      | some .first  => firstSem speaker
      | some .second => secondSem speaker addressee
      | some .third  => thirdSem
      | _            => PrProp.top)
    (PrProp.and
      (match e.number with
        | some .Sing => sgSem E
        | some .Plur => plSem E
        | _          => PrProp.top)
      (match e.gender with
        | some .feminine  => femSem isFemale
        | some .neuter    => neutSem isInanimate
        | some .masculine => mascSem
        | _               => PrProp.top))

/-- A pronoun's denotation as a `NominalDenot`: the selector is the canonical
variable denotation `interpPronoun i` (always defined under a total
assignment), and the intrinsic presupposition is the φ-feature presupposition
imposed on the resolved referent `g i`. The static case; world is trivial. -/
def Entry.denote {F : Frame} [PartialOrder F.Entity] (e : Entry) (i : ℕ)
    (speaker addressee : F.Entity) (isFemale isInanimate : F.Entity → Prop) :
    NominalDenot (Assignment F.Entity) PUnit F.Entity where
  presup := fun g _ => (e.phiPresup speaker addressee isFemale isInanimate).presup (g i)
  selector := fun g _ => some (interpPronoun (F := F) i g)

/-! ### Featural definedness tests -/

/-- A 3rd-person plural feminine entry (Spanish *ellas*), used to exercise
the φ-feature presupposition. -/
private def ellas : Entry :=
  { form := "ellas", person := some .third, number := some .Plur,
    gender := some .feminine }

/-- Negative: a feminine pronoun is undefined of a non-feminine referent. -/
example {E : Type*} [PartialOrder E] (speaker addressee : E)
    (isFemale isInanimate : E → Prop) (x : E) (h : ¬ isFemale x) :
    ¬ (ellas.phiPresup speaker addressee isFemale isInanimate).presup x :=
  fun hp => h hp.2.2

/-- Positive: under a feminine referent, the full pronoun denotation is
defined (its presupposition holds). -/
example {F : Frame} [PartialOrder F.Entity] (g : Assignment F.Entity) (i : ℕ)
    (speaker addressee : F.Entity) (isFemale isInanimate : F.Entity → Prop)
    (scope : F.Entity → Assignment F.Entity → PUnit → Prop)
    (hFem : isFemale (g i)) :
    ((ellas.denote i speaker addressee isFemale isInanimate).toPrProp scope g).presup ⟨⟩ := by
  refine ⟨⟨trivial, trivial, hFem⟩, ?_⟩
  rfl

end Pronoun
