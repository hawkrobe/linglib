import Linglib.Typology.Pronoun.Basic
import Linglib.Semantics.Reference.Nominal
import Linglib.Semantics.Presupposition.PhiFeatures
import Linglib.Core.Logic.Intensional.Variables
import Linglib.Core.Assignment
import Linglib.Semantics.Dynamic.Effects.HasFiberedLookup
import Linglib.Core.Nominal.Interpret

/-!
# The denotation of a pronoun

Gives the `PersonalPronoun` lexical record a meaning, as a `NominalDenot`: the
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

* `PersonalPronoun.phiPresup` — the conjoined φ-feature presupposition of an
  entry (absent or featurally-uncovered values contribute `PrProp.top`).
* `PersonalPronoun.denote` — the pronoun's `NominalDenot` (static case).

## Implementation notes

Number values beyond singular/plural (dual, trial, …) and the non-sex-based
surface genders contribute the vacuous cell here; the principled route is the
`Features.Number.Category.fromUD`/`Features.Gender.Features.fromSurfaceGender`
bridges plus `PhiFeatures.toPair`, deferred until a study needs them.
-/

set_option autoImplicit false

open Semantics.Presupposition (PrProp)
open Semantics.Presupposition.PhiFeatures
open Semantics.Reference (NominalDenot)
open Core (Assignment)
open Core.Logic.Intensional (Frame)
open Core.Logic.Intensional.Variables (interpPronoun DenotGS SitAssignment)

/-- The conjoined φ-feature presupposition of a pronoun entry, over an entity
domain `E`. The model supplies the entity-level predicates the cells need
(`speaker`/`addressee` for person, `isFemale`/`isInanimate` for gender;
number atomicity comes from the `PartialOrder`). A feature that is absent —
or present but outside the cells' coverage — contributes `PrProp.top`. -/
def PersonalPronoun.phiPresup {E : Type*} [PartialOrder E] (e : PersonalPronoun)
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
def PersonalPronoun.denote {F : Frame} [PartialOrder F.Entity] (e : PersonalPronoun) (i : ℕ)
    (speaker addressee : F.Entity) (isFemale isInanimate : F.Entity → Prop) :
    NominalDenot (Assignment F.Entity) PUnit F.Entity where
  presup := fun g _ => (e.phiPresup speaker addressee isFemale isInanimate).presup (g i)
  selector := fun g _ => some (interpPronoun (F := F) i g)

/-! ### Fusion seam with the dynamic lookup interface -/

/-- The pronoun's canonical variable selector `interpPronoun i` is exactly the
`M = Id` extensional-baseline instance of the dynamic-anaphora lookup interface
`HasFiberedLookup.iLookup` (`Semantics.Dynamic.Effects.HasFiberedLookup`,
`instAssignmentHasFiberedLookup`). So static reference and dynamic (`Set`/`PMF`)
anaphora already agree at the static fiber — modulo the `Option` partiality
layer `Entry.denote` adds. This discharges the first step of the functor-
parametric `NominalDenot` consolidation (`Nominal.lean`'s `Todo`): the remaining,
higher-blast-radius stage makes `selector` itself functor-valued and *be*
`iLookup`. -/
theorem interpPronoun_eq_iLookup {F : Frame} (i : ℕ) (g : Assignment F.Entity)
    (w : PUnit) :
    interpPronoun (F := F) i g
      = Semantics.Dynamic.Context.HasFiberedLookup.iLookup (M := Id) g i w :=
  rfl

/-! ### Featural definedness tests -/

/-- A 3rd-person plural feminine entry (Spanish *ellas*), used to exercise
the φ-feature presupposition. -/
private def ellas : PersonalPronoun :=
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
    (scope : F.Entity → PUnit → Prop)
    (hFem : isFemale (g i)) :
    ((ellas.denote i speaker addressee isFemale isInanimate).toPrProp scope g).presup ⟨⟩ := by
  refine ⟨⟨trivial, trivial, hFem⟩, ?_⟩
  rfl

/-! ### Pronouns are definite descriptions (@cite{elbourne-2005}, @cite{patel-grosz-grosz-2017})

The thesis that a pronoun *is* a (null-NP) definite description, and a
demonstrative pronoun is that description plus a D_deix layer, is made concrete
by routing pronoun denotation through `NominalKind`: a personal pronoun is the
`.anaphoric` (Schwarz strong-article) definite, a demonstrative pronoun is the
`.demonstrative` one — which the substrate already proves differ only by the
deixis presupposition filter (`interpret_demonstrative_eq_anaphoric`). -/

/-- A personal pronoun *is* a definite description: structurally the anaphoric
(Schwarz strong-article) definite over its restrictor `R` (the φ-feature NP) at
discourse index `i`. @cite{patel-grosz-grosz-2017}'s "pronoun = null NP + Ddet",
as a `NominalKind`. -/
def PersonalPronoun.toNominalKind {F : Frame} (_e : PersonalPronoun)
    (R : DenotGS F .et) (i : ℕ) : Core.Nominal.NominalKind F :=
  .anaphoric R i

/-- A demonstrative pronoun is the same definite description plus the D_deix
layer: `NominalKind.demonstrative` is `.anaphoric` with a deictic feature
(@cite{patel-grosz-grosz-2017}: DEM = PER + deixis). -/
def DemonstrativePronoun.toNominalKind {F : Frame} (p : DemonstrativePronoun)
    (R : DenotGS F .et) (sIdx i : ℕ) : Core.Nominal.NominalKind F :=
  .demonstrative R p.deictic sIdx i

/-- DEM = PER + deixis at the referential level: erasing the deixis layer
(`toPersonalPronoun`) leaves the same referent — the deictic feature is a
presupposition filter, not a selector (@cite{patel-grosz-grosz-2017} §4). -/
theorem DemonstrativePronoun.referent_eq_personal {F : Frame}
    (p : DemonstrativePronoun) (R : DenotGS F .et) (sIdx i : ℕ)
    (g : Assignment F.Entity) (gs : SitAssignment F) :
    Core.Nominal.interpret (p.toNominalKind R sIdx i) g gs
      = Core.Nominal.interpret (p.toPersonalPronoun.toNominalKind R i) g gs :=
  Core.Nominal.interpret_demonstrative_eq_anaphoric R p.deictic sIdx i g gs

/-- "Pronouns are definite descriptions," made precise: the pronoun's referent
selector (`PersonalPronoun.denote`) coincides with the interpretation of its
anaphoric-definite structure, whenever the restrictor (φ-features) holds of the
indexed referent. -/
theorem PersonalPronoun.denote_selector_eq_toNominalKind {F : Frame} [PartialOrder F.Entity]
    (e : PersonalPronoun) (i : ℕ) (R : DenotGS F .et)
    (speaker addressee : F.Entity) (isFemale isInanimate : F.Entity → Prop)
    (g : Assignment F.Entity) (gs : SitAssignment F) (w : PUnit)
    (h : R g gs (g i)) :
    (e.denote i speaker addressee isFemale isInanimate).selector g w
      = Core.Nominal.interpret (e.toNominalKind R i) g gs := by
  simp [PersonalPronoun.denote, PersonalPronoun.toNominalKind,
        Core.Nominal.interpret_anaphoric, interpPronoun, h]
