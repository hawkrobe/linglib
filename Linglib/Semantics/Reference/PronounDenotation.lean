import Linglib.Syntax.Category.Pronoun.Basic
import Linglib.Semantics.Reference.Nominal
import Linglib.Semantics.Presupposition.PhiFeatures
import Linglib.Semantics.Intensional.Variables
import Linglib.Core.Logic.Assignment
import Linglib.Semantics.Dynamic.HasFiberedLookup
import Linglib.Semantics.Definiteness.Interpret

/-!
# The denotation of a pronoun

Gives the `PersonalPronoun` lexical record a meaning, as a `NominalDenot`: the
selector is the project-canonical variable denotation `interpPronoun`
(`g ↦ g i`), so the pronoun-as-object and the bare assignment-indexed
variable are the same individual *by construction* — not via a bridge
theorem. The intrinsic presupposition is the φ-feature presupposition read
off the entry's person/number/gender via the [sauerland-2003]-style
cells in `Semantics.Presupposition.PhiFeatures`.

This follows [buring-2012]'s survey: the assignment lookup (his (14)), the
feature presuppositions (his (49)/(50)), and the absence-of-features treatment
of unmarked values. The same `interpPronoun` selector serves bound, anaphoric,
and deictic uses (his §2.1.1); binding is the external β-operator
(`Semantics.Reference.Binding`).

## Main definitions

* `PersonalPronoun.phiPresup` — the conjoined φ-feature presupposition of an
  entry (absent or featurally-uncovered values contribute `PartialProp.top`).
* `PersonalPronoun.denote` — the pronoun's `NominalDenot` (static case).

## Implementation notes

Number values beyond singular/plural (dual, trial, …) and the non-sex-based
surface genders contribute the vacuous cell here; the principled route is the
`Number.fromUD`/`Gender.Features.fromGender`
bridges plus `ContainmentPairLike.toPair`, deferred until a study needs them.
-/

set_option autoImplicit false

open Semantics.Presupposition (PartialProp)
open Semantics.Presupposition.PhiFeatures
open Semantics.Reference (NominalDenot)
open Core (Assignment)
open Intensional.Variables (interpPronoun DenotGS SitAssignment)

/-- The conjoined φ-feature presupposition of a pronoun entry, over an entity
domain `E`. The model supplies the entity-level predicates the cells need
(`speaker`/`addressee` for person, `isFemale`/`isInanimate` for gender;
number atomicity comes from the `PartialOrder`). A feature that is absent —
or present but outside the cells' coverage — contributes `PartialProp.top`. -/
def PersonalPronoun.phiPresup {E : Type*} [PartialOrder E] (e : PersonalPronoun)
    (speaker addressee : E) (isFemale isInanimate : E → Prop) : PartialProp E :=
  PartialProp.and
    (match e.person with
      | some .first  => firstSem speaker
      | some .second => secondSem speaker addressee
      | some .third  => thirdSem
      | _            => PartialProp.top)
    (PartialProp.and
      (match e.number with
        | some .singular => sgSem E
        | some .plural => plSem E
        | _          => PartialProp.top)
      (match e.gender with
        | some .feminine  => femSem isFemale
        | some .neuter    => neutSem isInanimate
        | some .masculine => mascSem
        | _               => PartialProp.top))

/-- A pronoun's denotation as a `NominalDenot`: the selector is the canonical
variable denotation `interpPronoun i` (always defined under a total
assignment), and the intrinsic presupposition is the φ-feature presupposition
imposed on the resolved referent `g i`. The static case; world is trivial. -/
def PersonalPronoun.denote {E : Type} [PartialOrder E] (e : PersonalPronoun) (i : ℕ)
    (speaker addressee : E) (isFemale isInanimate : E → Prop) :
    NominalDenot (Assignment E) PUnit E where
  presup := fun g _ => (e.phiPresup speaker addressee isFemale isInanimate).presup (g i)
  selector := fun g _ => some (interpPronoun (E := E) (W := PUnit) i g)

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
theorem interpPronoun_eq_iLookup {E W : Type} (i : ℕ) (g : Assignment E)
    (w : PUnit) :
    interpPronoun (E := E) (W := W) i g
      = Semantics.Dynamic.Context.HasFiberedLookup.iLookup (M := Id) g i w :=
  rfl

/-! ### Featural definedness tests -/

/-- A 3rd-person plural feminine entry (Spanish *ellas*), used to exercise
the φ-feature presupposition. -/
private def ellas : PersonalPronoun :=
  { form := "ellas", person := some .third, number := some .plural,
    gender := some .feminine }

/-- Negative: a feminine pronoun is undefined of a non-feminine referent. -/
example {E : Type*} [PartialOrder E] (speaker addressee : E)
    (isFemale isInanimate : E → Prop) (x : E) (h : ¬ isFemale x) :
    ¬ (ellas.phiPresup speaker addressee isFemale isInanimate).presup x :=
  fun hp => h hp.2.2

/-- Positive: under a feminine referent, the full pronoun denotation is
defined (its presupposition holds). -/
example {E : Type} [PartialOrder E] (g : Assignment E) (i : ℕ)
    (speaker addressee : E) (isFemale isInanimate : E → Prop)
    (scope : E → PUnit → Prop)
    (hFem : isFemale (g i)) :
    ((ellas.denote i speaker addressee isFemale isInanimate).toPartialProp scope g).presup ⟨⟩ := by
  refine ⟨⟨trivial, trivial, hFem⟩, ?_⟩
  rfl

/-! ### Pronouns are definite descriptions ([elbourne-2005], [patel-grosz-grosz-2017])

A referential pronoun *is* a (null-NP) definite description over its φ-feature
restrictor — a `Description`. [patel-grosz-grosz-2017]'s proposal is that the
personal/demonstrative split is the [schwarz-2009] weak/strong-article split:
PER (*er*) the **weak** article (`Description.ofPresupType .uniqueness` = `.unique`),
"DEM" (*der*) the **strong** article (`…ofPresupType .familiarity` = `.anaphoric`,
the weak description plus an anaphoric index). PG&G's "DEM = PER + index" is the
weak/strong refinement `Semantics.Definiteness.interpret_anaphoric_eq_unique_of_existsUnique`;
the strength round-trips through `expectedPresupType`. The extra layer is that index,
**not** spatial deixis (footnote 1) — *der* is a strong *personal* pronoun, not a
separate type; genuine deictic demonstratives are `Description.demonstrative`.

Caveat on `denote` below: the project's canonical `PersonalPronoun.denote` realizes
the [buring-2012] assignment lookup `g i` — the *indexed/anaphoric* referent,
i.e. the **strong** arm — so the bridge proves `denote` = `ofPresupType .familiarity`.
PG&G's *weak* PER (`ofPresupType .uniqueness`, the uniqueness iota over the
φ-restrictor) is a distinct denotation `denote` does not compute; the two arms agree
exactly when `g i` is the unique satisfier. -/

/-- A pronoun's [buring-2012] variable-lookup referent equals its definite
description whenever the restrictor holds of the indexed referent: the
**strong-article** (`Description.ofPresupType .familiarity`) reading, since the
anaphoric index *is* the indexed entity. The **weak** reading coincides too when
that entity is the unique satisfier (`Semantics.Definiteness.interpret_anaphoric_eq_unique_of_existsUnique`). -/
theorem PersonalPronoun.denote_selector_eq_ofPresupType {E W : Type} [PartialOrder E]
    (e : PersonalPronoun) (i : ℕ) (R : DenotGS E W .et)
    (speaker addressee : E) (isFemale isInanimate : E → Prop)
    (g : Assignment E) (gs : SitAssignment W) (w : PUnit)
    (h : R g gs (g i)) :
    (e.denote i speaker addressee isFemale isInanimate).selector g w
      = Semantics.Definiteness.interpret (Semantics.Definiteness.Description.ofPresupType .familiarity R i) g gs := by
  show some (g i) = Semantics.Definiteness.interpret (.anaphoric R i) g gs
  rw [Semantics.Definiteness.interpret_anaphoric, if_pos h]
