import Linglib.Core.IntensionalLogic.Variables
import Linglib.Core.Deixis.Feature
import Linglib.Features.Definiteness

/-!
# Nominal Descriptions: Unified Sum Type
@cite{coppock-beaver-2015} @cite{patel-grosz-grosz-2017} @cite{hanink-2021}
@cite{bondarenko-2023} @cite{moroney-2021} @cite{schwarz-2009} @cite{schwarz-2013}
@cite{sharvy-1980} @cite{kriz-2015}

A single sum type `NominalKind F` covering the principal flavors of nominal
description that the syntax–semantics interface needs to distinguish:

- bare noun (number-neutral; covert type-shifts decide the reading)
- indefinite (∃; introduces a new discourse referent)
- unique (Coppock–Beaver weak/uniqueness; Sharvy/Križ maximal)
- anaphoric (Schwarz strong-article familiarity; Hanink-indexed)
- demonstrative (Patel-Grosz–Grosz/Davis: a separate object, not "strong the")
- possessive (definite via a possession relation)

The whole type is parameterized by a `Core.IntensionalLogic.Frame`, so all
restrictors, situation pronouns, and possessor expressions are typed via the
unified `F.Denot` machinery rather than ad-hoc `E → Bool` predicates.

## Design notes

- **Restrictors are `DenotGS F .et`.** Both entity assignments and situation
  assignments are first-class. This is the @cite{hanink-2021} /
  @cite{bondarenko-2023} position: a noun's resource situation is a *bound
  variable* in the structure, not a free contextual parameter.

- **`unique` carries a situation-pronoun index.** Weak-article
  (@cite{coppock-beaver-2015} uniqueness) definites are evaluated at a
  structurally-bound situation, the `situationIdx`-th situation pronoun
  retrievable via `interpSitPronoun situationIdx gs`.

- **`anaphoric` carries a discourse index.** @cite{schwarz-2009}
  strong-article and @cite{hanink-2021} anaphoric definites point to a
  discourse referent, the `discourseIdx`-th entity slot. This is the entity
  assignment's role.

- **`demonstrative` is a separate constructor.** @cite{patel-grosz-grosz-2017}
  and the Patel-Grosz–Grosz–Davis tradition reject the pure "demonstrative =
  strong article" identification. A demonstrative carries **both** a discourse
  index *and* a deictic feature (`Core.Deixis.Feature`). Its restrictor is
  also evaluated at a situation pronoun (the situation in which the deictic
  predicate is checked).

- **`possessive` carries possessor + relation expressions** rather than
  conflating them with the restrictor. The relation has type `e ⇒ e ⇒ t`,
  and the possessor is an `e`-type expression that may itself be derived
  from a `NominalKind` higher in the structure.

- **Reuses `Core.Deixis.Feature`** for the deictic content, so
  Shan/English/Latin/German fragments share the same enum.

- **No semantic interpretation here.** This file only declares the type and
  a handful of classification predicates. The interpretation function lives
  in `Core/Nominal/Interpret.lean`.
-/

namespace Core.Nominal

open Core.IntensionalLogic
open Core.IntensionalLogic.Variables

-- ════════════════════════════════════════════════════════════════
-- § The Sum Type
-- ════════════════════════════════════════════════════════════════

/-- Principal flavors of nominal description. The frame parameter `F` supplies
    the entity domain and index set so all subexpressions live in the same
    `F.Denot` universe. -/
inductive NominalKind (F : Frame) where
  /-- Bare noun (no overt determiner). The actual reading — kind, indefinite,
      unique, or anaphoric — is selected by the language's covert type-shift
      hierarchy (@cite{chierchia-1998}, @cite{dayal-2004}). -/
  | bare (restrictor : DenotGS F .et)
  /-- Indefinite (∃). Introduces a new discourse referent and presupposes
      nothing about prior discourse. Heim (1982)/Kamp novelty. -/
  | indefinite (restrictor : DenotGS F .et)
  /-- Coppock–Beaver weak/uniqueness definite (Sharvy/Križ maximal). The
      restrictor is evaluated at the resource situation pointed to by the
      `situationIdx`-th situation pronoun (Hanink 2021 binding). -/
  | unique (restrictor : DenotGS F .et) (situationIdx : Nat)
  /-- Schwarz strong-article / Hanink-indexed anaphoric definite. The
      `discourseIdx`-th entity-assignment slot is the antecedent. -/
  | anaphoric (restrictor : DenotGS F .et) (discourseIdx : Nat)
  /-- Demonstrative (this/that). Carries a deictic feature
      (@cite{patel-grosz-grosz-2017} D-deix layer; @cite{moroney-2021} §2.1.3
      Shan *nâj*/*nân*) and a discourse/pointing index. The restrictor is
      checked at the resource situation pointed to by `situationIdx`. -/
  | demonstrative
      (restrictor : DenotGS F .et)
      (deictic : Core.Deixis.Feature)
      (situationIdx : Nat)
      (discourseIdx : Nat)
  /-- Definite description via a possession relation: ⟦the N of x⟧ where the
      restrictor and `relation` jointly pin down a unique satisfier related to
      `possessor`. -/
  | possessive
      (restrictor : DenotGS F .et)
      (possessor : DenotGS F .e)
      (relation : DenotGS F .eet)

-- ════════════════════════════════════════════════════════════════
-- § Classification Predicates (derivable, no semantics yet)
-- ════════════════════════════════════════════════════════════════

namespace NominalKind

variable {F : Frame}

/-- Is this a definite description (in the broad sense — uniqueness,
    familiarity, demonstrative, or possessive)? -/
def isDefinite : NominalKind F → Prop
  | .bare _              => False
  | .indefinite _        => False
  | .unique _ _          => True
  | .anaphoric _ _       => True
  | .demonstrative ..    => True
  | .possessive ..       => True

instance : DecidablePred (@isDefinite F) := fun n => by
  cases n <;> unfold isDefinite <;> infer_instance

/-- Does this description require a discourse antecedent? Anaphoric and
    demonstrative do; unique/possessive/bare/indefinite do not. -/
def isAnaphoric : NominalKind F → Prop
  | .anaphoric _ _       => True
  | .demonstrative ..    => True
  | _                    => False

instance : DecidablePred (@isAnaphoric F) := fun n => by
  cases n <;> unfold isAnaphoric <;> infer_instance

/-- Does this description bind a structural situation pronoun? Coppock–Beaver
    uniqueness and demonstratives do (resource situation for maximality and
    deictic check); the other constructors do not. -/
def usesSituationPronoun : NominalKind F → Bool
  | .unique _ _          => true
  | .demonstrative ..    => true
  | _                    => false

/-- Map each `NominalKind` flavor to the @cite{schwarz-2009}–@cite{schwarz-2013}
    presupposition type it expresses, where applicable. Bare and indefinite
    return `none` because they are not (in themselves) definites. -/
def expectedPresupType :
    NominalKind F → Option Features.Definiteness.DefPresupType
  | .bare _              => none
  | .indefinite _        => none
  | .unique _ _          => some .uniqueness
  | .anaphoric _ _       => some .familiarity
  | .demonstrative ..    => some .familiarity
  | .possessive ..       => some .uniqueness

/-- Definites are exactly those flavors with a non-`none` expected
    presupposition type. By construction. -/
theorem isDefinite_iff_expectedPresup_some (n : NominalKind F) :
    n.isDefinite ↔ n.expectedPresupType.isSome = true := by
  cases n <;> simp [isDefinite, expectedPresupType]

/-- Anaphoric flavors all carry the familiarity presupposition type. -/
theorem isAnaphoric_implies_familiarity (n : NominalKind F)
    (h : n.isAnaphoric) :
    n.expectedPresupType = some .familiarity := by
  cases n <;> simp [isAnaphoric] at h
  all_goals rfl

end NominalKind

end Core.Nominal
