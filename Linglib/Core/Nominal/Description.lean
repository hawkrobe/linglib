import Linglib.Core.Logic.Intensional.Variables
import Linglib.Features.Deixis
import Linglib.Features.Definiteness

/-!
# Nominal Descriptions: Unified Sum Type
[coppock-beaver-2015] [patel-grosz-grosz-2017] [hanink-2021]
[moroney-2021] [schwarz-2009] [schwarz-2013]
[sharvy-1980] [kriz-2015]

A single sum type `Description F` covering the principal flavors of nominal
description that the syntax–semantics interface needs to distinguish:

- bare noun (number-neutral; covert type-shifts decide the reading)
- indefinite (∃; introduces a new discourse referent)
- unique (Coppock–Beaver weak/uniqueness; Sharvy/Križ maximal)
- anaphoric (Schwarz strong-article familiarity; Hanink-indexed; PG&G's German *der*)
- demonstrative (genuinely deictic this/that: a deictic feature, distinct from the strong article)
- possessive (definite via a possession relation)

The whole type is parameterized by a `Core.Logic.Intensional.Frame`, so all
restrictors, situation pronouns, and possessor expressions are typed via the
unified `F.Denot` machinery rather than ad-hoc `E → Bool` predicates.

## Design notes

- **Restrictors are `DenotGS F .et`.** Both entity assignments and situation
  assignments are first-class. This is the [hanink-2021] position: a noun's
  resource situation is a *bound variable* in the structure, not a free
  contextual parameter.

- **`unique` carries a situation-pronoun index.** Weak-article
  ([coppock-beaver-2015] uniqueness) definites are evaluated at a
  structurally-bound situation, the `situationIdx`-th situation pronoun
  retrievable via `interpSitPronoun situationIdx gs`.

- **`anaphoric` carries a discourse index.** [schwarz-2009]
  strong-article and [hanink-2021] anaphoric definites point to a
  discourse referent, the `discourseIdx`-th entity slot. This is the entity
  assignment's role.

- **`demonstrative` is a separate constructor** for *genuinely deictic*
  demonstratives (this/that; [moroney-2021] Shan *nâj*/*nân*): it carries
  **both** a discourse/pointing index *and* a deictic feature
  (`Features.Deixis.Feature`), checked at a situation pronoun. This is **distinct**
  from the [schwarz-2009] strong article (`anaphoric`): [patel-grosz-grosz-2017]
  analyze German *der* as the strong article (`anaphoric`), not as a deictic
  demonstrative — their footnote 1 doubts *der* is truly demonstrative at all.

- **`possessive` carries possessor + relation expressions** rather than
  conflating them with the restrictor. The relation has type `e ⇒ e ⇒ t`,
  and the possessor is an `e`-type expression that may itself be derived
  from a `Description` higher in the structure.

- **Reuses `Features.Deixis.Feature`** for the deictic content, so
  Shan/English/Latin/German fragments share the same enum.

- **No semantic interpretation here.** This file only declares the type and
  a handful of classification predicates. The interpretation function lives
  in `Core/Nominal/Interpret.lean`.
-/

namespace Core.Nominal

open Core.Logic.Intensional
open Core.Logic.Intensional.Variables

-- ════════════════════════════════════════════════════════════════
-- § The Sum Type
-- ════════════════════════════════════════════════════════════════

/-- Principal flavors of nominal description — the *definiteness/reference*
    axis (bare/indefinite vs the definite subtypes), orthogonal to
    `Features.BindingClass` (binding distribution) and to a pronoun's lexical
    kind. The frame parameter `F` supplies the entity domain and index set so
    all subexpressions live in the same `F.Denot` universe. -/
inductive Description (F : Frame) where
  /-- Bare noun (no overt determiner). The actual reading — kind, indefinite,
      unique, or anaphoric — is selected by the language's covert type-shift
      hierarchy ([chierchia-1998], [dayal-2004]). -/
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
  /-- Demonstrative (genuinely deictic this/that). Carries a deictic feature
      ([moroney-2021] Shan *nâj*/*nân*) and a discourse/pointing index; the
      restrictor is checked at the resource situation `situationIdx`. Distinct from
      the [schwarz-2009] strong article `anaphoric` (PG&G's German *der*). -/
  | demonstrative
      (restrictor : DenotGS F .et)
      (deictic : Features.Deixis.Feature)
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

namespace Description

variable {F : Frame}

/-- Is this a definite description (in the broad sense — uniqueness,
    familiarity, demonstrative, or possessive)? -/
def isDefinite : Description F → Prop
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
def isAnaphoric : Description F → Prop
  | .anaphoric _ _       => True
  | .demonstrative ..    => True
  | _                    => False

instance : DecidablePred (@isAnaphoric F) := fun n => by
  cases n <;> unfold isAnaphoric <;> infer_instance

/-- Does this description bind a structural situation pronoun? Coppock–Beaver
    uniqueness and demonstratives do (resource situation for maximality and
    deictic check); the other constructors do not. -/
def usesSituationPronoun : Description F → Bool
  | .unique _ _          => true
  | .demonstrative ..    => true
  | _                    => false

/-- Map each `Description` flavor to the [schwarz-2009]–[schwarz-2013]
    presupposition type it expresses, where applicable. Bare and indefinite
    return `none` because they are not (in themselves) definites. -/
def expectedPresupType :
    Description F → Option Features.Definiteness.DefPresupType
  | .bare _              => none
  | .indefinite _        => none
  | .unique _ _          => some .uniqueness
  | .anaphoric _ _       => some .familiarity
  | .demonstrative ..    => some .familiarity
  | .possessive ..       => some .uniqueness

/-- Definites are exactly those flavors with a non-`none` expected
    presupposition type. By construction. -/
theorem isDefinite_iff_expectedPresup_some (n : Description F) :
    n.isDefinite ↔ n.expectedPresupType.isSome = true := by
  cases n <;> simp [isDefinite, expectedPresupType]

/-- Anaphoric flavors all carry the familiarity presupposition type. -/
theorem isAnaphoric_implies_familiarity (n : Description F)
    (h : n.isAnaphoric) :
    n.expectedPresupType = some .familiarity := by
  cases n <;> simp [isAnaphoric] at h
  all_goals rfl

/-- The definite description for a [schwarz-2009] presupposition type: the
    **weak** article (uniqueness) is `unique`, the **strong** article (familiarity)
    is `anaphoric`. A section of `expectedPresupType` over the two article
    strengths, so any item carrying a `DefPresupType` — a determiner, a definite,
    or (per [patel-grosz-grosz-2017]) a personal/demonstrative pronoun —
    denotes by `ofPresupType` and recovers its strength via `expectedPresupType`.

    `idx` is the strong article's anaphoric/discourse index; for the weak article
    it fills the situation-pronoun slot, which `interpret` discards
    (`interpret_unique_index_irrelevant`). -/
def ofPresupType (p : Features.Definiteness.DefPresupType)
    (restrictor : DenotGS F .et) (idx : Nat) : Description F :=
  match p with
  | .uniqueness  => .unique restrictor idx
  | .familiarity => .anaphoric restrictor idx

/-- `ofPresupType` is a section of `expectedPresupType`: the strength round-trips. -/
theorem expectedPresupType_ofPresupType
    (p : Features.Definiteness.DefPresupType) (R : DenotGS F .et) (idx : Nat) :
    (ofPresupType p R idx).expectedPresupType = some p := by
  cases p <;> rfl

end Description

end Core.Nominal
