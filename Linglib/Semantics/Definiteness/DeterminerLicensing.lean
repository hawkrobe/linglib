import Linglib.Syntax.Category.Determiner.Basic
import Linglib.Semantics.Definiteness.Description

/-!
# Determiner licensing

`Determiner.licenses`: does a declared `List Determiner.Entry` have the surface
form needed to realize a given `Description` constructor? Kept separate from
`Determiner.lean` so that marking-only Fragments do not transitively import the
`E`/`W`-parameterized `Description` substrate.
-/

open Intensional.Variables (DenotGS)
open Semantics.Definiteness (Description)
open Features.Definiteness (DefPresupType)

namespace Determiner

/-- Does the declared determiner set have the surface form needed to realize the
given `Description` constructor? Bare nominals are always licensed; unique and
anaphoric definites need a determiner exponing the corresponding presupposition
type (`MarksPresup`); indefinite/demonstrative/possessive need a determiner of
that kind. -/
def licenses {E W : Type} (ds : List Entry) : Description E W → Prop
  | .bare _           => True
  | .indefinite _     => ∃ e ∈ ds, e.IsIndefiniteArticle
  | .unique _ _       => MarksPresup ds .uniqueness
  | .anaphoric _ _    => MarksPresup ds .familiarity
  | .demonstrative .. => ∃ e ∈ ds, e.IsDemonstrative
  | .possessive ..    => ∃ e ∈ ds, e.IsPossessive

instance {E W : Type} (ds : List Entry) (k : Description E W) : Decidable (licenses ds k) := by
  cases k <;> unfold licenses <;> infer_instance

/-! ### An article's possible denotations

The deferred `Article.denote`: an article denotes the **set** of `Description`s its
admissible strengths (`Article.presupTypes`) realize through `Description.ofPresupType`
— a syncretic article (English *the*) denotes both the weak and the strong
description, not a single one. -/

/-- An article's possible (definite-description) denotations: the image of its
admissible [schwarz-2009] strengths under `Description.ofPresupType`. -/
def _root_.Article.toDescriptions {E W : Type} (a : Article)
    (R : DenotGS E W .et) (idx : Nat) : List (Description E W) :=
  a.presupTypes.map (Description.ofPresupType · R idx)

/-- Licensing through `ofPresupType` is exactly `MarksPresup`: a determiner set
licenses the weak/strong denotation of strength `p` iff some determiner expones a
definite use of presupposition type `p`. The denotation pipeline (`ofPresupType`)
and the inventory pipeline (`MarksPresup`) coincide by construction. -/
theorem licenses_ofPresupType {E W : Type} (ds : List Entry)
    (p : DefPresupType) (R : DenotGS E W .et) (idx : Nat) :
    licenses ds (Description.ofPresupType p R idx) ↔ MarksPresup ds p := by
  cases p <;> exact Iff.rfl

/-- An article licenses each of its own possible denotations. -/
theorem licenses_mem_toDescriptions {E W : Type} (a : Article)
    (R : DenotGS E W .et) (idx : Nat) (k : Description E W)
    (hk : k ∈ a.toDescriptions R idx) :
    licenses [.article a] k := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
  exact (licenses_ofPresupType [.article a] p R idx).mpr
    ((Article.mem_presupTypes_iff_marksPresup a p).mp hp)

end Determiner
