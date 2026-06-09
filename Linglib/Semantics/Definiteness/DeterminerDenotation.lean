import Linglib.Semantics.Definiteness.Interpret
import Linglib.Semantics.Definiteness.DeterminerLicensing
import Linglib.Semantics.Reference.Nominal

/-!
# The denotation of a determiner

[schwarz-2009] [patel-grosz-grosz-2017] [coppock-beaver-2015] [moroney-2021]

Gives the determiner lexical records (`Syntax/Determiner/Basic.lean`) meanings,
as `NominalDenot`s — the determiner half of the API whose pronoun half is
`Semantics/Reference/PronounDenotation.lean`. The wiring is parallel:

| | pronoun | determiner |
|---|---|---|
| lexical record | `PersonalPronoun` | `Article`, `DemonstrativeDeterminer` |
| selector | `interpPronoun` (`g ↦ g i`) | `Semantics.Definiteness.interpret` |
| intrinsic presupposition | φ-features (`phiPresup`) | deixis (`deixisPresup`) |

The selector is the canonical `Description` interpretation — determiner-as-object
and the interpreted description pick the same individual *by construction*, not
via a bridge theorem. The intrinsic presupposition is where a demonstrative's
deictic feature projects: deixis filters the referent but never selects it
(`denote_selector_eq_anaphoric`, the API-level form of
`interpret_demonstrative_eq_anaphoric`).

## Main declarations

* `Description.denote` — a description's `NominalDenot` (vacuous intrinsic
  presupposition; a definite's only presupposition is definedness).
* `DemonstrativeDeterminer.deixisPresup` — the deictic presupposition over an
  entity domain, with model-supplied proximity predicates (parallel to
  `PersonalPronoun.phiPresup`'s `speaker`/`addressee`).
* `DemonstrativeDeterminer.denote` — the demonstrative's `NominalDenot`
  (previously deferred in the lexical file's implementation notes).
* `Article.denotations` — an article's possible `NominalDenot`s, the image of
  `Article.toDescriptions` under `Description.denote`; a syncretic article
  (English *the*) denotes both the weak and the strong description.

## Implementation notes

Context is the bi-assignment `Assignment E × SitAssignment W` and the
world coordinate is trivial (`PUnit`), matching the static case of
`PersonalPronoun.denote`. `Quantifier` (a generalized quantifier, not an
individual denotation — it has no `NominalDenot`) and `Possessive` remain
deferred.
-/

namespace Semantics.Definiteness

open Semantics.Reference (NominalDenot)
open Core.Logic.Intensional.Variables
open Core (Assignment)
open Features.Definiteness (DefPresupType)

variable {E W : Type}

/-! ### Descriptions as nominal denotations -/

/-- A description's denotation as a `NominalDenot`: the selector is the
canonical interpretation function `interpret`, and the intrinsic
presupposition is vacuous — a definite's only presupposition is that the
selector is defined. The static case; world is trivial. -/
noncomputable def Description.denote (k : Description E W) :
    NominalDenot (Assignment E × SitAssignment W) PUnit E where
  presup := fun _ _ => True
  selector := fun gp _ => interpret k gp.1 gp.2

/-- The by-construction identity: a description's selector *is* `interpret`. -/
@[simp]
theorem Description.denote_selector (k : Description E W)
    (g : Assignment E) (gs : SitAssignment W) (w : PUnit) :
    k.denote.selector (g, gs) w = interpret k g gs := rfl

/-! ### The demonstrative determiner's denotation -/

/-- The deictic presupposition of a demonstrative determiner, over an entity
domain. The model supplies the proximity predicates the deixis cells need
(parallel to the `speaker`/`addressee`/`isFemale` parameters of
`PersonalPronoun.phiPresup`); an `unspecified` feature contributes the
trivial presupposition. -/
def _root_.DemonstrativeDeterminer.deixisPresup (dem : DemonstrativeDeterminer)
    (proximal medial distal : E → Prop) : E → Prop :=
  match dem.deictic with
  | .proximal    => proximal
  | .medial      => medial
  | .distal      => distal
  | .unspecified => fun _ => True

/-- A demonstrative determiner's denotation as a `NominalDenot` (the
`DemonstrativeDeterminer.denote` deferred by the lexical file): the selector
is the canonical interpretation of the demonstrative description at discourse
index `d`, and the intrinsic presupposition is the deictic presupposition
imposed on the indexed referent `g d` — parallel to `PersonalPronoun.denote`,
with deixis in place of φ-features. -/
noncomputable def _root_.DemonstrativeDeterminer.denote (dem : DemonstrativeDeterminer)
    (R : DenotGS E W .et) (sIdx d : Nat)
    (proximal medial distal : E → Prop) :
    NominalDenot (Assignment E × SitAssignment W) PUnit E where
  presup := fun gp _ => dem.deixisPresup proximal medial distal (gp.1 d)
  selector := fun gp _ =>
    interpret (.demonstrative R dem.deictic sIdx d) gp.1 gp.2

/-- Deixis filters, it does not select: a demonstrative determiner's selector
is exactly the bare anaphoric description's selector. The API-level form of
`interpret_demonstrative_eq_anaphoric` — the deictic content lives entirely
in the `presup` component. -/
theorem DemonstrativeDeterminer.denote_selector_eq_anaphoric
    (dem : DemonstrativeDeterminer) (R : DenotGS E W .et) (sIdx d : Nat)
    (proximal medial distal : E → Prop) :
    (dem.denote R sIdx d proximal medial distal).selector
      = (Description.anaphoric R d).denote.selector := by
  funext gp w
  exact interpret_demonstrative_eq_anaphoric R dem.deictic sIdx d gp.1 gp.2

/-- Two demonstrative determiners differing only in deictic feature share a
selector — *this* and *that* pick the same referent and differ only in what
they presuppose about it. -/
theorem DemonstrativeDeterminer.denote_selector_congr
    (dem₁ dem₂ : DemonstrativeDeterminer) (R : DenotGS E W .et) (sIdx d : Nat)
    (proximal medial distal : E → Prop) :
    (dem₁.denote R sIdx d proximal medial distal).selector
      = (dem₂.denote R sIdx d proximal medial distal).selector := by
  rw [DemonstrativeDeterminer.denote_selector_eq_anaphoric,
      DemonstrativeDeterminer.denote_selector_eq_anaphoric]

/-! ### The article's denotations -/

/-- An article's possible denotations: the `NominalDenot`s of its admissible
descriptions (`Article.toDescriptions`). A syncretic article (English *the*)
denotes both the weak and the strong description; a German weak or strong
article denotes exactly one. -/
noncomputable def _root_.Article.denotations (a : Article)
    (R : DenotGS E W .et) (idx : Nat) :
    List (NominalDenot (Assignment E × SitAssignment W) PUnit E) :=
  (a.toDescriptions R idx).map Description.denote

/-- Every denotation of an article arises from a description the article
licenses — the denotational pipeline and the licensing pipeline agree. -/
theorem Article.denotations_licensed (a : Article)
    (R : DenotGS E W .et) (idx : Nat)
    (nd : NominalDenot (Assignment E × SitAssignment W) PUnit E)
    (h : nd ∈ a.denotations R idx) :
    ∃ k : Description E W,
      Determiner.licenses [.article a] k ∧ nd = k.denote := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
  exact ⟨k, Determiner.licenses_mem_toDescriptions a R idx k hk, rfl⟩

end Semantics.Definiteness
