import Linglib.Semantics.Reference.Description
import Linglib.Syntax.Category.Determiner.Basic
import Linglib.Semantics.Reference.Nominal
import Linglib.Semantics.Possession.Basic

/-!
# The denotation of a determiner

[schwarz-2009] [patel-grosz-grosz-2017] [coppock-beaver-2015] [moroney-2021]

Gives the determiner lexical records (`Syntax/Category/Determiner/Basic.lean`) meanings,
as `Nominal`s — the determiner half of the API whose pronoun half is
`Semantics/Reference/Pronoun.lean`. The wiring is parallel:

| | pronoun | determiner |
|---|---|---|
| lexical record | `PersonalPronoun` | `Article`, `DemonstrativeDeterminer` |
| selector | `interpPronoun` (`g ↦ g i`) | `⟦k⟧` for a `Description` `k` |
| intrinsic presupposition | φ-features (`phiPresup`) | deixis (`deixisPresup`) |

The selector is the description's denotation, so determiner-as-object and the interpreted
description pick the same individual *by construction*. The intrinsic presupposition is where
a demonstrative's deictic feature projects: deixis filters the referent but never selects it
(`denote_selector_eq_anaphoric`, the API-level form of
`Description.denote_demonstrative_eq_anaphoric`).

## Main declarations

* `Description.toNominal` — a description's `Nominal` (vacuous intrinsic
  presupposition; a definite's only presupposition is definedness).
* `DemonstrativeDeterminer.deixisPresup` — the deictic presupposition over an
  entity domain, with model-supplied proximity predicates (parallel to
  `PersonalPronoun.phiPresup`'s `speaker`/`addressee`).
* `DemonstrativeDeterminer.denote` — the demonstrative's `Nominal`.
* `Article.toDescriptions` — an article's possible descriptions, the image of
  its admissible [schwarz-2009] strengths under `Description.ofStrength`.
* `Article.denotations` — an article's possible `Nominal`s, the image of
  `Article.toDescriptions` under `Description.toNominal`; a syncretic article
  (English *the*) denotes both the weak and the strong description.
* `PossessiveDeterminer.denote` — the possessive determiner's `Nominal`: a definite description
  selecting the unique satisfier of the possessee restrictor that stands in the possession
  relation to the possessor; the GQ-form possessive (`PossNP`, narrowing-aware) lives in
  `Semantics/Possession/Quantifier.lean`.
* `Description.denote_possessive_eq_pi`, `PossessiveDeterminer.denote_isSome_iff_existsUnique`
  — the determiner denotation *is* the `Possession` description: Barker's `π` applied to the
  possessor as restrictor, definedness as its presupposition.

## Implementation notes

Context is the entity assignment `Assignment E` and the world coordinate is the resource
situation `W`, exactly as for `PersonalPronoun.denote`. `QuantifierDeterminer` (a generalized
quantifier, not an individual denotation — it has no `Nominal`) remains deferred.
-/

namespace Reference

open Semantics Semantics.Composition

variable {E W : Type} (R : Restrictor E W) (d : ℕ) (possessor : Assignment E → W → E)
  (rel : Assignment E → W → E → E → Prop) (proximal medial distal : E → Prop)

/-! ### Descriptions as nominal denotations -/

/-- A description as a `Nominal`: the selector is its denotation and the intrinsic
presupposition is vacuous, a definite's only presupposition being that the selector is
defined. -/
noncomputable def Description.toNominal (k : Description E W) : Nominal (Assignment E) W E where
  presup _ _ := True
  selector := ⟦k⟧

@[simp] theorem Description.toNominal_selector (k : Description E W) :
    k.toNominal.selector = ⟦k⟧ := rfl

@[simp] theorem Description.toNominal_presup (k : Description E W) (g : Assignment E) (s : W) :
    k.toNominal.presup g s = True := rfl

/-! ### The demonstrative determiner's denotation -/

/-- The deictic presupposition of a demonstrative determiner, over an entity
domain. The model supplies the proximity predicates the deixis cells need
(parallel to the `speaker`/`addressee`/`isFemale` parameters of
`PersonalPronoun.phiPresup`); an `unspecified` feature contributes the
trivial presupposition. -/
def _root_.DemonstrativeDeterminer.deixisPresup (dem : DemonstrativeDeterminer) : E → Prop :=
  match dem.deictic with
  | .proximal    => proximal
  | .medial      => medial
  | .distal      => distal
  | .unspecified => fun _ ↦ True

/-- A demonstrative determiner's denotation as a `Nominal`: the selector is the demonstrative
description at discourse index `d`, and the intrinsic presupposition is the deictic
presupposition imposed on the indexed referent `g d` — parallel to `PersonalPronoun.denote`,
with deixis in place of φ-features. -/
noncomputable def _root_.DemonstrativeDeterminer.denote (dem : DemonstrativeDeterminer) :
    Nominal (Assignment E) W E where
  presup g _ := dem.deixisPresup proximal medial distal (g d)
  selector := ⟦Description.demonstrative R dem.deictic d⟧

/-- Deixis filters, it does not select: a demonstrative determiner's selector
is exactly the strong article's selector. The API-level form of
`Description.denote_demonstrative_eq_anaphoric` — the deictic content lives entirely
in the `presup` component. -/
theorem _root_.DemonstrativeDeterminer.denote_selector_eq_anaphoric
    (dem : DemonstrativeDeterminer) :
    (dem.denote R d proximal medial distal).selector
      = (Description.anaphoric R d).toNominal.selector := rfl

/-- Two demonstrative determiners differing only in deictic feature share a
selector — *this* and *that* pick the same referent and differ only in what
they presuppose about it. -/
theorem _root_.DemonstrativeDeterminer.denote_selector_congr
    (dem₁ dem₂ : DemonstrativeDeterminer) :
    (dem₁.denote R d proximal medial distal).selector
      = (dem₂.denote R d proximal medial distal).selector := rfl

/-! ### The article's descriptions and denotations -/

/-- The descriptions an article can denote are the images of its admissible [schwarz-2009]
strengths under `Description.ofStrength`. A syncretic article such as English *the* denotes both
the weak and the strong description. -/
def _root_.Article.toDescriptions (a : Article) (R : Restrictor E W)
    (idx : ℕ) : Set (Description E W) :=
  (Description.ofStrength · R idx) '' a.strengths

/-- An article realizes the kind of each of its own descriptions, so the denotation pipeline
through `Description.ofStrength` and the inventory pipeline through
`Determiner.Inventory.Realizes` coincide. -/
theorem _root_.Article.realizes_of_mem_toDescriptions (a : Article) (idx : ℕ)
    (k : Description E W) (hk : k ∈ a.toDescriptions R idx) :
    Determiner.Inventory.Realizes [.article a] k.kind := by
  obtain ⟨p, hp, rfl⟩ := hk
  rw [Description.kind_ofStrength, Determiner.Inventory.realizes_toKind,
    Determiner.Inventory.marks_singleton]
  exact (Article.mem_strengths_iff_marks a p).mp hp

/-- The `Nominal`s an article can denote are those of its descriptions. -/
def _root_.Article.denotations (a : Article) (R : Restrictor E W) (idx : ℕ) :
    Set (Nominal (Assignment E) W E) :=
  Description.toNominal '' a.toDescriptions R idx

/-- Every denotation of an article arises from a description whose kind the article realizes. -/
theorem _root_.Article.denotations_realized (a : Article) (idx : ℕ)
    (nd : Nominal (Assignment E) W E) (h : nd ∈ a.denotations R idx) :
    ∃ k : Description E W,
      Determiner.Inventory.Realizes [.article a] k.kind ∧ nd = k.toNominal := by
  obtain ⟨k, hk, rfl⟩ := h
  exact ⟨k, Article.realizes_of_mem_toDescriptions R a idx k hk, rfl⟩

/-! ### The possessive determiner's denotation -/

/-- A possessive determiner's denotation as a `Nominal`: the definite
description selecting the unique satisfier of the possessee restrictor `R` that
stands in `rel` to the `possessor` — the `Description.possessive` selector
(`russellIota` of `R ∧ rel possessor ·`). The intrinsic presupposition is
vacuous; the definite's only presupposition is definedness, exposed as the
selector returning `some`.

The narrowing-aware GQ form for quantificational possessors ("every student's
cat") is `Possession.PossNP` — `(individual a)` of
`PossNP` reduces here when the possessor is an entity. -/
noncomputable def _root_.PossessiveDeterminer.denote (_p : PossessiveDeterminer) :
    Nominal (Assignment E) W E :=
  (Description.possessive R possessor rel).toNominal

/-- A possessive determiner's selector is the possessive description's
selector — the determiner picks the unique possessee related to the
possessor by construction. -/
@[simp]
theorem _root_.PossessiveDeterminer.denote_selector (p : PossessiveDeterminer) :
    (p.denote R possessor rel).selector = ⟦Description.possessive R possessor rel⟧ := rfl

/-- A possessive determiner realizes the kind of its own denotation — the
denotational pipeline and the inventory pipeline agree, parallel to
`Article.denotations_realized`. -/
theorem _root_.PossessiveDeterminer.denote_realized (p : PossessiveDeterminer) :
    Determiner.Inventory.Realizes [.possessive p] (Description.possessive R possessor rel).kind :=
  ⟨.possessive p, List.mem_singleton_self _, rfl⟩

/-! ### Unification with the possessive description

The possessive determiner's denotation (`Description.possessive`/`russellIota`) and the
`Possession` description are not two analyses — they are the same construction. The
determiner's restrictor *is* Barker's `Possession.π` of the noun predicate and the possession
relation, applied to the possessor, and its definedness presupposition *is* the description's
Russellian uniqueness condition. -/

section DescriptionUnification

variable (g : Assignment E) (s : W)

/-- The possessive determiner's restrictor *is* Barker's `π` of the noun predicate `R`
and the possession relation `rel` at the situation, applied to the possessor: the
`Reference` and `Possession` encodings select through the same construction, by
construction. -/
theorem Description.denote_possessive_eq_pi :
    ⟦Description.possessive R possessor rel⟧ g s
      = russellIota fun x ↦ Possession.π (fun y s' ↦ R g s' y) (fun a b s' ↦ rel g s' a b)
          (possessor g s) x s :=
  rfl

/-- The possessive determiner's definedness presupposition *is* the description's Russellian
uniqueness condition. -/
theorem _root_.PossessiveDeterminer.denote_isSome_iff_existsUnique (p : PossessiveDeterminer) :
    ((p.denote R possessor rel).selector g s).isSome
      ↔ ∃! x, R g s x ∧ rel g s (possessor g s) x :=
  Description.denote_possessive_isSome_iff R possessor rel g s

end DescriptionUnification

end Reference
