import Linglib.Semantics.Composition.Assignment
import Linglib.Semantics.Reference.Deixis
import Linglib.Semantics.Reference.Definiteness
import Linglib.Semantics.Reference.Iota
import Linglib.Semantics.Denotation

/-!
# Nominal descriptions

A `Description E W` is a definite description over entities `E` at situations `W`: a bare noun
read by the covert iota, the weak (uniqueness) and strong (familiarity) articles of
[schwarz-2009], a deictic demonstrative, and a possessive. Its denotation `⟦k⟧ g s`, relative to
an entity assignment and a resource situation, is the partial individual the description picks
out, `none` when the uniqueness presupposition fails. Every constructor is a Russellian iota
([russell-1905]) over a restrictor at the situation; the strong article and the demonstrative are
the iota over the restrictor conjoined with identity to the indexed entity, so the anaphoric
index selects the referent while the situation only decides definedness
(`denote_anaphoric_eq_some_iff`, `denote_anaphoric_rigid`), whereas the weak article's referent
covaries with the situation.

## Main definitions

* `Restrictor E W`: a property of entities at a situation, relative to an assignment.
* `Description E W`, `Description.denote`: the descriptions and their partial individual.
* `Description.kind`, `Description.ofStrength`: the Frame-free kind and the description an
  article strength realizes.

## Main results

* `denote_unique_eq_some_iff`, `denote_anaphoric_eq_some_iff`, `denote_possessive_isSome_iff`:
  the referent conditions of the three iotas.
* `denote_bare_eq_unique`, `denote_demonstrative_eq_anaphoric`: the covert iota is the weak
  article, and deixis filters without selecting.

## Implementation notes

The resource situation is a Reader argument of the denotation, as the assignment is: a
situation pronoun binding it ([hanink-2021]) is composition above the description, `fun gs ↦
⟦k⟧ g (gs n)`, not a field of it. Indefinites do not denote a partial individual and are not
descriptions; `Description.Kind.indefinite` records them for inventory typology only.
Demonstratives carry a `Reference.Deixis` feature whose presupposition is imposed by the
determiner (`DemonstrativeDeterminer.denote`), not by the description.

## References

* [schwarz-2009]
* [coppock-beaver-2015]
* [patel-grosz-grosz-2017]
* [hanink-2021]
* [moroney-2021]
* [russell-1905]
* [sharvy-1980]
-/

namespace Reference

open Semantics Semantics.Composition

/-- A restrictor: a property of entities at a situation, relative to an entity assignment. -/
abbrev Restrictor (E W : Type) := Assignment E → W → E → Prop

/-- The definite descriptions, distinguished by form: the covert iota of a bare noun, the weak
and strong articles of [schwarz-2009], a deictic demonstrative, and a possessive. -/
inductive Description (E W : Type) where
  /-- A bare noun read by the covert iota ([chierchia-1998], [dayal-2004]). -/
  | bare (restrictor : Restrictor E W)
  /-- The weak article: [coppock-beaver-2015]'s uniqueness definite. -/
  | unique (restrictor : Restrictor E W)
  /-- The strong article: the familiarity definite whose antecedent is the `discourseIdx`-th
  entity of the assignment. -/
  | anaphoric (restrictor : Restrictor E W) (discourseIdx : ℕ)
  /-- A deictic demonstrative ([moroney-2021]): the strong article with a deictic feature. -/
  | demonstrative (restrictor : Restrictor E W) (deictic : Reference.Deixis) (discourseIdx : ℕ)
  /-- A possessive: the unique satisfier of the restrictor that stands in `relation` to the
  `possessor`. -/
  | possessive (restrictor : Restrictor E W) (possessor : Assignment E → W → E)
      (relation : Assignment E → W → E → E → Prop)

namespace Description

variable {E W : Type} (R : Restrictor E W) (δ : Reference.Deixis) (d : ℕ)
  (possessor : Assignment E → W → E) (rel : Assignment E → W → E → E → Prop) (g : Assignment E)
  (s : W) {x : E}

/-! ### The Frame-free kind -/

/-- The kind of a description, its constructor with the payload erased. -/
def kind : Description E W → Kind
  | .bare _           => .bare
  | .unique _         => .unique
  | .anaphoric _ _    => .anaphoric
  | .demonstrative .. => .demonstrative
  | .possessive ..    => .possessive

/-- The description an article strength realizes over a restrictor: the weak article for
uniqueness and the strong article for familiarity, `idx` being the strong article's anaphoric
index. -/
def ofStrength (p : Strength) (R : Restrictor E W) (idx : ℕ) : Description E W :=
  match p with
  | .uniqueness  => .unique R
  | .familiarity => .anaphoric R idx

@[simp] theorem kind_ofStrength (p : Strength) (idx : ℕ) :
    (ofStrength p R idx).kind = p.toKind := by
  cases p <;> rfl

/-! ### The denotation -/

/-- The partial individual a description picks out at an assignment and a resource situation:
the Russellian iota over its restrictor at the situation, conjoined for the strong article and
the demonstrative with identity to the indexed entity ([schwarz-2009]) and for the possessive
with the possession relation to the possessor. -/
noncomputable def denote : Description E W → Assignment E → W → Option E
  | .bare R, g, s | .unique R, g, s => russellIota (R g s)
  | .anaphoric R d, g, s | .demonstrative R _ d, g, s =>
      russellIota fun x ↦ R g s x ∧ x = g d
  | .possessive R possessor rel, g, s =>
      russellIota fun x ↦ R g s x ∧ rel g s (possessor g s) x

noncomputable instance : Denotes (Description E W) (Assignment E → W → Option E) := ⟨denote⟩

@[simp] theorem denote_bare : ⟦bare R⟧ g s = russellIota (R g s) := rfl

@[simp] theorem denote_unique : ⟦unique R⟧ g s = russellIota (R g s) := rfl

@[simp] theorem denote_anaphoric :
    ⟦anaphoric R d⟧ g s = russellIota fun x ↦ R g s x ∧ x = g d := rfl

@[simp] theorem denote_demonstrative :
    ⟦demonstrative R δ d⟧ g s = russellIota fun x ↦ R g s x ∧ x = g d := rfl

@[simp] theorem denote_possessive :
    ⟦possessive R possessor rel⟧ g s = russellIota fun x ↦ R g s x ∧ rel g s (possessor g s) x :=
  rfl

/-- The covert iota of a bare noun is the weak article; the two differ in form, not meaning. -/
theorem denote_bare_eq_unique : ⟦bare R⟧ = ⟦unique R⟧ := rfl

/-- Deixis filters the referent without selecting it: a demonstrative denotes as the strong
article with the same index, and its deictic feature is a presupposition on the referent. -/
theorem denote_demonstrative_eq_anaphoric : ⟦demonstrative R δ d⟧ = ⟦anaphoric R d⟧ := rfl

/-! ### Referent conditions -/

/-- The weak article denotes `x` iff `x` is the unique satisfier of the restrictor at the
situation. -/
theorem denote_unique_eq_some_iff : ⟦unique R⟧ g s = some x ↔ R g s x ∧ ∀ y, R g s y → y = x :=
  russellIota_eq_some_iff _

/-- The covert iota denotes `x` iff `x` is the unique satisfier of the restrictor at the
situation. -/
theorem denote_bare_eq_some_iff : ⟦bare R⟧ g s = some x ↔ R g s x ∧ ∀ y, R g s y → y = x :=
  russellIota_eq_some_iff _

/-- The weak article is defined iff the restrictor has a unique satisfier at the situation. -/
theorem denote_unique_isSome_iff : (⟦unique R⟧ g s).isSome ↔ ∃! x, R g s x :=
  russellIota_isSome_iff _

/-- The strong article denotes `x` iff `x` is its antecedent and the restrictor holds of the
antecedent at the situation: the index selects, the situation only decides definedness. -/
theorem denote_anaphoric_eq_some_iff : ⟦anaphoric R d⟧ g s = some x ↔ R g s (g d) ∧ x = g d := by
  rw [denote_anaphoric, russellIota_eq_some_iff]
  exact ⟨fun ⟨⟨h, hx⟩, _⟩ ↦ ⟨hx ▸ h, hx⟩,
    fun ⟨h, hx⟩ ↦ ⟨⟨hx ▸ h, hx⟩, fun _ hy ↦ hy.2.trans hx.symm⟩⟩

/-- The strong article is defined iff the restrictor holds of its antecedent at the situation. -/
theorem denote_anaphoric_isSome_iff : (⟦anaphoric R d⟧ g s).isSome ↔ R g s (g d) := by
  rw [Option.isSome_iff_exists]
  simp only [denote_anaphoric_eq_some_iff, exists_eq_right]

/-- The strong article's referent does not covary with the situation: wherever it is defined,
it is the antecedent. -/
theorem denote_anaphoric_rigid {s' : W} {x' : E} (h : ⟦anaphoric R d⟧ g s = some x)
    (h' : ⟦anaphoric R d⟧ g s' = some x') : x = x' :=
  ((denote_anaphoric_eq_some_iff R d g s).1 h).2.trans
    ((denote_anaphoric_eq_some_iff R d g s').1 h').2.symm

/-- The possessive is defined iff exactly one satisfier of the restrictor stands in the
possession relation to the possessor. -/
theorem denote_possessive_isSome_iff :
    (⟦possessive R possessor rel⟧ g s).isSome ↔ ∃! x, R g s x ∧ rel g s (possessor g s) x :=
  russellIota_isSome_iff _

end Description

end Reference
