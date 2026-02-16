import Linglib.Theories.Semantics.Lexical.Determiner.Quantifier
import Linglib.Theories.Semantics.Lexical.Noun.TypeShifting
import Linglib.Theories.Semantics.Reference.Donnellan
import Linglib.Core.Presupposition
import Linglib.Core.Definiteness
import Linglib.Fragments.English.Determiners

/-!
# The Semantics of Definiteness

Denotations for definite descriptions using the type vocabulary from
`Core/Definiteness.lean`. Two theories, formalized as determiner denotations
with presuppositions:

- **Uniqueness** (Russell 1905, Frege 1892, Strawson 1950): "the φ" presupposes
  existence and uniqueness of a φ-entity; asserts predication of that entity.
- **Familiarity** (Heim 1982, Kamp 1981): "the φ" presupposes that a φ-entity
  is already familiar/salient in the discourse; asserts predication of it.

## Key Results

- `the_uniq`: ⟦the⟧ under uniqueness (Russell/Strawson)
- `the_fam`: ⟦the⟧ under familiarity (Heim/Kamp)
- `the_uniq_eq_definitePrProp`: uniqueness = Donnellan's attributive semantics
- `the_uniq_presup_iff_iota`: uniqueness presup ↔ Partee's ι succeeds
- `the_is_every_on_singletons`: ⟦the⟧ = ⟦every⟧ on singleton restrictors

## References

- Russell, B. (1905). On Denoting. Mind.
- Strawson, P. (1950). On Referring. Mind.
- Heim, I. (1982). The Semantics of Definite and Indefinite NPs. UMass diss.
- Kamp, H. (1981). A Theory of Truth and Semantic Representation.
- Partee, B. (1987). NP Interpretation and Type-shifting Principles.
- Donnellan, K. (1966). Reference and Definite Descriptions. Phil. Review.
-/

namespace Semantics.Lexical.Determiner.Definite

open Semantics.Compositional (Model Ty toyModel ToyEntity)
open Semantics.Lexical.Determiner.Quantifier (FiniteModel every_sem some_sem Ty.det)
open Semantics.Lexical.Noun.TypeShifting (iota lift)
open Core.Presupposition (PrProp)
open Core.Definiteness (DefPresupType Definiteness)
open Semantics.Reference.Donnellan (definitePrProp attributiveContent)

-- ============================================================================
-- §1: Uniqueness-Based Definite (Weak Article)
-- ============================================================================

/-- ⟦the⟧ under uniqueness (Russell/Strawson/Heim & Kratzer 1998):

Presupposition: exactly one entity in the domain satisfies the restrictor.
Assertion: the scope predicate holds of that entity.

Type: `(e→t) → (e→t) → PrProp W`
(restrictor → scope → presuppositional proposition)

This corresponds to Schwarz's **weak article** (German contracted *vom*,
Fering A-form, Lakhota *kiŋ*). -/
def the_uniq {E : Type} (domain : List E) [DecidableEq E]
    (restrictor : E → Bool) (scope : E → Bool) : PrProp Unit :=
  { presup := λ _ =>
      match domain.filter restrictor with
      | [_] => true
      | _ => false
  , assertion := λ _ =>
      match domain.filter restrictor with
      | [e] => scope e
      | _ => false }

/-- ⟦the⟧ under uniqueness, world-indexed version.

For intensional contexts where the restrictor extension varies by world.
This is the standard Heim & Kratzer (1998) entry. -/
def the_uniq_w {W E : Type} (domain : List E)
    (restrictor : E → W → Bool) (scope : E → W → Bool) : PrProp W :=
  { presup := λ w =>
      match domain.filter (λ e => restrictor e w) with
      | [_] => true
      | _ => false
  , assertion := λ w =>
      match domain.filter (λ e => restrictor e w) with
      | [e] => scope e w
      | _ => false }

-- ============================================================================
-- §2: Familiarity-Based Definite (Strong Article)
-- ============================================================================

/-- A discourse context tracking salient/familiar entities.

Heim (1982): the context is a set of "file cards" — entities that have
been introduced into the discourse and are available for anaphoric reference. -/
structure DiscourseContext (E : Type) where
  /-- Entities currently salient/familiar in discourse -/
  salient : List E

/-- ⟦the⟧ under familiarity (Heim 1982, Kamp 1981):

Presupposition: there exists a salient entity in the discourse context
matching the restrictor.
Assertion: the scope predicate holds of that entity.

This corresponds to Schwarz's **strong article** (German full *von dem*,
Fering D-form, Lakhota *k'uŋ*, Akan *nó*). -/
def the_fam {E : Type} [DecidableEq E]
    (dc : DiscourseContext E)
    (restrictor : E → Bool) (scope : E → Bool) : PrProp Unit :=
  { presup := λ _ =>
      match dc.salient.filter restrictor with
      | [_] => true
      | _ => false
  , assertion := λ _ =>
      match dc.salient.filter restrictor with
      | [e] => scope e
      | _ => false }

/-- Familiarity presupposition requires discourse salience, not world-relative
uniqueness. The same restrictor can succeed under familiarity but fail under
uniqueness (if multiple entities satisfy the restrictor in the world but only
one is discourse-salient). -/
theorem familiarity_weaker_existence {E : Type} [DecidableEq E]
    (dc : DiscourseContext E) (restrictor : E → Bool) (scope : E → Bool)
    (e : E) (h_sal : dc.salient.filter restrictor = [e]) :
    (the_fam dc restrictor scope).presup () = true := by
  simp only [the_fam, h_sal]

-- ============================================================================
-- §3: Bridge to Donnellan (definitePrProp)
-- ============================================================================

/-- The uniqueness-based definite IS Donnellan's attributive semantics.

`the_uniq_w` and `definitePrProp` compute identical presuppositions
and assertions. Both filter the domain for unique restrictor-satisfiers. -/
theorem the_uniq_eq_definitePrProp {W E : Type} (domain : List E)
    (restrictor : E → W → Bool) (scope : E → W → Bool) :
    the_uniq_w domain restrictor scope = definitePrProp domain restrictor scope :=
  rfl

-- ============================================================================
-- §4: Bridge to Partee's ι (TypeShifting.iota)
-- ============================================================================

/-- The uniqueness presupposition holds iff Partee's ι succeeds.

`iota domain P = some e` exactly when the uniqueness presupposition
of `the_uniq` is satisfied. The ι-operator is the presupposition-free
core of the uniqueness-based definite. -/
theorem the_uniq_presup_iff_iota {m : Model} (domain : List m.Entity)
    (restrictor : m.interpTy Ty.et) :
    (match domain.filter restrictor with | [_] => true | _ => false) =
    (iota domain restrictor).isSome := by
  simp only [iota]
  cases h : domain.filter restrictor with
  | nil => simp
  | cons hd tl =>
    cases tl with
    | nil => simp
    | cons hd' tl' => simp

-- ============================================================================
-- §5: Bridge to every_sem (⟦the⟧ = ⟦every⟧ on singletons)
-- ============================================================================

/-- ⟦the⟧ agrees with ⟦every⟧ when the restrictor is a singleton.

When exactly one entity satisfies the restrictor, "the φ is ψ" and
"every φ is ψ" have the same truth value. This is the classical
observation that the definite article is a universal quantifier
restricted to singletons (Barwise & Cooper 1981).

TODO: prove by unfolding `every_sem` and showing that `∀x. R(x) → S(x)`
reduces to `S(e)` when `R` is the singleton `{e}`. Requires showing that
`elements.all (λ x => !restrictor x || scope x)` = `scope e` when
`elements.filter restrictor = [e]`. -/
theorem the_is_every_on_singletons (m : Model) [FiniteModel m]
    (restrictor scope : m.interpTy Ty.et)
    (e : m.Entity)
    (h_singleton : FiniteModel.elements.filter restrictor = [e]) :
    every_sem m restrictor scope = scope e := by
  simp only [every_sem]
  have h_restr : restrictor e = true := by
    have : e ∈ FiniteModel.elements.filter restrictor := by
      rw [h_singleton]; exact .head _
    exact (List.mem_filter.mp this).2
  have h_unique : ∀ x ∈ (@FiniteModel.elements m _), restrictor x = true → x = e := by
    intro x hx hr
    have hmem : x ∈ FiniteModel.elements.filter restrictor := List.mem_filter.mpr ⟨hx, hr⟩
    rw [h_singleton] at hmem
    cases hmem with
    | head => rfl
    | tail _ h => nomatch h
  cases hse : scope e with
  | false =>
    -- e ∈ elements and (!restrictor e || scope e) = false, so all must be false
    cases h : FiniteModel.elements.all (fun x => !restrictor x || scope x) with
    | false => rfl
    | true =>
      exfalso
      have h1 := List.all_eq_true.mp h e (FiniteModel.complete e)
      rw [h_restr, hse] at h1
      exact Bool.noConfusion h1
  | true =>
    have hall : FiniteModel.elements.all (fun x => !restrictor x || scope x) = true := by
      rw [List.all_eq_true]
      intro x hx
      cases hr : restrictor x with
      | false => rfl
      | true =>
        have hxe := h_unique x hx hr
        rw [congrArg scope hxe, hse]; rfl
    rw [hall]

-- ============================================================================
-- §6: Bridge to Fragments/English/Determiners.lean
-- ============================================================================

open Fragments.English.Determiners (QForce QuantifierEntry)

/-- English "the" is QForce.definite — our semantics provides its denotation.

The lexical entry in `Fragments/English/Determiners.lean` records `the`
as `QForce.definite`. Our `the_uniq` provides the compositional semantics
that was previously missing: `the` denotes a presuppositional determiner
that presupposes existence+uniqueness and asserts the scope.

Since English has only one article form (ArticleType.weakOnly), the
default semantics is uniqueness-based. The familiarity reading arises
pragmatically (accommodation) rather than structurally. -/
def qforceToPresupType : QForce → Option DefPresupType
  | .definite => some .uniqueness  -- Default: uniqueness (English = weak-only)
  | _ => none                       -- Non-definite determiners: no presupposition type

/-- `QForce.definite` maps to uniqueness by default. -/
theorem definite_is_uniqueness :
    qforceToPresupType .definite = some .uniqueness := rfl

/-- Map QForce to Definiteness. -/
def qforceToDefiniteness : QForce → Definiteness
  | .existential  => .indefinite
  | .definite     => .definite
  | .universal    => .definite   -- "every" presupposes non-empty domain
  | .negative     => .indefinite -- "no" is existential (negative)
  | .proportional => .indefinite -- "most" is proportional (no presupposition)

end Semantics.Lexical.Determiner.Definite
