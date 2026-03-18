import Linglib.Theories.Semantics.Lexical.Determiner.Quantifier
import Linglib.Theories.Semantics.Composition.TypeShifting
import Linglib.Theories.Semantics.Reference.Donnellan
import Linglib.Core.Semantics.Presupposition
import Linglib.Core.Definiteness
import Linglib.Fragments.English.Determiners

/-!
# The Semantics of Definiteness
@cite{donnellan-1966} @cite{heim-1982} @cite{kamp-1981} @cite{partee-1987} @cite{russell-1905} @cite{barwise-cooper-1981}

Denotations for definite descriptions using the type vocabulary from
`Core/Definiteness.lean`. Two theories, formalized as determiner denotations
with presuppositions:

- **Uniqueness**: "the φ" presupposes
  existence and uniqueness of a φ-entity; asserts predication of that entity.
- **Familiarity**: "the φ" presupposes that a φ-entity
  is already familiar/salient in the discourse; asserts predication of it.

## Key Results

- `the_uniq`: ⟦the⟧ under uniqueness (Russell/Strawson)
- `the_fam`: ⟦the⟧ under familiarity (Heim/Kamp)
- `the_uniq_eq_definitePrProp`: uniqueness = Donnellan's attributive semantics
- `the_uniq_presup_iff_iota`: uniqueness presup ↔ Partee's ι succeeds
- `the_is_every_on_singletons`: ⟦the⟧ = ⟦every⟧ on singleton restrictors

-/

namespace Semantics.Lexical.Determiner.Definite

open Semantics.Montague (Model Ty toyModel ToyEntity)
open Semantics.Lexical.Determiner.Quantifier (every_sem some_sem Ty.det)
open Semantics.Composition.TypeShifting (iota lift)
open Core.Presupposition (PrProp)
open Core.Definiteness (DefPresupType Definiteness)
open Semantics.Reference.Donnellan (definitePrProp attributiveContent)

-- ============================================================================
-- §1: Uniqueness-Based Definite (Weak Article)
-- ============================================================================

/-- ⟦the⟧ under uniqueness (Russell/Strawson/@cite{heim-kratzer-1998}):

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
This is the standard @cite{heim-kratzer-1998} entry. -/
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

@cite{heim-1982}: the context is a set of "file cards" — entities that have
been introduced into the discourse and are available for anaphoric reference. -/
structure DiscourseContext (E : Type) where
  /-- Entities currently salient/familiar in discourse -/
  salient : List E

/-- ⟦the⟧ under familiarity:

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
restricted to singletons. -/
theorem the_is_every_on_singletons (m : Model) [Fintype m.Entity]
    (restrictor scope : m.Entity → Bool)
    (e : m.Entity)
    (h_restr : restrictor e = true)
    (h_unique : ∀ x, restrictor x = true → x = e) :
    every_sem m restrictor scope = scope e := by
  simp only [every_sem]
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  constructor
  · intro h; exact h e h_restr
  · intro hse x hRx; rw [h_unique x hRx]; exact hse

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

-- ============================================================================
-- §7: Modifier Necessity
-- ============================================================================

/-- A modifier is **referentially necessary** in a domain when the bare
    restrictor fails to uniquely identify a referent but the modified
    (intersected) restrictor succeeds.

    This captures the shared mechanism underlying:
    - **Contrastive inference** (@cite{sedivy-etal-1999}): a scalar adjective
      is informative when a same-category competitor is present
    - **Context-sensitive attachment** (@cite{paape-vasishth-2026}): an RC
      modifier is pragmatically licensed when multiple potential referents
      make the bare definite ambiguous

    In both cases, the modifier rescues a failed uniqueness presupposition. -/
def modifierNecessary {E : Type}
    (domain : List E) (restrictor modifier : E → Bool) : Bool :=
  match domain.filter restrictor with
  | [_] => false  -- bare NP already uniquely identifies; modifier redundant
  | _ => match domain.filter (fun e => restrictor e && modifier e) with
    | [_] => true   -- modifier rescues uniqueness
    | _ => false    -- modifier doesn't help

end Semantics.Lexical.Determiner.Definite
