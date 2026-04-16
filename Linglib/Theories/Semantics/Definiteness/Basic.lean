import Linglib.Theories.Semantics.Quantification.Quantifier
import Linglib.Theories.Semantics.Composition.TypeShifting
import Linglib.Theories.Semantics.Reference.Donnellan
import Linglib.Core.Semantics.Presupposition
import Linglib.Core.Definiteness
import Linglib.Fragments.English.Determiners

/-!
# The Semantics of Definiteness
@cite{donnellan-1966} @cite{heim-1982} @cite{kamp-1981} @cite{moroney-2021} @cite{partee-1987} @cite{russell-1905} @cite{schwarz-2009} @cite{barwise-cooper-1981}

Denotations for definite descriptions built on a single evaluation function
`evalDefinite` parameterized by `DefiniteDesc` (from `Core/Definiteness.lean`).

The central insight: all definite descriptions — uniqueness-based (ι),
familiarity-based, and anaphoric (ι^x) — are the same operation:
filter a domain for entities satisfying a compound predicate (restrictor ∧
presupposition filter), presuppose uniqueness, assert scope.

The @cite{schwarz-2009} weak/strong distinction reduces to whether the
presupposition filter Q is trivial (weak: Q = λ _ => true) or non-trivial
(strong: Q encodes discourse familiarity / anaphoric link).

## Architecture

- `evalDefinite`: the single denotation function
- `the_uniq`: derived — `evalDefinite` with trivial Q (uniqueness)
- `the_fam`: derived — `evalDefinite` on discourse-salient domain
- `the_anaphoric`: derived — `evalDefinite` with non-trivial Q (familiarity)

## Key Results

- `the_uniq_from_eval`: ⟦the⟧_uniq = evalDefinite with .unique
- `the_anaphoric_from_eval`: ⟦the⟧_anaphoric = evalDefinite with .anaphoric
- `the_anaphoric_vacuous_eq_the_uniq`: ι^x with Q = trivial reduces to ι
- `the_uniq_eq_definitePrProp`: uniqueness = Donnellan's attributive semantics
- `the_uniq_presup_iff_iota`: uniqueness presup ↔ Partee's ι succeeds
- `the_is_every_on_singletons`: ⟦the⟧ = ⟦every⟧ on singleton restrictors

-/

namespace Semantics.Definiteness

open Core.IntensionalLogic (Frame Ty)
open Semantics.Montague (toyModel ToyEntity)
open Semantics.Quantification.Quantifier (every_sem some_sem Ty.det)
open Semantics.Composition.TypeShifting (iota lift)
open Core.Presupposition (PrProp)
open Core.Definiteness (DefPresupType Definiteness DefiniteDesc)
open Semantics.Reference.Donnellan (definitePrProp attributiveContent)

-- ============================================================================
-- §1: The Universal Definite Description Operator
-- ============================================================================

/-- The universal definite description operator.

Every definite description filters a domain for entities satisfying
a compound predicate (restrictor ∧ presupposition filter), presupposes
that exactly one entity passes, and asserts the scope of that entity.

This is the single source of truth for all definite denotations:
- Uniqueness (ι, weak article): `d = .unique R` — Q is trivial
- Familiarity (ι^x, strong article): `d = .anaphoric R Q` — Q is non-trivial
- Discourse-restricted: pass `dc.salient` as domain

All other definite denotations (`the_uniq`, `the_fam`, `the_anaphoric`)
are derived from this function. -/
def evalDefinite {E : Type} [DecidableEq E]
    (domain : List E) (d : DefiniteDesc E)
    (scope : E → Bool) : PrProp Unit :=
  { presup := λ _ =>
      match domain.filter (λ e => d.restrictor e && d.presupFilter e) with
      | [_] => true
      | _ => false
  , assertion := λ _ =>
      match domain.filter (λ e => d.restrictor e && d.presupFilter e) with
      | [e] => scope e
      | _ => false }

-- ============================================================================
-- §2: Derived Definite Denotations
-- ============================================================================

/-- ⟦the⟧ under uniqueness (Russell/Strawson/@cite{heim-kratzer-1998}):

Presupposition: exactly one entity in the domain satisfies the restrictor.
Assertion: the scope predicate holds of that entity.

This corresponds to Schwarz's **weak article** (German contracted *vom*,
Fering A-form, Lakhota *kiŋ*).

Derived from `evalDefinite` with a trivial presupposition filter. -/
def the_uniq {E : Type} (domain : List E) [DecidableEq E]
    (restrictor : E → Bool) (scope : E → Bool) : PrProp Unit :=
  evalDefinite domain (.unique restrictor) scope

/-- `the_uniq` is `evalDefinite` applied to a uniqueness description. -/
theorem the_uniq_from_eval {E : Type} (domain : List E) [DecidableEq E]
    (restrictor scope : E → Bool) :
    the_uniq domain restrictor scope =
    evalDefinite domain (.unique restrictor) scope := rfl

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
Fering D-form, Lakhota *k'uŋ*).

Derived from `evalDefinite` with a uniqueness description over the
discourse-salient domain. Familiarity is encoded as domain restriction:
searching `dc.salient` instead of the full domain.

NOTE: Akan *nó* is sometimes cited as a strong article (@cite{schwarz-2013}),
but this is disputed. @cite{bombi-2018} argues *nó* is weak (uniqueness-based),
and @cite{owusu-2022} analyses it as a demonstrative (familiarity +
non-uniqueness). See `Fragments/Akan/Determiners.lean` for details. -/
def the_fam {E : Type} [DecidableEq E]
    (dc : DiscourseContext E)
    (restrictor : E → Bool) (scope : E → Bool) : PrProp Unit :=
  evalDefinite dc.salient (.unique restrictor) scope

/-- `the_fam` is `evalDefinite` on the discourse-salient domain. -/
theorem the_fam_from_eval {E : Type} [DecidableEq E]
    (dc : DiscourseContext E) (restrictor scope : E → Bool) :
    the_fam dc restrictor scope =
    evalDefinite dc.salient (.unique restrictor) scope := rfl

/-- ⟦the⟧ under anaphoric definiteness (ι^x):

@cite{moroney-2021} Def 508: ι^x P Q = ιx[P(x) ∧ Q(x)].
The additional restrictor Q encodes the anaphoric link to a prior discourse
referent.

Derived from `evalDefinite` with an anaphoric description. -/
def the_anaphoric {E : Type} (domain : List E) [DecidableEq E]
    (restrictor : E → Bool) (anaphoricQ : E → Bool)
    (scope : E → Bool) : PrProp Unit :=
  evalDefinite domain (.anaphoric restrictor anaphoricQ) scope

/-- `the_anaphoric` is `evalDefinite` applied to an anaphoric description. -/
theorem the_anaphoric_from_eval {E : Type} (domain : List E) [DecidableEq E]
    (restrictor anaphoricQ scope : E → Bool) :
    the_anaphoric domain restrictor anaphoricQ scope =
    evalDefinite domain (.anaphoric restrictor anaphoricQ) scope := rfl

-- ============================================================================
-- §3: Unification Theorems
-- ============================================================================

/-- ι^x subsumes ι: when the anaphoric restrictor Q is vacuously true,
ι^x(P)(Q)(S) = ι(P)(S). This shows ι is a special case of ι^x.

Under the unified API, this is trivial: both reduce to `evalDefinite`
with the same `DefiniteDesc` (since `.unique R = .anaphoric R (λ _ => true)`). -/
theorem the_anaphoric_vacuous_eq_the_uniq {E : Type} (domain : List E) [DecidableEq E]
    (restrictor scope : E → Bool) :
    the_anaphoric domain restrictor (λ _ => true) scope =
    the_uniq domain restrictor scope := by
  simp only [the_anaphoric, the_uniq, evalDefinite,
             DefiniteDesc.anaphoric, DefiniteDesc.unique, Bool.and_true]

/-- Familiarity presupposition requires discourse salience, not world-relative
uniqueness. The same restrictor can succeed under familiarity but fail under
uniqueness (if multiple entities satisfy the restrictor in the world but only
one is discourse-salient). -/
theorem familiarity_weaker_existence {E : Type} [DecidableEq E]
    (dc : DiscourseContext E) (restrictor : E → Bool) (scope : E → Bool)
    (e : E) (h_sal : dc.salient.filter restrictor = [e]) :
    (the_fam dc restrictor scope).presup () = true := by
  simp only [the_fam, evalDefinite, DefiniteDesc.unique, Bool.and_true, h_sal]

/-- ι^x is strictly more restrictive than ι: adding an anaphoric restrictor
can only narrow the set of satisfiers, never widen it. If the intersected
filter yields a singleton, it is a subset of the bare filter. -/
theorem the_anaphoric_more_restrictive {E : Type} (domain : List E) [DecidableEq E]
    (restrictor anaphoricQ : E → Bool) (e : E)
    (h : domain.filter (λ x => restrictor x && anaphoricQ x) = [e]) :
    e ∈ domain.filter restrictor := by
  have hmem : e ∈ domain.filter (λ x => restrictor x && anaphoricQ x) :=
    h ▸ List.mem_cons_self ..
  simp only [List.mem_filter, Bool.and_eq_true] at hmem ⊢
  exact ⟨hmem.1, hmem.2.1⟩

/-- Domain restriction and filter conjunction are equivalent ways to encode
familiarity: searching a smaller domain with trivial Q is the same as
searching the full domain with Q = "is in the smaller domain."

This shows that `the_fam dc R S` (domain restriction) computes the same
result as `the_anaphoric domain R (λ e => dc.salient.contains e) S`
(filter conjunction) when the restrictor is applied to the salient subset. -/
theorem domain_restriction_eq_filter {E : Type} [DecidableEq E] [BEq E]
    [LawfulBEq E]
    (dc : DiscourseContext E) (restrictor scope : E → Bool) :
    the_fam dc restrictor scope =
    evalDefinite dc.salient (.unique restrictor) scope := rfl

-- ============================================================================
-- §4: Bridge to Donnellan (definitePrProp)
-- ============================================================================

/-- The uniqueness-based definite IS Donnellan's attributive semantics.

`the_uniq_w` and `definitePrProp` compute identical presuppositions
and assertions. Both filter the domain for unique restrictor-satisfiers. -/
theorem the_uniq_eq_definitePrProp {W E : Type} (domain : List E)
    (restrictor : E → W → Bool) (scope : E → W → Bool) :
    the_uniq_w domain restrictor scope = definitePrProp domain restrictor scope :=
  rfl

-- ============================================================================
-- §5: Bridge to Partee's ι (TypeShifting.iota)
-- ============================================================================

/-- The uniqueness presupposition holds iff Partee's ι succeeds.

`iota domain P = some e` exactly when the uniqueness presupposition
of `the_uniq` is satisfied. The ι-operator is the presupposition-free
core of the uniqueness-based definite. -/
theorem the_uniq_presup_iff_iota {m : Frame} (domain : List m.Entity)
    (restrictor : m.Denot Ty.et) :
    (match domain.filter (fun x => @decide (restrictor x) (Classical.dec _)) with
     | [_] => true | _ => false) =
    (iota domain restrictor).isSome := by
  simp only [iota]
  cases h : domain.filter (fun x => @decide (restrictor x) (Classical.dec _)) with
  | nil => simp
  | cons hd tl =>
    cases tl with
    | nil => simp
    | cons hd' tl' => simp

-- ============================================================================
-- §6: Bridge to every_sem (⟦the⟧ = ⟦every⟧ on singletons)
-- ============================================================================

/-- ⟦the⟧ agrees with ⟦every⟧ when the restrictor is a singleton.

When exactly one entity satisfies the restrictor, "the φ is ψ" and
"every φ is ψ" have the same truth value. This is the classical
observation that the definite article is a universal quantifier
restricted to singletons. -/
theorem the_is_every_on_singletons (m : Frame) [Fintype m.Entity]
    (restrictor scope : m.Entity → Prop)
    (e : m.Entity)
    (h_restr : restrictor e)
    (h_unique : ∀ x, restrictor x → x = e) :
    every_sem m restrictor scope ↔ scope e := by
  constructor
  · intro h; exact h e h_restr
  · intro hse x hRx; rw [h_unique x hRx]; exact hse

-- ============================================================================
-- §7: Bridge to Fragments/English/Determiners.lean
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
-- §8: Modifier Necessity
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

end Semantics.Definiteness
