import Linglib.Semantics.Quantification.Quantifier
import Linglib.Semantics.Composition.TypeShifting
import Linglib.Semantics.Reference.Donnellan
import Linglib.Semantics.Presupposition.Basic
import Linglib.Features.Definiteness
import Linglib.Semantics.Definiteness.Maximality
import Linglib.Fragments.English.Determiners

/-!
# The Semantics of Definiteness
[donnellan-1966] [heim-1982] [kamp-1981] [moroney-2021] [partee-1987] [russell-1905] [schwarz-2009] [barwise-cooper-1981]

Connective tissue between definite-description denotations and the rest of
the library. The denotational layer itself lives in two canonical pieces:

- `Semantics.Definiteness.russellIotaList` (the per-context referent selector,
  Russellian iota over a `List E` filtered by a `Bool` predicate), and
- `Semantics.Presupposition.PrProp.presupOfReferent` (the combinator lifting a
  referent selector and a scope predicate into a `PrProp W`).

All variants — uniqueness-based, familiarity-based, anaphoric (ι^x),
discourse-restricted, situation-relative — are obtained by composing these
two pieces with different referent-selector arguments. There are no named
wrappers (`the_uniq`, `the_fam`, `the_anaphoric`) at the library level;
consumer files compose the two canonical pieces directly, optionally with
a file-local convenience definition where one is used repeatedly.

This module retains:

- `DiscourseContext` — the file-card record from [heim-1982]
- `qforceToPresupType` / `qforceToDefiniteness` — bridges from the English
  Determiner fragment to the definiteness type vocabulary
- `the_is_every_on_singletons` — the classical observation that ⟦the⟧
  agrees with ⟦every⟧ on singleton restrictors
- `modifierNecessary` — abstract predicate capturing referential necessity
  of a modifier, shared between contrastive inference
  ([sedivy-etal-1999]) and context-sensitive attachment
  ([paape-vasishth-2026])

-/

namespace Semantics.Definiteness

open Core.Logic.Intensional (Ty)
open Semantics.Quantification.Quantifier (every_sem some_sem Ty.det)
open Semantics.Composition.TypeShifting (iota lift)
open Semantics.Presupposition (PrProp)
open Features.Definiteness (DefPresupType Definiteness)

-- ============================================================================
-- §1: Discourse Context
-- ============================================================================

/-- A discourse context tracking salient/familiar entities.

[heim-1982]: the context is a set of "file cards" — entities that have
been introduced into the discourse and are available for anaphoric reference.
Familiarity-based definites (Schwarz's strong article) are evaluated by
running the canonical Russellian-iota selector
(`Semantics.Definiteness.russellIotaList`) over `dc.salient` rather than the full
domain. -/
structure DiscourseContext (E : Type) where
  /-- Entities currently salient/familiar in discourse -/
  salient : List E

-- ============================================================================
-- §2: Bridge to Partee's ι (TypeShifting.iota)
-- ============================================================================

/-- The uniqueness presupposition of a definite description holds iff
Partee's `iota` succeeds on the same domain and restrictor. Both check
that `domain.filter restrictor` is a singleton; one returns `Bool` (the
presupposition flag), the other returns `Option E` (the witness). -/
theorem definite_presup_iff_iota {E : Type} (domain : List E)
    (restrictor : E → Prop) :
    (match domain.filter (fun x => @decide (restrictor x) (Classical.dec _)) with
     | [_] => true | _ => false) =
    (iota domain restrictor).isSome := by
  unfold iota
  generalize domain.filter (fun x => @decide (restrictor x) (Classical.dec _)) = l
  match l with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

-- ============================================================================
-- §3: Bridge to every_sem (⟦the⟧ = ⟦every⟧ on singletons)
-- ============================================================================

/-- ⟦the⟧ agrees with ⟦every⟧ when the restrictor is a singleton.

When exactly one entity satisfies the restrictor, "the φ is ψ" and
"every φ is ψ" have the same truth value. This is the classical
observation that the definite article is a universal quantifier
restricted to singletons. -/
theorem the_is_every_on_singletons {α : Type*}
    (restrictor scope : α → Prop)
    (e : α)
    (h_restr : restrictor e)
    (h_unique : ∀ x, restrictor x → x = e) :
    every_sem restrictor scope ↔ scope e := by
  constructor
  · intro h; exact h e h_restr
  · intro hse x hRx; rw [h_unique x hRx]; exact hse

-- ============================================================================
-- §4: Bridge to Fragments/English/Determiners.lean
-- ============================================================================

open English.Determiners (QForce QuantifierEntry)

/-- English "the" is `QForce.definite` — its denotation is given by
composing `presupOfReferent` with `russellIotaList domain restrictor`
(uniqueness-based, since English is `ArticleType.weakOnly`). The
familiarity reading arises pragmatically (accommodation) rather than
structurally. -/
def qforceToPresupType : QForce → Option DefPresupType
  | .definite => some .uniqueness
  | _ => none

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
-- §5: Modifier Necessity
-- ============================================================================

/-- A modifier is **referentially necessary** in a domain when the bare
    restrictor fails to uniquely identify a referent but the modified
    (intersected) restrictor succeeds.

    This captures the shared mechanism underlying:
    - **Contrastive inference** ([sedivy-etal-1999]): a scalar adjective
      is informative when a same-category competitor is present
    - **Context-sensitive attachment** ([paape-vasishth-2026]): an RC
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
