import Linglib.Syntax.HPSG.Signature
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic

/-!
# RSRL interpretations

This file defines the interpretations of an RSRL signature. An interpretation over a universe
`U` of entities assigns a sort to every entity, a partial function on entities to every
attribute, and a set of tuples of entities to every relation symbol. A term then denotes a
partial function on entities, and the components of an entity are the entities that some path
reaches from it.

## Main definitions

* `HPSG.RSRL.Interpretation`: an interpretation of a signature over a universe `U`.
* `HPSG.RSRL.Interpretation.termDenot`: the term interpretation function under a variable
  assignment.
* `HPSG.RSRL.Interpretation.IsComponentOf`: the component relation between entities.
* `HPSG.RSRL.Interpretation.WellTyped`: the interpretation is sort-resolved and totally
  well-typed.

## Main results

* `HPSG.RSRL.Interpretation.isComponentOf_iff_exists_path`: the components of an entity are the
  denotations of the paths that are defined on it.
* `HPSG.RSRL.Interpretation.termDenot_congr`: a term denotation depends only on the values that
  the assignment gives to the variables of the term.

## Implementation notes

The universe is a parameter of `Interpretation` rather than a field, as the carrier of a
first-order structure is in mathlib, so that `Fintype` and `DecidableEq` instances on the
universe are found without any per-model declaration.

Richter builds sort resolution and total well-typedness into the definition of an
interpretation. Here they form the separate predicate `WellTyped`, because a worked example
usually interprets only the part of a feature structure that the principle under test mentions.
Richter also restricts the tuples of a relation to entities that are components of one common
entity. That restriction is not imposed.

## References

* [richter-2000]
* [richter-2024]
-/

namespace HPSG.RSRL

universe u v

/-- An interpretation of the signature `Sig` over the universe `U`
([richter-2024], Definition 7). -/
structure Interpretation {Srt : Type u} [PartialOrder Srt] (Sig : Signature Srt)
    (U : Type v) where
  /-- The sort of each entity. -/
  S : U → Srt
  /-- The partial function on entities that interprets each attribute. -/
  A : Sig.Attr → U → Option U
  /-- The set of argument tuples that interprets each relation symbol. -/
  R : (ρ : Sig.Rel) → Set (Fin (Sig.arity ρ) → U)

namespace Interpretation

variable {Srt : Type u} [PartialOrder Srt] {Sig : Signature Srt} {U : Type v}
  (I : Interpretation Sig U)

/-! ### Term denotation -/

/-- The entity that a term denotes at the described entity `u` under the assignment `g`, when
every attribute along the term is defined ([richter-2024], Definition 10). -/
def termDenot (g : ℕ → U) : Term Sig → U → Option U
  | .colon, u => some u
  | .var n, _ => some (g n)
  | .feat t α, u => (termDenot g t u).bind (I.A α)

variable {I} {g g' : ℕ → U} {u v : U}

@[simp] theorem termDenot_colon : I.termDenot g .colon u = some u := rfl

@[simp] theorem termDenot_var (n : ℕ) : I.termDenot g (.var n) u = some (g n) := rfl

@[simp] theorem termDenot_feat (t : Term Sig) (α : Sig.Attr) :
    I.termDenot g (t.feat α) u = (I.termDenot g t u).bind (I.A α) := rfl

/-- A term denotation depends only on the values of the variables that occur in the term. -/
theorem termDenot_congr {t : Term Sig} (h : ∀ x ∈ t.freeVars, g x = g' x) :
    I.termDenot g t u = I.termDenot g' t u := by
  induction t with
  | colon => rfl
  | var n => simp [h n (Finset.mem_singleton_self n)]
  | feat t α ih => rw [termDenot_feat, termDenot_feat, ih h]

/-- The denotation of a path does not depend on the assignment. -/
theorem termDenot_path (g g' : ℕ → U) (p : Path Sig) :
    I.termDenot g (.path p) u = I.termDenot g' (.path p) u :=
  termDenot_congr (by simp)

/-! ### Components -/

variable (I) in
/-- The entity `v` is the value of some attribute at `u`. -/
def attrSucc (u v : U) : Prop := ∃ α : Sig.Attr, I.A α u = some v

instance [Fintype Sig.Attr] [DecidableEq U] : DecidableRel I.attrSucc :=
  fun _ _ ↦ by unfold attrSucc; infer_instance

variable (I) in
/-- The entity `v` is a component of `u` when a sequence of attributes leads from `u` to `v`.
Quantification in RSRL ranges over the components of the described entity. -/
abbrev IsComponentOf (u v : U) : Prop := Relation.ReflTransGen I.attrSucc u v

instance [Fintype U] [DecidableEq U] [Fintype Sig.Attr] (u v : U) :
    Decidable (I.IsComponentOf u v) :=
  Relation.ReflTransGen.decidable_of_fintype u v

/-- The components of `u` are the entities that some path denotes at `u`
([richter-2024], Definition 11). -/
theorem isComponentOf_iff_exists_path (g : ℕ → U) :
    I.IsComponentOf u v ↔ ∃ p : Path Sig, I.termDenot g (.path p) u = some v := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], rfl⟩
    | tail _ hα ih =>
      obtain ⟨α, hα⟩ := hα
      obtain ⟨p, hp⟩ := ih
      exact ⟨p ++ [α], by rw [Term.path_concat, termDenot_feat, hp]; exact hα⟩
  · rintro ⟨p, hp⟩
    induction p using List.reverseRecOn generalizing v with
    | nil => cases hp; exact .refl
    | append_singleton p α ih =>
      rw [Term.path_concat, termDenot_feat, Option.bind_eq_some_iff] at hp
      obtain ⟨w, hw, hα⟩ := hp
      exact (ih hw).tail ⟨α, hα⟩

/-! ### Well-typedness -/

variable (I) in
/-- An interpretation is well-typed when every entity has a species as its sort and the
attributes are defined exactly where the signature makes them appropriate, with values of the
appropriate sort. -/
structure WellTyped : Prop where
  /-- The sort of every entity is a species. -/
  species : ∀ u, IsSpecies (I.S u)
  /-- An attribute is defined on an entity exactly when it is appropriate to the entity's
  sort. -/
  appropDefined : ∀ (α : Sig.Attr) (u : U), (I.A α u).isSome = (Sig.approp (I.S u) α).isSome
  /-- The sort of an attribute value is at least as specific as the appropriate value sort. -/
  appropSort : ∀ (α : Sig.Attr) (u v : U), I.A α u = some v →
    ∀ τ ∈ Sig.approp (I.S u) α, I.S v ≤ τ

instance [Fintype Srt] [DecidableLE Srt] (σ : Srt) : Decidable (IsSpecies σ) :=
  inferInstanceAs (Decidable (∀ b, b ≤ σ → σ ≤ b))

instance [Fintype Srt] [DecidableLE Srt] [Fintype U] [DecidableEq U] [Fintype Sig.Attr] :
    Decidable I.WellTyped :=
  decidable_of_iff
    ((∀ u, IsSpecies (I.S u)) ∧
      (∀ (α : Sig.Attr) (u : U), (I.A α u).isSome = (Sig.approp (I.S u) α).isSome) ∧
      (∀ (α : Sig.Attr) (u v : U), I.A α u = some v → ∀ τ ∈ Sig.approp (I.S u) α, I.S v ≤ τ))
    ⟨fun ⟨a, b, c⟩ ↦ ⟨a, b, c⟩, fun ⟨a, b, c⟩ ↦ ⟨a, b, c⟩⟩

/-- The relations of an interpretation are decidable when the signature has no relation
symbols. -/
instance [IsEmpty Sig.Rel] (ρ : Sig.Rel) : DecidablePred (I.R ρ) := isEmptyElim ρ

end Interpretation

end HPSG.RSRL
