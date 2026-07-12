/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Logic.Relation
import Mathlib.Logic.Equiv.Basic

/-!
# Labeled mixed graphs — the autosegmental foundation

A labeled mixed graph `⟨V, E, A, ℓ⟩` ([jardine-heinz-2015] §2; [jardine-2016-diss]
§4.1) is the literature's most general autosegmental object: labeled nodes, a
symmetric association relation `E`, and a directed precedence relation `A`.
Rendered as pure relations over a vertex-type parameter (the `SimpleGraph`
pattern), it is a finite relational structure in the model-theoretic-phonology
sense — unary label predicates plus two binary relations — the format in which
notational-equivalence results are proved ([jardine-danis-iacoponi-2021],
[oakden-2020]). Nothing else is stored: in particular no ambient cross-tier
order, which is structure the object does not have.

Tiers are not part of the object. A tier assignment `t : S → ι` on the alphabet
induces the node partition, and [jardine-2016-diss] §4.2's well-formedness axioms
carve the autosegmental representations out of the raw graphs relative to it.

Concatenation is [jardine-heinz-2015] Definition 2 *minus its `R_ID` melody
merge* (the OCP repair, modeled separately as `OCP.collapse`, matching
`AR.lean`): the sum of the vertex types with, per tier class, bridging arcs from
the first factor's precedence-maximal nodes to the second factor's
precedence-minimal ones. The monoid laws hold up to structure-preserving
equivalence (`MixedGraph.Iso`), not up to equality — strictness belongs to the
tiered normal form, not to the foundation.

## Main definitions

* `MixedGraph V S`: association `Assoc` (symmetric), precedence `Prec`,
  labeling `label : V → S`; `PrecPath` is the transitive closure of `Prec`.
* The [jardine-2016-diss] §4.2 axioms, relative to a tier assignment where tiers
  matter: `IsTierOrdered` (Axioms 1–2), `NoInternalAssoc` (Axiom 3),
  `IsSaturated` (Axiom 4 — stated, deliberately not imposed, as in `AR.lean`),
  `IsPlanar` (Axiom 5, the No-Crossing Constraint in its general path form),
  `IsOCPClean` (Axiom 6).
* `MixedGraph.Iso`: label- and relation-preserving equivalence.
* `MixedGraph.concat t`: tier-bridging concatenation on the vertex sum.

## Main results

* `concat_empty_iso` / `empty_concat_iso`: the unit laws up to `Iso`
  ([jardine-heinz-2015] Theorem 1).

## TODO

* Associativity up to `Iso` ([jardine-heinz-2015] Theorem 3; conditional on the
  tier classes being precedence chains, per the paper's Lemma 1 remark).
* Axiom preservation under `concat` ([jardine-heinz-2015] Theorem 4 and its
  Axiom 1–3 analogues).
* The normal-form equivalence: every graph satisfying Axioms 1–3 is isomorphic
  to a tier-indexed family of `LabeledTuple`s with per-pair links — the strict
  tiered presentation `MultiAR` builds on — with `IsPlanar` reducing to the
  per-pair NCC.
-/

namespace Autosegmental

variable {V V₁ V₂ V₃ S ι : Type*}

/-- A labeled mixed graph `⟨V, E, A, ℓ⟩`: a symmetric association relation, a
    directed precedence relation, and a labeling of the vertices. -/
structure MixedGraph (V S : Type*) where
  /-- The association relation (`E`), undirected. -/
  Assoc : V → V → Prop
  /-- Association is symmetric. -/
  assoc_symm : Std.Symm Assoc
  /-- The precedence relation (`A`), directed. -/
  Prec : V → V → Prop
  /-- The labeling (`ℓ`). -/
  label : V → S

namespace MixedGraph

/-- The precedence-path relation: the transitive closure of `Prec`. -/
def PrecPath (G : MixedGraph V S) : V → V → Prop := Relation.TransGen G.Prec

/-- The tier of a vertex under a tier assignment on the alphabet. -/
def tier (t : S → ι) (G : MixedGraph V S) (v : V) : ι := t (G.label v)

/-! ### The §4.2 axioms -/

section Axioms
variable (t : S → ι) (G : MixedGraph V S)

/-- Axioms 1–2 ([jardine-2016-diss] §4.2): precedence stays within a tier,
    precedence paths totally order each tier class, and no path returns to its
    origin. -/
def IsTierOrdered : Prop :=
  (∀ ⦃v w⦄, G.Prec v w → G.tier t v = G.tier t w) ∧
    (∀ ⦃v w⦄, v ≠ w → G.tier t v = G.tier t w → G.PrecPath v w ∨ G.PrecPath w v) ∧
    ∀ v, ¬ G.PrecPath v v

/-- Axiom 3: association never links precedence-path-related (tier-internal)
    vertices. Tier-free — stated on paths alone, as in the dissertation. -/
def NoInternalAssoc : Prop := ∀ ⦃v w⦄, G.Assoc v w → ¬ G.PrecPath v w

/-- Axiom 4 (full specification): every vertex participates in an association.
    [goldsmith-1976]'s original well-formedness condition; stated but
    deliberately not imposed — floating elements are well-formed, as in
    `AR.lean`. -/
def IsSaturated : Prop := ∀ v, ∃ w, G.Assoc v w

/-- Axiom 5, the No-Crossing Constraint in [jardine-2016-diss]'s general path
    form: no two association edges whose endpoints straddle in opposite
    precedence order. -/
def IsPlanar : Prop :=
  ∀ ⦃v v' w w'⦄, G.Assoc v v' → G.Assoc w w' → G.PrecPath v w → ¬ G.PrecPath w' v'

/-- Axiom 6, the OCP on melody tier `m`: precedence-adjacent vertices on `m`
    bear distinct labels. -/
def IsOCPClean (m : ι) : Prop :=
  ∀ ⦃v w⦄, G.Prec v w → G.tier t v = m → G.label v ≠ G.label w

end Axioms

/-! ### Isomorphism -/

/-- A label- and relation-preserving equivalence of labeled mixed graphs. -/
structure Iso (G₁ : MixedGraph V₁ S) (G₂ : MixedGraph V₂ S) extends V₁ ≃ V₂ where
  assoc_iff : ∀ v w, G₂.Assoc (toEquiv v) (toEquiv w) ↔ G₁.Assoc v w
  prec_iff : ∀ v w, G₂.Prec (toEquiv v) (toEquiv w) ↔ G₁.Prec v w
  label_comp : ∀ v, G₂.label (toEquiv v) = G₁.label v

/-- The identity isomorphism. -/
def Iso.refl (G : MixedGraph V S) : Iso G G :=
  ⟨Equiv.refl V, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => rfl⟩

/-- Inverse isomorphism. -/
def Iso.symm {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S} (e : Iso G₁ G₂) : Iso G₂ G₁ where
  toEquiv := e.toEquiv.symm
  assoc_iff v w := by
    conv_rhs => rw [show v = e.toEquiv (e.toEquiv.symm v) from (e.toEquiv.apply_symm_apply v).symm,
      show w = e.toEquiv (e.toEquiv.symm w) from (e.toEquiv.apply_symm_apply w).symm]
    exact (e.assoc_iff _ _).symm
  prec_iff v w := by
    conv_rhs => rw [show v = e.toEquiv (e.toEquiv.symm v) from (e.toEquiv.apply_symm_apply v).symm,
      show w = e.toEquiv (e.toEquiv.symm w) from (e.toEquiv.apply_symm_apply w).symm]
    exact (e.prec_iff _ _).symm
  label_comp v := by
    conv_rhs => rw [show v = e.toEquiv (e.toEquiv.symm v) from (e.toEquiv.apply_symm_apply v).symm]
    exact (e.label_comp _).symm

/-- Composition of isomorphisms. -/
def Iso.trans {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S} {G₃ : MixedGraph V₃ S}
    (e : Iso G₁ G₂) (f : Iso G₂ G₃) : Iso G₁ G₃ where
  toEquiv := e.toEquiv.trans f.toEquiv
  assoc_iff v w := (f.assoc_iff _ _).trans (e.assoc_iff v w)
  prec_iff v w := (f.prec_iff _ _).trans (e.prec_iff v w)
  label_comp v := (f.label_comp _).trans (e.label_comp v)

/-! ### The empty graph -/

/-- The empty mixed graph, on the empty vertex type. -/
def empty (S : Type*) : MixedGraph PEmpty S where
  Assoc _ _ := False
  assoc_symm := ⟨fun _ _ h => h.elim⟩
  Prec _ _ := False
  label v := v.elim

/-! ### Tier-bridging concatenation

Per tier class, concatenation adds bridging arcs from the first factor's
precedence-maximal vertices of that class to the second factor's
precedence-minimal ones. On graphs whose tier classes are precedence chains
(Axioms 1–2) this is [jardine-heinz-2015]'s last-to-first bridge; on raw graphs
it is total (a maximal-to-minimal complete bridge), where the paper's
`first`/`last` are partial. -/

section Concat
variable (t : S → ι)

/-- `v` is precedence-maximal within its tier class. -/
def IsTierMax (G : MixedGraph V S) (v : V) : Prop :=
  ∀ ⦃w⦄, G.tier t w = G.tier t v → ¬ G.PrecPath v w

/-- `v` is precedence-minimal within its tier class. -/
def IsTierMin (G : MixedGraph V S) (v : V) : Prop :=
  ∀ ⦃w⦄, G.tier t w = G.tier t v → ¬ G.PrecPath w v

/-- Concatenation ([jardine-heinz-2015] Definition 2, minus the `R_ID` melody
    merge): the vertex sum, with association and precedence inherited blockwise
    and a bridging arc from each tier-maximal vertex of `G₁` to each same-tier
    tier-minimal vertex of `G₂`. -/
def concat (G₁ : MixedGraph V₁ S) (G₂ : MixedGraph V₂ S) : MixedGraph (V₁ ⊕ V₂) S where
  Assoc v w :=
    match v, w with
    | .inl v, .inl w => G₁.Assoc v w
    | .inr v, .inr w => G₂.Assoc v w
    | _, _ => False
  assoc_symm := ⟨by
    intro v w h
    cases v <;> cases w <;> simp_all only
    exacts [G₁.assoc_symm.symm _ _ h, G₂.assoc_symm.symm _ _ h]⟩
  Prec v w :=
    match v, w with
    | .inl v, .inl w => G₁.Prec v w
    | .inr v, .inr w => G₂.Prec v w
    | .inl v, .inr w =>
        G₁.tier t v = G₂.tier t w ∧ IsTierMax t G₁ v ∧ IsTierMin t G₂ w
    | .inr _, .inl _ => False
  label := Sum.elim G₁.label G₂.label

@[simp] theorem concat_label_inl (G₁ : MixedGraph V₁ S) (G₂ : MixedGraph V₂ S) (v : V₁) :
    (concat t G₁ G₂).label (.inl v) = G₁.label v := rfl

@[simp] theorem concat_label_inr (G₁ : MixedGraph V₁ S) (G₂ : MixedGraph V₂ S) (v : V₂) :
    (concat t G₁ G₂).label (.inr v) = G₂.label v := rfl

@[simp] theorem concat_assoc_inl_inl {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S} {v w : V₁} :
    (concat t G₁ G₂).Assoc (.inl v) (.inl w) ↔ G₁.Assoc v w := Iff.rfl

@[simp] theorem concat_assoc_inr_inr {G₁ : MixedGraph V₁ S} {G₂ : MixedGraph V₂ S} {v w : V₂} :
    (concat t G₁ G₂).Assoc (.inr v) (.inr w) ↔ G₂.Assoc v w := Iff.rfl

/-! ### Unit laws ([jardine-heinz-2015] Theorem 1) -/

/-- Concatenation with the empty graph on the right, up to isomorphism. -/
def concat_empty_iso (G : MixedGraph V S) : Iso (concat t G (empty S)) G where
  toEquiv := Equiv.sumEmpty V PEmpty
  assoc_iff v w := by
    rcases v with v | v
    · rcases w with w | w
      · exact Iff.rfl
      · exact w.elim
    · exact v.elim
  prec_iff v w := by
    rcases v with v | v
    · rcases w with w | w
      · exact Iff.rfl
      · exact w.elim
    · exact v.elim
  label_comp v := by
    rcases v with v | v
    · rfl
    · exact v.elim

/-- Concatenation with the empty graph on the left, up to isomorphism. -/
def empty_concat_iso (G : MixedGraph V S) : Iso (concat t (empty S) G) G where
  toEquiv := Equiv.emptySum PEmpty V
  assoc_iff v w := by
    rcases v with v | v
    · exact v.elim
    · rcases w with w | w
      · exact w.elim
      · exact Iff.rfl
  prec_iff v w := by
    rcases v with v | v
    · exact v.elim
    · rcases w with w | w
      · exact w.elim
      · exact Iff.rfl
  label_comp v := by
    rcases v with v | v
    · exact v.elim
    · rfl

end Concat

end MixedGraph

end Autosegmental
