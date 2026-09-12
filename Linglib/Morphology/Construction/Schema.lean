/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.Sum.Basic
import Linglib.Core.Order.PartialUnify
import Mathlib.Order.Lattice

/-!
# Constructional schemas

This file defines the schemas of Relational Morphology and Construction Morphology, lexical
entries with variables. A schema is a description indexed by slots, valued in a partial order
with a bottom element, together with the set of slots marked as open variables. A slot above
`⊥` is a constant and a slot at `⊥` is a variable, open or closed. An item instantiates a schema
when the description lies below it slot by slot, so the instances of a schema form the principal
upper set of its description, and instantiation is unification against the description.

A description over variables is read at positions through a subscripting of positions by
variables. Positions with the same subscript are coindexed and must be filled alike, so an item
over positions instantiates a schema when it is an instance read through the subscripting.
Two items are a paired instantiation, sister items, when their sum instantiates the schema
through the sum of their subscriptings; the relation is symmetric.

A schema plays two roles relative to a lexicon of stored items. In its relational role it
motivates an item already stored; in its generative role it licenses a possibly novel item whose
closed variables take only fillers attested among the stored instances. Every related item is
generated, every generated item is related once stored, and a schema is productive, every
variable open, exactly when it generates its own description over the empty lexicon.

Two items over one position space are the same except at a set of positions when they agree
off it, `Set.EqOn` on the complement, and what happens at those positions classifies the link
between them: an instantiation when the second strictly dominates the first there, the link
from a schema's description to its instances, and a contrast when the two are incompatible
there, the link between sister words. An elaboration, one item the same as the other plus
something else, is an instantiation read from the elaborated item. On a flat carrier a filled
item instantiates a schema exactly when it is the description, the same except at the
variables (`Schema.instantiates_iff_instantiation_of_forall_isMax`).

## Main declarations

* `Schema`: a slot-indexed description with a set of open variables.
* `Schema.Instantiates`, `Schema.instantiates_iff_unify`: instantiation as pointwise domination,
  equivalently as unification.
* `Schema.InstantiatesAt`, `Schema.instantiatesAt_iff`: instantiation at positions through a
  subscripting, as instantiation of the pulled-back description together with agreement at
  coindexed positions.
* `Schema.Relates`, `Schema.Generates`, `Schema.IsProductive`: the two roles of a schema and
  productivity.
* `Instantiation`, `Contrast`: the relational links, same except at a set of positions.
* `Schema.instantiates_inf_iff`, `Schema.instantiates_iff_of_unify_eq_some`: the meet of two
  items is their least general generalization, the Structural Intersection of Relational
  Morphology, and the unification of two descriptions has exactly their common instances.

## Implementation notes

Productivity is a property of variables rather than of a schema as a whole, so constants are
exempt from attestation and `Schema.IsProductive` is the case in which every variable is open.
Marking a constant slot as open has no effect.

## References

* [jackendoff-audring-2020]
* [culicover-jackendoff-2012]
* [booij-2010]
* [booij-2010-compass]
* [plotkin-1970]
* [albright-hayes-2003]
-/

namespace Morphology.Construction

variable {V P Q P₁ P₂ α : Type*}

/-- A schema is a slot-indexed description `body` together with a set `opens` of slots marked as
open variables. A slot at `⊥` is a variable and a slot above `⊥` is a constant. -/
@[ext]
structure Schema (V α : Type*) where
  /-- The slot-indexed description. -/
  body : V → α
  /-- The slots marked as open variables. -/
  opens : Set V

namespace Schema

section PartialOrder
variable [PartialOrder α] {s t : Schema V α} {w w₁ w₂ : V → α} {Λ Λ' : Set (V → α)}
  {v : V}

/-- An item `w` instantiates a schema `s` if the description of `s` lies below `w` slot by slot:
each constant is matched and each variable is filled freely. -/
def Instantiates (s : Schema V α) (w : V → α) : Prop := s.body ≤ w

/-- A schema instantiates its own description. -/
theorem instantiates_body (s : Schema V α) : s.Instantiates s.body := le_rfl

/-- The instances of a schema form an upper set. -/
theorem Instantiates.trans_le (h : s.Instantiates w₁) (hw : w₁ ≤ w₂) :
    s.Instantiates w₂ :=
  h.trans hw

/-- A fully specified description, every slot maximal, is instantiated by itself alone. -/
theorem instantiates_iff_eq_of_forall_isMax (h : ∀ v, IsMax (s.body v)) :
    s.Instantiates w ↔ w = s.body :=
  ⟨λ hw => funext λ v => le_antisymm (h v (hw v)) (hw v), λ hw => hw ▸ le_rfl⟩

/-- A schema lies below another exactly when it is instantiated by everything the other is. -/
theorem body_le_body_iff :
    t.body ≤ s.body ↔ ∀ ⦃w⦄, s.Instantiates w → t.Instantiates w :=
  ⟨λ h _ hw => h.trans hw, λ h => h s.instantiates_body⟩

/-- An item instantiates a schema exactly when unifying it with the description returns the
item. -/
theorem instantiates_iff_unify [Fintype V] [PartialUnify α] :
    s.Instantiates w ↔ PartialUnify.unify s.body w = some w := by
  rw [PartialUnify.unify_eq_some_iff_isLUB]
  refine ⟨λ h => ⟨?_, ?_⟩, λ h => h.1 (Set.mem_insert _ _)⟩
  · rintro x (rfl | rfl)
    exacts [h, le_rfl]
  · exact λ _ hu => hu (Set.mem_insert_of_mem _ rfl)

/-- The instances of a unified description are the common instances of its two conjuncts. -/
theorem instantiates_iff_of_unify_eq_some [Fintype V] [PartialUnify α] {u : Schema V α}
    (h : PartialUnify.unify s.body t.body = some u.body) :
    u.Instantiates w ↔ s.Instantiates w ∧ t.Instantiates w := by
  rw [Instantiates, isLUB_le_iff (PartialUnify.isLUB_of_unify_eq_some h),
    PartialUnify.mem_upperBounds_pair]
  rfl

end PartialOrder

/-! ### Positions and coindexation -/

/-- The schema `s` read at positions through the subscripting `pos`, with coindexation
forgotten: the description and the open variables pulled back along `pos`. -/
def comap (s : Schema V α) (pos : P → V) : Schema P α :=
  ⟨s.body ∘ pos, pos ⁻¹' s.opens⟩

@[simp] theorem comap_body (s : Schema V α) (pos : P → V) :
    (s.comap pos).body = s.body ∘ pos :=
  rfl

@[simp] theorem comap_opens (s : Schema V α) (pos : P → V) :
    (s.comap pos).opens = pos ⁻¹' s.opens :=
  rfl

section Positions
variable [PartialOrder α] {s : Schema V α} {pos : P → V} {w : P → α}

/-- An item `w` over positions instantiates a schema `s` through the subscripting `pos` if `w`
is an instance of `s` read at the positions: `w = u ∘ pos` for some instance `u`. -/
def InstantiatesAt (s : Schema V α) (pos : P → V) (w : P → α) : Prop :=
  ∃ u, s.Instantiates u ∧ w = u ∘ pos

theorem Instantiates.instantiatesAt {u : V → α} (h : s.Instantiates u) (pos : P → V) :
    s.InstantiatesAt pos (u ∘ pos) :=
  ⟨u, h, rfl⟩

@[simp] theorem instantiatesAt_id {w : V → α} : s.InstantiatesAt id w ↔ s.Instantiates w :=
  ⟨λ ⟨_, hu, hw⟩ => hw ▸ hu, λ h => ⟨w, h, rfl⟩⟩

/-- An item instantiates a schema through a subscripting exactly when it instantiates the
pulled-back description and fills coindexed positions alike. -/
theorem instantiatesAt_iff :
    s.InstantiatesAt pos w ↔ (s.comap pos).Instantiates w ∧ w.FactorsThrough pos := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨λ p => hu (pos p), λ _ _ h => congrArg u h⟩
  · rintro ⟨hc, hf⟩
    refine ⟨Function.extend pos w s.body, λ v => ?_, (hf.extend_comp _).symm⟩
    by_cases hv : ∃ p, pos p = v
    · obtain ⟨p, rfl⟩ := hv
      rw [hf.extend_apply]
      exact hc p
    · rw [Function.extend_apply' _ _ _ hv]

/-- Instantiation through a subscripting is invariant under reindexing the positions. -/
theorem instantiatesAt_comp_equiv (e : Q ≃ P) :
    s.InstantiatesAt (pos ∘ e) (w ∘ e) ↔ s.InstantiatesAt pos w := by
  constructor
  · rintro ⟨u, hu, hw⟩
    refine ⟨u, hu, funext λ p => ?_⟩
    simpa using congrFun hw (e.symm p)
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩

variable {pos₁ : P₁ → V} {pos₂ : P₂ → V} {w₁ : P₁ → α} {w₂ : P₂ → α}

/-- Two items are a paired instantiation through their subscriptings exactly when each
instantiates its pulled-back description, each fills its own coindexed positions alike, and
the two agree wherever their subscripts coincide. -/
theorem instantiatesAt_elim_iff :
    s.InstantiatesAt (Sum.elim pos₁ pos₂) (Sum.elim w₁ w₂) ↔
      (s.comap pos₁).Instantiates w₁ ∧ (s.comap pos₂).Instantiates w₂ ∧
        w₁.FactorsThrough pos₁ ∧ w₂.FactorsThrough pos₂ ∧
          ∀ a b, pos₁ a = pos₂ b → w₁ a = w₂ b := by
  have h : (s.comap (Sum.elim pos₁ pos₂)).Instantiates (Sum.elim w₁ w₂) ↔
      (s.comap pos₁).Instantiates w₁ ∧ (s.comap pos₂).Instantiates w₂ := by
    simp only [Instantiates, comap_body, Sum.comp_elim, Pi.le_def, Sum.forall, Sum.elim_inl,
      Sum.elim_inr]
  rw [instantiatesAt_iff, Function.factorsThrough_sumElim_iff, h, and_assoc]

/-- A paired instantiation is symmetric: the sister relation has no direction. -/
theorem instantiatesAt_elim_swap :
    s.InstantiatesAt (Sum.elim pos₂ pos₁) (Sum.elim w₂ w₁) ↔
      s.InstantiatesAt (Sum.elim pos₁ pos₂) (Sum.elim w₁ w₂) := by
  rw [← instantiatesAt_comp_equiv (Equiv.sumComm P₁ P₂)]
  have h₁ : Sum.elim pos₂ pos₁ ∘ ⇑(Equiv.sumComm P₁ P₂) = Sum.elim pos₁ pos₂ :=
    funext λ p => by cases p <;> rfl
  have h₂ : Sum.elim w₂ w₁ ∘ ⇑(Equiv.sumComm P₁ P₂) = Sum.elim w₁ w₂ :=
    funext λ p => by cases p <;> rfl
  rw [h₁, h₂]

end Positions

/-! ### The relational role -/

section PartialOrder
variable [PartialOrder α] {s : Schema V α} {w : V → α} {Λ Λ' : Set (V → α)} {v : V}

/-- A schema `s` relates an item `w` over a lexicon `Λ` if `w` is stored in `Λ` and instantiates
`s`: the relational role of a schema. -/
def Relates (s : Schema V α) (Λ : Set (V → α)) (w : V → α) : Prop :=
  w ∈ Λ ∧ s.Instantiates w

theorem Relates.instantiates (h : s.Relates Λ w) : s.Instantiates w := h.2

theorem Relates.mono (h : Λ ⊆ Λ') (hw : s.Relates Λ w) : s.Relates Λ' w := ⟨h hw.1, hw.2⟩

/-- An instance, once stored, is related by the schema. -/
theorem Instantiates.relates_insert (h : s.Instantiates w) : s.Relates (insert w Λ) w :=
  ⟨Set.mem_insert _ _, h⟩

/-- The fillers attested at a slot `v` are the values the stored instances of `s` take there:
the filler list of a closed variable, derived from the lexicon rather than stipulated. -/
def attested (s : Schema V α) (Λ : Set (V → α)) (v : V) : Set α :=
  {a | ∃ w, s.Relates Λ w ∧ w v = a}

@[simp]
theorem mem_attested {a : α} : a ∈ s.attested Λ v ↔ ∃ w, s.Relates Λ w ∧ w v = a :=
  Iff.rfl

theorem Relates.apply_mem_attested (h : s.Relates Λ w) (v : V) : w v ∈ s.attested Λ v :=
  ⟨w, h, rfl⟩

theorem attested_mono (h : Λ ⊆ Λ') (v : V) : s.attested Λ v ⊆ s.attested Λ' v := by
  rintro a ⟨w, hw, rfl⟩
  exact ⟨w, hw.mono h, rfl⟩

end PartialOrder

/-- A schema is instantiated by the meet of two items exactly when it is instantiated by both:
the meet is their least general generalization, the Structural Intersection of Relational
Morphology. -/
theorem instantiates_inf_iff [SemilatticeInf α] {s : Schema V α} {w₁ w₂ : V → α} :
    s.Instantiates (w₁ ⊓ w₂) ↔ s.Instantiates w₁ ∧ s.Instantiates w₂ :=
  le_inf_iff

/-! ### The generative role -/

section OrderBot
variable [PartialOrder α] [OrderBot α] {s : Schema V α} {w : V → α} {Λ Λ' : Set (V → α)}

/-- A schema `s` generates an item `w` over a lexicon `Λ` if `w` instantiates `s` and every closed
variable of `s`, a slot at `⊥` not marked open, takes in `w` a filler attested in `Λ`: the
generative role of a schema, licensing possibly novel items. -/
def Generates (s : Schema V α) (Λ : Set (V → α)) (w : V → α) : Prop :=
  s.Instantiates w ∧ ∀ v, s.body v = ⊥ → v ∉ s.opens → w v ∈ s.attested Λ v

theorem Generates.instantiates (h : s.Generates Λ w) : s.Instantiates w := h.1

/-- A related item is generated, attesting its own fillers. -/
theorem Relates.generates (h : s.Relates Λ w) : s.Generates Λ w :=
  ⟨h.2, λ v _ _ => h.apply_mem_attested v⟩

/-- A generated item, once stored, is related by the schema. -/
theorem Generates.relates_insert (h : s.Generates Λ w) : s.Relates (insert w Λ) w :=
  h.instantiates.relates_insert

/-- Generation is monotone in the lexicon. -/
theorem Generates.mono (h : Λ ⊆ Λ') (hw : s.Generates Λ w) : s.Generates Λ' w :=
  ⟨hw.1, λ v hv hvo => attested_mono h v (hw.2 v hv hvo)⟩

/-- A schema is productive if every variable, every slot at `⊥`, is open. -/
def IsProductive (s : Schema V α) : Prop := ∀ v, s.body v = ⊥ → v ∈ s.opens

/-- A productive schema generates exactly its instances. -/
theorem IsProductive.generates_iff (hs : s.IsProductive) :
    s.Generates Λ w ↔ s.Instantiates w :=
  ⟨Generates.instantiates, λ h => ⟨h, λ v hv hvo => absurd (hs v hv) hvo⟩⟩

/-- A schema is productive exactly when it generates its own description over the empty
lexicon. -/
theorem isProductive_iff_generates_empty : s.IsProductive ↔ s.Generates ∅ s.body := by
  refine ⟨λ hs => ⟨le_rfl, λ v hv hvo => absurd (hs v hv) hvo⟩, λ h v hv => ?_⟩
  by_contra hvo
  obtain ⟨w, ⟨hw, -⟩, -⟩ := h.2 v hv hvo
  exact hw

end OrderBot

end Schema

/-! ### Relational links

Two items over one position space are the same except at `S` when they agree off `S`; what
happens at `S` classifies the link. -/

section RelationalLinks
variable {f g : P → α} {S : Set P}

section PartialOrder
variable [PartialOrder α]

/-- `Instantiation f g S` means that `g` is the same as `f` except at `S`, where it strictly
dominates `f`: the relational link from a schema's description to its instances. -/
def Instantiation (f g : P → α) (S : Set P) : Prop :=
  Set.EqOn f g Sᶜ ∧ StrongLT (S.domRestrict f) (S.domRestrict g)

/-- `Contrast f g S` means that `f` and `g` are the same except at `S`, where they are
incompatible: the relational link between sister words. -/
def Contrast (f g : P → α) (S : Set P) : Prop :=
  Set.EqOn f g Sᶜ ∧ ∀ p ∈ S, ¬ Compat (f p) (g p)

theorem Contrast.symm (h : Contrast f g S) : Contrast g f S :=
  ⟨h.1.symm, λ p hp hc => h.2 p hp hc.symm⟩

/-- An instantiation of a schema's description instantiates the schema. -/
theorem Instantiation.instantiates {s : Schema P α} {w : P → α}
    (h : Instantiation s.body w S) : s.Instantiates w := by
  intro p
  by_cases hp : p ∈ S
  · exact (h.2 ⟨p, hp⟩).le
  · exact (h.1 hp).le

end PartialOrder

section OrderBot
variable [PartialOrder α] [OrderBot α]

/-- Where every value other than `⊥` is maximal, a contrast is two present and distinct
values. -/
theorem contrast_iff_of_forall_isMax (hα : ∀ a : α, a ≠ ⊥ → IsMax a) :
    Contrast f g S ↔
      Set.EqOn f g Sᶜ ∧ ∀ p ∈ S, f p ≠ ⊥ ∧ g p ≠ ⊥ ∧ f p ≠ g p :=
  and_congr_right' (forall₂_congr λ _ _ => not_compat_iff_of_forall_isMax hα)

/-- On a flat carrier, a filled item instantiates a schema exactly when it is the schema's
description, the same except at the variables. -/
theorem Schema.instantiates_iff_instantiation_of_forall_isMax
    (hα : ∀ a : α, a ≠ ⊥ → IsMax a) {s : Schema P α} {w : P → α}
    (hw : ∀ p, w p ≠ ⊥) :
    s.Instantiates w ↔ Instantiation s.body w {p | s.body p = ⊥} := by
  refine ⟨λ h => ⟨λ p hp => ?_, λ p => ?_⟩, Instantiation.instantiates⟩
  · simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hp
    exact le_antisymm (h p) (hα _ hp (h p))
  · have hp : s.body p = ⊥ := p.2
    show s.body p < w p
    rw [hp]
    exact bot_lt_iff_ne_bot.2 (hw p)

end OrderBot

end RelationalLinks

end Morphology.Construction
