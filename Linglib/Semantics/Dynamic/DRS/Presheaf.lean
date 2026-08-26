import Linglib.Semantics.Dynamic.DRS.Context
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Opposites
import Mathlib.Data.Finset.Sort

/-!
# The presheaf of basic DRSs

This file defines the presheaf of basic discourse representation structures on the category of
contexts: at a context `(L, X)` its sections are the consistent finite sets of literals over the
context, and restriction along a context morphism `f` is substitution-preimage,
`F(f)(s) ⊢ ±A(x̄) ⟺ s ⊢ ±A(f(x̄))`. A section `s` at `(L, X)` is the basic DRS `(X, s)`, which
`Theory.toDRS` realises as a `DRS` whose conditions are literals.

## Main definitions

* `DRT.Theory`: consistent finite sets of literals over a context, with `Theory.restrict`.
* `DRT.presheaf`: the presheaf `(Context L V)ᵒᵖ ⥤ Type`.
* `DRT.Condition.IsLiteral`, `DRT.DRS.IsBasic`: literal conditions and basic DRSs.
* `DRT.Theory.toDRS`: the basic DRS of a section.

## Main statements

* `DRT.Theory.isBasic_toDRS`: sections realise as basic DRSs.

## References

* [abramsky-sadrzadeh-2014]
* [kamp-reyle-1993]
-/

open CategoryTheory FirstOrder

namespace DRT

universe u v w

variable {L : Language.{u, v}} {V : Type w}

/-- A consistent finite set of literals over a context — a basic DRS's conditions, whose
deductive closure adds no literals. -/
@[ext] structure Theory (c : Context L V) where
  /-- The literals held true. -/
  lits : Finset (Literal c)
  /-- No literal occurs with both signs. -/
  consistent : ∀ l ∈ lits, l.neg ∉ lits

/-- A literal condition: an atom, or the negation of a one-atom box with no referents. -/
def Condition.IsLiteral : Condition L V → Prop
  | .rel _ _ => True
  | .neg K => K.referents = ∅ ∧ ∃ (n : ℕ) (R : L.Relations n) (args : Fin n → V),
      K.conditions = [.rel R args]
  | _ => False

/-- A basic DRS: every condition is a literal. -/
def DRS.IsBasic (K : DRS L V) : Prop := ∀ d ∈ K.conditions, d.IsLiteral

namespace Theory

variable {c c' : Context L V}

instance : Bot (Theory c) := ⟨⟨∅, by simp⟩⟩

@[simp] theorem lits_bot : (⊥ : Theory c).lits = ∅ := rfl

/-- The basic DRS `(X, s)` of a section: the context's referents with the literals as
conditions. -/
noncomputable def toDRS (s : Theory c) : DRS L V := ⟨c.vars, s.lits.toList.map Literal.toCondition⟩

@[simp] theorem referents_toDRS (s : Theory c) : s.toDRS.referents = c.vars := rfl

theorem coe_conditions_toDRS (s : Theory c) :
    (s.toDRS.conditions : Multiset (Condition L V)) = s.lits.val.map Literal.toCondition := by
  simp [toDRS, ← Multiset.map_coe]

theorem isBasic_toDRS (s : Theory c) : s.toDRS.IsBasic := by
  rintro _ hd
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hd
  unfold Literal.toCondition
  split
  · trivial
  · exact ⟨rfl, _, _, _, rfl⟩

variable [DecidableEq V] [∀ n, DecidableEq (L.Relations n)]

instance : DecidableEq (Theory c) := fun _ _ => decidable_of_iff _ Theory.ext_iff.symm

/-- Restriction along a context morphism: `F(f)(s) ⊢ ±A(x̄) ⟺ s ⊢ ±A(f(x̄))`. -/
def restrict (f : c ⟶ c') (s : Theory c') : Theory c where
  lits := Finset.univ.filter fun l => l.map f ∈ s.lits
  consistent _ hl hn := s.consistent _ (Finset.mem_filter.1 hl).2 (Finset.mem_filter.1 hn).2

@[simp] theorem mem_restrict {f : c ⟶ c'} {s : Theory c'} {l : Literal c} :
    l ∈ (s.restrict f).lits ↔ l.map f ∈ s.lits := by simp [restrict]

end Theory

variable (L V) [DecidableEq V] [∀ n, DecidableEq (L.Relations n)]

/-- The presheaf of basic DRSs: theories at each context, restriction along context morphisms. -/
def presheaf : (Context L V)ᵒᵖ ⥤ Type (max v w) where
  obj c := Theory c.unop
  map f := TypeCat.ofHom fun s => s.restrict f.unop

variable {L V}

@[simp] theorem presheaf_obj (c : (Context L V)ᵒᵖ) : (presheaf L V).obj c = Theory c.unop := rfl

@[simp] theorem presheaf_map {c c' : (Context L V)ᵒᵖ} (f : c ⟶ c') (s : Theory c.unop) :
    (presheaf L V).map f s = s.restrict f.unop := rfl

end DRT
