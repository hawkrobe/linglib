import Linglib.Semantics.Dynamic.DRS.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma

/-!
# Contexts, renamings, and literals

This file defines the category of *contexts* of discourse representation theory in its
sheaf-theoretic reading: a context is a finite vocabulary of relation symbols together with a
finite set of discourse referents, and a morphism is an inclusion of vocabularies with a map of
referents — a relabelling, an inclusion, or an identification of referents. Literals over a
context are signed atoms; they rename covariantly along context morphisms, and each one is a
DRS-condition.

This is the substitution category on contexts, complementary to the extension category `DRT.Ctx`
whose morphisms are DRSs composed by merge: `Ctx` grows a context by introducing referents,
`Context` maps referents between contexts.

## Main definitions

* `DRT.Context`, `DRT.Context.Hom`: contexts `(L, X)` and their morphisms, a `Category`.
* `DRT.Literal`: literals `±A(x̄)` over a context, with `Literal.map` (renaming), `Literal.neg`,
  decidable equality and finiteness.
* `DRT.Literal.toCondition`: a literal as a DRS-condition — an atom, or a negated one-atom box.

## Main statements

* `DRT.Literal.toCondition_map`: renaming a literal along a context morphism is `Condition.map`
  along any extension of the morphism to the referent type.

## References

* [abramsky-sadrzadeh-2014]
* [kamp-reyle-1993]
-/

open CategoryTheory FirstOrder

namespace DRT

universe u v w

/-- A context `(L, X)`: a finite vocabulary of relation symbols and a finite set of referents. -/
structure Context (L : Language.{u, v}) (V : Type w) where
  /-- The vocabulary. -/
  vocab : Finset (Σ n, L.Relations n)
  /-- The referents. -/
  vars : Finset V

variable {L : Language.{u, v}} {V : Type w}

/-- A context morphism: an inclusion of vocabularies together with a map of referents. -/
structure Context.Hom (c c' : Context L V) where
  /-- The vocabulary inclusion. -/
  incl : c.vocab ⊆ c'.vocab
  /-- The referent map. -/
  map : c.vars → c'.vars

instance : Category (Context L V) where
  Hom := Context.Hom
  id c := ⟨subset_rfl, id⟩
  comp f g := ⟨f.incl.trans g.incl, g.map ∘ f.map⟩

/-- A literal over a context: a signed atomic formula `±A(x̄)`. -/
structure Literal (c : Context L V) where
  /-- The relation symbol. -/
  rel : c.vocab
  /-- The argument referents. -/
  args : Fin rel.1.1 → c.vars
  /-- The sign. -/
  pos : Bool

namespace Literal

variable {c c' c'' : Context L V}

/-- Literals as dependent triples. -/
def equivSigma (c : Context L V) : Literal c ≃ Σ r : c.vocab, (Fin r.1.1 → c.vars) × Bool where
  toFun l := ⟨l.rel, l.args, l.pos⟩
  invFun l := ⟨l.1, l.2.1, l.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Renaming along a context morphism. -/
def map (f : c ⟶ c') (l : Literal c) : Literal c' :=
  ⟨⟨l.rel.1, f.incl l.rel.2⟩, f.map ∘ l.args, l.pos⟩

@[simp] theorem map_id (l : Literal c) : l.map (𝟙 c) = l := rfl

@[simp] theorem map_comp (f : c ⟶ c') (g : c' ⟶ c'') (l : Literal c) :
    l.map (f ≫ g) = (l.map f).map g := rfl

theorem map_injective {f : c ⟶ c'} (hf : Function.Injective f.map) :
    Function.Injective (map f) := by
  rintro ⟨⟨r, hr⟩, a, p⟩ ⟨⟨r', hr'⟩, a', p'⟩ h
  obtain ⟨h₁, h₂, rfl⟩ := Literal.mk.inj h
  obtain rfl := Subtype.mk.inj h₁
  cases funext fun i => hf (congrFun (eq_of_heq h₂) i)
  rfl

/-- The complementary literal. -/
def neg (l : Literal c) : Literal c := ⟨l.rel, l.args, !l.pos⟩

@[simp] theorem neg_neg (l : Literal c) : l.neg.neg = l := by cases l; simp [neg]

@[simp] theorem neg_map (f : c ⟶ c') (l : Literal c) : (l.map f).neg = l.neg.map f := rfl

/-- The literal as a DRS-condition: an atom, or for a negative literal the negation of the
one-atom box with no referents. -/
def toCondition (l : Literal c) : Condition L V :=
  if l.pos then .rel l.rel.1.2 fun i => (l.args i : V)
  else .neg ⟨∅, [.rel l.rel.1.2 fun i => (l.args i : V)]⟩

/-- Renaming a literal along `f` is `Condition.map` along any extension of `f` to the
referent type. -/
theorem toCondition_map [DecidableEq V] (f : c ⟶ c') (g : V → V)
    (hg : ∀ t : c.vars, g t = (f.map t : V)) (l : Literal c) :
    (l.map f).toCondition = l.toCondition.map g := by
  cases hp : l.pos <;> simp [toCondition, map, Condition.map, Box.map, hg, hp]

end Literal

variable [DecidableEq V] [∀ n, DecidableEq (L.Relations n)]

-- Compared through non-dependent data, which kernel `decide` evaluates on enumerated literals.
instance (c : Context L V) : DecidableEq (Literal c) := fun l l' =>
  decidable_of_iff (l.rel.1 = l'.rel.1 ∧ List.ofFn l.args = List.ofFn l'.args ∧ l.pos = l'.pos) (by
    constructor
    · rintro ⟨h₁, h₂, h₃⟩
      obtain ⟨⟨r, hr⟩, a, p⟩ := l
      obtain ⟨⟨r', hr'⟩, a', p'⟩ := l'
      obtain rfl : r = r' := h₁
      obtain rfl := List.ofFn_injective h₂
      obtain rfl := h₃
      rfl
    · rintro rfl; exact ⟨rfl, rfl, rfl⟩)

instance (c : Context L V) : Fintype (Literal c) := Fintype.ofEquiv _ (Literal.equivSigma c).symm

end DRT
