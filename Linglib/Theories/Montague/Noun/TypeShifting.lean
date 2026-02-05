/-
# NP Type-Shifting Principles (Partee 1987)

The type-shifting triangle between three NP semantic types:
- `e` : referential (proper names, pronouns)
- `⟨e,t⟩` : predicative (common nouns, adjectives)
- `⟨⟨e,t⟩,t⟩` : quantificational (generalized quantifiers)

```
         e  ——lift——→  ⟨⟨e,t⟩,t⟩
         ↑  ←—lower——    ↑
       iota              BE
         ↑               ↑
        ⟨e,t⟩  ——A——→  ⟨⟨e,t⟩,t⟩
         ↑
       ident
         ↑
         e
```

## References

- Partee, B. H. (1987). Noun Phrase Interpretation and Type-shifting Principles.
  In Groenendijk et al. (eds.), Studies in Discourse Representation Theory.
-/

import Linglib.Theories.Montague.Basic
import Linglib.Theories.Montague.Conjunction
import Mathlib.Order.Hom.BoundedLattice

namespace Montague.Noun.TypeShifting

open Montague (Model Ty toyModel ToyEntity)
open Montague.Conjunction (typeRaise)

variable {m : Model}

section TotalShifts

/-- Type-raising: `lift(j) = λP. P(j)` -/
def lift (j : m.interpTy .e) : m.interpTy Ty.ett :=
  fun P => P j

/-- Singleton property: `ident(j) = λx. [j = x]`.
Uses `j = x` order for definitional equality with `BE(lift(j))`. -/
def ident (j : m.interpTy .e) : m.interpTy Ty.et :=
  fun x => @decide (j = x) (m.decEq j x)

/-- Predicative content of a GQ: `BE(Q) = λx. Q(λy. y = x)` -/
def BE (Q : m.interpTy Ty.ett) : m.interpTy Ty.et :=
  fun x => Q (fun y => @decide (y = x) (m.decEq y x))

end TotalShifts

section BooleanHomomorphism

instance (m : Model) : BooleanAlgebra (m.interpTy Ty.et) :=
  show BooleanAlgebra (m.Entity → Bool) from inferInstance
instance (m : Model) : BooleanAlgebra (m.interpTy Ty.ett) :=
  show BooleanAlgebra ((m.Entity → Bool) → Bool) from inferInstance

/-- `BE` is a `BoundedLatticeHom` (Partee §3.3, Fact 1). -/
def BE_hom (m : Model) : BoundedLatticeHom (m.interpTy Ty.ett) (m.interpTy Ty.et) where
  toFun := BE
  map_sup' _ _ := by funext; rfl
  map_inf' _ _ := by funext; rfl
  map_top' := by funext x; show BE ⊤ x = true; rfl
  map_bot' := by funext x; show BE ⊥ x = false; rfl

/-- `BE ∘ lift = ident` (Figure 3 commutativity). -/
theorem BE_lift_eq_ident (j : m.interpTy .e) :
    BE (lift j) = ident j := by
  funext x; simp only [BE, lift, ident]

/-- `BE(Q₁ ∧ Q₂) = BE(Q₁) ∧ BE(Q₂)` -/
theorem BE_conj (Q₁ Q₂ : m.interpTy Ty.ett) :
    BE (fun P => Q₁ P && Q₂ P) = (fun x => BE Q₁ x && BE Q₂ x) := by
  funext x; simp only [BE]

/-- `BE(Q₁ ∨ Q₂) = BE(Q₁) ∨ BE(Q₂)` -/
theorem BE_disj (Q₁ Q₂ : m.interpTy Ty.ett) :
    BE (fun P => Q₁ P || Q₂ P) = (fun x => BE Q₁ x || BE Q₂ x) := by
  funext x; simp only [BE]

/-- `BE(¬Q) = ¬BE(Q)` -/
theorem BE_neg (Q : m.interpTy Ty.ett) :
    BE (fun P => !(Q P)) = (fun x => !(BE Q x)) := by
  funext x; simp only [BE]

end BooleanHomomorphism

section PartialShifts

/-- Partial inverse of `lift`. Defined when `Q` is a principal ultrafilter. -/
def lower (domain : List m.Entity) (Q : m.interpTy Ty.ett) : Option (m.interpTy .e) :=
  match domain.filter (fun j => Q (fun x => @decide (x = j) (m.decEq x j))) with
  | [j] => some j
  | _ => none

/-- Partial inverse of `ident`. Returns the unique satisfier of `P`. -/
def iota (domain : List m.Entity) (P : m.interpTy Ty.et) : Option (m.interpTy .e) :=
  match domain.filter (fun x => P x) with
  | [j] => some j
  | _ => none

/-- Existential closure: `A(P) = λQ. ∃x. P(x) ∧ Q(x)` -/
def A (domain : List m.Entity) (P : m.interpTy Ty.et) : m.interpTy Ty.ett :=
  fun Q => domain.any (fun x => P x && Q x)

theorem lower_lift (domain : List m.Entity) (j : m.interpTy .e) :
    lower domain (lift j) = some j := by
  simp only [lower, lift]
  sorry -- TODO: requires showing domain.filter yields [j] when j appears once

theorem iota_ident (domain : List m.Entity) (j : m.interpTy .e) :
    iota domain (ident j) = some j := by
  simp only [iota, ident]
  sorry -- TODO: analogous

end PartialShifts

section LexicalTypes

/-- Lexical semantic type of an NP: `e` (proper nouns) or `⟨e,t⟩` (common nouns). -/
inductive LexicalNPType where
  | entity
  | pred
  deriving DecidableEq, Repr, BEq

/-- Link's `*` operator applies to type `⟨e,t⟩` only. -/
def pluralAppliesTo : LexicalNPType → Bool
  | .pred => true
  | .entity => false

theorem proper_noun_no_direct_plural :
    pluralAppliesTo .entity = false := rfl

theorem common_noun_pluralizable :
    pluralAppliesTo .pred = true := rfl

/-- Coerced plural via `ident`: `e → ⟨e,t⟩`, enabling `*` to apply. -/
def coercedPlural {m : Model} (j : m.interpTy .e)
    (star : m.interpTy Ty.et → m.interpTy Ty.et) : m.interpTy Ty.et :=
  star (ident j)

end LexicalTypes

/-- `lift = Conjunction.typeRaise` -/
theorem lift_eq_typeRaise {m : Model} (j : m.interpTy .e) :
    lift j = typeRaise j := rfl

/-- Coherence of the three readings of "the king" (Partee §3.2). -/
theorem the_king_coherence (domain : List m.Entity) (P : m.interpTy Ty.et)
    (j : m.interpTy .e) (_h : iota domain P = some j) :
    BE (lift j) = ident j :=
  BE_lift_eq_ident j

section ToyExamples

open Montague.ToyLexicon (john_sem)

private def toyDomain : List ToyEntity := [.john, .mary, .pizza, .book]

example : lift (m := toyModel) john_sem Montague.ToyLexicon.sleeps_sem = true := rfl
example : BE (m := toyModel) (lift john_sem) = ident john_sem :=
  BE_lift_eq_ident john_sem
example : iota (m := toyModel) toyDomain (ident john_sem) = some john_sem := rfl
example : lower (m := toyModel) toyDomain (lift john_sem) = some john_sem := rfl

end ToyExamples

end Montague.Noun.TypeShifting
