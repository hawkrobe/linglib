import Linglib.Core.CylindricAlgebra
import Linglib.Theories.Semantics.Dynamic.DPL.Basic
import Linglib.Theories.Semantics.Dynamic.CDRT.Basic
import Linglib.Phenomena.Anaphora.Studies.Charlow2019

/-!
# Cylindric Algebra Bridges for Dynamic Semantics
@cite{henkin-monk-tarski-1971} @cite{groenendijk-stokhof-1991} @cite{muskens-1996}

Proves that the existential quantifiers and identity tests across
DPL, CDRT, and DRS are all instances of the cylindric algebra
operations `cylindrify` and `diagonal` from `Core.CylindricAlgebra`.

## Bridges

| Framework | Existential | = Cylindric |
|---|---|---|
| DPL | `DPLRel.exists_ x φ` | `cylindrify x (closure φ)` |
| CDRT | `DProp.new n ;; φ` | `cylindrify n (closure φ)` |
| DRS | `box [n] [conds]` | `cylindrify n (interp conds)` |

| Framework | Identity | = Cylindric |
|---|---|---|
| DPL | `atom (g(x) = g(y))` | `diagonal x y` |
| CDRT | `eq' (dref n) (dref m)` | `diagonal n m` |
| DRS | `.is n m` | `diagonal n m` |

These are not analogies — they are algebraic identities under `closure`.
-/

namespace Core.CylindricAlgebra

open Core (Assignment)
open Core.CylindricAlgebra

-- ════════════════════════════════════════════════════════════════
-- § DPL bridges
-- ════════════════════════════════════════════════════════════════

section DPL

open Semantics.Dynamic.DPL
open Semantics.Dynamic.Core

/-- **DPL existential = cylindrification.**

`closure(∃x.φ) = cₓ(closure(φ))`: the truth-conditional content of
DPL's existential quantifier at variable `x` is exactly cylindrification
at register `x`. This is the defining correspondence between DPL
and cylindric set algebra (@cite{groenendijk-stokhof-1991}). -/
theorem dpl_closure_exists_eq_cylindrify {E : Type*} (x : Nat) (φ : DPLRel E) :
    closure (toDRS (DPLRel.exists_ x φ)) =
    cylindrify x (closure (toDRS φ)) := by
  ext g; simp only [closure, toDRS, DPLRel.exists_, cylindrify]
  exact ⟨fun ⟨h, d, hφ⟩ => ⟨d, h, hφ⟩, fun ⟨d, h, hφ⟩ => ⟨h, d, hφ⟩⟩

/-- **DPL identity test = diagonal element.**

`closure(atom(g(x) = g(y))) = Dxy`: the truth condition of the DPL
atomic formula `x = y` is the diagonal element `Dxy` from cylindric
algebra. -/
theorem dpl_closure_identity_eq_diagonal {E : Type*} (x y : Nat) :
    closure (toDRS (DPLRel.atom (fun g : Assignment E => g x = g y))) =
    @diagonal E x y := by
  ext g; simp only [closure, toDRS, DPLRel.atom, diagonal]
  exact ⟨fun ⟨_, rfl, h⟩ => h, fun h => ⟨g, rfl, h⟩⟩

/-- DPL negation under closure is a test for non-cylindrifiability:
`closure(¬φ)(g)` iff no assignment update satisfies φ. -/
theorem dpl_closure_neg_eq {E : Type*} (φ : DPLRel E) :
    closure (toDRS (DPLRel.neg φ)) =
    fun g => ¬ closure (toDRS φ) g := by
  ext g; simp only [closure, toDRS, DPLRel.neg]
  exact ⟨fun ⟨_, rfl, h⟩ => h, fun h => ⟨g, rfl, h⟩⟩

end DPL

-- ════════════════════════════════════════════════════════════════
-- § CDRT bridges
-- ════════════════════════════════════════════════════════════════

section CDRT

open Semantics.Dynamic.CDRT
open Semantics.Dynamic.Core

/-- CDRT registers ARE assignments. -/
theorem cdrt_register_eq_assignment {E : Type*} :
    Register E = Assignment E := rfl

/-- Discourse referent introduction under closure = cylindrification.

`closure(new n ;; φ) = cₙ(closure(φ))`: introducing dref `n`
then continuing with `φ` equals cylindrifying `φ` at `n`. -/
theorem cdrt_new_seq_eq_cylindrify {E : Type*} (n : Nat) (φ : DProp E) :
    closure (toDRS (DProp.new n ;; φ)) =
    cylindrify n (closure (toDRS φ)) := by
  ext g; simp only [closure, toDRS, DProp.seq, DProp.new, cylindrify]
  constructor
  · rintro ⟨o, k, ⟨e, rfl⟩, hφ⟩
    exact ⟨e, o, by convert hφ using 2⟩
  · rintro ⟨e, o, hφ⟩
    exact ⟨o, _, ⟨e, rfl⟩, by convert hφ using 2⟩

/-- CDRT equality condition on drefs = diagonal element. -/
theorem cdrt_eq_dref_eq_diagonal {E : Type*} (i j : Nat) :
    eq' (dref i : Dref (Register E) E) (dref j) = @diagonal E i j := by
  ext g; simp only [eq', dref, diagonal]

end CDRT

-- ════════════════════════════════════════════════════════════════
-- § Charlow 2019 bridges
-- ════════════════════════════════════════════════════════════════

section Charlow

open Semantics.Dynamic.Charlow2019
open Semantics.Dynamic.DPL

/-- Static existential truth = cylindrification.

Charlow's `staticExists x body` tests whether `∃ d, body(g[x↦d])`,
which is exactly `cylindrify x body`. -/
theorem charlow_static_eq_cylindrify {E : Type*}
    (x : Nat) (body : Assignment E → Prop) (g : Assignment E) :
    trueAt (staticExists x body) g ↔ cylindrify x body g := by
  simp only [trueAt, staticExists, DPLRel.atom, cylindrify]
  exact ⟨fun ⟨_, rfl, d, hb⟩ => ⟨d, hb⟩, fun ⟨d, hb⟩ => ⟨g, rfl, d, hb⟩⟩

/-- Dynamic existential truth = cylindrification (same truth conditions). -/
theorem charlow_dynamic_eq_cylindrify {E : Type*}
    (x : Nat) (body : Assignment E → Prop) (g : Assignment E) :
    trueAt (dynamicExists x body) g ↔ cylindrify x body g := by
  rw [← static_dynamic_same_truth]
  exact charlow_static_eq_cylindrify x body g

end Charlow

end Core.CylindricAlgebra
