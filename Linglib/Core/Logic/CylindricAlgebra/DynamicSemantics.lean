import Linglib.Core.Logic.CylindricAlgebra
import Linglib.Semantics.Dynamic.DPL.Basic
import Linglib.Semantics.Dynamic.CDRT.Basic

/-!
# Cylindric Algebra Bridges for Dynamic Semantics
[henkin-monk-tarski-1971] [groenendijk-stokhof-1991] [muskens-1996]

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
and cylindric set algebra ([groenendijk-stokhof-1991]). -/
theorem dpl_closure_exists_eq_cylindrify {E : Type*} (x : Nat) (φ : DPLRel E) :
    closure (toDRS (DPLRel.exists_ x φ)) =
    cylindrify x (closure (toDRS φ)) := by
  have hup : ∀ (g : Assignment E) (d : E),
      (fun n => if n = x then d else g n) = Function.update g x d := fun g d => by
    funext n; simp [Function.update_apply]
  ext g; simp only [closure, toDRS, DPLRel.exists_, cylindrify]
  exact ⟨fun ⟨h, d, hφ⟩ => ⟨d, h, hup g d ▸ hφ⟩,
         fun ⟨d, h, hφ⟩ => ⟨h, d, (hup g d).symm ▸ hφ⟩⟩

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

/-- Discourse referent introduction under closure = cylindrification.

`closure(new n ;; φ) = cₙ(closure(φ))`: introducing dref `n`
then continuing with `φ` equals cylindrifying `φ` at `n`. -/
theorem cdrt_new_seq_eq_cylindrify {E : Type*} (n : Nat) (φ : DProp E) :
    closure (DProp.new n ;; φ) =
    cylindrify n (closure φ) := by
  ext g; simp only [closure, DProp.seq, dseq, Relation.Comp, DProp.new, cylindrify]
  constructor
  · rintro ⟨o, k, ⟨e, rfl⟩, hφ⟩
    exact ⟨e, o, by convert hφ using 2; simp [Function.update_apply]⟩
  · rintro ⟨e, o, hφ⟩
    exact ⟨o, _, ⟨e, rfl⟩, by convert hφ using 2; simp [Function.update_apply]⟩

/-- CDRT equality condition on drefs = diagonal element. -/
theorem cdrt_eq_dref_eq_diagonal {E : Type*} (i j : Nat) :
    eq' (dref i : Dref (State E) E) (dref j) = @diagonal E i j := by
  ext g; simp only [eq', dref, diagonal]

end CDRT

-- The Charlow 2019 bridges that previously lived here have been moved to
-- `Linglib/Studies/Charlow2019.lean` (§ Cylindric algebra bridges).
-- A Core file cannot import from Studies — the dependency arrow runs
-- substrate→Studies. The DPL and CDRT bridges above are layering-legal
-- because their substrate lives in `Semantics/Dynamic/`.

end Core.CylindricAlgebra
