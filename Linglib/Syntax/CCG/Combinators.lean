import Linglib.Syntax.CCG.Basic
import Linglib.Syntax.CCG.Interface
import Linglib.Core.Logic.Intensional.Frame
import Linglib.Semantics.Composition.Combinator

/-!
# CCG combinatory rules as combinatory-logic combinators

CCG's combinatory rules correspond to the basis combinators of combinatory logic
([curry-feys-1958], [smullyan-1985]): forward and backward composition to `B`,
type-raising to `T`, the substitution rule to `S`. The combinator algebra itself lives in
`Semantics/Composition/Combinator.lean`; this file establishes the correspondence between
those combinators and the *types* CCG assigns (`catToTy`), so that each rule's semantic
action is literally a combinator acting on `Frame.Denot` meanings ([steedman-2000],
Chapters 3 and 8).
-/

namespace CCG.Combinators

open CCG
open Core.Logic.Intensional
open Combinator

-- The `B`/`T`/`S`/`I`/`K`/`C` algebra lives in `Semantics/Composition/Combinator.lean`
-- (namespace `Combinator`). `B`/`T` are used bare via `open Combinator`; the combinator `S`
-- is written `Combinator.S` to keep it distinct from the sentence category `CCG.S`.

/-- Forward composition is `B`: its semantics is `B f g`. -/
theorem fcomp_is_B {F : Frame} {x y z : Cat}
    (f_sem : F.Denot (catToTy (x.rslash y)))
    (g_sem : F.Denot (catToTy (y.rslash z))) :
    (λ arg => f_sem (g_sem arg)) = B f_sem g_sem := rfl

/-- The type of a forward-composition result. -/
theorem fcomp_type_is_B (x _y z : Cat) :
    catToTy (x.rslash z) = (catToTy z ⇒ catToTy x) := rfl

/-- Backward composition is also `B`, with reversed linear order. -/
theorem bcomp_is_B {F : Frame} {x y z : Cat}
    (g_sem : F.Denot (catToTy (y.lslash z)))
    (f_sem : F.Denot (catToTy (x.lslash y))) :
    (λ arg => f_sem (g_sem arg)) = B f_sem g_sem := rfl

/-- Forward type-raising is `T`: its semantics is `T a`. -/
theorem type_raise_is_T {F : Frame} {x t : Cat}
    (a_sem : F.Denot (catToTy x)) :
    (λ (f : F.Denot (catToTy (t.lslash x))) => f a_sem) = T a_sem := rfl

/-- The type of a forward-type-raised category `T/(T\X)`. -/
theorem ftr_type_is_T (x t : Cat) :
    catToTy (forwardTypeRaise x t) = ((catToTy x ⇒ catToTy t) ⇒ catToTy t) := rfl

/-- Backward type-raising has the same type as forward type-raising. -/
theorem btr_type_is_T (x t : Cat) :
    catToTy (backwardTypeRaise x t) = ((catToTy x ⇒ catToTy t) ⇒ catToTy t) := rfl

/-- Crossed composition is `S`: `(X/Y)/Z + Y/Z ⇒ X/Z` with `S f g x = f x (g x)`. -/
theorem crossed_comp_is_S {F : Frame} {x y z : Cat}
    (f_sem : F.Denot (catToTy ((x.rslash y).rslash z)))
    (g_sem : F.Denot (catToTy (y.rslash z))) :
    (λ arg => f_sem arg (g_sem arg)) = Combinator.S f_sem g_sem := rfl

/-- Forward application is `T` applied the other way: `f a = T a f`. -/
theorem fapp_via_T {F : Frame} {x y : Cat}
    (f_sem : F.Denot (catToTy (x.rslash y)))
    (a_sem : F.Denot (catToTy y)) :
    f_sem a_sem = T a_sem f_sem := rfl

/-- Non-constituent coordination: a type-raised subject composed (`B`) with a transitive
verb is a function from objects to truth values — `B (T subj) verb obj = verb obj subj`.
This is the combinator account of "John likes and Mary hates beans". -/
theorem subject_verb_composition {F : Frame}
    (subj_sem : F.Denot (catToTy NP))
    (verb_sem : F.Denot (catToTy TV))
    (obj : F.Denot (catToTy NP)) :
    B (T subj_sem) verb_sem obj = verb_sem obj subj_sem := rfl

end CCG.Combinators
