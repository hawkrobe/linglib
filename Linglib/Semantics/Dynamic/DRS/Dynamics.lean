import Linglib.Semantics.Dynamic.DRS.Reduction

/-!
# Relational (dynamic) semantics of DRSs, and its equivalence with verifying embeddings
@cite{muskens-1996}

Muskens's reformulation of DRT. Conditions denote *sets* of embeddings (SEM1/2);
boxes denote *binary relations* between embeddings (SEM3, input → output); a box
is true under an input embedding `a` iff some output `a'` is related to it
(p. 148). This is the dynamic / CCP face of DRT, dual to the static
verifying-embedding semantics `DRS.Realize` (@cite{kamp-reyle-1993}, Def. 1.4.4).

The two semantics are *defined independently* and proved equivalent — Muskens's
remark that the relational interpretation "is in fact equivalent" to Kamp &
Reyle's. The equivalence is a theorem, not a definitional identification:

* `DRS.toRel_iff_realize` — the relation `toRel K a a'` holds iff `a'` extends `a`
  over `K`'s universe and verifies `K` (the keystone bridge).
* `DRS.trueRel_iff_realize_toFormula` — the dynamic truth of a DRS equals its
  first-order translation's `Realize`, closing the triangle with `Reduction`
  (`Realize` — `toFormula` — `toRel`, each pair related by a proven theorem).

## Main declarations

* `DRS.toRel` / `Condition.holds` — the relational (SEM3) and set (SEM1/2)
  denotations.
* `DRS.trueRel` — relational truth: some output embedding is related to the input.
* `DRS.toRel_iff_realize` / `Condition.holds_iff_realize` — equivalence with the
  static `DRS.Realize` semantics.
-/

open FirstOrder FirstOrder.Language

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {M : Type x} [L.Structure M]

/-! ### The relational denotation -/

mutual
/-- The relational (dynamic) denotation of a DRS (@cite{muskens-1996}, SEM3): the
input-output relation `⟨a, a'⟩` where `a'` differs from `a` at most on the
universe and verifies every condition. -/
def DRS.toRel : DRS L V → (V → M) → (V → M) → Prop
  | .mk U conds => fun a a' => (∀ x, x ∉ U → a' x = a x) ∧ Condition.holdsAll conds a'
/-- The set denotation of a condition (@cite{muskens-1996}, SEM1/2): the set of
embeddings at which it holds. Complex conditions reference the box relation
`DRS.toRel` of their sub-DRSs. -/
def Condition.holds : Condition L V → (V → M) → Prop
  | .rel R args => fun a => Structure.RelMap R (fun i => a (args i))
  | .eq u v => fun a => a u = a v
  | .neg K => fun a => ¬ ∃ a', DRS.toRel K a a'
  | .imp ante cons => fun a => ∀ a', DRS.toRel ante a a' → ∃ a'', DRS.toRel cons a' a''
  | .dis l r => fun a => ∃ a', DRS.toRel l a a' ∨ DRS.toRel r a a'
/-- Every condition in the list holds at `a`. A `List` helper — the higher-order
form fails the nested-inductive structural-recursion checker. -/
def Condition.holdsAll : List (Condition L V) → (V → M) → Prop
  | [] => fun _ => True
  | c :: cs => fun a => Condition.holds c a ∧ Condition.holdsAll cs a
end

/-- A DRS is *true* under an input embedding `a` iff some output embedding is
related to it (@cite{muskens-1996}, p. 148). -/
def DRS.trueRel (K : DRS L V) (a : V → M) : Prop := ∃ a', DRS.toRel K a a'

/-! ### Equivalence with the verifying-embedding semantics -/

mutual
/-- **Muskens ≡ Kamp & Reyle** (@cite{muskens-1996}): the relational denotation
agrees with the static verifying-embedding semantics — `toRel K a a'` holds iff
the output `a'` extends the input `a` over `K`'s universe and verifies `K`. -/
theorem DRS.toRel_iff_realize (K : DRS L V) (a a' : V → M) :
    DRS.toRel K a a' ↔ (∀ x, x ∉ K.referents → a' x = a x) ∧ DRS.Realize a' K := by
  match K with
  | .mk U conds =>
    simp only [DRS.toRel, DRS.referents_mk, DRS.Realize]
    exact and_congr_right (fun _ => Condition.holdsAll_iff_realizeAll conds a')
/-- A condition's set denotation agrees with its static `Realize`. -/
theorem Condition.holds_iff_realize (c : Condition L V) (a : V → M) :
    Condition.holds c a ↔ Condition.Realize a c := by
  match c with
  | .rel R args => simp only [Condition.holds, Condition.Realize]
  | .eq u v => simp only [Condition.holds, Condition.Realize]
  | .neg K =>
    simp only [Condition.holds, Condition.Realize]
    exact not_congr (exists_congr (fun a' => DRS.toRel_iff_realize K a a'))
  | .imp ante cons =>
    simp only [Condition.holds, Condition.Realize]
    refine forall_congr' (fun a' => ?_)
    rw [DRS.toRel_iff_realize ante a a', and_imp]
    refine imp_congr_right (fun _ => imp_congr_right (fun _ => ?_))
    exact exists_congr (fun a'' => DRS.toRel_iff_realize cons a' a'')
  | .dis l r =>
    simp only [Condition.holds, Condition.Realize, exists_or]
    exact or_congr (exists_congr (fun a' => DRS.toRel_iff_realize l a a'))
      (exists_congr (fun a' => DRS.toRel_iff_realize r a a'))
/-- The list analogue of `Condition.holds_iff_realize`. -/
theorem Condition.holdsAll_iff_realizeAll (cs : List (Condition L V)) (a : V → M) :
    Condition.holdsAll cs a ↔ Condition.RealizeAll a cs := by
  match cs with
  | [] => simp only [Condition.holdsAll, Condition.RealizeAll]
  | c :: cs =>
    simp only [Condition.holdsAll, Condition.RealizeAll]
    exact and_congr (Condition.holds_iff_realize c a) (Condition.holdsAll_iff_realizeAll cs a)
end

/-- The dynamic truth of a DRS equals its first-order translation's `Realize`
(@cite{muskens-1996}; @cite{kamp-reyle-1993} §1.5) — the third edge of the
`Realize`/`toFormula`/`toRel` triangle. -/
theorem DRS.trueRel_iff_realize_toFormula [DecidableEq V] (K : DRS L V) (a : V → M) :
    DRS.trueRel K a ↔ (K.toFormula).Realize a := by
  rw [DRS.trueRel, DRS.realize_toFormula K a]
  exact exists_congr (fun a' => DRS.toRel_iff_realize K a a')

end DRT
