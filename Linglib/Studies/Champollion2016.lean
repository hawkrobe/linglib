import Linglib.Syntax.Category.Coordinator
import Linglib.Semantics.Quantification.Defs
import Linglib.Semantics.Plurality.Algebra

/-!
# Champollion 2016: noun coordination and the intersective theory of conjunction

This file formalizes the case in [champollion-2016-coordination] that *and* has one lexical entry,
the intersective generalized conjunction of [partee-rooth-1983] — the Boolean meet that the
substrate calls `Coordinator.op .j`. Collective readings such as *John and Mary met* are not a
join on individuals folded into *and*; they come from silent type-shifters.

Two results support the entry. The type-shift from an individual join to a meet of type-raised
individuals is not an anti-homomorphism but holds exactly on the predicates that distribute the
join, and that guard is Link distributivity: a `ᴰ`-closed predicate distributes every join when
atoms are join-prime, while a collective predicate does not, which is why collectivity needs
raising and minimization rather than raising and intersection. And the rival collective entry of
[heycock-zamparelli-2005], which builds *and* from union of witness sets, makes *No man and no
woman smiled* true in a model where the only smilers are a man and a woman — where the
intersective entry correctly makes it false.

## Main definitions

* `DistributiveOverJoin` — a predicate decomposes a join into a meet
* `andIntersective`, `andSetProduct` — the two entries at the type of properties of pluralities

## Main results

* `individual_join_eq_op_iff` — the type-shift holds at a predicate iff it distributes the join
* `linkD_distributiveOverJoin`, `individual_join_eq_op_of_linkD` — Link's `ᴰ`-closed predicates
  are the licensed ones
* `collective_not_distributiveOverJoin`, `individual_join_ne_op_of_not_distributive` — a
  collective predicate breaks the type-shift
* `setProduct_overgenerates` — the set-product entry and the intersective entry assign opposite
  truth values to *No man and no woman smiled*, and the intersective one is right

## References

* [champollion-2016-coordination]
* [partee-rooth-1983]
* [heycock-zamparelli-2005]
* [link-1983]
* [link-1987]
-/

namespace Champollion2016

open Quantification (individual)
open Plurality.Algebra

/-! ### The type-shift `⊔ ↦ ⊓` is guarded to distributive predicates

The intersective entry says *and* is `INT` ([champollion-2016-coordination] eq. 16):
generalized conjunction, `Coordinator.op .j`, the Boolean meet `⊓`.
On two type-raised individuals it returns `λP. P x ∧ P y`. The collective behaviour
people attribute to *and* (a join `x ⊔ y` on individuals) coincides with this meet only
for predicates that *distribute* the join — for genuinely collective predicates the two
come apart, which is the whole motivation for Champollion's silent operators. -/

section TypeShift

variable {E : Type} [SemilatticeSup E]

/-- A predicate **distributes a join** when it decomposes `x ⊔ y` into a meet:
    `P (x ⊔ y) ↔ P x ∧ P y`. Link's `ᴰ`-closed (distributive) predicates satisfy this;
    collective predicates (`met`, `gather`) do not. -/
def DistributiveOverJoin {E : Type*} [SemilatticeSup E] (P : E → Prop) : Prop :=
  ∀ x y : E, P (x ⊔ y) ↔ (P x ∧ P y)

/-- **The type-shift `⊔ ↦ ⊓`, guarded.** Type-raising the individual-join `x ⊔ y` agrees
    with the GQ-meet `Coordinator.op .j` of the raised individuals *at `P`* iff `P`
    distributes this join. The bare anti-homomorphism (for all `P`) is therefore FALSE;
    distributivity is exactly the guard. -/
theorem individual_join_eq_op_iff (x y : E) (P : E → Prop) :
    (individual (x ⊔ y : E) P
        ↔ Coordinator.op .j (individual x) (individual y) P)
      ↔ (P (x ⊔ y : E) ↔ (P x ∧ P y)) := Iff.rfl

/-- For a distributive predicate the type-shift holds: `individual (x ⊔ y)` agrees with the
    GQ-meet on `P`. -/
theorem individual_join_eq_op_of_distributive (x y : E) {P : E → Prop}
    (hP : DistributiveOverJoin P) :
    individual (x ⊔ y : E) P
      ↔ Coordinator.op .j (individual x) (individual y) P :=
  (individual_join_eq_op_iff x y P).mpr (hP x y)

/-- **The guard is Link distributivity.** A Link `ᴰ`-closed predicate `ᴰQ`
    ([link-1987]) distributes every join, given join-prime atoms ([link-1983]). So
    Champollion's distributive *and* IS Link's distributive predication, and the
    predicates that break the type-shift are precisely the non-`ᴰ`-closed (collective)
    ones. -/
theorem linkD_distributiveOverJoin {E : Type*} [SemilatticeSup E]
    (hJP : AtomJoinPrime E) (Q : E → Prop) : DistributiveOverJoin (D Q) := by
  intro x y
  constructor
  · intro h
    exact ⟨fun z hz hAtom => h z (le_trans hz le_sup_left) hAtom,
           fun z hz hAtom => h z (le_trans hz le_sup_right) hAtom⟩
  · rintro ⟨hx, hy⟩ z hz hAtom
    rcases hJP z hAtom x y hz with h | h
    · exact hx z h hAtom
    · exact hy z h hAtom

/-- A Link `ᴰ`-closed predicate licenses the type-shift `⊔ ↦ ⊓`. -/
theorem individual_join_eq_op_of_linkD (hJP : AtomJoinPrime E) (x y : E)
    (Q : E → Prop) :
    individual (x ⊔ y : E) (D Q : E → Prop)
      ↔ Coordinator.op .j (individual x) (individual y) (D Q : E → Prop) :=
  individual_join_eq_op_of_distributive x y (linkD_distributiveOverJoin hJP Q)

/-- **The guard is necessary, lifted to the type-shift.** A predicate that does NOT
    distribute the join breaks the `⊔ ↦ ⊓` agreement at the witnessing pair: there
    `individual (x ⊔ y)` and the GQ-meet `Coordinator.op .j` come apart. -/
theorem individual_join_ne_op_of_not_distributive {P : E → Prop}
    (h : ¬ DistributiveOverJoin P) :
    ∃ x y : E, ¬ (individual (x ⊔ y : E) P
                    ↔ Coordinator.op .j (individual x) (individual y) P) := by
  simp only [DistributiveOverJoin, not_forall] at h
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨x, y, fun hiff => hxy ((individual_join_eq_op_iff x y P).mp hiff)⟩

end TypeShift

/-- **A collective predicate breaks the guard.** True of the plural `{false, true}`
    (`John and Mary met`) but of neither part (`Finset Bool`, `∪` as `⊔`): this collective
    predicate is not `DistributiveOverJoin`, so by `individual_join_ne_op_of_not_distributive`
    it breaks the type-shift `⊔ ↦ ⊓`. This is why Champollion derives collectivity via
    silent Raising + Minimization rather than via raising + intersection. -/
theorem collective_not_distributiveOverJoin :
    ∃ P : Finset Bool → Prop, ¬ DistributiveOverJoin P :=
  ⟨(· = ({false, true} : Finset Bool)), by
    intro hd
    exact absurd ((hd {false} {true}).mp (by decide)).1 (by decide)⟩

/-! ### The collective theory overgenerates (§7.1, journal p. 608)

Champollion's case against the collective theory: take [heycock-zamparelli-2005]'s entry,
which builds *and* by **set product** — combining two quantifier denotations `Q`, `Q'` by
forming the **union** `A ∪ B` of a `Q`-witness and a `Q'`-witness
([champollion-2016-coordination] eq. 101):

    ⟦and_coll⟧ = λQ λQ'. λP. ∃A ∃B [Q(A) ∧ Q'(B) ∧ P = A ∪ B]

We model the conjuncts at the property-of-pluralities level (type `⟨et,t⟩`), following
Champollion's prose reduction of the eq. (104) generalized-quantifier argument on journal
p. 608: `⟦no man⟧`/`⟦no woman⟧` as the *man-free* / *woman-free* witness-set properties.
The overgeneration: *No man and no woman smiled* (103a) comes out TRUE in the model where a
smiling man (John) and a smiling woman (Mary) are the only smilers — take `A = {Mary}` (no
man) and `B = {John}` (no woman), so `A ∪ B = {John, Mary} =` the smilers — even though a
man did smile. The intersective `Coordinator.op .j` correctly makes it FALSE. -/

section Overgeneration

/-- The two-individual model of [champollion-2016-coordination] §7.1: persons John and Mary. -/
inductive Person | john | mary
  deriving DecidableEq, Repr

/-- A plurality / witness set, as the characteristic function of a set of individuals
    (type `⟨e,t⟩`). -/
abbrev Plur := Person → Prop

/-- `man` holds of John only. -/
def man : Person → Prop
  | .john => True
  | .mary => False

/-- `woman` holds of Mary only. -/
def woman : Person → Prop
  | .john => False
  | .mary => True

/-- In the model, both John and Mary smiled — and they are the only people. -/
def smiled : Plur := fun _ => True

/-- `⟦no man⟧` as a property of pluralities: the set contains no man. -/
def noMan : Plur → Prop := fun X => ∀ a, X a → ¬ man a

/-- `⟦no woman⟧` as a property of pluralities: the set contains no woman. -/
def noWoman : Plur → Prop := fun X => ∀ a, X a → ¬ woman a

/-- Champollion's **intersective** *and* on quantifier denotations is `Coordinator.op .j`
    (the Boolean meet `⊓` on the `Plur → Prop` carrier) —
    [champollion-2016-coordination] eq. 16. -/
def andIntersective : (Plur → Prop) → (Plur → Prop) → (Plur → Prop) :=
  Coordinator.op .j

/-- Heycock & Zamparelli's **set-product** (collective) *and* ([heycock-zamparelli-2005];
    [champollion-2016-coordination] eq. 101): holds of a plurality `P` iff `P` is the union
    `A ∪ B` of a `Q`-witness `A` and a `Q'`-witness `B`. -/
def andSetProduct (Q Q' : Plur → Prop) : Plur → Prop :=
  fun P => ∃ A B : Plur, Q A ∧ Q' B ∧ P = fun a => A a ∨ B a

theorem andIntersective_apply (Q Q' : Plur → Prop) (P : Plur) :
    andIntersective Q Q' P ↔ (Q P ∧ Q' P) := Iff.rfl

/-- The two witness sets from journal p. 608. -/
def onlyMary : Plur
  | .john => False
  | .mary => True

def onlyJohn : Plur
  | .john => True
  | .mary => False

/-- **Intersective: correct.** The intersective `Coordinator.op .j` entry predicts *No man
    and no woman smiled* FALSE — a man (John) smiled, so `no man` already fails. -/
theorem intersective_false : ¬ andIntersective noMan noWoman smiled := by
  intro h
  exact (andIntersective_apply _ _ _).mp h |>.1 .john trivial trivial

/-- **Set product: wrong.** The [heycock-zamparelli-2005] set-product entry predicts *No
    man and no woman smiled* TRUE — witness `A = {Mary}` (no man), `B = {John}` (no woman),
    `A ∪ B =` the smilers. ([champollion-2016-coordination] §7.1, journal p. 608.) -/
theorem setProduct_true : andSetProduct noMan noWoman smiled := by
  refine ⟨onlyMary, onlyJohn, ?_, ?_, ?_⟩
  · intro a ha; cases a <;> simp_all [onlyMary, man]
  · intro a ha; cases a <;> simp_all [onlyJohn, woman]
  · funext a; cases a <;> simp [smiled, onlyMary, onlyJohn]

/-- **The payoff** ([champollion-2016-coordination] §7.1): on *No man and no woman smiled*
    in the John-and-Mary-smiled model, the collective set-product entry
    ([heycock-zamparelli-2005]) and the intersective `Coordinator.op .j` entry assign
    OPPOSITE truth values. The intersective answer (FALSE) is correct; the set-product
    (join-on-individuals) entry overgenerates (TRUE) — refuting the collective theory of
    *and*. -/
theorem setProduct_overgenerates :
    andSetProduct noMan noWoman smiled ∧ ¬ andIntersective noMan noWoman smiled :=
  ⟨setProduct_true, intersective_false⟩

end Overgeneration

end Champollion2016
