module

public import Mathlib.Data.Set.Prod
public import Mathlib.Order.Interval.Set.Disjoint
public import Mathlib.Order.Interval.Set.LinearOrder
public import Linglib.Semantics.Reference.Context.Index
public import Linglib.Logic.Temporal.Basic

/-!
# Historical alternatives

The historical alternatives of a world at a time are the worlds that perfectly match it in
matters of particular fact up to that time, Lewis's notion, which Cariani and Santorio take as
the modal base of *will*. A `HistoricalAlternatives` relation sends a world–time index to a set
of worlds; restricted to times from, up to, or strictly after the index's own, it gives
Condoravdi's historical base and Klecha's doxastic and circumstantial bases. A T × W frame
determines its alternatives, the classes of its historical equivalence.

## Main definitions

* `HistoricalAlternatives`, `metaphysicalBase`: the relation and its curried modal base.
* `historicalBase`, `actualHistoryBase`, `futureHistoryBase`: its temporal slices.
* `Temporal.TWFrame.alternatives`: the historical alternatives of a T × W frame.
* `settled`, `diverse`: settledness over a common ground, and Condoravdi's diversity condition.

## Main results

* `time_le_of_mem_actualHistoryBase`: Abusch's Upper Limit Constraint for the doxastic base.
* `actualHistoryBase_union_futureHistoryBase`: the actual and future bases partition the
  alternatives.
* `Temporal.TWFrame.alternatives_eq_of_mem`: the alternatives of an alternative are the same.
* `settled_not_diverse`: a settled property is not diverse.
* `settled_alternatives_iff`: over a frame, settledness is historical necessity of the property
  or its negation.

## References

* [D. Lewis, *Counterfactual dependence and time's arrow* (1979)][lewis-1979-time-arrow]
* [F. Cariani and P. Santorio, *Will done better: selection semantics, future credence, and
  indeterminacy* (2018)][cariani-santorio-2018]
* [C. Condoravdi, *Temporal interpretation of modals: modals for the present and for the
  past* (2002)][condoravdi-2002]
* [P. Klecha, *Modality and embedded temporal operators* (2016)][klecha-2016]
* [D. Abusch, *Sequence of tense and temporal de re* (1997)][abusch-1997]
* [R. H. Thomason, *Combinations of tense and modality* (1984)][thomason-1984]
* [F. von Kutschera, *T × W completeness* (1997)][von-kutschera-1997]
-/

@[expose] public section

open Reference Set
open scoped ModalLogic

/-- The historical alternatives of a world–time index are the worlds that agree with its world
up to its time. -/
def HistoricalAlternatives (W T : Type*) := Index W T → Set W

namespace HistoricalAlternatives

variable {W T : Type*}

/-- The metaphysical modal base of [condoravdi-2002] is the relation curried, giving at a world
and time the worlds that share the world's history up to that time. -/
abbrev metaphysicalBase (history : HistoricalAlternatives W T) : W → T → Set W :=
  Function.curry history

/-! ### The temporal slices -/

section Slices

variable [Preorder T] (history : HistoricalAlternatives W T) (s : Index W T)

/-- The historical modal base pairs the alternatives of an index with the times at or after its
own, the past fixed and the future branching ([thomason-1984], [condoravdi-2002]). -/
def historicalBase : Set (Index W T) := history s ×ˢ Ici s.time

/-- The actual-history base, [klecha-2016]'s doxastic base, pairs the alternatives with the
times at or before the index's own. -/
def actualHistoryBase : Set (Index W T) := history s ×ˢ Iic s.time

/-- The future-history base, [klecha-2016]'s circumstantial base, pairs the alternatives with
the times strictly after the index's own. -/
def futureHistoryBase : Set (Index W T) := history s ×ˢ Ioi s.time

variable {history s} {s' : Index W T}

theorem mem_historicalBase :
    s' ∈ historicalBase history s ↔ s'.world ∈ history s ∧ s.time ≤ s'.time :=
  Iff.rfl

theorem mem_actualHistoryBase :
    s' ∈ actualHistoryBase history s ↔ s'.world ∈ history s ∧ s'.time ≤ s.time :=
  Iff.rfl

theorem mem_futureHistoryBase :
    s' ∈ futureHistoryBase history s ↔ s'.world ∈ history s ∧ s.time < s'.time :=
  Iff.rfl

/-- A situation in the actual-history base is no later than the index, the Upper Limit
Constraint of [abusch-1997] as [klecha-2016] derives it from the doxastic base. -/
theorem time_le_of_mem_actualHistoryBase (h : s' ∈ actualHistoryBase history s) :
    s'.time ≤ s.time :=
  h.2

/-- A situation in the future-history base is later than the index. -/
theorem time_lt_of_mem_futureHistoryBase (h : s' ∈ futureHistoryBase history s) :
    s.time < s'.time :=
  h.2

theorem futureHistoryBase_subset_historicalBase :
    futureHistoryBase history s ⊆ historicalBase history s :=
  prod_mono le_rfl Ioi_subset_Ici_self

theorem disjoint_actualHistoryBase_futureHistoryBase :
    Disjoint (actualHistoryBase history s) (futureHistoryBase history s) :=
  disjoint_prod.2 (Or.inr (Iic_disjoint_Ioi le_rfl))

end Slices

/-- The actual and future bases together are the alternatives at every time. -/
theorem actualHistoryBase_union_futureHistoryBase [LinearOrder T]
    (history : HistoricalAlternatives W T) (s : Index W T) :
    actualHistoryBase history s ∪ futureHistoryBase history s = history s ×ˢ univ := by
  rw [actualHistoryBase, futureHistoryBase, ← prod_union, Iic_union_Ioi]

/-! ### The alternatives of a T × W frame

The historical alternatives of a T × W frame are its classes of historical equivalence, so a
world is an alternative to itself and the alternatives of an alternative are the same. -/

end HistoricalAlternatives

namespace Temporal.TWFrame

open HistoricalAlternatives

variable {W T : Type*} [Preorder T] (F : TWFrame W T) {w v : W} {t : T}

/-- The historical alternatives of a frame, at an index the worlds historically equivalent to
its world at its time. -/
def alternatives : HistoricalAlternatives W T := fun i ↦ {v | F.sim i.time i.world v}

variable {F}

@[simp] theorem mem_alternatives : v ∈ F.alternatives (w, t) ↔ F.sim t w v := Iff.rfl

theorem mem_alternatives_self : w ∈ F.alternatives (w, t) := (F.sim t).iseqv.refl w

/-- Historical equivalence partitions the worlds, so an alternative of a world has the same
alternatives as the world. -/
theorem alternatives_eq_of_mem (h : v ∈ F.alternatives (w, t)) :
    F.alternatives (v, t) = F.alternatives (w, t) :=
  Set.ext fun _ ↦ ⟨(F.sim t).iseqv.trans h, (F.sim t).iseqv.trans ((F.sim t).iseqv.symm h)⟩

end Temporal.TWFrame

namespace HistoricalAlternatives

variable {W T : Type*}

/-! ### Settledness and diversity -/

/-- A property is settled at a time over a common ground when the historical alternatives of
each of its worlds agree on it ([condoravdi-2002]). Past and present issues are settled, and
future ones need not be. -/
def settled (history : HistoricalAlternatives W T) (cg : Set W) (t : T) (P : W → Prop) : Prop :=
  ∀ w ∈ cg, ∀ w' ∈ history (w, t), (P w ↔ P w')

/-- A modal base meets the diversity condition of [condoravdi-2002] for a property when some
common-ground world sees worlds disagreeing on it. -/
def diverse (MB : W → T → Set W) (cg : Set W) (t : T) (P : W → Prop) : Prop :=
  ∃ w ∈ cg, ∃ w' ∈ MB w t, ∃ w'' ∈ MB w t, P w' ∧ ¬ P w''

/-- A settled property is not diverse over a modal base within the metaphysical one, so
metaphysical readings of possibility modals are blocked for settled properties. -/
theorem settled_not_diverse {history : HistoricalAlternatives W T} {MB : W → T → Set W}
    {cg : Set W} {t : T} {P : W → Prop} (hMB : ∀ w ∈ cg, MB w t ⊆ history (w, t))
    (h : settled history cg t P) : ¬ diverse MB cg t P :=
  fun ⟨w, hw, w', hw', w'', hw'', hP, hnP⟩ ↦
    hnP ((h w hw w'' (hMB w hw hw'')).mp ((h w hw w' (hMB w hw hw')).mpr hP))

/-- Over the alternatives of a T × W frame, a property is settled at a time over a common ground
exactly when, at every common-ground world, it or its negation is historically necessary. -/
theorem settled_alternatives_iff [Preorder T] {F : Temporal.TWFrame W T} {cg : Set W} {t : T}
    {P : W → Prop} :
    settled F.alternatives cg t P ↔ ∀ w ∈ cg, □[F.alt t] P w ∨ □[F.alt t] (fun v ↦ ¬ P v) w := by
  refine forall₂_congr fun w _ ↦ ⟨fun h ↦ ?_, fun h v hv ↦ ?_⟩
  · by_cases hw : P w
    exacts [.inl fun v hv ↦ (h v hv).1 hw, .inr fun v hv hv' ↦ hw ((h v hv).2 hv')]
  · rcases h with h | h
    · exact iff_of_true (h w ((F.sim t).iseqv.refl w)) (h v hv)
    · exact iff_of_false (h w ((F.sim t).iseqv.refl w)) (h v hv)

end HistoricalAlternatives
