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
the modal base of *will*. Restricted to times from, up to, or strictly after the index's own,
the alternatives give Condoravdi's historical base and Klecha's doxastic and circumstantial
bases. A relation has the historical properties when agreement up to each time is an
equivalence and the alternatives shrink as time advances, and it is then a T × W frame whose
historical necessity is truth throughout the alternatives.

## Main definitions

* `HistoricalAlternatives`, `metaphysicalBase`: the relation and its curried modal base.
* `historicalBase`, `actualHistoryBase`, `futureHistoryBase`: its temporal slices.
* `HistoricalProperties`, `ofDatedFacts`: the standard properties, and agreement on dated facts.
* `settled`, `diverse`: settledness over a common ground, and Condoravdi's diversity condition.
* `toTWFrame`: a relation with the historical properties as a `Temporal.TWFrame`.

## Main results

* `time_le_of_mem_actualHistoryBase`: Abusch's Upper Limit Constraint for the doxastic base.
* `actualHistoryBase_union_futureHistoryBase`: the actual and future bases partition the
  alternatives.
* `HistoricalProperties.history_eq_of_mem`: the alternatives of an alternative are the same.
* `historicalProperties_ofDatedFacts`: agreement on dated facts has the historical properties.
* `settled_not_diverse`, `settled_iff_determined`: a settled property is not diverse, and is
  historically determined in the frame.

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

/-! ### Historical equivalence -/

/-- A historical-alternatives relation has the standard properties of [condoravdi-2002] when
agreement up to each time is an equivalence and the alternatives shrink as time advances. -/
structure HistoricalProperties [Preorder T] (history : HistoricalAlternatives W T) : Prop where
  /-- Agreement up to a time is an equivalence relation. -/
  equivalence (t : T) : Equivalence fun w w' ↦ w' ∈ history (w, t)
  /-- The alternatives shrink as time advances. -/
  antitone (w : W) : Antitone (metaphysicalBase history w)

/-- Agreement up to a time partitions the worlds, so an alternative of a world has the same
alternatives as the world. -/
theorem HistoricalProperties.history_eq_of_mem [Preorder T] {history : HistoricalAlternatives W T}
    (hp : HistoricalProperties history) {w w' : W} {t : T} (h : w' ∈ history (w, t)) :
    history (w', t) = history (w, t) :=
  Set.ext fun _ ↦ ⟨(hp.equivalence t).trans h, (hp.equivalence t).trans ((hp.equivalence t).symm h)⟩

/-- Over a stock of dated facts, worlds are historical alternatives up to a time when they agree
on every fact dated at or before it, the world–time model of [thomason-1984]. -/
def ofDatedFacts [LE T] {F : Type*} (time : F → T) (holds : W → F → Prop) :
    HistoricalAlternatives W T :=
  fun s ↦ {w' | ∀ f, time f ≤ s.time → (holds s.world f ↔ holds w' f)}

/-- Agreement on dated facts is an equivalence at every time and is preserved backward. -/
theorem historicalProperties_ofDatedFacts [Preorder T] {F : Type*} (time : F → T)
    (holds : W → F → Prop) : HistoricalProperties (ofDatedFacts time holds) where
  equivalence _ :=
    ⟨fun _ _ _ ↦ Iff.rfl, fun h f hf ↦ (h f hf).symm, fun h₁ h₂ f hf ↦ (h₁ f hf).trans (h₂ f hf)⟩
  antitone _ _ _ hle _ h f hf := h f (hf.trans hle)

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

/-! ### Grounding in the T × W object logic

A relation with the historical properties satisfies exactly the axioms of a `Temporal.TWFrame`,
per-time equivalence and backward closure, so it is a T × W frame, and the object logic's
historical necessity `N` is quantification over the metaphysical base: the denotational base
and the object-language modality are one operator ([thomason-1984], [von-kutschera-1997]). -/

section TWFrame

open Temporal

variable [LinearOrder T] {Atom : Type*} (history : HistoricalAlternatives W T)
  (hp : HistoricalProperties history)

/-- A relation with the historical properties as a `TWFrame`, with agreement up to a time as
its similarity. -/
def toTWFrame : TWFrame T W where
  sim t w w' := w' ∈ history (w, t)
  sim_equiv := hp.equivalence
  sim_backward w _ hle h := hp.antitone w hle h

@[simp] theorem toTWFrame_sim (t : T) (w w' : W) :
    (toTWFrame history hp).sim t w w' ↔ w' ∈ metaphysicalBase history w t := Iff.rfl

/-- Historical necessity `N` in the object logic is truth throughout the metaphysical base. -/
theorem toTWFrame_sat_N_atom (V : Atom → T → W → Prop) (p : Atom) (t : T) (w : W) :
    (toTWFrame history hp).sat V (.N (.atom p)) t w ↔
      ∀ w' ∈ metaphysicalBase history w t, V p t w' := by
  simp only [TWFrame.sat_N, TWFrame.sat_atom, toTWFrame_sim]

/-- The all-worlds modality `box` is truth in every world, the unrestricted base. -/
theorem toTWFrame_sat_box_atom (V : Atom → T → W → Prop) (p : Atom) (t : T) (w : W) :
    (toTWFrame history hp).sat V (.box (.atom p)) t w ↔ ∀ w', V p t w' := by
  simp only [TWFrame.sat_box, TWFrame.sat_atom]

include hp in
/-- The evaluation world is a metaphysical alternative to itself. -/
theorem mem_metaphysicalBase_self (t : T) (w : W) :
    w ∈ metaphysicalBase history w t := (hp.equivalence t).refl w

/-- A formula is historically determined at `(t, w)`, decided as `N a ∨ N ¬a`, iff it is
constant across the metaphysical base, the single-world core of settledness. -/
theorem toTWFrame_N_or_N_neg_iff (V : Atom → T → W → Prop) (a : OForm Atom) (t : T) (w : W) :
    ((toTWFrame history hp).sat V a.N t w ∨ (toTWFrame history hp).sat V a.neg.N t w) ↔
      ∀ w' ∈ metaphysicalBase history w t,
        ((toTWFrame history hp).sat V a t w' ↔ (toTWFrame history hp).sat V a t w) := by
  simp only [TWFrame.sat_N, TWFrame.sat_neg, toTWFrame_sim]
  constructor
  · rintro (h | h) w' hw'
    · exact iff_of_true (h w' hw') (h w (mem_metaphysicalBase_self history hp t w))
    · exact iff_of_false (h w' hw') (h w (mem_metaphysicalBase_self history hp t w))
  · intro hd
    rcases Classical.em ((toTWFrame history hp).sat V a t w) with hw | hw
    · exact Or.inl fun w' hw' ↦ (hd w' hw').mpr hw
    · exact Or.inr fun w' hw' ha ↦ hw ((hd w' hw').mp ha)

/-- Settledness over a common ground is historical determinacy, `N P ∨ N ¬P`, at every
common-ground world. Here `P` is the world proposition after forward instantiation, whose
wrapper `AT([t₀,_), ·, P)` the caller discharges. -/
theorem settled_iff_determined (cg : Set W) (P : W → Prop) (t : T) :
    settled history cg t P ↔
      ∀ w ∈ cg,
        ((toTWFrame history hp).sat (fun _ _ w' ↦ P w') (.N (.atom ())) t w ∨
         (toTWFrame history hp).sat (fun _ _ w' ↦ P w') (.N (.neg (.atom ()))) t w) := by
  unfold settled
  refine forall_congr' fun w ↦ imp_congr_right fun _ ↦ ?_
  rw [toTWFrame_N_or_N_neg_iff history hp]
  simp only [TWFrame.sat_atom]
  exact forall₂_congr fun _ _ ↦ Iff.comm

end TWFrame

end HistoricalAlternatives
