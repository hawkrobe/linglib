module

public import Mathlib.Data.Set.Prod
public import Mathlib.Order.Interval.Set.Disjoint
public import Mathlib.Order.Interval.Set.LinearOrder
public import Linglib.Semantics.Reference.Context.Index
public import Linglib.Logic.Temporal.Basic

/-!
# Historical alternatives

The historical alternatives of a world at a time are the worlds that perfectly match it in
matters of particular fact up to that time ([lewis-1979-time-arrow],
[cariani-santorio-2018]). A `HistoricalAlternatives` relation sends a world–time index to that
set of worlds, and the metaphysical modal base of [condoravdi-2002] is the relation curried,
`metaphysicalBase`. The temporal slices of the relation are products of the alternatives with
a ray of times: the historical base of prospective times, `historicalBase`, the actual-history
base of times up to the evaluation time, `actualHistoryBase`, which [klecha-2016] takes as the
doxastic base and from which the Upper Limit Constraint of [abusch-1997] follows,
`time_le_of_mem_actualHistoryBase`, and the future-history base of later times,
`futureHistoryBase`, his circumstantial base; the actual and future bases partition the
alternatives, `disjoint_actualHistoryBase_futureHistoryBase` and
`actualHistoryBase_union_futureHistoryBase`. A relation has the `HistoricalProperties` of
[condoravdi-2002] when agreement up to each time is an equivalence and the alternatives shrink
as time advances, which agreement on a stock of dated facts does,
`historicalProperties_ofDatedFacts`. A property settled over a common ground, `settled`,
excludes the diversity a metaphysical possibility modal needs, `settled_not_diverse`. A
relation with the properties is a `Temporal.TWFrame`, `toTWFrame`, on which the object
logic's historical necessity is truth throughout the metaphysical base, `toTWFrame_sat_N_atom`,
and settledness is historical determinacy, `settled_iff_determined` ([thomason-1984],
[von-kutschera-1997]).

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

/-- The historical alternatives of a world–time index: the worlds that agree with its world up
to its time, the basis of the open-future modal base. -/
def HistoricalAlternatives (W T : Type*) := Index W T → Set W

namespace HistoricalAlternatives

variable {W T : Type*}

/-- The metaphysical modal base of [condoravdi-2002]: at a world and time, the worlds sharing
the world's history up to that time, the relation itself curried. -/
abbrev metaphysicalBase (history : HistoricalAlternatives W T) : W → T → Set W :=
  Function.curry history

/-! ### The temporal slices -/

section Slices

variable [Preorder T] (history : HistoricalAlternatives W T) (s : Index W T)

/-- The historical modal base: the alternatives of an index at times at or after its own, the
past fixed and the future branching ([thomason-1984], [condoravdi-2002]). -/
def historicalBase : Set (Index W T) := history s ×ˢ Ici s.time

/-- The actual-history base, [klecha-2016]'s doxastic base: the alternatives at times at or
before the index's own. -/
def actualHistoryBase : Set (Index W T) := history s ×ˢ Iic s.time

/-- The future-history base, [klecha-2016]'s circumstantial base: the alternatives at times
strictly after the index's own. -/
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

/-- A situation in the actual-history base is no later than the index: the Upper Limit
Constraint of [abusch-1997], as [klecha-2016] derives it from the doxastic base. -/
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

/-- The standard properties of a historical-alternatives relation ([condoravdi-2002]):
agreement up to each time is an equivalence, and the alternatives shrink as time advances. -/
structure HistoricalProperties [Preorder T] (history : HistoricalAlternatives W T) : Prop where
  /-- Agreement up to a time is an equivalence relation. -/
  equivalence (t : T) : Equivalence fun w w' ↦ w' ∈ history (w, t)
  /-- The alternatives shrink as time advances. -/
  antitone (w : W) : Antitone (metaphysicalBase history w)

/-- The historical alternatives determined by a stock of dated facts: worlds agree up to a time
when they agree on every fact dated at or before it, the world–time model of
[thomason-1984]. -/
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
each of its worlds agree on it ([condoravdi-2002]): past and present issues are settled,
future ones need not be. -/
def settled (history : HistoricalAlternatives W T) (cg : Set W) (t : T) (P : W → Prop) : Prop :=
  ∀ w ∈ cg, ∀ w' ∈ history (w, t), (P w ↔ P w')

/-- The diversity condition on a modal base for a possibility modal ([condoravdi-2002]): some
common-ground world sees worlds disagreeing on the property. -/
def diverse (MB : W → T → Set W) (cg : Set W) (t : T) (P : W → Prop) : Prop :=
  ∃ w ∈ cg, ∃ w' ∈ MB w t, ∃ w'' ∈ MB w t, P w' ∧ ¬ P w''

/-- A settled property is not diverse over a modal base within the metaphysical one:
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

/-- A formula is historically determined at `(t, w)`, the object logic decides it as `N a ∨ N ¬a`,
iff it is constant across the metaphysical base: the single-world, formula-general core of
settledness. -/
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

/-- Condoravdi's settledness over a common ground is object-logic historical determinacy at
every common-ground world, `N P ∨ N ¬P` for the lifted valuation: settled-whether, bilateral
and history-blind, not the unilateral inevitability. `P` is the world proposition after forward
instantiation, Condoravdi's `AT([t₀,_), ·, P)`, whose wrapper the caller discharges. -/
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
