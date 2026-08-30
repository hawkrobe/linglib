import Linglib.Semantics.Tense.SentDenotation
import Linglib.Studies.Anscombe1964
import Linglib.Semantics.Modality.HistoricalAlternatives
import Linglib.Semantics.Degree.Basic
import Linglib.Data.Examples.BeaverCondoravdi2003

/-!
# Beaver & Condoravdi (2003): a uniform *before* and *after*

*Before* and *after* differ in logical properties, NPI licensing and
veridicality, so since [anscombe-1964] they have been given non-uniform
semantics — a universal over the temporal clause for *before*, an existential
for *after*. The paper shows that the classical accounts of [anscombe-1964]
and [heinamaki-1974] coincide once the temporal clause is instantiated and
left-bounded, and that both reduce to a single scheme: some main-clause time
is earlier (*before*) or later (*after*) than the earliest temporal-clause
time. The two connectives then differ only in the direction of the ordering.
Veridicality is explained by branching time ([thomason-1984]): the earliest
time is computed across the historical alternatives of the evaluation world
at the main-clause time. An event earlier than that time must lie on the
actual branch, so *after* is veridical; an event later than it may lie on a
discarded branch, so *before* also has counterfactual and non-committal uses,
sorted by the context (48).

## Main statements

* `connective`, `before`, `after`: the uniform truth conditions (47); the two
  connectives are one operator with opposite orderings, by construction.
* `mem_earliestAlt_iff_isLeast`: the `earliest` operator (46) picks out the
  least instantiation time.
* `after_veridical`: under the initial branch point condition, *after*
  entails its temporal clause (§6).
* `connective_singleton_alt`: with trivial alternatives the connectives
  reduce to the extensional (45).
* `connective_alt_inst`: even a non-veridical *before* locates the temporal
  clause in some historical alternative (49).
* `Veridical`, `Counterfactual`, `NonCommittal`, `readings_partition`: the
  three readings of *before* partition the nonempty contexts (48).
* `anscombe_before_complement_DE`, `anscombe_after_complement_UE`,
  `anscombe_before_of_empty`: the classical rendering's monotonicity — the
  NPI environments (§3) — and the overgeneration (32) that motivates
  requiring instantiation.

## References

* [beaver-condoravdi-2003]: A uniform analysis of *before* and *after*.
  SALT 13.
* [anscombe-1964]: Before and after. *The Philosophical Review* 74.
* [heinamaki-1974]: Semantics of English Temporal Connectives.
* [thomason-1984]: Combinations of tense and modality.
-/

namespace BeaverCondoravdi2003

open Tense
open Core.Order (maxOnScale)

variable {W T : Type*} [LinearOrder T]

/-! ### Historical alternatives and the initial branch point condition (§6) -/

/-- The initial branch point condition (§6): every historical alternative of
`w` at `t` agrees with `w` at all earlier times, so branching happens only
from `t` onwards. -/
def initialBranchPoint (alt : HistoricalAlternatives W T)
    (agree : T → W → W → Prop) : Prop :=
  ∀ w t, ∀ w' ∈ alt ⟨w, t⟩, ∀ t', t' < t → agree t' w w'

/-! ### The `earliest` operator across alternatives (44)–(46) -/

/-- The times at which `B` is instantiated in some world of `worlds` (46). -/
def instTimes (worlds : Set W) (B : Set (W × T)) : Set T :=
  { t | ∃ w ∈ worlds, (w, t) ∈ B }

/-- The earliest `B`-time across the historical alternatives of `w` at `t`
(46): the least instantiation time, as `maxOnScale .lt`. -/
def earliestAlt (alt : HistoricalAlternatives W T) (B : Set (W × T))
    (w : W) (t : T) : Set T :=
  maxOnScale .lt (instTimes (alt ⟨w, t⟩) B)

/-- The `earliest` operator picks out exactly the least instantiation time. -/
theorem mem_earliestAlt_iff_isLeast (alt : HistoricalAlternatives W T)
    (B : Set (W × T)) (w : W) (t te : T) :
    te ∈ earliestAlt alt B w t ↔ IsLeast (instTimes (alt ⟨w, t⟩) B) te := by
  constructor
  · rintro ⟨hmem, hmin⟩
    refine ⟨hmem, λ y hy => ?_⟩
    by_cases hy_eq : y = te
    · exact le_of_eq hy_eq.symm
    · exact le_of_lt (hmin y hy hy_eq)
  · rintro ⟨hmem, hlb⟩
    exact ⟨hmem, λ y hy hne => lt_of_le_of_ne (hlb hy) (Ne.symm hne)⟩

/-! ### The uniform truth conditions (47) -/

/-- The uniform temporal connective (47): some main-clause time in `w` stands
in `cmp` to the earliest temporal-clause time across the historical
alternatives at that time. *Before* and *after* differ only in `cmp`. -/
def connective (cmp : T → T → Prop) (A B : Set (W × T))
    (alt : HistoricalAlternatives W T) (w : W) : Prop :=
  ∃ t, (w, t) ∈ A ∧ ∃ te ∈ earliestAlt alt B w t, cmp t te

/-- *A before B* (47). -/
abbrev before (A B : Set (W × T)) (alt : HistoricalAlternatives W T)
    (w : W) : Prop :=
  connective (· < ·) A B alt w

/-- *A after B* (47). -/
abbrev after (A B : Set (W × T)) (alt : HistoricalAlternatives W T)
    (w : W) : Prop :=
  connective (· > ·) A B alt w

/-! ### Instantiation and veridicality (§6) -/

/-- `B` is instantiated in `w`: it holds of some time there. -/
def Inst (B : Set (W × T)) (w : W) : Prop :=
  ∃ t, (w, t) ∈ B

/-- *After* is veridical (§6): under the initial branch point condition, the
earliest `B`-time precedes the `A`-time, so branching has not yet happened
there and the `B`-event lies on the actual branch. `eventLocal` says `B` only
cares about matters of particular fact, which agreeing worlds share. -/
theorem after_veridical (A B : Set (W × T)) (alt : HistoricalAlternatives W T)
    (agree : T → W → W → Prop)
    (hIBP : initialBranchPoint alt agree)
    (eventLocal : ∀ w w' t, agree t w w' → (w', t) ∈ B → (w, t) ∈ B)
    (w : W) :
    after A B alt w → Inst B w := by
  rintro ⟨t_A, _, t_B, ⟨⟨w', hw'_alt, hw'_B⟩, _⟩, ht_lt⟩
  exact ⟨t_B, eventLocal w w' t_B (hIBP w t_A w' hw'_alt t_B ht_lt) hw'_B⟩

/-- With trivial alternatives — B&C set `alt(w,t) = {w}` whenever `B` is
instantiated in `w` — the connectives reduce to the extensional (45): the
earliest `B`-time of `w` itself. -/
theorem connective_singleton_alt (cmp : T → T → Prop) (A B : Set (W × T))
    (alt : HistoricalAlternatives W T) (w : W) (h : ∀ t, alt ⟨w, t⟩ = {w}) :
    connective cmp A B alt w ↔
      ∃ t, (w, t) ∈ A ∧ ∃ te, IsLeast {t' | (w, t') ∈ B} te ∧ cmp t te := by
  have hs : ∀ t : T, instTimes (alt ⟨w, t⟩) B = {t' | (w, t') ∈ B} := fun t => by
    rw [h t]; ext t'; simp [instTimes]
  refine exists_congr fun t => and_congr_right fun _ => exists_congr fun te =>
    and_congr_left fun _ => ?_
  rw [mem_earliestAlt_iff_isLeast, hs t]

/-- Even a non-veridical *before* locates `B` on a branch (49): if the
connective holds at `w`, some main-clause time has a historical alternative
in which `B` is instantiated. -/
theorem connective_alt_inst (cmp : T → T → Prop) (A B : Set (W × T))
    (alt : HistoricalAlternatives W T) (w : W) :
    connective cmp A B alt w →
      ∃ t, (w, t) ∈ A ∧ ∃ w' ∈ alt ⟨w, t⟩, Inst B w' := by
  rintro ⟨t, htA, te, ⟨⟨w', hw', hB⟩, -⟩, -⟩
  exact ⟨t, htA, w', hw', te, hB⟩

/-! ### The three readings of *before* (48) -/

/-- The three contextual readings of *before* (48). -/
inductive BeforeReading where
  | veridical
  | counterfactual
  | nonCommittal
  deriving DecidableEq, Repr

/-- Veridical reading (48): every context world instantiates `B`. -/
def Veridical (B : Set (W × T)) (context : Set W) : Prop :=
  ∀ w ∈ context, Inst B w

/-- Counterfactual reading (48): no context world instantiates `B`. -/
def Counterfactual (B : Set (W × T)) (context : Set W) : Prop :=
  ∀ w ∈ context, ¬Inst B w

/-- Non-committal reading (48): some context worlds instantiate `B` and some
do not. -/
def NonCommittal (B : Set (W × T)) (context : Set W) : Prop :=
  (∃ w ∈ context, Inst B w) ∧ ∃ w ∈ context, ¬Inst B w

omit [LinearOrder T] in
/-- The three readings are mutually exclusive and exhaust the nonempty
contexts (48). -/
theorem readings_partition (B : Set (W × T)) (context : Set W)
    (hc : context.Nonempty) :
    (Veridical B context ∨ Counterfactual B context ∨ NonCommittal B context) ∧
      ¬(Veridical B context ∧ Counterfactual B context) ∧
      ¬(Veridical B context ∧ NonCommittal B context) ∧
      ¬(Counterfactual B context ∧ NonCommittal B context) := by
  obtain ⟨w0, hw0⟩ := hc
  refine ⟨?_, fun ⟨hv, hcf⟩ => hcf w0 hw0 (hv w0 hw0),
    fun ⟨hv, _, w, hw, hnw⟩ => hnw (hv w hw),
    fun ⟨hcf, ⟨w, hw, hiw⟩, _⟩ => hcf w hw hiw⟩
  by_cases hv : Veridical B context
  · exact Or.inl hv
  by_cases hcf : Counterfactual B context
  · exact Or.inr (Or.inl hcf)
  refine Or.inr (Or.inr ⟨?_, ?_⟩)
  · by_contra hno
    exact hcf fun w hw hi => hno ⟨w, hw, hi⟩
  · by_contra hno
    exact hv fun w hw => Classical.byContradiction fun hn => hno ⟨w, hw, hn⟩

/-! ### The classical rendering: complement monotonicity and overgeneration -/

section Classical

open Anscombe1964

variable {Time : Type*} [LinearOrder Time] (A B B' : SentDenotation Time)

/-- The complement of [anscombe-1964]'s *before* is downward entailing: the universal over
`B` reverses inclusion — the NPI-licensing environment. -/
theorem anscombe_before_complement_DE (h : timeTrace B' ⊆ timeTrace B) :
    Anscombe.before A B → Anscombe.before A B' :=
  fun ⟨t, ht, hall⟩ => ⟨t, ht, fun t' ht' => hall t' (h ht')⟩

/-- The complement of [anscombe-1964]'s *after* is upward entailing. -/
theorem anscombe_after_complement_UE (h : timeTrace B ⊆ timeTrace B') :
    Anscombe.after A B → Anscombe.after A B' :=
  fun ⟨t, ht, t', ht', hlt⟩ => ⟨t, ht, t', h ht', hlt⟩

/-- The overgeneration of (32)–(33): with a never-instantiated `B`, *A before B* is vacuously
true of any instantiated `A` — *David ate ketchup before he won all the gold medals* comes out
true if he never won. -/
theorem anscombe_before_of_empty (hB : timeTrace B = ∅) (hA : (timeTrace A).Nonempty) :
    Anscombe.before A B :=
  let ⟨t, ht⟩ := hA
  ⟨t, ht, fun t' ht' => absurd (hB ▸ ht') (Set.notMem_empty t')⟩

end Classical

end BeaverCondoravdi2003
