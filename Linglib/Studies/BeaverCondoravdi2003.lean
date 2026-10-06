module

public import Linglib.Semantics.Tense.RunTimes
public import Linglib.Studies.Anscombe1964
public import Linglib.Semantics.Modality.HistoricalAlternatives
public import Linglib.Data.Examples.BeaverCondoravdi2003

/-!
# Beaver and Condoravdi (2003): a uniform *before* and *after*

*Before* and *after* differ in logical properties, NPI licensing and veridicality, and since
Anscombe they have been given non-uniform semantics, a universal over the temporal clause for
*before* and an existential for *after*. Beaver and Condoravdi show that the accounts of Anscombe
and Heinämäki coincide once the temporal clause is instantiated and left-bounded, and reduce both
to one connective, which holds when some main-clause time is earlier or later than the earliest
temporal-clause time. Following Thomason, that earliest time is computed across the historical
alternatives of the evaluation world at the main-clause time. An earlier event lies on the actual
branch, so *after* is veridical, while a later one may lie on a discarded branch, so *before* also
has counterfactual and non-committal uses, which the context sorts (48).

## Main statements

* `connective`: the uniform truth conditions (47), one operator for *before* and *after* with
  opposite orderings.
* `after_veridical`: the initial branch point condition makes *after* entail its temporal clause
  (§6).
* `readings_partition`: the veridical, counterfactual and non-committal readings of *before*
  partition the nonempty contexts (48).

## References

* [beaver-condoravdi-2003]
* [anscombe-1964]
* [heinamaki-1974]
* [thomason-1984]
-/

@[expose] public section

namespace BeaverCondoravdi2003

open Tense

variable {W T : Type*}

/-! ### Instantiation -/

/-- The times at which `B` is instantiated in some world of `worlds` (46). -/
def instTimes (worlds : Set W) (B : Set (W × T)) : Set T :=
  { t | ∃ w ∈ worlds, (w, t) ∈ B }

/-- `Inst B w` says that `B` is instantiated in `w`, holding of some time there. -/
def Inst (B : Set (W × T)) (w : W) : Prop :=
  ∃ t, (w, t) ∈ B

section Connective

variable [LinearOrder T]

/-! ### The uniform truth conditions (44)–(47) -/

/-- The initial branch point condition (§6) says that every historical alternative of `w` at `t`
agrees with `w` at all earlier times, so branching happens only from `t` onwards. -/
def initialBranchPoint (alt : HistoricalAlternatives W T)
    (agree : T → W → W → Prop) : Prop :=
  ∀ w t, ∀ w' ∈ alt ⟨w, t⟩, ∀ t', t' < t → agree t' w w'

/-- The earliest `B`-time across the historical alternatives of `w` at `t`, (46), is the least
instantiation time. -/
def earliestAlt (alt : HistoricalAlternatives W T) (B : Set (W × T))
    (w : W) (t : T) : Set T :=
  { te | IsLeast (instTimes (alt ⟨w, t⟩) B) te }

/-- The uniform temporal connective, (47), holds when some main-clause time in `w` stands in `cmp`
to the earliest temporal-clause time across the historical alternatives at that time. *Before* and
*after* differ only in `cmp`. -/
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

/-! ### Veridicality (§6) -/

/-- *After* is veridical (§6). Under the initial branch point condition the earliest `B`-time
precedes the `A`-time, so branching has not yet happened there and the `B`-event lies on the actual
branch. `eventLocal` says `B` only cares about matters of particular fact, which agreeing worlds
share. -/
theorem after_veridical (A B : Set (W × T)) (alt : HistoricalAlternatives W T)
    (agree : T → W → W → Prop)
    (hIBP : initialBranchPoint alt agree)
    (eventLocal : ∀ w w' t, agree t w w' → (w', t) ∈ B → (w, t) ∈ B)
    (w : W) :
    after A B alt w → Inst B w := by
  rintro ⟨t_A, _, t_B, ⟨⟨w', hw'_alt, hw'_B⟩, _⟩, ht_lt⟩
  exact ⟨t_B, eventLocal w w' t_B (hIBP w t_A w' hw'_alt t_B ht_lt) hw'_B⟩

/-- With the trivial alternatives B&C set, `alt(w,t) = {w}` whenever `B` is instantiated
in `w`, the connectives reduce to the extensional (45), the earliest `B`-time of `w` itself. -/
theorem connective_singleton_alt (cmp : T → T → Prop) (A B : Set (W × T))
    (alt : HistoricalAlternatives W T) (w : W) (h : ∀ t, alt ⟨w, t⟩ = {w}) :
    connective cmp A B alt w ↔
      ∃ t, (w, t) ∈ A ∧ ∃ te, IsLeast {t' | (w, t') ∈ B} te ∧ cmp t te := by
  have hs : ∀ t : T, instTimes (alt ⟨w, t⟩) B = {t' | (w, t') ∈ B} := fun t => by
    rw [h t]; ext t'; simp [instTimes]
  refine exists_congr fun t => and_congr_right fun _ => exists_congr fun te =>
    and_congr_left fun _ => ?_
  simp only [earliestAlt, Set.mem_ofPred_eq]
  rw [hs t]

/-- Even a non-veridical *before* locates `B` on a branch, (49), since if the connective holds at
`w`, some main-clause time has a historical alternative in which `B` is instantiated. -/
theorem connective_alt_inst (cmp : T → T → Prop) (A B : Set (W × T))
    (alt : HistoricalAlternatives W T) (w : W) :
    connective cmp A B alt w →
      ∃ t, (w, t) ∈ A ∧ ∃ w' ∈ alt ⟨w, t⟩, Inst B w' := by
  rintro ⟨t, htA, te, ⟨⟨w', hw', hB⟩, -⟩, -⟩
  exact ⟨t, htA, w', hw', te, hB⟩

end Connective

/-! ### The three readings of *before* (48) -/

/-- The three contextual readings of *before* (48). -/
inductive BeforeReading where
  | veridical
  | counterfactual
  | nonCommittal
  deriving DecidableEq, Repr

/-- The veridical reading, (48), has every context world instantiate `B`. -/
def Veridical (B : Set (W × T)) (context : Set W) : Prop :=
  ∀ w ∈ context, Inst B w

/-- The counterfactual reading, (48), has no context world instantiate `B`. -/
def Counterfactual (B : Set (W × T)) (context : Set W) : Prop :=
  ∀ w ∈ context, ¬Inst B w

/-- The non-committal reading, (48), has some context worlds instantiate `B` and some not. -/
def NonCommittal (B : Set (W × T)) (context : Set W) : Prop :=
  (∃ w ∈ context, Inst B w) ∧ ∃ w ∈ context, ¬Inst B w

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

variable {T : Type*} [LinearOrder T] (A B B' : Set (NonemptyInterval T))

/-- The complement of [anscombe-1964]'s quantificational *before* is downward entailing, the
NPI-licensing environment, since the universal over `B` reverses inclusion. -/
theorem anscombe_before_complement_DE (h : timeTrace B' ⊆ timeTrace B) :
    Anscombe.beforeEver A B → Anscombe.beforeEver A B' :=
  fun ⟨t, ht, hall⟩ => ⟨t, ht, fun t' ht' => hall t' (h ht')⟩

/-- The complement of [anscombe-1964]'s *after* is upward entailing. -/
theorem anscombe_after_complement_UE (h : timeTrace B ⊆ timeTrace B') :
    Anscombe.after A B → Anscombe.after A B' :=
  fun ⟨t, ht, t', ht', hlt⟩ => ⟨t, ht, t', h ht', hlt⟩

/-- With a never-instantiated `B`, *A before B* is vacuously true of any instantiated `A`, the
overgeneration of (32)–(33), so *David ate ketchup before he won all the gold medals* comes out true
if he never won. -/
theorem anscombe_before_of_empty (hB : timeTrace B = ∅) (hA : (timeTrace A).Nonempty) :
    Anscombe.beforeEver A B :=
  let ⟨t, ht⟩ := hA
  ⟨t, ht, fun t' ht' => absurd (hB ▸ ht') (Set.notMem_empty t')⟩

end Classical

end BeaverCondoravdi2003
