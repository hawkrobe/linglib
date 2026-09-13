import Linglib.Semantics.Modality.Kratzer.Ordering

/-!
# Rudin (2025): Asserting epistemic modals

This file formalizes the paper's Neo-Stalnakerian formalization of assertion. A speaker who
asserts a sentence presents her epistemic state as one in which the sentence is known: the
meta-intensionalization of a sentence is the set of states at all of whose worlds it is true
relative to that very state (`MI`), an assertion proposes that the context be refined into
that set in the most conservative way, and a hearer may reject it when no nonempty refinement
of her own state lies in it (`Compatible`). For a sentence whose truth does not depend on the
state the set is the downward closure of its proposition, so the update is [stalnaker-1978]'s
intersection, the largest refinement in the set. For *might* under the simple quantificational
semantics the set is the states that contain a prejacent world, so the update is
[veltman-1996]'s consistency test, and rejection turns on the rejector's information while
truth turns on the assertor's: the dissociation of truth from acceptance that [khoo-2015]
observed (`dissociation`). Under the ordering semantics of [kratzer-1981] a state carries an
ordering source, and asserting *might* adds the prejacent to it, a commensurate update whenever
the base has a prejacent world (`mightOrdUpdate_commensurate`). The appendices' *must* and
relational semantics are also formalized.

## Implementation notes

Epistemic states are sets of worlds, and the ordering version pairs a base with the
substrate's ordering source, its best worlds the substrate's best worlds. Commensurativity is
stated as the paper states it, membership of the update in the meta-intensionalized set on
every compatible context; conservativity, quantified over sentences, is rendered for the
simple version by the update being the largest refinement in the set. The commensurativity of
the ordering update for *might* uses a finite frame, the paper's limit assumption. The ordering
update for *must* adds the prejacent and drops the propositions disjoint from it; the paper
argues on two three-world scenarios that both steps are needed, and both are formalized.

## TODO

* The paper claims that after the *must* update every best world is a prejacent world, since
  an ordering proposition overlapping the prejacent favors its prejacent worlds. Two
  overlapping propositions can jointly leave a non-prejacent world best
  (`overlapping_not_sufficient`), so the *must* update is not commensurate in general.

## References

* [rudin-2025a]
* [stalnaker-1978]
* [veltman-1996]
* [kratzer-1981]
* [khoo-2015]
* [yalcin-2007]
-/

namespace Rudin2025

open Modality.Kratzer

variable {W : Type*}

/-! ### Meta-intensionalization -/

/-- An information-sensitive denotation: truth at a world relative to an epistemic state. -/
abbrev Denotation (W : Type*) := Set W → W → Prop

/-- A sentence whose truth does not depend on the state: a proposition. -/
def plain (p : Set W) : Denotation W := λ _ w => w ∈ p

/-- *might* under the simple quantificational semantics: some world of the state is a
prejacent world. -/
def might (p : Set W) : Denotation W := λ i _ => (i ∩ p).Nonempty

/-- *must* under the simple quantificational semantics: every world of the state is a
prejacent world. -/
def must (p : Set W) : Denotation W := λ i _ => i ⊆ p

/-- The meta-intensionalization of a sentence: the states in which the speaker knows it, those
at all of whose worlds it is true relative to the state itself. -/
def MI (s : Denotation W) : Set (Set W) := {i | ∀ w ∈ i, s i w}

/-- A context is compatible with a sentence when some nonempty refinement, a subset, lies in
the sentence's meta-intensionalization. -/
def Compatible (s : Denotation W) (c : Set W) : Prop := ∃ c' ⊆ c, c'.Nonempty ∧ c' ∈ MI s

/-- Rejection of an assertion is licensed when the rejector's state is not compatible with
the sentence. -/
def RejectionLicensed (s : Denotation W) (i : Set W) : Prop := ¬ Compatible s i

/-- An update is commensurate with a sentence when it takes every compatible context into
the sentence's meta-intensionalization. -/
def Commensurate (s : Denotation W) (f : Set W → Set W) : Prop :=
  ∀ c, Compatible s c → f c ∈ MI s

/-- The meta-intensionalization of a proposition is its downward closure. -/
theorem MI_plain (p : Set W) : MI (plain p) = {i | i ⊆ p} := by
  ext i; simp [MI, plain, Set.subset_def]

/-- A nonempty state is in the meta-intensionalization of *might* exactly when it contains a
prejacent world: the outer quantifier is vacuous. -/
theorem mem_MI_might {p i : Set W} (hi : i.Nonempty) : i ∈ MI (might p) ↔ (i ∩ p).Nonempty :=
  let ⟨w, hw⟩ := hi
  ⟨λ h => h w hw, λ h _ _ => h⟩

/-- The meta-intensionalization of *must* is that of its prejacent. -/
theorem MI_must (p : Set W) : MI (must p) = MI (plain p) := by
  ext i
  exact ⟨λ h w hw => h w hw hw, λ h _ _ v hv => h v hv⟩

/-- A context is compatible with a proposition exactly when it has a world of it. -/
theorem compatible_plain {p c : Set W} : Compatible (plain p) c ↔ (c ∩ p).Nonempty := by
  constructor
  · rintro ⟨c', hc'c, ⟨w, hw⟩, hMI⟩
    exact ⟨w, hc'c hw, hMI w hw⟩
  · rintro ⟨w, hwc, hwp⟩
    exact ⟨{w}, Set.singleton_subset_iff.2 hwc, Set.singleton_nonempty w,
      λ v hv => Set.mem_singleton_iff.1 hv ▸ hwp⟩

/-- A context is compatible with *might* exactly when it has a prejacent world. -/
theorem compatible_might {p c : Set W} : Compatible (might p) c ↔ (c ∩ p).Nonempty := by
  constructor
  · rintro ⟨c', hc'c, hne, hMI⟩
    exact ((mem_MI_might hne).1 hMI).mono (Set.inter_subset_inter_left p hc'c)
  · intro h
    have hc : c.Nonempty := h.mono Set.inter_subset_left
    exact ⟨c, subset_rfl, hc, (mem_MI_might hc).2 h⟩

/-- Rejecting a proposition presents the rejector as knowing it false. -/
theorem rejectionLicensed_plain {p i : Set W} : RejectionLicensed (plain p) i ↔ i ∩ p = ∅ := by
  rw [RejectionLicensed, compatible_plain, Set.not_nonempty_iff_eq_empty]

/-- The Stalnakerian biconditional between truth and acceptance: a proposition may be
rejected exactly when its negation is known. -/
theorem rejectionLicensed_plain_iff {p i : Set W} :
    RejectionLicensed (plain p) i ↔ i ∈ MI (plain pᶜ) := by
  rw [rejectionLicensed_plain, MI_plain, Set.mem_ofPred_eq, Set.subset_compl_iff_disjoint_right,
    Set.disjoint_iff_inter_eq_empty]

/-- Rejecting *might* presents the rejector as having no prejacent world, whatever the
assertor's state. -/
theorem rejectionLicensed_might {p i : Set W} : RejectionLicensed (might p) i ↔ i ∩ p = ∅ := by
  rw [RejectionLicensed, compatible_might, Set.not_nonempty_iff_eq_empty]

/-! ### Update potentials -/

/-- Stalnakerian update: intersection with the proposition. -/
def plainUpdate (p c : Set W) : Set W := c ∩ p

theorem plainUpdate_commensurate (p : Set W) : Commensurate (plain p) (plainUpdate p) :=
  λ _ _ _ h => h.2

/-- Intersection is the most conservative commensurate update: every refinement of the
context in the meta-intensionalization lies inside it. -/
theorem plainUpdate_greatest {p c c' : Set W} (hc' : c' ⊆ c) (h : c' ∈ MI (plain p)) :
    c' ⊆ plainUpdate p c :=
  λ w hw => ⟨hc' hw, h w hw⟩

/-- The update of *might*: the context itself when it has a prejacent world, and the absurd
context otherwise. -/
def mightUpdate (p c : Set W) : Set W := {w ∈ c | (c ∩ p).Nonempty}

/-- The consistency test: a context with a prejacent world is left as it is. -/
theorem mightUpdate_of_nonempty {p c : Set W} (h : (c ∩ p).Nonempty) : mightUpdate p c = c := by
  ext w; simp [mightUpdate, h]

/-- The consistency test: a context without a prejacent world is anomalous. -/
theorem mightUpdate_of_empty {p c : Set W} (h : c ∩ p = ∅) : mightUpdate p c = ∅ := by
  ext w; simp [mightUpdate, h]

theorem mightUpdate_commensurate (p : Set W) : Commensurate (might p) (mightUpdate p) := by
  intro c hc
  have h := compatible_might.1 hc
  rw [mightUpdate_of_nonempty h]
  exact (mem_MI_might (h.mono Set.inter_subset_left)).2 h

/-- The test is the most conservative commensurate update: every nonempty refinement of the
context in the meta-intensionalization lies inside it. -/
theorem mightUpdate_greatest {p c c' : Set W} (hc' : c' ⊆ c) (hne : c'.Nonempty)
    (h : c' ∈ MI (might p)) : c' ⊆ mightUpdate p c :=
  λ _ hw => ⟨hc' hw, ((mem_MI_might hne).1 h).mono (Set.inter_subset_inter_left p hc')⟩

/-- *must* updates as its prejacent does. -/
theorem must_updates_as_plain (p : Set W) : Commensurate (must p) (plainUpdate p) := by
  intro c _
  rw [MI_must]
  exact λ _ h => h.2

/-- Truth and acceptance come apart for *might*: the assertor, with a prejacent world, knows
the claim, while the rejector, with none, is licensed to reject it. -/
theorem dissociation {p a r : Set W} (ha : (a ∩ p).Nonempty) (hr : r ∩ p = ∅) :
    a ∈ MI (might p) ∧ RejectionLicensed (might p) r :=
  ⟨λ _ _ => ha, rejectionLicensed_might.2 hr⟩

/-! ### The ordering semantics -/

/-- An epistemic state of the ordering version: a modal base and an ordering source. -/
structure OrdState (W : Type*) where
  base : Set W
  ordering : List (W → Prop)

/-- The best worlds of a state: the worlds of the base no other world of the base betters
under the ordering source. -/
def OrdState.best (i : OrdState W) : Set W := bestAmong i.base i.ordering

/-- A denotation relative to a state with an ordering source. -/
abbrev OrdDenotation (W : Type*) := OrdState W → W → Prop

/-- A proposition. -/
def plainOrd (p : Set W) : OrdDenotation W := λ _ w => w ∈ p

/-- *might* under the ordering semantics: some best world is a prejacent world. -/
def mightOrd (p : Set W) : OrdDenotation W := λ i _ => (i.best ∩ p).Nonempty

/-- *must* under the ordering semantics: every best world is a prejacent world. -/
def mustOrd (p : Set W) : OrdDenotation W := λ i _ => i.best ⊆ p

/-- Meta-intensionalization over the base of a state. -/
def MIOrd (s : OrdDenotation W) : Set (OrdState W) := {i | ∀ w ∈ i.base, s i w}

/-- A refinement shrinks the base; the ordering source may change freely. -/
def OrdState.Refines (i' i : OrdState W) : Prop := i'.base ⊆ i.base

/-- Compatibility, with a nonempty base in place of a nonempty state. -/
def CompatibleOrd (s : OrdDenotation W) (c : OrdState W) : Prop :=
  ∃ c', c'.Refines c ∧ c'.base.Nonempty ∧ c' ∈ MIOrd s

/-- A proposition still updates by intersection, the ordering source untouched. -/
def plainOrdUpdate (p : Set W) (c : OrdState W) : OrdState W := ⟨c.base ∩ p, c.ordering⟩

theorem plainOrdUpdate_mem_MIOrd (p : Set W) (c : OrdState W) :
    plainOrdUpdate p c ∈ MIOrd (plainOrd p) :=
  λ _ h => h.2

open scoped Classical in
/-- The update of *might*: the prejacent joins the ordering source when the base has a
prejacent world; otherwise the base is emptied. -/
noncomputable def mightOrdUpdate (p : Set W) (c : OrdState W) : OrdState W :=
  if (c.base ∩ p).Nonempty then ⟨c.base, (· ∈ p) :: c.ordering⟩ else ⟨∅, c.ordering⟩

theorem mightOrdUpdate_of_compatible {p : Set W} {c : OrdState W} (h : (c.base ∩ p).Nonempty) :
    mightOrdUpdate p c = ⟨c.base, (· ∈ p) :: c.ordering⟩ := by
  rw [mightOrdUpdate, if_pos h]

/-- Adding the prejacent to the ordering source is commensurate: with the prejacent among the
ordering propositions, only a prejacent world can better a prejacent world, so a prejacent
world best among the prejacent worlds of the base is best in the base. -/
theorem mightOrdUpdate_commensurate [Finite W] {p : Set W} {c : OrdState W}
    (h : (c.base ∩ p).Nonempty) : mightOrdUpdate p c ∈ MIOrd (mightOrd p) := by
  rw [mightOrdUpdate_of_compatible h]
  intro _ _
  obtain ⟨m, hm⟩ := exists_mem_bestAmong (worlds := c.base ∩ p) (A := (· ∈ p) :: c.ordering) h
  refine ⟨m, ?_, (bestAmong_subset _ _ hm).2⟩
  rw [mem_bestAmong] at hm
  show m ∈ bestAmong c.base ((· ∈ p) :: c.ordering)
  rw [mem_bestAmong]
  refine ⟨hm.1.1, λ v hv hvm => ?_⟩
  by_cases hvp : v ∈ p
  · exact hm.2 v ⟨hv, hvp⟩ hvm
  · exact absurd (hvm (· ∈ p) (List.mem_cons.2 (Or.inl rfl)) hm.1.2) hvp

/-- Compatibility with *might* under the ordering semantics is again having a prejacent world
in the base: the refinement whose ordering source is the prejacent alone makes the prejacent
worlds best. -/
theorem compatibleOrd_might {p : Set W} {c : OrdState W} :
    CompatibleOrd (mightOrd p) c ↔ (c.base ∩ p).Nonempty := by
  constructor
  · rintro ⟨c', hc'c, ⟨v, hv⟩, hMI⟩
    obtain ⟨m, hmb, hmp⟩ := hMI v hv
    exact ⟨m, hc'c (bestAmong_subset _ _ hmb), hmp⟩
  · rintro ⟨w, hwb, hwp⟩
    refine ⟨⟨c.base, [(· ∈ p)]⟩, subset_rfl, ⟨w, hwb⟩, λ _ _ => ⟨w, ?_, hwp⟩⟩
    show w ∈ bestAmong c.base [(· ∈ p)]
    rw [bestAmong_eq_of_exists ⟨w, hwb, by simpa using hwp⟩]
    exact ⟨hwb, by simpa using hwp⟩

/-- Rejection of *might* is licensed, as before, by the rejector's lack of a prejacent
world. -/
theorem rejectionOrd_might {p : Set W} {i : OrdState W} :
    ¬ CompatibleOrd (mightOrd p) i ↔ i.base ∩ p = ∅ := by
  rw [compatibleOrd_might, Set.not_nonempty_iff_eq_empty]

/-! ### *must* under the ordering semantics -/

open scoped Classical in
/-- The update of *must*: the prejacent joins the ordering source and the propositions
disjoint from it leave, when the base has a prejacent world. -/
noncomputable def mustOrdUpdate (p : Set W) (c : OrdState W) : OrdState W :=
  if (c.base ∩ p).Nonempty then
    ⟨c.base, (· ∈ p) :: c.ordering.filter λ q => ∃ w ∈ p, q w⟩
  else ⟨∅, c.ordering⟩

/-- With the prejacent as the whole ordering source, the best worlds are the prejacent worlds
of the base. -/
theorem mustOrd_singleton {p : Set W} {c : OrdState W} (h : (c.base ∩ p).Nonempty) :
    (⟨c.base, [(· ∈ p)]⟩ : OrdState W) ∈ MIOrd (mustOrd p) := by
  obtain ⟨w, hwb, hwp⟩ := h
  intro _ _ v hv
  change v ∈ bestAmong c.base [(· ∈ p)] at hv
  rw [bestAmong_eq_of_exists ⟨w, hwb, by simpa using hwp⟩] at hv
  simpa using hv.2

/-- Compatibility with *must* under the ordering semantics is having a prejacent world in
the base, given a best world in every nonempty base. -/
theorem compatibleOrd_must [Finite W] {p : Set W} {c : OrdState W} :
    CompatibleOrd (mustOrd p) c ↔ (c.base ∩ p).Nonempty := by
  constructor
  · rintro ⟨c', hc'c, ⟨v, hv⟩, hMI⟩
    obtain ⟨m, hm⟩ := exists_mem_bestAmong (worlds := c'.base) (A := c'.ordering) ⟨v, hv⟩
    exact ⟨m, hc'c (bestAmong_subset _ _ hm), hMI v hv hm⟩
  · intro h
    exact ⟨⟨c.base, [(· ∈ p)]⟩, subset_rfl, h.mono Set.inter_subset_left, mustOrd_singleton h⟩

/-- Decide a claim about a three-world state by unfolding the operators. -/
scoped macro "decide_states" : tactic =>
  `(tactic| (simp only [MIOrd, mustOrd, OrdState.best, bestAmong, Core.Order.Normality.mem_optimal,
      kratzerPreorder, Core.Order.Normality.fromProps, Preorder.ofCriteria_le_iff,
      Set.mem_ofPred_eq, Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, Set.subset_def,
      Set.mem_inter_iff, Set.Nonempty, List.forall_mem_cons, List.mem_nil_iff, false_implies,
      implies_true, true_and, and_true, forall_const]; decide))

/-- The paper's first scenario: with an empty ordering source every world of the base is
best, so a context with a prejacent world is compatible with *must* yet not in its
meta-intensionalization until the prejacent is added. -/
theorem must_needs_prejacent :
    (⟨Set.univ, []⟩ : OrdState (Fin 3)) ∉ MIOrd (mustOrd {0, 1}) ∧
      (⟨Set.univ, [(· ∈ ({0, 1} : Set (Fin 3)))]⟩ : OrdState (Fin 3)) ∈ MIOrd (mustOrd {0, 1}) := by
  decide_states

/-- The paper's second scenario: a proposition disjoint from the prejacent keeps a
non-prejacent world best even after the prejacent is added, so it has to be removed. -/
theorem must_needs_removal :
    (⟨Set.univ, [(· ∈ ({0, 1} : Set (Fin 3))), (· ∈ ({2} : Set (Fin 3)))]⟩ : OrdState (Fin 3)) ∉
      MIOrd (mustOrd {0, 1}) := by
  decide_states

/-- On the second scenario the *must* update removes the disjoint proposition and lands in
the meta-intensionalization. -/
theorem mustOrdUpdate_removal :
    mustOrdUpdate ({0, 1} : Set (Fin 3)) ⟨Set.univ, [(· ∈ ({2} : Set (Fin 3)))]⟩ ∈
      MIOrd (mustOrd {0, 1}) := by
  rw [mustOrdUpdate, if_pos ⟨0, Set.mem_univ _, by simp⟩, List.filter_cons_of_neg, List.filter_nil]
  · exact must_needs_prejacent.2
  · simp only [decide_eq_true_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    decide

/-- Removing the disjoint propositions does not suffice: two propositions each overlapping
the prejacent can jointly keep a non-prejacent world best. -/
theorem overlapping_not_sufficient :
    ∃ o : List (Fin 3 → Prop), (∀ q ∈ o, ∃ w ∈ ({0, 1} : Set (Fin 3)), q w) ∧
      (⟨Set.univ, (· ∈ ({0, 1} : Set (Fin 3))) :: o⟩ : OrdState (Fin 3)) ∉ MIOrd (mustOrd {0, 1}) :=
  ⟨[(· ∈ ({1, 2} : Set (Fin 3))), (· ∈ ({0, 2} : Set (Fin 3)))], by decide_states, by decide_states⟩

/-! ### The relational semantics -/

/-- *might* on an accessibility function. -/
def mightRel (f : W → Set W) (p : Set W) (w : W) : Prop := (f w ∩ p).Nonempty

/-- Epistemic closure: from every world of the state the whole state is accessible. -/
def Closed (f : W → Set W) (i : Set W) : Prop := ∀ w ∈ i, f w = i

/-- Under closure the relational *might* is known in a nonempty state exactly when the state
has a prejacent world, as on the domain semantics. -/
theorem relational_might {f : W → Set W} {p i : Set W} (hf : Closed f i) (hi : i.Nonempty) :
    (∀ w ∈ i, mightRel f p w) ↔ (i ∩ p).Nonempty := by
  obtain ⟨v, hv⟩ := hi
  exact ⟨λ h => hf v hv ▸ h v hv, λ h w hw => by rw [mightRel, hf w hw]; exact h⟩

/-- Under closure the relational *must* is known exactly when the state lies in the
prejacent. -/
theorem relational_must {f : W → Set W} {p i : Set W} (hf : Closed f i) :
    (∀ w ∈ i, f w ⊆ p) ↔ i ⊆ p :=
  ⟨λ h w hw => h w hw (hf w hw ▸ hw), λ h w hw => (hf w hw).symm ▸ h⟩

/-- Under closure of the accessibility and ordering functions, the relational ordering
*might* is known exactly when the domain version is. -/
theorem relational_ordering {f : W → Set W} {g : W → List (W → Prop)} {p : Set W}
    {i : OrdState W} (hf : Closed f i.base) (hg : ∀ w ∈ i.base, g w = i.ordering)
    (hi : i.base.Nonempty) :
    (∀ w ∈ i.base, (bestAmong (f w) (g w) ∩ p).Nonempty) ↔ i ∈ MIOrd (mightOrd p) := by
  obtain ⟨v, hv⟩ := hi
  constructor
  · intro h _ _
    have := h v hv
    rwa [hf v hv, hg v hv] at this
  · intro h w hw
    rw [hf w hw, hg w hw]
    exact h v hv

end Rudin2025
