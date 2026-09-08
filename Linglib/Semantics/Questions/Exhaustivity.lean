import Mathlib.Data.Finset.Basic
import Linglib.Semantics.Questions.Basic
import Linglib.Semantics.Questions.Resolution

/-!
# Answerhood operators on Hamblin sets

A Hamblin set `H : Set (Set W)` is a set of propositions. The theories that
take a question to denote such a set locate "the answer at world `w`" by an
operator on the members of `H` true at `w`:

- `trueAnswers H w`, the [karttunen-1977] set of true members;
- `weakAnswer H w`, their intersection, the weakly exhaustive answer of
  [heim-1994] (Ans₁) and [beck-rullmann-1999];
- `strongAnswer H w`, the worlds deciding every member as `w` does, the
  strongly exhaustive answer of [groenendijk-stokhof-1984] and Heim's Ans₂;
- `IsStrongestTrueAnswer H w p`, [dayal-1996]'s maximally informative true
  member: the least true member under entailment, `IsLeast`. Its existence is
  Dayal's existential presupposition `IsExhaustivelyResolvable`; `dayalAns`
  returns it and `dayalStrongAns` applies Heim's strengthening to it;
- `IsExhaustivelyResolvableOn H s`, the presupposition on an information
  state: a least member the state supports, Dayal's at the singleton `{w}`;
- `box H R`, the question under necessity, whose presupposition at a world is
  the prejacent's on that world's modal base (`isExhaustivelyResolvable_box_iff`);
- `exhCell H p` and `exhaustifiedPartition H`, [fox-2018]'s cells;
- `relExh H w M`, [xiang-2022]'s exhaustivity relative to a modal base;
- `ofFinset F`, a finite family of finite propositions, on which the
  presuppositions are decidable.

The presupposition holds exactly when the weak answer is itself a member
(`isExhaustivelyResolvable_iff`), so Dayal's operator agrees with Heim's and
Beck and Rullmann's wherever it is defined, and its strong form agrees with
the Groenendijk–Stokhof answer (`dayalStrongAns_eq_some_iff`). An inquisitive
question `Q : Question W` enters through its alternatives `alt Q`, an
antichain, over which the least true member is the only true member
(`isStrongestTrueAnswer_iff_of_antichain`): the number-sensitive answerhood
of [dayal-2016] needs Hamblin sets whose members entail one another, which
`alt` discards.

## References

* [karttunen-1977]
* [groenendijk-stokhof-1984]
* [heim-1994]
* [dayal-1996]
* [beck-rullmann-1999]
* [dayal-2016]
* [fox-2018]
* [xiang-2022]
-/

namespace Questions

open Question

variable {W : Type*} (H : Set (Set W)) (w : W)

/-! ### Karttunen sets and the weak and strong answers -/

/-- The [karttunen-1977] denotation: the members of `H` true at `w`. -/
def trueAnswers : Set (Set W) := {p ∈ H | w ∈ p}

@[simp] theorem mem_trueAnswers {p : Set W} :
    p ∈ trueAnswers H w ↔ p ∈ H ∧ w ∈ p := Iff.rfl

theorem trueAnswers_subset : trueAnswers H w ⊆ H := fun _ h => h.1

/-- The weakly exhaustive answer ([heim-1994]'s Ans₁, [beck-rullmann-1999]'s
Ans-BR): the intersection of the true members. -/
def weakAnswer : Set W := ⋂₀ trueAnswers H w

@[simp] theorem mem_weakAnswer {v : W} :
    v ∈ weakAnswer H w ↔ ∀ p ∈ H, w ∈ p → v ∈ p := by
  simp [weakAnswer, and_imp]

theorem self_mem_weakAnswer : w ∈ weakAnswer H w := by simp

theorem weakAnswer_subset {p : Set W} (hp : p ∈ H) (hw : w ∈ p) :
    weakAnswer H w ⊆ p :=
  Set.sInter_subset_of_mem ⟨hp, hw⟩

/-- The strongly exhaustive answer ([groenendijk-stokhof-1984]; [heim-1994]'s
Ans₂ form): the worlds that decide every member of `H` as `w` does. -/
def strongAnswer : Set W := {v | ∀ p ∈ H, (w ∈ p ↔ v ∈ p)}

@[simp] theorem mem_strongAnswer {v : W} :
    v ∈ strongAnswer H w ↔ ∀ p ∈ H, (w ∈ p ↔ v ∈ p) := Iff.rfl

/-- Heim's form of the strong answer: the worlds with the same Karttunen set. -/
theorem strongAnswer_eq_preimage :
    strongAnswer H w = trueAnswers H ⁻¹' {trueAnswers H w} := by
  ext v
  simp only [mem_strongAnswer, Set.mem_preimage, Set.mem_singleton_iff, Set.ext_iff,
    mem_trueAnswers]
  constructor
  · exact fun h p => and_congr_right fun hp => (h p hp).symm
  · exact fun h p hp =>
      ⟨fun hw => ((h p).2 ⟨hp, hw⟩).2, fun hv => ((h p).1 ⟨hp, hv⟩).2⟩

theorem strongAnswer_subset_weakAnswer : strongAnswer H w ⊆ weakAnswer H w :=
  fun _ hv => (mem_weakAnswer H w).2 fun p hp hwp => (hv p hp).1 hwp

@[simp] theorem self_mem_strongAnswer : w ∈ strongAnswer H w := fun _ _ => Iff.rfl

theorem mem_strongAnswer_comm {w v : W} :
    v ∈ strongAnswer H w ↔ w ∈ strongAnswer H v :=
  ⟨fun h p hp => (h p hp).symm, fun h p hp => (h p hp).symm⟩

theorem mem_strongAnswer_trans {w v u : W} (huv : u ∈ strongAnswer H v)
    (hvw : v ∈ strongAnswer H w) : u ∈ strongAnswer H w :=
  fun p hp => (hvw p hp).trans (huv p hp)

/-- Two strong answers are equal or disjoint: they are the cells of a partition. -/
theorem strongAnswer_eq_or_disjoint (w v : W) :
    strongAnswer H w = strongAnswer H v ∨ Disjoint (strongAnswer H w) (strongAnswer H v) := by
  by_cases h : ∃ u, u ∈ strongAnswer H w ∧ u ∈ strongAnswer H v
  · obtain ⟨u, huw, huv⟩ := h
    refine Or.inl (Set.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
    · exact mem_strongAnswer_trans H
        (mem_strongAnswer_trans H hx ((mem_strongAnswer_comm H).1 huw)) huv
    · exact mem_strongAnswer_trans H
        (mem_strongAnswer_trans H hx ((mem_strongAnswer_comm H).1 huv)) huw
  · exact Or.inr (Set.disjoint_left.2 fun u huw huv => h ⟨u, huw, huv⟩)

@[simp] theorem iUnion_strongAnswer : ⋃ w, strongAnswer H w = Set.univ :=
  Set.eq_univ_of_forall fun v => Set.mem_iUnion.2 ⟨v, self_mem_strongAnswer H v⟩

theorem mem_range_strongAnswer_iff {C : Set W} :
    C ∈ Set.range (strongAnswer H) ↔ ∃ w ∈ C, C = strongAnswer H w :=
  ⟨fun ⟨w, hw⟩ => ⟨w, hw ▸ self_mem_strongAnswer H w, hw.symm⟩,
   fun ⟨w, _, hw⟩ => ⟨w, hw.symm⟩⟩

/-- The strongly exhaustive answer to an inquisitive question mention-all answers it. -/
theorem mentionAll_strongAnswer (Q : Question W) : MentionAll (strongAnswer (alt Q) w) Q := by
  intro p hp
  by_cases hw : w ∈ p
  · exact Or.inl fun _ hv => (hv p hp).1 hw
  · exact Or.inr fun _ hv => (hv p hp).not.1 hw

/-! ### Dayal's strongest true answer -/

/-- [dayal-1996]'s maximally informative true member: `p` is in `H`, true at
`w`, and entails every member true at `w`, the least element of the Karttunen
set under `⊆`. -/
abbrev IsStrongestTrueAnswer (p : Set W) : Prop := IsLeast (trueAnswers H w) p

/-- Dayal's existential presupposition: a strongest true member exists. -/
def IsExhaustivelyResolvable : Prop := ∃ p, IsStrongestTrueAnswer H w p

theorem isStrongestTrueAnswer_iff {p : Set W} :
    IsStrongestTrueAnswer H w p ↔ p ∈ H ∧ p = weakAnswer H w := by
  constructor
  · intro h
    exact ⟨h.1.1,
      (Set.subset_sInter fun _ hq => h.2 hq).antisymm (Set.sInter_subset_of_mem h.1)⟩
  · rintro ⟨hp, rfl⟩
    exact ⟨⟨hp, self_mem_weakAnswer H w⟩, fun _ hq => Set.sInter_subset_of_mem hq⟩

/-- The presupposition holds exactly when the weak answer is itself a member. -/
theorem isExhaustivelyResolvable_iff : IsExhaustivelyResolvable H w ↔ weakAnswer H w ∈ H :=
  ⟨fun ⟨_, h⟩ =>
    have h' := (isStrongestTrueAnswer_iff H w).1 h
    h'.2 ▸ h'.1,
   fun h => ⟨_, (isStrongestTrueAnswer_iff H w).2 ⟨h, rfl⟩⟩⟩

theorem IsExhaustivelyResolvable.exists_mem {H : Set (Set W)} {w : W}
    (h : IsExhaustivelyResolvable H w) : ∃ p ∈ H, w ∈ p :=
  let ⟨p, hp⟩ := h; ⟨p, hp.1.1, hp.1.2⟩

theorem isLeast_singleton (p : Set W) : IsLeast {p} p :=
  ⟨Set.mem_singleton p, fun _ hq => le_of_eq (Set.mem_singleton_iff.1 hq).symm⟩

/-- Over an antichain the least true member is the only true member. -/
theorem isStrongestTrueAnswer_iff_of_antichain (hH : IsAntichain (· ⊆ ·) H) {p : Set W} :
    IsStrongestTrueAnswer H w p ↔ trueAnswers H w = {p} := by
  constructor
  · intro h
    refine Set.eq_singleton_iff_unique_mem.2 ⟨h.1, fun q hq => ?_⟩
    by_contra hne
    exact hH h.1.1 hq.1 (Ne.symm hne) (h.2 hq)
  · intro h
    rw [IsStrongestTrueAnswer, h]
    exact isLeast_singleton p

theorem isExhaustivelyResolvable_iff_of_antichain (hH : IsAntichain (· ⊆ ·) H) :
    IsExhaustivelyResolvable H w ↔ ∃ p, trueAnswers H w = {p} :=
  exists_congr fun _ => isStrongestTrueAnswer_iff_of_antichain H w hH

/-- Over inquisitive alternatives the strongest true answer is the only true alternative. -/
theorem isStrongestTrueAnswer_alt_iff (Q : Question W) {p : Set W} :
    IsStrongestTrueAnswer (alt Q) w p ↔ trueAnswers (alt Q) w = {p} :=
  isStrongestTrueAnswer_iff_of_antichain _ w (alt_isAntichain Q)

open Classical in
/-- Dayal's answerhood operator Ans-D: the strongest true member, when the
presupposition holds. -/
noncomputable def dayalAns : Option (Set W) :=
  if weakAnswer H w ∈ H then some (weakAnswer H w) else none

theorem dayalAns_eq_some_iff {p : Set W} :
    dayalAns H w = some p ↔ IsStrongestTrueAnswer H w p := by
  rw [isStrongestTrueAnswer_iff, dayalAns]
  split_ifs with h
  · constructor
    · intro e
      rw [Option.some.injEq] at e
      exact ⟨e ▸ h, e.symm⟩
    · rintro ⟨_, e⟩
      rw [e]
  · exact ⟨fun e => (by simp at e), fun ⟨hp, e⟩ => (h (e ▸ hp)).elim⟩

theorem dayalAns_isSome_iff : (dayalAns H w).isSome ↔ IsExhaustivelyResolvable H w := by
  rw [isExhaustivelyResolvable_iff, dayalAns]
  split_ifs with h <;> simp [h]

theorem dayalAns_eq_none_iff : dayalAns H w = none ↔ ¬ IsExhaustivelyResolvable H w := by
  rw [isExhaustivelyResolvable_iff, dayalAns]
  split_ifs with h <;> simp [h]

/-! ### Resolvability on an information state -/

/-- The members of `H` an information state `s` supports. -/
def supported (s : Set W) : Set (Set W) := {p ∈ H | s ⊆ p}

@[simp] theorem mem_supported {s p : Set W} : p ∈ supported H s ↔ p ∈ H ∧ s ⊆ p := Iff.rfl

@[simp] theorem supported_singleton : supported H {w} = trueAnswers H w := by
  ext p
  simp [supported, trueAnswers]

/-- Dayal's presupposition on an information state: a least supported member. On the
singleton state `{w}` it is the presupposition at `w`. -/
def IsExhaustivelyResolvableOn (s : Set W) : Prop := ∃ p, IsLeast (supported H s) p

theorem isExhaustivelyResolvableOn_singleton :
    IsExhaustivelyResolvableOn H {w} ↔ IsExhaustivelyResolvable H w := by
  rw [IsExhaustivelyResolvableOn, supported_singleton]
  rfl

/-! ### Questions under necessity -/

/-- The question `□Q` over the accessibility `R`: every member necessitated, holding at `x`
when it holds at every world accessible from `x`. -/
def box {W' : Type*} (R : W' → W → Prop) : Set (Set W') :=
  (fun p => {x | ∀ v, R x v → v ∈ p}) '' H

theorem mem_box {W' : Type*} {R : W' → W → Prop} {q : Set W'} :
    q ∈ box H R ↔ ∃ p ∈ H, {x | ∀ v, R x v → v ∈ p} = q := Iff.rfl

/-- Necessity lifts the presupposition: `□Q` is resolvable at `x` iff `Q` is resolvable on the
worlds accessible from `x`, provided every world is the sole world accessible from some `x`. -/
theorem isExhaustivelyResolvable_box_iff {W' : Type*} {R : W' → W → Prop}
    (hR : ∀ v, ∃ x, ∀ u, R x u ↔ u = v) {x : W'} {s : Set W} (hs : ∀ v, R x v ↔ v ∈ s) :
    IsExhaustivelyResolvable (box H R) x ↔ IsExhaustivelyResolvableOn H s := by
  have mem : ∀ p, x ∈ {y | ∀ v, R y v → v ∈ p} ↔ s ⊆ p := fun p =>
    ⟨fun h v hv => h v ((hs v).2 hv), fun h v hv => h ((hs v).1 hv)⟩
  have mono : ∀ p q : Set W, p ⊆ q →
      {y | ∀ v, R y v → v ∈ p} ⊆ {y | ∀ v, R y v → v ∈ q} :=
    fun _ _ hpq _ h v hv => hpq (h v hv)
  have refl : ∀ p q : Set W,
      {y | ∀ v, R y v → v ∈ p} ⊆ {y | ∀ v, R y v → v ∈ q} → p ⊆ q := by
    intro p q h v hv
    obtain ⟨y, hy⟩ := hR v
    exact h (fun u hu => ((hy u).1 hu) ▸ hv) v ((hy v).2 rfl)
  constructor
  · rintro ⟨q, ⟨⟨p, hp, rfl⟩, hx⟩, hmin⟩
    refine ⟨p, ⟨hp, (mem p).1 hx⟩, fun r ⟨hr, hsr⟩ => refl p r (hmin ⟨⟨r, hr, rfl⟩, (mem r).2 hsr⟩)⟩
  · rintro ⟨p, ⟨hp, hsp⟩, hmin⟩
    refine ⟨_, ⟨⟨p, hp, rfl⟩, (mem p).2 hsp⟩, ?_⟩
    rintro q ⟨⟨r, hr, rfl⟩, hx⟩
    exact mono p r (hmin ⟨hr, (mem r).1 hx⟩)

/-! ### Cells ([fox-2018]) -/

/-- The cell of `p`: the worlds where `p` is the strongest true member. -/
def exhCell (p : Set W) : Set W := {w | IsStrongestTrueAnswer H w p}

@[simp] theorem mem_exhCell {p : Set W} {w : W} :
    w ∈ exhCell H p ↔ IsStrongestTrueAnswer H w p := Iff.rfl

theorem exhCell_subset (p : Set W) : exhCell H p ⊆ p := fun _ h => h.1.2

/-- Where `p` is the strongest true member, the true members are those `p` entails. -/
theorem trueAnswers_eq_of_isStrongestTrueAnswer {p : Set W}
    (h : IsStrongestTrueAnswer H w p) : trueAnswers H w = {q ∈ H | p ⊆ q} :=
  Set.ext fun _ => ⟨fun hq => ⟨hq.1, h.2 hq⟩, fun ⟨hq, hpq⟩ => ⟨hq, hpq h.1.2⟩⟩

/-- The cell of the strongest true member at `w` is the strong answer at `w`. -/
theorem exhCell_eq_strongAnswer {p : Set W} (h : IsStrongestTrueAnswer H w p) :
    exhCell H p = strongAnswer H w := by
  ext v
  rw [mem_exhCell, mem_strongAnswer]
  constructor
  · exact fun hv q hq =>
      ⟨fun hwq => h.2 ⟨hq, hwq⟩ hv.1.2, fun hvq => hv.2 ⟨hq, hvq⟩ h.1.2⟩
  · exact fun hv =>
      ⟨⟨h.1.1, (hv p h.1.1).1 h.1.2⟩, fun _ hq => h.2 ⟨hq.1, (hv _ hq.1).2 hq.2⟩⟩

/-- The logical partition: the cells of the strong answer. -/
def exhaustifiedPartition : Set (Set W) := Set.range (strongAnswer H)

@[simp] theorem mem_exhaustifiedPartition {C : Set W} :
    C ∈ exhaustifiedPartition H ↔ ∃ w, C = strongAnswer H w := by
  simp [exhaustifiedPartition, eq_comm]

theorem exhaustifiedPartition_nonempty {C : Set W} (h : C ∈ exhaustifiedPartition H) :
    C.Nonempty :=
  let ⟨w, hw⟩ := h; ⟨w, hw ▸ self_mem_strongAnswer H w⟩

theorem exhaustifiedPartition_eq_or_disjoint {C₁ C₂ : Set W}
    (h₁ : C₁ ∈ exhaustifiedPartition H) (h₂ : C₂ ∈ exhaustifiedPartition H) :
    C₁ = C₂ ∨ Disjoint C₁ C₂ := by
  obtain ⟨w₁, rfl⟩ := h₁
  obtain ⟨w₂, rfl⟩ := h₂
  exact strongAnswer_eq_or_disjoint H w₁ w₂

@[simp] theorem sUnion_exhaustifiedPartition : ⋃₀ exhaustifiedPartition H = Set.univ := by
  rw [exhaustifiedPartition, Set.sUnion_range]
  exact iUnion_strongAnswer H

/-- Dayal's strong operator Ans-D/H, [heim-1994]'s strengthening of Ans-D:
the worlds with the same strongest true member as `w`. -/
noncomputable def dayalStrongAns : Option (Set W) := (dayalAns H w).map (exhCell H)

/-- Where defined, Dayal's strong operator is the Groenendijk–Stokhof answer. -/
theorem dayalStrongAns_eq_some_iff {A : Set W} :
    dayalStrongAns H w = some A ↔ IsExhaustivelyResolvable H w ∧ A = strongAnswer H w := by
  simp only [dayalStrongAns, Option.map_eq_some_iff, dayalAns_eq_some_iff]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, exhCell_eq_strongAnswer H w hp⟩
  · rintro ⟨⟨p, hp⟩, rfl⟩
    exact ⟨p, hp, exhCell_eq_strongAnswer H w hp⟩

/-! ### Relativized exhaustivity ([xiang-2022]) -/

/-- `p` is the strongest true member relative to the modal base `M`: true at
`w`, compatible with `M`, and entailing every other such member within `M`. -/
def IsStrongestRelTrueAnswer (M : Set W) (p : Set W) : Prop :=
  p ∈ H ∧ w ∈ p ∧ (∃ v ∈ M, v ∈ p) ∧
    ∀ q ∈ H, w ∈ q → (∃ v ∈ M, v ∈ q) → p ∩ M ⊆ q ∩ M

/-- Relativized exhaustivity: a strongest true member relative to `M` exists. -/
def relExh (M : Set W) : Prop := ∃ p, IsStrongestRelTrueAnswer H w M p

/-! ### Finite Hamblin sets

A finite family of finite propositions is the carrier on which the
presupposition is decidable; `ofFinset` places it in the `Set (Set W)` API. -/

section Finite

/-- The Hamblin set of a finite family of finite propositions. -/
def ofFinset (F : Finset (Finset W)) : Set (Set W) := ((↑) : Finset W → Set W) '' ↑F

@[simp] theorem mem_ofFinset {F : Finset (Finset W)} {p : Set W} :
    p ∈ ofFinset F ↔ ∃ q ∈ F, ↑q = p := by
  simp [ofFinset]

theorem isExhaustivelyResolvable_ofFinset_iff (F : Finset (Finset W)) (w : W) :
    IsExhaustivelyResolvable (ofFinset F) w ↔ ∃ p ∈ F, w ∈ p ∧ ∀ q ∈ F, w ∈ q → p ⊆ q := by
  constructor
  · rintro ⟨p, ⟨hp, hw⟩, hmin⟩
    obtain ⟨p', hp', rfl⟩ := mem_ofFinset.1 hp
    exact ⟨p', hp', hw, fun q hq hwq =>
      Finset.coe_subset.1 (hmin ⟨mem_ofFinset.2 ⟨q, hq, rfl⟩, hwq⟩)⟩
  · rintro ⟨p, hp, hw, hmin⟩
    refine ⟨↑p, ⟨mem_ofFinset.2 ⟨p, hp, rfl⟩, hw⟩, ?_⟩
    rintro q ⟨hq, hwq⟩
    obtain ⟨q', hq', rfl⟩ := mem_ofFinset.1 hq
    exact Finset.coe_subset.2 (hmin q' hq' hwq)

instance [DecidableEq W] (F : Finset (Finset W)) (w : W) :
    Decidable (IsExhaustivelyResolvable (ofFinset F) w) :=
  decidable_of_iff _ (isExhaustivelyResolvable_ofFinset_iff F w).symm

theorem isExhaustivelyResolvableOn_ofFinset_iff (F : Finset (Finset W)) (s : Finset W) :
    IsExhaustivelyResolvableOn (ofFinset F) ↑s ↔
      ∃ p ∈ F, s ⊆ p ∧ ∀ q ∈ F, s ⊆ q → p ⊆ q := by
  constructor
  · rintro ⟨p, ⟨hp, hs⟩, hmin⟩
    obtain ⟨p', hp', rfl⟩ := mem_ofFinset.1 hp
    exact ⟨p', hp', Finset.coe_subset.1 hs, fun q hq hsq =>
      Finset.coe_subset.1 (hmin ⟨mem_ofFinset.2 ⟨q, hq, rfl⟩, Finset.coe_subset.2 hsq⟩)⟩
  · rintro ⟨p, hp, hs, hmin⟩
    refine ⟨↑p, ⟨mem_ofFinset.2 ⟨p, hp, rfl⟩, Finset.coe_subset.2 hs⟩, ?_⟩
    rintro q ⟨hq, hsq⟩
    obtain ⟨q', hq', rfl⟩ := mem_ofFinset.1 hq
    exact Finset.coe_subset.2 (hmin q' hq' (Finset.coe_subset.1 hsq))

instance [DecidableEq W] (F : Finset (Finset W)) (s : Finset W) :
    Decidable (IsExhaustivelyResolvableOn (ofFinset F) ↑s) :=
  decidable_of_iff _ (isExhaustivelyResolvableOn_ofFinset_iff F s).symm

end Finite

/-! ### Polar and declarative questions -/

section Polar

variable {w} {p : Set W} (hne : p ≠ ∅) (hnu : p ≠ Set.univ)
include hne hnu

theorem trueAnswers_polar_of_pos (hwp : w ∈ p) :
    trueAnswers (alt (polar p)) w = {p} := by
  ext q
  constructor
  · rintro ⟨hq, hwq⟩
    rcases (mem_alt_polar_of_nontrivial hne hnu q).1 hq with rfl | rfl
    · exact Set.mem_singleton _
    · exact (hwq hwp).elim
  · intro hq
    obtain rfl := Set.mem_singleton_iff.1 hq
    exact ⟨(mem_alt_polar_of_nontrivial hne hnu _).2 (Or.inl rfl), hwp⟩

theorem trueAnswers_polar_of_neg (hwp : w ∉ p) :
    trueAnswers (alt (polar p)) w = {pᶜ} := by
  ext q
  constructor
  · rintro ⟨hq, hwq⟩
    rcases (mem_alt_polar_of_nontrivial hne hnu q).1 hq with rfl | rfl
    · exact (hwp hwq).elim
    · exact Set.mem_singleton _
  · intro hq
    obtain rfl := Set.mem_singleton_iff.1 hq
    exact ⟨(mem_alt_polar_of_nontrivial hne hnu _).2 (Or.inr rfl), hwp⟩

theorem weakAnswer_polar_of_pos (hwp : w ∈ p) : weakAnswer (alt (polar p)) w = p := by
  rw [weakAnswer, trueAnswers_polar_of_pos hne hnu hwp, Set.sInter_singleton]

theorem weakAnswer_polar_of_neg (hwp : w ∉ p) : weakAnswer (alt (polar p)) w = pᶜ := by
  rw [weakAnswer, trueAnswers_polar_of_neg hne hnu hwp, Set.sInter_singleton]

theorem strongAnswer_polar_of_pos (hwp : w ∈ p) : strongAnswer (alt (polar p)) w = p := by
  ext v
  simp only [mem_strongAnswer, alt_polar_of_nontrivial hne hnu, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, Set.mem_compl_iff]
  exact ⟨fun h => h.1.1 hwp,
    fun hv => ⟨iff_of_true hwp hv, iff_of_false (not_not.2 hwp) (not_not.2 hv)⟩⟩

theorem strongAnswer_polar_of_neg (hwp : w ∉ p) : strongAnswer (alt (polar p)) w = pᶜ := by
  ext v
  simp only [mem_strongAnswer, alt_polar_of_nontrivial hne hnu, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, Set.mem_compl_iff]
  exact ⟨fun h => h.2.1 hwp, fun hv => ⟨iff_of_false hwp hv, iff_of_true hwp hv⟩⟩

theorem isStrongestTrueAnswer_polar_of_pos (hwp : w ∈ p) :
    IsStrongestTrueAnswer (alt (polar p)) w p := by
  rw [IsStrongestTrueAnswer, trueAnswers_polar_of_pos hne hnu hwp]
  exact isLeast_singleton p

theorem isStrongestTrueAnswer_polar_of_neg (hwp : w ∉ p) :
    IsStrongestTrueAnswer (alt (polar p)) w pᶜ := by
  rw [IsStrongestTrueAnswer, trueAnswers_polar_of_neg hne hnu hwp]
  exact isLeast_singleton pᶜ

/-- A non-trivial polar question always satisfies Dayal's presupposition. -/
theorem isExhaustivelyResolvable_polar_of_nontrivial (w : W) :
    IsExhaustivelyResolvable (alt (polar p)) w := by
  by_cases hwp : w ∈ p
  · exact ⟨p, isStrongestTrueAnswer_polar_of_pos hne hnu hwp⟩
  · exact ⟨pᶜ, isStrongestTrueAnswer_polar_of_neg hne hnu hwp⟩

end Polar

theorem weakAnswer_ofSet_of_pos {p : Set W} {w : W} (hwp : w ∈ p) :
    weakAnswer (alt (ofSet p)) w = p := by
  ext v
  simp [weakAnswer, trueAnswers, alt_ofSet, hwp]

theorem strongAnswer_ofSet_of_pos {p : Set W} {w : W} (hwp : w ∈ p) :
    strongAnswer (alt (ofSet p)) w = p := by
  ext v
  simp [strongAnswer, alt_ofSet, hwp]

end Questions
