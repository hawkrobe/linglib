import Linglib.Semantics.Questions.Partition.Basic
import Linglib.Semantics.Presupposition.Defs
import Linglib.Data.Examples.DeoThomas2025

/-!
# Deo and Thomas (2025): Addressing the widest answerable question

This file formalizes [deo-thomas-2025]'s account of English *just* as a domain-widening
strategy. Beyond the complement-exclusion and rank-order uses it shares with *only*, (1) and
(3), *just* has emphatic, precisifying, minimal-sufficiency, unexplanatory, unelaboratory and
counterexpectational uses, (5) to (18), in none of which *only* can replace it and in some of
which its prejacent is not a member of the question it answers on any standard construal,
(19). The account replaces the shared current question of [beaver-clark-2008] and
[coppock-beaver-2014] by an underspecified question, the set of a question's construals at a
context, (31), each a cover of the common ground by alternatives none of which contains
another, (30), after the issues of [ciardelli-groenendijk-roelofsen-2018]. Construals are
compared by width, (32): one is wider than another over the same common ground when no
alternative of the narrower is properly contained in an alternative of the wider and some
alternative of the wider is properly contained in an alternative of the narrower. Width is
weaker than [groenendijk-stokhof-1984]'s question entailment, since construals at different
scale granularities, (22) to (24), are ordered by width but not by entailment, fn. 20 and
Figure 1. A construal is answerable when the speaker has evidence for a true answer to it,
Quality, and takes answering it to be relevant, Relevance, (34), and the optimal construal is
the unique widest answerable one, (35). *Just* presupposes that the current question is the
optimal construal and asserts its prejacent, (36), after which its uses fall into three kinds
of context, (37): the widest construal is answerable; the wider construals fail Quality, the
unexplanatory use of [wiegand-2018], §4.4; or they fail Relevance, the unelaboratory use of
[warstadt-2020], §4.5. The mention-all construal of a constituent question is wider than the
mention-some one, §4.1; a finer partition of the common ground is a wider construal, §4.2 and
§4.7; a finer grain is wider without refining the coarser one, Figure 1; and the construals
of a degree question with an extreme adjective, which differ in where the zone of
indifference of [morzycki-2012] begins, are wider the later it begins, Figure 2 of §4.8.

## Implementation notes

A construal is a `Question`, whose alternatives `Question.alt` are the maximal resolving
states, so (30a) holds by construction and (30b) is `Question.info`. The context of (31)
carries the common ground, the construals, and the speaker's Quality and Relevance verdicts
as primitives, with the paper's requirements that every construal cover the common ground
and that any two construals be comparable by width, which is what makes the optimal construal
unique. Partition construals are `Question.fromSetoid`, so refinement is the order on
`Setoid`. Grains follow the paper's convention that a measure phrase denotes the cell it lies
at the centre of, (24): on a discrete scale the grain of width `ε` has cells of `ε`
consecutive points centred on the multiples of `ε`, and Figure 1's year and half-year grains
are `grain 4` and `grain 2` in quarter years. Worlds for the constituent question of §4.1 are
the extensions of its predicate. The exhaustive interpretation of the prejacent is a mandatory
implicature that the paper leaves to Gricean reasoning, §4.1 and §4.9, and is not formalized;
neither are the interpretation of the prejacent relative to the granularity of the current
question in (36), the minimal-sufficiency construal of §4.3, whose alternatives are fixed by a
causal structure, nor the Focus Principle, (21).

## References

* [deo-thomas-2025]
* [thomas-deo-2020]
* [beaver-clark-2008]
* [coppock-beaver-2014]
* [ciardelli-groenendijk-roelofsen-2018]
* [groenendijk-stokhof-1984]
* [morzycki-2012]
* [wiegand-2018]
* [warstadt-2020]
-/

namespace DeoThomas2025

open Question Presupposition

variable {W : Type*}

/-! ### Width, (32) -/

/-- `P` is wider than `Q`, (32): the two cover the same common ground, no alternative of `Q`
is properly contained in an alternative of `P`, and some alternative of `P` is properly
contained in an alternative of `Q`. -/
def WiderThan (P Q : Question W) : Prop :=
  P.info = Q.info ∧ (∀ q ∈ alt Q, ∀ p ∈ alt P, ¬ q ⊂ p) ∧ ∃ p ∈ alt P, ∃ q ∈ alt Q, p ⊂ q

theorem WiderThan.irrefl (P : Question W) : ¬ WiderThan P P :=
  λ ⟨_, h, p, hp, q, hq, hpq⟩ => h p hp q hq hpq

theorem WiderThan.asymm {P Q : Question W} (h : WiderThan P Q) : ¬ WiderThan Q P :=
  λ ⟨_, h', _⟩ => let ⟨p, hp, q, hq, hpq⟩ := h.2.2; h' p hp q hq hpq

/-- The trivial construal, whose one alternative is the common ground, is narrower than any
other construal of the same common ground: the disjunction of all possible causes of §4.4. -/
theorem widerThan_ofSet {P : Question W} {s p : Set W} (hs : P.info = s) (hp : p ∈ alt P)
    (hne : p ≠ s) : WiderThan P (ofSet s) := by
  have hsub : ∀ q ∈ alt P, q ⊆ s := λ q hq =>
    hs ▸ (Set.subset_sUnion_of_mem hq).trans (sUnion_alt_subset_info P)
  refine ⟨by rw [hs, info_ofSet], ?_, p, hp, s, self_mem_alt_ofSet s,
    Set.ssubset_iff_subset_ne.2 ⟨hsub p hp, hne⟩⟩
  rw [alt_ofSet]
  rintro _ rfl q hq hlt
  exact hlt.2 (hsub q hq)

/-! ### The context, (31), and the optimal construal, (33) to (35) -/

/-- A context, (31): the common ground, the construals of the underspecified question, each a
cover of the common ground and any two comparable by width, and the speaker's verdicts on
which questions satisfy Quality and Relevance, (34). -/
structure Context (W : Type*) where
  /-- The common ground. -/
  info : Set W
  /-- The construals of the underspecified question. -/
  uq : Set (Question W)
  /-- The speaker has sufficient evidence that a true answer is accessible, (34a). -/
  quality : Question W → Prop
  /-- The speaker considers answering the question relevant to the discourse goals, (34b). -/
  relevance : Question W → Prop
  nonempty : uq.Nonempty
  info_eq : ∀ q ∈ uq, q.info = info
  comparable : ∀ q ∈ uq, ∀ q' ∈ uq, q ≠ q' → WiderThan q q' ∨ WiderThan q' q

namespace Context

variable (c : Context W) (q : Question W)

/-- A question is answerable when it satisfies Quality and Relevance, (34). -/
def Answerable : Prop := c.quality q ∧ c.relevance q

/-- The widest construal, (33): none is wider. -/
def IsWidest : Prop := q ∈ c.uq ∧ ∀ q' ∈ c.uq, ¬ WiderThan q' q

/-- The optimal construal, (35): answerable, with no wider answerable construal. -/
def IsOptimal : Prop :=
  q ∈ c.uq ∧ c.Answerable q ∧ ∀ q' ∈ c.uq, c.Answerable q' → ¬ WiderThan q' q

variable {c q}

/-- The widest construal is unique, since any two construals are comparable. -/
theorem IsWidest.unique {q' : Question W} (h : c.IsWidest q) (h' : c.IsWidest q') : q = q' :=
  by_contra λ hne => (c.comparable q h.1 q' h'.1 hne).elim (h'.2 q h.1) (h.2 q' h'.1)

/-- The optimal construal is unique: the definite description of (35). -/
theorem IsOptimal.unique {q' : Question W} (h : c.IsOptimal q) (h' : c.IsOptimal q') :
    q = q' :=
  by_contra λ hne =>
    (c.comparable q h.1 q' h'.1 hne).elim (h'.2.2 q h.1 h.2.1) (h.2.2 q' h'.1 h'.2.1)

/-- (37a): the widest construal, when answerable, is the optimal one. -/
theorem IsWidest.isOptimal (h : c.IsWidest q) (ha : c.Answerable q) : c.IsOptimal q :=
  ⟨h.1, ha, λ q' hq' _ => h.2 q' hq'⟩

/-- No construal wider than the optimal one is answerable. -/
theorem IsOptimal.not_answerable {q' : Question W} (h : c.IsOptimal q) (hq' : q' ∈ c.uq)
    (hw : WiderThan q' q) : ¬ c.Answerable q' :=
  λ ha => h.2.2 q' hq' ha hw

/-- The three kinds of context in which a construal is optimal, (37): it is the widest
construal; or some wider construal fails Quality; or some wider construal satisfies Quality
and fails Relevance. -/
theorem IsOptimal.widest_or_quality_or_relevance (h : c.IsOptimal q) :
    c.IsWidest q ∨ (∃ q' ∈ c.uq, WiderThan q' q ∧ ¬ c.quality q') ∨
      ∃ q' ∈ c.uq, WiderThan q' q ∧ c.quality q' ∧ ¬ c.relevance q' := by
  by_cases hw : c.IsWidest q
  · exact Or.inl hw
  obtain ⟨q', hq', hw'⟩ : ∃ q' ∈ c.uq, WiderThan q' q := by
    by_contra h'
    exact hw ⟨h.1, λ q' hq' hw' => h' ⟨q', hq', hw'⟩⟩
  by_cases hq : c.quality q'
  · exact Or.inr (Or.inr ⟨q', hq', hw', hq, λ hr => h.not_answerable hq' hw' ⟨hq, hr⟩⟩)
  · exact Or.inr (Or.inl ⟨q', hq', hw', hq⟩)

/-- The trivial construal is optimal exactly when it is answerable and no other construal is:
the unexplanatory use, where the others fail Quality, and the unelaboratory use, where they
fail Relevance, §4.4 and §4.5. -/
theorem isOptimal_ofSet_iff (hmem : ofSet c.info ∈ c.uq)
    (hnt : ∀ q ∈ c.uq, q ≠ ofSet c.info → ∃ p ∈ alt q, p ≠ c.info) :
    c.IsOptimal (ofSet c.info) ↔
      c.Answerable (ofSet c.info) ∧ ∀ q ∈ c.uq, q ≠ ofSet c.info → ¬ c.Answerable q := by
  refine ⟨λ h => ⟨h.2.1, λ q hq hne ha => ?_⟩, λ ⟨ha, h⟩ => ⟨hmem, ha, λ q hq ha' hw => ?_⟩⟩
  · obtain ⟨p, hp, hpne⟩ := hnt q hq hne
    exact h.2.2 q hq ha (widerThan_ofSet (c.info_eq q hq) hp hpne)
  · by_cases hne : q = ofSet c.info
    · exact WiderThan.irrefl _ (hne ▸ hw)
    · exact h q hq hne ha'

end Context

/-! ### The lexical entry, (36) -/

/-- *Just* with the current question `cq` and prejacent `p`, (36): it presupposes that `cq` is
the optimal construal of the underspecified question and asserts `p`. -/
def just (c : Context W) (cq : Question W) (p : Set W) : PartialProp W where
  presup _ := c.IsOptimal cq
  assertion := (· ∈ p)

variable {c : Context W} {cq cq' : Question W} {p p' : Set W} {w w' : W}

theorem just_defined_iff : PartialProp.defined w (just c cq p) ↔ c.IsOptimal cq := Iff.rfl

theorem just_holds_iff : PartialProp.holds w (just c cq p) ↔ c.IsOptimal cq ∧ w ∈ p :=
  Iff.rfl

/-- Two defined uses of *just* in one context address the same current question: the
presupposition fixes the construal. -/
theorem eq_of_just_defined (h : PartialProp.defined w (just c cq p))
    (h' : PartialProp.defined w' (just c cq' p')) : cq = cq' :=
  h.unique h'

/-! ### Partitions: refinement is width, §4.2 and §4.7 -/

/-- A finer partition of the common ground is a wider construal, (40b) against (40a). -/
theorem widerThan_fromSetoid {r s : Setoid W} (h : r < s) :
    WiderThan (fromSetoid r) (fromSetoid s) := by
  obtain ⟨hle, hnle⟩ := lt_iff_le_not_ge.1 h
  obtain ⟨x, y, hs, hr⟩ : ∃ x y, s x y ∧ ¬ r x y := by
    by_contra h'
    exact hnle (Setoid.le_def.2 λ {x y} hxy => by_contra λ hr => h' ⟨x, y, hxy, hr⟩)
  have : Nonempty W := ⟨x⟩
  refine ⟨by rw [info_fromSetoid, info_fromSetoid], ?_, {z | r z y},
    mem_alt_fromSetoid_of_mem_classes _ (Setoid.mem_classes r y), {z | s z y},
    mem_alt_fromSetoid_of_mem_classes _ (Setoid.mem_classes s y),
    λ z hz => Setoid.le_def.1 hle hz, λ hsub => hr (hsub hs)⟩
  rw [alt_fromSetoid, alt_fromSetoid]
  rintro _ ⟨v, rfl⟩ _ ⟨u, rfl⟩ hlt
  have huv : s u v := s.symm (Setoid.le_def.1 hle (hlt.1 (s.refl v)))
  exact hlt.2 λ z hz => s.trans (Setoid.le_def.1 hle hz) huv

/-! ### Grains, (22) to (24), and Figure 1 -/

/-- The grain of width `ε` on a discrete scale: cells of `ε` consecutive points centred on the
multiples of `ε`, so that a measure phrase denotes the cell it lies at the centre of, (24). -/
def grain (ε : ℕ) : Setoid ℕ := Setoid.ker (λ d => (2 * d + ε) / (2 * ε))

/-- The `k`th cell of the grain of width `ε`. -/
theorem mem_cell_iff {ε x k : ℕ} (hε : 0 < ε) :
    (2 * x + ε) / (2 * ε) = k ↔ 2 * (ε * k) ≤ 2 * x + ε ∧ 2 * x + ε < 2 * (ε * k) + 2 * ε := by
  have h2 : 0 < 2 * ε := by omega
  have e1 : k * (2 * ε) = 2 * (ε * k) := by rw [Nat.mul_comm k (2 * ε), Nat.mul_assoc]
  have e2 : (k + 1) * (2 * ε) = 2 * (ε * k) + 2 * ε := by rw [Nat.add_mul, Nat.one_mul, e1]
  rw [eq_comm, le_antisymm_iff, Nat.le_div_iff_mul_le h2, e1]
  refine and_congr_right λ _ => ⟨λ h3 => ?_, λ h3 => ?_⟩
  · have := (Nat.div_lt_iff_lt_mul h2).1 (Nat.lt_add_one_iff.2 h3)
    rwa [e2] at this
  · exact Nat.lt_add_one_iff.1 ((Nat.div_lt_iff_lt_mul h2).2 (by rw [e2]; exact h3))

/-- A cell of the grain of width `ε` spans fewer than `ε` points. -/
theorem sub_lt_of_cell {ε x y k : ℕ} (hε : 0 < ε) (hx : (2 * x + ε) / (2 * ε) = k)
    (hy : (2 * y + ε) / (2 * ε) = k) : y - x < ε := by
  have := (mem_cell_iff hε).1 hx
  have := (mem_cell_iff hε).1 hy
  omega

/-- Away from the bottom of the scale, a cell of the coarser grain has two points that no cell
of the finer grain contains together. -/
theorem not_cell_subset {ε₁ ε₂ k j : ℕ} (h₁ : 0 < ε₁) (h : ε₁ < ε₂) (hk : 0 < k) :
    ¬ {x | (2 * x + ε₂) / (2 * ε₂) = k} ⊆ {x | (2 * x + ε₁) / (2 * ε₁) = j} := λ hsub => by
  have hεk : ε₂ ≤ ε₂ * k := Nat.le_mul_of_pos_right ε₂ hk
  have hb : ε₂ * k - ε₂ / 2 ∈ {x | (2 * x + ε₂) / (2 * ε₂) = k} :=
    (mem_cell_iff (by omega)).2 ⟨by omega, by omega⟩
  have ht : ε₂ * k + (ε₂ - 1) / 2 ∈ {x | (2 * x + ε₂) / (2 * ε₂) = k} :=
    (mem_cell_iff (by omega)).2 ⟨by omega, by omega⟩
  have := sub_lt_of_cell h₁ (hsub hb) (hsub ht)
  omega

/-- The finer grain is the wider construal, (23) and §4.7.1: no cell of the coarser grain is
properly contained in a cell of the finer one, and the finer cell centred on `ε₁ * ε₂` is
properly contained in the coarser cell centred there. -/
theorem widerThan_grain {ε₁ ε₂ : ℕ} (h₁ : 0 < ε₁) (h : ε₁ < ε₂) :
    WiderThan (fromSetoid (grain ε₁)) (fromSetoid (grain ε₂)) := by
  have h₂ : 0 < ε₂ := h₁.trans h
  have hcomm : ε₂ * ε₁ = ε₁ * ε₂ := Nat.mul_comm _ _
  have hf : (2 * (ε₁ * ε₂) + ε₁) / (2 * ε₁) = ε₂ := (mem_cell_iff h₁).2 ⟨by omega, by omega⟩
  have hc : (2 * (ε₂ * ε₁) + ε₂) / (2 * ε₂) = ε₁ := (mem_cell_iff h₂).2 ⟨by omega, by omega⟩
  refine ⟨by rw [info_fromSetoid, info_fromSetoid], ?_, {x | grain ε₁ x (ε₁ * ε₂)},
    mem_alt_fromSetoid_of_mem_classes _ (Setoid.mem_classes _ _), {x | grain ε₂ x (ε₂ * ε₁)},
    mem_alt_fromSetoid_of_mem_classes _ (Setoid.mem_classes _ _), ?_, ?_⟩
  · rw [alt_fromSetoid, alt_fromSetoid]
    rintro _ ⟨y, rfl⟩ _ ⟨z, rfl⟩ ⟨hsub, hnsub⟩
    rcases Nat.eq_zero_or_pos ((2 * y + ε₂) / (2 * ε₂)) with hk | hk
    · have h0 : (2 * 0 + ε₁) / (2 * ε₁) = 0 := (mem_cell_iff h₁).2 ⟨by omega, by omega⟩
      have hz : (2 * z + ε₁) / (2 * ε₁) = 0 := by
        have := hsub (show (0 : ℕ) ∈ {x | grain ε₂ x y} by
          show (2 * 0 + ε₂) / (2 * ε₂) = (2 * y + ε₂) / (2 * ε₂)
          rw [hk]
          exact (mem_cell_iff h₂).2 ⟨by omega, by omega⟩)
        exact (this : (2 * 0 + ε₁) / (2 * ε₁) = (2 * z + ε₁) / (2 * ε₁)).symm.trans h0
      refine hnsub λ x hx => ?_
      have := (mem_cell_iff h₁).1 ((hx : (2 * x + ε₁) / (2 * ε₁) = _).trans hz)
      show (2 * x + ε₂) / (2 * ε₂) = (2 * y + ε₂) / (2 * ε₂)
      rw [hk]
      exact (mem_cell_iff h₂).2 ⟨by omega, by omega⟩
    · exact not_cell_subset h₁ h hk hsub
  · intro x hx
    have := (mem_cell_iff h₁).1 ((hx : (2 * x + ε₁) / (2 * ε₁) = _).trans hf)
    show (2 * x + ε₂) / (2 * ε₂) = (2 * (ε₂ * ε₁) + ε₂) / (2 * ε₂)
    rw [hc]
    exact (mem_cell_iff h₂).2 ⟨by omega, by omega⟩
  · intro hsub
    exact not_cell_subset h₁ h h₁ λ x hx => hsub (hx.trans hc.symm)

/-- Figure 1 in quarter years: the half-year grain is wider than the year grain but does not
refine it, since the half-year cell of one and a half years straddles two year cells; so the
construals are ordered by width and not by [groenendijk-stokhof-1984]'s entailment, fn. 20. -/
theorem figure1 :
    WiderThan (fromSetoid (grain 2)) (fromSetoid (grain 4)) ∧ ¬ grain 2 ≤ grain 4 ∧
      ¬ fromSetoid (grain 2) ≤ fromSetoid (grain 4) := by
  have hle : ¬ grain 2 ≤ grain 4 := λ h =>
    absurd (Setoid.le_def.1 h (show grain 2 5 6 from rfl))
      (show (2 * 5 + 4) / (2 * 4) ≠ (2 * 6 + 4) / (2 * 4) by decide)
  exact ⟨widerThan_grain (by omega) (by omega), hle, λ h => hle ((fromSetoid_le_iff _ _).1 h)⟩

/-! ### Extreme adjectives, §4.8 -/

/-- The construal of a degree question whose zone of indifference, [morzycki-2012], begins at
`m`: degrees below `m` are distinguished and degrees from `m` on are not. -/
def zone (m : ℕ) : Setoid ℕ := Setoid.ker (min · m)

/-- A construal whose zone of indifference begins later is finer and so wider, Figure 2: the
emphatic use takes the zone to begin as late as the speaker can conceive. -/
theorem widerThan_zone {m m' : ℕ} (h : m < m') :
    WiderThan (fromSetoid (zone m')) (fromSetoid (zone m)) := by
  refine widerThan_fromSetoid (lt_iff_le_not_ge.2 ⟨Setoid.le_def.2 λ {x y} hxy => ?_, λ hle => ?_⟩)
  · have hxy : min x m' = min y m' := hxy
    show min x m = min y m
    omega
  · have hmm : zone m m m' := by
      show min m m = min m' m
      omega
    have := Setoid.le_def.1 hle hmm
    have : min m m' = min m' m' := this
    omega

/-! ### Constituent questions, §4.1 -/

variable {A : Type*}

/-- The mention-all construal of *which x is P?* over worlds that are extensions of `P`: one
alternative per nonempty extension. -/
def mentionAll : Question (Set A) := which {E : Set A | E.Nonempty} λ E => {E}

/-- The mention-some construal: one alternative per individual, the worlds in which it is `P`. -/
def mentionSome : Question (Set A) := which Set.univ λ a => {E | a ∈ E}

/-- The mention-all construal of a constituent question is wider than the mention-some one,
§4.1: none of its alternatives is entailed by an alternative of the mention-some construal. -/
theorem widerThan_mentionAll [Nontrivial A] :
    WiderThan (mentionAll (A := A)) mentionSome := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne A
  have hall : alt (mentionAll (A := A)) = (λ E => {E}) '' {E : Set A | E.Nonempty} :=
    alt_which_of_forall_subset_eq ⟨{a}, Set.singleton_nonempty a⟩
      (λ E _ => Set.singleton_nonempty E) λ E _ E' _ h => by
        rw [Set.singleton_subset_singleton.1 h]
  have hsome : alt (mentionSome (A := A)) = (λ a => {E | a ∈ E}) '' Set.univ :=
    alt_which_of_forall_subset_eq ⟨a, Set.mem_univ a⟩ (λ a _ => ⟨{a}, Set.mem_singleton a⟩)
      λ a _ b _ h => by
        have hba : b = a := h (Set.mem_singleton a)
        rw [hba]
  refine ⟨?_, ?_, {{a}}, hall ▸ ⟨{a}, Set.singleton_nonempty a, rfl⟩, {E | a ∈ E},
    hsome ▸ ⟨a, Set.mem_univ a, rfl⟩, Set.singleton_subset_iff.2 (Set.mem_singleton a),
    λ hsub => ?_⟩
  · ext E
    simp only [mentionAll, mentionSome, info_which, Set.mem_iUnion, Set.mem_ofPred_eq,
      Set.mem_singleton_iff, Set.mem_univ, true_and, exists_prop, exists_eq_right']
    exact Set.nonempty_def
  · rw [hall, hsome]
    rintro _ ⟨x, -, rfl⟩ _ ⟨E, -, rfl⟩ hlt
    have hlt' : {E : Set A | x ∈ E} = ∅ := Set.eq_empty_of_ssubset_singleton hlt
    have hmem : ({x} : Set A) ∈ {E : Set A | x ∈ E} := Set.mem_singleton x
    rw [hlt'] at hmem
    exact Set.notMem_empty _ hmem
  · have hab' : ({a, b} : Set A) = {a} := hsub (show ({a, b} : Set A) ∈ {E | a ∈ E} from
      Set.mem_insert a {b})
    exact hab (hab' ▸ Set.mem_insert_of_mem a (Set.mem_singleton b) : b ∈ ({a} : Set A)).symm

end DeoThomas2025
