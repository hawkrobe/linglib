module

public import Linglib.Studies.KrizChemla2015
public import Linglib.Studies.BarLev2021
public import Linglib.Semantics.Homogeneity.Usable
public import Linglib.Data.Experiments.AugurzkyEtAl2023

/-!
# Augurzky et al. 2023: plural definites in context

Plural definites are homogeneous — *every boy opened his presents* is understood as *all* of
them, its negation as *none* — and non-maximal: where all that matters is whether any present
was opened, the sentence passes though a few presents stayed closed. The implicature approach
gives the definite an existential meaning, strengthened to the universal by an implicature in
positive environments only, so that pruning alternatives yields non-maximality there and
nowhere else. The non-implicature approach gives the sentence a truth-value gap in mixed
scenarios and lets the question the context raises group the gap with truth or with falsity,
symmetrically for positive and negative sentences. Two picture-verification experiments put the
plural definite under *every* and a negative quantifier, *no* in Experiment 1 and *not every* in
Experiment 2, while a family rule made it relevant whether any or whether all presents were
opened. The context affected *every* more than *no*, as only the implicature approach predicts,
and *every* and *not every* alike, as only the non-implicature approach predicts, so each
approach is challenged by one of the experiments.

Both approaches are derived from their sources. The non-implicature verdict is [kriz-2016]'s
usability of the trivalent sentence relative to the question the context raises
(`Homogeneity.usable`), which comes to truth at the resolution of the gap that the question
picks (`usable_iff_of_le`). The implicature verdict is the existential literal meaning,
strengthened to the universal one where an implicature arises and the context does not prune
it; for the unembedded sentence of Table 1 this is the reading [bar-lev-2021]'s pruning selects
under a polar question, and Križ's usability under that question agrees with it
(`usable_iff_mem_of_isReading`). The approaches agree wherever implicatures arise
(`implicature_iff_nonImplicature`), so they can part only under a downward-entailing
quantifier, where the non-implicature verdict negates under the complement of the quantifier
(`nonImplicature_compl`) while the implicature verdict ignores the context
(`implicature_context_free`). An approach predicts an interaction of context and polarity when
the context changes its verdict on one quantifier's mixed picture and not on the other's, and
the printed tests decide which prediction each experiment bears out.

## Main definitions

* `Quantifier.tree`, `Context.designation`, `Context.issue`: the paper's quantifiers as van
  Benthem number trees, the resolution each context makes and the question it raises.
* `nonImplicature`, `Strengthens`, `implicature`: the two verdicts on a display.
* `Quantifier.enriched`: *not every* together with its own implicature, the rescue of §4.2.
* `Approach`, `Approach.PredictsInteraction`, `InteractionSignificant`: the accounts against the
  printed tests.

## Main results

* `usable_iff_of_le`, `nonImplicature_iff`, `not_usable_rule`: usability under any question
  between the resolution and the reading, and failure under the question whether the rule was
  respected.
* `implicature_iff_nonImplicature`, `nonImplicature_compl`, `implicature_context_free`: where
  the approaches agree and how they part (§1.3).
* `table1_implicature`, `table1_nonImplicature`, `usable_iff_mem_of_isReading`, `table2`: the
  predictions of Tables 1 and 2.
* `implicature_fits_iff`, `nonImplicature_fits_iff`, `enrichedImplicature_fits`: each approach
  fits the interaction test of one experiment, and the §4.2 rescue fits both.
* `exactlyTwo_symmetric`: the non-implicature prediction for the test (20) proposed in §4.3.

## Implementation notes

The paper states the questions (12) and (13) only for the unembedded sentence. For the
quantified sentences the context's question is lifted boy by boy, to which boys opened any, or
which opened all, of their presents (`Context.issue`); any question between that one and the
polar question on the reading serves as well (`usable_iff_of_le`), but the literal question of
the secondary task, whether the rule was respected, is not among them (`not_usable_rule`). The
implicature verdict strengthens the definite of each boy, as the embedded implicature of (17)
does, and the resolution each context makes is the reading its question selects for a boy's
nine presents (`designated_cell`). The figures' pictures are examples of their conditions, and
the text of §3.2.1 misdescribes Experiment 2's mixed picture (`text_picture_notEvery`). The
verdicts are bivalent, so they register whether the context changes a judgment and not by how
much: the smaller context effect for *no*, which §3.1.2 also counts against the simple
implicature approach, is invisible to them.

## References

* [augurzky-etal-2023]
* [kriz-chemla-2015]
* [magri-2014]
* [bar-lev-2021]
* [kriz-2016]
* [kriz-spector-2021]
-/

open Quantifier (NumberTree)

@[expose] public section

namespace AugurzkyEtAl2023

open Data.Experiments
open Trivalent (Designation designated)
open KrizChemla2015 (Display cell resolve reading someReading allReading supervaluation
  gapValue_eq_true_iff gapValue_eq_false_iff reading_all reading_no)

/-! ### Quantifiers and pictures -/

/-- The number tree each quantifier denotes. -/
def Quantifier.tree : Quantifier → NumberTree
  | .every => NumberTree.all
  | .no => NumberTree.no
  | .notEvery => NumberTree.notAll

instance : (q : Quantifier) → DecidableRel q.tree
  | .every => inferInstanceAs (DecidableRel NumberTree.all)
  | .no => inferInstanceAs (DecidableRel NumberTree.no)
  | .notEvery => inferInstanceAs (DecidableRel NumberTree.notAll)

/-- A picture as a display: each boy's value is *he opened his presents* over his nine. -/
def Picture.display (p : Picture) : Display := p.opened.map cell

/-- The negative quantifier of an experiment. -/
def Experiment.negative : Experiment → Quantifier
  | .one => .no
  | .two => .notEvery

/-- A mixed picture for *every* and *not every*: some boy opened some but not all of his
presents, and the others opened all of theirs. -/
def PositiveMixed (d : Display) : Prop := .indet ∈ d ∧ .false ∉ d

/-- A mixed picture for *no*: some boy opened some but not all of his presents, and the others
opened none of theirs. -/
def NegativeMixed (d : Display) : Prop := .indet ∈ d ∧ .true ∉ d

instance : DecidablePred PositiveMixed := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

instance : DecidablePred NegativeMixed := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- Each experiment pairs *every* with its negative quantifier. -/
theorem pictures_quantifier :
    ∀ p ∈ pictures, p.quantifier = .every ∨ p.quantifier = p.experiment.negative := by
  decide

/-- The mixed pictures are mixed in the sense their quantifier needs. -/
theorem pictures_mixed : ∀ p ∈ pictures, p.truth = .mixed →
    if p.quantifier = .no then NegativeMixed p.display else PositiveMixed p.display := by
  decide

/-- The controls are clearly true or clearly false: both resolutions of the definite agree. -/
theorem pictures_controls : ∀ p ∈ pictures, p.truth ≠ .mixed →
    supervaluation p.quantifier.tree p.display =
      if p.truth = .trueControl then .true else .false := by
  decide

/-- The picture §3.2.1's text describes for Experiment 2's mixed condition, two boys with all
their presents open and two with none, would make *not every* clearly true. -/
theorem text_picture_notEvery :
    supervaluation NumberTree.notAll ([9, 9, 0, 0].map cell) = .true := by
  decide

/-! ### Contexts -/

/-- The resolution of a partially opened set that each context makes: the existential context
designates what is not false, the universal one only what is true. -/
def Context.designation : Context → Designation
  | .existential => .lp
  | .universal => .k3

/-- The question the family rule raises about the boys: which of them opened any of their
presents, or which opened all of them. -/
def Context.issue (ctx : Context) : Setoid Display := Setoid.ker (resolve ctx.designation)

/-- Each boy's value resolved at a designation standard. -/
private def complete (δ : Designation) (d : Display) : Display :=
  d.map fun v ↦ .ofProp (designated δ v)

/-- A completed display looks the same at every standard: the one it was completed at. -/
private theorem resolve_complete (δ δ' : Designation) (d : Display) :
    resolve δ' (complete δ d) = resolve δ d := by
  simp only [resolve, complete, List.map_map]
  exact List.map_congr_left fun v _ ↦ by
    simp [Function.comp, Trivalent.ofProp, Trivalent.designated_ofBool]

/-! ### The non-implicature approach -/

section NonImplicature

variable (q : NumberTree) [DecidableRel q]

/-- Under any question coarser than the resolution at `δ` and fine enough to decide the reading
at `δ`, the trivalent sentence is usable exactly where that reading holds: no cell holds both a
true and a false display, and a gapped display shares its cell with its completion at `δ`. -/
theorem usable_iff_of_le {Q : Setoid Display} {δ : Designation}
    (h₁ : Setoid.ker (resolve δ) ≤ Q) (h₂ : Q.Decides {d | reading q d δ}) (d : Display) :
    Homogeneity.usable Q (supervaluation q) d ↔ reading q d δ := by
  have hcell : ∀ {d d'}, Q d d' → (reading q d δ ↔ reading q d' δ) :=
    fun h ↦ Setoid.polar_iff.1 (h₂ h)
  have htrue : ∀ d', supervaluation q d' = .true → reading q d' δ := fun d' h ↦ by
    have := gapValue_eq_true_iff.1 h
    cases δ <;> tauto
  have hfalse : ∀ d', supervaluation q d' = .false → ¬ reading q d' δ := fun d' h ↦ by
    have := gapValue_eq_false_iff.1 h
    cases δ <;> tauto
  have hres : ∀ δ', reading q (complete δ d) δ' ↔ reading q d δ := fun δ' ↦ by
    rw [reading, reading, resolve_complete]
  refine ⟨fun ⟨_, ⟨d', hd', h'⟩, _⟩ ↦ (hcell hd').2 (htrue d' h'), fun h ↦
    ⟨fun hf ↦ hfalse d hf h, ⟨complete δ d, h₁ (resolve_complete δ δ d).symm,
      gapValue_eq_true_iff.2 ⟨(hres _).2 h, (hres _).2 h⟩⟩,
      fun ⟨d₁, d₂, h₁₂, ht, hf⟩ ↦ hfalse d₂ hf ((hcell h₁₂).1 (htrue d₁ ht))⟩⟩

/-- The non-implicature verdict ([kriz-2016]): the trivalent sentence is usable at the display
relative to the question the context raises. -/
def nonImplicature (ctx : Context) (d : Display) : Prop :=
  Homogeneity.usable ctx.issue (supervaluation q) d

/-- The non-implicature verdict is truth at the resolution the context makes. -/
theorem nonImplicature_iff (ctx : Context) (d : Display) :
    nonImplicature q ctx d ↔ reading q d ctx.designation :=
  usable_iff_of_le q le_rfl (fun _ _ h ↦ Setoid.polar_iff.2 <|
    show reading q _ _ ↔ reading q _ _ by
      rw [reading, reading, show resolve ctx.designation _ = resolve ctx.designation _ from h]) d

instance (ctx : Context) (d : Display) : Decidable (nonImplicature q ctx d) :=
  decidable_of_iff _ (nonImplicature_iff q ctx d).symm

/-- The non-implicature approach is symmetric: under the complement of a quantifier, *not
every* for *every*, the verdict is negated in every context. -/
theorem nonImplicature_compl (ctx : Context) (d : Display) :
    nonImplicature qᶜ ctx d ↔ ¬ nonImplicature q ctx d := by
  rw [nonImplicature_iff, nonImplicature_iff]
  rfl

end NonImplicature

/-- The question the secondary task asks, whether the family rule was respected: that no present
was opened, or that all were. -/
def Context.rule : Context → Set Display
  | .existential => {d | ∀ v ∈ d, v = .false}
  | .universal => {d | ∀ v ∈ d, v = .true}

/-- Under the question whether the rule was respected, *every boy opened his presents* is usable
nowhere in the existential context: the rule is broken both where every boy opened all his
presents and where one opened none, so the question does not separate truth from falsity. -/
theorem not_usable_rule (d : Display) :
    ¬ Homogeneity.usable (Setoid.polar Context.existential.rule)
      (supervaluation Quantifier.every.tree) d := by
  refine fun ⟨_, _, h⟩ ↦ h ⟨[.true, .true], [.false, .true], ?_, by decide, by decide⟩
  exact Setoid.polar_iff.2 (iff_of_false (by simp [Context.rule]) (by simp [Context.rule]))

/-! ### The implicature approach -/

section Implicature

/-- Implicatures arise in the scope of a quantifier unless it is downward entailing, as *no* and
*not every* are. -/
def Strengthens (q : NumberTree) : Prop := ¬ q.ScopeAntitone

instance : (q : Quantifier) → Decidable (Strengthens q.tree)
  | .every => isTrue fun h ↦ absurd (h 0 0 rfl) (Nat.succ_ne_zero 0)
  | .no => isFalse (not_not.2 NumberTree.scopeAntitone_no)
  | .notEvery => isFalse (not_not.2 NumberTree.scopeAntitone_notAll)

variable (q : NumberTree) [DecidableRel q] [Decidable (Strengthens q)]

/-- The implicature verdict: the existential literal meaning, strengthened boy by boy to the
universal one where an implicature arises, unless the existential context prunes the
alternatives that strengthen it. -/
def implicature (ctx : Context) (d : Display) : Prop :=
  if Strengthens q ∧ ctx = .universal then allReading q d else someReading q d

instance (ctx : Context) (d : Display) : Decidable (implicature q ctx d) :=
  inferInstanceAs
    (Decidable (if Strengthens q ∧ ctx = .universal then allReading q d else someReading q d))

variable {q}

/-- §1.3: wherever implicatures arise the two approaches agree. -/
theorem implicature_iff_nonImplicature (h : Strengthens q) (ctx : Context) (d : Display) :
    implicature q ctx d ↔ nonImplicature q ctx d := by
  rw [nonImplicature_iff]
  cases ctx <;> simp [implicature, h, Context.designation]

omit [DecidableRel q] in
/-- Where no implicature arises, the verdict is the literal meaning. -/
theorem implicature_of_not_strengthens (h : ¬ Strengthens q) (ctx : Context) (d : Display) :
    implicature q ctx d ↔ someReading q d := by
  simp [implicature, h]

omit [DecidableRel q] in
/-- §1.3: under a downward-entailing quantifier the implicature verdict ignores the context. -/
theorem implicature_context_free (h : ¬ Strengthens q) (ctx ctx' : Context) (d : Display) :
    implicature q ctx d ↔ implicature q ctx' d := by
  rw [implicature_of_not_strengthens h, implicature_of_not_strengthens h]

end Implicature

/-! ### Table 1: the unembedded sentence

*Frank opened his presents* in the model of [bar-lev-2021] whose worlds are the sets of presents
Frank opened, for any plurality of presents `x`. -/

section Table1

open BarLev2021 (holds atLeast existsPlural subdomainAlts IsReading)
open Exhaustification (exhIEII)

variable {α : Type*} [DecidableEq α] (x : Finset α)

/-- How many presents the context's question asks about: any, or all. -/
def Context.threshold : Context → ℕ
  | .existential => 1
  | .universal => x.card

/-- The questions (12), whether Frank opened any of his presents, and (13), whether he opened
all of them. -/
def Context.question (ctx : Context) : Setoid (Finset α) :=
  Setoid.polar (atLeast x x holds (ctx.threshold x))

variable {x}

private theorem mem_atLeast_iff {k : ℕ} {w : Finset α} :
    w ∈ atLeast x x holds k ↔ k ≤ (x ∩ w).card := by
  simp [atLeast, BarLev2021.count_holds, Finset.inter_self]

private theorem barePlural_eq_true_iff {w : Finset α} :
    Homogeneity.barePlural holds x w = .true ↔ x ⊆ w := by
  simp [Homogeneity.barePlural, Trivalent.supervaluation_eq_true_iff, Finset.subset_iff]

private theorem card_eq_zero_of_barePlural_eq_false {w : Finset α}
    (h : Homogeneity.barePlural holds x w = .false) : (x ∩ w).card = 0 := by
  simp only [Homogeneity.barePlural, Trivalent.supervaluation_eq_false_iff] at h
  exact Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun a ha ↦
    h.2 a (Finset.mem_inter.1 ha).1 (Finset.mem_inter.1 ha).2)

private theorem mem_atLeast_of_barePlural_eq_true {k : ℕ} (hkx : k ≤ x.card) {w : Finset α}
    (h : Homogeneity.barePlural holds x w = .true) : w ∈ atLeast x x holds k := by
  rwa [mem_atLeast_iff, Finset.inter_eq_left.2 (barePlural_eq_true_iff.1 h)]

private theorem notMem_atLeast_of_barePlural_eq_false {k : ℕ} (hk : 0 < k) {w : Finset α}
    (h : Homogeneity.barePlural holds x w = .false) : w ∉ atLeast x x holds k := by
  rw [mem_atLeast_iff, card_eq_zero_of_barePlural_eq_false h]
  omega

/-- Under the polar question whether at least `k` of the presents were opened, the trivalent
positive sentence is usable exactly where at least `k` were. -/
theorem usable_barePlural_iff {k : ℕ} (hk : 0 < k) (hkx : k ≤ x.card) (w : Finset α) :
    Homogeneity.usable (Setoid.polar (atLeast x x holds k)) (Homogeneity.barePlural holds x) w ↔
      w ∈ atLeast x x holds k := by
  have hx := mem_atLeast_of_barePlural_eq_true hkx (barePlural_eq_true_iff.2 subset_rfl)
  refine ⟨fun ⟨_, ⟨w', hw', h⟩, _⟩ ↦
    (Setoid.polar_iff.1 hw').2 (mem_atLeast_of_barePlural_eq_true hkx h), fun hw ↦
    ⟨fun hf ↦ notMem_atLeast_of_barePlural_eq_false hk hf hw,
      ⟨x, Setoid.polar_iff.2 (iff_of_true hw hx), barePlural_eq_true_iff.2 subset_rfl⟩,
      fun ⟨_, _, h₁₂, h₁, h₂⟩ ↦ notMem_atLeast_of_barePlural_eq_false hk h₂
        ((Setoid.polar_iff.1 h₁₂).1 (mem_atLeast_of_barePlural_eq_true hkx h₁))⟩⟩

/-- Under the same question the negated sentence is usable exactly where fewer than `k` were
opened. -/
theorem usable_neg_barePlural_iff {k : ℕ} (hk : 0 < k) (hkx : k ≤ x.card) (w : Finset α) :
    Homogeneity.usable (Setoid.polar (atLeast x x holds k))
      (fun w ↦ (Homogeneity.barePlural holds x w).neg) w ↔ w ∉ atLeast x x holds k := by
  have hne : x.Nonempty := Finset.card_pos.1 (by omega)
  have hfalse : Homogeneity.barePlural holds x ∅ = .false := by
    simp [Homogeneity.barePlural, Trivalent.supervaluation_eq_false_iff, hne]
  have h0 := notMem_atLeast_of_barePlural_eq_false hk hfalse
  refine ⟨fun ⟨_, ⟨w', hw', h⟩, _⟩ hw ↦ notMem_atLeast_of_barePlural_eq_false hk
    (Trivalent.neg_eq_true_iff.1 h) ((Setoid.polar_iff.1 hw').1 hw), fun hw ↦
    ⟨fun hf ↦ hw (mem_atLeast_of_barePlural_eq_true hkx (Trivalent.neg_eq_false_iff.1 hf)),
      ⟨∅, Setoid.polar_iff.2 (iff_of_false hw h0), by simp [hfalse]⟩,
      fun ⟨_, _, h₁₂, h₁, h₂⟩ ↦ notMem_atLeast_of_barePlural_eq_false hk
        (Trivalent.neg_eq_true_iff.1 h₁) ((Setoid.polar_iff.1 h₁₂).2
          (mem_atLeast_of_barePlural_eq_true hkx (Trivalent.neg_eq_false_iff.1 h₂)))⟩⟩

/-- Where the approaches meet: under a polar question on a number of presents, Križ's usability
of the positive sentence is membership in the reading [bar-lev-2021]'s pruning selects. -/
theorem usable_iff_mem_of_isReading {k : ℕ} (hk : 0 < k) (hkx : k ≤ x.card)
    {r : Set (Finset α)} (hr : IsReading x x holds (Setoid.polar (atLeast x x holds k)) r)
    (w : Finset α) :
    Homogeneity.usable (Setoid.polar (atLeast x x holds k)) (Homogeneity.barePlural holds x) w ↔
      w ∈ r := by
  rw [hr.unique (BarLev2021.isReading_polar_atLeast_holds x x hk (by rwa [Finset.inter_self])),
    usable_barePlural_iff hk hkx]

omit [DecidableEq α] in
private theorem threshold_pos (hx : x.Nonempty) (ctx : Context) : 0 < ctx.threshold x := by
  cases ctx
  · exact Nat.one_pos
  · exact Finset.card_pos.2 hx

omit [DecidableEq α] in
private theorem threshold_le (hx : x.Nonempty) (ctx : Context) : ctx.threshold x ≤ x.card := by
  cases ctx
  · exact Finset.card_pos.2 hx
  · exact le_rfl

/-- The implicature row of Table 1 in a mixed scenario, where Frank opened some but not all of
his presents: the positive sentence means the reading the context's question selects, true
under the existential question only; the negative sentence is exhaustified vacuously, whatever
alternatives are pruned, and is false. -/
theorem table1_implicature (hx : x.Nonempty) {w : Finset α} (h₀ : 0 < (x ∩ w).card)
    (h₁ : (x ∩ w).card < x.card) (ctx : Context) :
    (∀ r, IsReading x x holds (ctx.question x) r → (w ∈ r ↔ ctx = .existential)) ∧
    ∀ C ⊆ compl '' subdomainAlts x x holds, w ∉ exhIEII C (existsPlural x x holds)ᶜ := by
  refine ⟨fun r hr ↦ ?_, fun C hC ↦ ?_⟩
  · rw [hr.unique (BarLev2021.isReading_polar_atLeast_holds x x (threshold_pos hx ctx)
      (by rw [Finset.inter_self]; exact threshold_le hx ctx)), mem_atLeast_iff]
    cases ctx
    · exact iff_of_true h₀ rfl
    · exact iff_of_false (Nat.not_le.2 h₁) (by decide)
  · rw [BarLev2021.exhIEII_compl_existsPlural hC ⟨∅, by simp [existsPlural]⟩]
    obtain ⟨a, ha⟩ := Finset.card_pos.1 h₀
    exact fun h ↦ h ⟨a, (Finset.mem_inter.1 ha).1, (Finset.mem_inter.1 ha).1,
      (Finset.mem_inter.1 ha).2⟩

/-- The non-implicature row of Table 1 in a mixed scenario: the gapped positive sentence is
usable under the existential question (12), and its negation under the universal one (13). -/
theorem table1_nonImplicature (hx : x.Nonempty) {w : Finset α} (h₀ : 0 < (x ∩ w).card)
    (h₁ : (x ∩ w).card < x.card) (ctx : Context) :
    (Homogeneity.usable (ctx.question x) (Homogeneity.barePlural holds x) w ↔
        ctx = .existential) ∧
      (Homogeneity.usable (ctx.question x) (fun w ↦ (Homogeneity.barePlural holds x w).neg) w ↔
        ctx = .universal) := by
  rw [Context.question, usable_barePlural_iff (threshold_pos hx ctx) (threshold_le hx ctx),
    usable_neg_barePlural_iff (threshold_pos hx ctx) (threshold_le hx ctx), mem_atLeast_iff]
  cases ctx
  · exact ⟨iff_of_true h₀ rfl, iff_of_false (not_not.2 h₀) (by decide)⟩
  · exact ⟨iff_of_false (Nat.not_le.2 h₁) (by decide), iff_of_true (Nat.not_le.2 h₁) rfl⟩

end Table1

/-- The resolution a context makes of a boy's cell is the reading its question selects for his
nine presents: at least one opened under the existential question, all nine under the universal
one. -/
theorem designated_cell (ctx : Context) (n : ℕ) :
    designated ctx.designation (cell n) ↔ ctx.threshold (Finset.range 9) ≤ n := by
  cases ctx
  · exact KrizChemla2015.designated_lp_cell n
  · rw [Context.threshold, Finset.card_range]
    exact KrizChemla2015.designated_k3_cell n

/-! ### Table 2 -/

/-- Table 2, on any mixed picture: both approaches accept *every* exactly in the existential
context; the implicature approach rejects *no* and *not every* in both contexts, the
non-implicature approach accepts both exactly in the universal context. -/
theorem table2 (ctx : Context) {d d' : Display} (hd : PositiveMixed d) (hd' : NegativeMixed d') :
    (implicature Quantifier.every.tree ctx d ↔ ctx = .existential) ∧
      ¬ implicature Quantifier.no.tree ctx d' ∧ ¬ implicature Quantifier.notEvery.tree ctx d ∧
      (nonImplicature Quantifier.every.tree ctx d ↔ ctx = .existential) ∧
      (nonImplicature Quantifier.no.tree ctx d' ↔ ctx = .universal) ∧
      (nonImplicature Quantifier.notEvery.tree ctx d ↔ ctx = .universal) := by
  have hk3 : ¬ reading NumberTree.all d .k3 := fun h ↦ by simpa using (reading_all _).1 h _ hd.1
  have hlp : reading NumberTree.all d .lp := (reading_all _).2 fun v hv ↦ by
    cases v <;> simp_all [PositiveMixed]
  have hk3' : reading NumberTree.no d' .k3 := (reading_no _).2 fun v hv ↦ by
    cases v <;> simp_all [NegativeMixed]
  have hlp' : ¬ reading NumberTree.no d' .lp := fun h ↦ by simpa using (reading_no _).1 h _ hd'.1
  have hc : ∀ δ, reading NumberTree.notAll d δ ↔ ¬ reading NumberTree.all d δ := fun _ ↦ Iff.rfl
  rw [implicature_iff_nonImplicature (by decide), implicature_of_not_strengthens (by decide),
    implicature_of_not_strengthens (by decide), nonImplicature_iff, nonImplicature_iff,
    nonImplicature_iff]
  cases ctx <;> simp [Context.designation, Quantifier.tree, someReading, hc, hk3, hlp, hk3', hlp']

/-! ### The implicature approach amended (§4.2) -/

/-- The quantifier together with its own scalar implicature, (16): *not every* strengthened by
the negation of its stronger alternative *no*, that some boy did. The other quantifiers have no
stronger alternative to deny. -/
def Quantifier.enriched : Quantifier → NumberTree
  | .notEvery => NumberTree.notAll ⊓ NumberTree.some
  | q => q.tree

instance : (q : Quantifier) → DecidableRel q.enriched
  | .every => inferInstanceAs (DecidableRel NumberTree.all)
  | .no => inferInstanceAs (DecidableRel NumberTree.no)
  | .notEvery => fun a b ↦ inferInstanceAs (Decidable (a ≠ 0 ∧ b ≠ 0))

/-- Together with its implicature, *not every* is no longer downward entailing, so implicatures
can arise in its scope, the added assumption of §4.2. -/
instance : (q : Quantifier) → Decidable (Strengthens q.enriched)
  | .every => isTrue fun h ↦ absurd (h 0 0 rfl) (Nat.succ_ne_zero 0)
  | .no => isFalse (not_not.2 NumberTree.scopeAntitone_no)
  | .notEvery => isTrue fun h ↦ (h 1 0 ⟨one_ne_zero, one_ne_zero⟩).2 rfl

/-- Nor is it upward entailing: the enriched environment is non-monotonic (§4.2). -/
theorem not_scopeMonotone_enriched_notEvery : ¬ Quantifier.notEvery.enriched.ScopeMonotone :=
  fun h ↦ (h 0 1 ⟨one_ne_zero, one_ne_zero⟩).1 rfl

/-! ### The experiments -/

/-- The accounts assessed: the two approaches, and the implicature approach amended by §4.2. -/
inductive Approach where
  | implicature
  | nonImplicature
  | enrichedImplicature
  deriving DecidableEq

/-- An approach's verdict on a quantifier's sentence in a context. -/
def Approach.verdict : Approach → Quantifier → Context → Display → Prop
  | .implicature, q => AugurzkyEtAl2023.implicature q.tree
  | .nonImplicature, q => AugurzkyEtAl2023.nonImplicature q.tree
  | .enrichedImplicature, q => AugurzkyEtAl2023.implicature q.enriched

instance : (a : Approach) → (q : Quantifier) → (ctx : Context) → (d : Display) →
    Decidable (a.verdict q ctx d)
  | .implicature, q, ctx, d => inferInstanceAs (Decidable (implicature q.tree ctx d))
  | .nonImplicature, q, ctx, d => inferInstanceAs (Decidable (nonImplicature q.tree ctx d))
  | .enrichedImplicature, q, ctx, d => inferInstanceAs (Decidable (implicature q.enriched ctx d))

/-- The context favouring a non-maximal reading, as Figures 3 and 5 recode it: the existential
one for *every*, the universal one for the negative quantifiers. -/
def Quantifier.lax : Quantifier → Context
  | .every => .existential
  | _ => .universal

/-- The context favouring a maximal reading. -/
def Quantifier.strict : Quantifier → Context
  | .every => .universal
  | _ => .existential

/-- An approach predicts that the lax context accepts a picture the strict context rejects. -/
def Approach.LaxEffect (a : Approach) (q : Quantifier) (d : Display) : Prop :=
  a.verdict q q.lax d ∧ ¬ a.verdict q q.strict d

instance (a : Approach) (q : Quantifier) (d : Display) : Decidable (a.LaxEffect q d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- An approach predicts an interaction of context and polarity in an experiment when it
predicts the lax context's effect on one of its quantifiers' mixed pictures but not on the
other's. -/
def Approach.PredictsInteraction (a : Approach) (e : Experiment) : Prop :=
  ∃ p ∈ pictures, ∃ p' ∈ pictures, p.experiment = e ∧ p'.experiment = e ∧ p.truth = .mixed ∧
    p'.truth = .mixed ∧
      ¬ (a.LaxEffect p.quantifier p.display ↔ a.LaxEffect p'.quantifier p'.display)

instance (a : Approach) (e : Experiment) : Decidable (a.PredictsInteraction e) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- A printed p-value is below 0.05: an upper bound at most 0.05, or a value under it. -/
def Bound.Significant : Bound → Decimal → Prop
  | .below, p => p.toRat ≤ 5 / 100
  | .exact, p => p.toRat < 5 / 100

instance : ∀ b p, Decidable (Bound.Significant b p)
  | .below, _ => inferInstanceAs (Decidable (_ ≤ _))
  | .exact, _ => inferInstanceAs (Decidable (_ < _))

/-- The mixed conditions of an experiment show a significant interaction of context and
polarity. -/
def InteractionSignificant (e : Experiment) : Prop :=
  ∃ t ∈ tests, t.experiment = e ∧ t.model = .mixed ∧ t.effect = .interaction ∧
    t.bound.Significant t.p

instance (e : Experiment) : Decidable (InteractionSignificant e) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The implicature approach predicts the interaction of Experiment 1 and misses the absence of
one in Experiment 2, where *not every* behaved like *every*. -/
theorem implicature_fits_iff (e : Experiment) :
    (Approach.implicature.PredictsInteraction e ↔ InteractionSignificant e) ↔ e = .one := by
  cases e <;> decide +kernel

/-- The non-implicature approach predicts the absence of an interaction in Experiment 2 and
misses the interaction of Experiment 1, where *no* resisted the universal context. -/
theorem nonImplicature_fits_iff (e : Experiment) :
    (Approach.nonImplicature.PredictsInteraction e ↔ InteractionSignificant e) ↔ e = .two := by
  cases e <;> decide +kernel

/-- The amendment of §4.2 "would capture our results": it predicts the outcome of both
interaction tests. -/
theorem enrichedImplicature_fits (e : Experiment) :
    Approach.enrichedImplicature.PredictsInteraction e ↔ InteractionSignificant e := by
  cases e <;> decide +kernel

/-! ### The proposed test (§4.3) -/

/-- (20) in a mixed scenario for its positive part: two boys opened some but not all of their
presents and the others opened none. -/
def exactlyTwoPositive : Display := [.indet, .indet, .false, .false]

/-- (20) in a mixed scenario for its negative part: two boys opened all of their presents and two
opened some but not all. -/
def exactlyTwoNegative : Display := [.true, .true, .indet, .indet]

/-- With the prior bias of the sentence held constant, the non-implicature approach predicts the
symmetric pattern: the positive part's gap resolved to truth by the existential question, the
negative part's by the universal one. -/
theorem exactlyTwo_symmetric (ctx : Context) :
    (nonImplicature (NumberTree.cardinal {2}) ctx exactlyTwoPositive ↔ ctx = .existential) ∧
      (nonImplicature (NumberTree.cardinal {2}) ctx exactlyTwoNegative ↔ ctx = .universal) := by
  cases ctx <;> decide

end AugurzkyEtAl2023
