import Mathlib.Order.UpperLower.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Linglib.Semantics.Degree.Basic
import Linglib.Semantics.Definiteness.Maximality

/-!
# Beck, Oda and Sugisaki 2004: comparison in Japanese without degree abstraction

This file formalizes Beck, Oda and Sugisaki's analysis of Japanese *yori*-comparatives. A
*yori*-constituent denotes an individual — a free relative, or a definite built from a
relative clause — and fixes the standard `c` of a positive or contextual comparative in the
main clause, in place of the *than*-clause degree set of the standard analysis. The authors
attribute the difference to a Degree Abstraction Parameter: Japanese does not bind degree
variables in the syntax. We state both repertoires of denotations and derive from them the
paper's three empirical differences — variable acceptability, no subcomparatives of degree,
no degree-based negative islands — and its scope argument.

## Main definitions

* `er`: the comparative morpheme on degree sets, `max D₂ > max D₁`.
* `pos`, `er₂`: the positive form and the contextual comparative at a standard `c`.
* `theC`: the Fregean definite over a contextual domain, the denotation of a *yori*-clause.
* `erJ`: the comparative that combines directly with the adjective meaning.

## Main results

* `pos_comparedTo`, `er₂_Iic_iff`: a context setter supplying `y` turns the positive form
  and the contextual comparative into the comparison with `y`.
* `isGreatest_card_of_isMaximal`: an amount standard is the cardinality of the maximal
  plurality.
* `pos_ne_subcomparative`: an individual standard lies on the matrix dimension and does not
  express a subcomparative of degree.
* `not_er_nobodyDegrees`, `yori_negative_entails_unbought`: the negated *than*-clause has
  no maximum on an unbounded scale, while the definite *yori*-clause is defined and entails
  a particular unbought individual.
* `er_everyoneDegrees_without_shared_book`: the standard comparative lacks the definite's
  uniqueness presupposition.
* `erJ_iff_pos`, `exists_wideScope_not_inSitu`: `erJ` has the truth conditions of the
  positive form and, applied in situ, yields only the narrow reading under `need`.

Example numbers follow the journal article; the examples are typed in
`Data/Examples/BeckOdaSugisaki2004.json`.

## References

* [beck-oda-sugisaki-2004]
* [von-stechow-1984], [heim-2000]: the standard analysis and the scope argument from
  intensional verbs.
* [rullmann-1995]: negative islands as maximality failure.
* [heim-kratzer-1998]: the positive form and the Fregean definite.
* [jacobson-1995]: free relatives as maximal individuals.
* [kennedy-1997]: the comparative combining directly with the adjective.
* [ishii-1991], [snyder-wexler-das-1995]: the acceptability and subcomparative data.
-/

namespace BeckOdaSugisaki2004

open Degree Definiteness

variable {Entity D : Type*} [LinearOrder D]

/-! ### The standard analysis -/

/-- The comparative morpheme on degree sets: `er D₁ D₂` holds iff `max D₂ > max D₁` (8). -/
def er (D₁ D₂ : Set D) : Prop :=
  ∃ m₁ m₂, IsGreatest D₁ m₁ ∧ IsGreatest D₂ m₂ ∧ m₁ < m₂

theorem er_Iic_Iic (d₁ d₂ : D) : er (Set.Iic d₁) (Set.Iic d₂) ↔ d₁ < d₂ := by
  refine ⟨fun ⟨_, _, h₁, h₂, h⟩ => ?_,
    fun h => ⟨_, _, isGreatest_Iic, isGreatest_Iic, h⟩⟩
  rwa [h₁.unique isGreatest_Iic, h₂.unique isGreatest_Iic] at h

/-- With unique witnesses, `er` is the direct comparison of measures ((7′), (9′)). -/
theorem er_Iic_iff_comparativeSem (μ : Entity → D) (a b : Entity) :
    er (Set.Iic (μ b)) (Set.Iic (μ a)) ↔ comparativeSem μ a b .positive :=
  er_Iic_Iic _ _

/-- A subcomparative compares the maxima of degree sets on two dimensions (10′). -/
theorem er_Iic_iff_subcomparative (μ ν : Entity → D) (a b : Entity) :
    er (Set.Iic (ν b)) (Set.Iic (μ a)) ↔ subcomparative μ ν a b :=
  er_Iic_Iic _ _

/-! ### The contextual analysis -/

/-- The positive form at a contextual standard: `pos μ c x` holds iff `x` is `d`-A for some
`d > c` (20). -/
def pos (μ : Entity → D) (c : D) (x : Entity) : Prop :=
  ∃ d, d ≤ μ x ∧ c < d

theorem pos_iff_lt (μ : Entity → D) (c : D) (x : Entity) : pos μ c x ↔ c < μ x :=
  ⟨fun ⟨_, hd, hc⟩ => hc.trans_le hd, fun h => ⟨_, le_rfl, h⟩⟩

/-- The positive form is the point-standard predication `Comparison.gt.over`. -/
theorem pos_iff_mem_over (μ : Entity → D) (c : D) (x : Entity) :
    pos μ c x ↔ x ∈ Comparison.gt.over μ c := by
  simp only [pos_iff_lt, Comparison.mem_over, Comparison.rel, gt_iff_lt]

/-- The contextual comparative: `er₂ c S` holds iff `max S > c` (23). -/
def er₂ (c : D) (S : Set D) : Prop :=
  ∃ m, IsGreatest S m ∧ c < m

/-- If `S` has a greatest element, then `er₂ c S` holds iff some `d ∈ S` exceeds `c`
(footnote 7). -/
theorem er₂_iff_of_isGreatest {S : Set D} {m : D} (h : IsGreatest S m) (c : D) :
    er₂ c S ↔ ∃ d ∈ S, c < d :=
  ⟨fun ⟨_, h', hc⟩ => ⟨_, h'.1, hc⟩,
    fun ⟨_, hd, hc⟩ => ⟨m, h, hc.trans_le (h.2 hd)⟩⟩

/-- On an adjective's own degree set the contextual comparative and the positive form
coincide ((24d), (21b)). -/
theorem er₂_Iic_iff (μ : Entity → D) (c : D) (x : Entity) :
    er₂ c (Set.Iic (μ x)) ↔ pos μ c x :=
  (er₂_iff_of_isGreatest isGreatest_Iic c).trans Iff.rfl

/-- A context setter supplying `y` sets `c := μ y`, and the positive form becomes the
comparison with `y` ((21), (25)). -/
theorem pos_comparedTo (μ : Entity → D) (x y : Entity) :
    pos μ (μ y) x ↔ comparativeSem μ x y .positive :=
  pos_iff_lt μ (μ y) x

/-! ### Yori-clauses denote individuals -/

/-- `theC C P` is the unique `P`-individual of the contextual domain `C` (54). -/
noncomputable def theC (C : Set Entity) (P : Entity → Prop) : Option Entity :=
  russellIota fun x => x ∈ C ∧ P x

theorem theC_eq_some_iff (C : Set Entity) (P : Entity → Prop) (y : Entity) :
    theC C P = some y ↔ (y ∈ C ∧ P y) ∧ ∀ z, z ∈ C → P z → z = y := by
  simp only [theC, russellIota_eq_some_iff, and_imp]

/-- If `Y` is the maximal `P`-plurality, then the greatest `n` for which some `P`-plurality
has at least `n` members is the cardinality of `Y` (41a). -/
theorem isGreatest_card_of_isMaximal {Atom : Type*} {P : Finset Atom → Prop}
    {Y : Finset Atom} (h : IsMaximal P Y) :
    IsGreatest {n | ∃ S, P S ∧ n ≤ S.card} Y.card :=
  ⟨⟨Y, h.1, le_rfl⟩, fun _ ⟨_, hS, hn⟩ => hn.trans (Finset.card_le_card (h.2 _ hS))⟩

/-! ### Subcomparatives -/

/-- An individual standard lies on the matrix dimension: the reading of the shelf–door
sentence with the door as standard differs from the subcomparative ((74), (79)). -/
theorem pos_ne_subcomparative :
    ∃ μ ν : Fin 2 → ℕ, subcomparative μ ν 0 1 ∧ ¬ pos μ (μ 1) 0 :=
  ⟨![2, 3], ![0, 1], by simp [subcomparative], by simp [pos_iff_lt]⟩

/-! ### Negative islands -/

/-- The *than*-clause degree set of a negated comparative: the degrees `d` such that nobody
bought a `d`-expensive book (11). -/
def nobodyDegrees (bought : Entity → Prop) (μ : Entity → D) : Set D :=
  {d | ∀ x, bought x → μ x < d}

theorem isUpperSet_nobodyDegrees (bought : Entity → Prop) (μ : Entity → D) :
    IsUpperSet (nobodyDegrees bought μ) :=
  fun _ _ h hd x hx => (hd x hx).trans_le h

/-- On a scale without a top, the negated *than*-clause has no greatest degree (12). -/
theorem not_isGreatest_nobodyDegrees [NoMaxOrder D] (bought : Entity → Prop)
    (μ : Entity → D) : ¬ ∃ m, IsGreatest (nobodyDegrees bought μ) m :=
  fun ⟨_, hm⟩ => (isUpperSet_nobodyDegrees bought μ).not_bddAbove ⟨_, hm.1⟩ hm.bddAbove

/-- `er` over a negated *than*-clause never holds: the negative island ((11), (87a)). -/
theorem not_er_nobodyDegrees [NoMaxOrder D] (bought : Entity → Prop) (μ : Entity → D)
    (S : Set D) : ¬ er (nobodyDegrees bought μ) S :=
  fun ⟨m, _, hm, _, _⟩ => not_isGreatest_nobodyDegrees bought μ ⟨m, hm⟩

/-- A *yori*-clause built on the unbought individuals denotes the unique one of them, so the
construction entails that some book in the domain went unbought ((86), (88c)). -/
theorem yori_negative_entails_unbought (C : Set Entity) (bought : Entity → Prop)
    (μ : Entity → D) (x : Entity)
    (h : ∃ y, theC C (fun z => ¬ bought z) = some y ∧ pos μ (μ y) x) :
    ∃ y ∈ C, ¬ bought y :=
  let ⟨y, hy, _⟩ := h; ⟨y, ((theC_eq_some_iff _ _ _).1 hy).1⟩

/-- The *than*-clause degree set of a universally quantified comparative: the degrees `d`
such that every boy read a `d`-long book (95a). -/
def everyoneDegrees {Agent : Type*} (read : Agent → Entity → Prop) (μ : Entity → D) :
    Set D :=
  {d | ∀ b, ∃ x, read b x ∧ d ≤ μ x}

/-- The universally quantified comparative can hold when no book was read by every boy, so it
lacks the uniqueness presupposition of the *yori*-clause ((94), (95)). -/
theorem er_everyoneDegrees_without_shared_book :
    ∃ (read : Fin 2 → Fin 3 → Prop) (μ : Fin 3 → ℕ),
      er (everyoneDegrees read μ) (Set.Iic (μ 2)) ∧ ¬ ∃ x, ∀ b, read b x := by
  refine ⟨fun b x => x.val = b.val, ![1, 1, 2],
    ⟨1, _, ⟨fun b => ?_, fun d hd => ?_⟩, isGreatest_Iic, by simp⟩, ?_⟩
  · fin_cases b
    · exact ⟨0, rfl, by simp⟩
    · exact ⟨1, rfl, by simp⟩
  · obtain ⟨x, hx, hle⟩ := hd 0
    obtain rfl : x = 0 := Fin.ext (by simpa using hx)
    simpa using hle
  · rintro ⟨x, hx⟩
    have h0 := hx 0
    have h1 := hx 1
    simp at h0 h1
    omega

/-! ### The main clause and scope -/

/-- The comparative on adjective meanings: `erJ c P x` holds iff the greatest degree to which
`x` is `P` exceeds `c` (133). -/
def erJ (c : D) (P : D → Entity → Prop) (x : Entity) : Prop :=
  er₂ c {d | P d x}

/-- For a monotone adjective, `erJ` and the positive form have the same truth conditions
(footnote 15). -/
theorem erJ_iff_pos (μ : Entity → D) (c : D) (x : Entity) :
    erJ c (fun d x => d ≤ μ x) x ↔ pos μ c x :=
  er₂_Iic_iff μ c x

/-- The degree predicate abstracted across `need`: the degrees reached in every acceptable
world (136c). -/
def needDegrees {W : Type*} (acc : Set W) (μ : W → D) : Set D :=
  {d | ∀ w ∈ acc, d ≤ μ w}

/-- The wide-scope reading: the greatest degree in `needDegrees` is the target `s` (136b). -/
def wideScope {W : Type*} (acc : Set W) (μ : W → D) (s : D) : Prop :=
  IsGreatest (needDegrees acc μ) s

/-- The in-situ reading, which `erJ` with a differential yields: in every acceptable world
the greatest degree is the target `s`. -/
def inSitu {W : Type*} (acc : Set W) (μ : W → D) (s : D) : Prop :=
  ∀ w ∈ acc, IsGreatest (Set.Iic (μ w)) s

theorem inSitu_iff {W : Type*} (acc : Set W) (μ : W → D) (s : D) :
    inSitu acc μ s ↔ ∀ w ∈ acc, μ w = s :=
  forall₂_congr fun _ _ =>
    ⟨fun h => (h.unique isGreatest_Iic).symm, fun h => by rw [h]; exact isGreatest_Iic⟩

theorem wideScope_of_inSitu {W : Type*} {acc : Set W} {μ : W → D} {s : D}
    (hne : acc.Nonempty) (h : inSitu acc μ s) : wideScope acc μ s := by
  rw [inSitu_iff] at h
  obtain ⟨w₀, hw₀⟩ := hne
  exact ⟨fun w hw => (h w hw).ge, fun d hd => (hd w₀ hw₀).trans_eq (h w₀ hw₀)⟩

/-- In a model where the acceptable versions of a 10-page draft run to 15 or 16 pages, the
wide-scope reading of "needs to be exactly 5 pages longer" holds and the in-situ reading
fails ((136), (138)). -/
theorem exists_wideScope_not_inSitu :
    ∃ (acc : Set (Fin 2)) (μ : Fin 2 → ℕ),
      wideScope acc μ (10 + 5) ∧ ¬ inSitu acc μ (10 + 5) := by
  refine ⟨Set.univ, ![15, 16], ⟨fun w _ => ?_, fun d hd => ?_⟩, ?_⟩
  · fin_cases w <;> simp
  · simpa using hd 0 (Set.mem_univ _)
  · rw [inSitu_iff]
    intro h
    simpa using h 1 (Set.mem_univ _)

end BeckOdaSugisaki2004
