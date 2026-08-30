import Linglib.Semantics.Focus.Interpretation
import Mathlib.Data.Set.Lattice
import Linglib.Data.Examples.Ahn2015

/-!
# The semantics of additive *either*

Ahn takes *too* and additive *either* to be two-place predicates over the host proposition and a
silent propositional anaphor `q`, presupposed to be a distinct focus alternative of the host, and
lets them assert a conjunction and a disjunction respectively (`too`, `either`, `Antecedent`).
Negation then scopes over the assertion: *Mary didn't buy them too* asserts `¬(q ∧ p)`, which
with the discourse-given `q` is `¬p` (`not_too_of_antecedent`), while *John didn't leave either*
asserts `¬(q ∨ p)`, so both the host and the antecedent are denied (`either_compl`). Since the
additive component is asserted rather than presupposed, denying it with an anaphoric *as well*
is consistent where denying an existential is not (`abrusan_contrast`).

The distribution of *either* follows from the disjunction under the exhaustification account of
polarity items: the alternatives of a disjunction are the disjuncts and their conjunction, and
the naive exhaustifier `exhO` negates every alternative the prejacent fails to entail. In a
positive context that leaves the disjunction without either disjunct, a contradiction
(`either_positive_contradiction`); under negation the negated disjunction entails every
alternative, so exhaustification is vacuous (`either_negative_vacuous`), and likewise in any
downward-entailing context (`either_vacuous_in_de`), which is why the account overgenerates to
all such contexts and leaves the strong-NPI restriction to negation open. *Too* entails all of
its alternatives, so it is exhaustified vacuously everywhere and is no polarity item
(`too_entails_alts`). The paper's judgments are its rows: *either* is acceptable exactly in a
negative host whose antecedent is not positive, and *too* fails only for want of an antecedent
(`either_iff_negative`, `too_any_polarity`).

## References

* [ahn-2015]
* [rullmann-2003]
* [heim-1992]
* [kripke-2009]
* [rooth-1992]
* [chierchia-2013]
* [sauerland-2004]
-/

namespace Ahn2015

open Data.Examples Focus.Interpretation

variable {World : Type*} (q p : Set World)

/-! ### Too and either -/

/-- The presupposition shared by *too* and *either*: the anaphor is a focus alternative of the
host distinct from it. -/
def Antecedent (C : PropFocusValue World) : Prop := q ∈ C ∧ q ≠ p

/-- `too q p = q ⊓ p`: the additive meaning is asserted as a conjunction with the anaphor. -/
abbrev too : Set World := q ⊓ p

/-- `either q p = q ⊔ p`: the disjunctive counterpart. -/
abbrev either : Set World := q ⊔ p

/-- Negation above *too* denies the conjunction. -/
theorem too_compl : (too q p)ᶜ = qᶜ ⊔ pᶜ := compl_inf

/-- With the antecedent settled true, negated *too* denies the host. -/
theorem not_too_of_antecedent {w : World} (hq : w ∈ q) : w ∈ (too q p)ᶜ ↔ w ∉ p := by
  simp [hq]

/-- Negation above *either* denies both the host and the antecedent. -/
theorem either_compl : (either q p)ᶜ = qᶜ ⊓ pᶜ := compl_sup

/-- Denying an existential the host entails is contradictory, denying the anaphoric conjunction
is not: it denies the antecedent. -/
theorem abrusan_contrast {e : Set World} (he : p ≤ e) :
    p ⊓ eᶜ = ⊥ ∧ p ⊓ (too q p)ᶜ = p ⊓ qᶜ := by
  refine ⟨?_, ?_⟩
  · exact le_bot_iff.1 (inf_le_inf_right _ he |>.trans (by rw [inf_compl_eq_bot]))
  · rw [too_compl, inf_sup_left, inf_compl_eq_bot, sup_bot_eq, inf_comm]

/-! ### Exhaustification -/

/-- The naive exhaustifier: the prejacent with every alternative it does not entail negated. -/
def exhO (alts : Set (Set World)) (φ : Set World) : Set World :=
  φ ⊓ ⨅ a ∈ {a ∈ alts | ¬ φ ≤ a}, aᶜ

theorem exhO_le_compl {alts : Set (Set World)} {φ a : Set World} (ha : a ∈ alts)
    (hna : ¬ φ ≤ a) : exhO alts φ ≤ aᶜ :=
  inf_le_right.trans (iInf₂_le a ⟨ha, hna⟩)

/-- When the prejacent entails every alternative, exhaustification is vacuous. -/
theorem exhO_eq_self {alts : Set (Set World)} {φ : Set World} (h : ∀ a ∈ alts, φ ≤ a) :
    exhO alts φ = φ := by
  have : {a ∈ alts | ¬ φ ≤ a} = ∅ := Set.eq_empty_of_forall_notMem fun a ⟨ha, hna⟩ => hna (h a ha)
  simp [exhO, this]

/-- The alternatives of a disjunction: the disjuncts and their conjunction. -/
def disjAlts : Set (Set World) := {q ⊔ p, q, p, q ⊓ p}

/-- *Too* entails every alternative of the conjunction, so exhaustification is vacuous. -/
theorem too_entails_alts : exhO {q ⊓ p, q, p, q ⊔ p} (too q p) = too q p :=
  exhO_eq_self fun a ha => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    exacts [le_rfl, inf_le_left, inf_le_right, inf_le_left.trans le_sup_left]

/-- In a positive context *either* is exhaustified to a contradiction, provided neither disjunct
is entailed by the disjunction. -/
theorem either_positive_contradiction (hq : ¬ either q p ≤ q) (hp : ¬ either q p ≤ p) :
    exhO (disjAlts q p) (either q p) = ⊥ := by
  refine le_bot_iff.1 ?_
  calc exhO (disjAlts q p) (either q p) ≤ either q p ⊓ qᶜ ⊓ pᶜ :=
        le_inf (le_inf inf_le_left (exhO_le_compl (by simp [disjAlts]) hq))
          (exhO_le_compl (by simp [disjAlts]) hp)
    _ = ⊥ := by rw [inf_assoc, ← compl_sup, inf_compl_eq_bot]

/-- Under negation the negated disjunction entails every negated alternative, so
exhaustification is vacuous. -/
theorem either_negative_vacuous :
    exhO ((disjAlts q p).image compl) (either q p)ᶜ = (either q p)ᶜ :=
  exhO_eq_self fun a ⟨b, hb, hba⟩ => by
    subst hba
    simp only [disjAlts, Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl | rfl | rfl
    exacts [le_rfl, compl_le_compl le_sup_left, compl_le_compl le_sup_right,
      compl_le_compl (inf_le_left.trans le_sup_left)]

/-- In any downward-entailing context the scalar alternative of the disjunction is entailed, so
exhaustification is vacuous there too: the account licenses *either* beyond negation. -/
theorem either_vacuous_in_de (C : Set World → Set World) (hDE : Antitone C) :
    C (either q p) ⊆ C (q ⊓ p) :=
  hDE (inf_le_left.trans le_sup_left)

/-! ### The data -/

/-- *Either* is acceptable exactly in a negative host whose antecedent is not positive. -/
theorem either_iff_negative :
    ∀ e ∈ Examples.all, e.feature? "particle" = some "either" →
      (e.judgment = .acceptable ↔
        e.feature? "polarity" = some "negative" ∧ e.feature? "antecedent" ≠ some "positive") := by
  decide

/-- *Too* occurs in both polarities; its infelicity needs a missing antecedent. -/
theorem too_any_polarity :
    ∀ e ∈ Examples.all, e.feature? "particle" = some "too" → e.judgment = .unacceptable →
      e.feature? "polarity" = some "positive" ∧ (e.context ≠ "") := by
  decide

end Ahn2015
