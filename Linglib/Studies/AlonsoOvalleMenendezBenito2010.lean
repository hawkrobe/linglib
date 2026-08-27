import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Finset.Powerset
import Linglib.Semantics.Presupposition.Defs
import Linglib.Data.Examples.AlonsoOvalleMenendezBenito2010

/-!
# Alonso-Ovalle & Menéndez-Benito (2010): modal indefinites

Spanish *algún* conveys that at least two individuals in its domain are possibilities — the
Modal Variation component (18), `ModalVariation` — where German *irgendein* conveys the
stronger Free Choice component (13c), `FreeChoice`: in the hide-and-seek scenario (15) Pedro
can use *algún* with the bathroom ruled out (`hideAndSeek`), and under uniqueness Free Choice
entails Modal Variation but not conversely (`modalVariation_of_freeChoice`). The component is
a conversational implicature: as a presupposition it would make the negated (36) contradictory
(`not_modalVariation_of_nec_empty`), and it is cancellable (42), absent under downward
entailing operators (43)–(44), and reinforceable (45d).

The paper derives it from an anti-singleton constraint (53)–(54) on the subset selection
function *algún* takes (`algún`), which excludes the singleton restrictors of (47)/(49)
(`algún_not_of_singleton`). The competitors (58) are the singleton subdomains; their falsity
under a necessity modal (59) gives Modal Variation (`modalVariation_of_falseCompetitors`), and
under a possibility modal, where some competitor must be true (`some_competitor_of_poss`), the
anti-exhaustivity implicatures (67)–(68) do (`antiSingleton_modalVariation`). A domain widener
competes with every proper subdomain (70), and the same reasoning yields Free Choice
(`widening_freeChoice`). Without uniqueness the blocked exhaustivity inference (76) and the
plural competitor (77) give ignorance of number (`numberIgnorance_of_competition`), which
uniqueness makes unavailable (`not_numberIgnorance_of_uniqueness`) — the two parameters of
Table 1. The scenario verdicts (24)–(30) are checked in `rows_agree`.

## References

* [alonso-ovalle-menendez-benito-2010]
* [kratzer-shimoyama-2002]
* [chierchia-2006]
* [von-fintel-2000-whatever]
* [dayal-1997]
* [schwarzschild-2002]
* [potts-2005]
* [zimmermann-2000]
* [jayez-tovena-2006]
-/

namespace AlonsoOvalleMenendezBenito2010

open Presupposition Data.Examples

variable {E W : Type*} [DecidableEq E]

/-! ### Subset selection functions (§4.1) -/

/-- A singleton subset selection function (52). -/
def IsSingleton (f : Finset E → Finset E) : Prop := ∀ P, (f P).card = 1

/-- An anti-singleton subset selection function (53). -/
def IsAntiSingleton (f : Finset E → Finset E) : Prop := ∀ P, (f P).card ≠ 1

/-- *un* (50): existential quantification over the subdomain `f` selects from `P`. -/
def un (f : Finset E → Finset E) (P : Finset E) (Q : W → E → Prop) : PartialProp W :=
  .ofProp fun w => ∃ x ∈ f P, Q w x

/-- *algún* (54): the assertion of *un*, defined only for anti-singleton `f`. -/
def algún (f : Finset E → Finset E) (P : Finset E) (Q : W → E → Prop) : PartialProp W where
  presup _ := IsAntiSingleton f
  assertion w := ∃ x ∈ f P, Q w x

omit [DecidableEq E] in
/-- (46)–(49): on a singleton restrictor an anti-singleton selection returns no domain, so
*algún*'s claim cannot be true where *un*'s can. -/
theorem algún_not_of_singleton {f : Finset E → Finset E} (hf : ∀ P, f P ⊆ P)
    {P : Finset E} (hP : P.card = 1) (Q : W → E → Prop) (w : W)
    (h : (algún f P Q).presup w) : ¬ (algún f P Q).assertion w := by
  have : f P = ∅ := Finset.card_eq_zero.1 <|
    Nat.lt_one_iff.1 <| lt_of_le_of_ne (hP ▸ Finset.card_le_card (hf P)) (h P)
  simp [algún, this]

/-! ### Modal Variation and Free Choice (§2) -/

variable (A : Finset W) (D : Finset E) (Q : W → E → Prop) [∀ w, DecidablePred (Q w)]

/-- The witnesses of the existential claim at `w`. -/
def witnesses (w : W) : Finset E := D.filter (Q w ·)

/-- The Modal Variation component (18): the witnesses vary across the accessible worlds. -/
def ModalVariation : Prop := ∃ w' ∈ A, ∃ w'' ∈ A, witnesses D Q w' ≠ witnesses D Q w''

/-- The Free Choice component (13c): every member of the domain is a witness somewhere. -/
def FreeChoice : Prop := ∀ x ∈ D, ∃ w ∈ A, Q w x

/-- Uniqueness: at most one witness in each accessible world. -/
def Uniqueness : Prop := ∀ w ∈ A, (witnesses D Q w).card ≤ 1

omit [DecidableEq E] in
/-- ◇ over the accessible worlds. -/
def poss (p : W → Prop) : Prop := ∃ w ∈ A, p w

omit [DecidableEq E] in
/-- □ over the accessible worlds; the covert ASSERT (20) when `A` is the speaker's
epistemic alternatives. -/
def nec (p : W → Prop) : Prop := ∀ w ∈ A, p w

omit [DecidableEq E] in
/-- The existential claim over the subdomain `S` (58): some member of `S` is a witness. -/
def claim (S : Finset E) (w : W) : Prop := ∃ x ∈ S, Q w x

instance [DecidableEq W] : Decidable (ModalVariation A D Q) :=
  inferInstanceAs (Decidable (∃ w' ∈ A, ∃ w'' ∈ A, _ ≠ _))

instance : Decidable (FreeChoice A D Q) := inferInstanceAs (Decidable (∀ x ∈ D, ∃ w ∈ A, _))

instance (p : W → Prop) [DecidablePred p] : Decidable (poss A p) :=
  inferInstanceAs (Decidable (∃ w ∈ A, _))

instance (p : W → Prop) [DecidablePred p] : Decidable (nec A p) :=
  inferInstanceAs (Decidable (∀ w ∈ A, _))

instance (S : Finset E) (w : W) : Decidable (claim Q S w) :=
  inferInstanceAs (Decidable (∃ x ∈ S, _))

omit [DecidableEq E] in
theorem claim_iff_witnesses_nonempty (w : W) : claim Q D w ↔ (witnesses D Q w).Nonempty := by
  simp [claim, witnesses, Finset.Nonempty]

omit [DecidableEq E] in
/-- Two distinct possibilities give Modal Variation under uniqueness. -/
theorem modalVariation_of_two (hU : Uniqueness A D Q) {a b : E} (ha : a ∈ D) (hb : b ∈ D)
    (hab : a ≠ b) (pa : poss A (Q · a)) (pb : poss A (Q · b)) : ModalVariation A D Q := by
  obtain ⟨w', hw', hqa⟩ := pa
  obtain ⟨w'', hw'', hqb⟩ := pb
  refine ⟨w', hw', w'', hw'', fun h => ?_⟩
  have hb' : b ∈ witnesses D Q w' := h ▸ Finset.mem_filter.2 ⟨hb, hqb⟩
  have := hU w' hw'
  rw [Finset.card_le_one] at this
  exact hab (this a (Finset.mem_filter.2 ⟨ha, hqa⟩) b hb')

omit [DecidableEq E] in
/-- Under uniqueness, Free Choice on a domain with two members entails Modal Variation. -/
theorem modalVariation_of_freeChoice (hU : Uniqueness A D Q) (hD : 1 < D.card)
    (h : FreeChoice A D Q) : ModalVariation A D Q :=
  let ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hD
  modalVariation_of_two A D Q hU ha hb hab (h a ha) (h b hb)

/-! ### Not a presupposition (§3.1) -/

omit [DecidableEq E] in
/-- (35)–(36): a Modal Variation presupposition projecting through negation contradicts the
assertion that no accessible world has a witness. -/
theorem not_modalVariation_of_nec_empty (h : nec A fun w => witnesses D Q w = ∅) :
    ¬ ModalVariation A D Q :=
  fun ⟨w', hw', w'', hw'', hne⟩ => hne ((h w' hw').trans (h w'' hw'').symm)

/-! ### Deriving the component (§4) -/

/-- The domain constraints of §4.4. -/
inductive DomainConstraint
  /-- The domain is as wide as it can be ([kratzer-shimoyama-2002]'s *irgendein*). -/
  | widening
  /-- The domain is not a singleton (*algún*). -/
  | antiSingleton
  deriving DecidableEq

/-- The pragmatic competitors of the claim over `D`: the singleton subdomains (58) for an
anti-singleton indefinite, every nonempty proper subdomain (70) for a domain widener. -/
def competitors : DomainConstraint → Finset E → Finset (Finset E)
  | .antiSingleton, D => D.image ({·})
  | .widening, D => D.powerset.filter fun S => S.Nonempty ∧ S ≠ D

/-- The anti-singleton competitors are among the widening competitors. -/
theorem competitors_antiSingleton_subset (hD : 1 < D.card) :
    competitors .antiSingleton D ⊆ competitors .widening D := by
  intro S hS
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hS
  refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.singleton_subset_iff.2 ha),
    Finset.singleton_nonempty a, fun h => ?_⟩
  simp [← h] at hD

/-- §4.2, (59): under a necessity modal, a true claim whose singleton competitors are all
false shows Modal Variation. -/
theorem modalVariation_of_falseCompetitors (hA : A.Nonempty) (h : nec A (claim Q D))
    (hc : ∀ S ∈ competitors .antiSingleton D, ¬ nec A (claim Q S)) : ModalVariation A D Q := by
  obtain ⟨w', hw'⟩ := hA
  obtain ⟨a, ha, hqa⟩ := h w' hw'
  have := hc {a} (Finset.mem_image_of_mem _ ha)
  simp only [nec, claim, Finset.mem_singleton, exists_eq_left, not_forall] at this
  obtain ⟨w'', hw'', hna⟩ := this
  exact ⟨w', hw', w'', hw'', fun h =>
    hna (Finset.mem_filter.1 (h ▸ Finset.mem_filter.2 ⟨ha, hqa⟩ : a ∈ witnesses D Q w'')).2⟩

omit [∀ w, DecidablePred (Q w)] in
/-- (60)–(61): under a possibility modal the claim entails one of its singleton competitors,
so they cannot all be false. -/
theorem some_competitor_of_poss (h : poss A (claim Q D)) :
    ∃ S ∈ competitors .antiSingleton D, poss A (claim Q S) :=
  let ⟨w, hw, a, ha, hqa⟩ := h
  ⟨{a}, Finset.mem_image_of_mem _ ha, w, hw, a, Finset.mem_singleton_self a, hqa⟩

/-- The anti-exhaustivity implicature (67) for the competitor `S`: if `S` is possible, so is
the rest of the domain. -/
def AntiExhaustivity (S : Finset E) : Prop := poss A (claim Q S) → poss A (claim Q (D \ S))

instance (S : Finset E) : Decidable (AntiExhaustivity A D Q S) :=
  inferInstanceAs (Decidable (_ → _))

omit [∀ w, DecidablePred (Q w)] in
/-- §4.3, (68): the anti-exhaustivity implicatures of the singleton competitors make at
least two individuals possibilities. -/
theorem two_of_antiSingleton (h : poss A (claim Q D))
    (hs : ∀ S ∈ competitors .antiSingleton D, AntiExhaustivity A D Q S) :
    ∃ a ∈ D, ∃ b ∈ D, a ≠ b ∧ poss A (Q · a) ∧ poss A (Q · b) := by
  obtain ⟨w, hw, a, ha, hqa⟩ := h
  obtain ⟨w', hw', b, hb, hqb⟩ :=
    hs {a} (Finset.mem_image_of_mem _ ha) ⟨w, hw, a, Finset.mem_singleton_self a, hqa⟩
  obtain ⟨hbD, hba⟩ := Finset.mem_sdiff.1 hb
  exact ⟨a, ha, b, hbD, fun h => hba (h ▸ Finset.mem_singleton_self a), ⟨w, hw, hqa⟩,
    ⟨w', hw', hqb⟩⟩

/-- Under uniqueness the anti-singleton derivation yields Modal Variation. -/
theorem antiSingleton_modalVariation (hU : Uniqueness A D Q) (h : poss A (claim Q D))
    (hs : ∀ S ∈ competitors .antiSingleton D, AntiExhaustivity A D Q S) :
    ModalVariation A D Q :=
  let ⟨_, ha, _, hb, hab, pa, pb⟩ := two_of_antiSingleton A D Q h hs
  modalVariation_of_two A D Q hU ha hb hab pa pb

/-- §4.4, (70)–(72): the anti-exhaustivity implicatures of every proper subdomain yield Free
Choice. -/
theorem widening_freeChoice (h : poss A (claim Q D))
    (hs : ∀ S ∈ competitors .widening D, AntiExhaustivity A D Q S) : FreeChoice A D Q := by
  intro a ha
  by_contra hna
  obtain ⟨w, hw, x, hx, hqx⟩ := h
  have hxa : x ≠ a := fun h => hna ⟨w, hw, h ▸ hqx⟩
  have hS : D.erase a ∈ competitors .widening D := by
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.erase_subset a D),
      ⟨x, Finset.mem_erase.2 ⟨hxa, hx⟩⟩, fun h => ?_⟩
    exact Finset.notMem_erase a D (by rw [h]; exact ha)
  obtain ⟨w', hw', y, hy, hqy⟩ := hs _ hS ⟨w, hw, x, Finset.mem_erase.2 ⟨hxa, hx⟩, hqx⟩
  obtain ⟨-, hy'⟩ := Finset.mem_sdiff.1 hy
  have : y = a := by
    by_contra hya
    exact hy' (Finset.mem_erase.2 ⟨hya, (Finset.mem_sdiff.1 hy).1⟩)
  exact hna ⟨w', hw', this ▸ hqy⟩

/-! ### Non-uniqueness (§5) -/

/-- Ignorance with respect to number: the number of witnesses varies across the accessible
worlds. -/
def NumberIgnorance : Prop :=
  ∃ w' ∈ A, ∃ w'' ∈ A, (witnesses D Q w').card ≠ (witnesses D Q w'').card

omit [DecidableEq E] in
theorem modalVariation_of_numberIgnorance (h : NumberIgnorance A D Q) :
    ModalVariation A D Q :=
  let ⟨w', hw', w'', hw'', hne⟩ := h
  ⟨w', hw', w'', hw'', fun h => hne (h ▸ rfl)⟩

omit [DecidableEq E] in
/-- (76)–(78): with the exhaustivity inference of a singleton domain blocked and the plural
competitor (77) unassertable, a true claim conveys ignorance of number. -/
theorem numberIgnorance_of_competition (hc : nec A (claim Q D))
    (h₁ : ¬ nec A fun w => (witnesses D Q w).card = 1)
    (h₂ : ¬ nec A fun w => 2 ≤ (witnesses D Q w).card) : NumberIgnorance A D Q := by
  simp only [nec, not_forall] at h₁ h₂
  obtain ⟨w', hw', h₁⟩ := h₁
  obtain ⟨w'', hw'', h₂⟩ := h₂
  refine ⟨w', hw', w'', hw'', fun h => ?_⟩
  have := Finset.card_pos.2 ((claim_iff_witnesses_nonempty D Q w'').1 (hc w'' hw''))
  omega

omit [DecidableEq E] in
/-- Under uniqueness a true claim fixes the number of witnesses at one in every accessible
world, so ignorance of number conflicts with the common ground. -/
theorem not_numberIgnorance_of_uniqueness (hU : Uniqueness A D Q) (h : nec A (claim Q D)) :
    ¬ NumberIgnorance A D Q := by
  rintro ⟨w', hw', w'', hw'', hne⟩
  have one : ∀ w ∈ A, (witnesses D Q w).card = 1 := fun w hw =>
    le_antisymm (hU w hw) (Finset.card_pos.2 ((claim_iff_witnesses_nonempty D Q w).1 (h w hw)))
  exact hne ((one w' hw').trans (one w'' hw'').symm)

/-! ### The scenarios -/

/-- The hiding places; the domain of *habitación de la casa* is the house. -/
inductive Room | bedroom | livingRoom | bathroom | kitchen | barn
  deriving DecidableEq, Fintype

/-- Worlds are Juan's hiding places. -/
def inRoom (w r : Room) : Prop := w = r

instance (w : Room) : DecidablePred (inRoom w) := fun r => inferInstanceAs (Decidable (w = r))

abbrev house : Finset Room := {.bedroom, .livingRoom, .bathroom, .kitchen}
/-- (15): the bathroom and the kitchen are ruled out. -/
abbrev pedro15 : Finset Room := {.bedroom, .livingRoom}
/-- (23): only the bathroom. -/
abbrev pedro23 : Finset Room := {.bathroom}
/-- (27): the other rooms or the barn. -/
abbrev pedro27 : Finset Room := {.bedroom, .livingRoom, .barn}

/-- The candidates of (29); worlds are the permitted hires. -/
inductive Candidate | phdA | phdB | noPhd
  deriving DecidableEq, Fintype

def hires (w c : Candidate) : Prop := w = c

instance (w : Candidate) : DecidablePred (hires w) := fun c => inferInstanceAs (Decidable (w = c))

abbrev applicants : Finset Candidate := Finset.univ
abbrev permitted : Finset Candidate := {.phdA, .phdB}

/-- In (15) Modal Variation holds without Free Choice; the singleton competitors are all
false (59b) and carry their anti-exhaustivity implicatures (68b), while the widening
competitor *bedroom or living room* (72) does not. -/
theorem hideAndSeek :
    ModalVariation pedro15 house inRoom ∧ ¬ FreeChoice pedro15 house inRoom ∧
      (∀ S ∈ competitors .antiSingleton house, ¬ nec pedro15 (claim inRoom S)) ∧
      (∀ S ∈ competitors .antiSingleton house, AntiExhaustivity pedro15 house inRoom S) ∧
      ¬ AntiExhaustivity pedro15 house inRoom {.bedroom, .livingRoom} := by decide

/-! ### The paper's verdicts -/

/-- The accessible worlds and domain a row's `scenario` feature names, as the Modal Variation
and Free Choice verdicts over them. -/
def scenario : String → Option (Prop × Prop)
  | "hideAndSeek15" => some (ModalVariation pedro15 house inRoom, FreeChoice pedro15 house inRoom)
  | "oneRoom23" => some (ModalVariation pedro23 house inRoom, FreeChoice pedro23 house inRoom)
  | "barn27" => some (ModalVariation pedro27 house inRoom, FreeChoice pedro27 house inRoom)
  | "hiring29" =>
    some (ModalVariation permitted applicants hires, FreeChoice permitted applicants hires)
  | _ => none

/-- A row's predicted verdict: *algún* needs Modal Variation, *cualquiera* Free Choice, *un*
nothing. -/
def predicted (row : LinguisticExample) : Option Bool :=
  match row.feature? "scenario", row.feature? "determiner" with
  | some "hideAndSeek15", some d => verdictIn pedro15 house inRoom d
  | some "oneRoom23", some d => verdictIn pedro23 house inRoom d
  | some "barn27", some d => verdictIn pedro27 house inRoom d
  | some "hiring29", some d => verdictIn permitted applicants hires d
  | _, _ => none
where
  verdictIn {E W : Type} [DecidableEq E] [DecidableEq W] (A : Finset W) (D : Finset E)
      (Q : W → E → Prop) [∀ w, DecidablePred (Q w)] : String → Option Bool
    | "algún" => some (decide (ModalVariation A D Q))
    | "cualquiera" => some (decide (FreeChoice A D Q))
    | "un" => some true
    | _ => none

/-- A row's observed verdict: deviant or judged false, else fine. -/
def observed (row : LinguisticExample) : Bool :=
  row.judgment == .acceptable && row.feature? "verdict" != some "false"

/-- Every row in a modelled scenario carries the predicted verdict. -/
theorem rows_agree :
    ∀ row ∈ Examples.all, ∀ b, predicted row = some b → observed row = b := by decide +kernel

example : (Examples.all.filter fun row => (predicted row).isSome).length = 7 := by
  decide +kernel

end AlonsoOvalleMenendezBenito2010
