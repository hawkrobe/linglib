import Mathlib.Tactic.DeriveFintype
import Linglib.Semantics.Presupposition.Defs
import Linglib.Semantics.Exhaustification.DomainAlternatives
import Linglib.Data.Examples.AlonsoOvalleMenendezBenito2010

/-!
# Alonso-Ovalle & Menéndez-Benito (2010): modal indefinites

Spanish *algún* conveys that at least two individuals in its domain are possibilities — the
Modal Variation component (18), `ModalVariation` — where German *irgendein*
conveys the stronger Free Choice component (13c), `FreeChoice`: in the
hide-and-seek scenario (15) Pedro can use *algún* with the bathroom ruled out
(`hideAndSeek`), and under uniqueness Free Choice entails Modal Variation but not
conversely (`modalVariation_of_freeChoice`). The component is a conversational
implicature: as a presupposition it would make the negated (36) contradictory
(`not_modalVariation_of_box_empty`), and it is cancellable (42), absent under
downward entailing operators (43)–(44), and reinforceable (45d).

The paper derives it from an anti-singleton constraint (53)–(54) on the subset selection
function *algún* takes (`algún`), which excludes the singleton restrictors of (47)/(49)
(`algún_not_of_singleton`). The competitors (58) are the singleton subdomains; their
falsity under a necessity modal (59) gives Modal Variation (`modalVariation_of_box`),
and under a possibility modal, where some competitor must be true
(`exists_singleton_of_diamond`), the anti-exhaustivity implicatures (67)–(68) do
(`modalVariation_of_singletons`). A domain widener competes with every proper
subdomain (70), and the same reasoning yields Free Choice (`freeChoice_of_proper`).
Without uniqueness the blocked exhaustivity inference (76) and the plural competitor (77)
give ignorance of number (`numberIgnorance_of_competition`), which uniqueness makes
unavailable (`not_numberIgnorance_of_uniqueness`) — the two parameters of Table 1. The
scenario verdicts (24)–(30) are checked in `rows_agree`.

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

open Presupposition Exhaustification ModalLogic Data.Examples

variable {E W : Type*}

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

/-- (46)–(49): on a singleton restrictor an anti-singleton selection returns no domain, so
*algún*'s claim cannot be true where *un*'s can. -/
theorem algún_not_of_singleton {f : Finset E → Finset E} (hf : ∀ P, f P ⊆ P)
    {P : Finset E} (hP : P.card = 1) (Q : W → E → Prop) (w : W)
    (h : (algún f P Q).presup w) : ¬ (algún f P Q).assertion w := by
  have : f P = ∅ := Finset.card_eq_zero.1 <|
    Nat.lt_one_iff.1 <| lt_of_le_of_ne (hP ▸ Finset.card_le_card (hf P)) (h P)
  simp [algún, this]

/-! ### Non-uniqueness (§5) -/

variable (R : W → W → Prop) (w : W) (D : Finset E) (Q : W → E → Prop) [∀ v, DecidablePred (Q v)]

/-- Ignorance with respect to number: the number of witnesses varies across the accessible
worlds. -/
def NumberIgnorance : Prop :=
  ∃ v, R w v ∧ ∃ v', R w v' ∧ (witnesses D Q v).card ≠ (witnesses D Q v').card

theorem modalVariation_of_numberIgnorance (h : NumberIgnorance R w D Q) :
    ModalVariation R w D Q :=
  let ⟨v, hv, v', hv', hne⟩ := h
  ⟨v, hv, v', hv', fun h => hne (h ▸ rfl)⟩

/-- (76)–(78): with the exhaustivity inference of a singleton domain blocked and the plural
competitor (77) unassertable, a true claim conveys ignorance of number. -/
theorem numberIgnorance_of_competition (hc : □[R] (claim Q D) w)
    (h₁ : ¬ □[R] (fun v => (witnesses D Q v).card = 1) w)
    (h₂ : ¬ □[R] (fun v => 2 ≤ (witnesses D Q v).card) w) : NumberIgnorance R w D Q := by
  simp only [box, not_forall] at h₁ h₂
  obtain ⟨v, hv, h₁⟩ := h₁
  obtain ⟨v', hv', h₂⟩ := h₂
  refine ⟨v, hv, v', hv', fun h => ?_⟩
  have := Finset.card_pos.2 ((claim_iff_witnesses_nonempty D Q v').1 (hc v' hv'))
  omega

/-- Under uniqueness a true claim fixes the number of witnesses at one in every accessible
world, so ignorance of number conflicts with the common ground. -/
theorem not_numberIgnorance_of_uniqueness (hU : Uniqueness R w D Q) (h : □[R] (claim Q D) w) :
    ¬ NumberIgnorance R w D Q := by
  rintro ⟨v, hv, v', hv', hne⟩
  have one : ∀ v, R w v → (witnesses D Q v).card = 1 := fun v hv =>
    le_antisymm (hU v hv) (Finset.card_pos.2 ((claim_iff_witnesses_nonempty D Q v).1 (h v hv)))
  exact hne ((one v hv).trans (one v' hv').symm)

/-! ### The scenarios -/

/-- The hiding places; the domain of *habitación de la casa* is the house. -/
inductive Room | bedroom | livingRoom | bathroom | kitchen | barn
  deriving DecidableEq, Fintype

/-- Worlds are Juan's hiding places. -/
def inRoom (w r : Room) : Prop := w = r

instance (w : Room) : DecidablePred (inRoom w) := fun r => inferInstanceAs (Decidable (w = r))

abbrev house : Finset Room := {.bedroom, .livingRoom, .bathroom, .kitchen}

/-- Pedro's epistemic alternatives: what he takes to be possible, from any world. -/
def epist (A : Finset Room) : Room → Room → Prop := fun _ r => r ∈ A

instance (A : Finset Room) : DecidableRel (epist A) :=
  fun _ r => inferInstanceAs (Decidable (r ∈ A))

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

/-- The permitted hires, from any world. -/
def permitted : Candidate → Candidate → Prop := fun _ c => c ∈ ({.phdA, .phdB} : Finset Candidate)

instance : DecidableRel permitted := fun _ c => inferInstanceAs (Decidable (c ∈ _))

/-- In (15) Modal Variation holds without Free Choice; the singleton competitors are all
false (59b) and carry their anti-exhaustivity implicatures (68b), while the widening
competitor *bedroom or living room* (72) does not. -/
theorem hideAndSeek (w : Room) :
    ModalVariation (epist pedro15) w house inRoom ∧ ¬ FreeChoice (epist pedro15) w house inRoom ∧
      (∀ S ∈ subdomainAlternatives .singletons house, ¬ □[epist pedro15] (claim inRoom S) w) ∧
      (∀ S ∈ subdomainAlternatives .singletons house,
        AntiExhaustivity (epist pedro15) w house inRoom S) ∧
      ¬ AntiExhaustivity (epist pedro15) w house inRoom {.bedroom, .livingRoom} := by
  revert w; decide

/-! ### The paper's verdicts -/

/-- A row's predicted verdict: *algún* needs Modal Variation, *cualquiera* Free Choice, *un*
nothing. -/
def predicted (row : LinguisticExample) : Option Bool :=
  match row.feature? "scenario", row.feature? "determiner" with
  | some "hideAndSeek15", some d => verdictIn (epist pedro15) house inRoom d
  | some "oneRoom23", some d => verdictIn (epist pedro23) house inRoom d
  | some "barn27", some d => verdictIn (epist pedro27) house inRoom d
  | some "hiring29", some d => verdictIn permitted Finset.univ hires d
  | _, _ => none
where
  verdictIn {E W : Type} [DecidableEq E] [DecidableEq W] [Fintype W] (R : W → W → Prop)
      [DecidableRel R] (D : Finset E) (Q : W → E → Prop) [∀ v, DecidablePred (Q v)] :
      String → Option Bool
    | "algún" => some (decide (∀ w, ModalVariation R w D Q))
    | "cualquiera" => some (decide (∀ w, FreeChoice R w D Q))
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
