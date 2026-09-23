module

public import Linglib.Semantics.Exhaustification.Trivalent
public import Linglib.Semantics.Dynamic.Partial
public import Linglib.Data.Examples.WangDavidson2026
public import Mathlib.Data.Fintype.Prod

/-!
# Wang & Davidson (2026): Presupposition Filtering in Disjunction

This file formalizes [wang-davidson-2026]'s survey of what fully semantic implementations of
exclusive disjunction predict for presupposition projection. Under Strong Kleene an inclusive
disjunction is true when one disjunct is, whatever the other, so a true disjunct filters the
other's presupposition, whereas an exclusive disjunction is undefined whenever a disjunct is
(`Filters`, `not_filters_xor`). Bivalent exhaustification ([fox-2007]) strengthens a disjunction
to its exclusive reading (`exh_or`), so once the strengthened truth conditions feed the projection
computation three projection theories agree that an exclusive disjunction projects uniformly:
Strong Kleene ([mayr-romoli-2016a]); [george-2008]'s algorithm, rendered as `george` over any
classical connective, which agrees with Strong Kleene on inclusive and exclusive disjunction
(`george_or`, `george_xor`) while filtering conjunction only from left to right; and dynamic
semantics, where each of the eight context change potentials that [rothschild-2011]'s
restrictions allow for exclusive disjunction is admitted only by a context satisfying both
presuppositions (`xorCCPs_admits`). The trivalent exhaustifiers of [spector-sudo-2017] split:
weak-negation EXH¹ is undefined exactly where its prejacent is, so it leaves projection alone,
while strong-negation EXH² is undefined wherever an innocently excludable alternative is, and
for a disjunction the conjunction alternative's presupposition together with the disjunction's
is both disjuncts' (`sup_inf_ne_indet_iff`). The theories predicting that more exclusive readings
mean less filtering are the paper's Type A; the paper's Mandarin experiment on *huozhe* finds no
such effect.

## Implementation notes

The exhaustification identity is checked on the four valuations of two atoms, the free model of
a propositional identity. George's algorithm is stated as the paper renders it, on the set of
classical values a trivalent argument leaves open. The experiment's ratings are not formalized;
its stimuli are in `Data.Examples.WangDavidson2026`.

## References

* [wang-davidson-2026]
* [fox-2007]
* [george-2008]
* [kalomoiros-schwarz-2024]
* [mayr-romoli-2016a]
* [rothschild-2011]
* [spector-sudo-2017]
-/

@[expose] public section

namespace WangDavidson2026

open Exhaustification Exhaustification.Trivalent Presupposition DynamicSemantics CCP.Partial

/-! ### Filtering by a trivalent connective -/

/-- A trivalent connective filters from left to right when a defined left argument can make the
whole defined with an undefined right argument. -/
def FiltersLR (f : Trivalent → Trivalent → Trivalent) : Prop := ∃ a, f a .indet ≠ .indet

/-- Filtering from right to left. -/
def FiltersRL (f : Trivalent → Trivalent → Trivalent) : Prop := ∃ b, f .indet b ≠ .indet

/-- A connective filters when it does so in either direction. -/
def Filters (f : Trivalent → Trivalent → Trivalent) : Prop := FiltersLR f ∨ FiltersRL f

/-- Strong Kleene inclusive disjunction filters in both directions (Table 1). -/
theorem filtersLR_sup : FiltersLR (· ⊔ ·) := ⟨.true, by decide⟩

theorem filtersRL_sup : FiltersRL (· ⊔ ·) := ⟨.true, by decide⟩

/-- Strong Kleene exclusive disjunction never filters (Table 2). -/
theorem not_filters_xor : ¬ Filters Trivalent.xor := by
  rintro (⟨a, h⟩ | ⟨b, h⟩)
  · exact h (Trivalent.xor_indet_right a)
  · exact h (Trivalent.xor_indet_left b)

/-! ### Bivalent exhaustification yields exclusive disjunction -/

/-- The valuations of two atoms. -/
abbrev Val := Bool × Bool

/-- The alternatives of `p ∨ q`: `p`, `q` and `p ∧ q` (3a). -/
def orAlts : Finset (Finset Val) :=
  altsFromPreds [λ v => v.1 || v.2, Prod.fst, Prod.snd, λ v => v.1 && v.2]

/-- Only the conjunction is innocently excludable (3b). -/
theorem excluded_or :
    innocent.excluded orAlts (predToFinset λ v : Val => v.1 || v.2)
      = {predToFinset λ v : Val => v.1 && v.2} := by
  decide

/-- Bivalent exhaustification of `p ∨ q` is `p xor q` (3c). -/
theorem exh_or :
    innocent.exh orAlts (predToFinset λ v : Val => v.1 || v.2)
      = predToFinset λ v : Val => v.1 ^^ v.2 := by
  decide

/-! ### George's algorithm -/

/-- The classical values a trivalent value leaves open. -/
def values : Trivalent → Finset Bool
  | .true => {true}
  | .false => {false}
  | .indet => Finset.univ

/-- [george-2008]'s algorithm for the trivalent table of a classical connective, as
[kalomoiros-schwarz-2024] render it: if the left argument settles the value, that is the value;
otherwise, if some value of the right argument could make the sentence true, the two arguments
settle the value or the sentence is undefined; otherwise it is undefined. -/
def george (f : Bool → Bool → Bool) (a b : Trivalent) : Trivalent :=
  if ∀ x ∈ values a, ∀ y, f x y then .true
  else if ∀ x ∈ values a, ∀ y, f x y = false then .false
  else if ∃ y, ∀ x ∈ values a, f x y then
    if ∀ x ∈ values a, ∀ y ∈ values b, f x y then .true
    else if ∀ x ∈ values a, ∀ y ∈ values b, f x y = false then .false
    else .indet
  else .indet

/-- On inclusive disjunction George's algorithm is Strong Kleene. -/
theorem george_or : george (· || ·) = (· ⊔ ·) := by
  funext a b; revert a b; decide

/-- On exclusive disjunction George's algorithm is Strong Kleene too. -/
theorem george_xor : george (· ^^ ·) = Trivalent.xor := by
  funext a b; revert a b; decide

/-- George's algorithm filters conjunction from left to right only. -/
theorem filtersLR_george_and : FiltersLR (george (· && ·)) := ⟨.false, by decide⟩

theorem not_filtersRL_george_and : ¬ FiltersRL (george (· && ·)) := by
  rintro ⟨b, h⟩; revert b; decide

theorem not_filters_george_xor : ¬ Filters (george (· ^^ ·)) := george_xor ▸ not_filters_xor

/-! ### Dynamic semantics -/

section Dynamic

variable {W : Type*} (α β : PartialProp W) {s : Set W}

/-- Update with a proposition or with its negation. -/
def lit : Bool → PartialProp W → CCP.Partial W
  | true, p => ofPartialProp p
  | false, p => CCP.Partial.neg (ofPartialProp p)

/-- The context `C[p][q]`, for `p` and `q` propositions or their negations. -/
def chain (b₁ : Bool) (p : PartialProp W) (b₂ : Bool) (q : PartialProp W) : CCP.Partial W :=
  seq (lit b₁ p) (lit b₂ q)

/-- The union of two updates, defined when both are. -/
def union (φ ψ : CCP.Partial W) : CCP.Partial W :=
  λ s => ⟨(φ s).Dom ∧ (ψ s).Dom, λ h => (φ s).get h.1 ∪ (ψ s).get h.2⟩

/-- The context minus two updates, defined when both are. -/
def diff (φ ψ : CCP.Partial W) : CCP.Partial W :=
  λ s => ⟨(φ s).Dom ∧ (ψ s).Dom, λ h => (s \ (φ s).get h.1) \ (ψ s).get h.2⟩

/-- The eight context change potentials for `α xor β` (Table 3). -/
def xorCCPs : List (CCP.Partial W) :=
  [union (chain true α false β) (chain true β false α),
   union (chain false α true β) (chain false β true α),
   union (chain true α false β) (chain false α true β),
   union (chain true β false α) (chain false β true α),
   diff (chain true α true β) (chain false β false α),
   diff (chain false α false β) (chain true β true α),
   diff (chain true α true β) (chain false α false β),
   diff (chain true β true α) (chain false β false α)]

/-- A presupposition satisfied on `C[α]` and on `C[¬α]` is satisfied on `C`. -/
theorem presupSatisfied_of_split (h₁ : Context.presupSatisfied {w ∈ s | α.assertion w} β)
    (h₂ : Context.presupSatisfied (s \ {w ∈ s | α.assertion w}) β) :
    Context.presupSatisfied s β := λ w hw => by
  by_cases ha : α.assertion w
  · exact h₁ ⟨hw, ha⟩
  · exact h₂ ⟨hw, λ h => ha h.2⟩

/-- Every context change potential for exclusive disjunction is admitted only by a context
satisfying both presuppositions: no filtering. -/
theorem xorCCPs_admits :
    ∀ u ∈ xorCCPs α β, u.admits s →
      Context.presupSatisfied s α ∧ Context.presupSatisfied s β := by
  simp only [xorCCPs, List.mem_cons, List.mem_nil_iff, or_false]
  rintro u (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
  · exact ⟨h₁, h₃⟩
  · exact ⟨h₁, h₃⟩
  · exact ⟨h₁, presupSatisfied_of_split α β h₂ h₄⟩
  · exact ⟨presupSatisfied_of_split β α h₂ h₄, h₁⟩
  · exact ⟨h₁, h₃⟩
  · exact ⟨h₁, h₃⟩
  · exact ⟨h₁, presupSatisfied_of_split α β h₂ h₄⟩
  · exact ⟨presupSatisfied_of_split β α h₂ h₄, h₁⟩

/-- Inclusive dynamic disjunction, by contrast, filters: a context can admit `α ∨ β` without
satisfying `β`'s presupposition. -/
theorem exists_disj_admits_not_presupSatisfied :
    ∃ (α β : PartialProp Bool), (disj (ofPartialProp α) (ofPartialProp β)).admits Set.univ ∧
      ¬ Context.presupSatisfied Set.univ β := by
  refine ⟨{ presup := λ _ => True, assertion := (· = true) },
    { presup := (· = false), assertion := λ _ => True }, ⟨λ _ _ => trivial, ?_⟩, ?_⟩
  · rintro (_ | _) hw
    · rfl
    · exact absurd ⟨trivial, rfl⟩ hw.2
  · exact λ h => Bool.noConfusion (h (Set.mem_univ true))

end Dynamic

/-! ### Trivalent exhaustification -/

/-- The presupposition of `α ∨ β` together with that of `α ∧ β` is that of both disjuncts
under Strong Kleene (8), so EXH², which imports the conjunction alternative's presupposition,
makes an exhaustified disjunction project uniformly. -/
theorem sup_inf_ne_indet_iff (a b : Trivalent) :
    (a ⊔ b ≠ .indet ∧ a ⊓ b ≠ .indet) ↔ a ≠ .indet ∧ b ≠ .indet := by
  revert a b; decide

/-- A bathroom disjunction on the valuations of two atoms: `bathLeft` is always defined and
`bathRight` presupposes its negation. -/
def bathLeft : Trivalent.Prop3 Val := λ v => .ofBool v.1

def bathRight : Trivalent.Prop3 Val := λ v => if v.1 then .indet else .ofBool v.2

/-- The alternatives of the bathroom disjunction. -/
def bathAlts : List (Trivalent.Prop3 Val) :=
  [bathLeft, bathRight, λ v => bathLeft v ⊓ bathRight v]

/-- The inclusive bathroom disjunction. -/
def bathOr : Trivalent.Prop3 Val := λ v => bathLeft v ⊔ bathRight v

/-- EXH¹ keeps the filtering: where the left disjunct is true and the right undefined, the
exhaustified disjunction is true. -/
theorem exh1_bathOr : exh1 bathAlts bathOr (true, false) = Trivalent.true := by decide

/-- EXH² undoes it: the undefined conjunction alternative makes the exhaustified disjunction
undefined there. -/
theorem exh2_bathOr : exh2 bathAlts bathOr (true, false) = Trivalent.indet := by decide

end WangDavidson2026
