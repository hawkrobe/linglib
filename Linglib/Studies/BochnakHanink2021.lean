import Linglib.Fragments.Washo.Clause
import Linglib.Syntax.Category.Verb.Complement.Takes
import Linglib.Studies.Hanink2021
import Linglib.Syntax.Minimalist.ExtendedProjection.ClauseSpine

/-!
# Bochnak & Hanink (2021): Clausal embedding in Washo: complementation vs. modification

This file formalizes [bochnak-hanink-2021]'s two strategies of clausal embedding in Washo. A
presuppositional predicate selects its clause as a nominalized DP complement, and a
non-presuppositional predicate is intransitive and modified by a dependent-mood clause. The
split is read off the Fragment's frames: a predicate selects iff it has an internal-argument
frame (`Selects`), which holds iff it takes the nominalizer as a clause-typer
(`selects_iff_takes_ge`), and Table 2's clause size, a CP under D against a MoodP without C,
follows (`spine`). The nominalized complement is [hanink-2021]'s familiar DP restricted by the
FPROP type-shift (`complement`), so it denotes the individual whose content is the embedded
proposition (78) and is defined when that individual is familiar, not when the proposition is
true (`not_factive`, §5.3.2). The dependent mood is generalized conjunction (`dependentMood`),
which equates the content of the attitude event with the clause (92) and forbids stacking
(`stack_eq`).

## Implementation notes

* `Cat` has no mood head, so the MoodP of (47b) is the T-level spine, whose relevant property is
  the absence of C and D.
* The Neo-Davidsonian holder and theme arguments of (78) and (92) are not represented; the
  theorems concern the complement's and the modifier's denotations.

## TODO

* §5.5: the same conjunction over propositions (97) in concessive adjuncts and the tenseless
  simultaneous adjuncts (100)–(101).

## References

* [bochnak-hanink-2021]
* [hanink-2021]
* [kastner-2015]
* [elliott-2016]
-/

namespace BochnakHanink2021

open Washo.Clause Minimalist Semantics Semantics.Composition Reference

/-! ### Complementation against modification, Table 2 -/

/-- A predicate selects when it has an internal-argument frame (§3.2.2). -/
def Selects (v : Embedder) : Prop := v.frames ≠ []

instance : DecidablePred Selects := fun v ↦ inferInstanceAs (Decidable (v.frames ≠ []))

/-- A predicate selects iff it takes the nominalizer as clause-typer, the selected clause being
the nominalized DP. -/
theorem selects_iff_takes_ge : ∀ v ∈ embedders, Selects v ↔ v.toVerb.takes ge := by
  decide

/-- A nominalized complement is a CP under a silent D (3). -/
def complementSpine : ClauseSpine := ClauseSpine.cP.extend [.D]

/-- A dependent-mood modifier is a MoodP without C, adjoined to VP ((4), (47b)). -/
def modifierSpine : ClauseSpine := ClauseSpine.tP

/-- The spine of the clause a predicate embeds, from whether it selects. -/
def spine (v : Embedder) : ClauseSpine :=
  if Selects v then complementSpine else modifierSpine

/-- The embedded clause projects D iff it bears the nominalizer, and then it is a CP, while the
dependent-mood clause projects neither (Table 2). -/
theorem spine_projects_D_iff :
    ∀ v ∈ embedders, ((spine v).projects .D ↔ v.typer = ge) ∧
      ((spine v).projects .C ↔ v.typer = ge) := by
  decide

/-- 'Dream' without the reflexive selects and with it does not, so selection rather than the
predicate concept fixes the embedding ((53)–(55)). -/
theorem suus_selects_gumsuus_not : Selects suus ∧ ¬ Selects gumsuus := by
  decide

/-! ### The semantics of the two clauses, §5 -/

variable {E W : Type} (cont : E → W → Prop) (p q : W → Prop) (d : ℕ) (g : Assignment E) (s : W)

/-- The FPROP type-shift takes a proposition to the property of the individuals whose content it
is (76). -/
def fprop : E → Prop := fun x ↦ cont x = p

/-- The nominalized complement with index `d` is the familiar DP over FPROP (77). -/
def complement : Description E W := .anaphoric (fun _ _ x ↦ fprop cont p x) d

/-- The complement denotes the familiar individual whose content is the embedded proposition,
[hanink-2021]'s index as a variable (78). -/
theorem denote_complement :
    ⟦complement cont p d⟧ g s = russellIota fun x ↦ cont x = p ∧ Hanink2021.idxVar d g x := rfl

/-- The complement is defined iff its antecedent has the embedded content, familiarity rather
than truth (§5.3). -/
theorem denote_complement_isSome_iff : (⟦complement cont p d⟧ g s).isSome ↔ cont (g d) = p :=
  Description.denote_anaphoric_isSome_iff _ _ _ _

/-- Factivity is not lexically specified: the complement of 'know' is defined at a situation
where its content is false (§5.3.2, (86)–(87)). -/
theorem not_factive :
    ∃ (cont : Unit → Bool → Prop) (p : Bool → Prop) (g : Assignment Unit) (s : Bool),
      (⟦complement cont p 0⟧ g s).isSome ∧ ¬ p s :=
  ⟨fun _ ↦ (· = true), (· = true), fun _ ↦ (), false,
    (denote_complement_isSome_iff ..).2 rfl, Bool.false_ne_true⟩

/-- The dependent mood is generalized conjunction (75). -/
def dependentMood {α : Type*} (P Q : α → Prop) : α → Prop := P ⊓ Q

/-- A dependent-mood clause modifies the intransitive attitude predicate, equating the content of
the attitude event with the clause ((91)–(92)). -/
theorem dependentMood_fprop (V : E → Prop) (x : E) :
    dependentMood (fprop cont p) V x ↔ cont x = p ∧ V x := Iff.rfl

/-- Two dependent-mood clauses on one event are contradictory unless their contents agree, so
contents do not stack (§5.4). -/
theorem stack_eq (V : E → Prop) {x : E}
    (h : dependentMood (fprop cont p) (dependentMood (fprop cont q) V) x) : p = q :=
  h.1.symm.trans h.2.1

end BochnakHanink2021
