import Linglib.Syntax.Minimalist.Probe.Phi

/-!
# Béjar and Rezac 2003: person licensing and the Person Case Constraint

This file formalizes Béjar and Rezac's derivation of the Person Case Constraint — in a
combination of two phonologically weak objects the direct object may not be 1st or 2nd
person — from a probe–goal system with separate person and number probes and a Person
Licensing Condition: an interpretable 1st/2nd person feature must enter an Agree relation
with a functional category. The person probe of a Case-licensing head matches the closest
nominal; a dative already Case-licensed by its own functional category is inactive and
absorbs the probe, so a 1st/2nd person theme below it is never licensed. Obviation supplies
a further person probe: embedding the theme's competitor under a preposition, or, in a
dative–nominative construction whose dative cannot satisfy the EPP, raising the nominative
over the dative so that the projection of T probes again.

Goals are `Minimalist.PhiGoal`s — a Case-licensing state with a φ-cell — and the person
probe is `Probe.ofAct`, the probe gated only by the Active Goal Hypothesis.

## Main definitions

* `dat`: a dative, Case-valued by its own functional category.
* `pi`: the person probe.
* `PLCOk`: the Person Licensing Condition over the person-Agree cycles of a derivation.
* `dncCycles`: the cycles of a dative–nominative construction, determined by whether the
  dative satisfies the EPP.

## Main results

* `pi_agree_eq_some_iff`: the person probe Agrees with the closest nominal, and only if it
  is active.
* `plcOk_iff`: a participant satisfies the condition iff its Case is already valued or it
  heads some cycle.
* `strong_pcc`: over a dative and an unvalued nominal the condition holds iff the lower
  nominal is 3rd person.
* `dnc_pcc_iff`: in a dative–nominative construction the constraint applies iff the dative
  satisfies the EPP.
* `plcOk_singleCycle_iff_allLicensed`: one cycle over the base order is
  `Probe.AllLicensed` for the indiscriminate probe.

## References

* [bejar-rezac-2003]
* [bonet-1991]: the constraint.
* [chomsky-2000]: Agree, the Active Goal Hypothesis, and closest c-command.
* [anagnostopoulou-2003]: checking of the person feature by the dative and the
  cliticization loophole.
* [harley-ritter-2002]: the person geometry behind `Agreement.Cell.IsParticipant`.
* [zaenen-maling-thrainsson-1985], [taraldsen-1995], [sigurdsson-1996]: the Icelandic
  dative subject and its person restriction.
-/

namespace BejarRezac2003

open Minimalist Agreement

/-- A dative: Case valued by its own φ-bearing functional category — applicative P or
dative marker — and so inactive for outside Agree (§4). -/
def dat (c : Cell) : PhiGoal := .valued .dat c

/-- The person probe of a Case-licensing head: every nominal bears a person value (8), and
a nominal whose Case is already valued is inactive (§2, §4). -/
def pi : Probe PhiGoal := .ofAct (·.isActive)

/-- The person probe Agrees with the closest nominal, and only if that nominal is active
((9), (10)). -/
theorem pi_agree_eq_some_iff {goals : List PhiGoal} {g : PhiGoal} :
    pi.agree goals = some g ↔ goals.head? = some g ∧ g.isActive = true :=
  Probe.ofAct_agree_eq_some_iff

/-- An inactive closest nominal absorbs the probe: match without Agree (9). -/
theorem pi_agree_absorbed (d g : PhiGoal) (hd : d.isActive = false) :
    pi.agree [d, g] = none :=
  Probe.agree_eq_none_of_inactive rfl hd

/-- The Person Licensing Condition over the person-Agree cycles of a derivation: every
participant among `args` has its Case valued by a functional category of its own or Agrees
with the person probe of some cycle (§3). -/
def PLCOk (cycles : List (List PhiGoal)) (args : List PhiGoal) : Prop :=
  ∀ g ∈ args, g.cell.IsParticipant →
    (g.isActive = false ∨ ∃ goals ∈ cycles, pi.agree goals = some g)

instance (cycles : List (List PhiGoal)) (args : List PhiGoal) :
    Decidable (PLCOk cycles args) :=
  inferInstanceAs (Decidable (∀ g ∈ args, g.cell.IsParticipant →
    (g.isActive = false ∨ ∃ goals ∈ cycles, pi.agree goals = some g)))

/-- A participant satisfies the condition iff its Case is already valued or it is the
highest nominal of some cycle (§6). -/
theorem plcOk_iff (cycles : List (List PhiGoal)) (args : List PhiGoal) :
    PLCOk cycles args ↔ ∀ g ∈ args, g.cell.IsParticipant →
      (g.isActive = false ∨ ∃ goals ∈ cycles, goals.head? = some g) := by
  unfold PLCOk
  refine forall₃_congr fun g _ _ => ?_
  simp only [pi_agree_eq_some_iff]
  cases g.isActive <;> simp

/-- One cycle over the base order is `Probe.AllLicensed` for the indiscriminate probe, with
the needy goals the active participants. -/
theorem plcOk_singleCycle_iff_allLicensed (goals : List PhiGoal) :
    PLCOk [goals] goals ↔
      (Probe.indiscriminate (α := PhiGoal)).AllLicensed
        (fun g => decide g.cell.IsParticipant && g.isActive) goals := by
  rw [plcOk_iff, Probe.indiscriminate_allLicensed_iff]
  refine forall₂_congr fun g _ => ?_
  cases g.isActive <;> simp

/-! ### The constraint -/

/-- Over a dative and an unvalued nominal in one person-Agree cycle, the condition holds iff
the lower nominal is 3rd person ((1), (7)). -/
theorem strong_pcc (cd ca : Cell) :
    PLCOk [[dat cd, .unvalued ca]] [dat cd, .unvalued ca] ↔ ¬ ca.IsParticipant := by
  rw [plcOk_iff]
  simp [dat]

-- (1): *le lui* licit, *te lui* excluded.
example :
    PLCOk [[dat (.pn .third .Sing), .unvalued (.pn .third .Sing)]]
      [dat (.pn .third .Sing), .unvalued (.pn .third .Sing)] ∧
    ¬ PLCOk [[dat (.pn .third .Sing), .unvalued (.pn .second .Sing)]]
      [dat (.pn .third .Sing), .unvalued (.pn .second .Sing)] := by
  decide

/-! ### Obviation -/

/-- In the prepositional construction the theme is the highest nominal and the goal sits
under P, so the person probe Agrees with the theme and P licenses the goal ((3), (11a)). -/
theorem pp_repair (ct cg : Cell) :
    PLCOk [[.unvalued ct, dat cg]] [.unvalued ct, dat cg] := by
  rw [plcOk_iff]
  simp [dat]

/-- The person-Agree cycles of a dative–nominative construction: T probes the base order,
and once the EPP is satisfied the projection of T probes again — over the same order if the
dative can satisfy the EPP, over the reversed order if the nominative has raised past it
((16), (17), (25)). -/
def dncCycles (dativeEPP : Bool) (d n : PhiGoal) : List (List PhiGoal) :=
  [[d, n], if dativeEPP then [d, n] else [n, d]]

/-- The Person Case Constraint applies in a dative–nominative construction iff the dative
satisfies the EPP (§5). -/
theorem dnc_pcc_iff (dativeEPP : Bool) (cd cn : Cell) :
    PLCOk (dncCycles dativeEPP (dat cd) (.unvalued cn)) [dat cd, .unvalued cn] ↔
      (dativeEPP = true → ¬ cn.IsParticipant) := by
  rw [plcOk_iff]
  cases dativeEPP <;> simp [dncCycles, dat]

-- (12) Icelandic *þið* excluded; (13) French *je lui fus présenté* licit.
example :
    ¬ PLCOk (dncCycles true (dat (.pn .third .Sing)) (.unvalued (.pn .second .Sing)))
        [dat (.pn .third .Sing), .unvalued (.pn .second .Sing)] ∧
    PLCOk (dncCycles false (dat (.pn .third .Sing)) (.unvalued (.pn .first .Sing)))
        [dat (.pn .third .Sing), .unvalued (.pn .first .Sing)] := by
  decide

end BejarRezac2003
