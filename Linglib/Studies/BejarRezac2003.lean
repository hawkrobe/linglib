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

## Main definitions

* `Argument`: a weak nominal, with its person and whether a functional category of its own
  licenses it.
* `pi`: the person probe, a `Probe` with total visibility whose active goals are the
  nominals not already licensed.
* `PLCOk`: the Person Licensing Condition over the person-Agree cycles of a derivation.
* `dncCycles`: the cycles of a dative–nominative construction, determined by whether the
  dative satisfies the EPP.

## Main results

* `pi_agree_eq_some_iff`: the person probe Agrees with the closest nominal, and only if it
  is not already licensed.
* `plcOk_iff`: a participant satisfies the condition iff its own functional category
  licenses it or it heads some cycle.
* `strong_pcc`: over a dative and an accusative the condition holds iff the accusative is
  3rd person.
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
* [harley-ritter-2002]: the person geometry behind `Argument.IsParticipant`.
* [zaenen-maling-thrainsson-1985], [taraldsen-1995], [sigurdsson-1996]: the Icelandic
  dative subject and its person restriction.
-/

namespace BejarRezac2003

open Minimalist

/-- A weak nominal in a Case-licensing domain: its person, and whether a φ-bearing
functional category of its own — applicative P, dative marker, focus — assigns its Case and
licenses its person feature (§4). -/
structure Argument where
  person : Person
  fLicensed : Bool
  deriving DecidableEq, Repr

/-- `a` bears an interpretable 1st/2nd person feature, the domain of the Person Licensing
Condition. -/
def Argument.IsParticipant (a : Argument) : Prop :=
  (decomposePerson a.person).hasParticipant = true

instance : DecidablePred Argument.IsParticipant := fun a =>
  inferInstanceAs (Decidable ((decomposePerson a.person).hasParticipant = true))

theorem Argument.ne_of_fLicensed {a b : Argument} (ha : a.fLicensed = true)
    (hb : b.fLicensed = false) : a ≠ b :=
  fun h => by subst h; simp [hb] at ha

/-- The person probe of a Case-licensing head: every nominal bears a person value (8), and
a nominal already licensed by its own functional category is inactive (§2, §4). -/
def pi : Probe Argument :=
  { vis := fun _ => true, act := fun a => !a.fLicensed }

theorem pi_search (goals : List Argument) : pi.search goals = goals.head? := by
  cases goals <;> rfl

/-- The person probe Agrees with the closest nominal, and only if that nominal is not
already licensed ((9), (10)). -/
theorem pi_agree_eq_some_iff {goals : List Argument} {a : Argument} :
    pi.agree goals = some a ↔ goals.head? = some a ∧ a.fLicensed = false := by
  rw [Probe.agree_eq_some_iff, pi_search]
  simp [pi]

/-- An inactive closest nominal absorbs the probe: match without Agree (9). -/
theorem pi_agree_absorbed (dat acc : Argument) (hd : dat.fLicensed = true) :
    pi.agree [dat, acc] = none :=
  Probe.agree_eq_none_of_inactive rfl (by simp [pi, hd])

/-- The Person Licensing Condition over the person-Agree cycles of a derivation: every
participant among `args` is licensed by its own functional category or Agrees with the person
probe of some cycle (§3). -/
def PLCOk (cycles : List (List Argument)) (args : List Argument) : Prop :=
  ∀ a ∈ args, a.IsParticipant →
    (a.fLicensed = true ∨ ∃ goals ∈ cycles, pi.agree goals = some a)

instance (cycles : List (List Argument)) (args : List Argument) :
    Decidable (PLCOk cycles args) :=
  inferInstanceAs (Decidable (∀ a ∈ args, a.IsParticipant →
    (a.fLicensed = true ∨ ∃ goals ∈ cycles, pi.agree goals = some a)))

/-- A participant satisfies the condition iff its own functional category licenses it or it
is the highest nominal of some cycle (§6). -/
theorem plcOk_iff (cycles : List (List Argument)) (args : List Argument) :
    PLCOk cycles args ↔ ∀ a ∈ args, a.IsParticipant →
      (a.fLicensed = true ∨ ∃ goals ∈ cycles, goals.head? = some a) := by
  unfold PLCOk
  refine forall₃_congr fun a _ _ => ?_
  simp only [pi_agree_eq_some_iff]
  cases a.fLicensed <;> simp

/-- One cycle over the base order is `Probe.AllLicensed` for the indiscriminate probe, with
the needy goals the participants not licensed by a functional category of their own. -/
theorem plcOk_singleCycle_iff_allLicensed (goals : List Argument) :
    PLCOk [goals] goals ↔
      (Probe.indiscriminate (α := Argument)).AllLicensed
        (fun a => decide a.IsParticipant && !a.fLicensed) goals := by
  rw [plcOk_iff, Probe.indiscriminate_allLicensed_iff]
  refine forall₂_congr fun a _ => ?_
  cases a.fLicensed <;> simp

/-! ### The constraint -/

/-- Over a dative and an accusative in one person-Agree cycle, the condition holds iff the
accusative is 3rd person ((1), (7)). -/
theorem strong_pcc (dat acc : Argument)
    (hd : dat.fLicensed = true) (ha : acc.fLicensed = false) :
    PLCOk [[dat, acc]] [dat, acc] ↔ ¬ acc.IsParticipant := by
  rw [plcOk_iff]
  simp [hd, ha, Argument.ne_of_fLicensed hd ha]

-- (1): *le lui* licit, *te lui* excluded.
example :
    PLCOk [[⟨.third, true⟩, ⟨.third, false⟩]] [⟨.third, true⟩, ⟨.third, false⟩] ∧
    ¬ PLCOk [[⟨.third, true⟩, ⟨.second, false⟩]] [⟨.third, true⟩, ⟨.second, false⟩] := by
  decide

/-! ### Obviation -/

/-- In the prepositional construction the theme is the highest nominal and the goal sits
under P, so the person probe Agrees with the theme and P licenses the goal ((3), (11a)). -/
theorem pp_repair (theme goal : Argument) (hg : goal.fLicensed = true) :
    PLCOk [[theme, goal]] [theme, goal] := by
  rw [plcOk_iff]
  simp [hg]

/-- The person-Agree cycles of a dative–nominative construction: T probes the base order,
and once the EPP is satisfied the projection of T probes again — over the same order if the
dative can satisfy the EPP, over the reversed order if the nominative has raised past it
((16), (17), (25)). -/
def dncCycles (dativeEPP : Bool) (dat nom : Argument) : List (List Argument) :=
  [[dat, nom], if dativeEPP then [dat, nom] else [nom, dat]]

/-- The Person Case Constraint applies in a dative–nominative construction iff the dative
satisfies the EPP (§5). -/
theorem dnc_pcc_iff (dativeEPP : Bool) (dat nom : Argument)
    (hd : dat.fLicensed = true) (hn : nom.fLicensed = false) :
    PLCOk (dncCycles dativeEPP dat nom) [dat, nom] ↔
      (dativeEPP = true → ¬ nom.IsParticipant) := by
  rw [plcOk_iff]
  cases dativeEPP <;> simp [dncCycles, hd, hn, Argument.ne_of_fLicensed hd hn]

-- (12) Icelandic *þið* excluded; (13) French *je lui fus présenté* licit.
example :
    ¬ PLCOk (dncCycles true ⟨.third, true⟩ ⟨.second, false⟩)
        [⟨.third, true⟩, ⟨.second, false⟩] ∧
    PLCOk (dncCycles false ⟨.third, true⟩ ⟨.first, false⟩)
        [⟨.third, true⟩, ⟨.first, false⟩] := by
  decide

end BejarRezac2003
