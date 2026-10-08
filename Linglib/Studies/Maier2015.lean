module

public import Linglib.Semantics.Dynamic.DRS.Accessibility
public import Linglib.Data.Examples.Maier2015
public import Mathlib.Data.Fin.VecNotation

/-!
# Maier (2015): Parasitic Attitudes

This file formalizes the solution in [maier-2015] to the attitude-projection puzzle of
[karttunen-1973], *Bill believed Fred had been beating his wife and he hoped Fred would
stop*, which does not presuppose for the speaker that Fred was beating his wife. An agent's
mental state is one discourse representation, a belief layer with labelled non-doxastic
compartments embedded in it (`MentalState`, `MentalState.flatten`), so a referent introduced
in the belief layer is accessible from every compartment while a compartment's referents are
visible nowhere else (`accessible_belief_of_compartment`, `not_accessible_of_belief`):
the non-doxastic attitudes are parasitic on belief. A sequence of ascriptions to one agent
merges into one description (`MentalState.merge`), after which a presupposition triggered in
a desire compartment binds, in the manner of [van-der-sandt-1992], to the believed event
rather than projecting (`MentalState.bind`, `presup_binds_after_merge`,
`presup_resolved_after_binding`), whereas one triggered in the belief layer after a desire
finds no antecedent there and projects. That asymmetry is the paper's data: in the sequences
of `Data/Examples/Maier2015` the presupposition is filtered exactly when the doxastic
ascription comes first (`filtering_iff_doxastic_first`).

## Implementation notes

The compartment labels are structural, not intensional operators, so parasitism is the
standard accessibility of the DRS core in `Semantics/Dynamic/DRS`, a compartment being a
subordinate box; the core's negation is the subordination device, its truth conditions
playing no role. The general accessibility lemmas assume the belief layer and the
compartments hold atomic conditions, as every description in the paper does.

## TODO

The paper is not on file; the example and definition numbers are transcribed from an
earlier version of this file and are UNVERIFIED.

## References

* [maier-2015]
* [karttunen-1973]
* [van-der-sandt-1992]
-/

@[expose] public section

open FirstOrder DRT

namespace Maier2015

/-! ### The DRS language of the Karttunen example (§5.3) -/

/-- The example's relations are `sue` and `jane`, `husband(h, j)`, the event
`cheat(e, j, h)`, and `stop(j, e')`. -/
inductive MaierRel : ℕ → Type
  | sue : MaierRel 1
  | jane : MaierRel 1
  | husband : MaierRel 2
  | cheat : MaierRel 3
  | stop : MaierRel 2

/-- The first-order language of the example. -/
def maierLang : Language := ⟨λ _ => Empty, MaierRel⟩

/-- Conditions over `maierLang` with `ℕ` discourse referents. -/
abbrev MCond := Condition maierLang ℕ

/-- A condition introducing no box. -/
def MCond.IsAtomic : MCond → Prop
  | .rel _ _ | .eq _ _ => True
  | _ => False

instance : DecidablePred MCond.IsAtomic := λ c => by
  cases c <;> unfold MCond.IsAtomic <;> infer_instance

/-! ### Mental-state descriptions (§3.1) -/

/-- Attitude-mode labels for the non-doxastic compartments: desire, imagination, intention. -/
inductive AttMode where
  | des
  | imgn
  | int
  deriving DecidableEq, Repr, BEq

/-- A labelled non-doxastic compartment: its own referents and conditions under a mode. -/
structure Compartment where
  mode : AttMode
  drefs : List ℕ
  conds : List MCond

/-- A mental-state description (32): a belief layer with embedded compartments. -/
structure MentalState where
  beliefDrefs : List ℕ
  beliefConds : List MCond
  compartments : List Compartment

/-- A compartment as a subordinate box. -/
def Compartment.box (c : Compartment) : MCond := .neg (.mk c.drefs.toFinset c.conds)

/-- A description flattens to the belief box with each compartment a subordinate box, so
that accessibility runs from a compartment up to the belief layer and not back. -/
def MentalState.flatten (K : MentalState) : DRS maierLang ℕ :=
  .mk K.beliefDrefs.toFinset (K.beliefConds ++ K.compartments.map Compartment.box)

/-! ### Parasitism as accessibility -/

/-- No step of the walk leaves a box whose conditions introduce no box. -/
private theorem not_scopeStep_of_atomic {bs : List (DRS maierLang ℕ)} {D : DRS maierLang ℕ}
    {q : List (DRS maierLang ℕ) × DRS maierLang ℕ} (h : ∀ c ∈ D.conditions, MCond.IsAtomic c) :
    ¬ ScopeStep (bs, D) q := by
  rintro (⟨hc⟩ | ⟨hc⟩ | ⟨hc⟩ | ⟨hc⟩ | ⟨hc⟩) <;> exact h _ hc

/-- The belief layer does not see a compartment: where a belief referent is declared, only
belief referents are accessible, if no compartment declares it again. -/
theorem not_accessible_of_belief (K : MentalState) (hb : ∀ c ∈ K.beliefConds, c.IsAtomic)
    (hcs : ∀ c ∈ K.compartments, ∀ cd ∈ c.conds, cd.IsAtomic) {x y : ℕ}
    (hxc : ∀ c ∈ K.compartments, x ∉ c.drefs) (hy : y ∉ K.beliefDrefs) :
    ¬ DRS.Accessible K.flatten x y := by
  rintro ⟨p, hp, hx, hyp⟩
  rcases hp.cases_head with rfl | ⟨q, hq, hqp⟩
  · simp [MentalState.flatten, hy] at hyp
  · cases hq with
    | neg hc =>
      rcases List.mem_append.1 hc with hc | hc
      · exact absurd (hb _ hc) id
      · obtain ⟨c, hcK, hbox⟩ := List.mem_map.1 hc
        simp only [Compartment.box, Condition.neg.injEq] at hbox
        subst hbox
        rcases hqp.cases_head with rfl | ⟨r, hr, -⟩
        · exact hxc c hcK (by simpa using hx)
        · exact not_scopeStep_of_atomic (hcs c hcK) hr
    | impAnte hc | impCons hc | disL hc | disR hc =>
      rcases List.mem_append.1 hc with hc | hc
      · exact absurd (hb _ hc) id
      · obtain ⟨c, -, hbox⟩ := List.mem_map.1 hc
        simp [Compartment.box] at hbox

/-- A compartment sees the belief layer: where a compartment declares a referent, every belief
referent is accessible, parasitism in the paper's sense (§3.1). -/
theorem accessible_belief_of_compartment (K : MentalState) {x y : ℕ} (hx : x ∈ K.beliefDrefs)
    (hyc : ∃ c ∈ K.compartments, y ∈ c.drefs) : DRS.Accessible K.flatten y x := by
  obtain ⟨c, hc, hy⟩ := hyc
  exact ⟨_, .single (.neg (D := K.flatten) (List.mem_append_right _ (List.mem_map_of_mem hc))),
    by simpa using hy, by simp [MentalState.flatten, hx]⟩

/-! ### Attitude merge (58) and presupposition binding -/

/-- Append one compartment's content to another of the same mode. -/
def Compartment.append (c c' : Compartment) : Compartment :=
  { mode := c.mode, drefs := c.drefs ++ c'.drefs, conds := c.conds ++ c'.conds }

/-- Merge two compartment lists by attitude mode. -/
def mergeCompartments (cs cs' : List Compartment) : List Compartment :=
  cs'.foldl (λ cur c' =>
    if cur.any (·.mode == c'.mode) then
      cur.map (λ c => if c.mode == c'.mode then c.append c' else c)
    else cur ++ [c']) cs

/-- Attitude merge (58) makes two partial descriptions of one agent's state one, merging the
belief layers and combining like-mode compartments. -/
def MentalState.merge (K K' : MentalState) : MentalState :=
  { beliefDrefs := K.beliefDrefs ++ K'.beliefDrefs
    beliefConds := K.beliefConds ++ K'.beliefConds
    compartments := mergeCompartments K.compartments K'.compartments }

/-- Resolve a presupposition by binding its referent to an accessible antecedent, in the
manner of [van-der-sandt-1992]: drop the presupposed referent and rename it throughout. -/
def MentalState.bind (presup antecedent : ℕ) (K : MentalState) : MentalState :=
  { beliefDrefs := K.beliefDrefs.filter (· != presup)
    beliefConds := K.beliefConds.map (Condition.map λ d => if d = presup then antecedent else d)
    compartments := K.compartments.map λ c =>
      { mode := c.mode
        drefs := c.drefs.filter (· != presup)
        conds := c.conds.map (Condition.map λ d => if d = presup then antecedent else d) } }

/-! ### Karttunen's puzzle (§5.3)

*Sue thinks that Jane has been cheating on her husband. She hopes that Jane will stop
cheating on him.* Referents: Sue 10, Jane 11, the husband 12, the believed cheating event 20,
and the cheating event 21 presupposed by *stop*. -/

/-- After the first sentence Sue believes there is a cheating event (59). -/
def sueBelief : MentalState :=
  { beliefDrefs := [10, 11, 12, 20]
    beliefConds := [.rel .sue ![10], .rel .jane ![11], .rel .husband ![12, 11],
                    .rel .cheat ![20, 11, 12]]
    compartments := [] }

/-- The second sentence on its own gives a desire compartment with *stop* and the presupposed
event, with no antecedent in its belief layer. -/
def sueHope : MentalState :=
  { beliefDrefs := []
    beliefConds := []
    compartments := [{ mode := .des, drefs := [21],
                       conds := [.rel .stop ![11, 21], .rel .cheat ![21, 11, 12]] }] }

/-- The two ascriptions merged (59). -/
def sueMerged : MentalState := sueBelief.merge sueHope

/-- The merged description after binding the presupposed event to the believed one (60). -/
def sueBound : MentalState := sueMerged.bind 21 20

/-- Before the merge the believed event does not occur in the hope description, so the
presupposition of *stop* has no antecedent and could only be accommodated. -/
theorem believed_event_absent_before_merge : 20 ∉ DRS.varFinset sueHope.flatten := by
  decide

/-- After the merge the believed event is accessible from the presupposed one, so binding is
licensed: the filtering. -/
theorem presup_binds_after_merge : DRS.Accessible sueMerged.flatten 21 20 :=
  accessible_belief_of_compartment sueMerged (by decide) (by decide)

/-- The dependence is asymmetric: the believed event does not see the desire's referent. -/
theorem parasitic_asymmetry : ¬ DRS.Accessible sueMerged.flatten 20 21 :=
  not_accessible_of_belief sueMerged (by decide) (by decide) (by decide) (by decide)

/-- After binding, the presupposed referent is gone and the believed event remains: resolved
by binding, neither accommodated nor projected (60). -/
theorem presup_resolved_after_binding :
    21 ∉ DRS.varFinset sueBound.flatten ∧ 20 ∈ DRS.varFinset sueBound.flatten := by
  decide

/-! ### The data -/

/-- In the attitude sequences of the paper and of [karttunen-1973], the presupposition of the
second ascription is filtered, and the discourse felicitous, exactly when the doxastic
ascription comes first: the parasitic attitude sees the belief and not conversely. -/
theorem filtering_iff_doxastic_first :
    ∀ e ∈ Examples.all, e.judgment = .acceptable ↔ e.feature? "order" = some "doxasticFirst" := by
  decide

end Maier2015
