import Linglib.Syntax.Minimalist.Probe.Phi
import Linglib.Fragments.Mayan.Kaqchikel.Agreement
import Linglib.Studies.BejarRezac2003

/-!
# Preminger (2014): Agreement and Its Failures

This file formalizes the account of φ-agreement in the Kichean Agent-Focus construction of
[preminger-2014], chapters 3 to 5 and 7. The Agent-Focus verb has a single agreement slot,
filled from the absolutive series, and which core argument controls it is summarized by the
hierarchy *1st/2nd person > 3rd plural > 3rd singular*, symmetric in subject and object (22),
(23). The account derives the hierarchy from two feature-relativized probes: a person probe
seeking [participant], merged first, whose goal is clitic-doubled, and a number probe seeking
[plural], whose own exponent surfaces only when no clitic occupies the slot (65), (71), (74).
Each probe skips arguments lacking its feature, so the slot reflects the participant if there is
one, otherwise the plural argument, otherwise nothing (`afTarget_eq`, `afTarget_eq_rank`,
`af_paradigm`, `afMarker_comm`). The Person Licensing Condition of [bejar-rezac-2003], that a
[participant] feature be licensed by Agree (75), makes the person restriction, at most one
1st/2nd person core argument (25), (76), the consequence of a single person probe
(`personRestriction_iff_plc`), while nothing restricts two plural arguments (77); the clitic
carries its goal's whole φ-set, its number included, whatever the other argument's number (68),
(69) (`participant_marker`). Under the obligatory-operations model of chapter 5, a probe that
finds no goal ends unvalued and the derivation converges with the null exponent (112), (113)
(`afTarget_eq_none_iff`, `failed_agree_tolerated`), while an available plural goal must be
agreed with (114) (`plural_marker`). Relativization is what separates the pattern from the
Person Case Constraint: an unrelativized person probe is absorbed by a third-person goal above
a participant, where the relativized one skips it (§4.2) (`relativization_contrast`). A
hierarchy assigns a marker to two participants where the probes exclude them, the asymmetry
of §7.1 (`hierarchy_silent_on_restriction`).

## Implementation notes

The person and number probes are the substrate's `Probe.Target.participant` and `.plural` over
φ-cells, and their derivation is the `Probe.cascade` of the two, which is the single-slot
competition (71). The marker is the fragment's Set B exponent of the cascade's goal, the empty
exponent when both probes fail, and undefined when the Person Licensing Condition fails. The
empirical paradigm (22) enters as the paper's own shorthand, the hierarchy (23) read as the
substrate's `probeResolutionRank`, so that `af_paradigm` states that the probes derive it. The
morphophonology of the markers (§3.4, (148), (149)), the alternatives of §4.5, the regular
transitives and intransitives of §4.6, and the Zulu and Basque case studies of chapter 6 are
prose; the Zulu analysis is `Studies/Halpert2012.lean`.

## References

* [preminger-2014]
* [bejar-rezac-2003]
* [harley-ritter-2002]
* [nevins-2011]
* [halpert-2012]
-/

namespace Preminger2014

open Kaqchikel Minimalist Agreement

/-! ### The probes and the slot (§4.4) -/

/-- π⁰, the person probe, relativized to [participant]. -/
def piProbe : Probe Cell := Probe.Target.participant.toProbe

/-- #⁰, the number probe, relativized to [plural]. -/
def numProbe : Probe Cell := Probe.Target.plural.toProbe

/-- The goal the Agent-Focus slot reflects, given the subject's and the object's cells: the
person probe's goal, else the number probe's, else none, the competition for the single slot
(71) as a cascade. -/
def afTarget (subj obj : Cell) : Option Cell := Probe.cascade [piProbe, numProbe] [subj, obj]

/-- The Person Licensing Condition on the clause's two core arguments. -/
def Plc (subj obj : Cell) : Prop :=
  PLC Prod.snd ([(.A, subj), (.P, obj)] : List (ArgumentRole × Cell))

instance (subj obj : Cell) : Decidable (Plc subj obj) := inferInstanceAs (Decidable (PLC _ _))

/-- The absolutive exponent of a cell, empty where the paradigm has none. -/
def exponent (c : Cell) : List Morphology.Morph := (setBExponent.realize c).getD []

/-- The Agent-Focus marker: the exponent of the slot's goal, the empty exponent when both probes
fail, and undefined when the Person Licensing Condition fails. -/
def afMarker (subj obj : Cell) : Option (List Morphology.Morph) :=
  if Plc subj obj then some (((afTarget subj obj).map exponent).getD []) else none

/-- The person restriction (25): at most one core argument bears [participant]. -/
def PersonRestriction (subj obj : Cell) : Prop := ¬ (subj.IsParticipant ∧ obj.IsParticipant)

instance : DecidableRel PersonRestriction := λ s o =>
  inferInstanceAs (Decidable ¬ (s.IsParticipant ∧ o.IsParticipant))

/-! ### Relativized probing (§4.2, §4.4) -/

/-- Skipping: the slot reflects a participant if either argument is one, the subject first;
otherwise a plural argument; otherwise nothing (66), (73). -/
theorem afTarget_eq (s o : Cell) :
    afTarget s o = if s.IsParticipant then some s else if o.IsParticipant then some o
      else if s.isPlural then some s else if o.isPlural then some o else none := by
  rcases Bool.eq_false_or_eq_true (decomposePerson s.toPerson).hasParticipant with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (decomposePerson o.toPerson).hasParticipant with h2 | h2 <;>
    rcases Bool.eq_false_or_eq_true s.isPlural with h3 | h3 <;>
    rcases Bool.eq_false_or_eq_true o.isPlural with h4 | h4 <;>
    simp [afTarget, piProbe, numProbe, Probe.Target.toProbe, Cell.visibleTo, probeVisible,
      Cell.IsParticipant, Probe.cascade, Probe.search, Probe.ofVis,
      List.find?_cons, h1, h2, h3, h4]

/-- The rank of a cell on the hierarchy (23): [participant] above [plural] above the rest, the
substrate's probe-resolution rank. -/
def rank (c : Cell) : ℕ := probeResolutionRank c.toPerson c.isPlural

/-- The probes derive the hierarchy: the slot reflects the higher-ranked argument, the subject
at a tie, and nothing when both rank lowest. -/
theorem afTarget_eq_rank (s o : Cell) :
    afTarget s o = if rank s = 0 ∧ rank o = 0 then none
      else if rank o ≤ rank s then some s else some o := by
  rw [afTarget_eq]
  rcases Bool.eq_false_or_eq_true (decomposePerson s.toPerson).hasParticipant with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (decomposePerson o.toPerson).hasParticipant with h2 | h2 <;>
    rcases Bool.eq_false_or_eq_true s.isPlural with h3 | h3 <;>
    rcases Bool.eq_false_or_eq_true o.isPlural with h4 | h4 <;>
    simp [rank, probeResolutionRank, Cell.IsParticipant, Cell.visibleTo, probeVisible, h1, h2, h3,
      h4]

/-- The hierarchy (23) as an account, the morphological competition of §3.3.2: the slot shows
the higher-ranked argument's absolutive marker. -/
def hierarchyMarker (subj obj : Cell) : List Morphology.Morph :=
  exponent (if rank obj ≤ rank subj then subj else obj)

/-- The paradigm (22), (74): on every licit pair of person–number cells the probes deliver
the hierarchy's marker. -/
theorem af_paradigm :
    ∀ s ∈ Cell.pnCells, ∀ o ∈ Cell.pnCells,
      PersonRestriction s o → afMarker s o = some (hierarchyMarker s o) := by
  decide

/-- The marker is symmetric in subject and object (22, note a), (74): a consequence of skipping,
the probe finding its goal in either position. -/
theorem afMarker_comm : ∀ s ∈ Cell.pnCells, ∀ o ∈ Cell.pnCells, afMarker s o = afMarker o s := by
  decide

/-! ### Licensing (§4.4.2) -/

/-- The person restriction is the Person Licensing Condition on the clause's two core
arguments (76): a single person probe licenses at most one [participant] feature. -/
theorem personRestriction_iff_plc (s o : Cell) : PersonRestriction s o ↔ Plc s o := by
  unfold PersonRestriction Plc PLC
  rw [Probe.allLicensed_iff]
  constructor
  · intro h a ha b hb hva hvb
    rcases List.mem_pair.mp ha with rfl | rfl <;> rcases List.mem_pair.mp hb with rfl | rfl
    · rfl
    · exact absurd ⟨hva, hvb⟩ h
    · exact absurd ⟨hvb, hva⟩ h
    · rfl
  · rintro h ⟨hs, ho⟩
    exact nomatch congrArg Prod.fst (h (.A, s) (.head _) (.P, o) (.tail _ (.head _)) hs ho)

/-- The marker is undefined exactly when the person restriction is violated; two plural
arguments in particular are never excluded (77). -/
theorem afMarker_eq_none_iff (s o : Cell) : afMarker s o = none ↔ ¬ PersonRestriction s o := by
  rw [afMarker, personRestriction_iff_plc]
  split_ifs with h <;> simp [h]

/-- The clitic is featurally coarse (68), (69): with one participant argument, the marker is
that argument's whole exponent, its number included, whether it is the subject or the object
and whatever the other argument's number. -/
theorem participant_marker (s o : Cell) (h : ¬ (s.IsParticipant ∧ o.IsParticipant)) :
    (s.IsParticipant → afMarker s o = some (exponent s)) ∧
      (o.IsParticipant → afMarker s o = some (exponent o)) := by
  have hplc : Plc s o := (personRestriction_iff_plc s o).1 h
  rw [afMarker, if_pos hplc, afTarget_eq]
  refine ⟨λ hs => by simp [hs], λ ho => ?_⟩
  have hs : ¬ s.IsParticipant := λ hs => h ⟨hs, ho⟩
  simp [hs, ho]

/-! ### Obligatory operations (chapter 5) -/

/-- The slot is empty exactly when both probes end unvalued: failed Agree at the level of
outcomes and at the level of the slot are one fact. -/
theorem afTarget_eq_none_iff (s o : Cell) :
    afTarget s o = none ↔
      piProbe.outcome [s, o] = .unvalued ∧ numProbe.outcome [s, o] = .unvalued := by
  rw [afTarget, Probe.cascade_eq_none_iff, Probe.outcome_eq_unvalued_iff,
    Probe.outcome_eq_unvalued_iff]
  simp

/-- Failed Agree is tolerated (112), (113): with no participant and no plural argument, both
probes end unvalued, the derivation converges, and the slot carries the null exponent. -/
theorem failed_agree_tolerated (s o : Cell) (hs : ¬ s.IsParticipant) (ho : ¬ o.IsParticipant)
    (hsp : ¬ s.isPlural) (hop : ¬ o.isPlural) :
    afTarget s o = none ∧ afMarker s o = some [] := by
  have hplc : Plc s o := (personRestriction_iff_plc s o).1 λ h => hs h.1
  rw [afMarker, if_pos hplc, afTarget_eq]
  simp [hs, ho, hsp, hop]

/-- No gratuitous nonagreement (114): with no participant argument, a plural argument must be
agreed with, and the slot carries its exponent, the subject's first. -/
theorem plural_marker (s o : Cell) (hs : ¬ s.IsParticipant) (ho : ¬ o.IsParticipant) :
    (s.isPlural → afMarker s o = some (exponent s)) ∧
      (¬ s.isPlural → o.isPlural → afMarker s o = some (exponent o)) := by
  have hplc : Plc s o := (personRestriction_iff_plc s o).1 λ h => hs h.1
  rw [afMarker, if_pos hplc, afTarget_eq]
  exact ⟨λ hsp => by simp [hs, ho, hsp], λ hsp hop => by simp [hs, ho, hsp, hop]⟩

/-! ### Against the alternatives (§4.2, chapter 7) -/

/-- Relativization against the Person Case Constraint (§4.2): the unrelativized person probe
of [bejar-rezac-2003] is absorbed by a Case-licensed third-person dative above a participant,
the PCC, where the Kichean probe, relativized to [participant], skips the third-person argument
and licenses the participant below it. -/
theorem relativization_contrast :
    ¬ BejarRezac2003.PLCOk
        [[BejarRezac2003.dat (.pn .third .Sing), PhiGoal.unvalued (.pn .first .Sing)]]
        [BejarRezac2003.dat (.pn .third .Sing), PhiGoal.unvalued (.pn .first .Sing)] ∧
      Plc (.pn .third .Sing) (.pn .first .Sing) := by
  decide

/-- The asymmetry a hierarchy cannot state (§7.1): it assigns a marker to two participant
arguments, which the probes exclude, while two plural arguments are admitted by both. -/
theorem hierarchy_silent_on_restriction :
    afMarker (.pn .first .Sing) (.pn .second .Sing) = none ∧
      hierarchyMarker (.pn .first .Sing) (.pn .second .Sing) = exponent (.pn .first .Sing) ∧
      afMarker (.pn .third .Plur) (.pn .third .Plur) = some (exponent (.pn .third .Plur)) := by
  decide

end Preminger2014
