import Linglib.Phonology.Constraints.Basic
import Linglib.Phonology.OptimalityTheory.PartiallyOrderedConstraints
import Linglib.Core.Optimization.PermSubsetCombinatorics
import Linglib.Fragments.Tagalog.Phonology

/-!
# Zuraw (2010): A Model of Lexical Variation and the Grammar

This file formalizes the factorial typology of nasal substitution in [zuraw-2010]. When a
nasal-final prefix such as *maŋ-* attaches to an obstruent-initial stem, the nasal and the
obstruent may coalesce into a single nasal at the obstruent's place, *maŋ+bigáj* → *mamigáj*
'to distribute', or the cluster may survive, *paŋ+tabój* → *pantabój* 'to goad'. Six
constraints decide the outcome: `DEP-C` of (6), named `nasSub` after [zuraw-hayes-2017] and
extensionally the same here, and *NC of (17) after [pater-1999] favour substitution, while
*ASSOCIATE of (7) and the stringent stem-initial nasal hierarchy of (19), after
[prince-1997-stringency] and [delacy-2002], oppose it. With the six constraints freely ranked,
the paper's footnote counts the share of the 720 rankings that substitute for each stem-initial
stop; the same shares follow here in closed form from the substrate's uniform sampling of total
orders (`factorial_rates`), so that substitution is more likely on voiceless than on voiced
stems (`voicing_monotonicity`) and on fronter than on backer stems (`place_monotonicity`).
The implicational universals of [newman-1984] that the paper's Table 5 organizes hold
ranking by ranking: substitution on a voiced stop entails substitution on its voiceless
counterpart, and substitution on a stop entails substitution on any fronter stop of the same
voicing (`voicing_b_implies_p` and its kin, `g_implies_all`), and a ranking exists on which
every stop substitutes, the paper's pattern (j) (`pattern_j_witness`).

## Implementation notes

* The candidate space is the stem-initial stop paired with the substitution decision; the
  constraints the paper holds fixed above the six do not distinguish the two candidates.
* The rates are model quantities of the free-ranking idealization. The paper's dictionary
  counts, corpus rates and acceptability results are not represented; the place effect among
  voiceless stems is not significant in its judgment data.

## References

* [zuraw-2010]
* [zuraw-hayes-2017]
* [pater-1999]
* [prince-1997-stringency]
* [delacy-2002]
* [newman-1984]
* [blust-2004]
-/

namespace Zuraw2010

open Constraints Core.Optimization OptimalityTheory Core.Optimization.PermSubsetCombinatorics

/-! ### Stems and substitution decisions -/

/-- The six stem-initial stops; coalescence maps each to its homorganic nasal. -/
inductive StemC
  | p | t | k
  | b | d | g
  deriving DecidableEq, Repr, Fintype

/-- Whether nasal substitution applies: the coalesced nasal, or the faithful cluster. -/
inductive SubSt
  | yes
  | no
  deriving DecidableEq, Repr, Fintype

/-- A candidate is a stem-initial stop paired with a substitution decision. -/
abbrev NSCand := StemC × SubSt

/-- The stem-initial stop as a segment of `Fragments/Tagalog/Phonology.lean`. -/
def StemC.segment : StemC → Phonology.Segment
  | .p => Tagalog.p | .t => Tagalog.t | .k => Tagalog.k
  | .b => Tagalog.b | .d => Tagalog.d | .g => Tagalog.g

/-- The stem classes that the constraints below list are natural classes: the stems of *NC are
the voiceless ones, those of *[ŋ the dorsal ones, and those of *[n the ones that are not
labial. -/
theorem mem_iff_segment (c : StemC) :
    (c ∈ [StemC.p, .t, .k] ↔ Phonology.Segment.ofSpecs [(.voice, false)] ≤ c.segment) ∧
      (c ∈ [StemC.k, .g] ↔ Phonology.Segment.ofSpecs [(.dorsal, true)] ≤ c.segment) ∧
      (c ∈ [StemC.t, .d, .k, .g] ↔ Phonology.Segment.ofSpecs [(.labial, false)] ≤ c.segment) := by
  cases c <;> decide

/-- The nasal of the stop's place. -/
def StemC.nasal : StemC → Phonology.Segment
  | .p | .b => Tagalog.m
  | .t | .d => Tagalog.n
  | .k | .g => Tagalog.ŋ

/-- Coalescence gives the nasal of the stop's place, by the fragment's substitution. -/
theorem substitute_segment (c : StemC) : Tagalog.substitute c.segment = [c.nasal] := by
  cases c <;> decide

/-! ### The six constraints -/

/-- `DEP-C` of (6), which penalizes inserting a segmental host for the floating nasal: violated
by the faithful cluster for every stem. Named after [zuraw-hayes-2017]'s markedness `NasSub`,
which has the same violation profile on this candidate space. -/
def nasSub : Constraint NSCand :=
  Constraint.binary λ c => c.2 = SubSt.no

/-- *NC of (17), after [pater-1999]: a nasal must not be followed by a voiceless obstruent.
Violated by the faithful cluster for voiceless stems. -/
def starNC : Constraint NSCand :=
  Constraint.binary λ c => c.1 ∈ [StemC.p, .t, .k] ∧ c.2 = .no

/-- *ASSOCIATE of (7): no new association lines across a morpheme boundary. Violated by
coalescence for every stem. -/
def starAssoc : Constraint NSCand :=
  Constraint.binary λ c => c.2 = SubSt.yes

/-- *[ŋ of (19): a stem must not begin with ŋ. Violated by coalescence on velar stems. -/
def starInitVelar : Constraint NSCand :=
  Constraint.binary λ c => c.1 ∈ [StemC.k, .g] ∧ c.2 = .yes

/-- *[n of (19): a stem must not begin with n or a backer nasal. Violated by coalescence on
coronal and velar stems. -/
def starInitCorVel : Constraint NSCand :=
  Constraint.binary λ c => c.1 ∈ [StemC.t, .d, .k, .g] ∧ c.2 = .yes

/-- *[m of (19): a stem must not begin with m or a backer nasal. Violated by coalescence on
every stem. -/
def starInitAll : Constraint NSCand :=
  Constraint.binary λ c => c.2 = SubSt.yes

/-- The six constraints, in the order of the paper's footnote on free ranking. -/
def constraint : Fin 6 → Constraint NSCand
  | 0 => nasSub
  | 1 => starNC
  | 2 => starAssoc
  | 3 => starInitVelar
  | 4 => starInitCorVel
  | 5 => starInitAll

/-- The stringent hierarchy assigns one, two and three violations to coalesced labial, coronal
and velar stems. -/
theorem stringency_violations :
    starInitAll (.p, .yes) + starInitCorVel (.p, .yes) + starInitVelar (.p, .yes) = 1 ∧
    starInitAll (.t, .yes) + starInitCorVel (.t, .yes) + starInitVelar (.t, .yes) = 2 ∧
    starInitAll (.k, .yes) + starInitCorVel (.k, .yes) + starInitVelar (.k, .yes) = 3 := by
  decide

/-- *ASSOCIATE and *[m have the same violation profile on this candidate space. -/
theorem assoc_eq_initAll (c : StemC) (s : SubSt) : starAssoc (c, s) = starInitAll (c, s) := by
  cases c <;> cases s <;> rfl

/-! ### The free-ranking rates -/

/-- The violation profile in the shape the substrate's ranking sampler consumes. -/
def vp (c : StemC) (s : SubSt) (i : Fin 6) : ℕ := (constraint i) (c, s)

/-- Both decisions are available for every stem. -/
def nsCands : StemC → Finset SubSt := λ _ => Finset.univ

/-- The constraints that distinguish the two candidates for stem `c`. -/
def relevant (c : StemC) : Finset (Fin 6) :=
  Finset.univ.filter (λ i => vp c .yes i ≠ vp c .no i)

/-- The constraints that favour substitution for stem `c`. -/
def yesFav (c : StemC) : Finset (Fin 6) :=
  Finset.univ.filter (λ i => vp c .yes i < vp c .no i)

@[simp] theorem relevant_p : relevant .p = ({0, 1, 2, 5} : Finset (Fin 6)) := by decide
@[simp] theorem relevant_t : relevant .t = ({0, 1, 2, 4, 5} : Finset (Fin 6)) := by decide
@[simp] theorem relevant_k : relevant .k = ({0, 1, 2, 3, 4, 5} : Finset (Fin 6)) := by decide
@[simp] theorem relevant_b : relevant .b = ({0, 2, 5} : Finset (Fin 6)) := by decide
@[simp] theorem relevant_d : relevant .d = ({0, 2, 4, 5} : Finset (Fin 6)) := by decide
@[simp] theorem relevant_g : relevant .g = ({0, 2, 3, 4, 5} : Finset (Fin 6)) := by decide

@[simp] theorem yesFav_p : yesFav .p = ({0, 1} : Finset (Fin 6)) := by decide
@[simp] theorem yesFav_t : yesFav .t = ({0, 1} : Finset (Fin 6)) := by decide
@[simp] theorem yesFav_k : yesFav .k = ({0, 1} : Finset (Fin 6)) := by decide
@[simp] theorem yesFav_b : yesFav .b = ({0} : Finset (Fin 6)) := by decide
@[simp] theorem yesFav_d : yesFav .d = ({0} : Finset (Fin 6)) := by decide
@[simp] theorem yesFav_g : yesFav .g = ({0} : Finset (Fin 6)) := by decide

private theorem nsCands_two (c : StemC) : nsCands c = {SubSt.yes, SubSt.no} := by
  unfold nsCands
  ext o
  cases o <;> simp

/-- The share of the 720 total orders on which stem `c` substitutes. -/
def subProb (c : StemC) : ℚ := winProb nsCands vp (· = ·) c .yes

/-- The share is the fraction of distinguishing constraints that favour substitution. -/
private theorem subProb_eq_rate (c : StemC) :
    subProb c = ((yesFav c ∩ relevant c).card : ℚ) / (relevant c).card :=
  winProb_discrete_binary_rate (nsCands_two c) (λ heq => SubSt.noConfusion heq)

theorem subProb_p : subProb .p = 1/2 := by
  rw [subProb_eq_rate, relevant_p, yesFav_p,
      show (({0, 1} : Finset (Fin 6)) ∩ {0, 1, 2, 5}).card = 2 from by decide,
      show ({0, 1, 2, 5} : Finset (Fin 6)).card = 4 from by decide]
  norm_num

theorem subProb_t : subProb .t = 2/5 := by
  rw [subProb_eq_rate, relevant_t, yesFav_t,
      show (({0, 1} : Finset (Fin 6)) ∩ {0, 1, 2, 4, 5}).card = 2 from by decide,
      show ({0, 1, 2, 4, 5} : Finset (Fin 6)).card = 5 from by decide]
  norm_num

theorem subProb_k : subProb .k = 1/3 := by
  rw [subProb_eq_rate, relevant_k, yesFav_k,
      show (({0, 1} : Finset (Fin 6)) ∩ {0, 1, 2, 3, 4, 5}).card = 2 from by decide,
      show ({0, 1, 2, 3, 4, 5} : Finset (Fin 6)).card = 6 from by decide]
  norm_num

theorem subProb_b : subProb .b = 1/3 := by
  rw [subProb_eq_rate, relevant_b, yesFav_b,
      show (({0} : Finset (Fin 6)) ∩ {0, 2, 5}).card = 1 from by decide,
      show ({0, 2, 5} : Finset (Fin 6)).card = 3 from by decide]
  norm_num

theorem subProb_d : subProb .d = 1/4 := by
  rw [subProb_eq_rate, relevant_d, yesFav_d,
      show (({0} : Finset (Fin 6)) ∩ {0, 2, 4, 5}).card = 1 from by decide,
      show ({0, 2, 4, 5} : Finset (Fin 6)).card = 4 from by decide]
  norm_num

theorem subProb_g : subProb .g = 1/5 := by
  rw [subProb_eq_rate, relevant_g, yesFav_g,
      show (({0} : Finset (Fin 6)) ∩ {0, 2, 3, 4, 5}).card = 1 from by decide,
      show ({0, 2, 3, 4, 5} : Finset (Fin 6)).card = 5 from by decide]
  norm_num

/-- The six free-ranking shares of the paper's footnote: a half, two fifths and a third for
the voiceless stops, a third, a quarter and a fifth for the voiced ones. -/
theorem factorial_rates :
    subProb .p = 1/2 ∧ subProb .t = 2/5 ∧ subProb .k = 1/3 ∧
    subProb .b = 1/3 ∧ subProb .d = 1/4 ∧ subProb .g = 1/5 :=
  ⟨subProb_p, subProb_t, subProb_k, subProb_b, subProb_d, subProb_g⟩

/-- Within each voicing class the share falls from labial to coronal to velar. -/
theorem place_monotonicity :
    subProb .p > subProb .t ∧ subProb .t > subProb .k ∧
    subProb .b > subProb .d ∧ subProb .d > subProb .g := by
  rw [subProb_p, subProb_t, subProb_k, subProb_b, subProb_d, subProb_g]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-- At each place the voiceless share is at least the voiced one. -/
theorem voicing_monotonicity :
    subProb .p ≥ subProb .b ∧ subProb .t ≥ subProb .d ∧ subProb .k ≥ subProb .g := by
  rw [subProb_p, subProb_t, subProb_k, subProb_b, subProb_d, subProb_g]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-! ### The implicational universals, ranking by ranking -/

/-- If `c'` has a smaller distinguishing set than `c` and every extra constraint of `c` favours
substitution, then substitution on `c'` entails substitution on `c`. -/
theorem PicksAt_extends_smaller_D {σ : Equiv.Perm (Fin 6)} {c c' : StemC}
    (h_D : relevant c' ⊆ relevant c) (h_Y : yesFav c' ⊆ yesFav c)
    (h_extra : ∀ x ∈ relevant c, x ∉ relevant c' → x ∈ yesFav c)
    (h_c' : PicksAt nsCands vp σ c' .yes) : PicksAt nsCands vp σ c .yes := by
  rw [picksAt_binary_iff_head_mem_favoring (nsCands_two c')
        (λ heq => SubSt.noConfusion heq)] at h_c'
  rw [picksAt_binary_iff_head_mem_favoring (nsCands_two c) (λ heq => SubSt.noConfusion heq)]
  exact head_filter_subset_extends h_D h_Y h_extra _ h_c'

/-- If `c'` has a larger distinguishing set than `c` and its substitution-favouring constraints
all distinguish the candidates for `c`, then substitution on `c'` entails substitution on
`c`. -/
theorem PicksAt_extends_larger_D {σ : Equiv.Perm (Fin 6)} {c c' : StemC}
    (h_D : relevant c ⊆ relevant c') (h_Y : yesFav c' ⊆ yesFav c)
    (h_subset : yesFav c' ⊆ relevant c)
    (h_c' : PicksAt nsCands vp σ c' .yes) : PicksAt nsCands vp σ c .yes := by
  rw [picksAt_binary_iff_head_mem_favoring (nsCands_two c')
        (λ heq => SubSt.noConfusion heq)] at h_c'
  rw [picksAt_binary_iff_head_mem_favoring (nsCands_two c) (λ heq => SubSt.noConfusion heq)]
  exact head_filter_smaller_inherits h_D h_Y h_subset _ h_c'

/-- Substitution on voiced *b* entails substitution on voiceless *p*. -/
theorem voicing_b_implies_p (σ : Equiv.Perm (Fin 6)) :
    PicksAt nsCands vp σ .b .yes → PicksAt nsCands vp σ .p .yes :=
  PicksAt_extends_smaller_D (by decide) (by decide) (by decide)

/-- Substitution on voiced *d* entails substitution on voiceless *t*. -/
theorem voicing_d_implies_t (σ : Equiv.Perm (Fin 6)) :
    PicksAt nsCands vp σ .d .yes → PicksAt nsCands vp σ .t .yes :=
  PicksAt_extends_smaller_D (by decide) (by decide) (by decide)

/-- Substitution on voiced *g* entails substitution on voiceless *k*. -/
theorem voicing_g_implies_k (σ : Equiv.Perm (Fin 6)) :
    PicksAt nsCands vp σ .g .yes → PicksAt nsCands vp σ .k .yes :=
  PicksAt_extends_smaller_D (by decide) (by decide) (by decide)

/-- Substitution on velar *k* entails substitution on coronal *t*. -/
theorem place_k_implies_t (σ : Equiv.Perm (Fin 6)) :
    PicksAt nsCands vp σ .k .yes → PicksAt nsCands vp σ .t .yes :=
  PicksAt_extends_larger_D (by decide) (by decide) (by decide)

/-- Substitution on coronal *t* entails substitution on labial *p*. -/
theorem place_t_implies_p (σ : Equiv.Perm (Fin 6)) :
    PicksAt nsCands vp σ .t .yes → PicksAt nsCands vp σ .p .yes :=
  PicksAt_extends_larger_D (by decide) (by decide) (by decide)

/-- Substitution on velar *g* entails substitution on coronal *d*. -/
theorem place_g_implies_d (σ : Equiv.Perm (Fin 6)) :
    PicksAt nsCands vp σ .g .yes → PicksAt nsCands vp σ .d .yes :=
  PicksAt_extends_larger_D (by decide) (by decide) (by decide)

/-- Substitution on coronal *d* entails substitution on labial *b*. -/
theorem place_d_implies_b (σ : Equiv.Perm (Fin 6)) :
    PicksAt nsCands vp σ .d .yes → PicksAt nsCands vp σ .b .yes :=
  PicksAt_extends_larger_D (by decide) (by decide) (by decide)

/-- Substitution on voiced velar *g* entails substitution on every stop, the top of the
implicational hierarchy of Table 5. -/
theorem g_implies_all (σ : Equiv.Perm (Fin 6)) (h : PicksAt nsCands vp σ .g .yes) :
    PicksAt nsCands vp σ .p .yes ∧ PicksAt nsCands vp σ .t .yes ∧
    PicksAt nsCands vp σ .k .yes ∧ PicksAt nsCands vp σ .b .yes ∧
    PicksAt nsCands vp σ .d .yes ∧ PicksAt nsCands vp σ .g .yes := by
  have h_d := place_g_implies_d σ h
  have h_b := place_d_implies_b σ h_d
  have h_k := voicing_g_implies_k σ h
  have h_t := place_k_implies_t σ h_k
  have h_p := place_t_implies_p σ h_t
  exact ⟨h_p, h_t, h_k, h_b, h_d, h⟩

/-- Some ranking substitutes on every stop: pattern (j) of Table 5, that of Kalinga and
Sarangani Manobo. The identity ranking, with `DEP-C` on top, is one. -/
theorem pattern_j_witness :
    ∃ σ : Equiv.Perm (Fin 6),
      PicksAt nsCands vp σ .p .yes ∧ PicksAt nsCands vp σ .t .yes ∧
      PicksAt nsCands vp σ .k .yes ∧ PicksAt nsCands vp σ .b .yes ∧
      PicksAt nsCands vp σ .d .yes ∧ PicksAt nsCands vp σ .g .yes :=
  ⟨1, by decide, by decide, by decide, by decide, by decide, by decide⟩

end Zuraw2010
