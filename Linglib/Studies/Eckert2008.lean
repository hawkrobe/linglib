import Linglib.Core.Relation.ReflTransGen
import Mathlib.Data.Fintype.Sum
import Mathlib.Order.Closure
import Mathlib.Order.Iterate
import Mathlib.Tactic.DeriveFintype

/-!
# Eckert (2008): Variation and the indexical field

This file formalizes the indexical field of [eckert-2008]. Against the reading of a variable as
the reflection of a fixed social category, the paper builds on [silverstein-2003]'s indexical
order: a first-order index marks membership in a population, the social evaluation of that
population is reconstrued into elements of character the variable comes to mark, and every
nth-order value is available for an n + 1st reconstrual, so that continual reconstrual creates
an indexical field, a constellation of ideologically linked meanings any of which a situated use
may activate. An ideological field records what each meaning is available to be construed as
(`IdeologicalField`), one reconstrual adds the construals of a set of meanings (`construe`), and
the indexical field of a first-order index is its closure under construal (`indexicalField`), a
closure operator whose closed sets are the sets no reconstrual extends and whose closure the
iterated reconstruals exhaust. [labov-1963]'s Martha's Vineyard (ay) is the paper's example of an
indicator becoming a marker, the fishermen's claim about what a Vineyarder is a second-order
value of the index of Vineyarders.

The (ING) field of Figure 3, built on [campbell-kibler-2007]'s matched-guise results, holds
favourable and unfavourable meanings for both variants, so the variants' meanings do not work in
lockstep, and a hearer interprets a variant against presupposed indexicality: the variant whose
field holds the hearer's impression of the speaker passes, and the other is heard as a social
move. The /t/ release field of Figure 4 distinguishes momentary stances from permanent
qualities, the former accreting into the latter, the ideological field that elaborates it
(`accretion`), and is anchored by social types; the diva style of [podesva-2007]'s Heath
combines the two extremes of the articulation continuum. The Belten High variables of Figure 1
divide into the older changes led by girls and the newer urban changes led by burnouts, so that
the burnout girls alone are among the leaders of every variable, the urban–suburban opposition
embedded within a suburban school.

## Implementation notes

The fields hold the meanings of Figures 3 and 4 as printed, and the ideological links the text
states; the association strengths of the numerical `IndexicalField` substrate are not in the
paper. The leadership of Figure 1 is derived from the two generalizations the text states, and
`Leads` marks a group among the greatest or second-greatest users, which reproduces the figure's
marked cells. The burned-out burnout girls, a network cluster within the burnout girls, the
Beijing variables of Figure 2 from [zhang-2005], Podesva's release-rate measurements, and the
(DH) discussion are not represented.

## References

* [eckert-2008]
* [silverstein-2003]
* [labov-1963]
* [campbell-kibler-2007]
* [podesva-2007]
* [eckert-2000]
* [zhang-2005]
-/

namespace Eckert2008

/-! ### Indexical order and the indexical field -/

/-- An ideological field: the meanings each potential meaning is available to be construed as,
the links along which an nth-order value acquires an n + 1st. -/
abbrev IdeologicalField (T : Type*) := T → Finset T

namespace IdeologicalField

variable {T : Type*} [DecidableEq T] (I : IdeologicalField T) {S : Finset T} {t : T}

/-- One reconstrual: the meanings of `S` together with everything they are construed as. -/
def construe (S : Finset T) : Finset T := S ∪ S.biUnion I

@[simp] theorem mem_construe : t ∈ I.construe S ↔ t ∈ S ∨ ∃ s ∈ S, t ∈ I s := by
  simp [construe]

theorem subset_construe (S : Finset T) : S ⊆ I.construe S := Finset.subset_union_left

theorem construe_mono : Monotone I.construe := λ _ _ h =>
  Finset.union_subset_union h (Finset.biUnion_subset_biUnion_of_subset_left _ h)

/-- Reconstrual only adds meanings: the values of order `n` are among those of order `n + 1`. -/
theorem monotone_construe_iterate (S : Finset T) : Monotone λ n => I.construe^[n] S :=
  I.construe_mono.monotone_iterate_of_le_map (I.subset_construe S)

variable [Fintype T]

/-- The indexical field a first-order index creates: every meaning the index is continually
reconstrued as, the closure of the index under the ideological links. -/
def indexicalField : ClosureOperator (Finset T) :=
  .mk₂ (λ S => Finset.univ.filter λ t => ∃ s ∈ S, Relation.ReflTransGen (λ a b => b ∈ I a) s t)
    (λ _ _ h => Finset.mem_filter.2 ⟨Finset.mem_univ _, _, h, .refl⟩)
    (λ _ _ h _ ht => by
      obtain ⟨s, hs, hst⟩ := (Finset.mem_filter.1 ht).2
      obtain ⟨u, hu, hus⟩ := (Finset.mem_filter.1 (h hs)).2
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, u, hu, hus.trans hst⟩)

@[simp] theorem mem_indexicalField :
    t ∈ I.indexicalField S ↔ ∃ s ∈ S, Relation.ReflTransGen (λ a b => b ∈ I a) s t := by
  simp [indexicalField]

/-- The reconstruals of every order lie in the field. -/
theorem iterate_construe_subset_indexicalField (n : ℕ) (S : Finset T) :
    I.construe^[n] S ⊆ I.indexicalField S := by
  induction n with
  | zero => exact I.indexicalField.le_closure S
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    intro t ht
    obtain ht | ⟨s, hs, hts⟩ := I.mem_construe.1 ht
    · exact ih ht
    · obtain ⟨u, hu, hus⟩ := I.mem_indexicalField.1 (ih hs)
      exact I.mem_indexicalField.2 ⟨u, hu, hus.tail hts⟩

/-- Continual reconstrual creates, in the end, the indexical field: a meaning is in the field
exactly when some order of reconstrual reaches it. -/
theorem mem_indexicalField_iff_exists_iterate :
    t ∈ I.indexicalField S ↔ ∃ n, t ∈ I.construe^[n] S := by
  refine ⟨λ h => ?_, λ ⟨n, h⟩ => I.iterate_construe_subset_indexicalField n S h⟩
  obtain ⟨s, hs, hst⟩ := I.mem_indexicalField.1 h
  clear h
  induction hst with
  | refl => exact ⟨0, hs⟩
  | tail _ hbc ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by rw [Function.iterate_succ_apply']; exact I.mem_construe.2 (.inr ⟨_, hn, hbc⟩)⟩

/-- A set of meanings is closed exactly when no reconstrual extends it. -/
theorem isClosed_iff : I.indexicalField.IsClosed S ↔ I.construe S = S := by
  rw [I.indexicalField.isClosed_iff]
  constructor
  · intro h
    refine (I.subset_construe S).antisymm' ?_
    exact (I.iterate_construe_subset_indexicalField 1 S).trans h.subset
  · intro h
    refine (I.indexicalField.le_closure S).antisymm' λ t ht => ?_
    obtain ⟨n, hn⟩ := I.mem_indexicalField_iff_exists_iterate.1 ht
    rwa [Function.iterate_fixed h] at hn

/-- Once a reconstrual stabilizes, it is the indexical field. -/
theorem indexicalField_eq_iterate {n : ℕ}
    (h : I.construe (I.construe^[n] S) = I.construe^[n] S) :
    I.indexicalField S = I.construe^[n] S :=
  ((I.indexicalField.monotone (I.monotone_construe_iterate S (Nat.zero_le n))).trans
    (I.isClosed_iff.2 h).closure_eq.le).antisymm (I.iterate_construe_subset_indexicalField n S)

end IdeologicalField

/-! ### Martha's Vineyard (ay) -/

/-- The meanings of centralized (ay): membership among Vineyarders, and the claim about what a
Vineyarder is that the fishermen made with the variant, local authenticity and opposition to
the mainland. -/
inductive VineyardMeaning
  | vineyarder
  | localAuthenticity
  | oppositionToMainland
  deriving DecidableEq, Fintype

/-- The island's ideological field: the evaluation of Vineyarders that the disagreements about
the future of the island made available to the index. -/
def vineyardIdeology : IdeologicalField VineyardMeaning
  | .vineyarder => {.localAuthenticity, .oppositionToMainland}
  | _ => ∅

/-- The first-order index of centralized (ay): Vineyarders. -/
def centralizedAy : Finset VineyardMeaning := {.vineyarder}

/-- The indicator becomes a marker: local authenticity is a second-order value of centralized
(ay), not a first-order one. -/
theorem vineyard_marker :
    .localAuthenticity ∉ centralizedAy ∧
      .localAuthenticity ∈ vineyardIdeology.construe centralizedAy := by
  decide

/-- The field of [labov-1963]'s variant reconstrued: Vineyarders, and what a Vineyarder is. -/
theorem indexicalField_centralizedAy :
    vineyardIdeology.indexicalField centralizedAy =
      {.vineyarder, .localAuthenticity, .oppositionToMainland} :=
  vineyardIdeology.indexicalField_eq_iterate (n := 1) (by decide)

/-! ### The (ING) field, Figure 3 -/

/-- The velar and apical variants of (ING). -/
inductive INGVariant
  | velar
  | apical
  deriving DecidableEq, Fintype

/-- The potential meanings of Figure 3: the velar variant educated, formal, effortful and
articulate or pretentious; the apical variant uneducated, relaxed, easygoing or lazy, and
inarticulate or unpretentious. -/
inductive INGMeaning
  | educated
  | uneducated
  | formal
  | relaxed
  | effortful
  | easygoing
  | lazy
  | articulate
  | pretentious
  | inarticulate
  | unpretentious
  deriving DecidableEq, Fintype

/-- The (ING) field of Figure 3, black for the velar variant and gray for the apical. -/
def ingField : INGVariant → Finset INGMeaning
  | .velar => {.educated, .formal, .effortful, .articulate, .pretentious}
  | .apical => {.uneducated, .relaxed, .easygoing, .lazy, .inarticulate, .unpretentious}

/-- A hearer's evaluation of a meaning. -/
inductive Evaluation
  | favourable
  | unfavourable
  deriving DecidableEq, Fintype

/-- The evaluation of the meanings the figure pairs as alternatives: the apical speaker heard
as inarticulate or lazy or else as unpretentious or easygoing, the velar speaker as articulate
or as pretentious. The other meanings carry none. -/
def INGMeaning.evaluation : INGMeaning → Option Evaluation
  | .articulate | .unpretentious | .easygoing => some .favourable
  | .pretentious | .inarticulate | .lazy => some .unfavourable
  | _ => none

/-- The region of a variant's field a hearer's evaluation activates. -/
def activate (e : Evaluation) (v : INGVariant) : Finset INGMeaning :=
  (ingField v).filter (·.evaluation = some e)

/-- The pairs do not work in lockstep: each variant has favourable and unfavourable meanings. -/
theorem activate_nonempty : ∀ e v, (activate e v).Nonempty := by decide

/-- Presupposed indexicality: the variants a hearer expects from an impression of the speaker
formed on general style and content, those whose field holds the impression. -/
def expected (i : INGMeaning) : Finset INGVariant := Finset.univ.filter (i ∈ ingField ·)

/-- An impression of the speaker as educated leads the hearer to expect the velar variant, one
as uneducated the apical. -/
theorem expected_educated_uneducated :
    expected .educated = {.velar} ∧ expected .uneducated = {.apical} := by
  decide

/-- The social moves a hearer attributes to the wrong variant. -/
inductive Move
  | pretentious
  | condescending
  | insincere
  deriving DecidableEq, Fintype, Inhabited

/-- The expected variant passes; the wrong one is heard as pretentious, condescending or
insincere. -/
def interpret (i : INGMeaning) (v : INGVariant) : Finset Move :=
  if v ∈ expected i then ∅ else Finset.univ

theorem interpret_eq_empty_iff (i : INGMeaning) (v : INGVariant) :
    interpret i v = ∅ ↔ v ∈ expected i := by
  unfold interpret; split_ifs with h <;> simp [h, Finset.univ_nonempty.ne_empty]

/-- The velar variant from a speaker taken to be uneducated is heard as a move. -/
theorem interpret_velar_of_uneducated : interpret .uneducated .velar = Finset.univ := by
  decide

/-! ### The /t/ release field, Figure 4 -/

/-- The stances of Figure 4, momentary and situated. -/
inductive TStance
  | formal
  | clear
  | emphatic
  | annoyed
  | angry
  | careful
  | exasperated
  | polite
  | effortful
  deriving DecidableEq, Fintype

/-- The permanent qualities of Figure 4, and the quality of habitually taking a stance, the
angry person of stance accretion. -/
inductive TQuality
  | educated
  | articulate
  | elegant
  | prissy
  | habitual (s : TStance)
  deriving DecidableEq, Fintype

/-- A meaning of /t/ release: a stance or a quality. -/
inductive TMeaning
  | stance (s : TStance)
  | quality (q : TQuality)
  deriving DecidableEq, Fintype

/-- Stance accretion as an ideological field: a stance is available to be construed as the
quality of habitually taking it, the mechanism by which the field is elaborated. -/
def accretion : IdeologicalField TMeaning
  | .stance s => {.quality (.habitual s)}
  | .quality _ => ∅

/-- The stances of a set of meanings accrete into qualities. -/
theorem quality_habitual_mem_construe {S : Finset TMeaning} {s : TStance}
    (h : .stance s ∈ S) : .quality (.habitual s) ∈ accretion.construe S :=
  accretion.mem_construe.2 (.inr ⟨_, h, by simp [accretion]⟩)

/-- The field of /t/ release of Figure 4: nine stances and four qualities. -/
def tRelease : Finset TMeaning :=
  {.stance .formal, .stance .clear, .stance .emphatic, .stance .annoyed, .stance .angry,
    .stance .careful, .stance .exasperated, .stance .polite, .stance .effortful,
    .quality .educated, .quality .articulate, .quality .elegant, .quality .prissy}

/-- Qualities are construed no further, so accretion elaborates the field in one round: the
indexical field of /t/ release is Figure 4 with the habitual quality of each of its stances. -/
theorem indexicalField_tRelease :
    accretion.indexicalField tRelease = accretion.construe tRelease :=
  accretion.indexicalField_eq_iterate (n := 1) (by decide)

/-- The social types of Figure 4, the enregistered voices at the less fluid end of the field
that anchor interpretation: the British of the stereotype /t/ release evokes, the school teacher
of the standard of clear speech, the nerd girl who builds on that standard while distancing
herself from teachers, and the gay diva of [podesva-2007]'s Heath. -/
inductive SocialType
  | british
  | schoolTeacher
  | nerdGirl
  | gayDiva
  deriving DecidableEq

/-- The meanings the text has each type anchor: the British the articulateness of their
stereotype and the elegance it opens up, the teacher clear, careful standard speech, the nerd
girl its clarity and education, the diva the prissiness of the teacher's pet with
exasperation. -/
def SocialType.anchors : SocialType → Finset TMeaning
  | .british => {.quality .articulate, .quality .elegant}
  | .schoolTeacher => {.stance .clear, .stance .careful, .quality .educated}
  | .nerdGirl => {.stance .clear, .quality .educated}
  | .gayDiva => {.quality .prissy, .stance .exasperated}

/-- The nerd girls build on the school-teachery standard from which they distance themselves. -/
theorem nerdGirl_anchors_subset :
    SocialType.nerdGirl.anchors ⊆ SocialType.schoolTeacher.anchors := by
  decide

/-- The diva's generalized attitude of exasperation: the stance accreted into a quality. -/
theorem gayDiva_habitual_exasperated :
    .quality (.habitual .exasperated) ∈ accretion.construe SocialType.gayDiva.anchors :=
  quality_habitual_mem_construe (by decide)

/-- The continuum of /t/ articulation, hypo- to hyperarticulation: the deletion stigmatized in
African American English, the flap of American English, the release of British English and the
exaggerated release of the diva's parody. -/
inductive Articulation
  | deletion
  | flap
  | released
  | exaggeratedRelease
  deriving DecidableEq, Fintype

/-- Position on the continuum. -/
def Articulation.rank : Articulation → ℕ
  | .deletion => 0
  | .flap => 1
  | .released => 2
  | .exaggeratedRelease => 3

instance : LinearOrder Articulation := .lift' Articulation.rank (by decide)

instance : OrderBot Articulation where
  bot := .deletion
  bot_le := by decide

instance : OrderTop Articulation where
  top := .exaggeratedRelease
  le_top := by decide

/-- The diva style combines deletion with exaggerated bursts. -/
def divaStyle : Finset Articulation := {.deletion, .exaggeratedRelease}

/-- The diva style is the two extremes of the continuum. -/
theorem divaStyle_eq : divaStyle = {⊥, ⊤} := rfl

/-! ### Belten High, Figure 1 -/

inductive Gender
  | girl
  | boy
  deriving DecidableEq

/-- The school-oriented jocks and the urban-oriented burnouts. -/
inductive Orientation
  | jock
  | burnout
  deriving DecidableEq

/-- A social category of Figure 1: gender crossed with orientation. -/
structure Group where
  gender : Gender
  orientation : Orientation
  deriving DecidableEq

/-- The strata of the seven variables: the older fronting components of the Northern Cities
Shift, stabilized across the suburbs, the newer backing changes more advanced near the urban
centre, and negative concord. -/
inductive Stratum
  | older
  | newer
  | negativeConcord
  deriving DecidableEq, Fintype

/-- A group is among the leaders of a stratum, the greatest or second-greatest users Figure 1
marks: the older changes are used predominantly by girls, the newer urban changes and negative
concord by burnouts. -/
def Leads (g : Group) : Stratum → Prop
  | .older => g.gender = .girl
  | .newer | .negativeConcord => g.orientation = .burnout

instance (g : Group) : DecidablePred (Leads g)
  | .older => inferInstanceAs (Decidable (g.gender = .girl))
  | .newer | .negativeConcord => inferInstanceAs (Decidable (g.orientation = .burnout))

/-- The burnout girls alone are among the leaders of every variable: the two leaderships cross
gender with orientation, the urban–suburban opposition embedded within the school. -/
theorem leads_all_iff (g : Group) : (∀ s, Leads g s) ↔ g = ⟨.girl, .burnout⟩ :=
  ⟨λ h => by cases g; cases h .older; cases h .newer; rfl, by rintro rfl s; cases s <;> rfl⟩

/-- The jock boys lead nothing. -/
theorem jockBoys_lead_none : ∀ s, ¬ Leads ⟨.boy, .jock⟩ s := by decide

end Eckert2008
