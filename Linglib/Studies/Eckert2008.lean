import Linglib.Pragmatics.SocialMeaning.IndexicalField
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Eckert (2008): Variation and the Indexical Field

This file formalizes the indexical field of [eckert-2008]. Against the view of a variable as
reflecting a fixed social category, the paper builds on [silverstein-2003]'s indexical order:
a variable that indexes membership in a population, a first-order index or indicator, has the
social evaluation of that population reconstrued into elements of character, a second-order
index or marker, and every nth-order value is available for an n + 1st reconstrual, so that
the continual reconstrual of a variable creates an indexical field, a constellation of
ideologically linked meanings any of which a situated use may activate, `Field` and
`Reconstrual`, with [labov-1963]'s Martha's Vineyard (ay) as the example, `vineyard`. The
(ING) field of Figure 3, built on [campbell-kibler-2007]'s matched-guise results, holds
favourable and unfavourable meanings for both variants, so the variants' meanings do not work
in lockstep, `ing_not_antipodal`, and a hearer interprets a variant against presupposed
indexicality: the variant expected from the impression of the speaker passes and the other
is heard as pretentious, condescending or insincere, `interpret`. The /t/ release field of
Figure 4 distinguishes momentary stances from permanent qualities, the former accreting into
the latter and so elaborating the field, `accretion`, and is anchored by social types, the
nerd girl, the Yeshiva boy and the gay diva of the studies it reviews and the British and the
school teacher of the ideology of hyperarticulation, `region`, the diva style combining the
two ends of the articulation continuum, `divaStyle`. The Belten High variables of Figure 1
divide into the older changes led by girls and the newer urban changes led by burnouts, so
that the burnout girls alone lead every variable, `burnoutGirls_lead` and
`leads_all_iff`, the embedding of the urban–suburban opposition within a suburban school.

## Implementation notes

A field is a set of potential meanings per variant, the paper's constellation, and the
substrate's numerical `IndexicalField` is recovered by the indicator association,
`toIndexicalField`; the association strengths the substrate allows are not in the paper.
Only the meanings the text attributes are recorded, since Figures 3 and 4 are not in the
text layer. The leadership of Figure 1 is derived from the two generalizations the text
states rather than transcribed cell by cell. The Beijing variables of Figure 2, Podesva's
measurements of one speaker's release rates and burst strengths, and the (DH) discussion are
not represented.

## References

* [eckert-2008]
* [silverstein-2003]
* [campbell-kibler-2007]
* [podesva-2007]
* [labov-1963]
* [eckert-2000]
-/

namespace Eckert2008

open SocialMeaning.IndexicalField

/-! ### Fields and reconstrual -/

/-- An indexical field: the constellation of potential meanings of each variant. -/
abbrev Field (V T : Type) := V → Finset T

/-- The substrate's numerical field with the indicator association: a variant indexes exactly
the meanings of its field. -/
def toIndexicalField {V T : Type} [DecidableEq T] (f : Field V T) (order : IndexicalOrder) :
    IndexicalField V T where
  association v t := if t ∈ f v then 1 else 0
  order := order

theorem toIndexicalField_indexes {V T : Type} [DecidableEq T] (f : Field V T)
    (order : IndexicalOrder) (v : V) (t : T) :
    (toIndexicalField f order).indexes v t ↔ t ∈ f v := by
  show (if t ∈ f v then (1 : ℚ) else 0) > 0 ↔ t ∈ f v
  split_ifs with h <;> simp [h]

/-- A variable's history of construal: the field at each order, each order's field extending
the last, since an nth-order value is always available for an n + 1st reconstrual. -/
structure Reconstrual (V T : Type) where
  /-- The field at order `n`. -/
  field : ℕ → Field V T
  grows : ∀ n v, field n v ⊆ field (n + 1) v

/-- The field only grows across orders. -/
theorem Reconstrual.mono {V T : Type} (r : Reconstrual V T) (v : V) :
    Monotone (λ n => r.field n v) :=
  monotone_nat_of_le_succ λ n => r.grows n v

/-- The two variants of (ay) on Martha's Vineyard. -/
inductive AyVariant
  | centralized
  | open_
  deriving DecidableEq, Repr, Fintype

/-- The meanings of centralized (ay): membership among Vineyarders, and the claim about what a
Vineyarder is that the fishermen made with it, local authenticity and opposition to the
mainland. -/
inductive VineyardMeaning
  | vineyarder
  | localAuthenticity
  | oppositionToMainland
  deriving DecidableEq, Repr, Fintype

/-- [labov-1963] reconstrued: the first-order index of Vineyarders acquires the fishermen's
ideological claim as a second-order value. -/
def vineyard : Reconstrual AyVariant VineyardMeaning where
  field
    | 0, .centralized => {.vineyarder}
    | _ + 1, .centralized => {.vineyarder, .localAuthenticity, .oppositionToMainland}
    | _, .open_ => ∅
  grows n v := by cases n <;> cases v <;> first | decide | exact Finset.Subset.refl _

/-- The indicator becomes a marker: at the second order the substrate's field indexes local
authenticity, which the first-order field did not. -/
theorem vineyard_marker :
    (toIndexicalField (vineyard.field 1) .second).indexes .centralized .localAuthenticity ∧
      ¬ (toIndexicalField (vineyard.field 0) .first).indexes .centralized .localAuthenticity := by
  simp only [toIndexicalField_indexes]
  decide

/-! ### The (ING) field, Figure 3 -/

/-- The velar and apical variants of (ING). -/
inductive INGVariant
  | velar
  | apical
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The potential meanings of (ING) the text attributes: the velar variant as educated,
intelligent, articulate and effortful, or pretentious; the apical variant as lacking effort,
lazy, uncaring, rebellious, impolite, inarticulate, casual and relaxed, or unpretentious and
easygoing. -/
inductive INGMeaning
  | educated
  | intelligent
  | articulate
  | effortful
  | pretentious
  | lackingEffort
  | lazy
  | uncaring
  | rebellious
  | impolite
  | inarticulate
  | casual
  | relaxed
  | unpretentious
  | easygoing
  deriving DecidableEq, Repr, Fintype

/-- A hearer's evaluation of a meaning. -/
inductive Evaluation
  | favourable
  | unfavourable
  deriving DecidableEq, Repr, Fintype

/-- The evaluation the text attaches to a meaning, `none` for the casual and relaxed readings
it leaves neutral. -/
def INGMeaning.evaluation : INGMeaning → Option Evaluation
  | .educated | .intelligent | .articulate | .effortful | .unpretentious | .easygoing =>
    some .favourable
  | .pretentious | .lackingEffort | .lazy | .uncaring | .rebellious | .impolite
  | .inarticulate => some .unfavourable
  | .casual | .relaxed => none

/-- The (ING) field. -/
def ingField : Field INGVariant INGMeaning
  | .velar => {.educated, .intelligent, .articulate, .effortful, .pretentious}
  | .apical => {.lackingEffort, .lazy, .uncaring, .rebellious, .impolite, .inarticulate, .casual,
      .relaxed, .unpretentious, .easygoing}

/-- The region of a variant's field a hearer's perspective activates. -/
def activate (e : Evaluation) (v : INGVariant) : Finset INGMeaning :=
  (ingField v).filter (·.evaluation = some e)

/-- Each variant has favourable and unfavourable meanings: the pairs do not work in lockstep,
the apical variant heard as inarticulate or as easygoing, the velar as articulate or as
pretentious. -/
theorem activate_nonempty : ∀ e v, (activate e v).Nonempty := by decide

/-- On the substrate's field, the two variants are not antipodal. -/
theorem ing_not_antipodal : ¬ (toIndexicalField ingField .second).Antipodal .velar .apical := by
  unfold IndexicalField.Antipodal
  decide

/-- A hearer's impression of the speaker from general style and content. -/
inductive Impression
  | educatedNorthern
  | uneducatedSouthern
  deriving DecidableEq, Repr

/-- Presupposed indexicality: the variant a hearer expects from an impression. -/
def expected : Impression → INGVariant
  | .educatedNorthern => .velar
  | .uneducatedSouthern => .apical

/-- The social move a hearer attributes to a variant. -/
inductive Move
  | expected
  | pretentious
  | condescending
  | insincere
  deriving DecidableEq, Repr

/-- The expected variant passes; the wrong one is heard as pretentious, condescending or
insincere. -/
def interpret (i : Impression) (v : INGVariant) : Finset Move :=
  if v = expected i then {.expected} else {.pretentious, .condescending, .insincere}

theorem interpret_expected (i : Impression) : interpret i (expected i) = {.expected} := by
  simp [interpret]

theorem interpret_velar_of_uneducated :
    interpret .uneducatedSouthern .velar = {.pretentious, .condescending, .insincere} := by
  decide

/-! ### The /t/ release field, Figure 4 -/

/-- The stances /t/ release indexes: emphasis, and the exasperation and anger that stop release
commonly expresses. -/
inductive TStance
  | emphatic
  | exasperated
  | angry
  deriving DecidableEq, Repr, Fintype

/-- The permanent qualities in the field, and the quality of habitually taking a stance. -/
inductive TQuality
  | clear
  | educated
  | articulate
  | cultured
  | refined
  | elegant
  | polite
  | careful
  | prissy
  | habitual (s : TStance)
  deriving DecidableEq, Repr, Fintype

/-- A meaning of /t/ release: a stance or a quality. -/
inductive TMeaning
  | stance (s : TStance)
  | quality (q : TQuality)
  deriving DecidableEq, Repr, Fintype

/-- Stance accretion: a person habitually taking a stance is positioned as having the
corresponding quality, the mechanism by which the field is elaborated. -/
def accretion (f : Finset TMeaning) : Finset TMeaning :=
  f ∪ (Finset.univ.filter (λ s => TMeaning.stance s ∈ f)).image (λ s => .quality (.habitual s))

theorem subset_accretion (f : Finset TMeaning) : f ⊆ accretion f := Finset.subset_union_left

/-- The stances of a field accrete into qualities. -/
theorem quality_habitual_mem_accretion {f : Finset TMeaning} {s : TStance}
    (h : TMeaning.stance s ∈ f) : TMeaning.quality (.habitual s) ∈ accretion f :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ s, h⟩))

/-- The meanings of /t/ release the text attributes before accretion: the stances and the
qualities of clear speech, the school-teachery standard, the British stereotype, and the
refinement, elegance, care and politeness they open up, and the prissiness of the diva. -/
def tReleaseBase : Finset TMeaning :=
  {.stance .emphatic, .stance .exasperated, .stance .angry, .quality .clear, .quality .educated,
    .quality .articulate, .quality .cultured, .quality .refined, .quality .elegant,
    .quality .polite, .quality .careful, .quality .prissy}

/-- The field of /t/ release as a history of accretion. -/
def tRelease : Reconstrual Unit TMeaning where
  field n _ := accretion^[n] tReleaseBase
  grows n _ := by
    rw [Function.iterate_succ_apply']
    exact subset_accretion _

/-- The social types that anchor regions of the field: the nerd girl and the Yeshiva boy
building on clear speech, the diva on prissiness and exasperation, the British on refinement,
and the school teacher on clear, careful, standard speech. -/
inductive SocialType
  | nerdGirl
  | yeshivaBoy
  | gayDiva
  | british
  | schoolTeacher
  deriving DecidableEq, Repr, Fintype

/-- The region of the field each social type anchors. -/
def region : SocialType → Finset TMeaning
  | .schoolTeacher => {.quality .clear, .quality .careful, .quality .educated}
  | .nerdGirl => {.quality .clear, .quality .educated}
  | .yeshivaBoy => {.quality .clear, .stance .emphatic}
  | .british => {.quality .cultured, .quality .refined, .quality .articulate}
  | .gayDiva => {.quality .prissy, .stance .exasperated}

/-- Every social type anchors a region of the field. -/
theorem region_subset : ∀ st, region st ⊆ tRelease.field 0 () := by decide

/-- The nerd girls' /t/ release builds on the school-teachery standard of clear speech from
which they distance themselves. -/
theorem nerdGirl_region_subset : region .nerdGirl ⊆ region .schoolTeacher := by decide

/-- The continuum of /t/ articulation, from the deletion stigmatized in African American
English through the flap of American English and the release of British English to the
exaggerated release of the diva's parody, hypo- to hyperarticulation. -/
inductive Articulation
  | deletion
  | flap
  | released
  | exaggeratedRelease
  deriving DecidableEq, Repr, Fintype

def Articulation.rank : Articulation → ℕ
  | .deletion => 0
  | .flap => 1
  | .released => 2
  | .exaggeratedRelease => 3

instance : LinearOrder Articulation :=
  LinearOrder.lift' Articulation.rank λ a b h => by
    cases a <;> cases b <;> simp_all [Articulation.rank]

/-- The diva style combines deletion with exaggerated bursts. -/
def divaStyle : Finset Articulation := {.deletion, .exaggeratedRelease}

/-- The diva style spans the whole continuum: every articulation lies between two of its
members. -/
theorem divaStyle_spans : ∀ b, ∃ a ∈ divaStyle, ∃ a' ∈ divaStyle, a ≤ b ∧ b ≤ a' := by decide

/-! ### Belten High, Figure 1 -/

inductive Gender
  | girl
  | boy
  deriving DecidableEq, Repr, Fintype

/-- The school-oriented jocks and the urban-oriented burnouts. -/
inductive Orientation
  | jock
  | burnout
  deriving DecidableEq, Repr, Fintype

/-- A social category of Figure 1: gender crossed with orientation. -/
structure Group where
  gender : Gender
  orientation : Orientation
  deriving DecidableEq, Repr, Fintype

/-- The strata of the seven variables: the older components of the Northern Cities Shift,
stabilized across the suburbs, the newer changes more advanced near the urban centre, and
negative concord. -/
inductive Stratum
  | older
  | newer
  | negativeConcord
  deriving DecidableEq, Repr, Fintype

/-- The leaders of Figure 1: the older changes are used predominantly by girls, the newer
urban changes and negative concord by burnouts. -/
def Leads (g : Group) : Stratum → Prop
  | .older => g.gender = .girl
  | .newer => g.orientation = .burnout
  | .negativeConcord => g.orientation = .burnout

instance (g : Group) : DecidablePred (Leads g)
  | .older => inferInstanceAs (Decidable (g.gender = .girl))
  | .newer => inferInstanceAs (Decidable (g.orientation = .burnout))
  | .negativeConcord => inferInstanceAs (Decidable (g.orientation = .burnout))

/-- The burnout girls lead every variable. -/
theorem burnoutGirls_lead : ∀ s, Leads ⟨.girl, .burnout⟩ s := by
  intro s; cases s <;> rfl

/-- They are the only group that does: the two leaderships cross gender with orientation,
the urban–suburban opposition embedded within the school. -/
theorem leads_all_iff (g : Group) : (∀ s, Leads g s) ↔ g = ⟨.girl, .burnout⟩ := by
  constructor
  · intro h
    have h1 : g.gender = .girl := h .older
    have h2 : g.orientation = .burnout := h .newer
    cases g; cases h1; cases h2; rfl
  · rintro rfl s; cases s <;> rfl

/-- The jock boys lead nothing. -/
theorem jockBoys_lead_none : ∀ s, ¬ Leads ⟨.boy, .jock⟩ s := by
  intro s; cases s <;> decide

end Eckert2008
