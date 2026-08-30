import Mathlib.Tactic.DeriveFintype
import Linglib.Semantics.Degree.Hom
import Linglib.Data.Examples.Bale2008

/-!
# Bale 2008: a universal scale of comparison

One interpretation of the comparative serves both indirect comparisons (*Esme is more
beautiful than Einstein is intelligent*) and direct ones (*Seymour is taller than he is
wide*). A gradable adjective ranks the comparison class; the ranking's classes form the
primary scale; and each class is sent to the universal degree that records its relative
position, a fraction with the number of classes as denominator. The comparative says that the
subject's universal degree exceeds the standard's, whatever the two scales. Adding members
equivalent to existing ones changes no degree, since classes, not members, are counted. A
direct comparison is what results when measurements — inches, treated as individuals — belong
to both comparison classes: each class then holds exactly one measurement, both scales take the
same values, and comparing universal degrees is comparing measurements. A for-phrase or a
modified nominal restricts the comparison class to people, drops the measurements, and forces
an indirect comparison: Seymour, the shortest of the men but as wide as the widest, is taller
than he is wide yet not taller for a man than he is wide for a man.

## Main definitions

* `Member`, `beauty`, `intelligence`: the ten-member committee and its two rankings;
  `Member'`, `beautyTwin`, `intelligenceTwin`: the expanded committee, each new member as
  beautiful and as intelligent as an original one.
* `Person`, `height`, `width`: the seven people together with the measurements up to eighty
  inches, ranked by height and width in inches.
* `heightClass`, `widthClass`: the nineteen men ranked among themselves.

## Main results

* `committee`: the two committee sentences' truth values; `expanded`: the expanded committee
  assigns every member the degree it had.
* `direct_comparison`, `seymour`: with measurements in both scales universal degrees compare
  as measurements do, so Seymour is taller than he is wide.
* `not_more_of_least_of_greatest`, `for_a_man`: a subject lowest on its scale is never more
  than a standard highest on its own, so Seymour is not taller for a man than he is wide for
  a man.
* `rows_truth`: the paper's evaluated sentences take the truth values it reports.

## References

* [bale-2008]
* [cresswell-1976] — scales as quotients of a comparison relation
* [klein-1980] — comparison classes and the delineation alternative
* [kennedy-1999] — the measure-function interpretation and the comparative
* [bartsch-vennemann-1972] — comparisons of deviation
* [fox-hackl-2006] — density of the universal scale
-/

namespace Bale2008

open Data.Examples Degree

/-! ### The comparative -/

/-- *x is more ADJ₁ than y is ADJ₂*: the subject's universal degree on its scale exceeds the
    standard's on its own. -/
def More {α β : Type*} (μ₁ : α → ℚ) (x : α) (μ₂ : β → ℚ) (y : β) : Prop := μ₂ y < μ₁ x

/-- A subject ranked lowest on its scale is never more than a standard ranked highest on its
    own: its degree is at most one over the number of classes and the standard's is one. -/
theorem not_more_of_least_of_greatest {α β D D' : Type*} [Fintype α] [Fintype β]
    [LinearOrder D] [LinearOrder D'] (rank₁ : α → D) (rank₂ : β → D') {x : α} {y : β}
    (hx : ∀ z, rank₁ x ≤ rank₁ z) (hy : ∀ z, rank₂ z ≤ rank₂ y) :
    ¬ More (universalDegree rank₁) x (universalDegree rank₂) y := by
  rw [More, universalDegree_of_forall_le rank₂ hy, universalDegree_of_forall_ge rank₁ hx,
    not_lt, div_le_one]
  · exact_mod_cast Finset.card_pos.2 ⟨rank₁ x, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  · exact_mod_cast Finset.card_pos.2 ⟨rank₁ x, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

/-! ### The committee -/

/-- The ten committee members; `b` is Betty, `e` Evelin, `h` Heather. -/
inductive Member
  | a | b | c | d | e | f | g | h | i | j
  deriving DecidableEq, Fintype, Repr

/-- The ranking by beauty, most beautiful highest: a, b, c, d, e, f, g, h, i, j. -/
def beauty : Member → Fin 10
  | .a => 9 | .b => 8 | .c => 7 | .d => 6 | .e => 5
  | .f => 4 | .g => 3 | .h => 2 | .i => 1 | .j => 0

/-- The ranking by intelligence, most intelligent highest: i, f, j, g, h, a, d, b, e, c. -/
def intelligence : Member → Fin 10
  | .i => 9 | .f => 8 | .j => 7 | .g => 6 | .h => 5
  | .a => 4 | .d => 3 | .b => 2 | .e => 1 | .c => 0

theorem beauty_surjective : Function.Surjective beauty := by decide

theorem intelligence_surjective : Function.Surjective intelligence := by decide

/-- With no ties, a member's universal degree is one plus the number below them, over ten. -/
theorem universalDegree_beauty (m : Member) :
    universalDegree beauty m = ((beauty m).val + 1 : ℚ) / 10 := by
  rw [universalDegree_of_surjective beauty_surjective, relativeRank_fin]; rfl

theorem universalDegree_intelligence (m : Member) :
    universalDegree intelligence m = ((intelligence m).val + 1 : ℚ) / 10 := by
  rw [universalDegree_of_surjective intelligence_surjective, relativeRank_fin]; rfl

/-- Betty, second most beautiful, is more beautiful for a committee member than Heather, fifth
    most intelligent, is intelligent; Betty, third least intelligent, is not more intelligent
    than Evelin, fifth most beautiful, is beautiful. -/
theorem committee :
    More (universalDegree beauty) .b (universalDegree intelligence) .h ∧
    ¬ More (universalDegree intelligence) .b (universalDegree beauty) .e := by
  simp only [More, universalDegree_beauty, universalDegree_intelligence, beauty, intelligence]
  norm_num

/-- The expanded committee: five further members, each as beautiful and as intelligent as one
    of the original ten. -/
inductive Member'
  | old (m : Member) | a' | b' | c' | d' | e'
  deriving DecidableEq, Fintype, Repr

/-- The original member each is as beautiful as: a′ and b′ as Betty, c′ as c, d′ as d, e′ as
    Evelin. -/
def beautyTwin : Member' → Member
  | .old m => m | .a' => .b | .b' => .b | .c' => .c | .d' => .d | .e' => .e

/-- The original member each is as intelligent as: a′ as Heather, b′ and c′ as Betty, d′ as f,
    e′ as Evelin. -/
def intelligenceTwin : Member' → Member
  | .old m => m | .a' => .h | .b' => .b | .c' => .b | .d' => .f | .e' => .e

/-- Every member of the expanded committee keeps the degree of the original member they match,
    on both scales: the quotient absorbs the newcomers into existing classes. -/
theorem expanded (m : Member') :
    universalDegree (beauty ∘ beautyTwin) m = universalDegree beauty (beautyTwin m) ∧
    universalDegree (intelligence ∘ intelligenceTwin) m =
      universalDegree intelligence (intelligenceTwin m) :=
  ⟨universalDegree_comp_of_surjective beauty (λ m => ⟨.old m, rfl⟩) m,
   universalDegree_comp_of_surjective intelligence (λ m => ⟨.old m, rfl⟩) m⟩

/-! ### Measurements -/

/-- The seven people of the height-and-width situation; `s` is Seymour. -/
inductive Person
  | a | b | c | d | e | f | s
  deriving DecidableEq, Fintype, Repr

/-- The height ranking over people and the measurements from one to eighty inches, in inches
    above one: a six foot three, b six foot two, c six foot, d, e and f five foot ten, Seymour
    five foot two, and each measurement itself. -/
def height : Person ⊕ Fin 80 → Fin 80
  | .inl .a => 74 | .inl .b => 73 | .inl .c => 71 | .inl .d => 69 | .inl .e => 69 | .inl .f => 69
  | .inl .s => 61 | .inr m => m

/-- The width ranking: Seymour three feet, f two foot five, b two foot two, the rest two foot
    one, and each measurement itself. -/
def width : Person ⊕ Fin 80 → Fin 80
  | .inl .s => 35 | .inl .f => 28 | .inl .b => 25 | .inl .a => 24 | .inl .c => 24 | .inl .d => 24
  | .inl .e => 24 | .inr m => m

theorem height_surjective : Function.Surjective height := λ m => ⟨.inr m, rfl⟩

theorem width_surjective : Function.Surjective width := λ m => ⟨.inr m, rfl⟩

/-- Each class of either scale holds exactly one measurement, so the two scales take the same
    values and comparing universal degrees is comparing measurements: a direct comparison. -/
theorem direct_comparison (x y : Person ⊕ Fin 80) :
    More (universalDegree height) x (universalDegree width) y ↔ width y < height x :=
  universalDegree_lt_iff_of_image_eq
    (by rw [Finset.image_univ_of_surjective width_surjective,
      Finset.image_univ_of_surjective height_surjective]) y x

/-- Seymour's universal degrees are his measurements over eighty, so he is taller than he is
    wide and not wider than he is tall. -/
theorem seymour_measured :
    universalDegree height (.inl .s) = 62 / 80 ∧ universalDegree width (.inl .s) = 36 / 80 ∧
    More (universalDegree height) (.inl .s) (universalDegree width) (.inl .s) ∧
    ¬ More (universalDegree width) (.inl .s) (universalDegree height) (.inl .s) := by
  rw [universalDegree_of_surjective height_surjective, universalDegree_of_surjective
    width_surjective, relativeRank_fin, relativeRank_fin, More, More,
    universalDegree_of_surjective height_surjective, universalDegree_of_surjective
    width_surjective, relativeRank_fin, relativeRank_fin]
  simp only [height, width]
  norm_num

/-! ### For a man -/

/-- The nineteen men, Seymour last. -/
abbrev Man := Fin 19

/-- Seymour. -/
def seymour : Man := 18

/-- The height classes of the men: Seymour alone in the lowest of eight. The text fixes only
    that every other man is taller; their classes reproduce the eight levels of the paper's
    figure. -/
def heightClass (m : Man) : Fin 8 := if m = seymour then 0 else ⟨m.val % 7 + 1, by omega⟩

/-- The width classes of the men: Seymour and one other man in the highest of seven. -/
def widthClass (m : Man) : Fin 7 := if m = seymour ∨ m = 8 then 6 else ⟨m.val % 6, by omega⟩

theorem seymour_shortest (m : Man) : heightClass seymour ≤ heightClass m := by
  revert m; decide

theorem seymour_widest (m : Man) : widthClass m ≤ widthClass seymour := by
  revert m; decide

/-- Restricted to men, Seymour's height degree is one eighth and his width degree one, so he
    is not taller for a man than he is wide for a man, though five feet exceeds three. -/
theorem for_a_man :
    universalDegree heightClass seymour = 1 / 8 ∧ universalDegree widthClass seymour = 1 ∧
    ¬ More (universalDegree heightClass) seymour (universalDegree widthClass) seymour := by
  refine ⟨?_, universalDegree_of_forall_le _ seymour_widest,
    not_more_of_least_of_greatest _ _ seymour_shortest seymour_widest⟩
  rw [universalDegree_of_forall_ge _ seymour_shortest]
  decide +kernel

/-! ### The rows -/

/-- A committee member by name. -/
def Member.parse? : String → Option Member
  | "a" => some .a | "b" => some .b | "c" => some .c | "d" => some .d | "e" => some .e
  | "f" => some .f | "g" => some .g | "h" => some .h | "i" => some .i | "j" => some .j
  | _ => none

/-- A person of the measured situation by name. -/
def Person.parse? : String → Option Person
  | "a" => some .a | "b" => some .b | "c" => some .c | "d" => some .d | "e" => some .e
  | "f" => some .f | "s" => some .s | _ => none

/-- The universal degree a row assigns one of its participants, by model and scale. -/
def degree? (r : LinguisticExample) (who scale : String) : Option ℚ :=
  match r.feature? "model", r.feature? scale, r.feature? who with
  | some "committee", some "beauty", some n => (Member.parse? n).map (universalDegree beauty)
  | some "committee", some "intelligence", some n =>
    (Member.parse? n).map (universalDegree intelligence)
  | some "measured", some "height", some n =>
    (Person.parse? n).map λ p => universalDegree height (.inl p)
  | some "measured", some "width", some n =>
    (Person.parse? n).map λ p => universalDegree width (.inl p)
  | some "men", some "height", some "s" => some (universalDegree heightClass seymour)
  | some "men", some "width", some "s" => some (universalDegree widthClass seymour)
  | _, _, _ => none

/-- The truth value the paper reports. -/
def truth? (r : LinguisticExample) : Option Bool :=
  match r.feature? "truth" with
  | some "true" => some true
  | some "false" => some false
  | _ => none

/-- Every sentence the paper evaluates in one of its situations has the truth value it reports:
    the subject's universal degree exceeds the standard's exactly when the paper says the
    sentence is true. -/
theorem rows_truth :
    ∀ r ∈ Examples.all, ∀ t ∈ truth? r, ∀ d₁ ∈ degree? r "subject" "subjectScale",
      ∀ d₂ ∈ degree? r "standard" "standardScale", (d₂ < d₁ ↔ t = true) := by
  decide +kernel

end Bale2008
