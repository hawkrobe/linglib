import Mathlib.Tactic.FinCases
import Linglib.Phonology.Constraints.Profile

/-!
# Steriade (1997): Lexical Conservatism

This file formalizes [steriade-1997]'s lexical conservatism, a family of grammatical
conditions against phonologically novel forms: a property of the allomorph under evaluation
must have a precedent in some listed allomorph of the same morpheme. The Lex(P) conditions
(`lexP`) require a precedent for a phonological property, and the Lex(P, M) conditions
(`lexPM`) require the target to share a property with a listed allomorph bearing a
morphosyntactic feature the target must encode; unlike the correspondence conditions of
[mccarthy-prince-1995], both search the whole paradigm rather than compare with one base,
and the morphosyntactic base is only the listed allomorph carrying the required features
(`IsBase`). Listed allomorphs are conservative by construction (`lexP_of_mem`), and with a
single listed allomorph every precedent is that base (`lexP_singleton`), one of the sources
of the appearance of single-base derivation.

The split-base effect arises when a phonological property is desirable in a novel form but
absent from the morphosyntactic base and present in another listed allomorph: the novel form
adopts the property from the second allomorph and a property identifying the base from the
first, and satisfies the precedent condition, the phonological constraint and the
base-identity condition at once, whereas each listed allomorph violates one of them
(`split_base`). The forms compete under the ranking schema in which the precedent condition
and the phonological constraint outrank the base-identity condition
(`split_wins_of_phono_over_lexPM`), and the base-faithful form wins under the reverse
ranking (`base_wins_of_lexPM_over_phono`). The French masculine liaison allomorph of *vain*,
the masculine vowel with the feminine consonant, is the split-base form for speakers who
rank identity of the accented vowel to the masculine above identity of the whole rime to a
listed allomorph; the feminine form wins for the others (`vain_split`, `vain_feminine`). The
English *-able* adjective on *remedy* adopts the stress of *remedial* to avoid a lapse for
speakers who rank the lapse constraint above stress identity to the verbal allomorph, and
keeps the verb's stress for the others, while *parody*, with no listed amphibrachic
allomorph, admits only the lapsed form (`remediable`, `parodiable`).

## Implementation notes

The listed allomorphs are treated as categorical, as the paper does, and only the properties
the analysed conditions mention are represented: the accented vowel, the final consonant and
the gender of a French adjective form, the stress pattern and the lexical category of an
English stem allomorph. The paper's survey of *-able* forms, in which the accentually
heterogeneous paradigms take the stress of the non-verbal allomorph in most responses and
the homogeneous ones keep the verb's stress, and its corpus of 186 forms, are described and
not reproduced. The lapse constraint is the paper's three-stressless-syllable version.

## References

* [steriade-1997]
* [mccarthy-prince-1995]
* [prince-1983]
-/

namespace Steriade1997

open Constraints

/-! ### Lexical conservatism conditions -/

section Conditions

variable {Form : Type*} (L : List Form) (P Q M : Form → Prop) [DecidablePred P]
  [DecidablePred Q] [DecidablePred M]

/-- Lex(P), the paper's (7): the target allomorph has the property `P` only if some listed
allomorph of the morpheme has it. -/
def lexP : Constraint Form := Constraint.binary λ t => P t ∧ ∀ l ∈ L, ¬ P l

/-- Lex(P, M), the paper's (9): the target has the property `P` if some listed allomorph has
`P` and the morphosyntactic feature `M` the target must encode. -/
def lexPM : Constraint Form := Constraint.binary λ t => (∃ l ∈ L, P l ∧ M l) ∧ ¬ P t

/-- A phonological well-formedness constraint demanding the property `P`. -/
def wellFormed : Constraint Form := Constraint.binary λ t => ¬ P t

/-- The morphosyntactically appropriate base, the paper's (12): a listed allomorph with the
required features. -/
def IsBase (b : Form) : Prop := b ∈ L ∧ M b

theorem lexP_eq_zero_iff (t : Form) : lexP L P t = 0 ↔ (P t → ∃ l ∈ L, P l) := by
  simp [lexP, Constraint.binary]

theorem lexPM_eq_zero_iff (t : Form) : lexPM L P M t = 0 ↔ ((∃ l ∈ L, P l ∧ M l) → P t) := by
  simp [lexPM, Constraint.binary]

theorem wellFormed_eq_zero_iff (t : Form) : wellFormed P t = 0 ↔ P t := by
  simp [wellFormed, Constraint.binary]

/-- A listed allomorph never violates a Lex(P) condition. -/
theorem lexP_of_mem {t : Form} (h : t ∈ L) : lexP L P t = 0 :=
  (lexP_eq_zero_iff L P t).mpr λ hp => ⟨t, h, hp⟩

/-- With a single listed allomorph, a precedent is identity to that allomorph: the
appearance of single-base derivation from an impoverished paradigm. -/
theorem lexP_singleton (b t : Form) : lexP [b] P t = 0 ↔ (P t → P b) := by
  simp [lexP_eq_zero_iff]

/-! ### The split-base effect -/

/-- The constraints of the paper's (30): the precedent condition for the desired property
`P`, the phonological constraint demanding it, and the base-identity condition for the
property `Q` of the listed allomorphs carrying the feature `M`. -/
def con30 : CON Form 3 := ![lexP L P, wellFormed P, lexPM L Q M]

/-- The reverse ranking, with the base-identity condition above the phonological one. -/
def con30' : CON Form 3 := ![lexP L P, lexPM L Q M, wellFormed P]

/-- The profile of a form under the ranking of (30), constraint by constraint. -/
theorem con30_profile (t : Form) :
    buildViolationProfile (con30 L P Q M) t =
      toLex ![lexP L P t, wellFormed P t, lexPM L Q M t] := by
  rw [buildViolationProfile, Core.Optimization.Evaluation.lexFinNatOf, toLex_inj]
  funext i; fin_cases i <;> rfl

theorem con30'_profile (t : Form) :
    buildViolationProfile (con30' L P Q M) t =
      toLex ![lexP L P t, lexPM L Q M t, wellFormed P t] := by
  rw [buildViolationProfile, Core.Optimization.Evaluation.lexFinNatOf, toLex_inj]
  funext i; fin_cases i <;> rfl

theorem lexPM_eq_one {μ t : Form} (h : μ ∈ L) (hP : P μ) (hM : M μ) (ht : ¬ P t) :
    lexPM L P M t = 1 := by
  simp [lexPM, Constraint.binary, ht]; exact ⟨μ, h, hP, hM⟩

theorem wellFormed_eq_one {t : Form} (ht : ¬ P t) : wellFormed P t = 1 := by
  simp [wellFormed, Constraint.binary, ht]

/-- The split-base effect, the paper's (11): with a listed allomorph `μ₁` carrying `M` and
the identifying property `Q` but not `P`, and another `μ₂` with `P` but not `Q`, a novel
form with `P` and `Q` violates none of the three constraints, while `μ₁` violates the
phonological constraint and `μ₂` the base-identity condition. -/
theorem split_base {μ₁ μ₂ t : Form} (h₁ : μ₁ ∈ L) (hM₁ : M μ₁) (hQ₁ : Q μ₁) (hP₁ : ¬ P μ₁)
    (h₂ : μ₂ ∈ L) (hP₂ : P μ₂) (hQ₂ : ¬ Q μ₂) (hPt : P t) (hQt : Q t) :
    buildViolationProfile (con30 L P Q M) t = toLex ![0, 0, 0] ∧ wellFormed P μ₁ = 1 ∧
      lexPM L Q M μ₂ = 1 :=
  ⟨by rw [con30_profile, (lexP_eq_zero_iff L P t).mpr λ _ => ⟨μ₂, h₂, hP₂⟩,
      (wellFormed_eq_zero_iff P t).mpr hPt, (lexPM_eq_zero_iff L Q M t).mpr λ _ => hQt],
    wellFormed_eq_one P hP₁, lexPM_eq_one L Q M h₁ hQ₁ hM₁ hQ₂⟩

/-- Under the ranking of (30) the form adopting `P` from a non-base allomorph beats the form
faithful to the base's `Q` but lacking `P`. -/
theorem split_wins_of_phono_over_lexPM {μ₁ μ₂ a b : Form} (h₁ : μ₁ ∈ L) (hM₁ : M μ₁)
    (hQ₁ : Q μ₁) (h₂ : μ₂ ∈ L) (hP₂ : P μ₂) (hPa : P a) (hQa : ¬ Q a) (hPb : ¬ P b)
    (hQb : Q b) :
    buildViolationProfile (con30 L P Q M) a < buildViolationProfile (con30 L P Q M) b := by
  rw [con30_profile, con30_profile, (lexP_eq_zero_iff L P a).mpr λ _ => ⟨μ₂, h₂, hP₂⟩,
    (wellFormed_eq_zero_iff P a).mpr hPa, lexPM_eq_one L Q M h₁ hQ₁ hM₁ hQa,
    (lexP_eq_zero_iff L P b).mpr λ h => absurd h hPb, wellFormed_eq_one P hPb,
    (lexPM_eq_zero_iff L Q M b).mpr λ _ => hQb]
  decide

/-- Under the reverse ranking the base-faithful form wins. -/
theorem base_wins_of_lexPM_over_phono {μ₁ μ₂ a b : Form} (h₁ : μ₁ ∈ L) (hM₁ : M μ₁)
    (hQ₁ : Q μ₁) (h₂ : μ₂ ∈ L) (hP₂ : P μ₂) (hPa : P a) (hQa : ¬ Q a) (hPb : ¬ P b)
    (hQb : Q b) :
    buildViolationProfile (con30' L P Q M) b < buildViolationProfile (con30' L P Q M) a := by
  rw [con30'_profile, con30'_profile, (lexP_eq_zero_iff L P a).mpr λ _ => ⟨μ₂, h₂, hP₂⟩,
    (wellFormed_eq_zero_iff P a).mpr hPa, lexPM_eq_one L Q M h₁ hQ₁ hM₁ hQa,
    (lexP_eq_zero_iff L P b).mpr λ h => absurd h hPb, wellFormed_eq_one P hPb,
    (lexPM_eq_zero_iff L Q M b).mpr λ _ => hQb]
  decide

end Conditions

/-! ### French liaison -/

section French

/-- Grammatical gender. -/
inductive Gender
  | masculine
  | feminine
  deriving DecidableEq, Repr

/-- A form of a French adjective, by the properties the liaison analysis mentions: whether
its accented vowel is nasal, whether it ends in a consonant, and its gender. -/
structure Adjective where
  nasalVowel : Bool
  finalC : Bool
  gender : Gender
  deriving DecidableEq, Repr

/-- The listed allomorphs of *vain*: the citation masculine, a nasal vowel with no final
consonant, and the citation feminine, an oral vowel with a final consonant. -/
def vainListed : List Adjective := [⟨true, false, .masculine⟩, ⟨false, true, .feminine⟩]

/-- The masculine liaison candidates: the citation masculine, the citation feminine, and the
split-base blend of the masculine vowel with the feminine consonant. -/
def vainMasc : Adjective := ⟨true, false, .masculine⟩
def vainFem : Adjective := ⟨false, true, .masculine⟩
def vainBlend : Adjective := ⟨true, true, .masculine⟩

/-- Lex C], the paper's (8): the final consonant needs a listed precedent. -/
def lexC : Constraint Adjective := lexP vainListed (·.finalC = true)

/-- Hiatus avoidance before a vowel-initial noun. -/
def noHiatus : Constraint Adjective := wellFormed (·.finalC = true)

/-- Lex 'V-gender, the paper's (10): the accented vowel is identical to that of a listed
allomorph of the same gender. -/
def lexVGender : Constraint Adjective :=
  lexPM vainListed (·.nasalVowel = true) (·.gender = .masculine)

/-- Lex σ': the accented syllable, here the rime, is identical in its entirety to that of
some listed allomorph. -/
def lexSyllable : Constraint Adjective :=
  Constraint.binary λ t => ∀ l ∈ vainListed, (l.nasalVowel, l.finalC) ≠ (t.nasalVowel, t.finalC)

/-- Speakers ranking Lex 'V-gender above Lex σ' select the split-base form *[vɛ̃n] espoir*
over both citation forms. -/
theorem vain_split :
    let con : CON Adjective 4 := ![lexC, noHiatus, lexVGender, lexSyllable]
    buildViolationProfile con vainBlend < buildViolationProfile con vainMasc ∧
      buildViolationProfile con vainBlend < buildViolationProfile con vainFem := by
  decide

/-- Speakers ranking Lex σ' above Lex 'V-gender select the citation feminine *[vɛn] espoir*. -/
theorem vain_feminine :
    let con : CON Adjective 4 := ![lexC, noHiatus, lexSyllable, lexVGender]
    buildViolationProfile con vainFem < buildViolationProfile con vainMasc ∧
      buildViolationProfile con vainFem < buildViolationProfile con vainBlend := by
  decide

end French

/-! ### English *-able* -/

section English

/-- The stress patterns of a trisyllabic stem allomorph. -/
inductive Stress
  | dactyl
  | amphibrach
  deriving DecidableEq, Repr

/-- Lexical category of a listed allomorph. -/
inductive LexCat
  | verb
  | adjective
  deriving DecidableEq, Repr

/-- A stem allomorph by its stress pattern and lexical category. -/
structure Stem where
  stress : Stress
  lexcat : LexCat
  deriving DecidableEq, Repr

/-- The listed allomorphs of *remedy*: the dactylic verb *rémedy* and the amphibrachic
adjective stem of *remédial*, the paper's (13). -/
def remedyListed : List Stem := [⟨.dactyl, .verb⟩, ⟨.amphibrach, .adjective⟩]

/-- The listed allomorphs of *parody*: only the dactylic verb. -/
def parodyListed : List Stem := [⟨.dactyl, .verb⟩]

/-- The *-able* stem is verbal; the candidates differ in stress. -/
def dactylAble : Stem := ⟨.dactyl, .verb⟩
def amphibrachAble : Stem := ⟨.amphibrach, .verb⟩

/-- Lex [±stress], the paper's (15): the stress pattern needs a listed precedent. -/
def lexStress (L : List Stem) : Constraint Stem := lexP L (·.stress = .amphibrach)

/-- *Lapse σσσ: three stressless syllables before *-able* are avoided, so the stem must shift
its stress rightward. -/
def noLapse : Constraint Stem := wellFormed (·.stress = .amphibrach)

/-- Lex([±stress], lexcat), the paper's (17): the stress pattern of the verbal target matches
that of a listed verbal allomorph. -/
def lexStressLexcat (L : List Stem) : Constraint Stem :=
  lexPM L (·.stress = .dactyl) (·.lexcat = .verb)

/-- *remédiable* wins under the ranking Lex [±stress] ≫ *Lapse ≫ Lex([±stress], lexcat) and
*rémediable* under Lex [±stress] ≫ Lex([±stress], lexcat) ≫ *Lapse, the paper's (18). -/
theorem remediable :
    buildViolationProfile (con30 remedyListed (·.stress = .amphibrach) (·.stress = .dactyl)
        (·.lexcat = .verb)) amphibrachAble <
      buildViolationProfile (con30 remedyListed (·.stress = .amphibrach) (·.stress = .dactyl)
        (·.lexcat = .verb)) dactylAble ∧
    buildViolationProfile (con30' remedyListed (·.stress = .amphibrach) (·.stress = .dactyl)
        (·.lexcat = .verb)) dactylAble <
      buildViolationProfile (con30' remedyListed (·.stress = .amphibrach) (·.stress = .dactyl)
        (·.lexcat = .verb)) amphibrachAble := by
  decide

/-- With no amphibrachic allomorph listed, *paródiable* violates Lex [±stress], so
*párodiable* wins under either ranking despite its lapse. -/
theorem parodiable :
    buildViolationProfile (con30 parodyListed (·.stress = .amphibrach) (·.stress = .dactyl)
        (·.lexcat = .verb)) dactylAble <
      buildViolationProfile (con30 parodyListed (·.stress = .amphibrach) (·.stress = .dactyl)
        (·.lexcat = .verb)) amphibrachAble ∧
    buildViolationProfile (con30' parodyListed (·.stress = .amphibrach) (·.stress = .dactyl)
        (·.lexcat = .verb)) dactylAble <
      buildViolationProfile (con30' parodyListed (·.stress = .amphibrach) (·.stress = .dactyl)
        (·.lexcat = .verb)) amphibrachAble := by
  decide

end English

end Steriade1997
