import Linglib.Data.Examples.Carstens2026
import Linglib.Fragments.Xhosa.Nouns
import Linglib.Fragments.Shona.Nouns
import Linglib.Syntax.Minimalist.Agree.Coordination
import Linglib.Studies.TaraldsenEtAl2018

/-!
# Carstens (2026): The grammar of gender

Uniform conjoined singulars of Xhosa's genders 1/2, 7/8 and 9/10 pair with gender-matching
plural agreement, those of 3/4 and 5/6 only with the semantic agreement of class 2 for humans
and class 8 for the rest, and mismatched conjuncts pattern with the latter ([carstens-2026]).
The split diagnoses interpretability: every Bantu nominal is a stacked nP, a core n bearing
one of the semantic genders, i[human], i[inanimate], i[animal] in Xhosa, i[human] and
i[non-human] in Shona, under a visible n that fixes its class; with
[adamson-anagnostopoulou-2025], the conjuncts' interpretable gender features percolate to &P
and are intersected, so a u-gender contributes nothing and only the cores can match, while an
i-gender's arbitrary members carry a bare i[entity] flavor and match with it. Two grammars
read the intersection, Highest Wins taking the shared visible gender and Best Semantic Match
the shared core, which is where the minority choices come from; where neither matches the
conjunction is ineffable. In Shona six of eight genders are uninterpretable, so matching
agreement is the exception, not the rule.

## Implementation notes

A nominal is a core gender with an optional outer gender. The visible gender's feature is
annotated with the interpretability its n carries and resolved by
`Minimalist.Coordination.resolve`, so the exclusion of u-genders is the substrate's
percolation; the cores resolve as interpretable features. A noun's core is read off the
animacy of what it denotes and its outer layer off its class, in the English fragments'
lexicons. The rows carry the paper's example sentences with the classes they accept and
reject, and the Table 13 counts on one example per cell; single-conjunct agreement, the
choices offered in at most 5% of cases and Taraldsen et al.'s Tables 4 and 6, which the paper
sets aside, are not encoded. The comparison with [halpert-hammerly-2026]'s binary features
in §8 is stated in prose only.

## References

* [carstens-2026]
* [adamson-anagnostopoulou-2025]
* [kramer-2015]
* [taraldsen-et-al-2018]
* [halpert-hammerly-2026]
-/

namespace Carstens2026

open Bantu Data.Examples Features.Prominence Minimalist.Coordination

/-- (13), (77b): whether the n of a gender carries a feature that percolates to &P. -/
def interpretability : GenderStatus → Minimalist.Interpretability
  | .interpretable _ => .interpretable
  | .uninterpretable => .uninterpretable

/-! ### Nominals and the two grammars (§4–§5) -/

section Mechanism

variable {G C : Type*} [DecidableEq G] [DecidableEq C]

/-- A Bantu nominal, (10), (72)–(73): a core nP of the gender that carries the semantic flavor of
what it denotes, wrapped, when its visible class belongs to another gender, in an outer nP of
that gender. -/
structure Nominal (G : Type*) where
  core : G
  outer : Option G := none
  deriving DecidableEq, Repr

variable (status : G → GenderStatus) (pluralClass : G → C)

namespace Nominal

variable (n : Nominal G)

/-- The visible gender, the outer layer's or the core's. -/
def visible : G := n.outer.getD n.core

/-- The visible gender's feature as percolation sees it, annotated with the interpretability of
the gender's n. -/
def visibleBundle : Bundle G := [⟨n.visible, interpretability (status n.visible)⟩]

/-- The core's feature, always interpretable. -/
def coreBundle : Bundle G := [⟨n.core, .interpretable⟩]

end Nominal

/-- Agreement valued by a resolved feature set: the plural class of its one gender. -/
def valued : Option (List G) → Option C
  | some [g] => some (pluralClass g)
  | _ => none

variable (a b : Nominal G)

/-- Highest Wins (79): the visible genders percolate and intersect, the shared gender valuing
its plural class. -/
def highestWins : Option C :=
  valued pluralClass (resolve (a.visibleBundle status) (b.visibleBundle status))

/-- Best Semantic Match (80): the cores intersect, a total match of gender with flavor, the
shared core valuing its plural class. -/
def bestSemanticMatch : Option C := valued pluralClass (resolve a.coreBundle b.coreBundle)

/-- `c` values plural agreement on &P under one of the two grammars (§5.1). -/
def Values (c : C) : Prop :=
  highestWins status pluralClass a b = some c ∨ bestSemanticMatch pluralClass a b = some c

instance (c : C) : Decidable (Values status pluralClass a b c) :=
  inferInstanceAs (Decidable (_ ∨ _))

variable {a b}

theorem highestWins_eq :
    highestWins status pluralClass a b =
      if interpretability (status a.visible) = .interpretable ∧ a.visible = b.visible then
        some (pluralClass a.visible)
      else none := by
  unfold highestWins Nominal.visibleBundle
  rw [resolve_singleton]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd ⟨h₁.1, h₁.2.2⟩ h₂
  · exact absurd ⟨h₂.1, h₂.2 ▸ h₂.1, h₂.2⟩ h₁
  · rfl

theorem bestSemanticMatch_eq :
    bestSemanticMatch pluralClass a b =
      if a.core = b.core then some (pluralClass a.core) else none := by
  unfold bestSemanticMatch Nominal.coreBundle
  simp only [resolve_singleton, true_and]
  split_ifs <;> rfl

/-- (52a–b), (54): uniform conjuncts pair with gender-matching plural agreement exactly when
their gender is interpretable. -/
theorem matching_iff (h : a.visible = b.visible) :
    highestWins status pluralClass a b = some (pluralClass a.visible) ↔
      interpretability (status a.visible) = .interpretable := by
  rw [highestWins_eq]
  by_cases hi : interpretability (status a.visible) = .interpretable
  · simp [h]
  · simp [hi]

/-- (77): a u-gender stacked above a core is ignored, the cores alone valuing agreement. -/
theorem values_iff_of_uninterpretable
    (hu : interpretability (status a.visible) = .uninterpretable) (c : C) :
    Values status pluralClass a b c ↔ bestSemanticMatch pluralClass a b = some c := by
  unfold Values
  rw [highestWins_eq]
  simp [hu]

/-- (78)–(80): an arbitrary member of an interpretable gender stacked above a core carries both
i-genders to &P, uniform conjuncts match twice, and the two grammars value the visible and the
core plural respectively. -/
theorem two_grammars {g : G} (ho : a.outer = some g)
    (hi : interpretability (status g) = .interpretable) :
    highestWins status pluralClass a a = some (pluralClass g) ∧
      bestSemanticMatch pluralClass a a = some (pluralClass a.core) := by
  have hv : a.visible = g := by simp [Nominal.visible, ho]
  rw [highestWins_eq, bestSemanticMatch_eq, hv]
  simp [hi]

/-- Single-layer conjuncts of an interpretable gender give the two grammars nothing to
disagree about. -/
theorem highestWins_eq_bestSemanticMatch (ha : a.outer = none) (hb : b.outer = none)
    (hi : interpretability (status a.core) = .interpretable) :
    highestWins status pluralClass a b = bestSemanticMatch pluralClass a b := by
  have ha' : a.visible = a.core := by simp [Nominal.visible, ha]
  have hb' : b.visible = b.core := by simp [Nominal.visible, hb]
  rw [highestWins_eq, bestSemanticMatch_eq, ha', hb']
  simp [hi]

/-- (91)–(92), (111)–(112): with neither the visible genders nor the cores matching, no class
values agreement and the conjunction is ineffable. -/
theorem not_values (hv : a.visible ≠ b.visible) (hc : a.core ≠ b.core) (c : C) :
    ¬ Values status pluralClass a b c := by
  unfold Values
  rw [highestWins_eq, bestSemanticMatch_eq]
  simp [hv, hc]

end Mechanism

/-! ### Xhosa (71)–(73) -/

/-- (71): the core genders of Xhosa's three entity types, gender A i[human], E i[animal] and
D i[inanimate]. -/
def xhosaCore : AnimacyLevel → Xhosa.Gender
  | .human => .genderA
  | .animate => .genderE
  | .inanimate => .genderD

/-- The flavor each core bears. -/
def xhosaFlavor : AnimacyLevel → SemanticCore
  | .human => .human
  | .animate => .animal
  | .inanimate => .inanimate

/-- The cores are the genders the fragment marks interpretable, with the flavors of (71). -/
theorem xhosaCore_status (a : AnimacyLevel) :
    (xhosaCore a).status = .interpretable (xhosaFlavor a) := by
  cases a <;> rfl

/-- (72)–(73): a noun's nominal, its core from what it denotes and, when its class belongs to
another gender, that gender stacked above. -/
def xhosaNominal (n : Xhosa.NounEntry) : Nominal Xhosa.Gender :=
  ⟨xhosaCore n.animacy,
    (Xhosa.Gender.ofSingular n.cls).filter λ g => decide (g ≠ xhosaCore n.animacy)⟩

/-- A class values agreement on a Xhosa &P. -/
abbrev XhosaValues (a b : Nominal Xhosa.Gender) (c : Xhosa.NounClass) : Prop :=
  Values Xhosa.Gender.status Xhosa.Gender.pluralClass a b c

/-! ### Shona (§3.5, §5.2) -/

/-- §5.2: Shona's two cores, gender A i[human] and gender D i[non-human]. -/
def shonaCore : AnimacyLevel → Shona.Gender
  | .human => .genderA
  | _ => .genderD

/-- The two cores are Shona's interpretable genders. -/
theorem shonaCore_status (a : AnimacyLevel) :
    (shonaCore a).status = .interpretable (if a = .human then .human else .nonhuman) := by
  cases a <;> rfl

/-- A Shona noun's nominal; (98): a diminutive's u-gender 12/13 stacks above its core. -/
def shonaNominal (n : Shona.NounEntry) : Nominal Shona.Gender :=
  ⟨shonaCore n.animacy,
    (Shona.Gender.ofSingular n.cls).filter λ g => decide (g ≠ shonaCore n.animacy)⟩

/-- A class values agreement on a Shona &P. -/
abbrev ShonaValues (a b : Nominal Shona.Gender) (c : Shona.NounClass) : Prop :=
  Values Shona.Gender.status Shona.Gender.pluralClass a b c

/-! ### The rows -/

/-- The values of a feature key, in order. -/
private def features (e : LinguisticExample) (key : String) : List String :=
  (e.paperFeatures.filter (·.1 = key)).map (·.2)

/-- The rows of one language. -/
def rows (glottocode : String) : List LinguisticExample :=
  Examples.all.filter (·.language = glottocode)

private def xhosaClassOf : String → Option Xhosa.NounClass
  | "2" => some .cl2
  | "4" => some .cl4
  | "6" => some .cl6
  | "8" => some .cl8
  | "10" => some .cl10
  | _ => none

private def shonaClassOf : String → Option Shona.NounClass
  | "2" => some .cl2
  | "4" => some .cl4
  | "6" => some .cl6
  | "8" => some .cl8
  | "10" => some .cl10
  | "13" => some .cl13
  | _ => none

/-- A Xhosa row's conjuncts, from the fragment's nouns. -/
def xhosaConjuncts (e : LinguisticExample) :
    Option (Nominal Xhosa.Gender × Nominal Xhosa.Gender) := do
  let a ← (e.feature? "conjunct1").bind λ s => Xhosa.Nouns.all.find? (·.form = s)
  let b ← (e.feature? "conjunct2").bind λ s => Xhosa.Nouns.all.find? (·.form = s)
  pure (xhosaNominal a, xhosaNominal b)

/-- A Shona row's conjuncts. -/
def shonaConjuncts (e : LinguisticExample) :
    Option (Nominal Shona.Gender × Nominal Shona.Gender) := do
  let a ← (e.feature? "conjunct1").bind λ s => Shona.Nouns.all.find? (·.form = s)
  let b ← (e.feature? "conjunct2").bind λ s => Shona.Nouns.all.find? (·.form = s)
  pure (shonaNominal a, shonaNominal b)

/-- The classes a Xhosa row accepts and rejects for plural agreement on &P. -/
def xhosaAccepted (e : LinguisticExample) : List Xhosa.NounClass :=
  (features e "agreement").filterMap xhosaClassOf

def xhosaRejected (e : LinguisticExample) : List Xhosa.NounClass :=
  (features e "rejected").filterMap xhosaClassOf

def shonaAccepted (e : LinguisticExample) : List Shona.NounClass :=
  (features e "agreement").filterMap shonaClassOf

def shonaRejected (e : LinguisticExample) : List Shona.NounClass :=
  (features e "rejected").filterMap shonaClassOf

/-- (6)–(9), (37)–(49), (55), (81)–(91), (111): every class a row accepts values agreement under
one of the two grammars, and none it rejects does. -/
theorem xhosa_rows :
    ∀ e ∈ rows "xhos1239", ∃ p ∈ xhosaConjuncts e,
      (∀ c ∈ xhosaAccepted e, XhosaValues p.1 p.2 c) ∧
        ∀ c ∈ xhosaRejected e, ¬ XhosaValues p.1 p.2 c := by
  decide +kernel

/-- (58)–(68): the same over the Shona rows, matching agreement confined to 1/2 and 7/8. -/
theorem shona_rows :
    ∀ e ∈ rows "shon1251", ∃ p ∈ shonaConjuncts e,
      (∀ c ∈ shonaAccepted e, ShonaValues p.1 p.2 c) ∧
        ∀ c ∈ shonaRejected e, ¬ ShonaValues p.1 p.2 c := by
  decide +kernel

/-- Table 13, (52a–b): gender-matching agreement is chosen at least as often as default
exactly in the cells whose gender is interpretable. -/
theorem table13 :
    ∀ e ∈ rows "xhos1239", ∀ m ∈ e.nat? "matching", ∀ d ∈ e.nat? "default",
      ∀ p ∈ xhosaConjuncts e,
        (d ≤ m ↔ interpretability (Xhosa.Gender.status p.1.visible) = .interpretable) := by
  decide +kernel

/-! ### Taraldsen et al.'s reading (§3.2.3) -/

/-- The same failures read structurally by [taraldsen-et-al-2018]: the genders whose singular
and plural prefixes share one classifier N are exactly the interpretable genders, the paper's
diagnostic and their partition of the Xhosa data coinciding. -/
theorem taraldsen_split (g : Xhosa.Gender) :
    interpretability g.status = .interpretable ↔
      TaraldsenEtAl2018.SharesClassifierN (TaraldsenEtAl2018.xhosaSg g)
        (TaraldsenEtAl2018.xhosaPl g) := by
  cases g <;> decide

end Carstens2026
