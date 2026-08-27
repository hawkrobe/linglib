import Mathlib.Data.Fintype.Powerset
import Linglib.Semantics.Quantification.Generators
import Linglib.Studies.AlonsoOvalleMenendezBenito2010
import Linglib.Data.Examples.AlonsoOvalleMoghiseh2025b

/-!
# Alonso-Ovalle & Moghiseh (2025): number marking in Farsi *what* interrogatives

Farsi singular *what* interrogatives, bare (*chi*) and complex (*che ketab-i*), allow both
singular and plural answers (20), (23); with the differential object marker *-ro* only the
bare ones do (26)–(27). The paper derives this from three assumptions: interrogatives range
over the conjunctions and disjunctions of nonempty subdomains (29), built with the
`Quantification.conjGQ`/`disjGQ` generators (`hamblin`, `mem_conjProp`); singular marking on
bare interrogatives is a default over atoms and pluralities (37), while SING on complex
interrogatives keeps atoms only (42) (`neutral`, `atoms`); and *-ro* restricts the subset
selection function to singletons (52), the `IsSingleton` functions of
[alonso-ovalle-menendez-benito-2010], which collapses ⊓ and ⊔ to individual answers
(`hamblinRo`, `hamblinRo_neutral`). Dayal's answerhood operator (8) presupposes a maximally
strong true answer (`Resolvable`); a plural answer is available iff the presupposition holds
in a world where two atoms were bought (`farsi`, (40)/(45)/(53)/(55)).

The background pattern of §2 — English bare vs. singular and plural complex interrogatives
under Dayal's atoms-only domains and the presuppositional exhaustifier (15) — is
`dayal_english`, and the generalized-quantifier answer to the Spanish bare-interrogative
problem (19) is `spanish_gq`. Questions with *must* (30)–(36) are answerable by free
choice disjunctions only when the interrogative ranges over disjunctions, which *-ro*
removes (`modal_gq`, (58)–(63)); collective predicates need pluralities in the domain
(`collective`, (56)–(57)). The paper's answer judgments are checked in `rows_agree`.

## References

* [alonso-ovalle-moghiseh-2025b]
* [dayal-1996]
* [dayal-2016]
* [hamblin-1973b]
* [maldonado-2020]
* [elliott-nicolae-sauerland-2022]
* [alonso-ovalle-rouillard-2023]
* [scontras-2022]
* [alonso-ovalle-menendez-benito-2010]
-/

namespace AlonsoOvalleMoghiseh2025b

open Quantification Data.Examples Finset

/-! ### Entities, worlds, and answers -/

/-- The atomic things; an entity is a nonempty sum of atoms and a world records which atoms
Roya bought. -/
abbrev Atom := Fin 2

abbrev Entity := Finset Atom

abbrev World := Finset Atom

/-- Distributive *bought*: every atom of the entity was bought. -/
def bought (e : Entity) (w : World) : Prop := e ⊆ w

instance (e : Entity) : DecidablePred (bought e) := fun w => inferInstanceAs (Decidable (e ⊆ w))

theorem bought_union (e₁ e₂ : Entity) (w : World) :
    bought (e₁ ∪ e₂) w ↔ bought e₁ w ∧ bought e₂ w := Finset.union_subset_iff

/-- The number-neutral root (37): atoms and pluralities. -/
def neutral : Finset Entity := univ.filter (·.Nonempty)

/-- SING (42): the atoms. -/
def atoms : Finset Entity := univ.filter (·.card = 1)

/-! ### Hamblin sets over generalized quantifiers (29) -/

variable {W : Type*} [Fintype W] [DecidableEq W] (P : Entity → W → Prop)
  [∀ e, DecidablePred (P e)]

/-- The proposition that the conjunction ⊓X holds of `P`. -/
def conjProp (X : Finset Entity) : Finset W := univ.filter fun w => ∀ e ∈ X, P e w

/-- The proposition that the disjunction ⊔X holds of `P`. -/
def disjProp (X : Finset Entity) : Finset W := univ.filter fun w => ∃ e ∈ X, P e w

omit [DecidableEq W] in
theorem mem_conjProp (X : Finset Entity) (w : W) :
    w ∈ conjProp P X ↔ conjGQ X.toList (P · w) := by
  simp [conjProp, conjGQ_iff_forall]

omit [DecidableEq W] in
theorem mem_disjProp (X : Finset Entity) (w : W) :
    w ∈ disjProp P X ↔ disjGQ X.toList (P · w) := by
  simp [disjProp, disjGQ_iff_exists]

/-- The Hamblin set (29): ⊓ and ⊔ over every nonempty subdomain of `D`, applied to `P`. -/
def hamblin (D : Finset Entity) : Finset (Finset W) :=
  (D.powerset.filter (·.Nonempty)).image (conjProp P) ∪
    (D.powerset.filter (·.Nonempty)).image (disjProp P)

/-- With *-ro* (52) the selection function returns a singleton, so the Hamblin set is the
union of the Hamblin sets over the singleton subdomains. -/
def hamblinRo (D : Finset Entity) : Finset (Finset W) := D.biUnion fun e => hamblin P {e}

/-- Dayal's exhaustivity presupposition (8): some true member of the Hamblin set entails
every true member. -/
def Resolvable (H : Finset (Finset W)) (w : W) : Prop :=
  ∃ p ∈ H, w ∈ p ∧ ∀ q ∈ H, w ∈ q → p ⊆ q

instance (H : Finset (Finset W)) (w : W) : Decidable (Resolvable H w) :=
  inferInstanceAs (Decidable (∃ p ∈ H, _ ∧ ∀ q ∈ H, _ → _))

/-- The worlds where the question's presupposition holds. -/
def dom (H : Finset (Finset W)) : Finset W := univ.filter (Resolvable H)

/-- EXHp (15): `φ` is defined and every alternative `ψ` with a stronger presupposition is
undefined. -/
def ExhP (φ ψ : Finset (Finset W)) (w : W) : Prop :=
  Resolvable φ w ∧ (dom ψ ⊂ dom φ → ¬ Resolvable ψ w)

instance (φ ψ : Finset (Finset W)) (w : W) : Decidable (ExhP φ ψ w) :=
  inferInstanceAs (Decidable (_ ∧ (_ → _)))

/-! ### The predictions -/

/-- The worlds a singular and a plural answer describe. -/
abbrev one : World := {0}
abbrev two : World := {0, 1}

/-- (53)/(55): over a singleton subdomain ⊓ and ⊔ collapse, so the *-ro* Hamblin sets contain
the individual answers only — with the plurality for the neutral domain. -/
theorem hamblinRo_neutral :
    hamblinRo bought neutral = (neutral.image fun e => univ.filter (bought e)) ∧
      hamblinRo bought atoms = atoms.image fun e => univ.filter (bought e) := by decide

/-- §2: English bare interrogatives (9)–(11) allow both answers, singular complex ones
(12)–(13) only a singular answer, and plural complex ones (14)–(15), whose singular
alternative has the stronger presupposition, only a plural one. -/
theorem dayal_english :
    (Resolvable (hamblinRo bought neutral) one ∧ Resolvable (hamblinRo bought neutral) two) ∧
      (Resolvable (hamblinRo bought atoms) one ∧ ¬ Resolvable (hamblinRo bought atoms) two) ∧
      dom (hamblinRo bought atoms) ⊂ dom (hamblinRo bought neutral) ∧
      (¬ ExhP (hamblinRo bought neutral) (hamblinRo bought atoms) one ∧
        ExhP (hamblinRo bought neutral) (hamblinRo bought atoms) two) := by decide

/-- (19): over atoms alone a Spanish singular bare interrogative wrongly presupposes
uniqueness; ranging over their conjunctions and disjunctions admits the plural answer. -/
theorem spanish_gq :
    ¬ Resolvable (hamblinRo bought atoms) two ∧ Resolvable (hamblin bought atoms) two := by
  decide

/-- (40), (45): singular bare and complex interrogatives allow both answers; (53): so does
the *-ro* bare interrogative, through the plurality; (55): the *-ro* complex interrogative
allows only the singular answer. -/
theorem farsi :
    (Resolvable (hamblin bought neutral) one ∧ Resolvable (hamblin bought neutral) two) ∧
      (Resolvable (hamblin bought atoms) one ∧ Resolvable (hamblin bought atoms) two) ∧
      (Resolvable (hamblinRo bought neutral) one ∧ Resolvable (hamblinRo bought neutral) two) ∧
      (Resolvable (hamblinRo bought atoms) one ∧ ¬ Resolvable (hamblinRo bought atoms) two) := by
  decide

/-! ### Questions with *must* (30)–(36) and collective predicates (56)–(57) -/

/-- A deontic world: the nonempty set of permitted buy-worlds. -/
abbrev Base := {A : Finset World // A.Nonempty}

instance : Fintype Base := Subtype.fintype fun A : Finset World => A.Nonempty

/-- *Must* over a proposition about buy-worlds: it holds in every permitted world. -/
def box (p : Finset World) : Finset Base := univ.filter fun A => ∀ v ∈ A.1, v ∈ p

theorem mem_box {p : Finset World} {A : Base} : A ∈ box p ↔ A.1 ⊆ p := by
  simp [box, Finset.subset_iff]

theorem box_subset_iff {p q : Finset World} : box p ⊆ box q ↔ p ⊆ q := by
  refine ⟨fun h v hv => ?_, fun h A hA => mem_box.2 ((mem_box.1 hA).trans h)⟩
  have := h (mem_box.2 (Finset.singleton_subset_iff.2 hv) :
    (⟨{v}, Finset.singleton_nonempty v⟩ : Base) ∈ box p)
  exact Finset.singleton_subset_iff.1 (mem_box.1 this)

/-- Resolvability of the modalized question at the permitted worlds `A`, stated on the
buy-world Hamblin set. -/
def ResolvableAt (H : Finset (Finset World)) (A : Finset World) : Prop :=
  ∃ p ∈ H, A ⊆ p ∧ ∀ q ∈ H, A ⊆ q → p ⊆ q

instance (H : Finset (Finset World)) (A : Finset World) : Decidable (ResolvableAt H A) :=
  inferInstanceAs (Decidable (∃ p ∈ H, _ ∧ ∀ q ∈ H, _ → _))

/-- The question with *must* is resolvable at a deontic world iff its buy-world Hamblin set
is resolvable at the permitted worlds. -/
theorem resolvable_image_box (H : Finset (Finset World)) (A : Base) :
    Resolvable (H.image box) A ↔ ResolvableAt H A.1 := by
  constructor
  · rintro ⟨_, hP, hA, hmax⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hP
    refine ⟨p, hp, mem_box.1 hA, fun q hq hAq => ?_⟩
    exact box_subset_iff.1 (hmax _ (Finset.mem_image_of_mem _ hq) (mem_box.2 hAq))
  · rintro ⟨p, hp, hA, hmax⟩
    refine ⟨box p, Finset.mem_image_of_mem _ hp, mem_box.2 hA, fun Q hQ hAQ => ?_⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hQ
    exact box_subset_iff.2 (hmax q hq (mem_box.1 hAQ))

/-- (59): Forood must buy one of two things, and either is permitted. -/
def freeChoice : Base := ⟨{{0}, {1}}, by decide⟩

/-- (35)–(36) vs. (32)–(33): with the interrogative binding into the scope of *must* (34),
only □(b₁ ∨ b₂) is true in the free-choice scenario, so the presupposition holds iff the
interrogative ranges over disjunctions — which *-ro* removes, (62)–(63). -/
theorem modal_gq :
    (Resolvable ((hamblin bought neutral).image box) freeChoice ∧
        Resolvable ((hamblin bought atoms).image box) freeChoice) ∧
      (¬ Resolvable ((hamblinRo bought neutral).image box) freeChoice ∧
        ¬ Resolvable ((hamblinRo bought atoms).image box) freeChoice) := by
  simp only [resolvable_image_box]; decide

/-- *Mixed together*: a collective predicate, true of a plurality that was bought. -/
def mixed (e : Entity) (w : World) : Prop := 2 ≤ e.card ∧ e ⊆ w

instance (e : Entity) : DecidablePred (mixed e) :=
  fun w => inferInstanceAs (Decidable (2 ≤ e.card ∧ e ⊆ w))

/-- (56)–(57): a collective predicate has a true answer over the neutral domain, with or
without *-ro*, and none over the atoms. -/
theorem collective :
    (Resolvable (hamblin mixed neutral) two ∧ Resolvable (hamblinRo mixed neutral) two) ∧
      (¬ Resolvable (hamblin mixed atoms) two ∧ ¬ Resolvable (hamblinRo mixed atoms) two) := by
  decide

/-! ### The paper's answer judgments -/

/-- The Hamblin set a row's `type`, `ro`, and `language` features name, for the
interrogatives the paper derives. -/
def hamblinOf (row : LinguisticExample) : Option (Finset (Finset World)) :=
  match row.feature? "language", row.feature? "type", row.feature? "ro" with
  | some "English", some "BI", _ => some (hamblinRo bought neutral)
  | some "English", some "SCI", _ => some (hamblinRo bought atoms)
  | some "Spanish", some "SBI", _ => some (hamblin bought atoms)
  | none, some "SBI", some "no" => some (hamblin bought neutral)
  | none, some "SCI", some "no" => some (hamblin bought atoms)
  | none, some "SBI", some "yes" => some (hamblinRo bought neutral)
  | none, some "SCI", some "yes" => some (hamblinRo bought atoms)
  | _, _, _ => none

/-- Whether a singular and a plural answer are predicted: the English plural complex
interrogative goes through EXHp against its singular alternative, the others through ANS. -/
def predicted (row : LinguisticExample) : Option (Bool × Bool) :=
  match row.feature? "language", row.feature? "type" with
  | some "English", some "PCI" =>
    some (decide (ExhP (hamblinRo bought neutral) (hamblinRo bought atoms) one),
      decide (ExhP (hamblinRo bought neutral) (hamblinRo bought atoms) two))
  | _, _ => (hamblinOf row).map fun H => (decide (Resolvable H one), decide (Resolvable H two))

/-- A row's answer judgments, read off its `singular answer`/`plural answer` readings. -/
def observed (row : LinguisticExample) : Bool × Bool :=
  (row.readings.any fun r => "singular".toList <+: r.1.toList ∧ r.2 = .acceptable,
    row.readings.any fun r => "plural".toList <+: r.1.toList ∧ r.2 = .acceptable)

/-- Every derived interrogative's answers are those the paper reports. -/
theorem rows_agree :
    ∀ row ∈ Examples.all, ∀ b, predicted row = some b →
      (row.readings.any fun r => "singular".toList <+: r.1.toList) = true → observed row = b := by
  decide +kernel

example : (Examples.all.filter fun row => (predicted row).isSome).length = 16 := by decide +kernel

/-- (60)–(63): the embedded questions are felicitous in (59) iff their interrogative ranges
over disjunctions (`resolvable_image_box` relates this to the modalized question). -/
theorem scenario_rows :
    ∀ row ∈ Examples.all, row.feature? "scenario" = some "freeChoice59" →
      (hamblinOf row).map (fun H => decide (ResolvableAt H freeChoice.1)) =
        some (row.feature? "verdict" == some "true") := by decide +kernel

end AlonsoOvalleMoghiseh2025b
