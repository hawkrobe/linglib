import Mathlib.Data.Fintype.Powerset
import Linglib.Semantics.Quantification.Generators
import Linglib.Semantics.Questions.Exhaustivity
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
strong true answer (`Questions.IsExhaustivelyResolvable` on the finite Hamblin set); a plural
answer is available iff the presupposition holds in a world where two atoms were bought
(`farsi`, (40)/(45)/(53)/(55)).

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

open Quantification Questions Data.Examples Finset

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

/-- The worlds where the question's presupposition (8) holds. -/
def dom (H : Finset (Finset W)) : Finset W :=
  univ.filter (IsExhaustivelyResolvable (ofFinset H))

/-- EXHp (15): `φ` is defined and every alternative `ψ` with a stronger presupposition is
undefined. -/
def ExhP (φ ψ : Finset (Finset W)) (w : W) : Prop :=
  IsExhaustivelyResolvable (ofFinset φ) w ∧
    (dom ψ ⊂ dom φ → ¬ IsExhaustivelyResolvable (ofFinset ψ) w)

instance (φ ψ : Finset (Finset W)) (w : W) : Decidable (ExhP φ ψ w) :=
  inferInstanceAs (Decidable (_ ∧ (_ → _)))

/-! ### The predictions -/

/-- The worlds a singular and a plural answer describe. -/
abbrev one : World := {0}
abbrev two : World := {0, 1}

/-- Whether a singular and a plural answer are available: the presupposition (8) holds in the
world where one atom was bought and in the world where two were. -/
def answers (H : Finset (Finset World)) : Bool × Bool :=
  (decide (IsExhaustivelyResolvable (ofFinset H) one),
    decide (IsExhaustivelyResolvable (ofFinset H) two))

/-- The answers available through EXHp (15) of `φ` against its alternative `ψ`. -/
def exhAnswers (φ ψ : Finset (Finset World)) : Bool × Bool :=
  (decide (ExhP φ ψ one), decide (ExhP φ ψ two))

/-- (53)/(55): over a singleton subdomain ⊓ and ⊔ collapse, so the *-ro* Hamblin sets contain
the individual answers only — with the plurality for the neutral domain. -/
theorem hamblinRo_neutral :
    hamblinRo bought neutral = (neutral.image fun e => univ.filter (bought e)) ∧
      hamblinRo bought atoms = atoms.image fun e => univ.filter (bought e) := by decide

/-- §2: English bare interrogatives (9)–(11) allow both answers, singular complex ones
(12)–(13) only a singular answer, and plural complex ones (14)–(15), whose singular
alternative has the stronger presupposition, only a plural one. -/
theorem dayal_english :
    answers (hamblinRo bought neutral) = (true, true) ∧
      answers (hamblinRo bought atoms) = (true, false) ∧
      dom (hamblinRo bought atoms) ⊂ dom (hamblinRo bought neutral) ∧
      exhAnswers (hamblinRo bought neutral) (hamblinRo bought atoms) = (false, true) := by
  decide

/-- (19): over atoms alone a Spanish singular bare interrogative wrongly presupposes
uniqueness; ranging over their conjunctions and disjunctions admits the plural answer. -/
theorem spanish_gq :
    answers (hamblinRo bought atoms) = (true, false) ∧
      answers (hamblin bought atoms) = (true, true) := by
  decide

/-- (40), (45): singular bare and complex interrogatives allow both answers; (53): so does
the *-ro* bare interrogative, through the plurality; (55): the *-ro* complex interrogative
allows only the singular answer. -/
theorem farsi :
    answers (hamblin bought neutral) = (true, true) ∧
      answers (hamblin bought atoms) = (true, true) ∧
      answers (hamblinRo bought neutral) = (true, true) ∧
      answers (hamblinRo bought atoms) = (true, false) := by
  decide

/-! ### Questions with *must* (30)–(36) and collective predicates (56)–(57) -/

/-- A deontic world: the nonempty set of buy-worlds it permits. -/
abbrev Base := {A : Finset World // A.Nonempty}

/-- *Must*'s accessibility: the buy-worlds a deontic world permits. -/
def permits (A : Base) (v : World) : Prop := v ∈ A.1

/-- Every buy-world is the sole world some deontic world permits. -/
theorem permits_singleton (v : World) : ∃ A : Base, ∀ u, permits A u ↔ u = v :=
  ⟨⟨{v}, Finset.singleton_nonempty v⟩, fun _ => Finset.mem_singleton⟩

/-- (59): Forood must buy one of two things, and either is permitted. -/
def freeChoice : Base := ⟨{{0}, {1}}, by decide⟩

/-- (35)–(36) vs. (32)–(33): with the interrogative binding into the scope of *must* (34), the
question is resolvable in the free-choice scenario iff the interrogative ranges over
disjunctions — which *-ro* removes, (62)–(63). -/
theorem modal_gq :
    ∀ D ∈ [neutral, atoms],
      IsExhaustivelyResolvable (box (ofFinset (hamblin bought D)) permits) freeChoice ∧
        ¬ IsExhaustivelyResolvable (box (ofFinset (hamblinRo bought D)) permits) freeChoice := by
  simp only [isExhaustivelyResolvable_box_iff _ permits_singleton (x := freeChoice)
    (s := (↑freeChoice.1 : Set World)) fun _ => Iff.rfl]
  decide

/-- *Mixed together*: a collective predicate, true of a plurality that was bought. -/
def mixed (e : Entity) (w : World) : Prop := 2 ≤ e.card ∧ e ⊆ w

instance (e : Entity) : DecidablePred (mixed e) :=
  fun w => inferInstanceAs (Decidable (2 ≤ e.card ∧ e ⊆ w))

/-- (56)–(57): a collective predicate has a true answer over the neutral domain, with or
without *-ro*, and none over the atoms. -/
theorem collective :
    answers (hamblin mixed neutral) = (false, true) ∧
      answers (hamblinRo mixed neutral) = (false, true) ∧
      answers (hamblin mixed atoms) = (false, false) ∧
      answers (hamblinRo mixed atoms) = (false, false) := by
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
    some (exhAnswers (hamblinRo bought neutral) (hamblinRo bought atoms))
  | _, _ => (hamblinOf row).map answers

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
over disjunctions (`isExhaustivelyResolvable_box_iff` relates this to the question with
*must*). -/
theorem scenario_rows :
    ∀ row ∈ Examples.all, row.feature? "scenario" = some "freeChoice59" →
      (hamblinOf row).map
          (fun H => decide (IsExhaustivelyResolvableOn (ofFinset H) ↑freeChoice.1)) =
        some (row.feature? "verdict" == some "true") := by decide +kernel

end AlonsoOvalleMoghiseh2025b
