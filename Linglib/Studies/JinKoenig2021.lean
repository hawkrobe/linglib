import Linglib.Data.Examples.JinKoenig2021
import Linglib.Semantics.Polarity.ExpletiveNegation
import Linglib.Studies.Karttunen1974
import Linglib.Semantics.Modality.Kratzer.Operators
import Linglib.Semantics.Degree.Basic
import Linglib.Semantics.Conditionals.Basic
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Jin and Koenig (2021): A Cross-Linguistic Study of Expletive Negation

This file formalizes [jin-koenig-2021], the typology of expletive negation: a negator in the
dependent of a lexical item, triggered by the item's meaning, that contributes no negation to
the dependent's proposition, (2). A survey of 722 languages finds it in 74, across 37 genera,
most often under *before* and *fear*, and a comparison of English, French, Januubi, Mandarin and
Zarma-Sonrai finds the same trigger classes in all five, Table 5. The account is that a
trigger's meaning activates both its argument and the argument's negation, in distinct sets of
worlds, at distinct times, in the meaning itself, or as predications of distinct entities, the
four licensing conditions of (13) (`Negation.ENLicensing`); the classes and concepts of Tables
5 and 6 are `Negation.ENTriggerClass` and `Negation.ENConcept`, and the paper's examples are
rows. The activation is `DualInference`, the argument true at one point of a domain and false
at another, and the substrate's operators deliver it: *q before p* leaves *p* false at the time
of *q* (`before_dual`), *impossible p* leaves it false at the best worlds (`impossible_dual`),
*without* and *unless* carry the negation in their meaning, and a comparative predicates a
degree of one entity and denies it of the other (`comparative_dual`). The verbal triggers are
the negative-valence, negative-implicative and preventive verbs of the English fragment
(`negative_valence_is_en_trigger` and its siblings). The rows carry Section 6's negator facts:
Mandarin's imperative negator under *fear* and deontic negator under the *regret* class, French
*ne* alone in its entrenched uses, and Januubi's standard negator throughout (`mandarin_negators`,
`french_ne_of_entrenched`, `januubi_standard`).

## Implementation notes

* The survey tables, Tables 1 to 4, are counts over a convenience sample that the paper itself
  declines to draw inferences from; they are not encoded. The per-language blocking of a class,
  Section 7, is typed by `Negation.ENBlockingReason` in the fragments.
* The propositional-attitude condition is not derived from the preferential semantics, whose
  valence is a label; the paper's production model is not formalized.

## References

* [jin-koenig-2021]
* [heim-1992]
* [dell-1986]
-/

namespace JinKoenig2021

open Negation Data.Examples

/-! ### The dual inference (Section 5.5) -/

/-- (13): a trigger's meaning activates its argument and the argument's negation at distinct
points of a domain, worlds, times or entities. -/
def DualInference {X : Type*} (p : X → Prop) : Prop := (∃ x, p x) ∧ ∃ y, ¬ p y

/-! ### Temporal operators (Section 6.2) -/

open Tense Anscombe1964 Karttunen1974 in
/-- *q before p*: *p* holds at some time and fails at the time of *q*, which precedes every time
of *p*, (13b). -/
theorem before_dual {T : Type*} [LinearOrder T] {A B : RunTimes T}
    (h : Anscombe.beforeEver A B) (hB : (timeTrace B).Nonempty) :
    DualInference (· ∈ timeTrace B) :=
  ⟨hB, let ⟨t, _, ht⟩ := h; ⟨t, λ hmem => lt_irrefl t (ht t hmem)⟩⟩

/-! ### Logical operators (Section 6.3) -/

open Modality.Kratzer in
/-- *impossible p* is the necessity of `¬p`: `p` fails at the best worlds and, if it holds
anywhere, the meaning activates both, (13c). -/
theorem impossible_dual {W : Type*} (f : ModalBase W) (g : OrderingSource W) (p : W → Prop)
    (w : W) (h : necessity f g (λ w' => ¬ p w') w) (hb : (bestWorlds f g w).Nonempty)
    (hp : ∃ x, p x) : DualInference p :=
  let ⟨w', hw'⟩ := hb
  ⟨hp, w', (necessity_iff_all f g _ w).1 h w' hw'⟩

open Modality.Kratzer in
/-- The negation of *impossible p* is the possibility of `p`. -/
theorem possibility_of_not_impossible {W : Type*} (f : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W) (h : ¬ necessity f g (λ w' => ¬ p w') w) : possibility f g p w := by
  rw [necessity_iff_all] at h
  rw [possibility_iff_any]
  by_contra hne
  exact h λ w' hw' => λ hp => hne ⟨w', hw', hp⟩

/-- *q without p*: `q ∧ ¬p`, the negation in the meaning, (13c). -/
def withoutSem {W : Type*} (q p : Set W) : Set W := q ∩ pᶜ

theorem withoutSem_subset_compl {W : Type*} (q p : Set W) : withoutSem q p ⊆ pᶜ :=
  Set.inter_subset_right

/-- *q unless p*: if not `p` then `q`, so `¬p` holds in the suppositive worlds, (13c). -/
def unlessSem {W : Type*} (q p : Set W) : Set W := Conditionals.materialImp pᶜ q

theorem mem_of_mem_unlessSem {W : Type*} {q p : Set W} {w : W} (h : w ∈ unlessSem q p)
    (hp : w ∉ p) : w ∈ q :=
  h hp

/-! ### Comparatives (Section 6.4) -/

open Degree in
/-- *Y is more Q than Z*: `Y` has `Q` to its own degree and `Z` does not, the two predications of
(13d) over distinct entities. -/
theorem comparative_dual {Entity α : Type*} [LinearOrder α] (μ : Entity → α) (y z : Entity)
    (h : comparativeSem μ y z .positive) : DualInference λ e => μ y ≤ μ e :=
  ⟨⟨y, le_rfl⟩, ⟨z, not_le.2 h⟩⟩

/-! ### Verbal triggers -/

/-- A negative-valence preferential attitude is a trigger of the *fear* class. -/
theorem negative_valence_is_en_trigger (v : Verb)
    (h : v.preferentialValence = some .negative) : v.isENTrigger = true := by
  simp only [Verb.isENTrigger, h, show (some Preferential.Valence.negative ==
    some Preferential.Valence.negative) = true from rfl, Bool.true_or]

/-- A negative implicative verb is a trigger of the *forget* class. -/
theorem negative_implicative_is_en_trigger (v : Verb) (h : v.implicative = some .negative) :
    v.isENTrigger = true := by
  simp only [Verb.isENTrigger, h, show (some Implicative.negative ==
    some Implicative.negative) = true from rfl, Bool.true_or, Bool.or_true]

/-- A preventive causative is a trigger of the *forget* class. -/
theorem prevent_is_en_trigger (v : Verb) (h : v.causative = some .prevent) :
    v.isENTrigger = true := by
  simp only [Verb.isENTrigger, h, show (some Causative.prevent ==
    some Causative.prevent) = true from rfl, Bool.or_true]

open English.Predicates.Verbal in
/-- The English fragment's *fear*, *dread*, *worry*, *forget* and *prevent* are triggers. -/
theorem english_triggers :
    fear.toVerb.isENTrigger = true ∧ dread.toVerb.isENTrigger = true ∧
      worry.toVerb.isENTrigger = true ∧ forget.toVerb.isENTrigger = true ∧
      prevent.toVerb.isENTrigger = true :=
  ⟨negative_valence_is_en_trigger _ rfl, negative_valence_is_en_trigger _ rfl,
    negative_valence_is_en_trigger _ rfl, negative_implicative_is_en_trigger _ rfl,
    prevent_is_en_trigger _ rfl⟩

/-! ### The examples -/

/-- The five languages of Section 4. -/
inductive Language
  | english
  | french
  | januubi
  | mandarin
  | zarmaSonrai
  deriving DecidableEq, Repr

/-- The kind of negator an example uses: the standard negator, a dedicated expletive negator
(French *ne* alone), an imperative negator (Mandarin *bié*), a deontic one (Mandarin *bùgāi*) or
a copular one (Zarma-Sonrai *sinda*). -/
inductive NegatorKind
  | standard
  | dedicated
  | imperative
  | deontic
  | copular
  deriving DecidableEq, Repr

/-- A row: the language, the trigger concept, the negator, its kind, and for French whether the
paper reports the use as entrenched. -/
structure Row where
  language : Language
  concept : ENConcept
  negator : String
  kind : NegatorKind
  entrenched : Option Bool
  deriving DecidableEq

private def languageOf : String → Option Language
  | "stan1293" => some .english
  | "stan1290" => some .french
  | "" => some .januubi
  | "mand1415" => some .mandarin
  | "zarm1239" => some .zarmaSonrai
  | _ => none

private def conceptOf : String → Option ENConcept
  | "fear" => some .fear
  | "avoid" => some .avoid
  | "regret" => some .regret
  | "complain" => some .complain
  | "deny" => some .deny
  | "hide" => some .hide
  | "forget" => some .forget
  | "delay" => some .delay
  | "barely" => some .barely
  | "before" => some .before
  | "cannotWait" => some .cannotWait
  | "rarely" => some .rarely
  | "onlyDependsOn" => some .onlyDependsOn
  | "differentThan" => some .differentThan
  | "tooTo" => some .tooTo
  | _ => none

private def kindOf : String → Option NegatorKind
  | "standard" => some .standard
  | "dedicated" => some .dedicated
  | "imperative" => some .imperative
  | "deontic" => some .deontic
  | "copular" => some .copular
  | _ => none

/-- A row from the paper's features. -/
def Row.ofExample (e : LinguisticExample) : Option Row := do
  let l ← languageOf e.language
  let c ← (e.feature? "concept").bind conceptOf
  let n ← e.feature? "negator"
  let k ← (e.feature? "negator_kind").bind kindOf
  some ⟨l, c, n, k, (e.feature? "entrenched").map (· == "high")⟩

/-- The examples of Sections 1, 2 and 6. -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- Mandarin's negator tracks the trigger, Sections 6.1.1 and 6.1.2: the imperative negator
exactly under *fear* and the deontic negator exactly under the *regret* class. -/
theorem mandarin_negators :
    ∀ r ∈ rows, r.language = .mandarin →
      (r.kind = .imperative ↔ r.concept = .fear) ∧
        (r.kind = .deontic ↔ r.concept.cls = .regret) := by
  decide

/-- French marks its entrenched uses with *ne* alone, Section 5.5. -/
theorem french_ne_of_entrenched :
    ∀ r ∈ rows, r.language = .french → r.entrenched = some true → r.negator = "ne" := by
  decide

/-- Januubi uses its standard negator throughout, Section 6. -/
theorem januubi_standard : ∀ r ∈ rows, r.language = .januubi → r.kind = .standard := by decide

end JinKoenig2021
