import Linglib.Semantics.Focus.Particles
import Linglib.Fragments.Hindi.PolarityItems
import Linglib.Data.Examples.Lahiri1998

/-!
# Lahiri (1998): Focus and negative polarity in Hindi

This file formalizes the paper's account of the Hindi negative polarity items, each a weak
indefinite plus the focus particle *bhii* 'even' (`Hindi.PolarityItems`). The scalar
presupposition of *even*, that the prejacent is less likely than every focus alternative,
clashes with an entailment-monotone likelihood exactly when an alternative entails the
prejacent (`Focus.Particles.not_evenPresup_of_subset`). The indefinite is the weakest
predicate, so in an upward-entailing context every alternative entails the assertion and the
presupposition is contradictory (`ue_clash`), while a downward-entailing operator reverses the
entailments and leaves it satisfiable (`de_presup`); the restriction of a generic, read as a
universal under the paper's background assumption, is such a slot (`generic_presup`), as are
the negative-expectation reading of a question and the permission reading of an imperative.
Clausemate negation takes scope over a Hindi subject indefinite, which is why Hindi licenses
subject NPIs where English does not (`clausemate_negation`). The judgments of the paper's
survey are rows, which `analysis_matches_judgments` reads as the analysis predicts, apart from
the numeral and measure items *ek bhii* and *zaraa bhii* in imperatives and with numerals,
whose cardinality alternatives the paper distinguishes from the contextual alternatives of
*koii bhii* and *kuch bhii* and whose exclusion it leaves open (`cardinality_exceptions`).

## Implementation notes

A likelihood is a monotone map from propositions into a partial order, and the alternatives
an item introduces are a list of predicates, cardinalities or contextual properties, each at
most as strong as the weakest predicate `⊤`, the paper's `one`. The generic operator is read
as a universal quantifier, which the paper grants on the background assumption that the
exceptions the alternatives tolerate are exceptions the assertion tolerates too; the
permission analysis of imperatives and the two implicature sets of a question are instances of
`de_presup` and `ue_clash` and are not restated. The environments of the survey are
classified as the analysis classifies them, downward entailing, generic, or neither;
necessity modals and the episodic readings of possibility modals and the future are among
the last, which the paper reports without deriving. The oblique forms *kisii-ko*, *kisii-se*,
and *kisiike* are *koii*'s.

## References

* [lahiri-1998]
* [karttunen-peters-1979]
* [kadmon-landman-1993]
-/

namespace Lahiri1998

open Focus.Particles Polarity Data.Examples Hindi.PolarityItems

/-! ### The implicature clash (§7, §8) -/

section Model

variable {World Ent α : Type*} [PartialOrder α] {μ : Set World → α}

/-- The existential assertion of an indefinite restricted by `P`: some `P`-entity satisfies
the predicate. -/
def exist (P : Ent → Prop) (φ : World → Ent → Prop) : Set World := {w | ∃ x, P x ∧ φ w x}

/-- The universal reading of a generic restricted by `P`: every `P`-entity satisfies the
predicate. -/
def restrict (P : Ent → Prop) (φ : World → Ent → Prop) : Set World := {w | ∀ x, P x → φ w x}

variable {φ : World → Ent → Prop}

theorem exist_mono : Monotone (exist · φ) := λ _ _ h _ ⟨x, hx, hφ⟩ => ⟨x, h x hx, hφ⟩

theorem restrict_anti : Antitone (restrict · φ) := λ _ _ h _ hr x hx => hr x (h x hx)

/-- The weakest predicate is true of everything, so every alternative entails the existential
assertion. -/
theorem exist_subset_exist_top (P : Ent → Prop) : exist P φ ⊆ exist ⊤ φ := exist_mono le_top

/-- The universal assertion on the weakest predicate entails every alternative. -/
theorem restrict_top_subset (P : Ent → Prop) : restrict ⊤ φ ⊆ restrict P φ :=
  restrict_anti le_top

/-- The focus alternatives *bhii* induces from alternative predicates. -/
def alternatives (Ps : List (Ent → Prop)) (φ : World → Ent → Prop) : List (Set World) :=
  Ps.map (exist · φ)

variable {Ps : List (Ent → Prop)}

/-- In an upward-entailing context the presupposition of *bhii* is contradictory as soon as
there is an alternative, cardinality or contextual property: each entails the assertion and
so is at least as likely. -/
theorem ue_clash (hμ : Monotone μ) (hPs : Ps ≠ []) :
    ¬ evenPresup μ (exist ⊤ φ) (alternatives Ps φ) :=
  let ⟨P, hP⟩ := Ps.exists_mem_of_ne_nil hPs
  not_evenPresup_of_subset hμ (List.mem_map_of_mem hP) (exist_subset_exist_top P)

/-- A downward-entailing operator reverses the entailments, so under it the presupposition
asks only that no alternative be exactly as likely; negation, the complement of a prohibition
verb, and the permission an imperative grants are such operators. -/
theorem de_presup (hμ : Monotone μ) {Q : Set World → Set World} (hQ : Antitone Q) :
    evenPresup μ (Q (exist ⊤ φ)) ((alternatives Ps φ).map Q) ↔
      ∀ P ∈ Ps, μ (Q (exist ⊤ φ)) ≠ μ (Q (exist P φ)) := by
  rw [evenPresup_iff_ne hμ]
  · simp [alternatives]
  · simp only [alternatives, List.map_map, List.mem_map, Function.comp_def,
      forall_exists_index, and_imp]
    rintro _ P hP rfl
    exact hQ (exist_subset_exist_top P)

/-- *koii bhii aayaa* against *koii bhii nahiiN aayaa*, and the two implicature sets of a
yes-no question: the positive reading clashes and the negative one is satisfiable. Negation
inside the existential, the only scope English gives a subject indefinite, is again a positive
context, which is why English lacks the subject NPIs that Hindi licenses. -/
theorem clausemate_negation (hμ : Monotone μ) (hPs : Ps ≠ []) :
    ¬ evenPresup μ (exist ⊤ φ) (alternatives Ps φ) ∧
      (evenPresup μ (exist ⊤ φ)ᶜ ((alternatives Ps φ).map compl) ↔
        ∀ P ∈ Ps, μ (exist ⊤ φ)ᶜ ≠ μ (exist P φ)ᶜ) ∧
      ¬ evenPresup μ (exist ⊤ λ w x => ¬ φ w x) (alternatives Ps λ w x => ¬ φ w x) :=
  ⟨ue_clash hμ hPs, de_presup hμ compl_anti, ue_clash hμ hPs⟩

/-- In the restriction of a generic the assertion entails every alternative, so the
presupposition is satisfiable and the free-choice reading licensed. -/
theorem generic_presup (hμ : Monotone μ) :
    evenPresup μ (restrict ⊤ φ) (Ps.map (restrict · φ)) ↔
      ∀ P ∈ Ps, μ (restrict ⊤ φ) ≠ μ (restrict P φ) := by
  rw [evenPresup_iff_ne hμ]
  · simp
  · simp only [List.mem_map, forall_exists_index, and_imp]
    rintro _ P hP rfl
    exact restrict_top_subset P

end Model

/-! ### The survey (§4–§6, §8–§10) -/

/-- The environments of the survey. -/
inductive Environment where
  | positive
  | negation
  | protasis
  | apodosis
  | universalRestrictor
  | existentialRestrictor
  | adversative
  | factive
  | settleForLess
  | prohibitionComplement
  | prohibitionObject
  | before
  | after
  | question
  | generic
  | possibilityModal
  | episodicModal
  | genericFuture
  | episodicFuture
  | necessityModal
  | imperative
  | numeralGeneric
  deriving DecidableEq, Repr

/-- Whether the analysis licenses an indefinite plus *bhii* in the environment: the
downward-entailing environments, questions on their negative-expectation reading, and the
generic environments, generics with or without a numeral, generically read possibility modals
and futures, and imperatives read as permissions. -/
def Environment.Licensed : Environment → Prop
  | .negation | .protasis | .universalRestrictor | .adversative | .settleForLess
  | .prohibitionComplement | .before | .question | .generic | .possibilityModal
  | .genericFuture | .imperative | .numeralGeneric => True
  | .positive | .apodosis | .existentialRestrictor | .factive | .prohibitionObject | .after
  | .episodicModal | .episodicFuture | .necessityModal => False

instance : DecidablePred Environment.Licensed
  | .negation | .protasis | .universalRestrictor | .adversative | .settleForLess
  | .prohibitionComplement | .before | .question | .generic | .possibilityModal
  | .genericFuture | .imperative | .numeralGeneric => isTrue trivial
  | .positive | .apodosis | .existentialRestrictor | .factive | .prohibitionObject | .after
  | .episodicModal | .episodicFuture | .necessityModal => isFalse id

/-- A judged example: its environment, the fragment entry of its item, and the judgment. -/
structure Datum where
  env : Environment
  item : Item
  judgment : Judgment

/-- The fragment entry of a row's item. -/
def item? (r : LinguisticExample) : Option Item :=
  r.parse? "npi" [("koii bhii", koiiBhii), ("koi bhii", koiiBhii), ("kisii-ko bhii", koiiBhii),
    ("kisii-se bhii", koiiBhii), ("kisiike bhii", koiiBhii), ("ek bhii", ekBhii),
    ("kuch bhii", kuchBhii), ("kuchh bhii", kuchBhii), ("zaraa bhii", zaraaBhii),
    ("kabhii bhii", kabhiiBhii)]

/-- A row of the survey. -/
def datum (r : LinguisticExample) : Option Datum := do
  let env ← r.parse? "environment" [("positive (UE)", Environment.positive),
    ("negation", .negation), ("negation (subject NPI)", .negation),
    ("conditional protasis", .protasis), ("conditional apodosis", .apodosis),
    ("universal restrictor", .universalRestrictor),
    ("existential restrictor", .existentialRestrictor), ("adversative", .adversative),
    ("non-adversative factive", .factive), ("settle-for-less glad", .settleForLess),
    ("prohibition verb", .prohibitionComplement),
    ("outside prohibition scope", .prohibitionObject), ("before-clause", .before),
    ("after-clause", .after), ("question", .question), ("generic", .generic),
    ("possibility modal", .possibilityModal), ("episodic possibility modal", .episodicModal),
    ("generic future", .genericFuture), ("episodic future", .episodicFuture),
    ("necessity modal", .necessityModal), ("imperative", .imperative),
    ("generic, with numeral", .numeralGeneric)]
  let item ← item? r
  pure ⟨env, item, r.judgment⟩

/-- The survey. -/
def data : List Datum := Examples.all.filterMap datum

/-- The analysis reads every judgment of the survey, the cardinality items in imperatives and
with numerals aside: an indefinite plus *bhii* is acceptable exactly in the environments it
licenses. -/
theorem analysis_matches_judgments :
    ∀ d ∈ data,
      d.item.alternativeType = .contextualProperty ∨
        (d.env ≠ .imperative ∧ d.env ≠ .numeralGeneric) →
      (d.judgment = .acceptable ↔ d.env.Licensed) := by
  decide +kernel

/-- The numeral and measure items, whose alternatives are cardinalities, are out with a
numeral and odd in imperatives, where the analysis predicts them licensed; the paper leaves
the imperative case open. -/
theorem cardinality_exceptions :
    ∀ d ∈ data, d.item.alternativeType = .cardinality →
      d.env = .imperative ∨ d.env = .numeralGeneric → d.judgment ≠ .acceptable := by
  decide +kernel

end Lahiri1998
