import Linglib.Studies.UegakiSudo2019
import Linglib.Semantics.Modality.Kratzer.Ordering
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.Mandarin.Predicates
import Linglib.Fragments.Japanese.Predicates
import Linglib.Fragments.Turkish.Predicates
import Linglib.Data.Examples.QingEtAl2025

/-!
# Qing et al. (2025): When Can Non-Veridical Preferential Attitude Predicates Take Questions?

This file formalizes [qing-uegaki-2025]'s classification of non-veridical preferential
predicates by clausal distributivity and evaluative valence. [uegaki-sudo-2019] derive the
anti-rogativity of *hope* from two assumptions, that the predicate is clausally distributive and
that it carries the Threshold Significance Presupposition, under which its composition with a
question is true whenever defined. Neither holds of preferentials in general. A predicate that
holds of a question but of none of its answers is not distributive, the diagnostic the paper
applies to *worry* and Mandarin *qidai* (`relational_not_isDistributive`), and evaluatively
negative predicates lack the presupposition. Composition with a question is therefore trivial,
and the predicate anti-rogative, exactly for the distributive positive class
(`trivial_iff_class`), where the class of a predicate is read off the compositional strategy
its lexical entry records. The paper's judgments from English, Mandarin, Japanese, Spanish, and
Turkish are the rows: every acceptable interrogative complement is under a predicate of the two
responsive classes (`responsive_rows`), and no class 3 predicate takes one canonically.

Apparent question-taking by *hope* is non-canonical composition. Composing with the highlighted
content of a polar question is the declarative meaning, which yields the interpretive asymmetry
of *hope whether p* but not its inquisitive implication; the preferred analysis, modelled on
Turkish *diye* clauses ([ozyildiz-uegaki-2024]), takes the question as a report of wondering
adjoined to the predicate and derives the asymmetry pragmatically. Under [tabatowski-2022]'s
convention that wondering whether `p` prefers learning `p`, a hopeful wondering whose goals are
the hoped-for proposition or its belief is coherent when the agent hopes for the radical and
incoherent when they hope for its negation, while fear constrains no goal (`hopes_negation`);
the truth-value and felicity judgments of the polar cases follow the pattern (`asymmetry_rows`).

## Implementation notes

Triviality quantifies over the degree function and threshold, the non-logical constants of
[gajewski-2002]'s analyticity, with the question as its own comparison class as in
[uegaki-sudo-2019]. A relational predicate carries its relation to the question as a parameter,
since the paper characterizes the class only as a relation to the question not reducible to one
to any answer. The pragmatic derivation compares the two outcomes the paper's gloss of
[tabatowski-2022]'s condition compares, coming to believe the radical or not, by Kratzer's
ordering with the event's goals as ordering source, leaving the doxastic and similarity
machinery of (82) aside; the event summation of the adjunction analysis is not formalized. The
Spanish predicates, which have no Fragment entries, are classified in this file. The rows carry
the paper's truth values where it gives them and its felicity judgments otherwise; the attested
*hope whether* examples, (63a) included, are recorded as marginal following the paper's own
assessment of the construction, and *temer* with a polar question and *haipa* with a
constituent question, which the paper sets aside, are recorded but not predicted.

## References

* [qing-uegaki-2025]
* [uegaki-sudo-2019]
* [gajewski-2002]
* [villalta-2008]
* [elliott-etal-2017]
* [white-2021]
* [uegaki-2022]
* [tabatowski-2022]
* [ozyildiz-uegaki-2024]
* [kratzer-1981]
-/

namespace QingEtAl2025

open Data.Examples Examples Features Preferential Modality.Kratzer

variable {W E : Type*}

/-- Preference degree functions: `μ x p` is the degree to which `x` prefers, or for a negative
predicate dreads, `p`. -/
abbrev Degree (W E : Type*) := E → Finset W → ℚ

/-- Thresholds over a comparison class. -/
abbrev Threshold (W : Type*) := List (Finset W) → ℚ

/-! ### The two escapes from triviality (§3) -/

/-- A preferential predicate whose question use is a relation to the question itself, anxious
uncertainty for *worry* (§3.1.2) or anticipation of resolution for Mandarin *qidai* (§3.1.1),
while its declarative use is the degree comparison. -/
def relational (valence : AttitudeValence) (μ : Degree W E) (θ : Threshold W)
    (R : E → List (Finset W) → Prop) : PreferentialPredicate W E where
  valence := valence
  μ := μ
  θ := θ
  propSemantics x p C := μ x p > θ C
  questionSemantics x Q _ := R x Q

/-- The diagnostic of (23) to (25): an agent anxious to find out where he can dock, and happy
to dock anywhere, worries where he can dock without worrying that he can dock at any particular
place, so *worry* is not clausally distributive. -/
theorem relational_not_isDistributive (v : AttitudeValence) (μ : Degree W E) (θ : Threshold W)
    (R : E → List (Finset W) → Prop) {x : E} {Q C : List (Finset W)} (hR : R x Q)
    (h : ∀ p ∈ Q, ¬ μ x p > θ C) : ¬ (relational v μ θ R).IsDistributive :=
  PreferentialPredicate.not_isDistributive_of_forall_not (V := relational v μ θ R) hR h

/-- Composition of a predicate family with a question is trivial under a presupposition when in
every model the presupposition entails the assertion, the question serving as comparison class
([uegaki-sudo-2019]): true whenever defined, [gajewski-2002]'s analyticity with the degree
function and threshold as the non-logical constants. -/
def Trivial (V : Degree W E → Threshold W → PreferentialPredicate W E)
    (π : Degree W E → Threshold W → E → List (Finset W) → Prop) : Prop :=
  ∀ μ θ x Q, π μ θ x Q → (V μ θ).questionSemantics x Q Q

/-- What a preferential predicate presupposes of a question: threshold significance for a
positive predicate, and for a negative one, which triggers none (§3.2), only that the question
has an answer in the comparison class. -/
def presupposition : AttitudeValence → Degree W E → Threshold W → E → List (Finset W) → Prop
  | .positive => ThresholdSignificance
  | .negative => λ _ _ _ Q => Q ≠ []

/-- [uegaki-sudo-2019]: a distributive positive predicate composed with a question is trivial. -/
theorem trivial_positive :
    Trivial (mkDegreeComparison (W := W) (E := E) .positive) (presupposition .positive) :=
  λ μ θ x Q h => (UegakiSudo2019.hope_question_iff_significance μ θ x Q).2 h

/-- Without threshold significance, *x fears Q* says only that some answer is feared, which a
model falsifies. -/
theorem not_trivial_negative [Inhabited E] :
    ¬ Trivial (mkDegreeComparison (W := W) (E := E) .negative) (presupposition .negative) :=
  λ h => by
    have := h (λ _ _ => 0) (λ _ => 0) default [∅] (by simp [presupposition])
    simp [mkDegreeComparison] at this

/-- A relational predicate is not trivial even under threshold significance: some agent does
not stand in the relation to a question an answer of which clears the threshold. -/
theorem not_trivial_relational (v : AttitudeValence) (R : E → List (Finset W) → Prop)
    (hR : ∃ x Q, Q ≠ [] ∧ ¬ R x Q) :
    ¬ Trivial (λ μ θ => relational v μ θ R) (presupposition v) :=
  λ h => by
    obtain ⟨x, Q, hQ, hxQ⟩ := hR
    refine hxQ (h (λ _ _ => 1) (λ _ => 0) x Q ?_)
    cases v
    · obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil Q hQ
      exact ⟨p, hp, by simp⟩
    · exact hQ

/-! ### The classification (Table 2) -/

/-- The three classes of non-veridical preferential predicates. -/
inductive PredicateClass
  /-- Class 1: not clausally distributive, of either valence. -/
  | nonDistributive
  /-- Class 2: distributive and negative. -/
  | distributiveNegative
  /-- Class 3: distributive and positive, the class [uegaki-sudo-2019] describe. -/
  | distributivePositive
  deriving DecidableEq, Repr

/-- The class of a predicate, read off the compositional strategy its lexical entry records. -/
def classOf : Features.Preferential → PredicateClass
  | .degreeComparison .positive => .distributivePositive
  | .degreeComparison .negative => .distributiveNegative
  | .uncertaintyBased | .relevanceBased _ => .nonDistributive

/-- The semantics of a strategy, the relational ones over a relation `R` to the question. -/
def semantics (R : E → List (Finset W) → Prop) :
    Features.Preferential → Degree W E → Threshold W → PreferentialPredicate W E
  | .degreeComparison v => mkDegreeComparison v
  | .uncertaintyBased => λ μ θ => relational .negative μ θ R
  | .relevanceBased v => λ μ θ => relational v μ θ R

/-- Table 2: canonical composition with a question is trivial, hence anti-rogative, exactly for
the distributive positive class. -/
theorem trivial_iff_class [Inhabited E] (k : Features.Preferential)
    (R : E → List (Finset W) → Prop) (hR : ∃ x Q, Q ≠ [] ∧ ¬ R x Q) :
    Trivial (semantics R k) (presupposition k.valence) ↔ classOf k = .distributivePositive := by
  cases k with
  | degreeComparison v =>
    cases v
    · exact iff_of_true trivial_positive rfl
    · exact iff_of_false not_trivial_negative (by decide)
  | uncertaintyBased => exact iff_of_false (not_trivial_relational _ R hR) (by simp [classOf])
  | relevanceBased v => exact iff_of_false (not_trivial_relational v R hR) (by simp [classOf])

/-! ### The paper's judgments -/

/-- The attitude a predicate name denotes: the Fragment entry for English, Mandarin, Japanese,
and Turkish, and the paper's classification for Spanish. -/
def attitude? : String → Option Attitude
  | "hope" => English.Predicates.Verbal.hope.attitude
  | "fear" => English.Predicates.Verbal.fear.attitude
  | "worry" => English.Predicates.Verbal.worry.attitude
  | "qidai" => Mandarin.Predicates.qidai.attitude
  | "danxin" => Mandarin.Predicates.danxin.attitude
  | "xiwang" => Mandarin.Predicates.xiwang.attitude
  | "haipa" => Mandarin.Predicates.haipa.attitude
  | "tanosimi" => Japanese.Predicates.tanosimi.attitude
  | "sinpai" => Japanese.Predicates.shinpai.attitude
  | "osore" => Japanese.Predicates.osore.attitude
  | "nozomu" => Japanese.Predicates.nozomu.attitude
  | "kork" => Turkish.Predicates.kork.attitude
  | "um" => Turkish.Predicates.um.attitude
  | "endiselen" => Turkish.Predicates.endiselen.attitude
  | "preocupar" => some (.preferential .uncertaintyBased)
  | "temer" => some (.preferential (.degreeComparison .negative))
  | "esperar" => some (.preferential (.degreeComparison .positive))
  | _ => none

/-- The class of a row's predicate. -/
def class? (r : LinguisticExample) : Option PredicateClass :=
  ((r.feature? "predicate").bind attitude?).bind Attitude.getPreferential |>.map classOf

/-- The valence of a row's predicate, or of its manner adverb or veridical preferential where
the paper's argument turns on valence alone. -/
def valence? (r : LinguisticExample) : Option AttitudeValence :=
  match r.feature? "valence" with
  | some "positive" => some .positive
  | some "negative" => some .negative
  | _ => ((r.feature? "predicate").bind attitude?).bind Attitude.valence

/-- A row holds in its context: judged true where the paper gives a truth value, and not
infelicitous otherwise. -/
def Holds (r : LinguisticExample) : Prop :=
  match r.feature? "truth" with
  | some t => t = "true"
  | none => r.judgment ≠ .unacceptable

instance (r : LinguisticExample) : Decidable (Holds r) := by unfold Holds; split <;> infer_instance

/-- An interrogative complement composed canonically, as the predicate's argument. -/
def Argument (r : LinguisticExample) : Prop :=
  r.feature? "embedding" = some "argument" ∧ r.feature? "clause" ≠ some "declarative"

instance (r : LinguisticExample) : Decidable (Argument r) := by unfold Argument; infer_instance

/-- Every acceptable interrogative complement is under a class 1 or class 2 predicate. -/
theorem responsive_rows :
    ∀ r ∈ Examples.all, Argument r → r.judgment = .acceptable →
      ∀ c ∈ class? r, c ≠ .distributivePositive := by
  decide +kernel

/-- Under canonical composition a class 3 predicate takes no question: the attested *hope
whether* and its Mandarin counterpart are marginal, the Spanish, Japanese, and Turkish
counterparts unacceptable. -/
theorem anti_rogative_rows :
    ∀ r ∈ Examples.all, Argument r → class? r = some .distributivePositive →
      r.judgment ≠ .acceptable := by
  decide +kernel

/-- The negative predicates' lack of threshold significance, (38) to (41), (44), (49), (52): a
negated positive preferential is infelicitous where the agent prefers no answer, a negated
negative one felicitous. -/
theorem tsp_rows :
    ∀ r ∈ Examples.all, r.feature? "polarity" = some "negated" →
      ∀ v ∈ valence? r, (r.judgment = .acceptable ↔ v = .negative) := by
  decide +kernel

/-- The non-distributivity diagnostic, (23) to (36): every declarative the paper judges false
is under a class 1 predicate and sits beside a constituent question of the same predicate judged
true in the same context. -/
theorem nondistributive_rows :
    ∀ r ∈ Examples.all, r.feature? "truth" = some "false" →
      r.feature? "clause" = some "declarative" →
        class? r = some .nonDistributive ∧ ∃ r' ∈ Examples.all, r'.context = r.context ∧
          r'.feature? "predicate" = r.feature? "predicate" ∧
          r'.feature? "clause" = some "constituent" ∧ r'.feature? "truth" = some "true" := by
  decide +kernel

/-- Turkish *diye* clauses combine with *um-* "hope", *kork-* "fear", and an intransitive verb
alike, (71), (73), (75), (76): they are adjoined reports of wondering, not arguments. -/
theorem diye_rows :
    ∀ r ∈ Examples.all, r.feature? "embedding" = some "diye" → r.judgment = .acceptable := by
  decide +kernel

/-! ### Non-canonical composition (§4) -/

/-- Candidate analysis 1 (§4.2): composed with the highlighted content of *whether p*, the
singleton of the radical, a degree-comparison predicate means its declarative (70), which yields
the interpretive asymmetry but not the inquisitive implication. -/
theorem highlighted_eq_declarative (v : AttitudeValence) (μ : Degree W E) (θ : Threshold W)
    (x : E) (p : Finset W) (C : List (Finset W)) :
    (mkDegreeComparison v μ θ).questionSemantics x [p] C ↔
      (mkDegreeComparison v μ θ).propSemantics x p C := by
  simp [mkDegreeComparison]

section Asymmetry

variable {V : Type*} {p Bp Bnp : V → Prop} {v₁ v₂ : V}

/-- (89): the goals of a hopeful event whose agent hopes `φ` are `φ` or the agent's believing
`φ`. -/
def HopefulGoals (φ Bφ : V → Prop) (G : List (V → Prop)) : Prop := ∀ g ∈ G, g = φ ∨ g = Bφ

/-- Hoping for the radical: with the goal of believing `p`, the outcome in which the agent comes
to believe `p` is strictly better than the one in which they do not, so the wondering meets
[tabatowski-2022]'s convention on asking whether `p`. -/
theorem hopes_radical (h₁ : Bp v₁) (h₂ : ¬ Bp v₂) : v₁ <[[Bp]] v₂ := by
  simp only [strictlyBetter, atLeastAsGoodAs_iff, List.mem_singleton, forall_eq]
  exact ⟨λ h => (h₂ h).elim, λ h => h₂ (h h₁)⟩

/-- Hoping for the negation: whichever goal (89) allows, an outcome in which `p` holds and the
agent does not believe `¬p` satisfies neither `¬p` nor believing `¬p`, so coming to believe `p`
is no better than not, and the wondering cannot be hopeful. -/
theorem hopes_negation {G : List (V → Prop)} (hG : HopefulGoals (λ v => ¬ p v) Bnp G)
    (hp₁ : p v₁) (hn₁ : ¬ Bnp v₁) : ¬ v₁ <[G] v₂ := by
  rintro ⟨-, h⟩
  refine h ((atLeastAsGoodAs_iff G v₂ v₁).2 λ g hg hg₁ => ?_)
  rcases hG g hg with rfl | rfl
  · exact absurd hp₁ hg₁
  · exact absurd hg₁ hn₁

/-- Fear constrains no goal (87): the purely epistemic goal of knowing whether `p` makes coming
to believe `p` strictly better than remaining undecided, whichever answer is feared. -/
theorem fears (h₁ : Bp v₁) (h₂ : ¬ Bp v₂) (hn₂ : ¬ Bnp v₂) :
    v₁ <[[λ v => Bp v ∨ Bnp v]] v₂ := by
  simp only [strictlyBetter, atLeastAsGoodAs_iff, List.mem_singleton, forall_eq]
  exact ⟨λ h => (h.elim h₂ hn₂).elim, λ h => (h (Or.inl h₁)).elim h₂ hn₂⟩

end Asymmetry

/-- The polar cases, (45), (50), (62), (63), (75), (76), (78), (79): a positive predicate or
adverb holds exactly when the agent's attitude targets the radical, a negative one either
way. -/
theorem asymmetry_rows :
    ∀ r ∈ Examples.all, ∀ t ∈ r.feature? "target", ∀ v ∈ valence? r,
      (v = .positive → (Holds r ↔ t = "radical")) ∧ (v = .negative → Holds r) := by
  decide +kernel

end QingEtAl2025
