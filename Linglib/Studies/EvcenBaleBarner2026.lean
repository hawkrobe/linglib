import Linglib.Data.Examples.EvcenBaleBarner2026
import Linglib.Studies.VonFintel2001
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype

/-!
# Evcen, Bale and Barner (2026): Conditional Inference and Access to Alternatives

This file formalizes [evcen-bale-barner-2026]'s account of conditional perfection as a quantity
implicature over the alternatives a context makes available, and the three experiments that
test it. A conditional *if p then q* is perfected to *only if p* when the conditionals with the
alternative antecedents are excluded ([geis-zwicky-1971], [von-fintel-2001]); under
[stalnaker-1968]'s semantics the negation of *if r then q* is *if r then not q*. The
alternatives are the answers to the Question Under Discussion ([roberts-1996]) that the speaker
is competent about, so that the exhaustification operator negates only the non-weaker
alternatives in ALT(p) ⊆ ANS(QUD) ∩ {q : K(q) ∨ K(¬q)}, and from the speaker's not having
asserted an alternative she knows the truth of, the hearer infers its falsity (§1). In the
paradigm Mary tests buttons that each play an animal sound only she hears and answers a question
with *If you press the blue button, it will play a dog barking*; the participant is asked
whether the orange button plays that sound, *No* being the perfected reading. Experiment 1
varies the question: an antecedent-focused one, which button plays the dog sound, makes the
other buttons' conditionals the alternatives and yields perfection, a consequent-focused one,
what the blue button plays, makes the other sounds the alternatives and yields none, and a
neutral one, what happens with the buttons, makes every button–sound pair an alternative, whose
exclusion would say that Mary heard nothing from the other buttons, against the context, so
strengthening is blocked; the perfection rates were 0.65, 0.22 and 0.29 (N = 98). Experiment 2
finds that an overly informative answer, naming one square where the question asked which shape,
is perfected within its shape like an optimally informative one (0.84 against 0.92, N = 55), so
that such answers count as relevant or the question is accommodated to their grain. Experiment
3 finds perfection only when Mary has tested all three buttons (0.72 against 0.21, N = 72):
untested, the orange button's conditional is not among the alternatives and cannot be excluded,
the competence gate that governs scalar implicature ([bale-etal-2025], [bergen-grodner-2012]).
[horn-2000]'s alternative, the unconditional *q no matter what*, is too weak: its negation
leaves open which other button fails, while participants answered *No* about a specific button.

## Implementation notes

* A world assigns each button a sound; every button plays one, the context Mary's listening
  establishes. With buttons deterministic, the Stalnaker conditional *if you press b, it plays
  s* holds at a world exactly when b plays s there, so perfection about a button is the
  negation of its conditional.
* The operator is the paper's Exh of its seventh footnote, the prejacent with every non-weaker
  alternative negated, and strengthening is blocked when the result is contextually
  inconsistent (§2.3); on the licensed case it coincides with [von-fintel-2001]'s exhaustive
  answer by innocent exclusion, `exh_eq_exhaustifiedAnswer`.
* Mary knows what a button plays exactly when she tested it.
* Experiment 2's shapes are modelled separately, a world recording which of the four buttons
  play the dog sound, with a cell-level answer read as the dog button being among the shape's,
  which the paper treats as weaker than the specific answer.
* The rows carry each condition's modal response; the rates stay in the prose above.

## References

* [evcen-bale-barner-2026]
* [von-fintel-2001]
* [horn-2000]
* [geis-zwicky-1971]
* [stalnaker-1968]
* [roberts-1996]
* [bale-etal-2025]
* [bergen-grodner-2012]
-/

namespace EvcenBaleBarner2026

open Data.Examples EvcenBaleBarner2026.Examples

/-- The three buttons of Experiments 1 and 3. -/
inductive Button
  | red
  | blue
  | orange
  deriving DecidableEq, Fintype, Repr

/-- The animal sounds: the dog barking of Mary's answer and the sounds a consequent-focused
question ranges over. -/
inductive Sound
  | dog
  | cat
  | lion
  deriving DecidableEq, Fintype, Repr

/-- A world: what each button plays. -/
abbrev World := Button → Sound

/-- *If you press b, it plays s*, true at a world exactly when b plays s there. -/
def cond (b : Button) (s : Sound) : Set World := {w | w b = s}

instance (b : Button) (s : Sound) : DecidablePred (· ∈ cond b s) :=
  λ w => inferInstanceAs (Decidable (w b = s))

instance (S T : Set World) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] :
    Decidable (S ⊆ T) :=
  decidable_of_iff (∀ w, w ∈ S → w ∈ T) Iff.rfl

/-- The trigger map of [von-fintel-2001]'s answers: button `b` plays the dog sound. -/
def causesDog (b : Button) : Set World := cond b .dog

/-- Mary's answer, *If you press the blue button, it will play a dog barking*. -/
def answer : Set World := causesDog .blue

instance : DecidablePred (· ∈ answer) := inferInstanceAs (DecidablePred (· ∈ cond .blue .dog))

/-! ### Alternatives -/

/-- The questions of Experiment 1. -/
inductive QUD
  | antecedentFocused
  | consequentFocused
  | neutral
  deriving DecidableEq, Repr

/-- The conditionals that answer a question, indexed by button and sound: which button plays the
dog sound, what the blue button plays, or what happens with the buttons. -/
def answers : QUD → Set (Button × Sound)
  | .antecedentFocused => {i | i.2 = .dog}
  | .consequentFocused => {i | i.1 = .blue}
  | .neutral => Set.univ

instance (q : QUD) : DecidablePred (· ∈ answers q) := by
  cases q <;> unfold answers <;> infer_instance

/-- The conditionals a speaker who tested the buttons in `tested` knows to hold or to fail. -/
def known (tested : Finset Button) : Set (Button × Sound) := {i | i.1 ∈ tested}

/-- The alternatives to Mary's answer: the answers to the question she is competent about,
`ALT(p) ⊆ ANS(QUD) ∩ {q : K(q) ∨ K(¬q)}`. -/
def alternatives (q : QUD) (tested : Finset Button) : Set (Button × Sound) :=
  answers q ∩ known tested

instance (q : QUD) (tested : Finset Button) : DecidablePred (· ∈ alternatives q tested) :=
  λ i => inferInstanceAs (Decidable (i ∈ answers q ∧ i.1 ∈ tested))

/-- The paper's exhaustification: the prejacent with every non-weaker alternative negated. -/
def exh (A : Set (Button × Sound)) (p : Set World) : Set World :=
  {w | w ∈ p ∧ ∀ i ∈ A, ¬ p ⊆ cond i.1 i.2 → w ∉ cond i.1 i.2}

instance (A : Set (Button × Sound)) [DecidablePred (· ∈ A)] (p : Set World)
    [DecidablePred (· ∈ p)] : DecidablePred (· ∈ exh A p) :=
  λ w => inferInstanceAs
    (Decidable (w ∈ p ∧ ∀ i ∈ A, ¬ p ⊆ cond i.1 i.2 → w ∉ cond i.1 i.2))

/-- Strengthening is blocked when it is inconsistent with the context (§2.3): no world
survives. -/
def Blocked (A : Set (Button × Sound)) (p : Set World) : Prop := exh A p = ∅

instance (A : Set (Button × Sound)) [DecidablePred (· ∈ A)] (p : Set World)
    [DecidablePred (· ∈ p)] : Decidable (Blocked A p) :=
  decidable_of_iff (∀ w, w ∉ exh A p) Set.eq_empty_iff_forall_notMem.symm

/-- The participant's response about the orange button. -/
inductive Response
  | no
  | cantTell
  deriving DecidableEq, Repr

/-- The predicted response: *No* when the strengthened answer, if not blocked, excludes the
orange button's playing the dog sound, *Can't tell* otherwise. -/
def response (A : Set (Button × Sound)) [DecidablePred (· ∈ A)] : Response :=
  if ¬ Blocked A answer ∧ exh A answer ⊆ (cond .orange .dog)ᶜ then .no else .cantTell

/-! ### Experiments 1 and 3 -/

/-- The buttons Mary tested: all three, or only the red and blue ones. -/
def testedTable : List (String × Finset Button) :=
  [("all", Finset.univ), ("two", {.red, .blue})]

/-- The questions as named in the rows. -/
def qudTable : List (String × QUD) :=
  [("antecedentFocused", .antecedentFocused), ("consequentFocused", .consequentFocused),
    ("neutral", .neutral)]

/-- The responses as named in the rows. -/
def responseTable : List (String × Response) := [("no", .no), ("cantTell", .cantTell)]

/-- A condition of Experiment 1 or 3: the question, the buttons Mary tested, and the modal
response. -/
structure Row where
  qud : QUD
  tested : Finset Button
  response : Response
  deriving DecidableEq

/-- A row from an example. -/
def Row.ofExample (ex : LinguisticExample) : Option Row := do
  pure ⟨← ex.parse? "qud" qudTable, ← ex.parse? "tested" testedTable,
    ← ex.parse? "response" responseTable⟩

/-- The conditions of Experiments 1 and 3. -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- Each condition's modal response is the one the alternatives predict: perfection under the
antecedent-focused question from a speaker who tested every button, and nothing otherwise. -/
theorem rows_response : ∀ r ∈ rows, response (alternatives r.qud r.tested) = r.response := by
  decide +kernel

/-- The neutral question: excluding every alternative leaves no button any sound, against the
context, so strengthening is blocked. -/
theorem neutral_blocked : Blocked (alternatives .neutral Finset.univ) answer := by decide +kernel

/-- The consequent-focused question: the alternatives are the other sounds of the blue button,
which the answer already excludes, so the orange button is left open. -/
theorem consequent_open :
    ¬ Blocked (alternatives .consequentFocused Finset.univ) answer ∧
      ¬ exh (alternatives .consequentFocused Finset.univ) answer ⊆ (cond .orange .dog)ᶜ := by
  decide +kernel

/-- Experiment 3: with the orange button untested its conditional is no alternative, and the
answer is not perfected about it. -/
theorem partial_knowledge_open :
    ¬ exh (alternatives .antecedentFocused {.red, .blue}) answer ⊆ (cond .orange .dog)ᶜ := by
  decide +kernel

/-! ### Von Fintel's exhaustive answer -/

/-- On the licensed case, the antecedent-focused question and a fully knowledgeable speaker,
the paper's operator is [von-fintel-2001]'s exhaustive answer with the other buttons'
conditionals innocently excluded. -/
theorem exh_eq_exhaustifiedAnswer :
    exh (alternatives .antecedentFocused Finset.univ) answer =
      VonFintel2001.exhaustifiedAnswer causesDog Set.univ .blue := by
  have hfin : (VonFintel2001.answerAlternatives causesDog Set.univ .blue).Finite :=
    Set.Finite.image _ (Set.toFinite _)
  have hsat : ∃ w, causesDog .blue w := ⟨λ _ => .dog, rfl⟩
  have hwit : ∀ b, b ≠ Button.blue →
      (λ x => if x = Button.blue then Sound.dog else .cat) ∉ causesDog b := by
    intro b hb h
    simp [causesDog, cond, hb] at h
  ext w
  constructor
  · rintro ⟨hw, hexcl⟩ ψ hψ
    rcases Exhaustification.eq_or_exists_of_mem_IE _ _ hfin ψ hψ hsat with rfl | ⟨a, ha, rfl⟩
    · exact hw
    · obtain ⟨b, -, hb, rfl⟩ := VonFintel2001.mem_answerAlternatives.mp ha
      exact hexcl (b, .dog) ⟨rfl, by simp [known]⟩
        (λ h => hwit b hb (h (show (λ x => if x = Button.blue then Sound.dog else .cat) ∈ answer
          by simp [answer, causesDog, cond])))
  · intro hw
    refine ⟨hw _ (Exhaustification.self_mem_IE _ _), ?_⟩
    rintro ⟨b, s⟩ ⟨hs, -⟩ hns
    have hs : s = .dog := hs
    subst hs
    by_cases hb : b = .blue
    · exact absurd (hb ▸ subset_rfl) hns
    · exact hw _ (Exhaustification.IsInnocentlyExcludable.of_full_exclusion_consistent
        (ALT := VonFintel2001.answerAlternatives causesDog Set.univ .blue)
        (φ := causesDog .blue)
        (VonFintel2001.mem_answerAlternatives.mpr ⟨b, Set.mem_univ _, hb, rfl⟩)
        ⟨λ x => if x = Button.blue then Sound.dog else .cat,
          show (λ x => if x = Button.blue then Sound.dog else .cat) ∈ causesDog .blue by
            simp [causesDog, cond],
          λ a ha => by
            obtain ⟨b', -, hb', rfl⟩ := VonFintel2001.mem_answerAlternatives.mp ha
            exact hwit b' hb'⟩).2

/-! ### Horn's unconditional alternative -/

/-- [horn-2000]'s alternative: the sound plays whichever button is pressed. -/
def unconditional : Set World := {w | ∀ b, w b = .dog}

/-- Negating the unconditional says only that some other button fails; it does not exclude the
orange button, which participants excluded. -/
theorem unconditional_too_weak :
    ¬ answer ∩ unconditionalᶜ ⊆ (cond .orange .dog)ᶜ := by
  intro h
  exact h (a := λ b => if b = .red then Sound.cat else .dog) ⟨rfl, λ hu => by simpa using hu .red⟩
    rfl

/-! ### Experiment 2: optimally and overly informative answers -/

/-- The four buttons of Experiment 2, two shapes in two colours. -/
inductive Button2
  | blueSquare
  | redSquare
  | yellowTriangle
  | greenTriangle
  deriving DecidableEq, Fintype, Repr

/-- The shapes the question asks about. -/
inductive Shape
  | square
  | triangle
  deriving DecidableEq, Fintype, Repr

/-- The shape of a button. -/
def Button2.shape : Button2 → Shape
  | .blueSquare | .redSquare => .square
  | .yellowTriangle | .greenTriangle => .triangle

/-- A world of Experiment 2: which buttons play the dog sound. -/
abbrev World2 := Button2 → Bool

/-- *If you press b, it plays a dog barking*. -/
def plays (b : Button2) : Set World2 := {w | w b = true}

instance (b : Button2) : DecidablePred (· ∈ plays b) :=
  λ w => inferInstanceAs (Decidable (w b = true))

instance (S T : Set World2) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] :
    Decidable (S ⊆ T) :=
  decidable_of_iff (∀ w, w ∈ S → w ∈ T) Iff.rfl

/-- The cell-level answer *if you press the [shape]s, it plays a dog barking*: the dog button is
among that shape's, weaker than any one button's answer. -/
def shapePlays (s : Shape) : Set World2 := {w | ∃ b, b.shape = s ∧ w b = true}

instance (s : Shape) : DecidablePred (· ∈ shapePlays s) :=
  λ w => inferInstanceAs (Decidable (∃ b, Button2.shape b = s ∧ w b = true))

/-- Exhaustification against the cell-level answers. -/
def exhCell (p : Set World2) : Set World2 :=
  {w | w ∈ p ∧ ∀ s, ¬ p ⊆ shapePlays s → w ∉ shapePlays s}

/-- Exhaustification against every button's answer. -/
def exhButton (p : Set World2) : Set World2 :=
  {w | w ∈ p ∧ ∀ b, ¬ p ⊆ plays b → w ∉ plays b}

instance (p : Set World2) [DecidablePred (· ∈ p)] : DecidablePred (· ∈ exhCell p) :=
  λ w => inferInstanceAs (Decidable (w ∈ p ∧ ∀ s, ¬ p ⊆ shapePlays s → w ∉ shapePlays s))

instance (p : Set World2) [DecidablePred (· ∈ p)] : DecidablePred (· ∈ exhButton p) :=
  λ w => inferInstanceAs (Decidable (w ∈ p ∧ ∀ b, ¬ p ⊆ plays b → w ∉ plays b))

/-- The optimally informative answer, *If you press the triangles, it plays the sound of a dog
barking*, is asked about the squares; the overly informative one, *If you press the blue
square, it plays the sound of a dog barking*, about the red square. -/
inductive AnswerType
  | optimallyInformative
  | overlyInformative
  deriving DecidableEq, Repr

/-- Mary's answer. -/
def AnswerType.form : AnswerType → Set World2
  | .optimallyInformative => shapePlays .triangle
  | .overlyInformative => plays .blueSquare

/-- The proposition the participant is asked about. -/
def AnswerType.query : AnswerType → Set World2
  | .optimallyInformative => shapePlays .square
  | .overlyInformative => plays .redSquare

instance (a : AnswerType) : DecidablePred (· ∈ a.form) := by
  cases a <;> unfold AnswerType.form <;> infer_instance
instance (a : AnswerType) : DecidablePred (· ∈ a.query) := by
  cases a <;> unfold AnswerType.query <;> infer_instance

/-- The answer types as named in the rows. -/
def answerTable : List (String × AnswerType) :=
  [("optimallyInformative", .optimallyInformative), ("overlyInformative", .overlyInformative)]

/-- A condition of Experiment 2: the answer type and the modal response. -/
structure Row2 where
  answerType : AnswerType
  response : Response
  deriving DecidableEq

/-- A row from an example. -/
def Row2.ofExample (ex : LinguisticExample) : Option Row2 := do
  pure ⟨← ex.parse? "answerType" answerTable, ← ex.parse? "response" responseTable⟩

/-- The conditions of Experiment 2. -/
def rows2 : List Row2 := Examples.all.filterMap Row2.ofExample

/-- Against every button's answer, both answer forms exclude the queried buttons, the modal
response in both conditions. -/
theorem rows2_response :
    ∀ r ∈ rows2,
      (if exhButton r.answerType.form ⊆ r.answerType.queryᶜ then Response.no else .cantTell) =
        r.response := by
  decide +kernel

/-- Against the cell-level answers alone, the overly informative answer leaves the red square
open: the observed perfection needs the finer alternatives, whether as relevant overly
informative answers or through an accommodated question. -/
theorem cell_level_leaves_red_open :
    ¬ exhCell AnswerType.overlyInformative.form ⊆ AnswerType.overlyInformative.queryᶜ := by
  decide +kernel

end EvcenBaleBarner2026
