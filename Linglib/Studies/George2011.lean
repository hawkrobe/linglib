import Mathlib.Data.Fin.VecNotation
import Linglib.Semantics.Questions.Exhaustivity
import Linglib.Data.Examples.George2011

/-!
# George (2011): Question Embedding and the Semantics of Answers

This file formalizes the baseline theory of [george-2011] and the two arguments the dissertation
builds on it. A *wh*-question is an abstract, a world-dependent property of the things the
*wh*-phrase ranges over; the question operator turns it into its mention-some answer set, and
composing with the exhaustivity operator, which tests extensions for identity, turns it into the
strongly exhaustive answer set. A responsive predicate holds of a question when it holds of some
answer. The strongly exhaustive answer of [groenendijk-stokhof-1984] and the weakly exhaustive
answer of [heim-1994] are recovered as the answers of a world (`Strong`, `Weak`) and shown to be
the substrate's `strongAnswer` and `weakAnswer` over the mention-some set; the strongly
exhaustive set has a unique true member at each world while the weakly exhaustive set has only a
least one, which is why the existential embedding rule cannot use it. Partial answers are the
unions of answers.

The first argument dismantles the case for weak exhaustivity from consistent pairs such as
*Maggie knows who was admitted but not who wasn't* ([sharvit-2002]): with negation outscoping
the restrictor the strongly exhaustive answer sets of a question and its negation coincide
(`negation_generalization`), but once the restrictor sits outside the negation, uncertainty about
its extension (`domain_uncertainty`) or a negation that is not complementation
(`rupert_not_knows_rejected`) makes the pair true on strongly exhaustive readings alone. The
second is that *know* lacks the reducibility property: agents with the same propositional
knowledge can differ in question knowledge because a false belief in a mention-some answer
defeats it (`knowsQ_not_reducible`), whereas the existential rule makes any predicate reducible
(`reducible_embed`).

## Implementation notes

* Abstracts are functions `W → τ → Prop`, the dissertation's intensions with the world argument
  first; a product `τ` covers multiple *wh*. Answer sets are `Set (Set W)`, and an agent's
  propositional knowledge in the admission scenarios is the entailment of the proposition by the
  set of worlds compatible with what the agent was told.
* The strongly exhaustive set built through the exhaustivity operator admits contradictory
  members for extensions no world realizes; the set of Strong answers omits them, the
  dissertation's own footnoted discrepancy (`exists_Strong_of_nonempty`).
* The admission scenarios assign four candidates a status of not having applied, being admitted,
  rejected or waitlisted. Knowledge in the newspaper scenario is true belief, the propositional
  relation the dissertation holds fixed while varying belief.

## References

* [george-2011]
* [groenendijk-stokhof-1984]
* [heim-1994]
* [karttunen-1977]
* [lahiri-2002]
* [sharvit-2002]
-/

namespace George2011

open Questions Data.Examples

variable {W τ E : Type*}

/-! ### Answer sets from abstracts -/

/-- The question operator: the mention-some answers of an abstract, one per value. -/
def mentionSome (α : W → τ → Prop) : Set (Set W) := Set.range λ β => {w | α w β}

/-- The exhaustivity operator on extensions: identity with the given extension. -/
def X (γ : τ → Prop) : (τ → Prop) → Prop := λ δ => γ = δ

/-- The strongly exhaustive answers: the question operator over the exhaustified abstract. -/
def stronglyExhaustive (α : W → τ → Prop) : Set (Set W) := mentionSome λ w => X (α w)

theorem mem_mentionSome {α : W → τ → Prop} {p : Set W} :
    p ∈ mentionSome α ↔ ∃ β, {w | α w β} = p := Set.mem_range

theorem mem_stronglyExhaustive {α : W → τ → Prop} {p : Set W} :
    p ∈ stronglyExhaustive α ↔ ∃ S, {w | α w = S} = p := Set.mem_range

/-- The strongly exhaustive answer of a world: the worlds where the abstract has the same
extension. -/
def Strong (w : W) (α : W → τ → Prop) : Set W := {w' | α w' = α w}

/-- The weakly exhaustive answer of a world: the worlds where the extension includes this one. -/
def Weak (w : W) (α : W → τ → Prop) : Set W := {w' | ∀ β, α w β → α w' β}

theorem Strong_eq_strongAnswer (w : W) (α : W → τ → Prop) :
    Strong w α = strongAnswer (mentionSome α) w := by
  ext v
  simp only [Strong, Set.mem_ofPred_eq, strongAnswer, mentionSome, Set.forall_mem_range]
  exact ⟨λ h β => h ▸ Iff.rfl, λ h => funext λ β => propext (h β).symm⟩

theorem Weak_eq_weakAnswer (w : W) (α : W → τ → Prop) :
    Weak w α = weakAnswer (mentionSome α) w := by
  ext v
  simp [Weak, weakAnswer, trueAnswers, mentionSome]

theorem Strong_mem_stronglyExhaustive (w : W) (α : W → τ → Prop) :
    Strong w α ∈ stronglyExhaustive α :=
  ⟨α w, rfl⟩

/-- A satisfiable strongly exhaustive answer is the Strong answer of one of its worlds. -/
theorem exists_Strong_of_nonempty {α : W → τ → Prop} {p : Set W} (hp : p ∈ stronglyExhaustive α)
    (hne : p.Nonempty) : ∃ w, p = Strong w α := by
  obtain ⟨S, rfl⟩ := hp
  obtain ⟨w, hw⟩ := hne
  have : α w = S := hw
  subst this
  exact ⟨w, rfl⟩

/-- Each world's Strong answer is the unique true strongly exhaustive answer there. -/
theorem trueAnswers_stronglyExhaustive (w : W) (α : W → τ → Prop) :
    trueAnswers (stronglyExhaustive α) w = {Strong w α} := by
  ext p
  simp only [trueAnswers, mem_stronglyExhaustive, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨S, rfl⟩, hw⟩
    have : α w = S := hw
    subst this
    rfl
  · rintro rfl
    exact ⟨⟨α w, rfl⟩, rfl⟩

/-- The weakly exhaustive answers of the worlds. -/
def weaklyExhaustive (α : W → τ → Prop) : Set (Set W) := Set.range λ w => Weak w α

theorem self_mem_Weak (w : W) (α : W → τ → Prop) : w ∈ Weak w α := λ _ h => h

/-- A world's Weak answer is the least true member of the weakly exhaustive set, not its only
one: recovering it needs maximality, which the existential embedding rule cannot supply. -/
theorem isStrongestTrueAnswer_Weak (w : W) (α : W → τ → Prop) :
    IsStrongestTrueAnswer (weaklyExhaustive α) w (Weak w α) :=
  ⟨⟨⟨w, rfl⟩, self_mem_Weak w α⟩,
    λ _ ⟨⟨_, hv⟩, hwq⟩ => hv ▸ λ _ hw' β hβ => hw' β ((hv ▸ hwq) β hβ)⟩

/-! ### Partial answers -/

/-- The generalized partial answers: the unions of subsets of the answer set. -/
def part (P : Set (Set W)) : Set (Set W) := Set.sUnion '' 𝒫 P

theorem subset_part (P : Set (Set W)) : P ⊆ part P :=
  λ p hp => ⟨{p}, Set.singleton_subset_iff.mpr hp, Set.sUnion_singleton p⟩

theorem part_mono : Monotone (part : Set (Set W) → Set (Set W)) :=
  λ _ _ h => Set.image_mono (Set.powerset_mono.mpr h)

theorem part_part (P : Set (Set W)) : part (part P) = part P := by
  refine Set.Subset.antisymm ?_ (subset_part _)
  rintro p ⟨𝒬, h𝒬, rfl⟩
  choose S hS hSq using λ q (hq : q ∈ 𝒬) => h𝒬 hq
  refine ⟨{s | ∃ q, ∃ hq : q ∈ 𝒬, s ∈ S q hq}, λ s ⟨q, hq, hs⟩ => hS q hq hs, ?_⟩
  ext w
  simp only [Set.mem_sUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨s, ⟨q, hq, hs⟩, hw⟩
    exact ⟨q, hq, hSq q hq ▸ Set.mem_sUnion.mpr ⟨s, hs, hw⟩⟩
  · rintro ⟨q, hq, hw⟩
    obtain ⟨s, hs, hws⟩ := Set.mem_sUnion.mp (hSq q hq ▸ hw)
    exact ⟨s, ⟨q, hq, hs⟩, hws⟩

/-- Every mention-some answer is a partial answer to the strongly exhaustive set: the union of
the strongly exhaustive answers whose extension contains its value. -/
theorem mentionSome_subset_part (α : W → τ → Prop) :
    mentionSome α ⊆ part (stronglyExhaustive α) := by
  rintro p ⟨β, rfl⟩
  refine ⟨{q | ∃ S, S β ∧ {w | α w = S} = q}, λ q ⟨S, _, hq⟩ => ⟨S, hq⟩, ?_⟩
  ext w
  simp only [Set.mem_sUnion, Set.mem_ofPred_eq]
  exact ⟨λ ⟨_, ⟨S, hS, rfl⟩, hw⟩ => (show α w = S from hw) ▸ hS,
    λ h => ⟨{w' | α w' = α w}, ⟨α w, h, rfl⟩, rfl⟩⟩

/-! ### Embedding and reducibility -/

/-- The embedding rule: a responsive predicate holds of a question when it holds of some
answer. -/
def embed (R : Set W → E → Prop) (P : Set (Set W)) (x : E) : Prop := ∃ p ∈ P, R p x

/-- The reducibility property: agents related to the same propositions are related to the same
questions. -/
def Reducible (R : Set W → E → Prop) (RQ : Set (Set W) → E → Prop) : Prop :=
  ∀ a b, (∀ p, R p a ↔ R p b) → ∀ P, RQ P a ↔ RQ P b

theorem reducible_embed (R : Set W → E → Prop) : Reducible R (embed R) :=
  λ _ _ h _ => exists_congr λ p => and_congr_right λ _ => h p

/-- Knowledge as true belief, the propositional relation the dissertation holds fixed. -/
def knows (believes : Set W → E → Prop) (w : W) (p : Set W) (x : E) : Prop := believes p x ∧ w ∈ p

/-- Question-embedding *know*: knowing an answer and believing no false one. -/
def knowsQ (believes : Set W → E → Prop) (w : W) (P : Set (Set W)) (x : E) : Prop :=
  embed (knows believes w) P x ∧ ∀ p ∈ P, believes p x → w ∈ p

/-- Two agents with the same knowledge, one of whom believes a false answer: *know* lacks the
reducibility property. -/
theorem knowsQ_not_reducible {believes : Set W → E → Prop} {w : W} {P : Set (Set W)} {a b : E}
    {p₁ p₂ : Set W} (h₁ : p₁ ∈ P) (h₂ : p₂ ∈ P) (hw₁ : w ∈ p₁) (hw₂ : w ∉ p₂)
    (ha₁ : believes p₁ a) (hb₂ : believes p₂ b) (ha : ∀ p ∈ P, believes p a → w ∈ p)
    (hab : ∀ p, w ∈ p → (believes p a ↔ believes p b)) :
    ¬ Reducible (knows believes w) (knowsQ believes w) := λ h =>
  hw₂ ((((h a b λ p => and_congr_left λ hp => hab p hp) P).mp ⟨⟨p₁, h₁, ha₁, hw₁⟩, ha⟩).2 p₂ h₂ hb₂)

/-! ### The newspaper scenario -/

/-- A world of the newspaper scenario: whether Rupert can buy one at PaperWorld and at Newstopia. -/
abbrev Newspaper := Bool × Bool

/-- The mention-some answers to *where can Rupert buy a newspaper*. -/
def newspaperAnswers : Set (Set Newspaper) := {{w | w.1 = true}, {w | w.2 = true}}

/-- Janna (`false`) believes what holds at PaperWorld, Red (`true`) also the Newstopia answer. -/
def newspaperBelieves (p : Set Newspaper) : Bool → Prop
  | false => {w | w.1 = true} ⊆ p
  | true => {w | w.1 = true ∧ w.2 = true} ⊆ p

private theorem janna_iff_red {p : Set Newspaper} (hp : (true, false) ∈ p) :
    newspaperBelieves p false ↔ newspaperBelieves p true := by
  refine ⟨λ h _ hw => h hw.1, λ h w hw => ?_⟩
  obtain ⟨a, b⟩ := w
  cases a <;> cases b
  all_goals first | exact absurd hw Bool.false_ne_true | exact hp | exact h ⟨rfl, rfl⟩

theorem newspaper_not_reducible :
    ¬ Reducible (knows newspaperBelieves (true, false)) (knowsQ newspaperBelieves (true, false)) :=
  knowsQ_not_reducible (P := newspaperAnswers) (a := false) (b := true) (p₁ := {w | w.1 = true})
    (p₂ := {w | w.2 = true}) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl) rfl
    Bool.false_ne_true (λ _ h => h) (λ _ h => h.2)
    (λ p hp h => by
      rcases Set.mem_insert_iff.mp hp with rfl | rfl
      · rfl
      · exact absurd (h (show (true, false) ∈ {w : Newspaper | w.1 = true} from rfl))
          Bool.false_ne_true)
    (λ _ hp => janna_iff_red hp)

/-! ### Negation and strong exhaustivity -/

/-- With negation outscoping the restrictor and a fixed domain, a question and its negation have
the same strongly exhaustive answers. -/
theorem negation_generalization (α : W → τ → Prop) :
    stronglyExhaustive (λ w x => ¬ α w x) = stronglyExhaustive α := by
  ext p
  simp only [mem_stronglyExhaustive]
  constructor
  · rintro ⟨S, rfl⟩
    refine ⟨λ x => ¬ S x, ?_⟩
    ext w
    simp only [Set.mem_ofPred_eq]
    exact ⟨λ h => funext λ x => by rw [congrFun h x]; exact propext not_not,
      λ h => funext λ x => by rw [← congrFun h x]; exact (propext not_not).symm⟩
  · rintro ⟨S, rfl⟩
    refine ⟨λ x => ¬ S x, ?_⟩
    ext w
    simp only [Set.mem_ofPred_eq]
    exact ⟨λ h => funext λ x => propext (not_iff_not.mp (iff_of_eq (congrFun h x))),
      λ h => h ▸ rfl⟩

/-- A candidate's status in the admission scenarios. -/
inductive Status
  | notApplicant | admitted | rejected | waitlisted
  deriving DecidableEq, Repr

/-- A world assigns the four candidates a status. -/
abbrev Admissions := Fin 4 → Status

/-- *Which applicants were admitted*: the restrictor outside the negation. -/
def admittedApplicant (w : Admissions) (x : Fin 4) : Prop :=
  w x ≠ .notApplicant ∧ w x = .admitted

/-- *Which applicants weren't admitted*. -/
def notAdmittedApplicant (w : Admissions) (x : Fin 4) : Prop :=
  w x ≠ .notApplicant ∧ w x ≠ .admitted

/-- *Which students were rejected*, the reading of *weren't admitted* that is not
complementation. -/
def rejected (w : Admissions) (x : Fin 4) : Prop := w x = .rejected

/-- An agent identified with the worlds compatible with what they know knows a proposition the
state entails. -/
def stateKnows (p σ : Set W) : Prop := σ ⊆ p

/-- Maggie's state: Riley and Adam are the admitted applicants and nobody else was admitted. -/
def maggie : Set Admissions := {w | ∀ x, w x = .admitted ↔ x = 0 ∨ x = 1}

/-- Maggie's state is the strongly exhaustive answer that Riley and Adam were the admitted
applicants. -/
theorem maggie_eq : {w | admittedApplicant w = λ x => x = 0 ∨ x = 1} = maggie :=
  Set.ext λ w => ⟨λ hw x => have hx := iff_of_eq (congrFun hw x)
      ⟨λ h => hx.mp ⟨λ hn => Status.noConfusion (h.symm.trans hn), h⟩, λ h => (hx.mpr h).2⟩,
    λ hw => funext λ x => propext ⟨λ h => (hw x).mp h.2,
      λ h => ⟨λ hn => Status.noConfusion (((hw x).mpr h).symm.trans hn), (hw x).mpr h⟩⟩⟩

private def robinRejected : Admissions :=
  ![Status.admitted, Status.admitted, Status.rejected, Status.notApplicant]

private def robinAbsent : Admissions :=
  ![Status.admitted, Status.admitted, Status.notApplicant, Status.notApplicant]

private theorem robinRejected_mem : robinRejected ∈ maggie :=
  show ∀ x, robinRejected x = .admitted ↔ x = 0 ∨ x = 1 by decide

private theorem robinAbsent_mem : robinAbsent ∈ maggie :=
  show ∀ x, robinAbsent x = .admitted ↔ x = 0 ∨ x = 1 by decide

/-- Maggie's state entails no strongly exhaustive answer about the applicants not admitted: it
does not settle whether Robin applied. -/
theorem maggie_not_knows_notAdmitted :
    ¬ embed stateKnows (stronglyExhaustive notAdmittedApplicant) maggie := by
  rintro ⟨p, ⟨S, rfl⟩, hσ⟩
  have h₁ : notAdmittedApplicant robinRejected = S := hσ robinRejected_mem
  have h₂ : notAdmittedApplicant robinAbsent = S := hσ robinAbsent_mem
  exact (Eq.mp (congrFun (h₁.trans h₂.symm) 2) ⟨by decide, by decide⟩).1 rfl

theorem maggie_knows_admitted :
    embed stateKnows (stronglyExhaustive admittedApplicant) maggie :=
  ⟨maggie, ⟨_, maggie_eq⟩, subset_rfl⟩

/-- Once the restrictor sits outside the negation, the two answer sets come apart. -/
theorem domain_uncertainty :
    stronglyExhaustive notAdmittedApplicant ≠ stronglyExhaustive admittedApplicant := λ h =>
  maggie_not_knows_notAdmitted ⟨maggie, h ▸ ⟨_, maggie_eq⟩, subset_rfl⟩

/-- Rupert's state: all four students applied, Anne and Red are the admitted ones, and Alex and
Jonathan were each rejected or waitlisted. -/
def rupert : Set Admissions :=
  {w | (∀ x, w x ≠ .notApplicant) ∧ ∀ x, w x = .admitted ↔ x = 0 ∨ x = 1}

private def jonathanRejected : Admissions :=
  ![Status.admitted, Status.admitted, Status.waitlisted, Status.rejected]

private def jonathanWaitlisted : Admissions :=
  ![Status.admitted, Status.admitted, Status.waitlisted, Status.waitlisted]

private theorem jonathanRejected_mem : jonathanRejected ∈ rupert :=
  show (∀ x, jonathanRejected x ≠ .notApplicant) ∧
    ∀ x, jonathanRejected x = .admitted ↔ x = 0 ∨ x = 1 by decide

private theorem jonathanWaitlisted_mem : jonathanWaitlisted ∈ rupert :=
  show (∀ x, jonathanWaitlisted x ≠ .notApplicant) ∧
    ∀ x, jonathanWaitlisted x = .admitted ↔ x = 0 ∨ x = 1 by decide

theorem rupert_knows_admitted :
    embed stateKnows (stronglyExhaustive admittedApplicant) rupert :=
  ⟨maggie, ⟨_, maggie_eq⟩, λ _ hw => hw.2⟩

/-- Complementation failure: with the domain known, Rupert still knows no strongly exhaustive
answer to *which were rejected*. -/
theorem rupert_not_knows_rejected :
    ¬ embed stateKnows (stronglyExhaustive rejected) rupert := by
  rintro ⟨p, ⟨S, rfl⟩, hσ⟩
  have h₁ : rejected jonathanRejected = S := hσ jonathanRejected_mem
  have h₂ : rejected jonathanWaitlisted = S := hσ jonathanWaitlisted_mem
  exact absurd (Eq.mp (congrFun (h₁.trans h₂.symm) 3) rfl)
    (by decide : jonathanWaitlisted 3 ≠ .rejected)

/-! ### The dissertation's judgments -/

/-- The sentences whose truth in their scenarios the file settles. -/
inductive Sentence
  | admittedKnown | notAdmittedKnown | admittedButNot | fourStudents | jannaNewspaper
  | redNewspaper
  deriving DecidableEq, Repr

/-- What each sentence claims in its scenario, on the readings the dissertation assigns. -/
def Verdict : Sentence → Prop
  | .admittedKnown => embed stateKnows (stronglyExhaustive admittedApplicant) maggie
  | .notAdmittedKnown => embed stateKnows (stronglyExhaustive notAdmittedApplicant) maggie
  | .admittedButNot => embed stateKnows (stronglyExhaustive admittedApplicant) maggie ∧
      ¬ embed stateKnows (stronglyExhaustive notAdmittedApplicant) maggie
  | .fourStudents => embed stateKnows (stronglyExhaustive admittedApplicant) rupert ∧
      ¬ embed stateKnows (stronglyExhaustive rejected) rupert
  | .jannaNewspaper => knowsQ newspaperBelieves (true, false) newspaperAnswers false
  | .redNewspaper => knowsQ newspaperBelieves (true, false) newspaperAnswers true

structure Row where
  sentence : Sentence
  holds : Bool
  deriving DecidableEq, Repr

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let sentence ← ex.parse? "sentence" [("admittedKnown", Sentence.admittedKnown),
    ("notAdmittedKnown", .notAdmittedKnown), ("admittedButNot", .admittedButNot),
    ("fourStudents", .fourStudents), ("jannaNewspaper", .jannaNewspaper),
    ("redNewspaper", .redNewspaper)]
  let holds ← ex.parse? "holds" [("yes", true), ("no", false)]
  pure ⟨sentence, holds⟩

def rows : List Row := Examples.all.filterMap Row.ofExample

theorem rows_eq : rows = [⟨.admittedKnown, true⟩, ⟨.notAdmittedKnown, false⟩,
    ⟨.admittedButNot, true⟩, ⟨.fourStudents, true⟩, ⟨.jannaNewspaper, true⟩,
    ⟨.redNewspaper, false⟩] := by
  decide

/-- Every judgment the dissertation reports for its scenarios holds in the models. -/
theorem rows_predicted : ∀ r ∈ rows, (r.holds = true ↔ Verdict r.sentence) := by
  simp only [rows_eq, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
    and_true, true_iff, false_iff, Bool.false_eq_true]
  refine ⟨maggie_knows_admitted, maggie_not_knows_notAdmitted,
    ⟨maggie_knows_admitted, maggie_not_knows_notAdmitted⟩,
    ⟨rupert_knows_admitted, rupert_not_knows_rejected⟩,
    ⟨⟨_, Set.mem_insert _ _, λ _ h => h, rfl⟩, λ p hp h => ?_⟩, λ h => ?_⟩
  · rcases Set.mem_insert_iff.mp hp with rfl | rfl
    · rfl
    · exact absurd (h (show (true, false) ∈ {w : Newspaper | w.1 = true} from rfl))
        Bool.false_ne_true
  · exact absurd (h.2 _ (Set.mem_insert_of_mem _ rfl) λ _ hw => hw.2) Bool.false_ne_true

end George2011
