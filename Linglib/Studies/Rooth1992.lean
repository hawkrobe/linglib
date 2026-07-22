import Linglib.Semantics.Alternatives.AltMeaning
import Linglib.Semantics.Focus.Interpretation
import Linglib.Semantics.Focus.Control
import Linglib.Semantics.Focus.Particles
import Linglib.Semantics.Composition.Tree
import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Data.Examples.Rooth1992

/-!
# Rooth 1992: A theory of focus interpretation

Formalises [rooth-1992] over the example rows in
`Data/Examples/Rooth1992.json`: question-answer congruence via the
focus interpretation principle (FIP, the paper's (27)), association
with *only* ((26a), (30b)), the contrasting-phrases rule (14), and the
argument that focus *constrains* rather than *fixes* the domain of
*only* (the *Recognitions* example (7)).

The question-answer model is the paper's §2.4 paradigm — "Who cut Bill
down to size?" answered by *[Mary]F cut Bill down to size* (23), with
the alternative answers of (24) — in a four-world model crossing
subjects {Mary, Monique} with objects {Bill, Björn}. The *only* model
is the §2.1 introduction scenario (Mary introduced Bill and Tom to
Sue). Focus values are computed, not stipulated: the `interp` engine
that computes ordinary values at `M = Id` computes O/A-values at
`M = AltMeaning`, grounding the stipulated Hamblin sets, and the
lexicon's surface forms are checked against the English fragment
entries.
-/

namespace Rooth1992

open Alternatives
open Focus.Interpretation (fip PropFocusValue qaCongruent qaCongruentWeak)

/-! ### The question-answer world model -/

/-- Worlds crossing cutter (Mary/Monique) × cuttee (Bill/Björn),
    after the answer columns of [rooth-1992] (24). Sufficient to
    distinguish subject-focus from object-focus alternative sets. -/
inductive QAWorld where
  | maryBill | maryBjorn | moniqueBill | moniqueBjorn
  deriving DecidableEq, Repr

open QAWorld

/-- "Mary cut Bill down to size" — true exactly at `maryBill`. -/
def maryCutBill : Set QAWorld := {maryBill}

/-- "Monique cut Bill down to size" — true exactly at `moniqueBill`. -/
def moniqueCutBill : Set QAWorld := {moniqueBill}

/-- "Mary cut Björn down to size" — true exactly at `maryBjorn`. -/
def maryCutBjorn : Set QAWorld := {maryBjorn}

/-! ### Alternative meanings -/

/-- Focused *[MARY]F* in the answer *[Mary]F cut Bill down to size*
    ((23Aa) of [rooth-1992] §2.4): O-value = "Mary";
    A-value = {"Mary", "Monique"}. -/
def altSubjectFocused : AltMeaning String :=
  { oValue := "Mary", aValue := ["Mary", "Monique"] }

/-- Non-focused "cut Bill down to size": singleton A-value. Exercises
    `AltMeaning.unfeatured`. -/
def altPredicateUnfeatured : AltMeaning String :=
  AltMeaning.unfeatured "cut Bill down to size"

/-- Unfeatured O-value equals the input. -/
theorem unfeatured_preserves_oValue :
    altPredicateUnfeatured.oValue = "cut Bill down to size" := rfl

/-- Unfeatured A-value is a singleton containing the O-value — "the
    focus semantic value of a focus-free phrase is the unit set of its
    ordinary semantic value" ([rooth-1992] (42)). -/
theorem unfeatured_singleton_aValue :
    altPredicateUnfeatured.aValue = ["cut Bill down to size"] := rfl

/-! ### Question-answer congruence and the FIP

The question-answer constraint ((26d) of [rooth-1992] §3, motivated by
the §2.4 question-answer paradigm): in a Q-A pair ⟨ψ, α⟩,
⟦ψ⟧° ⊆ ⟦α⟧f — the ordinary semantic value of the question is a subset
of the focus semantic value of the answer. The FIP (27) schematizes
this as Γ ⊆ ⟦α⟧f with Γ resolved to the question denotation. -/

/-- "Who cut Bill down to size?" ((23Qa)) — Hamblin question with
    subject alternatives, the (25a) value restricted to the model's
    individuals. -/
def q_whoCutBill : PropFocusValue QAWorld :=
  {maryCutBill, moniqueCutBill}

/-- Focus value of *[MARY]F cut Bill down to size* ((23Aa)) — same
    subject alternatives. -/
def fv_subjectFocus : PropFocusValue QAWorld :=
  {maryCutBill, moniqueCutBill}

/-- Focus value of *Mary cut [BILL]F down to size* ((23Ab)) — object
    alternatives (varies object, not subject). -/
def fv_objectFocus : PropFocusValue QAWorld :=
  {maryCutBill, maryCutBjorn}

/-- Q-A congruence: subject focus value = question denotation. -/
theorem qa_subject_focus_congruent :
    qaCongruent fv_subjectFocus q_whoCutBill := rfl

/-- The FIP holds for subject focus: question alternatives ⊆ focus
    value — trivially, since the sets are equal. -/
theorem fip_congruent :
    fip q_whoCutBill fv_subjectFocus :=
  fun _ h => h

/-- "moniqueCutBill" is in the question alternatives... -/
theorem moniqueCutBill_in_question :
    moniqueCutBill ∈ q_whoCutBill := Or.inr rfl

/-- ...but it is NOT in the object-focus alternative set... -/
theorem moniqueCutBill_not_in_objectFocus :
    moniqueCutBill ∉ fv_objectFocus := by
  simp [fv_objectFocus, moniqueCutBill, maryCutBill, maryCutBjorn]

/-- ...so the FIP fails for object focus: (23Ab) is linked to (23Qa)
    only by a dotted (inappropriate) line in the paper's (23). -/
theorem fip_fails_object_focus :
    ¬ fip q_whoCutBill fv_objectFocus :=
  fun h => moniqueCutBill_not_in_objectFocus (h moniqueCutBill_in_question)

/-! ### The question as focus antecedent -/

/-- 'Who cut Bill down to size?' as a focus antecedent
    (`Focus.Antecedent`): the anaphoric source of the squiggle's
    contrast set. -/
def qaAntecedent : Focus.Antecedent QAWorld := .question q_whoCutBill

/-- Question antecedents license the new-information use. -/
theorem qaAntecedent_use : qaAntecedent.use = .newInfo := rfl

/-- The antecedent admits subject focus — the FIP routed through the
    antecedent layer. -/
theorem qaAntecedent_admits_subjectFocus :
    qaAntecedent.Admits fv_subjectFocus := fip_congruent

/-- The antecedent rejects object focus. -/
theorem qaAntecedent_rejects_objectFocus :
    ¬ qaAntecedent.Admits fv_objectFocus := fip_fails_object_focus

/-- The question antecedent *fully* resolves against the subject-focus
    meaning: all three clauses of the squiggle presupposition
    ([rooth-1992] (40) set case), not just the FIP — the contrast set
    contains the ordinary value `maryCutBill` and the distinct
    alternative `moniqueCutBill`. -/
theorem qaAntecedent_resolves :
    qaAntecedent.Resolves maryCutBill fv_subjectFocus :=
  ⟨fip_congruent, Or.inl rfl,
    moniqueCutBill, Or.inr rfl,
    fun h => by simp [moniqueCutBill, maryCutBill] at h⟩

/-- A focus-free answer cannot resolve any antecedent: its focus value
    is the unit set of its ordinary value ((42)), defeating the
    contrast clause — "the argument must contain a focus". -/
theorem focusFree_answer_cannot_resolve (Γ : PropFocusValue QAWorld) :
    ¬ Focus.SquiggleSet maryCutBill {maryCutBill} Γ :=
  Focus.not_squiggleSet_singleton maryCutBill Γ

/-- Contrasting phrases ([rooth-1992] (14), on the symmetric-contrast
    joke opening (11)): construe α as contrasting with β if
    ⟦β⟧° ∈ ⟦α⟧f. *Canadian farmer*'s ordinary value is a member of
    *[American]F farmer*'s focus value distinct from its ordinary
    value. -/
theorem farmer_contrast :
    Focus.SquiggleInd "American farmer"
      ({"American farmer", "Canadian farmer"} : Set String)
      "Canadian farmer" :=
  ⟨Or.inr rfl, by decide⟩

/-! ### Constraining vs fixing the domain of *only*

With a focused transitive verb — *Mary only [read]F The Recognitions*
((7) of [rooth-1992] §2.1) — the full focus value contains "even
trivial relations", so [rooth-1985]'s move of *fixing* *only*'s domain
`C` to it yields unsatisfiable truth conditions, while intuitively (7)
can be true. The 1992 revision (9c) merely *constrains* `C ⊆ ⟦VP⟧f`,
leaving `C` to pragmatics: it "might be quite a small set", e.g.
{read(c), understand(c)} ((37c)). A lexically carried alternative list
cannot be narrowed this way. -/

/-- Worlds tracking Mary's relation to *The Recognitions*. -/
inductive RWorld where
  | readOnly      -- read it, nothing more
  | readAndGrasp  -- read and understood it
  | neither
  deriving DecidableEq, Repr

/-- 'reading The Recognitions'. -/
def reading : Set RWorld := {.readOnly, .readAndGrasp}
/-- 'understanding The Recognitions'. -/
def grasping : Set RWorld := {.readAndGrasp}
/-- A trivial property of the same semantic type — a member of the
    full focus value. -/
def trivialR : Set RWorld := Set.univ

/-- With the pragmatically restricted domain ((37c)), *only READ* is
    satisfiable: true where Mary read without understanding. -/
theorem restricted_only_satisfiable :
    RWorld.readOnly ∈
      Focus.onlyVia {reading, grasping} reading := by
  intro q hq hw
  rcases hq with rfl | rfl
  · rfl
  · exact absurd hw (by simp [grasping])

/-- With the domain fixed to the full focus value (trivial property
    included), *only READ* is unsatisfiable — fixing `C`
    over-generates exclusions. -/
theorem direct_only_unsatisfiable :
    Focus.onlyVia {reading, grasping, trivialR} reading = ∅ := by
  have hne : trivialR ≠ reading := fun h =>
    (by simp [reading] : RWorld.neither ∉ reading)
      (h ▸ Set.mem_univ RWorld.neither)
  ext w
  simp only [Focus.mem_onlyVia, Set.mem_empty_iff_false, iff_false]
  exact fun hw => hne (hw trivialR (by simp) (Set.mem_univ w))

private def readingB : RWorld → Bool
  | .readOnly | .readAndGrasp => true
  | .neither => false
private def graspingB : RWorld → Bool
  | .readAndGrasp => true
  | _ => false
private def trivialB : RWorld → Bool := fun _ => true

/-- The same over-generation exhibited on `TraditionalOnly` itself:
    with a lexically carried full alternative list its assertion is
    everywhere false in this model, and no pragmatic narrowing is
    possible — the list is fixed in the lexical entry. -/
theorem traditional_only_unsatisfiable (w : RWorld) :
    (Focus.Particles.TraditionalOnly.mk
      readingB [graspingB, trivialB]).assertion w = false := by
  cases w <;> rfl

/-! ### Association with *only*

The focusing adverb constraint ((26a) of [rooth-1992] §3): the domain
of quantification `C` of a focusing adverb with argument α satisfies
`C ⊆ ⟦α⟧f`. The lexical semantics (30b) is
∀P[P ∈ C ∧ P(m) → P = VP']. The model is the §2.1 introduction
scenario: Mary introduced Bill and Tom to Sue, and there were no other
introductions — so *Mary only introduced [Bill]F to Sue* (3a) is
false. -/

/-- Worlds for the *only* model: who Mary introduced to Sue. -/
inductive OnlyWorld where
  | billOnly   -- Mary introduced only Bill to Sue
  | tomOnly    -- Mary introduced only Tom to Sue
  | both       -- Mary introduced both Bill and Tom (the paper's story)
  deriving DecidableEq, Repr

open OnlyWorld

/-- "Mary introduced Bill to Sue" -/
def introBill : OnlyWorld → Bool
  | billOnly => true | tomOnly => false | both => true

/-- "Mary introduced Tom to Sue" -/
def introTom : OnlyWorld → Bool
  | billOnly => false | tomOnly => true | both => true

/-- Focus on BILL ((3a)): O-value = introBill;
    A-value = {introBill, introTom}. Focus constrains the domain of
    *only*. -/
def altBillFocused : AltMeaning (OnlyWorld → Bool) :=
  { oValue := introBill, aValue := [introBill, introTom] }

/-- "Only Bill" = Mary introduced Bill but not Tom. -/
def onlyBill : OnlyWorld → Bool
  | billOnly => true | _ => false

/-- "Only Tom" = Mary introduced Tom but not Bill. -/
def onlyTom : OnlyWorld → Bool
  | tomOnly => true | _ => false

/-- *Only* with focus on BILL: the prejacent holds and all non-actual
    alternatives are excluded ((30b)). -/
theorem only_bill_semantics :
    ∀ w, onlyBill w = (introBill w && !introTom w) :=
  fun w => by cases w <;> rfl

/-- *Only* with focus on TOM: symmetric case. -/
theorem only_tom_semantics :
    ∀ w, onlyTom w = (introTom w && !introBill w) :=
  fun w => by cases w <;> rfl

/-- Different domains → different *only* meanings. (The paper's minimal
    pair (3a)/(3b) varies focus between *Bill* and *Sue*; the model
    exhibits the domain-dependence on the introducee axis.) -/
theorem only_focus_determines_meaning :
    onlyBill ≠ onlyTom :=
  fun h => absurd (congrFun h billOnly) (by decide)

/-! ### Data rows

The rows (`Data/Examples/Rooth1992.json`) record the paper's (23):
"MARY cut Bill down to size" is congruent and "#Mary cut BILL down to
size" incongruent with "Who cut Bill down to size?", and focus
determines what *only* excludes ((3a)/(3b)). The theory explains both:
subject focus produces a focus value equal to the question denotation
(`fip_congruent`), object focus one that excludes a question
alternative (`fip_fails_object_focus`); and the FIP constrains the
domain `C` of *only*, so different focus positions yield different
exclusion domains. -/

/-- The FIP prediction for a row, read off its `focus` feature: subject
    focus ("Mary") evokes the subject-alternative focus value, object
    focus ("Bill") the object-alternative one. -/
def fipPrediction (row : Data.Examples.LinguisticExample) : Prop :=
  match row.feature? "focus" with
  | some "Mary" => fip q_whoCutBill fv_subjectFocus
  | some "Bill" => fip q_whoCutBill fv_objectFocus
  | _ => False

/-- **Transfer**: a Q-A row is acceptable iff its focus value satisfies
    the FIP against "Who cut Bill down to size?"
    ([rooth-1992] (26d)). -/
theorem qa_acceptable_iff_fip :
    ∀ row ∈ Examples.all,
      row.feature? "fip_application" = some "qaCongruence" →
      (row.judgment = .acceptable ↔ fipPrediction row) := by
  intro row hrow happ
  simp only [Examples.all, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl
  · exact absurd happ (by decide)
  · exact absurd happ (by decide)
  · exact ⟨fun _ => fip_congruent, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide),
           fun h => absurd h fip_fails_object_focus⟩

/-- Distinct focusing-adverb rows carry distinct `focus` features: the
    rows form an association-with-focus minimal pair. -/
theorem focusingAdverb_rows_differ_in_focus :
    ∀ r₁ ∈ Examples.all, ∀ r₂ ∈ Examples.all,
      r₁.feature? "fip_application" = some "focusingAdverb" →
      r₂.feature? "fip_application" = some "focusingAdverb" →
      r₁.id ≠ r₂.id → r₁.feature? "focus" ≠ r₂.feature? "focus" := by
  decide

/-- Bridge: the focusing-adverb rows differ only in focus position
    ((3a) vs (3b)), and the theory maps distinct domains to distinct
    *only* meanings. -/
theorem bridge_only_association :
    Examples.only_bill.feature? "focus" ≠
      Examples.only_sue.feature? "focus" ∧
    onlyBill ≠ onlyTom :=
  ⟨by decide, only_focus_determines_meaning⟩

/-! ### Montague lexicon and trees

The propositions above were hand-defined. Here they are derived
compositionally: entity denotations + a world-indexed verb meaning are
combined via Heim & Kratzer's `interp`, run once per world. The
particle-verb *cut … down to size* is treated as a single transitive
lexical item keyed "cut". -/

open Intensional
open Semantics.Montague (Lexicon)
open Syntax
open Semantics.Composition.Tree

/-- Entity domain for the focus model. -/
inductive E where
  | mary | monique | bill | bjorn
  deriving DecidableEq, Repr

/-- World-indexed verb semantics for "cut (down to size)".
    `cutInWorld w obj subj` follows Montague's argument order
    (object first, then subject). -/
def cutInWorld (w : QAWorld) : Denot E Unit (.e ⇒ .e ⇒ .t) :=
  fun obj subj => match w, subj, obj with
  | .maryBill,     .mary,    .bill  => True
  | .maryBjorn,    .mary,    .bjorn => True
  | .moniqueBill,  .monique, .bill  => True
  | .moniqueBjorn, .monique, .bjorn => True
  | _, _, _ => False

/-- Montague lexicon parameterized by world.
    Maps surface forms to typed denotations. -/
def focusLex (w : QAWorld) : Lexicon E Unit := fun word =>
  match word with
  | "Mary"    => some ⟨.e, E.mary⟩
  | "Monique" => some ⟨.e, E.monique⟩
  | "cut"     => some ⟨.e ⇒ .e ⇒ .t, cutInWorld w⟩
  | "Bill"    => some ⟨.e, E.bill⟩
  | "Björn"   => some ⟨.e, E.bjorn⟩
  | _ => none

/-- Syntax tree: [S [NP Mary] [VP [V cut] [NP Bill]]] -/
def tree_maryCutBill : Tree Unit String :=
  .bin (.leaf "Mary") (.bin (.leaf "cut") (.leaf "Bill"))

/-- Syntax tree: [S [NP Monique] [VP [V cut] [NP Bill]]] -/
def tree_moniqueCutBill : Tree Unit String :=
  .bin (.leaf "Monique") (.bin (.leaf "cut") (.leaf "Bill"))

/-- Syntax tree: [S [NP Mary] [VP [V cut] [NP Björn]]] -/
def tree_maryCutBjorn : Tree Unit String :=
  .bin (.leaf "Mary") (.bin (.leaf "cut") (.leaf "Björn"))

/-- Default assignment for binding-free trees. -/
private def g₀ : Core.Assignment E := λ _ => E.mary

/-- Extract the Prop truth value from a tree interpretation.
    Returns `none` if the tree is uninterpretable or has non-`t` type. -/
def treeResult (lex : Lexicon E Unit) (t : Tree Unit String) : Option Prop :=
  match interp E Unit lex g₀ t with
  | some ⟨.t, p⟩ => some p
  | _ => none

/-! ### Grounding the stipulated propositions -/

/-- Compositionally derived "Mary cut Bill" proposition. -/
def maryCutBill_comp : QAWorld → Prop :=
  fun w => (treeResult (focusLex w) tree_maryCutBill).getD False

/-- Compositionally derived "Monique cut Bill" proposition. -/
def moniqueCutBill_comp : QAWorld → Prop :=
  fun w => (treeResult (focusLex w) tree_moniqueCutBill).getD False

/-- Compositionally derived "Mary cut Björn" proposition. -/
def maryCutBjorn_comp : QAWorld → Prop :=
  fun w => (treeResult (focusLex w) tree_maryCutBjorn).getD False

/-- Direct function application matches tree interpretation. -/
theorem direct_eq_interp (w : QAWorld) :
    treeResult (focusLex w) tree_maryCutBill =
    some (cutInWorld w E.bill E.mary) := by
  cases w <;> rfl

/-- Grounding: compositional "Mary cut Bill" agrees with the
    hand-defined proposition at each world. -/
theorem comp_grounds_maryCutBill :
    maryCutBill_comp = fun w => cutInWorld w E.bill E.mary := by
  funext w; cases w <;> rfl

/-- Grounding: compositional "Monique cut Bill" = direct application. -/
theorem comp_grounds_moniqueCutBill :
    moniqueCutBill_comp = fun w => cutInWorld w E.bill E.monique := by
  funext w; cases w <;> rfl

/-- Grounding: compositional "Mary cut Björn" = direct application. -/
theorem comp_grounds_maryCutBjorn :
    maryCutBjorn_comp = fun w => cutInWorld w E.bjorn E.mary := by
  funext w; cases w <;> rfl

/-! ### The focus dimension through the engine

F-marking is a non-`pure` lexicon entry: the same `interp` that
computes ordinary values at `M = Id` computes focus values at
`M = AltMeaning` (`pure = AltMeaning.unfeatured` lifts the focus-free
entries), with `applyForward`'s `<*>` doing Hamblin functional
application. -/

/-- Alternatives do not distribute through predicate abstraction —
    the honest `none`. -/
instance (E W : Type) : PredAbs AltMeaning E W := ⟨none⟩

/-- The focus lexicon at `M = AltMeaning`: every entry `pure`-lifts
    except focused *[Mary]F*, whose entry carries the subject
    alternatives. -/
def focusLexF (w : QAWorld) : Lexicon E Unit AltMeaning := fun word =>
  match word with
  | "Mary" => some ⟨.e, (⟨E.mary, [E.mary, E.monique]⟩ : AltMeaning _)⟩
  | w' => Lexicon.lift AltMeaning (focusLex w) w'

/-- Focus-dimension tree interpretation. -/
def treeResultF (lex : Lexicon E Unit AltMeaning) (t : Tree Unit String) :
    Option (AltMeaning Prop) :=
  match interp E Unit lex g₀ t with
  | some ⟨.t, p⟩ => some p
  | _ => none

/-- The engine at `M = AltMeaning` computes the two-dimensional meaning
    of *[MARY]F cut Bill down to size*: the O-value is the ordinary
    interpretation and the A-value is the subject-alternative family —
    the focus value is computed, not stipulated. -/
theorem treeResultF_maryCutBill (w : QAWorld) :
    treeResultF (focusLexF w) tree_maryCutBill =
      some ⟨cutInWorld w E.bill E.mary,
            [cutInWorld w E.bill E.mary, cutInWorld w E.bill E.monique]⟩ := by
  cases w <;> rfl

/-- O-projection through the engine: mapping `oValue` over the
    `AltMeaning` run recovers the `Id` run. -/
theorem treeResultF_oValue (w : QAWorld) :
    (treeResultF (focusLexF w) tree_maryCutBill).map (·.oValue) =
      treeResult (focusLex w) tree_maryCutBill := by
  cases w <;> rfl

/-- The stipulated `fv_subjectFocus` is exactly the engine's computed
    alternative family, read as proposition sets. -/
theorem fv_subjectFocus_computed :
    fv_subjectFocus =
      {{w | cutInWorld w E.bill E.mary}, {w | cutInWorld w E.bill E.monique}} := by
  have h1 : ({w | cutInWorld w E.bill E.mary} : Set QAWorld) = maryCutBill := by
    ext w; cases w <;> simp [cutInWorld, maryCutBill]
  have h2 : ({w | cutInWorld w E.bill E.monique} : Set QAWorld) = moniqueCutBill := by
    ext w; cases w <;> simp [cutInWorld, moniqueCutBill]
  rw [h1, h2]
  rfl

/-! ### Fragment connection

Fragment entries provide morphological and syntactic properties; the
bridge verifies these are consistent with the model and that fragment
surface forms feed the compositional lexicon. -/

section FragmentNouns
open English.Nouns

/-- Mary is a proper name in the English fragment. -/
theorem fragment_mary_proper : mary.proper = true := rfl

/-- Bill is a proper name in the English fragment. -/
theorem fragment_bill_proper : bill.proper = true := rfl

/-- Fragment surface forms feed the Montague lexicon.
    The form field of each fragment entry matches a lexicon key. -/
theorem fragment_mary_in_lexicon :
    (focusLex .maryBill mary.formSg).isSome = true := rfl

theorem fragment_bill_in_lexicon :
    (focusLex .maryBill bill.formSg).isSome = true := rfl

end FragmentNouns

section FragmentVerbs
open English.Predicates.Verbal

/-- "cut" is transitive (NP frame). -/
theorem fragment_cut_transitive : cut.frames = [.np] := rfl

/-- "cut" has (irregular) past tense "cut" matching the lexicon key. -/
theorem fragment_cut_past_form : cut.formPast = "cut" := rfl

/-- The past form of "cut" is in the Montague lexicon. -/
theorem fragment_cut_past_in_lexicon :
    (focusLex .maryBill cut.formPast).isSome = true := rfl

end FragmentVerbs

/-! ### End to end -/

/-- End-to-end: at each world, the compositional derivation produces
    the same truth values as the hand-defined propositions used to
    build the Hamblin question. -/
theorem endToEnd_question_grounded :
    (∀ w, treeResult (focusLex w) tree_maryCutBill = some (cutInWorld w E.bill E.mary)) ∧
    (∀ w, treeResult (focusLex w) tree_moniqueCutBill = some (cutInWorld w E.bill E.monique)) :=
  ⟨fun w => by cases w <;> rfl, fun w => by cases w <;> rfl⟩

end Rooth1992
