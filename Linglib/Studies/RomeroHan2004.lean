module

public import Linglib.Data.Examples.RomeroHan2004
public import Linglib.Discourse.CommonGround
public import Linglib.Fragments.English.PolarityItems
public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.Questions.Hamblin
public import Linglib.Semantics.Questions.Bias
public import Mathlib.Order.Interval.Set.Defs

/-!
# Romero and Han (2004): On negative yes/no questions

This file formalizes the paper's derivation of the epistemic bias of yes/no questions with
preposed negation from one assumption: preposing negation contributes the conversational
epistemic operator VERUM, `verum`, true at a world when the proposition is in the common
ground at every world compatible with the speaker's knowledge and conversational goals. A
question over VERUM partitions on certainty about adding the proposition to the common
ground rather than on the proposition, `denotation_eq`, a meta-conversational move licit
only under a prior bias; the paper's positive and negative readings are the two scopes of
negation relative to VERUM, distinguished by which polarity items they license, `Licensed`.
The polarity of the implicature is fixed not by the partition, which the positive reading
shares with a *really*-question, but by the pronounced cell: pronouncing certainty asks for
conclusive evidence, so the speaker believes the negation, and pronouncing uncertainty asks
for doubts, so the speaker believes the proposition, `speakerBelief_eq`. The paper's
examples are rows: the polarity-item judgments follow licensing, and the bias of every
question with preposed negation and of every VERUM form is the one the model implicates,
`bias_of_form`.

## Implementation notes

Speaker belief is the epistemic proposition of the states settling a proposition,
`Set.Iic`. Question forms are the substrate's `Question.PQForm`, preposed negation being the
high-negation form, and a bias is the sign of the proposition the speaker's belief supports. The Principle of
Economy that makes VERUM questions biased is stated in the paper in prose and is not
formalized.

## References

* [M. Romero, C.-H. Han, *On negative yes/no questions* (2004)][romero-han-2004]
* [D. R. Ladd, *A first look at the semantics and pragmatics of negative questions and tag
  questions* (1981)][ladd-1981]
* [T. N. Höhle, *Über Verum-Fokus im Deutschen* (1992)][hohle-1992]
-/

@[expose] public section

namespace RomeroHan2004

open ModalLogic (box)
open Question (polar polar_compl PQForm)
open Set (Iic)
open Data.Examples

variable {W : Type*} (epi conv : W → W → Prop) (cg : W → Filter W) (p : Set W)

/-! ### VERUM -/

/-- The VERUM operator (43): the proposition is in the common ground at every world
compatible with the conversational goals of every world compatible with the speaker's
knowledge. -/
def verum : Set W :=
  {w | ∀ w', epi w w' → ∀ w'', conv w' w'' → p ∈ cg w''}

/-- VERUM is a necessity nested in a necessity. -/
theorem verum_eq_box_box :
    verum epi conv cg p = box epi (box conv λ w => p ∈ cg w) := rfl

/-! ### The four VERUM questions -/

/-- The yes/no questions containing VERUM: the positive reading of preposed negation, with
negation over VERUM (73), the negative reading, with VERUM over negation (68), the
*really*-question (111), and focused *NOT* (118). -/
inductive Form
  | pi
  | ni
  | really
  | notFocus
  deriving DecidableEq, Fintype

/-- The proposition under VERUM: the proposition for the positive reading and *really*, its
negation for the negative reading and focused *NOT*. -/
def prejacent : Form → Set W
  | .pi | .really => p
  | .ni | .notFocus => pᶜ

/-- Whether the form pronounces the doubt cell, the complement of VERUM: only the positive
reading, where negation scopes over VERUM, does. -/
def Form.Doubt : Form → Prop
  | .pi => True
  | .ni | .really | .notFocus => False

instance : DecidablePred Form.Doubt := λ f => by cases f <;> unfold Form.Doubt <;> infer_instance

/-- The cell a form pronounces. -/
def pronounced (f : Form) : Set W :=
  if f.Doubt then (verum epi conv cg (prejacent p f))ᶜ else verum epi conv cg (prejacent p f)

/-- The question denoted: the polar question over the pronounced cell. -/
def denotation (f : Form) : Question W := polar (pronounced epi conv cg p f)

/-- Every VERUM question denotes the partition on certainty about its prejacent (48), (69),
(74), whichever cell it pronounces. -/
theorem denotation_eq (f : Form) :
    denotation epi conv cg p f = polar (verum epi conv cg (prejacent p f)) := by
  unfold denotation pronounced
  split_ifs <;> simp

/-- The positive reading and the *really*-question denote the same partition (84), (85). -/
theorem denotation_pi_eq_really :
    denotation epi conv cg p .pi = denotation epi conv cg p .really := by
  simp [denotation_eq, prejacent]

/-! ### The epistemic implicature

A question pronouncing certainty about its prejacent asks for conclusive evidence for it,
which the addressee can only supply if the prejacent is the addressee's proposition and its
negation the speaker's belief; a question pronouncing uncertainty asks for doubts, so the
prejacent is the speaker's belief. -/

/-- The speaker's original belief implicated by a form: the epistemic proposition of the
states settling the prejacent's negation, or the prejacent itself for the doubt cell. -/
def speakerBelief (f : Form) : Set (Set W) :=
  if f.Doubt then Iic (prejacent p f) else Iic (prejacent p f)ᶜ

/-- The bias each form implicates: belief in the proposition for the preposed-negation
readings (81), (82) and focused *NOT* (117), belief in its negation for *really* (110). -/
def Form.implicature : Form → Polarity
  | .pi | .ni | .notFocus => .positive
  | .really => .negative

/-- The implicated belief settles the proposition under the polarity of the form's implicature;
the partition shared by the positive reading and *really* cannot fix it. -/
theorem speakerBelief_eq (f : Form) : speakerBelief p f = Iic (f.implicature • p) := by
  cases f <;> simp [speakerBelief, Form.Doubt, Form.implicature, prejacent]

/-! ### Polarity items

Positive polarity items are licensed under VERUM in a positive clause and negative ones in
a negative clause (70), (71), (75), (76); VERUM intervenes between negation and the clause
in the positive reading, so the clause is negated only in the negative reading and under
focused *NOT*. -/

/-- Whether the clause under VERUM is negated. -/
def Form.Negated : Form → Prop
  | .ni | .notFocus => True
  | .pi | .really => False

instance : DecidablePred Form.Negated := λ f => by
  cases f <;> unfold Form.Negated <;> infer_instance

/-- A polarity item is licensed in a form iff a positive item finds the clause unnegated and
a negative one finds it negated. -/
def Licensed (e : Polarity.Item) (f : Form) : Prop :=
  (e.isPPI → ¬ f.Negated) ∧ (e.isNPI → f.Negated)

instance (e : Polarity.Item) (f : Form) : Decidable (Licensed e f) := by
  unfold Licensed; infer_instance

/-! ### The paper's examples -/

/-- An example: its question form by the position of negation, its reported bias, its VERUM
form and its polarity item, each when the paper gives one, and its judgment. -/
structure Datum where
  pqForm : Option PQForm
  bias : Option SignType
  form : Option Form
  item : Option Polarity.Item
  judgment : Data.Examples.Judgment

/-- An example read into its datum. -/
def datum (e : LinguisticExample) : Datum where
  pqForm := e.parse? "negation"
    [("preposed", PQForm.hiNQ), ("nonPreposed", .loNQ), ("none", .posQ)]
  bias := e.parse? "bias" [("positive", (1 : SignType)), ("negative", -1), ("none", 0)]
  form := e.parse? "form" [("pi", Form.pi), ("ni", .ni), ("really", .really),
    ("notFocus", .notFocus)]
  item := e.parse? "item"
    [("too", English.PolarityItems.too), ("either", English.PolarityItems.either_npi)]
  judgment := e.judgment

/-- The paper's examples. -/
def data : List Datum := Examples.all.map datum

/-- Licensing predicts every *too* and *either* judgment on (6), (7) and (77) to (80). -/
theorem licensed_iff_acceptable :
    ∀ d ∈ data, ∀ e ∈ d.item.toList, ∀ f ∈ d.form.toList,
      (Licensed e f ↔ d.judgment = .acceptable) := by
  decide

/-- Preposed negation carries a positive bias in every language of the survey, (1), (5) and
(14) to (18), and non-preposed negation none. -/
theorem bias_of_pqForm :
    ∀ d ∈ data, ∀ pq ∈ d.pqForm.toList, ∀ b ∈ d.bias.toList,
      (pq = .hiNQ → b = 1) ∧ (pq = .loNQ → b = 0) := by
  decide

/-- The bias reported for a VERUM form is the belief the model implicates. -/
theorem bias_of_form :
    ∀ d ∈ data, ∀ f ∈ d.form.toList, ∀ b ∈ d.bias.toList, b = f.implicature := by
  decide

end RomeroHan2004
