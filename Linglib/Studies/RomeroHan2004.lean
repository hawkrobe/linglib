import Linglib.Data.Examples.RomeroHan2004
import Linglib.Discourse.CommonGround
import Linglib.Fragments.English.PolarityItems
import Linglib.Logic.Modal.Defs
import Linglib.Semantics.Questions.Hamblin
import Mathlib.Order.Interval.Set.Defs

/-!
# Romero & Han (2004): negative yes/no questions

[romero-han-2004] derive the epistemic bias of preposed-negation *yn*-questions from a single
assumption: preposing negation contributes the conversational epistemic operator VERUM
((9), (64)), `FOR-SURE-CG_x p` — at every world compatible with `x`'s knowledge, at every world
where `x`'s conversational goals are fulfilled, `p` is in the common ground ((43)). A
*yn*-question over VERUM partitions on certainty about adding `p` to the common ground rather
than on `p` ((46) vs (48)), a meta-conversational move licit only under a prior bias (the
Principle of Economy (50)); [ladd-1981]'s `p`/`¬p` ambiguity is the scope of negation relative
to VERUM — the PI reading `[Q [not [VERUM p]]]` ((73)) and the NI reading
`[Q [VERUM [not p]]]` ((68)) — disambiguated by positive and negative polarity items since
VERUM intervenes between negation and the IP only in the former. The polarity of the
implicature is fixed not by the partition, which PI- and *really*-questions share ((84), (85)),
but by the *pronounced cell* ((iii′)): pronouncing `FOR-SURE-CG q` asks for conclusive evidence
for `q`, so `¬q` is the speaker's belief; pronouncing `¬FOR-SURE-CG q` asks for doubts about
`q`, so `q` is. Hence PI-, NI-, and focused-*NOT* questions implicate `p` and
*really*-questions `¬p` ((81), (82), (110), (117)). Speaker belief is the epistemic
proposition `Set.Iic` of `Pragmatics/NeoGricean/Basic.lean`.

## Main definitions

* `verum`: FOR-SURE-CG over epistemic and conversational accessibility and a common-ground
  assignment.
* `Form`: the four VERUM *yn*-questions — PI, NI, *really*, focused *NOT* — with their
  `prejacent` under VERUM and pronounced `Cell`.
* `denotation`, `pronounced`, `speakerBelief`: the partition, the pronounced cell, and the
  epistemic implicature of each form.
* `Licensed`: a polarity item is licensed iff its requirement matches whether the IP under
  VERUM is negated.

## Main results

* `verum_eq_box_box`: VERUM is a necessity nested in a necessity.
* `denotation_eq`: every VERUM question denotes the unbalanced partition `polar (VERUM q)`;
  `polar_compl` is why non-preposed negation leaves the partition balanced ((22), (65)).
* `speakerBelief_pi`, `speakerBelief_ni`, `speakerBelief_really`, `speakerBelief_notFocus`:
  the implicature pattern, positive for the negative questions and negative for the positive
  one; `denotation_pi_eq_really` shows the partition alone cannot fix it.
* `licensed_iff_acceptable`: the *too*/*either* judgments on (6), (7), (77)–(80).

## References

* [romero-han-2004] — the VERUM analysis
* [ladd-1981] — the `p`/`¬p` ambiguity and its polarity-item diagnostic
* [hohle-1992] — VERUM as polarity focus, `Studies/Hohle1992.lean`
-/

namespace RomeroHan2004

open ModalLogic (box)
open Question (polar polar_compl)
open Set (Iic)

variable {W : Type*} (epi conv : W → W → Prop) (cg : W → CommonGround W) (p q : Set W)

/-! ### VERUM -/

/-- The VERUM operator `FOR-SURE-CG_x p` ((43)): `p` is in the common ground at every world
compatible with the conversational goals of every world compatible with `x`'s knowledge. -/
def verum : Set W :=
  {w | ∀ w', epi w w' → ∀ w'', conv w' w'' → p ∈ (cg w'').propositions}

/-- VERUM is a necessity nested in a necessity. -/
theorem verum_eq_box_box :
    verum epi conv cg p = box epi (box conv fun w => p ∈ (cg w).propositions) := rfl

/-! ### The four VERUM questions -/

/-- The *yn*-questions containing VERUM: the PI reading `[Q [not [VERUM p]]]` ((73)), the NI
reading `[Q [VERUM [not p]]]` ((68)), the *really*-question `[Q [VERUM p]]` ((111)), and
focused *NOT*, `[Q [NOT p]]` with `NOT = FOR-SURE-CG-NOT` ((54), (118)). -/
inductive Form where
  | pi
  | ni
  | really
  | notFocus
  deriving DecidableEq, Repr

/-- Which cell of the partition the question pronounces: the `FOR-SURE-CG q` cell, asking for
conclusive evidence for `q`, or its complement, asking for doubts about `q` ((98), (103)). -/
inductive Cell where
  | conclusive
  | doubt
  deriving DecidableEq, Repr

/-- The proposition under VERUM: `p` for PI and *really*, `¬p` for NI and focused *NOT*. -/
def prejacent : Form → Set W
  | .pi | .really => p
  | .ni | .notFocus => pᶜ

/-- The pronounced cell: only the PI reading, where negation scopes over VERUM, pronounces
the complement ((97), (102), (112), (119)). -/
def cell : Form → Cell
  | .pi => .doubt
  | .ni | .really | .notFocus => .conclusive

/-- The cell a form pronounces, as a proposition. -/
def pronounced (f : Form) : Set W :=
  match cell f with
  | .conclusive => verum epi conv cg (prejacent p f)
  | .doubt => (verum epi conv cg (prejacent p f))ᶜ

/-- The question denoted: the polar question over the pronounced cell. -/
def denotation (f : Form) : Question W := polar (pronounced epi conv cg p f)

/-- Every VERUM question denotes the unbalanced partition
`{FOR-SURE-CG q, ¬FOR-SURE-CG q}` ((48), (69), (74)). -/
theorem denotation_eq (f : Form) :
    denotation epi conv cg p f = polar (verum epi conv cg (prejacent p f)) := by
  cases f <;> simp [denotation, pronounced, cell]

/-- PI- and *really*-questions denote the same partition ((84), (85)). -/
theorem denotation_pi_eq_really :
    denotation epi conv cg p .pi = denotation epi conv cg p .really := by
  simp [denotation_eq, prejacent]

/-! ### The epistemic implicature

The intent of a question pronouncing `FOR-SURE-CG q` is to ask for conclusive evidence for
`q`, which the addressee can only have if `q` is the addressee's proposition and `¬q` the
speaker's belief; pronouncing `¬FOR-SURE-CG q` asks for doubts about `q`, so `q` is the
speaker's belief ((99), (104), (iii′)). -/

/-- The speaker's original belief implicated by a form: the epistemic proposition of states
settling the prejacent's negation (conclusive cell) or the prejacent (doubt cell). -/
def speakerBelief (f : Form) : Set (Set W) :=
  match cell f with
  | .conclusive => Iic (prejacent p f)ᶜ
  | .doubt => Iic (prejacent p f)

/-- The PI-question implicates `p` ((81)). -/
theorem speakerBelief_pi : speakerBelief p .pi = Iic p := rfl

/-- The NI-question, double-checking the addressee's `¬p`, also implicates `p` ((82)). -/
theorem speakerBelief_ni : speakerBelief p .ni = Iic p := by
  simp [speakerBelief, cell, prejacent]

/-- The *really*-question implicates `¬p` ((37), (110)). -/
theorem speakerBelief_really : speakerBelief p .really = Iic pᶜ := rfl

/-- The focused-*NOT* question implicates `p` ((117)). -/
theorem speakerBelief_notFocus : speakerBelief p .notFocus = Iic p := by
  simp [speakerBelief, cell, prejacent]

/-! ### Polarity items

PIs are licensed under VERUM in a positive IP and NIs in a negative one ((70), (71), (75),
(76)); VERUM intervenes between negation and the IP in the PI reading, so the IP is negated
only in the NI and focused-*NOT* forms. -/

/-- Whether the IP under VERUM is negated. -/
def IPNegated : Form → Prop
  | .ni | .notFocus => True
  | .pi | .really => False

instance : DecidablePred IPNegated
  | .ni | .notFocus => isTrue trivial
  | .pi | .really => isFalse id

/-- A polarity item is licensed in a form iff a positive polarity item finds the IP unnegated
and a negative one finds it negated. -/
def Licensed (e : Polarity.Item) (f : Form) : Prop :=
  (e.isPPI → ¬ IPNegated f) ∧ (e.isNPI → IPNegated f)

instance (e : Polarity.Item) (f : Form) : Decidable (Licensed e f) := by
  unfold Licensed; infer_instance

/-! ### The paper's judgments -/

/-- A licensing row: the polarity item, the form, and whether the paper judges it
acceptable. -/
def datum (e : Data.Examples.LinguisticExample) : Option (Polarity.Item × Form × Bool) := do
  let item ← match e.feature? "item" with
    | some "too" => some English.PolarityItems.too
    | some "either" => some English.PolarityItems.either_npi
    | _ => none
  let f ← match e.feature? "form" with
    | some "pi" => some Form.pi
    | some "ni" => some .ni
    | some "really" => some .really
    | some "notFocus" => some .notFocus
    | _ => none
  pure (item, f, e.judgment == .acceptable)

/-- The *too*/*either* judgments on (6), (7), and (77)–(80). -/
def data : List (Polarity.Item × Form × Bool) := Examples.all.filterMap datum

/-- Licensing predicts every *too*/*either* judgment. -/
theorem licensed_iff_acceptable : ∀ d ∈ data, Licensed d.1 d.2.1 ↔ d.2.2 = true := by
  decide

end RomeroHan2004
