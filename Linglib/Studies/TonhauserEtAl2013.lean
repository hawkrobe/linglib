module

public import Linglib.Semantics.Presupposition.BeliefEmbedding
public import Linglib.Data.Examples.TonhauserEtAl2013

/-!
# Tonhauser, Beaver, Roberts and Simons (2013): Toward a Taxonomy of Projective Content

This file formalizes the two properties by which [tonhauser-beaver-roberts-simons-2013] sort
projective contents, contents that survive embedding under entailment-cancelling operators,
(1), and the argument that the resulting classes cross-cut the theories of projection. A
trigger imposes a strong contextual felicity constraint with respect to its content `m` when
it is acceptable only in `m`-positive contexts, (11), a context being `m`-positive when it
entails `m` and `m`-neutral when it entails neither `m` nor its negation, (10), so
acceptability in an `m`-neutral context refutes the constraint, (12i),
`not_scf_of_acceptable_neutral`. Under a belief predicate `m` has local effect when it is part
of the attitude holder's belief state, (38), and obligatory local effect when it always is,
(40), so acceptability with the holder explicitly ignorant of `m`, (41i), or believing its
negation, (41ii), refutes it, `not_ole_of_acceptable_ignorant` and
`not_ole_of_acceptable_negated`. The two properties yield the four classes of Table 1,
`ProjectiveClass`, and the diagnostics applied to English and Paraguayan Guaraní, Table 2,
populate all four: the existence implications of pronouns and *too* in class A, [potts-2005]'s
conventional implicatures with the descriptive contents of pronouns and demonstratives in
class B, the classical presuppositions of *know* and *stop* with the prejacent of *only* and
the polar implication of *almost* in class C, and the salience and indication implications of
*too*, focus and demonstratives in class D. Theories on which a presupposition is acceptable
iff its local context entails it, [karttunen-1974-presupposition], [heim-1983],
[van-der-sandt-1992] and [schlenker-2009], make every projective content impose the constraint
and have obligatory local effect, `scf_of_satisfaction` and `ole_of_satisfaction`, and so
place it in class A, while classes B, C and D are populated.

## Implementation notes

A context is a set of worlds and a content a proposition, the paper's own characterization,
and acceptability is a predicate on contexts that the diagnostics take as given. Local
satisfaction is the substrate's `Context.presupSatisfied` at the matrix and
`BeliefEmbedding.presupAttributedToHolder`, [schlenker-2009]'s local context under belief.
Projection, (21), and its family-of-sentences diagnostic, (24), which tests acceptability
across contexts for triggers with the constraint, after [matthewson-2004], and implication in
`m`-neutral contexts for the others, are recorded in the rows rather than defined, since they
quantify over sentence variants. The Guaraní consultants' judgments, and the objection that
two-dimensional theories after [karttunen-peters-1979] and [potts-2005] make projectivity
conventional where [simons-tonhauser-beaver-roberts-2010] find it context-dependent, are
reported in prose. The examples are the rows of `Data.Examples.TonhauserEtAl2013`.

## References

* [tonhauser-beaver-roberts-simons-2013]
* [karttunen-1974-presupposition]
* [heim-1983]
* [van-der-sandt-1992]
* [schlenker-2009]
* [potts-2005]
* [karttunen-peters-1979]
* [simons-tonhauser-beaver-roberts-2010]
* [matthewson-2004]
-/

@[expose] public section

namespace TonhauserEtAl2013

open Presupposition Presupposition.Context Presupposition.BeliefEmbedding

/-! ### The taxonomy (Table 1) -/

/-- The four classes of projective content, by whether the trigger imposes the strong
contextual felicity constraint and whether the content has obligatory local effect. -/
inductive ProjectiveClass where
  | classA
  | classB
  | classC
  | classD
  deriving DecidableEq, Repr

/-- Whether a class's triggers impose the strong contextual felicity constraint. -/
def ProjectiveClass.scf : ProjectiveClass → Bool
  | .classA | .classD => true
  | .classB | .classC => false

/-- Whether a class's contents have obligatory local effect. -/
def ProjectiveClass.ole : ProjectiveClass → Bool
  | .classA | .classC => true
  | .classB | .classD => false

/-- Table 1: the class of a content with the given properties. -/
def ProjectiveClass.ofProperties : Bool → Bool → ProjectiveClass
  | true, true => .classA
  | false, false => .classB
  | false, true => .classC
  | true, false => .classD

/-- The two properties determine the class, and every combination is a class. -/
def ProjectiveClass.equivProd : ProjectiveClass ≃ Bool × Bool where
  toFun c := (c.scf, c.ole)
  invFun p := ofProperties p.1 p.2
  left_inv c := by cases c <;> rfl
  right_inv p := by rcases p with ⟨_ | _, _ | _⟩ <;> rfl

/-! ### Strong contextual felicity (section 3) -/

variable {W E : Type*} (m c : Set W)

/-- (10): the context entails `m`. -/
def MPositive : Prop := c ⊆ m

/-- (10): the context entails neither `m` nor `¬m`. -/
def MNeutral : Prop := ¬ c ⊆ m ∧ ¬ c ⊆ mᶜ

/-- (11): uttering the trigger's sentence, acceptable in the contexts `Acc`, is acceptable
only in `m`-positive contexts. -/
def StrongContextualFelicity (Acc : Set W → Prop) : Prop := ∀ c, Acc c → MPositive m c

/-- (12i): acceptability in an `m`-neutral context refutes the constraint. -/
theorem not_scf_of_acceptable_neutral {Acc : Set W → Prop} (h : Acc c) (hn : MNeutral m c) :
    ¬ StrongContextualFelicity m Acc :=
  λ hs => hn.1 (hs c h)

/-! ### Obligatory local effect (section 5) -/

/-- (38): under `a believes S` at `w`, `m` has local effect when it is part of `a`'s belief
state. -/
def LocalEffect (Dox : E → W → W → Prop) (a : E) (w : W) : Prop := {v | Dox a w v} ⊆ m

/-- (40): wherever the belief report is acceptable, `m` has local effect. -/
def ObligatoryLocalEffect (Dox : E → W → W → Prop) (a : E) (Acc : Set W → Prop) : Prop :=
  ∀ c, Acc c → ∀ w ∈ c, LocalEffect m Dox a w

/-- (41i): acceptability of the report with the holder ignorant of `m` refutes obligatory
local effect. -/
theorem not_ole_of_acceptable_ignorant {Dox : E → W → W → Prop} {a : E} {Acc : Set W → Prop}
    (h : Acc c) {w : W} (hw : w ∈ c) (hig : MNeutral m (Dox a w)) :
    ¬ ObligatoryLocalEffect m Dox a Acc :=
  λ ho => hig.1 (ho c h w hw)

/-- (41ii): a consistent belief state cannot give both `m` and its negation local effect, so
acceptability of the report with `¬m` attributed to the holder refutes obligatory local
effect. -/
theorem not_ole_of_acceptable_negated {Dox : E → W → W → Prop} {a : E} {Acc : Set W → Prop}
    (h : Acc c) {w : W} (hw : w ∈ c) (hcons : ∃ v, Dox a w v)
    (hneg : LocalEffect mᶜ Dox a w) :
    ¬ ObligatoryLocalEffect m Dox a Acc :=
  λ ho => hcons.elim λ _ hv => hneg hv (ho c h w hw hv)

/-! ### Against local satisfaction (section 8) -/

variable (p : PartialProp W) (Dox : E → W → W → Prop) (a : E)

/-- A trigger acceptable exactly where its local context entails its presupposition imposes
the strong contextual felicity constraint. -/
theorem scf_of_satisfaction : StrongContextualFelicity p.presup (presupSatisfied · p) :=
  λ _ h => h

/-- Under belief, local satisfaction is satisfaction in the holder's belief state, so the
presupposition has obligatory local effect. -/
theorem ole_of_satisfaction :
    ObligatoryLocalEffect p.presup Dox a (presupAttributedToHolder ⟨·, Dox, a⟩ p) :=
  λ _ h w hw _ hx => h w hw ⟨hw, hx⟩

end TonhauserEtAl2013
