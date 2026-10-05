module

public import Linglib.Logic.Natural.Strawson
public import Linglib.Semantics.Conditionals.Restrictor
public import Linglib.Data.Examples.VonFintel1999

/-!
# von Fintel (1999): NPI licensing, Strawson entailment, and context dependency

Von Fintel defends the Fauconnier–Ladusaw theory of negative polarity licensing against four
licensers that are not downward entailing, focus *only*, the adversative attitudes, superlatives
and conditional antecedents: each is downward entailing once the inference is checked only where
the presuppositions hold. The notion and the operators are in `Logic/Natural/Strawson.lean`, the
attitude entries in `Semantics/Attitudes/Desire/BestWorlds.lean`; this file carries the paper's
arguments around them, and its licensing judgments are the rows of
`Data/Examples/VonFintel1999.json`.

*Want* and *glad* are upward entailing in the Strawson sense, on the best-worlds semantics and on
the set comparison alike. On the best-worlds semantics wanting and believing `p` makes one glad
that `p`, which the Honda Civic scenario refutes for the set comparison. The set-comparison
*sorry* is not Strawson downward entailing, which is why the paper keeps the best-worlds one.
Of two entries for propositional *only*, the one that admits the prejacent's entailments as
alternatives is Strawson downward entailing and the one that bars them assesses no downward
inference at all; a conditional antecedent under a genuine ordering source is not downward
entailing; and a superlative inside a definite description is not even Strawson downward
entailing.

## Main results

* `isStrawsonUE_gladBetter`, `isStrawsonUE_regretBetter`: the set-comparison *glad* and *sorry*
  are Strawson upward entailing, like the best-worlds *want* and *glad*.
* `holds_glad_of_want`, `not_gladBetter_of_want`: wanting and believing gives gladness on the
  best-worlds semantics, not on the set comparison.
* `not_isStrawsonDE_regretBetter`: the set-comparison *sorry* would not license.
* `not_presup_only68b`: the rejected entry for propositional *only* can assess no downward
  inference within one set of alternatives.
* `not_antitone_conditionalNecessity`, `not_isStrawsonDE_theSuperlativeExceeds`: the conditional
  under an ordering source and the superlative description fail downward inference.

## TODO

* The shifted-context readings of §3.4 and the expansion of the modal horizon in §4.3 need
  [von-fintel-2000]'s context-change operator; the static horizon semantics of (81)–(83) is
  `NaturalLogic.would`.

## References

* [von-fintel-1999]
* [kadmon-landman-1993]
* [rooth-1992]
* [kratzer-1986]
* [von-fintel-2000]
-/

@[expose] public section

namespace VonFintel1999

open NaturalLogic Presupposition Modality Conditional Desire.BestWorlds

variable {W ι : Type*}

/-! ### *Want* and *glad* -/

section Attitudes

variable (dox rel : W → Set W) (g : W → List (W → Prop)) (p : Set W)

/-- `X` is better than `Y` when every `X`-world is strictly better than every `Y`-world under the
ordering source `A`. -/
def Better (A : List (W → Prop)) (X Y : Set W) : Prop := ∀ x ∈ X, ∀ y ∈ Y, x <[A] y

/-- The set-comparison *glad* (52) has the presupposition of the best-worlds one and asserts that
the belief worlds are strictly better than every relevant non-`p` world. -/
def gladBetter : PartialProp W where
  presup := (glad dox rel g p).presup
  assertion w := Better (g w) (dox w) (rel w \ p)

/-- The set-comparison *glad* is still Strawson upward entailing in its complement (§3.3). -/
theorem isStrawsonUE_gladBetter : IsStrawsonUE (gladBetter dox rel g) :=
  .of_monotone fun _ _ h _ hw a ha b hb ↦ hw a ha b ⟨hb.1, fun hp ↦ hb.2 (h hp)⟩

/-- On the best-worlds *glad*, *a wants p and believes p* entails *a is glad that p*, the
inference [kadmon-landman-1993] draw, when the modal base contains the belief worlds. -/
theorem holds_glad_of_want {w : W} (hd : dox w ⊆ rel w) (hb : dox w ⊆ p)
    (hw : (want rel g p).holds w) : (glad dox rel g p).holds w :=
  ⟨⟨hb, hd, hw.1⟩, hw.2⟩

/-- The Honda Civic scenario refutes that inference on the set-comparison *glad*. World `0` is
the actual one, where the Civic bought is a lemon, `1` is where a good Civic is bought, and `2`
where none is; the subject believes `0`, wants the good Civic, and is not glad that a Civic was
bought, since `0` is no better than `2`. -/
theorem not_gladBetter_of_want :
    ∃ (dox rel : Fin 3 → Set (Fin 3)) (g : Fin 3 → List (Fin 3 → Prop)) (p : Set (Fin 3))
      (w : Fin 3), dox w ⊆ p ∧ (want rel g p).assertion w ∧
        ¬ (gladBetter dox rel g p).assertion w :=
  ⟨fun _ ↦ {0}, fun _ ↦ Set.univ, fun _ ↦ [(· = 1)], {0, 1}, 0, by simp, by
    simp only [want, Want, Set.subset_def, mem_bestAmong, atLeastAsGoodAs_iff,
      List.forall_mem_singleton, Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff]
    decide, by
    simp only [gladBetter, Better, strictlyBetter_iff, atLeastAsGoodAs_iff,
      List.forall_mem_singleton, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_univ,
      Set.mem_insert_iff]
    decide⟩

/-- The set-comparison *sorry* (54) has the presupposition of *glad* and asserts that every
relevant non-`p` world is strictly better than every belief world. -/
def regretBetter : PartialProp W where
  presup := (glad dox rel g p).presup
  assertion w := Better (g w) (rel w \ p) (dox w)

/-- The set-comparison *sorry* is Strawson upward entailing in its complement. -/
theorem isStrawsonUE_regretBetter : IsStrawsonUE (regretBetter dox rel g) :=
  .of_monotone fun _ _ h _ hw b hb a ha ↦ hw b ⟨hb.1, fun hp ↦ hb.2 (h hp)⟩ a ha

/-- The set-comparison *sorry* is not Strawson downward entailing, so it would not license; the
paper keeps the best-worlds `regret`. World `2` is the preferred one; the subject believes `0`
and is sorry about `{0, 1}` but not about `{0}`, since `1` is no better than `0`. -/
theorem not_isStrawsonDE_regretBetter :
    ¬ IsStrawsonDE (regretBetter (fun _ : Fin 3 ↦ {0}) (fun _ ↦ Set.univ) (fun _ ↦ [(· = 2)])) :=
  fun h ↦ by
    have := h (p := {0}) (q := {0, 1}) (by simp) 0
      ⟨by simp, Set.subset_univ _, ⟨0, by simp⟩, ⟨2, by simp⟩⟩
      ⟨subset_rfl, Set.subset_univ _, ⟨0, by simp⟩, ⟨1, by simp⟩⟩
    simp only [regretBetter, Better, strictlyBetter_iff, atLeastAsGoodAs_iff,
      List.forall_mem_singleton, Set.mem_sdiff, Set.mem_univ, Set.mem_insert_iff,
      Set.mem_singleton_iff, true_and] at this
    revert this
    decide

end Attitudes

/-! ### Propositional *only*, §3.4

Of the two entries for propositional *only* von Fintel compares, (68a) presupposes the prejacent
and asserts that every true alternative is entailed by it; it is the substrate's
`Focus.Particles.only (· ⊆ ·)` (`Focus.Particles.only_subset_eq`), Strawson downward entailing
with the alternatives held fixed (`Focus.Particles.isStrawsonDE_only_subset`). (68b) bars the
prejacent's entailments from the alternatives and asserts that every true alternative is the
prejacent. -/

section Only

open Focus.Particles

variable (C : Set (Set W)) (p : Set W)

/-- *Only* in the entry (68b) presupposes the prejacent and that no alternative is entailed by
it, and asserts that every true alternative is the prejacent. -/
def only68b : PartialProp W :=
  ⟨fun w ↦ w ∈ p ∧ ¬ ∃ r ∈ C, p ⊆ r, (· ∈ atMost (· = ·) C p)⟩

/-- With (68b) no downward inference can be assessed within one set of alternatives, since when
the premise's prejacent is an alternative the conclusion's presupposition fails (p. 134). -/
theorem not_presup_only68b {q : Set W} (hp : p ∈ C) (hqp : q ⊆ p) (w : W) :
    ¬ (only68b C q).presup w :=
  fun h ↦ h.2 ⟨p, hp, hqp⟩

end Only

/-! ### Conditional antecedents under an ordering source -/

/-- With a genuine ordering source the antecedent position of Kratzer's conditional necessity is
not downward entailing (73). The best *strike*-worlds are dry and the match lights, while the best
*dip and strike*-worlds do not light; world `0` strikes a dry match, world `1` dips it first. -/
theorem not_antitone_conditionalNecessity :
    ¬ Antitone fun α : Fin 2 → Prop ↦
      {w | Restrictor.conditionalNecessity (fun _ ↦ []) (fun _ ↦ [(· = 0)]) α (· = 0) w} :=
  fun h ↦ by
    have := @h (· = 1) (fun _ ↦ True) (fun _ _ ↦ trivial) 0
    simp only [Restrictor.conditionalNecessity, necessity_iff, bestWorlds, mem_bestAmong,
      ModalBase.accessibleWorlds, ModalBase.restrict, propIntersection, atLeastAsGoodAs_iff,
      List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true,
      Set.mem_ofPred_eq] at this
    revert this
    decide

/-! ### The superlative inside a definite description -/

section Description

variable {D : Type*} [Preorder D] (μ : ι → D) (Q : ι → Set W) (d : D)

/-- *The μ-est Q exceeds d* presupposes a superlative individual and asserts that every such
individual exceeds `d`. -/
def theSuperlativeExceeds : PartialProp W where
  presup w := ∃ a, (superlative μ Q a).holds w
  assertion w := ∀ a, (superlative μ Q a).holds w → d < μ a

/-- The definite-description use is not even Strawson-valid (80). *The tallest girl in the
school is over four feet* does not Strawson-entail *the tallest girl in the class is over four
feet*, since the class's tallest girl need not be the school's; individual `false` is five feet,
`true` three feet, and the class is `{true}`. -/
theorem not_isStrawsonDE_theSuperlativeExceeds :
    ¬ IsStrawsonDE (theSuperlativeExceeds (W := Unit) (fun b : Bool ↦ if b then 3 else 5) · 4) :=
  fun h ↦ by
    have := @h (fun b ↦ {_u | b = true}) (fun _ ↦ Set.univ) (fun _ _ _ ↦ trivial) ()
    simp only [theSuperlativeExceeds, superlative, PartialProp.holds, Set.mem_ofPred_eq,
      Set.mem_univ] at this
    revert this
    decide

end Description

end VonFintel1999
