module

public import Linglib.Logic.Natural.Strawson.Basic
public import Linglib.Semantics.Exhaustification.Excluder
public import Linglib.Semantics.Conditionals.Restrictor
public import Linglib.Data.Examples.VonFintel1999

/-!
# von Fintel (1999): NPI Licensing, Strawson Entailment, and Context Dependency

This file formalizes [von-fintel-1999]'s defense of the Fauconnier–Ladusaw theory of negative
polarity licensing. Four licensers that are not downward entailing, *only*, the adversative
attitudes, superlatives, and conditional antecedents, are downward entailing once the inference
is checked only where the conclusion's presupposition holds; that notion, the operators, and
their Strawson downward entailingness are the substrate of `Logic/Natural/Strawson/Basic.lean`,
and this file carries the paper's arguments around them, its licensing data being
`Examples.ex10`, `Examples.ex21`, `Examples.ex28a`, `Examples.ex28b`, `Examples.ex70a`, and
`Examples.ex75`.

*Want* and *glad* are upward entailing on the best-worlds semantics (`want`, `gladBetter`), so
neither licenses; the first semantics for *glad* makes it belief conjoined with *want*, which
validates [kadmon-landman-1993]'s inference from wanting and knowing to gladness, and the Honda
Civic scenario refutes that inference on the second (`not_gladBetter_of_want`). The parallel
set-comparison semantics for *sorry* is upward entailing and so not Strawson downward entailing,
which is why the paper keeps the best-worlds one. Focus *only* over a name is [rooth-1992]'s
propositional *only* over the alternatives the name generates. A conditional antecedent is
downward entailing under an idle ordering source but not under a genuine one, the match that is
dipped before it is struck; and the superlative's Strawson downward entailingness is lost once it
restricts a definite description (`not_isStrawsonDE_theSuperlativeExceeds`).

## TODO

* The shifted-context readings of §3.4 and the dynamic rescue of conditional antecedents in
  §4.3 need [von-fintel-2000]'s context-change operator, which is not in the substrate.

## References

* [von-fintel-1999]
* [kadmon-landman-1993]
* [rooth-1992]
* [kratzer-1986]
* [von-fintel-2000]
-/

@[expose] public section

namespace VonFintel1999

open NaturalLogic Presupposition Modality Conditional

variable {W ι : Type*}

/-! ### *Want* and *glad* -/

section Attitudes

variable (dox rel : W → Set W) (g : W → List (W → Prop)) (p : Set W)

/-- `X` is better than `Y` throughout: every `X`-world is strictly better than every `Y`-world
under the ordering source `A`. -/
def Better (A : List (W → Prop)) (X Y : Set W) : Prop := ∀ x ∈ X, ∀ y ∈ Y, x <[A] y

/-- *a wants p*: the best worlds of the relevant modal base under the desire ordering are
`p`-worlds, presupposing that the base contains both `p`-worlds and non-`p`-worlds.
`Desire.BestWorlds.Want` is the assertion with a finite ordering source. -/
def want : PartialProp W where
  presup w := (rel w ∩ p).Nonempty ∧ (rel w \ p).Nonempty
  assertion w := bestAmong (rel w) (g w) ⊆ p

/-- *Want* is upward entailing in its complement (§3.2). -/
theorem want_assertion_monotone : Monotone λ p => (want rel g p).assertion :=
  λ _ _ h _ hw => hw.trans h

/-- *Glad* on the set comparison: the belief worlds are strictly better than every relevant
non-`p` world. -/
def gladBetter : PartialProp W where
  presup w := dox w ⊆ p
  assertion w := Better (g w) (dox w) (rel w \ p)

/-- The set-comparison *glad* is still upward entailing in its complement (§3.3). -/
theorem gladBetter_monotone : Monotone λ p => (gladBetter dox rel g p).truthSet :=
  λ _ _ h _ hw => ⟨hw.1.trans h, λ a ha b hb => hw.2 a ha b ⟨hb.1, λ hp => hb.2 (h hp)⟩⟩

/-- On the best-worlds *glad*, *a wants p and knows p* entails *a is glad that p*,
[kadmon-landman-1993]'s inference. -/
theorem glad_of_want (w : W) (hb : dox w ⊆ p) (hw : (want rel g p).assertion w) :
    (glad dox (λ w => bestAmong (rel w) (g w)) p).holds w :=
  ⟨hb, hw⟩

/-- The Honda Civic scenario refutes that inference on the set-comparison *glad*: world `0` is
the actual one, where the Civic bought is a lemon, `1` is where a good Civic is bought, and `2`
where none is; the subject believes `0`, wants the good Civic, and is not glad that a Civic was
bought, since `0` is no better than `2`. -/
theorem not_gladBetter_of_want :
    ∃ (dox rel : Fin 3 → Set (Fin 3)) (g : Fin 3 → List (Fin 3 → Prop)) (p : Set (Fin 3))
      (w : Fin 3), dox w ⊆ p ∧ (want rel g p).assertion w ∧
        ¬ (gladBetter dox rel g p).assertion w :=
  ⟨λ _ => {0}, λ _ => Set.univ, λ _ => [(· = 1)], {0, 1}, 0, by simp, by
    simp only [want, Set.subset_def, mem_bestAmong, atLeastAsGoodAs_iff,
      List.forall_mem_singleton, Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff]
    decide, by
    simp only [gladBetter, Better, strictlyBetter_iff, atLeastAsGoodAs_iff,
      List.forall_mem_singleton, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_univ,
      Set.mem_insert_iff]
    decide⟩

/-- *Sorry* on the set comparison: every relevant non-`p` world is strictly better than every
belief world. -/
def regretBetter : PartialProp W where
  presup w := dox w ⊆ p
  assertion w := Better (g w) (rel w \ p) (dox w)

/-- The set-comparison *sorry* is upward entailing in its complement. -/
theorem regretBetter_monotone : Monotone λ p => (regretBetter dox rel g p).truthSet :=
  λ _ _ h _ hw => ⟨hw.1.trans h, λ b hb a ha => hw.2 b ⟨hb.1, λ hp => hb.2 (h hp)⟩ a ha⟩

/-- The set-comparison *sorry* is not Strawson downward entailing, so it would not license; the
paper keeps the best-worlds `regret`. World `2` is the preferred one; the subject believes `0`
and is sorry about `{0, 1}` but not about `{0}`, since `1` is no better than `0`. -/
theorem not_isStrawsonDE_regretBetter :
    ¬ IsStrawsonDE (regretBetter (λ _ : Fin 3 => {0}) (λ _ => Set.univ) (λ _ => [(· = 2)])) :=
  λ h => by
    have := @h {0} {0, 1} (Set.singleton_subset_iff.2 (Set.mem_insert 0 _)) 0
    simp only [regretBetter, Better, strictlyBetter_iff, atLeastAsGoodAs_iff,
      List.forall_mem_singleton, Set.subset_def, Set.mem_sdiff, Set.mem_univ, Set.mem_insert_iff,
      Set.mem_singleton_iff] at this
    revert this
    decide

end Attitudes

/-! ### Focus *only* and propositional *only* -/

section Only

open Exhaustification

/-- Focus *only* over a name is the exclusion over the alternatives the name generates
(`Exhaustification.excludes`, §3.4) when the prejacent entails no other alternative. -/
theorem only_assertion_eq_excludes (P : ι → Set W) (x : ι) (hP : ∀ y, P x ⊆ P y → y = x) :
    {w | (only x P).assertion w} = excludes (Set.range P) (P x) := by
  ext w
  simp only [only, Set.mem_ofPred_eq, mem_excludes]
  constructor
  · rintro h q ⟨y, rfl⟩ hw
    by_cases hyx : y = x
    · exact hyx ▸ subset_rfl
    · exact absurd hw (h y hyx)
  · intro h y hyx hw
    exact hyx (hP y (h (P y) ⟨y, rfl⟩ hw))

/-- Without that condition the two come apart: individuals generating one proposition are one
alternative, entailed by the prejacent, for the exclusion but several for `only`. -/
theorem only_assertion_ne_excludes :
    {w | (only true λ _ : Bool => (Set.univ : Set Unit)).assertion w} ≠
      excludes (Set.range λ _ : Bool => (Set.univ : Set Unit)) Set.univ := by
  intro h
  have h0 : () ∈ {w | (only true λ _ : Bool => (Set.univ : Set Unit)).assertion w} := by
    rw [h]
    exact λ q hq _ => by obtain ⟨y, rfl⟩ := hq; exact subset_rfl
  exact h0 false Bool.false_ne_true (Set.mem_univ ())

end Only

/-! ### Conditional antecedents under an ordering source -/

/-- With a genuine ordering source the antecedent position of Kratzer's conditional necessity is
not downward entailing (§4.1): the best *strike*-worlds are dry and the match lights, the best
*dip and strike*-worlds do not light. World `0` strikes a dry match, world `1` dips it first. -/
theorem not_antitone_conditionalNecessity :
    ¬ Antitone λ α : Fin 2 → Prop =>
      {w | Restrictor.conditionalNecessity (λ _ => []) (λ _ => [(· = 0)]) α (· = 0) w} :=
  λ h => by
    have := @h (· = 1) (λ _ => True) (λ _ _ => trivial) 0
    simp only [Restrictor.conditionalNecessity, necessity_iff_all, bestWorlds, mem_bestAmong,
      ModalBase.accessibleWorlds, ModalBase.restrict, propIntersection, atLeastAsGoodAs_iff,
      List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true,
      Set.mem_ofPred_eq] at this
    revert this
    decide

/-! ### The superlative inside a definite description -/

section Description

variable {D : Type*} [Preorder D] (μ : ι → D) (Q : ι → Set W) (d : D)

/-- *The μ-est Q exceeds d*: presupposes a superlative individual and predicates the degree of
every such individual. -/
def theSuperlativeExceeds : PartialProp W where
  presup w := ∃ a, (superlative μ Q a).holds w
  assertion w := ∀ a, (superlative μ Q a).holds w → d < μ a

/-- The definite-description use is not even Strawson-valid (§4.2): *the tallest girl in the
school is over four feet* does not Strawson-entail *the tallest girl in the class is over four
feet*, since the class's tallest girl need not be the school's. Individual `false` is five feet,
`true` three feet; the class is `{true}`. -/
theorem not_isStrawsonDE_theSuperlativeExceeds :
    ¬ IsStrawsonDE (theSuperlativeExceeds (W := Unit) (λ b : Bool => if b then 3 else 5) · 4) :=
  λ h => by
    have := @h (λ b => {_u | b = true}) (λ _ => Set.univ) (λ _ _ _ => trivial) ()
    simp only [theSuperlativeExceeds, superlative, PartialProp.holds, Set.mem_ofPred_eq,
      Set.mem_univ] at this
    revert this
    decide

end Description

end VonFintel1999
