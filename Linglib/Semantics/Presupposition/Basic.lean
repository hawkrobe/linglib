module

public import Linglib.Semantics.Presupposition.Defs
public import Mathlib.Order.Antisymmetrization

/-!
# Canonical operations on partial propositions

The canonical connectives, entailment relations, and combinators on `PartialProp`. Every
connective evaluates pointwise to an operation on `Trivalent`, stated as an unconditional
`eval_*` bridge: the classical connectives are Weak Kleene (an undefined operand absorbs),
Karttunen's filtering connectives are Peters' Middle Kleene (the left operand filters), and
Bochvar's truth operator is the meta-assertion operator. The rival families — Strong Kleene,
Belnap, and the symmetric two-dimensional disjunction, which evaluates to no trivalent
operation at all — live in `Presupposition.Trivalent`; quantified projection lives in
`Presupposition.Quantified`.

## Main declarations

* `neg`, `truthOp`, `negExt`: internal negation (a hole), Bochvar's truth operator and
  external negation `neg ∘ truthOp` (plugs).
* `and`, `or`, `imp`, `xor`: the classical connectives, Weak Kleene under `eval`.
* `andFilter`, `impFilter`, `orFilter`: the filtering connectives, Middle Kleene under
  `eval`, with the scoped notation `/\'`, `->'`, `\/'`.
* `strawsonEntails`, `strongEntails`: von Fintel's entailment with the conclusion's
  presupposition as a premise (not transitive, `strawsonEntails_not_trans`), and the stronger
  variant that also projects the conclusion's presupposition.
* `negFactive`, `presupOfReferent`: the negative-factive embedding combinator and the
  definite-description combinator shared by the singular definite denotations.

## References

* [heim-1983]
* [schlenker-2009]
* [von-fintel-1999]
* [karttunen-1973]
* [peters-1979]
* [bochvar-1937]
-/

@[expose] public section

namespace Presupposition

namespace PartialProp

open Classical

variable {W : Type*}

/-! ### Classical connectives -/

/-- Classical (internal, choice) negation is a hole, letting the presupposition through
    unchanged. -/
def neg (p : PartialProp W) : PartialProp W where
  presup := p.presup
  assertion := fun w => ¬p.assertion w

/-- Bochvar's truth operator `t` is always defined and maps presupposition failure to
    `False` — the plug-as-affirmation of [bochvar-1937], with the truth table of
    [karttunen-1973] §10 fn 18. Classical negation composed with it is external negation
    (`negExt`). -/
def truthOp (p : PartialProp W) : PartialProp W where
  presup := fun _ => True
  assertion := fun w => p.presup w ∧ p.assertion w

/-- Bochvar's external (exclusion) negation is a plug — always defined, true when `p` is
    false or undefined, false only when `p` is true. It is `neg (truthOp p)`, as in
    [karttunen-1973] §10 fn 18. -/
def negExt (p : PartialProp W) : PartialProp W := neg (truthOp p)

/-- Classical conjunction requires both presuppositions to hold; under `eval` it is Weak
    Kleene conjunction ([kleene-1952]), with an absorbing `indet`. -/
def and (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∧ q.presup w
  assertion := fun w => p.assertion w ∧ q.assertion w

/-- Classical disjunction requires both presuppositions to hold; under `eval` it is Weak
    Kleene disjunction ([kleene-1952]) — see `eval_or`. -/
def or (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∧ q.presup w
  assertion := fun w => p.assertion w ∨ q.assertion w

/-- Classical implication requires both presuppositions to hold; under `eval` it is the Weak
    Kleene material conditional (`eval_imp`). -/
def imp (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∧ q.presup w
  assertion := fun w => p.assertion w → q.assertion w

/-- Exclusive disjunction requires both presuppositions to hold, and never filters —
    `Trivalent.xor` propagates undefinedness unconditionally (`xor_indet_iff`), so
    presupposition failure in either disjunct projects ([wang-davidson-2026]). -/
def xor (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∧ q.presup w
  assertion := fun w => (p.assertion w ∧ ¬q.assertion w) ∨ (¬p.assertion w ∧ q.assertion w)

/-! ### Filtering connectives (Karttunen) -/

/-- The filtering conjunction of [karttunen-1973] lets the first conjunct satisfy the
    second's presupposition ([peters-1979]). -/
def andFilter (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∧ (p.assertion w → q.presup w)
  assertion := fun w => p.assertion w ∧ q.assertion w

/-- The filtering implication of [karttunen-1973] lets the antecedent satisfy the
    consequent's presupposition ([peters-1979]). -/
def impFilter (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∧ (p.assertion w → q.presup w)
  assertion := fun w => p.assertion w → q.assertion w

/-- The asymmetric filtering disjunction of [karttunen-1973] lets the *negation* of the
    first disjunct satisfy the second's presupposition — *Either there is no bathroom or
    the bathroom is upstairs* is defined because the second disjunct's bathroom
    presupposition is required only at worlds where the first disjunct is false. The
    symmetric K&P variant is `PartialProp.orKPSymmetric` (`Presupposition.Trivalent`). -/
def orFilter (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∧ (¬p.assertion w → q.presup w)
  assertion := fun w => p.assertion w ∨ q.assertion w

-- Notation for filtering connectives
scoped infixl:65 " /\\' " => andFilter
scoped infixr:55 " ->' " => impFilter
scoped infixl:60 " \\/' " => orFilter

/-! ### Entailment relations -/

/-- Strawson entailment ([von-fintel-1999]) requires `p`'s assertion to entail `q`'s at
    every world where both presuppositions hold; the conclusion's presupposition is a
    *premise* added to the entailment, not something the entailment delivers. -/
def strawsonEntails (p q : PartialProp W) : Prop :=
  ∀ w, p.presup w → q.presup w → p.assertion w → q.assertion w

/-- Strawson entailment is **not** transitive — an undefined middle term discharges both
    premises vacuously, the well-known failure of [von-fintel-1999]'s notion — so
    `strawsonEntails` supports no `Preorder` instance. -/
theorem strawsonEntails_not_trans :
    ¬ ∀ p q r : PartialProp Unit,
        strawsonEntails p q → strawsonEntails q r → strawsonEntails p r :=
  λ h =>
    (h top undefined bot (λ _ _ hq _ => hq.elim) (λ _ hq _ _ => hq.elim))
      () trivial trivial trivial

/-- Strong (Strawson-projecting) entailment requires that at every world where `p` is
    defined and true, `q` is *both* defined and true. It strengthens `strawsonEntails` by
    making `q`'s presupposition project from `p`'s satisfaction, a projection burden the
    canonical von Fintel form exempts. -/
def strongEntails (p q : PartialProp W) : Prop :=
  ∀ w, p.presup w → p.assertion w → q.presup w ∧ q.assertion w

/-- Strawson equivalence is mutual Strawson entailment, the `AntisymmRel` of
    `strawsonEntails`. -/
def strawsonEquiv (p q : PartialProp W) : Prop :=
  AntisymmRel strawsonEntails p q

/-! ### Negation theorems -/

/-- Negation preserves presupposition. -/
@[simp] theorem neg_presup (p : PartialProp W) : (neg p).presup = p.presup := rfl

/-- Double negation identity. -/
@[simp] theorem neg_neg (p : PartialProp W) : neg (neg p) = p :=
  PartialProp.ext rfl (funext fun _ => propext Classical.not_not)

@[simp] theorem top_presup (w : W) : (top : PartialProp W).presup w := trivial

@[simp] theorem top_assertion (w : W) : (top : PartialProp W).assertion w := trivial

@[simp] theorem and_presup (p q : PartialProp W) (w : W) :
    (p.and q).presup w ↔ p.presup w ∧ q.presup w := Iff.rfl

@[simp] theorem and_assertion (p q : PartialProp W) (w : W) :
    (p.and q).assertion w ↔ p.assertion w ∧ q.assertion w := Iff.rfl

/-- The truth operator is always defined (it's a plug). -/
@[simp] theorem truthOp_presup (p : PartialProp W) (w : W) :
    (truthOp p).presup w := trivial

/-- External negation is always defined (it's a plug). -/
@[simp] theorem negExt_presup (p : PartialProp W) (w : W) :
    (negExt p).presup w := trivial

/-- Internal and external negation agree on assertion when the presupposition
    holds. They diverge only at presupposition failure: `neg p` is undefined,
    `negExt p` is true. [karttunen-1973] §10 fn 18. -/
theorem neg_assertion_iff_negExt_assertion_when_defined (p : PartialProp W) (w : W)
    (h : p.presup w) :
    (neg p).assertion w ↔ (negExt p).assertion w := by
  simp only [neg, negExt, truthOp, h, true_and]

/-- External negation asserts the dual of the truth operator at every world, by definition,
    since `negExt` negates `truthOp`'s assertion. -/
theorem negExt_assertion (p : PartialProp W) (w : W) :
    (negExt p).assertion w ↔ ¬(truthOp p).assertion w := Iff.rfl

/-- When `p`'s presupposition fails, `negExt p` is true — the plug row of the
    [karttunen-1973] §10 fn 18 truth table. -/
theorem negExt_assertion_of_presup_failure (p : PartialProp W) (w : W)
    (h : ¬p.presup w) :
    (negExt p).assertion w := by
  simp only [negExt, neg, truthOp, h, false_and, not_false_eq_true]

/-! ### Filtering theorems -/

/-- Filtering implication eliminates presupposition when antecedent entails it. -/
theorem impFilter_eliminates_presup (p q : PartialProp W)
    (h : ∀ w, p.assertion w → q.presup w) :
    (impFilter p q).presup = p.presup := by
  funext w; simp only [impFilter]
  exact propext ⟨fun ⟨hp, _⟩ => hp, fun hp => ⟨hp, h w⟩⟩

/-- The filtering presuppositions of `impFilter` and `andFilter` are identical — the formal
    content of [karttunen-1973] §8, where the filtering rules for *if A then B* and
    *A and B* coincide because both reduce to `p.presup ∧ (p.assertion → q.presup)`. -/
theorem impFilter_presup_eq_andFilter_presup (p q : PartialProp W) :
    (impFilter p q).presup = (andFilter p q).presup := rfl

/-! ### Evaluation bridges

Each connective descends along `eval` to its trivalent face, unconditionally: the classical
connectives to Weak Kleene, the filtering connectives to Middle Kleene, the plugs to
meta-assertion. The symmetric two-dimensional disjunction admits no such bridge
(`orKPSymmetric_not_trivalent` in `Presupposition.Trivalent`). -/

/-- Internal negation evaluates to Strong Kleene negation pointwise. -/
theorem eval_neg (p : PartialProp W) (w : W) :
    (neg p).eval w = Trivalent.neg (p.eval w) := by
  by_cases hp : p.presup w <;> by_cases ha : p.assertion w <;>
    simp [eval, neg, Trivalent.neg, hp, ha]

/-- Bochvar's truth operator evaluates to meta-assertion pointwise — the plug is the 𝒜
    operator. -/
theorem eval_truthOp (p : PartialProp W) (w : W) :
    (truthOp p).eval w = Trivalent.metaAssert (p.eval w) := by
  by_cases hp : p.presup w <;> by_cases ha : p.assertion w <;>
    simp [eval, truthOp, hp, ha]

/-- External negation evaluates to negated meta-assertion pointwise. -/
theorem eval_negExt (p : PartialProp W) (w : W) :
    (negExt p).eval w = Trivalent.neg (Trivalent.metaAssert (p.eval w)) := by
  rw [negExt, eval_neg, eval_truthOp]

/-- Classical conjunction evaluates to Weak Kleene conjunction pointwise. -/
theorem eval_and (p q : PartialProp W) (w : W) :
    (and p q).eval w = Trivalent.meetWeak (p.eval w) (q.eval w) := by
  by_cases hp : p.presup w <;> by_cases hq : q.presup w <;>
    by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [eval, and, Trivalent.meetWeak, hp, hq, ha, hb]

/-- Classical disjunction evaluates to Weak Kleene disjunction pointwise. -/
theorem eval_or (p q : PartialProp W) (w : W) :
    (or p q).eval w = Trivalent.joinWeak (p.eval w) (q.eval w) := by
  by_cases hp : p.presup w <;> by_cases hq : q.presup w <;>
    by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [eval, or, Trivalent.joinWeak, hp, hq, ha, hb]

/-- Classical implication evaluates to the Weak Kleene material conditional pointwise. -/
theorem eval_imp (p q : PartialProp W) (w : W) :
    (imp p q).eval w = Trivalent.joinWeak (Trivalent.neg (p.eval w)) (q.eval w) := by
  by_cases hp : p.presup w <;> by_cases hq : q.presup w <;>
    by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [eval, imp, Trivalent.joinWeak, Trivalent.neg, hp, hq, ha, hb]

/-- **Karttunen filtering conjunction is Peters' middle Kleene.** `andFilter` evaluates to
    the asymmetric `Trivalent.meetMiddle` on both dimensions, unconditionally. -/
theorem eval_andFilter (p q : PartialProp W) (w : W) :
    (andFilter p q).eval w = Trivalent.meetMiddle (p.eval w) (q.eval w) := by
  by_cases hp : p.presup w <;> by_cases hq : q.presup w <;>
    by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [eval, andFilter, Trivalent.meetMiddle, hp, hq, ha, hb] <;> decide

/-- **Karttunen filtering disjunction is Peters' middle Kleene.** `orFilter` evaluates to
    the asymmetric `Trivalent.joinMiddle` on both dimensions, unconditionally. -/
theorem eval_orFilter (p q : PartialProp W) (w : W) :
    (orFilter p q).eval w = Trivalent.joinMiddle (p.eval w) (q.eval w) := by
  by_cases hp : p.presup w <;> by_cases hq : q.presup w <;>
    by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [eval, orFilter, Trivalent.joinMiddle, hp, hq, ha, hb] <;> decide

/-- **Karttunen filtering implication is Peters' middle Kleene.** `impFilter` evaluates to
    the Middle Kleene material conditional, unconditionally — the antecedent filters from
    the left exactly as in `andFilter` and `orFilter`. -/
theorem eval_impFilter (p q : PartialProp W) (w : W) :
    (impFilter p q).eval w = Trivalent.joinMiddle (Trivalent.neg (p.eval w)) (q.eval w) := by
  by_cases hp : p.presup w <;> by_cases hq : q.presup w <;>
    by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [eval, impFilter, Trivalent.joinMiddle, Trivalent.neg, hp, hq, ha, hb] <;> decide

/-- Exclusive disjunction evaluates to Strong Kleene exclusive disjunction pointwise. -/
theorem eval_xor (p q : PartialProp W) (w : W) :
    (xor p q).eval w = Trivalent.xor (p.eval w) (q.eval w) := by
  by_cases hp : p.presup w <;> by_cases hq : q.presup w <;>
    by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [eval, xor, Trivalent.xor, hp, hq, ha, hb]

/-- Exclusive disjunction never filters — when either presupposition fails, the result is
    undefined ([wang-davidson-2026]). -/
theorem eval_xor_no_filter (p q : PartialProp W) (w : W) (hq : ¬q.presup w) :
    (xor p q).eval w = .indet := by
  rw [eval_xor, (eval_eq_indet_iff q w).2 hq, Trivalent.xor_indet_right]

/-! ### Embedding combinators ([heim-1992], [delpinal-bassi-sauerland-2024]) -/

/-- Embedding under a negative factive (e.g., "is unaware that").

    "x is unaware that p" presupposes p and asserts ¬Bel_x(p).

    The choice of `complement.holds` (presupposition AND assertion) for the
    factive's presupposition is the [delpinal-bassi-sauerland-2024]
    treatment, where projection-through-factive requires both the trigger's
    presupposition and the at-issue complement to be carried. The
    [heim-1992] standard for atomic complements is `complement.assertion`
    alone; the two coincide when `complement` itself carries no presupposition
    but diverge when the complement contains its own embedded presupposition
    trigger (the case Del Pinal-Bassi-Sauerland use to handle presupposed
    free choice). -/
def negFactive (complement : PartialProp W)
    (believes : (W → Prop) → (W → Prop)) : PartialProp W where
  assertion := fun w => ¬(believes complement.assertion w)
  presup := fun w => complement.holds w

/-- Presupposition of `negFactive` is full satisfaction of the complement. -/
theorem negFactive_presup_eq (complement : PartialProp W)
    (believes : (W → Prop) → (W → Prop)) :
    (negFactive complement believes).presup = complement.holds := rfl

/-! ### Definite-description combinator -/

/-- The canonical definite-description combinator. Given:

- `referent : W → Option E` — a partial selector returning the referent at
  each world (or `none` when no unique referent is determined),
- `scope : E → W → Prop` — what is asserted of the chosen referent,

build the `PartialProp` that presupposes referent definedness and asserts the
scope of the referent. Every definite denotation in the library instantiates the selector
slot: the Russellian iota `Reference.iota` over a restrictor, over the restrictor
conjoined with identity to an antecedent, and Donnellan's attributive use pointwise. -/
def presupOfReferent {E : Type*} (referent : W → Option E)
    (scope : E → W → Prop) : PartialProp W where
  presup := fun w => (referent w).isSome
  assertion := fun w => match referent w with
    | some e => scope e w
    | none => False

/-- `presupOfReferent` is defined iff a referent is selected at `w`. -/
@[simp] theorem presupOfReferent_presup {E : Type*}
    (referent : W → Option E) (scope : E → W → Prop) (w : W) :
    (presupOfReferent referent scope).presup w = (referent w).isSome := rfl

/-- When a referent is selected, the assertion is the scope applied to it. -/
theorem presupOfReferent_assertion_some {E : Type*}
    (referent : W → Option E) (scope : E → W → Prop) (w : W) (e : E)
    (h : referent w = some e) :
    (presupOfReferent referent scope).assertion w = scope e w := by
  simp only [presupOfReferent, h]

/-- Without a referent, the assertion is `False`. -/
theorem presupOfReferent_assertion_none {E : Type*}
    (referent : W → Option E) (scope : E → W → Prop) (w : W)
    (h : referent w = none) :
    (presupOfReferent referent scope).assertion w = False := by
  simp only [presupOfReferent, h]

end PartialProp

end Presupposition
