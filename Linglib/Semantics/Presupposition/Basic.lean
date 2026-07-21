import Linglib.Semantics.Presupposition.Defs
import Mathlib.Order.Antisymmetrization

/-!
# Canonical operations on partial propositions

The canonical connectives, entailment relations, and combinators on
`PartialProp`. References: [heim-1983], [schlenker-2009], [von-fintel-1999],
[karttunen-1973], [peters-1979], [bochvar-1937].

## Main declarations

* Negations: internal `neg` (a hole), Bochvar's truth operator `truthOp`
  and external negation `negExt = neg ∘ truthOp` (plugs).
* Classical connectives `and`, `or`, `imp`, `xor` (simultaneously Weak
  Kleene: indet is absorbing).
* Filtering / Karttunen connectives `andFilter`, `impFilter`, `orFilter` —
  Peters' middle Kleene ([peters-1979], `eval_andFilter`/`eval_orFilter`) —
  with the scoped notation `/\'`, `->'`, `\/'`.
* `strawsonEntails`, `strongEntails` — entailment relations: the
  canonical [von-fintel-1999] form (presup-as-premise; not transitive,
  `strawsonEntails_not_trans`) and the stronger variant that additionally
  requires `q`'s presupposition to project from `p`'s satisfaction.
* Embedding combinators `disjFilterLeft`, `negFactive`.
* `presupOfReferent` — definite-description combinator (single source of
  truth for singular definite denotations).

The rival trivalent connective families (Strong Kleene, Belnap / flexible
accommodation, symmetric K&P, positive-antecedent) live in
`Semantics.Presupposition.Trivalent`; quantified projection lives in
`Semantics.Presupposition.Quantified`.

## Implementation notes

The choice of connective system (how gaps behave under ∧/∨) is orthogonal
to the representation type — see `Trivalent.GapPolicy`. Connectives are
paired with `eval_*` bridge theorems mapping each to the corresponding
`Trivalent` operator on the evaluation.
-/

namespace Semantics.Presupposition

namespace PartialProp

open Classical

variable {W : Type*}

/-! ### Classical connectives -/

/-- Classical (internal / choice) negation: a hole.
    Lets the presupposition through unchanged. -/
def neg (p : PartialProp W) : PartialProp W where
  presup := p.presup
  assertion := fun w => ¬p.assertion w

/-- Bochvar's truth operator `t`: a plug-as-affirmation ([bochvar-1937]).
    Always defined; maps presupposition failure to `False`.
    [karttunen-1973] §10 fn 18: `t(A)` has truth-table
    `T → T`, `F → F`, `# → F`. Composing classical negation with `t`
    yields external negation: `negExt p = neg (truthOp p)`. -/
def truthOp (p : PartialProp W) : PartialProp W where
  presup := fun _ => True
  assertion := fun w => p.presup w ∧ p.assertion w

/-- Bochvar external (exclusion) negation: a plug.
    Always defined; true when `p` is false or undefined, false only when
    `p` is true. Equals `neg (truthOp p)` per [karttunen-1973] §10
    fn 18: `⌜¬A⌝ ≡ ⌜~t(A)⌝`. -/
def negExt (p : PartialProp W) : PartialProp W := neg (truthOp p)

/-- Classical conjunction: both presuppositions must hold. This is also
    Weak Kleene conjunction ([kleene-1952]: indet is absorbing). -/
def and (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∧ q.presup w
  assertion := fun w => p.assertion w ∧ q.assertion w

/-- Classical disjunction: both presuppositions must hold. This is also
    Weak Kleene disjunction ([kleene-1952]: indet is absorbing) — see
    `eval_or`. -/
def or (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∧ q.presup w
  assertion := fun w => p.assertion w ∨ q.assertion w

/-- Classical implication: both presuppositions must hold. -/
def imp (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∧ q.presup w
  assertion := fun w => p.assertion w → q.assertion w

/-- Exclusive disjunction: both presuppositions must hold (no filtering).

    Under Strong Kleene, `Trivalent.xor` propagates undefinedness
    unconditionally (`xor_indet_iff`), so exclusive disjunction never
    filters presupposition failure from either disjunct.
    [wang-davidson-2026] -/
def xor (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∧ q.presup w
  assertion := fun w => (p.assertion w ∧ ¬q.assertion w) ∨ (¬p.assertion w ∧ q.assertion w)

/-! ### Filtering connectives (Karttunen) -/

/-- Filtering conjunction ([karttunen-1973], [peters-1979]): the first
    conjunct can satisfy the second's presupposition. -/
def andFilter (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∧ (p.assertion w → q.presup w)
  assertion := fun w => p.assertion w ∧ q.assertion w

/-- Filtering implication ([karttunen-1973], [peters-1979]): the
    antecedent can satisfy the consequent's presupposition. -/
def impFilter (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∧ (p.assertion w → q.presup w)
  assertion := fun w => p.assertion w → q.assertion w

/-- Filtering disjunction (asymmetric, [karttunen-1973]): the *negation*
    of the first disjunct can satisfy the second's presupposition —
    *Either there is no bathroom or the bathroom is upstairs* is defined
    because the second disjunct's bathroom presupposition is required
    only at worlds where the first disjunct is false.

    Generalizes `disjFilterLeft` to a presuppositional first disjunct
    (`orFilter_ofProp`). The symmetric K&P variant is
    `PartialProp.orKPSymmetric`; the positive-antecedent variant is
    `PartialProp.orPositive` (`Semantics.Presupposition.Trivalent`). -/
def orFilter (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∧ (¬p.assertion w → q.presup w)
  assertion := fun w => p.assertion w ∨ q.assertion w

-- Notation for filtering connectives
scoped infixl:65 " /\\' " => andFilter
scoped infixr:55 " ->' " => impFilter
scoped infixl:60 " \\/' " => orFilter

/-! ### Entailment relations -/

/-- Strawson entailment ([von-fintel-1999]): `p` entails `q` at every
    world where both presuppositions hold. The conclusion `q`'s
    presupposition is a *premise* added to the entailment, not something
    the entailment delivers. The same notion on bilateral-update
    denotations is `ElliottSudo2025.strawsonEntails`. -/
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

/-- Strong (Strawson-projecting) entailment: at every world where `p` is
    defined and true, `q` is *both* defined and true. Stronger than
    `strawsonEntails`: this variant also requires that `q`'s
    presupposition projects from `p`'s satisfaction (so it embeds a
    presupposition-projection burden the canonical von Fintel form
    exempts). -/
def strongEntails (p q : PartialProp W) : Prop :=
  ∀ w, p.presup w → p.assertion w → q.presup w ∧ q.assertion w

/-- Strawson equivalence: mutual Strawson entailment
    (`AntisymmRel` of `strawsonEntails`). -/
def strawsonEquiv (p q : PartialProp W) : Prop :=
  AntisymmRel strawsonEntails p q

/-! ### Negation theorems -/

/-- Negation preserves presupposition. -/
@[simp] theorem neg_presup (p : PartialProp W) : (neg p).presup = p.presup := rfl

/-- Double negation restores assertion (classical). -/
theorem neg_neg_assertion (p : PartialProp W) (w : W) :
    (neg (neg p)).assertion w ↔ p.assertion w := Classical.not_not

/-- Double negation identity. -/
@[simp] theorem neg_neg (p : PartialProp W) : neg (neg p) = p :=
  PartialProp.ext rfl (funext fun _ => propext Classical.not_not)

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

/-- External negation has the dual assertion to the truth operator at every
    world: `negExt = ¬truthOp` extensionally, by definition (negExt = neg ∘ truthOp
    and neg is `¬` on assertion). -/
theorem negExt_assertion (p : PartialProp W) (w : W) :
    (negExt p).assertion w ↔ ¬(truthOp p).assertion w := Iff.rfl

/-- Karttunen §10 fn 18 truth table for external negation, presup-failure case:
    when `p`'s presupposition fails, `negExt p` is true (the plug behavior). -/
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

/-- When A(p) = P(q), filtering implication has trivial presupposition. -/
theorem impFilter_trivializes_presup (p q : PartialProp W)
    (h : p.assertion = q.presup) :
    (impFilter p q).presup = p.presup :=
  impFilter_eliminates_presup p q (fun _ ha => h ▸ ha)

/-- The filtering presupposition of `impFilter` and `andFilter` are identical.
    This is the formal content of [karttunen-1973] §8: the filtering
    rules for *if A then B* and *A and B* coincide because both reduce to
    `p.presup ∧ (p.assertion → q.presup)`. -/
theorem impFilter_presup_eq_andFilter_presup (p q : PartialProp W) :
    (impFilter p q).presup = (andFilter p q).presup := rfl

/-! ### Evaluation theorems -/

/-- Negation evaluation. -/
theorem eval_neg (p : PartialProp W) (w : W) :
    (neg p).eval w = Trivalent.neg (p.eval w) := by
  simp only [eval, neg]
  by_cases hp : p.presup w
  · simp only [if_pos hp]
    by_cases ha : p.assertion w
    · simp [if_pos ha, if_neg (not_not.mpr ha), Trivalent.neg]
    · simp [if_neg ha, if_pos ha, Trivalent.neg]
  · simp [if_neg hp, Trivalent.neg]

/-- Classical conjunction evaluation (both defined). -/
theorem eval_and (p q : PartialProp W) (w : W)
    (hp : p.presup w) (hq : q.presup w) :
    (and p q).eval w = p.eval w ⊓ q.eval w := by
  have hpq : p.presup w ∧ q.presup w := ⟨hp, hq⟩
  simp only [eval, and, if_pos hp, if_pos hq, if_pos hpq]
  by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [ha, hb]

/-- `or` evaluates to `Trivalent.joinWeak` pointwise (classical disjunction
    is Weak Kleene). -/
theorem eval_or (p q : PartialProp W) (w : W) :
    (or p q).eval w = Trivalent.joinWeak (p.eval w) (q.eval w) := by
  simp only [eval, or, Trivalent.joinWeak]
  by_cases hp : p.presup w <;> by_cases hq : q.presup w <;> simp [hp, hq];
    by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [ha, hb]

/-- Filtering implication when antecedent false: result is true. -/
theorem eval_impFilter_antecedent_false (p q : PartialProp W) (w : W)
    (hp : p.presup w) (ha : ¬p.assertion w) :
    (impFilter p q).eval w = .true := by
  have hpresup : (impFilter p q).presup w := ⟨hp, fun h => absurd h ha⟩
  have hassert : (impFilter p q).assertion w := fun h => absurd h ha
  simp only [eval, if_pos hpresup, if_pos hassert]

/-- Filtering implication when antecedent true: depends on consequent. -/
theorem eval_impFilter_antecedent_true (p q : PartialProp W) (w : W)
    (hp : p.presup w) (ha : p.assertion w) (hq : q.presup w) :
    (impFilter p q).eval w =
      if q.assertion w then .true else .false := by
  have hpresup : (impFilter p q).presup w := ⟨hp, fun _ => hq⟩
  by_cases hqa : q.assertion w
  · have hass : (impFilter p q).assertion w := fun _ => hqa
    simp only [eval, if_pos hpresup, if_pos hass, if_pos hqa]
  · have hass : ¬(impFilter p q).assertion w := fun h => hqa (h ha)
    simp only [eval, if_pos hpresup, if_neg hass, if_neg hqa]

/-- **Karttunen filtering conjunction is Peters' middle Kleene**
    ([peters-1979]): `andFilter` evaluates to the asymmetric
    `Trivalent.meetMiddle` on both dimensions, unconditionally. -/
theorem eval_andFilter (p q : PartialProp W) (w : W) :
    (andFilter p q).eval w = Trivalent.meetMiddle (p.eval w) (q.eval w) := by
  by_cases hp : p.presup w <;> by_cases hq : q.presup w <;>
    by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [eval, andFilter, Trivalent.meetMiddle, hp, hq, ha, hb] <;> decide

/-- **Karttunen filtering disjunction is Peters' middle Kleene**
    ([peters-1979]): `orFilter` evaluates to the asymmetric
    `Trivalent.joinMiddle` on both dimensions, unconditionally. -/
theorem eval_orFilter (p q : PartialProp W) (w : W) :
    (orFilter p q).eval w = Trivalent.joinMiddle (p.eval w) (q.eval w) := by
  by_cases hp : p.presup w <;> by_cases hq : q.presup w <;>
    by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [eval, orFilter, Trivalent.joinMiddle, hp, hq, ha, hb] <;> decide

/-- Exclusive disjunction evaluation matches `Trivalent.xor` when both defined. -/
theorem eval_xor (p q : PartialProp W) (w : W)
    (hp : p.presup w) (hq : q.presup w) :
    (xor p q).eval w = Trivalent.xor (p.eval w) (q.eval w) := by
  have hpq : p.presup w ∧ q.presup w := ⟨hp, hq⟩
  simp only [eval, xor, if_pos hp, if_pos hq, if_pos hpq]
  by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [ha, hb, Trivalent.xor]

/-- Exclusive disjunction never filters: when either presupposition fails,
    the result is undefined. [wang-davidson-2026] -/
theorem eval_xor_no_filter (p q : PartialProp W) (w : W)
    (hq : ¬q.presup w) :
    (xor p q).eval w = .indet := by
  have : ¬(xor p q).presup w := fun ⟨_, hq'⟩ => hq hq'
  simp [eval, if_neg this]

/-! ### Embedding combinators ([heim-1992], [karttunen-1973], [delpinal-bassi-sauerland-2024]) -/

/-- Asymmetric filtering disjunction: plain proposition ∨ PartialProp.

    For "A ∨ B_ψ" where only B carries a presupposition ψ, the overall
    presupposition is ¬A → ψ (Karttunen's generalization for disjunction).
    The assertion is A ∨ B.

    This is the standard projection rule for presuppositions in the second
    disjunct of a disjunction. [karttunen-1973], [heim-1983] -/
def disjFilterLeft (firstDisjunct : W → Prop) (second : PartialProp W) :
    PartialProp W where
  assertion := fun w => firstDisjunct w ∨ second.assertion w
  presup := fun w => ¬firstDisjunct w → second.presup w

/-- `orFilter` with a presuppositionless first disjunct is `disjFilterLeft`. -/
theorem orFilter_ofProp (A : W → Prop) (q : PartialProp W) :
    orFilter (ofProp A) q = disjFilterLeft A q :=
  PartialProp.ext (funext fun _ => propext (and_iff_right trivial)) rfl

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

/-- When the first disjunct is false, `disjFilterLeft` recovers full
    satisfaction of the second disjunct. -/
theorem disjFilterLeft_recovers (firstDisjunct : W → Prop) (sp : PartialProp W)
    (w : W) (hFirst : ¬firstDisjunct w)
    (hFiltered : (disjFilterLeft firstDisjunct sp).holds w) :
    sp.holds w := by
  obtain ⟨hPresup, hAssert⟩ := hFiltered
  exact ⟨hPresup hFirst, hAssert.resolve_left hFirst⟩

/-- When `¬A` entails `q`'s presupposition pointwise, `disjFilterLeft A q`
    is presuppositionless (the filtering condition is satisfied at every
    world). The substrate-side fact behind [karttunen-1973]'s
    asymmetric disjunction filtering rule (24b), p. 181: "A or B" carries
    no residual presupposition from B when ¬A entails it. -/
theorem disjFilterLeft_eliminates_presup_when_neg_entails
    (A : W → Prop) (q : PartialProp W)
    (h : ∀ w, ¬A w → q.presup w) :
    (disjFilterLeft A q).presup = fun _ => True := by
  funext w
  simp only [disjFilterLeft, eq_iff_iff, iff_true]
  exact h w

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
scope of the referent. This is the single source of truth for all definite
denotations in the library: uniqueness-based (`russellIotaList domain R`),
familiarity-based (`russellIotaList dc.salient R`), anaphoric
(`russellIotaList domain (R ∧ Q)`), and Donnellan's attributive
(`attributiveContent domain R`) all instantiate the selector slot. -/
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

end Semantics.Presupposition
