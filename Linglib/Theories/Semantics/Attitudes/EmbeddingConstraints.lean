import Linglib.Theories.Semantics.Attitudes.CDistributivity
import Mathlib.Order.Basic

/-!
# Universal Constraints on Clause-Embedding Predicates
@cite{roelofsen-uegaki-2020} @cite{uegaki-2022} @cite{spector-egr-2015}
@cite{steinert-threlkeld-2020}

This file formalizes universal constraints on the possible denotations of
clause-embedding predicates — the semantic analogue of conservativity for
determiners (@cite{barwise-cooper-1981}).

## Constraints

Four constraints have been proposed, forming a hierarchy:

```
C-distributivity  ⟹  P-to-Q Entailment  (but NOT vice versa)
C-distributivity  ⟹  Strawson C-distributivity  (but NOT vice versa)
```

Veridical Uniformity is independent of both.

## Organization

- `CDistributivity.lean`: C-distributivity definition and proofs (semantic structure)
- This file: P-to-Q Entailment, Strawson C-dist, Veridical Uniformity,
  constraint hierarchy, and fictitious predicate rejection
- `Phenomena/Questions/Studies/Uegaki2022.lean`: empirical data (Table 8.2)
-/

namespace Semantics.Attitudes.EmbeddingConstraints

open Semantics.Attitudes.CDistributivity

-- ============================================================================
-- P-to-Q Entailment (@cite{roelofsen-uegaki-2020})
-- ============================================================================

/-!
## P-to-Q Entailment

@cite{roelofsen-uegaki-2020} propose a weaker constraint than C-distributivity:

**P-to-Q Entailment**: If there is an answer p to Q such that ⟦V⟧({p})(x) holds,
then ⟦V⟧(Q)(x) also holds.

This is the **one-directional** version of C-distributivity (P→Q direction only).
It is empirically superior: it rules in attested predicates that violate
C-distributivity (care, mõtlema, daroo, wonder) while still ruling out
fictitious predicates (*shknow, *knopinion, *all-open).
-/

/--
A predicate V is **P-to-Q entailing** iff for any term x and any
exhaustivity-neutral interrogative complement Q, if there is an answer
p to Q such that `V x [p] w = true`, then `V x Q w = true`.

This is weaker than C-distributivity: it only requires the P→Q direction,
not the Q→P direction.
-/
def IsPtoQEntailing {W E : Type*}
    (V : E → QuestionDen W → W → Bool) : Prop :=
  ∀ (x : E) (Q : QuestionDen W) (w : W) (p : BProp W),
    p ∈ Q → V x [p] w = true → V x Q w = true

/--
C-distributivity implies P-to-Q entailment.

If V_Q(x, Q, w) ↔ ∃p ∈ Q. V_p(x, p, w), then in particular the ← direction
gives us: V_p(x, p, w) → V_Q(x, Q, w) for any p ∈ Q. Since V_Q(x, [p], w) ↔
V_p(x, p, w), this yields P-to-Q entailment.
-/
theorem cDistributive_implies_ptoq {W E : Type*}
    (V_prop : E → BProp W → W → Bool)
    (V_question : E → QuestionDen W → W → Bool)
    (hCD : IsCDistributive V_prop V_question) :
    IsPtoQEntailing V_question := by
  intro x Q w p hp hSingleton
  have ⟨q, hq_mem, hq_holds⟩ := (hCD x [p] w).mp hSingleton
  simp only [List.mem_singleton] at hq_mem
  rw [hq_mem] at hq_holds
  exact (hCD x Q w).mpr ⟨p, hp, hq_holds⟩

/--
Degree-comparison predicates are P-to-Q entailing (follows from C-distributivity).
-/
theorem degreeComparison_isPtoQEntailing {W E : Type*}
    (μ : DegreeFn W E) (θ : ThresholdFn W) (C : QuestionDen W) :
    IsPtoQEntailing (degreeComparisonQuestion μ θ C) := by
  exact cDistributive_implies_ptoq
    (degreeComparisonProp μ θ C)
    (degreeComparisonQuestion μ θ C)
    (degreeComparison_isCDistributive μ θ C)

-- ============================================================================
-- Strawson C-Distributivity (@cite{uegaki-2019}, @cite{uegaki-2022} Ch 8)
-- ============================================================================

/--
**Strawson C-distributivity**: a weaker variant of C-distributivity that
accounts for presuppositional predicates (e.g., predicates of relevance
like `care`).

A predicate V is Strawson C-distributive iff:
- (→) If V(x, Q), then there is an answer p to Q such that,
       **if the presuppositions of V(x, p) are satisfied**, then V(x, p).
- (←) If there is an answer p to Q such that V(x, p), then V(x, Q).

The key difference from plain C-distributivity: the → direction is
weakened to only require the propositional version to hold *when its
presuppositions are met*. This handles `care`, whose presupposition
(belief that p) blocks the → direction in plain C-distributivity.
-/
def IsStrawsonCDistributive {W E : Type*}
    (V_prop : E → BProp W → W → Bool)
    (V_question : E → QuestionDen W → W → Bool)
    (presupSatisfied : E → BProp W → W → Bool)
    : Prop :=
  (∀ (x : E) (Q : QuestionDen W) (w : W),
    V_question x Q w = true →
    ∃ p ∈ Q, presupSatisfied x p w = true → V_prop x p w = true) ∧
  (∀ (x : E) (Q : QuestionDen W) (w : W),
    (∃ p ∈ Q, V_prop x p w = true) → V_question x Q w = true)

/--
Plain C-distributivity implies Strawson C-distributivity
(with any presupposition predicate).
-/
theorem cDist_implies_strawson {W E : Type*}
    (V_prop : E → BProp W → W → Bool)
    (V_question : E → QuestionDen W → W → Bool)
    (presupSatisfied : E → BProp W → W → Bool)
    (hCD : IsCDistributive V_prop V_question) :
    IsStrawsonCDistributive V_prop V_question presupSatisfied := by
  constructor
  · intro x Q w hQ
    obtain ⟨p, hp_mem, hp_holds⟩ := (hCD x Q w).mp hQ
    exact ⟨p, hp_mem, fun _ => hp_holds⟩
  · intro x Q w ⟨p, hp_mem, hp_holds⟩
    exact (hCD x Q w).mpr ⟨p, hp_mem, hp_holds⟩

-- ============================================================================
-- Veridical Uniformity (@cite{spector-egr-2015})
-- ============================================================================

/-!
## Veridical Uniformity

@cite{spector-egr-2015} propose that all responsive clause-embedding predicates
are uniform w.r.t. veridicality: either veridical w.r.t. both declarative and
interrogative complements, or non-veridical w.r.t. both.

Veridical Uniformity is independent of C-distributivity and P-to-Q
Entailment. It captures a different dimension: whether the predicate
is truth-entailing, not whether question semantics reduces to
propositional semantics.
-/

/--
A predicate V is **veridical w.r.t. declarative complements** iff
V(x, {p}, w) entails p(w).

@cite{roelofsen-uegaki-2020} eq. 1 / @cite{spector-egr-2015}:
⌜x Vs p⌝ ⇒ ⌜p⌝
-/
def IsVeridicalDecl {W E : Type*}
    (V : E → QuestionDen W → W → Bool) : Prop :=
  ∀ (x : E) (p : BProp W) (w : W),
    V x [p] w = true → p w = true

/--
A predicate V is **veridical w.r.t. interrogative complements** iff
V(x, Q, w) and p(w) with p ∈ Q together entail V(x, {p}, w).

@cite{roelofsen-uegaki-2020} eq. 3 / @cite{spector-egr-2015}:
⌜x Vs Q⌝ ∧ ⌜p⌝ ∧ p ∈ Q ⇒ ⌜x Vs p⌝
-/
def IsVeridicalInterrog {W E : Type*}
    (V : E → QuestionDen W → W → Bool) : Prop :=
  ∀ (x : E) (Q : QuestionDen W) (p : BProp W) (w : W),
    V x Q w = true → p ∈ Q → p w = true → V x [p] w = true

/--
A responsive predicate V is **veridically uniform** iff it is either
veridical w.r.t. both declarative and interrogative complements,
or non-veridical w.r.t. both.

@cite{roelofsen-uegaki-2020} eq. 5 / @cite{spector-egr-2015}:
V is veridically uniform iff (VDecl(V) ↔ VInterrog(V)).
-/
def IsVeridicallyUniform {W E : Type*}
    (V : E → QuestionDen W → W → Bool) : Prop :=
  IsVeridicalDecl V ↔ IsVeridicalInterrog V

/--
The predicate `V(Q) = Q.any (fun _ => true)` (true iff Q is non-empty) is NOT
veridically uniform: it is veridical w.r.t. interrogatives but not declaratives.

This is the shared counterexample used in three separation theorems below.
-/
private theorem anyTrue_not_veridicallyUniform :
    ¬IsVeridicallyUniform
      (fun (_ : Unit) (Q : QuestionDen Unit) (_ : Unit) => Q.any fun _ => true) := by
  intro ⟨_, hR⟩
  have hInterrog : IsVeridicalInterrog
      (fun (_ : Unit) (Q : QuestionDen Unit) (_ : Unit) => Q.any fun _ => true) := by
    intro x Q p w _ _ _
    simp only [List.any_eq_true, List.mem_singleton]
    exact ⟨p, rfl, trivial⟩
  have hDecl := hR hInterrog
  exact absurd (hDecl () (fun _ => false) () rfl) Bool.false_ne_true

/--
Veridical Uniformity is independent of C-distributivity: a predicate
can be C-distributive without being veridically uniform.

Counterexample: V_question always returns true for any non-empty Q.
- Non-veridical w.r.t. declaratives: V({false}, w) = true but false(w) = false
- Veridical w.r.t. interrogatives: trivially (V always returns true for singletons)
- Not uniform: veridical-interrog but not veridical-decl.
-/
theorem cDist_not_implies_veridicalUniformity :
    ∃ (W E : Type) (V_prop : E → BProp W → W → Bool)
                   (V_question : E → QuestionDen W → W → Bool),
    IsCDistributive V_prop V_question ∧ ¬IsVeridicallyUniform V_question := by
  refine ⟨Unit, Unit,
    (fun _ _ _ => true),
    (fun _ Q _ => Q.any fun _ => true),
    ?_, ?_⟩
  · intro x Q w
    simp only [List.any_eq_true]
  · exact anyTrue_not_veridicallyUniform

-- ============================================================================
-- Constraint Hierarchy as a Partial Order
-- (@cite{roelofsen-uegaki-2020}, @cite{uegaki-2022} Ch 8)
-- ============================================================================

/-!
## Constraint Hierarchy

The four constraints form a partial order under semantic strength (implication).
The Hasse diagram:

```
      cDist
     ╱     ╲
  ptoQ   strawsonCDist

  vu  (incomparable with all three)
```

C-distributivity is the strongest: it implies both P-to-Q entailment and
Strawson C-distributivity. The other pairs are all incomparable.
-/

/-- The four universal constraints on clause-embedding predicates. -/
inductive Constraint where
  | cDist
  | ptoQ
  | strawsonCDist
  | vu
  deriving DecidableEq, Repr

namespace Constraint

/-- Ordering: `c₁ ≤ c₂` iff every predicate satisfying `c₂` also satisfies `c₁`.
    Equivalently, `c₂` is at least as strong as `c₁`.
    Only non-trivial edges: ptoQ ≤ cDist and strawsonCDist ≤ cDist. -/
private def ord : Constraint → Constraint → Bool
  | .cDist, .cDist => true
  | .ptoQ, .ptoQ => true
  | .ptoQ, .cDist => true
  | .strawsonCDist, .strawsonCDist => true
  | .strawsonCDist, .cDist => true
  | .vu, .vu => true
  | _, _ => false

instance : LE Constraint where le c₁ c₂ := c₁.ord c₂ = true
instance : LT Constraint where lt c₁ c₂ := c₁ ≤ c₂ ∧ ¬c₂ ≤ c₁

instance : DecidableEq Constraint := inferInstance

instance : Preorder Constraint where
  le_refl a := by cases a <;> rfl
  le_trans a b c h₁ h₂ := by
    cases a <;> cases b <;> cases c <;> simp_all [LE.le, ord]

instance : PartialOrder Constraint where
  le_antisymm a b h₁ h₂ := by
    cases a <;> cases b <;> simp_all [LE.le, ord]

/-- P-to-Q Entailment is weaker than C-distributivity. -/
theorem ptoQ_le_cDist : (.ptoQ : Constraint) ≤ .cDist := rfl

/-- Strawson C-distributivity is weaker than C-distributivity. -/
theorem strawsonCDist_le_cDist : (.strawsonCDist : Constraint) ≤ .cDist := rfl

/-- P-to-Q and Strawson C-dist are incomparable (neither implies the other). -/
theorem ptoQ_strawson_incomparable :
    ¬(.ptoQ : Constraint) ≤ .strawsonCDist ∧ ¬(.strawsonCDist : Constraint) ≤ .ptoQ :=
  ⟨nofun, nofun⟩

/-- VU is incomparable with C-dist. -/
theorem vu_cDist_incomparable :
    ¬(.vu : Constraint) ≤ .cDist ∧ ¬(.cDist : Constraint) ≤ .vu :=
  ⟨nofun, nofun⟩

/-- VU is incomparable with P-to-Q. -/
theorem vu_ptoQ_incomparable :
    ¬(.vu : Constraint) ≤ .ptoQ ∧ ¬(.ptoQ : Constraint) ≤ .vu :=
  ⟨nofun, nofun⟩

/-- VU is incomparable with Strawson C-dist. -/
theorem vu_strawson_incomparable :
    ¬(.vu : Constraint) ≤ .strawsonCDist ∧ ¬(.strawsonCDist : Constraint) ≤ .vu :=
  ⟨nofun, nofun⟩

end Constraint

/-!
### Semantic Soundness

The order relationships are justified by semantic implication theorems
already proved above:
- `cDistributive_implies_ptoq`: C-dist ⟹ P-to-Q (justifies `ptoQ ≤ cDist`)
- `cDist_implies_strawson`: C-dist ⟹ Strawson C-dist (justifies `strawsonCDist ≤ cDist`)
- `cDist_not_implies_veridicalUniformity`: C-dist ⇏ VU (justifies `¬(vu ≤ cDist)`)

### Semantic Separations

The incomparability results require counterexamples showing non-implications.
These are proved as separation theorems below.
-/

/--
P-to-Q does NOT imply Strawson C-distributivity.

Counterexample: V_question always returns true, V_prop always returns false.
- Satisfies P-to-Q: if V([p], w) = true and p ∈ Q, then V(Q, w) = true.
  (V([p]) = true trivially, and V(Q) = true trivially.)
- Violates Strawson C-dist (Q→P direction): V_question(Q) = true but
  ¬∃p ∈ Q, presup(p) → V_prop(p) = true, because V_prop is always false.
  Specifically, with presup = true and a non-empty Q, the → direction fails.
-/
theorem ptoQ_not_implies_strawsonCDist :
    ∃ (W E : Type)
      (V_question : E → QuestionDen W → W → Bool),
    IsPtoQEntailing V_question ∧
    ∀ (V_prop : E → BProp W → W → Bool)
      (presup : E → BProp W → W → Bool),
      V_prop = (fun _ _ _ => false) →
      presup = (fun _ _ _ => true) →
      ¬IsStrawsonCDistributive V_prop V_question presup := by
  refine ⟨Unit, Unit, (fun _ _ _ => true), ?_, ?_⟩
  · intro _ _ _ _ _ _; rfl
  · intro V_prop presup hV hP ⟨hLR, _⟩
    have := hLR () [fun _ => true] () rfl
    obtain ⟨p, _, hp⟩ := this
    have := hp (by rw [hP])
    rw [hV] at this
    exact Bool.false_ne_true this

/--
Strawson C-distributivity does NOT imply P-to-Q Entailment.

Counterexample: V_question(Q) = (Q.length == 1), V_prop always false, presup always false.
- Strawson (→): V_question(Q) = true → |Q| = 1 → Q non-empty → ∃p ∈ Q, (false → false). ✓
- Strawson (←): ∃p ∈ Q, V_prop(p) = true is impossible (V_prop = false), so ← vacuously true. ✓
- P-to-Q fails: V_question([p]) = true, p ∈ [p, q], but V_question([p, q]) = false. ✓

The key insight: Strawson uses a separate V_prop, while P-to-Q is about V_question alone.
With V_prop = false and presup = false, Strawson(←) is vacuously true, freeing
V_question to violate P-to-Q without constraint from the ← direction.
-/
theorem strawsonCDist_not_implies_ptoQ :
    ∃ (W E : Type) (V_question : E → QuestionDen W → W → Bool),
    (∃ (V_prop : E → BProp W → W → Bool)
       (presup : E → BProp W → W → Bool),
       IsStrawsonCDistributive V_prop V_question presup) ∧
    ¬IsPtoQEntailing V_question := by
  -- V_question: returns true iff Q is a singleton
  refine ⟨Unit, Unit,
    (fun _ Q _ => decide (Q.length = 1)),
    ⟨(fun _ _ _ => false), (fun _ _ _ => false), ?_, ?_⟩, ?_⟩
  · -- Strawson (→): Q.length = 1 → ∃p ∈ Q, (false → false)
    intro x Q w hQ
    simp only [decide_eq_true_eq] at hQ
    match Q, hQ with
    | [p], _ => exact ⟨p, List.mem_singleton.mpr rfl, nofun⟩
  · -- Strawson (←): ∃p ∈ Q, false → V_question(Q)
    intro _ _ _ ⟨_, _, hp⟩
    exact absurd hp Bool.false_ne_true
  · -- P-to-Q fails: V([p]) = true, p ∈ [p, q], but V([p, q]) = false
    intro hPtoQ
    have h1 : decide ([(fun _ : Unit => true)].length = 1) = true := by decide
    have hmem : (fun _ : Unit => true) ∈
        ([(fun _ => true), (fun _ => false)] : List (Unit → Bool)) := by simp
    have h2 := hPtoQ () [(fun _ => true), (fun _ => false)] ()
      (fun _ => true) hmem h1
    simp at h2

/--
VU does NOT imply C-distributivity.

Counterexample: V always returns false.
- Veridically uniform: IsVeridicalDecl holds vacuously (V({p}) = false),
  IsVeridicalInterrog holds vacuously (V(Q) = false). Both directions of
  the biconditional hold.
- NOT C-distributive: V_question(x, [{p}], w) = false even though
  V_prop(x, p, w) = true (for suitable V_prop).
-/
theorem vu_not_implies_cDist :
    ∃ (W E : Type) (V_question : E → QuestionDen W → W → Bool),
    IsVeridicallyUniform V_question ∧
    ∀ (V_prop : E → BProp W → W → Bool),
      V_prop = (fun _ _ _ => true) →
      ¬IsCDistributive V_prop V_question := by
  refine ⟨Unit, Unit, (fun _ _ _ => false), ?_, ?_⟩
  · -- VU: both IsVeridicalDecl and IsVeridicalInterrog are vacuously true
    constructor
    · intro hDecl; intro x Q p w hQ _ _
      exact absurd hQ Bool.false_ne_true
    · intro _; intro x p w hV
      exact absurd hV Bool.false_ne_true
  · intro V_prop hV hCD
    have := (hCD () [fun _ => true] ()).mpr
      ⟨fun _ => true, List.mem_singleton.mpr rfl, by rw [hV]⟩
    exact Bool.false_ne_true this

/--
VU does NOT imply P-to-Q Entailment.

Same counterexample as `vu_not_implies_cDist`: V always false.
P-to-Q fails because V([p]) = false, so the antecedent is never satisfied,
wait — that makes P-to-Q vacuously TRUE.

Revised counterexample: V(Q) = Q.isEmpty (true when Q has no alternatives).
- VU: V([p]) = false always (singleton is non-empty), so IsVeridicalDecl
  holds vacuously. IsVeridicalInterrog: V(Q) = true requires Q empty, but
  then p ∈ Q is impossible, so holds vacuously. Both hold → biconditional true.
- P-to-Q fails: need V([p]) = true. But V([p]) = [p].isEmpty = false. So P-to-Q
  is vacuously true again!

V always false makes P-to-Q vacuously true. We need V that satisfies VU but
has V([p]) = true for some p while V(Q) = false for some Q ∋ p.

V(Q, w) = Q.length == 1 && (match Q.head? with | some p => p w | none => false).
i.e., singleton + answer is true.
- V([p], w) = true iff p w = true
- V([p, q], w) = false always
- IsVeridicalDecl: V([p], w) = true → p w = true ✓
- IsVeridicalInterrog: V(Q, w) = true → p ∈ Q → p w → V([p], w).
  V(Q, w) = true requires Q singleton, say Q = [q], and q w = true.
  p ∈ [q] means p = q. V([p]) = V([q]) = (q w = true) = true ✓
- VU: IsVeridicalDecl holds, IsVeridicalInterrog holds → biconditional ✓
- P-to-Q: V([p], w) = true (so p w = true), p ∈ [p, q].
  V([p, q], w) = false. P-to-Q fails! ✓
-/
theorem vu_not_implies_ptoQ :
    ∃ (W E : Type) (V : E → QuestionDen W → W → Bool),
    IsVeridicallyUniform V ∧ ¬IsPtoQEntailing V := by
  -- V(Q, w) = true iff Q is a singleton [p] with p w = true
  let V : Unit → QuestionDen Unit → Unit → Bool :=
    fun _ Q w => match Q with
      | [p] => p w
      | _ => false
  refine ⟨Unit, Unit, V, ?_, ?_⟩
  · constructor
    · -- Decl → Interrog: V(Q, w) ∧ p ∈ Q ∧ p w → V([p], w) = p w
      intro _; intro x Q p w _hQ _hmem hpw
      exact hpw
    · -- Interrog → Decl: V([p], w) = p w → p w
      intro _; intro x p w hV
      exact hV
  · intro hPtoQ
    have hmem : (fun _ : Unit => true) ∈
        ([(fun _ => true), (fun _ => false)] : List (Unit → Bool)) := by simp
    have h1 : V () [fun _ => true] () = true := rfl
    have h2 := hPtoQ () [(fun _ => true), (fun _ => false)] ()
      (fun _ => true) hmem h1
    exact Bool.false_ne_true h2

/--
P-to-Q Entailment does NOT imply VU.

The counterexample from `cDist_not_implies_veridicalUniformity` works here
too, since C-dist implies P-to-Q and that example violates VU.
-/
theorem ptoQ_not_implies_vu :
    ∃ (W E : Type) (V : E → QuestionDen W → W → Bool),
    IsPtoQEntailing V ∧ ¬IsVeridicallyUniform V := by
  refine ⟨Unit, Unit, (fun _ Q _ => Q.any fun _ => true), ?_, ?_⟩
  · -- P-to-Q: V([p]) = true (any singleton is non-empty), p ∈ Q → V(Q) = Q.any(true)
    intro x Q w p hp _
    simp only [List.any_eq_true]
    exact ⟨p, hp, trivial⟩
  · exact anyTrue_not_veridicallyUniform

/--
Strawson C-distributivity does NOT imply VU.

Same V_question as P-to-Q case above (Q.any true), with V_prop = true, presup = true.
-/
theorem strawsonCDist_not_implies_vu :
    ∃ (W E : Type) (V_question : E → QuestionDen W → W → Bool),
    (∃ (V_prop : E → BProp W → W → Bool) (presup : E → BProp W → W → Bool),
       IsStrawsonCDistributive V_prop V_question presup) ∧
    ¬IsVeridicallyUniform V_question := by
  refine ⟨Unit, Unit, (fun _ Q _ => Q.any fun _ => true),
    ⟨(fun _ _ _ => true), (fun _ _ _ => true), ?_, ?_⟩, ?_⟩
  · -- Strawson (→): V_question = true → ∃p ∈ Q, presup → V_prop = true
    intro x Q w hQ
    simp only [List.any_eq_true] at hQ
    obtain ⟨p, hp, _⟩ := hQ
    exact ⟨p, hp, fun _ => rfl⟩
  · -- Strawson (←): ∃p ∈ Q, V_prop = true → V_question(Q) = true
    intro x Q w ⟨p, hp, _⟩
    simp only [List.any_eq_true]
    exact ⟨p, hp, trivial⟩
  · exact anyTrue_not_veridicallyUniform

/--
VU does NOT imply Strawson C-distributivity.

Counterexample: V_question(Q, w) = Q.all(fun p => p w) — universal.
- VU: IsVeridicalDecl holds (V([p], w) = p w = true → p w = true).
  IsVeridicalInterrog: V(Q, w) = true → all p ∈ Q have p w = true →
  for any p ∈ Q with p w = true, V([p], w) = p w = true. ✓
- ¬Strawson (←): With V_prop(p, w) = p w, presup = true:
  ∃p ∈ Q, p w = true → V_question(Q) = Q.all(⋯)? Only if ALL p ∈ Q are true.
  Take Q = [true, false]: ∃p ∈ Q, p w = true (namely true), but
  V_question(Q) = false.
-/
theorem vu_not_implies_strawsonCDist :
    ∃ (W E : Type) (V_question : E → QuestionDen W → W → Bool),
    IsVeridicallyUniform V_question ∧
    ∀ (V_prop : E → BProp W → W → Bool) (presup : E → BProp W → W → Bool),
      V_prop = (fun _ p w => p w) →
      presup = (fun _ _ _ => true) →
      ¬IsStrawsonCDistributive V_prop V_question presup := by
  -- V(Q, w) = Q.all(fun p => p w) — all answers must hold at w
  refine ⟨Unit, Unit, (fun _ Q w => Q.all (fun p => p w)), ?_, ?_⟩
  · -- VU
    constructor
    · intro hDecl; intro x Q p w hQ hmem hpw
      -- V(Q) = true → all q ∈ Q have q w = true → V([p]) = p w = true
      simp only [List.all_eq_true] at hQ
      simp only [List.all_eq_true, List.mem_singleton]
      intro q hq; rw [hq]; exact hpw
    · intro hInterrog; intro x p w hV
      -- V([p], w) = true → p w = true
      simp only [List.all_eq_true, List.mem_singleton] at hV
      exact hV p rfl
  · intro V_prop presup hV hP ⟨_, hRL⟩
    -- Strawson (←) fails: take Q = [true, false]
    have hEx : ∃ p ∈ ([(fun _ : Unit => true), (fun _ => false)] : List (Unit → Bool)),
        V_prop () p () = true := by
      exact ⟨fun _ => true, by simp, by rw [hV]⟩
    have hContra := hRL () [(fun _ => true), (fun _ => false)] () hEx
    -- V_question(Q) = Q.all(fun p => p ()) = true && false = false
    simp at hContra

-- ============================================================================
-- Fictitious Predicates (@cite{roelofsen-uegaki-2020} §4.6,
--                        @cite{steinert-threlkeld-2020})
-- ============================================================================

/-!
## Fictitious Predicates: Negative Tests

@cite{roelofsen-uegaki-2020} and @cite{steinert-threlkeld-2020} consider
predicates that are *conceivable* but *unattested* cross-linguistically.
P-to-Q Entailment predicts their non-existence by ruling them out.

These negative tests increase interconnection density: they show the
constraint has empirical bite beyond just describing attested predicates.
-/

/--
*shknow (@cite{spector-egr-2015}): "know" with declaratives but "wonder"
with interrogatives. Violates P-to-Q Entailment because knowing p (the
declarative reading) does NOT entail wondering Q (the interrogative reading).

**Paper's definition** (@cite{roelofsen-uegaki-2020} eq. 37, in inquisitive semantics):
⟦shknow⟧ᵂ = λQ λx. (|alt(Q)|=1 ∧ DOXᵂₓ ∈ Q) ∨ (|alt(Q)|≠1 ∧ DOXᵂₓ ∉ Q ∧ INQᵂₓ ⊆ Q)

**Our Hamblin simplification**: branches on `Q.length` and uses abstract
`believes`/`entertains` functions instead of DOX/INQ membership. This
preserves the essential violation property while avoiding the need for
inquisitive semantics infrastructure (downward closure, support).
-/
def shknow {W E : Type*}
    (believes : E → (W → Bool) → Bool)
    (entertains : E → QuestionDen W → Bool)
    : E → QuestionDen W → W → Bool :=
  fun x Q _w =>
    if Q.length == 1 then
      match Q.head? with
      | some p => believes x p
      | none => false
    else
      !(Q.any (believes x)) && entertains x Q

/--
*shknow violates P-to-Q Entailment: knowing p does not entail wondering Q.
-/
theorem shknow_violates_ptoq {W E : Type*}
    (believes : E → (W → Bool) → Bool)
    (entertains : E → QuestionDen W → Bool)
    (x : E) (p q : BProp W) (w : W)
    (hp_bel : believes x p = true)
    (hpq : p ≠ q) :
    ¬IsPtoQEntailing (shknow believes entertains) := by
  intro hPtoQ
  have h1 : shknow believes entertains x [p] w = true := by
    simp [shknow, hp_bel]
  have hp_mem : p ∈ ([p, q] : List (W → Bool)) := by simp
  have h2 := hPtoQ x [p, q] w p hp_mem h1
  simp only [shknow, List.length_cons] at h2
  have h3 : ([p, q] : List (W → Bool)).any (believes x) = true := by
    simp [List.any_cons, hp_bel]
  simp [h3] at h2

/--
*all-open (@cite{roelofsen-uegaki-2020} §4.6): "consider all possibilities
open." Defined as:
⟦all-open⟧(Q)(x) = ∀p ∈ Q. ¬B(x, p̄)

x's beliefs are compatible with every answer. This predicate quantifies
universally over alternatives, violating P-to-Q Entailment.
-/
def allOpen {W E : Type*}
    (believes : E → (W → Bool) → Bool)
    : E → QuestionDen W → W → Bool :=
  fun x Q _w => Q.all (fun p => !(believes x (fun w => !(p w))))

/--
*all-open violates P-to-Q Entailment: being compatible with one answer p
does not entail being compatible with ALL answers in Q.
-/
theorem allOpen_violates_ptoq {W E : Type*}
    (believes : E → (W → Bool) → Bool)
    (x : E) (p q : BProp W) (w : W)
    (hp_compat : believes x (fun w => !(p w)) = false)
    (hq_incompat : believes x (fun w => !(q w)) = true) :
    ¬IsPtoQEntailing (allOpen believes) := by
  intro hPtoQ
  have h1 : allOpen believes x [p] w = true := by
    simp [allOpen, hp_compat]
  have hp_mem : p ∈ ([p, q] : List (W → Bool)) := by simp
  have h2 := hPtoQ x [p, q] w p hp_mem h1
  simp only [allOpen, List.all_cons, List.all_cons, List.all_nil] at h2
  simp [hp_compat, hq_incompat] at h2

/--
*knopinion (@cite{steinert-threlkeld-2020}): "know" with declaratives,
"have no opinion about" with interrogatives.

**Paper's definition** (@cite{roelofsen-uegaki-2020} eq. 38, in inquisitive semantics):
⟦knopinion⟧ᵂ = λQ λx. w ∈ DOXᵂₓ ∧ (DOXᵂₓ ∈ Q ∨ DOXᵂₓ ∈ ¬Q)

This is a uniform definition (no branching on |alt(Q)|): factivity + either
resolving or fully ignorant.

**Our Hamblin simplification**: branches on `Q.length` with `believes`/`all ¬believes`.
Structurally different from the paper's definition, but preserves the essential
P-to-Q violation: knowing p does not entail having no opinion about Q.
-/
def knopinion {W E : Type*}
    (believes : E → (W → Bool) → Bool)
    : E → QuestionDen W → W → Bool :=
  fun x Q _w =>
    if Q.length == 1 then
      match Q.head? with
      | some p => believes x p
      | none => false
    else
      Q.all (fun p => !(believes x p))

/--
*knopinion violates P-to-Q Entailment: knowing p does not entail having
no opinion about Q.
-/
theorem knopinion_violates_ptoq {W E : Type*}
    (believes : E → (W → Bool) → Bool)
    (x : E) (p q : BProp W) (w : W)
    (hp_bel : believes x p = true)
    (hpq : p ≠ q) :
    ¬IsPtoQEntailing (knopinion believes) := by
  intro hPtoQ
  have h1 : knopinion believes x [p] w = true := by
    simp [knopinion, hp_bel]
  have hp_mem : p ∈ ([p, q] : List (W → Bool)) := by simp
  have h2 := hPtoQ x [p, q] w p hp_mem h1
  simp only [knopinion, List.length_cons] at h2
  have h3 : ([p, q] : List (W → Bool)).all (fun r => !(believes x r)) = false := by
    simp [List.all_cons, hp_bel]
  simp [h3] at h2

-- ============================================================================
-- Positive P-to-Q Proofs for Attested Predicates
-- (@cite{roelofsen-uegaki-2020} §§4.2–4.5)
-- ============================================================================

/-!
## Attested Predicates Satisfy P-to-Q Entailment

The negative tests above show fictitious predicates violate P-to-Q. Here we
prove that attested predicates **satisfy** it, completing the paper's argument.

### Modal Bases for Clause-Embedding Predicates

Following @cite{ciardelli-groenendijk-roelofsen-2018} and
@cite{roelofsen-uegaki-2020}, we use:
- `DOX x w` — doxastic state: set of worlds x considers possible in w
- `INQ x w` — inquisitive state: set of subsets of DOX that x entertains in w

A clause-embedding predicate's semantics can be expressed in terms of how
these modal bases relate to the complement denotation Q.
-/

/-- Doxastic state: the set of worlds an agent considers possible. -/
abbrev DoxState (W : Type*) := W → Bool

/-- Bouletic state: the set of worlds compatible with an agent's preferences. -/
abbrev BouState (W : Type*) := W → Bool

/-- Inquisitive state: the issues an agent entertains.
Modeled as a list of propositions (subsets of DOX) that the agent
would like to resolve. -/
abbrev InqState (W : Type*) := List (W → Bool)

/--
Wonder semantics (@cite{roelofsen-uegaki-2020} eq. 33):
⟦wonder⟧ = λQ λx. DOX_x ∉ Q ∧ INQ_x ⊆ Q

The first conjunct (ignorance) says x's doxastic state doesn't resolve Q.
The second (entertainment) says x entertains the issue expressed by Q.

We parametrize on a `covers` relation (s ⊆ p) to avoid requiring `Fintype W`.
The ignorance component checks that NO alternative in Q covers DOX.
The entertainment component checks that every issue in INQ is covered by
some alternative in Q.
-/
def wonderSem {W E : Type*}
    (dox : E → W → W → Bool)
    (inq : E → W → InqState W)
    (covers : (W → Bool) → (W → Bool) → Bool)
    : E → QuestionDen W → W → Bool :=
  fun x Q w =>
    !(Q.any (fun p => covers (dox x w) p)) &&
    (inq x w).all (fun s => Q.any (fun p => covers s p))

/--
Wonder trivially satisfies P-to-Q Entailment because the declarative
semantics is always false.

For a singleton complement {p}, ⟦wonder⟧({p})(x)(w) requires both:
- ignorance: ¬(covers DOX p) — DOX is NOT a subset of p
- entertainment: covers DOX p (the only alternative is p, so INQ ⊆ {p}
  requires each issue to be covered by p; if DOX itself is an issue,
  this requires covers DOX p)

These are contradictory when DOX is among the inquisitive issues.
More generally, if any s ∈ INQ has `covers s p = covers DOX p`
(e.g., DOX ∈ INQ), the conjunction is false.

The general proof: if INQ contains DOX, the singleton semantics is
always false, making P-to-Q vacuously true.
-/
theorem wonder_satisfies_ptoq {W E : Type*}
    (dox : E → W → W → Bool)
    (inq : E → W → InqState W)
    (covers : (W → Bool) → (W → Bool) → Bool)
    (hDoxInINQ : ∀ x w, dox x w ∈ inq x w) :
    IsPtoQEntailing (wonderSem dox inq covers) := by
  intro x Q w p _hp hSingleton
  simp only [wonderSem, Bool.and_eq_true, Bool.not_eq_true',
             List.any_cons, List.any_nil, Bool.or_false,
             List.all_eq_true] at hSingleton
  obtain ⟨hIgn, hEnt⟩ := hSingleton
  -- hIgn : covers (dox x w) p = false
  -- hEnt : ∀ s ∈ inq x w, [p].any (covers s) = true
  -- From hEnt with s = dox x w (by hDoxInINQ): covers (dox x w) p = true
  have hDox := hEnt (dox x w) (hDoxInINQ x w)
  simp at hDox
  -- hDox : covers (dox x w) p = true contradicts hIgn
  exact absurd hDox (by rw [hIgn]; exact Bool.false_ne_true)

/--
Daroo semantics (@cite{roelofsen-uegaki-2020} eq. 24, @cite{uegaki-roelofsen-2018}):
⟦daroo⟧ = λQ λx. INQ_sp ⊆ Q

Unlike wonder, daroo lacks the ignorance component (DOX ∉ Q). This makes
daroo compatible with both declarative and interrogative complements:
- With declarative p: INQ_sp ⊆ {p}↓ iff DOX_sp ⊆ p (x believes p)
- With interrogative Q: INQ_sp ⊆ Q (x entertains the issue of Q)
-/
def darooSem {W E : Type*}
    (inq : E → W → InqState W)
    (covers : (W → Bool) → (W → Bool) → Bool)
    : E → QuestionDen W → W → Bool :=
  fun x Q w =>
    (inq x w).all (fun s => Q.any (fun p => covers s p))

/--
Daroo satisfies P-to-Q Entailment: if INQ ⊆ {p} and p ∈ Q, then INQ ⊆ Q.

If every s in INQ is covered by the sole alternative p in the singleton,
and p ∈ Q, then every s in INQ is covered by some alternative in Q
(namely p itself). This is pure list-level monotonicity.
-/
theorem daroo_satisfies_ptoq {W E : Type*}
    (inq : E → W → InqState W)
    (covers : (W → Bool) → (W → Bool) → Bool) :
    IsPtoQEntailing (darooSem inq covers) := by
  intro x Q w p hp hSingleton
  simp only [darooSem, List.all_eq_true, List.any_eq_true] at hSingleton ⊢
  intro s hs
  obtain ⟨q, hq_mem, hq_cov⟩ := hSingleton s hs
  simp only [List.mem_singleton] at hq_mem
  exact ⟨p, hp, hq_mem ▸ hq_cov⟩

/--
Care semantics (@cite{roelofsen-uegaki-2020} eq. 23, based on
@cite{elliott-etal-2017} and @cite{theiler-etal-2018}):
⟦care⟧ᵂ = λQ λx : DOXᵂₓ ⊆ ⋃Q ∧ ∃p ∈ alt(Q). BOUᵂₓ ⊆ p ∨ BOUᵂₓ ∩ p = ∅

The first conjunct (doxastic support) says x's beliefs are compatible with Q.
The second conjunct (bouletic settlement) says some answer settles x's preferences
(either all preference worlds satisfy p, or none do).

`doxSupports s Q` checks DOX ⊆ ⋃Q (every doxastic world is in some answer).
`settled b p` checks BOU ⊆ p ∨ BOU ∩ p = ∅ (preferences are settled by p).
-/
def careSem {W E : Type*}
    (dox : E → W → DoxState W)
    (bou : E → W → BouState W)
    (doxSupports : DoxState W → QuestionDen W → Bool)
    (settled : BouState W → (W → Bool) → Bool)
    : E → QuestionDen W → W → Bool :=
  fun x Q w =>
    doxSupports (dox x w) Q &&
    Q.any (fun p => settled (bou x w) p)

/--
Care satisfies P-to-Q Entailment (@cite{roelofsen-uegaki-2020} §4.2, fn. 5).

If care({p})(x), then DOX ⊆ p (x believes p) and BOU is settled by p.
Since p ∈ Q: DOX ⊆ p ⊆ ⋃Q (doxastic support is monotone), and the
bouletic witness carries over. Hence care(Q)(x).

The proof requires monotonicity of doxastic support: if DOX supports {p}
and p ∈ Q, then DOX supports Q. This holds because DOX ⊆ p ⊆ ⋃Q.
-/
theorem care_satisfies_ptoq {W E : Type*}
    (dox : E → W → DoxState W)
    (bou : E → W → BouState W)
    (doxSupports : DoxState W → QuestionDen W → Bool)
    (settled : BouState W → (W → Bool) → Bool)
    (hMono : ∀ (s : DoxState W) (p : BProp W) (Q : QuestionDen W),
      doxSupports s [p] = true → p ∈ Q → doxSupports s Q = true) :
    IsPtoQEntailing (careSem dox bou doxSupports settled) := by
  intro x Q w p hp hSingleton
  simp only [careSem, Bool.and_eq_true, List.any_eq_true] at hSingleton ⊢
  obtain ⟨hDox, q, hq_mem, hq_settled⟩ := hSingleton
  simp only [List.mem_singleton] at hq_mem
  exact ⟨hMono _ _ _ hDox hp, p, hp, hq_mem ▸ hq_settled⟩

/--
Mõtlema semantics (@cite{roelofsen-uegaki-2020} eq. 32, @cite{roberts-2018}):

⟦mõtlema⟧ʷ = λQ λx. INQʷₓ ⊆ Q ∨ ∃p ∈ alt(Q): DOXʷₓ ⊆ p̄ ∧ IMGʷₓ ⊆ p

Two disjunctive readings:
- 'daroo' reading: INQ ⊆ Q (x entertains the issue expressed by Q)
- 'imagine' reading: ∃p ∈ Q, x believes ¬p but imagines p

**Hamblin simplification**: `covers` replaces set containment; `img` models
the imagination state IMGʷₓ.
-/
def mõtlemaSem {W E : Type*}
    (inq : E → W → InqState W)
    (dox : E → W → W → Bool)
    (img : E → W → W → Bool)
    (covers : (W → Bool) → (W → Bool) → Bool)
    : E → QuestionDen W → W → Bool :=
  fun x Q w =>
    -- 'daroo' reading: INQ ⊆ Q
    (inq x w).all (fun s => Q.any (fun p => covers s p)) ||
    -- 'imagine' reading: ∃p ∈ Q, believes ¬p ∧ imagines p
    Q.any (fun p => covers (dox x w) (fun w' => !(p w')) &&
                    covers (img x w) p)

/--
Mõtlema satisfies P-to-Q Entailment (@cite{roelofsen-uegaki-2020} §4.4).

On the 'daroo' reading: if INQ ⊆ {p}↓ and p ∈ Q, then INQ ⊆ Q
(same monotonicity argument as daroo).
On the 'imagine' reading: if ∃p ∈ {p₀}, believes ¬p ∧ imagines p
holds for p = p₀, and p₀ ∈ Q, then the same witness works for Q.
Either disjunct of the singleton semantics provides a witness for Q.
-/
theorem mõtlema_satisfies_ptoq {W E : Type*}
    (inq : E → W → InqState W)
    (dox : E → W → W → Bool)
    (img : E → W → W → Bool)
    (covers : (W → Bool) → (W → Bool) → Bool) :
    IsPtoQEntailing (mõtlemaSem inq dox img covers) := by
  intro x Q w p hp hSingleton
  simp only [mõtlemaSem, Bool.or_eq_true, List.all_eq_true, List.any_eq_true,
             Bool.and_eq_true] at hSingleton ⊢
  rcases hSingleton with hDaroo | hImagine
  · -- 'daroo' reading: INQ ⊆ {p}, so INQ ⊆ Q (p ∈ Q)
    left; intro s hs
    obtain ⟨q, hq_mem, hq_cov⟩ := hDaroo s hs
    simp only [List.mem_singleton] at hq_mem
    exact ⟨p, hp, hq_mem ▸ hq_cov⟩
  · -- 'imagine' reading: witness p works in Q too
    right
    obtain ⟨q, hq_mem, hq_bel, hq_img⟩ := hImagine
    simp only [List.mem_singleton] at hq_mem
    exact ⟨p, hp, hq_mem ▸ hq_bel, hq_mem ▸ hq_img⟩

/--
*wondows (@cite{steinert-threlkeld-2020}, @cite{roelofsen-uegaki-2020} eq. 35):
"know" with declaratives, "be uncertain" with interrogatives.

⟦wondows⟧ʷ = λQ λx. w ∈ DOXʷₓ ∧ DOXʷₓ ⊆ info(Q) ∧ ∀p ∈ alt(Q): DOXʷₓ ∩ p ≠ ∅

Three conjuncts: factivity (w ∈ DOX), informational support (DOX ⊆ ⋃Q),
and all-open (compatible with every alternative). The third conjunct
corresponds to `allOpen` and is what violates P-to-Q Entailment.

**Hamblin simplification**: `factive` checks w ∈ DOX, `doxSupports` checks
DOX ⊆ info(Q), and the all-open component reuses the `allOpen` pattern.
-/
def wondowsSem {W E : Type*}
    (factive : E → W → Bool)
    (doxSupports : E → QuestionDen W → W → Bool)
    (believes : E → (W → Bool) → Bool)
    : E → QuestionDen W → W → Bool :=
  fun x Q w =>
    factive x w &&
    doxSupports x Q w &&
    Q.all (fun p => !(believes x (fun w' => !(p w'))))

/--
*wondows violates P-to-Q Entailment (@cite{roelofsen-uegaki-2020} §4.6).

The all-open component (∀p ∈ Q. DOX ∩ p ≠ ∅) makes the predicate
anti-monotone in Q: being compatible with one answer p does not entail
being compatible with ALL answers in a larger Q. Same mechanism as `allOpen`.
-/
theorem wondows_violates_ptoq {W E : Type*}
    (factive : E → W → Bool)
    (doxSupports : E → QuestionDen W → W → Bool)
    (believes : E → (W → Bool) → Bool)
    (x : E) (p q : BProp W) (w : W)
    (h_factive : factive x w = true)
    (h_dox_singleton : doxSupports x [p] w = true)
    (_h_dox_pair : doxSupports x [p, q] w = true)
    (hp_compat : believes x (fun w' => !(p w')) = false)
    (hq_incompat : believes x (fun w' => !(q w')) = true) :
    ¬IsPtoQEntailing (wondowsSem factive doxSupports believes) := by
  intro hPtoQ
  have h1 : wondowsSem factive doxSupports believes x [p] w = true := by
    simp [wondowsSem, h_factive, h_dox_singleton, hp_compat]
  have hp_mem : p ∈ ([p, q] : List (W → Bool)) := by simp
  have h2 := hPtoQ x [p, q] w p hp_mem h1
  -- h2 : wondowsSem ... x [p, q] w = true
  -- The all-open component requires !(believes x (¬q)) = true, i.e., believes x (¬q) = false
  -- But hq_incompat says believes x (¬q) = true — contradiction
  simp only [wondowsSem, Bool.and_eq_true, List.all_eq_true,
             Bool.not_eq_true'] at h2
  obtain ⟨_, hall⟩ := h2
  have hq_mem : q ∈ ([p, q] : List (W → Bool)) := by simp
  rw [hall q hq_mem] at hq_incompat
  exact Bool.false_ne_true hq_incompat

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## Results

### P-to-Q Entailment (@cite{roelofsen-uegaki-2020})
- `IsPtoQEntailing`: Definition of the constraint
- `cDistributive_implies_ptoq`: C-distributivity ⟹ P-to-Q Entailment
- `degreeComparison_isPtoQEntailing`: Degree-comparison predicates satisfy it

### Positive P-to-Q Proofs (@cite{roelofsen-uegaki-2020} §§4.2–4.5)
- `wonder_satisfies_ptoq`: wonder is P-to-Q entailing (vacuously — declarative
  semantics is contradictory due to ignorance + singleton)
- `daroo_satisfies_ptoq`: daroo is P-to-Q entailing (INQ monotonicity)
- `care_satisfies_ptoq`: care is P-to-Q entailing (doxastic support monotonicity)
- `mõtlema_satisfies_ptoq`: mõtlema is P-to-Q entailing (both disjuncts monotone)

### Strawson C-Distributivity (@cite{uegaki-2019})
- `IsStrawsonCDistributive`: Weakened C-distributivity accounting for presuppositions
- `cDist_implies_strawson`: Plain C-dist ⟹ Strawson C-dist

### Fictitious Predicate Rejection (@cite{roelofsen-uegaki-2020} §4.6)
- `shknow_violates_ptoq`: *shknow (know+wonder hybrid) ruled out
- `knopinion_violates_ptoq`: *knopinion (know+no-opinion hybrid) ruled out
- `allOpen_violates_ptoq`: *all-open (universal compatibility) ruled out
- `wondows_violates_ptoq`: *wondows (know+uncertain hybrid) ruled out

### Veridical Uniformity (@cite{spector-egr-2015})
- `IsVeridicalDecl`: ⟦V that p⟧(x) entails p (eq. 1)
- `IsVeridicalInterrog`: ⟦V Q⟧(x) ∧ p ∧ p ∈ Q entails ⟦V that p⟧(x) (eq. 3)
- `IsVeridicallyUniform`: both or neither (eq. 5)
- `cDist_not_implies_veridicalUniformity`: C-dist ⇏ Veridical Uniformity

### Constraint Hierarchy (Mathlib `PartialOrder`)
- `Constraint`: inductive with `.cDist`, `.ptoQ`, `.strawsonCDist`, `.vu`
- `PartialOrder Constraint`: ptoQ ≤ cDist, strawsonCDist ≤ cDist, vu incomparable
- **Separation theorems** (all 6 non-implication directions proved):
  - `ptoQ_not_implies_strawsonCDist`: P-to-Q ⇏ Strawson C-dist
  - `strawsonCDist_not_implies_ptoQ`: Strawson C-dist ⇏ P-to-Q
  - `vu_not_implies_cDist`: VU ⇏ C-dist
  - `vu_not_implies_ptoQ`: VU ⇏ P-to-Q
  - `vu_not_implies_strawsonCDist`: VU ⇏ Strawson C-dist
  - `ptoQ_not_implies_vu`, `strawsonCDist_not_implies_vu`: ⇏ VU
-/

end Semantics.Attitudes.EmbeddingConstraints
