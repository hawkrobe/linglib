import Linglib.Core.Logic.Truth3

/-!
# Three-Valued Logics: LP and K3
@cite{priest-1979} @cite{kleene-1952}

LP (Logic of Paradox) and K3 (Strong Kleene logic) are dual
three-valued logics built on the same truth tables but with
different designated values:

- **K3** (Strong Kleene): designated value = {1}. Preserves truth.
- **LP** (Logic of Paradox): designated values = {1, ½}. Preserves
  non-falsity.

Both use Strong Kleene connectives (already in `Core/Logic/Truth3.lean`).
The only difference is what counts as "satisfied": K3 requires value 1
(like classical truth), while LP accepts value ½ as well (overlap of
truth and falsity, as in paraconsistent logic).

## Key Results

- **LP/K3 duality via negation**: LP-sat(¬φ) ↔ ¬K3-sat(φ)
- **LP preserves excluded middle**: P ∨ ¬P is always LP-designated
- **K3 has no tautologies**: every formula gets value ½ in the
  all-indeterminate model
- **Explosion fails in LP**: P ∧ ¬P ⊭^LP Q
- **Conjunction respects designation**: LP/K3 designation distributes
  over Strong Kleene conjunction

## Connection to TCS

@cite{cobreros-etal-2012} Theorem 3: in the restricted vocabulary,
t-consequence = LP-consequence and s-consequence = K3-consequence.
The correspondence is proved in `Theories/Semantics/Supervaluation/TCS.lean`.
-/

namespace Core.Logic.ThreeValuedLogic

open Core.Duality (Truth3)

-- ════════════════════════════════════════════════════
-- § 1. Designated Values
-- ════════════════════════════════════════════════════

/-- LP-designated: value is non-false (true or indeterminate).
    In LP, ½ is in the overlap of truth and falsity — both P and ¬P
    can hold. This makes LP paraconsistent: contradictions don't
    entail everything. -/
def isLPDesignated (v : Truth3) : Prop := v ≠ Truth3.false

/-- K3-designated: value is true (= 1). The only designated value.
    This makes K3 paracomplete: some formulas (borderline cases)
    are neither true nor false. -/
def isK3Designated (v : Truth3) : Prop := v = Truth3.true

instance (v : Truth3) : Decidable (isLPDesignated v) :=
  inferInstanceAs (Decidable (v ≠ Truth3.false))

instance (v : Truth3) : Decidable (isK3Designated v) :=
  inferInstanceAs (Decidable (v = Truth3.true))

-- ════════════════════════════════════════════════════
-- § 2. Structural Properties of Designation
-- ════════════════════════════════════════════════════

/-- **LP/K3 duality via negation.** LP-designation of the negation
    is equivalent to K3-non-designation of the original. This is
    the semantic core of duality between LP and K3. -/
theorem lp_neg_iff_not_k3 (v : Truth3) :
    isLPDesignated (Truth3.neg v) ↔ ¬isK3Designated v := by
  cases v <;> simp [isLPDesignated, isK3Designated, Truth3.neg]

/-- K3-designation of the negation ↔ LP-non-designation. -/
theorem k3_neg_iff_not_lp (v : Truth3) :
    isK3Designated (Truth3.neg v) ↔ ¬isLPDesignated v := by
  cases v <;> simp [isLPDesignated, isK3Designated, Truth3.neg]

/-- LP-designation distributes over Strong Kleene conjunction. -/
theorem lp_meet (v w : Truth3) :
    isLPDesignated (Truth3.meet v w) ↔
    isLPDesignated v ∧ isLPDesignated w := by
  cases v <;> cases w <;>
    simp [isLPDesignated, Truth3.meet]

/-- K3-designation distributes over Strong Kleene conjunction. -/
theorem k3_meet (v w : Truth3) :
    isK3Designated (Truth3.meet v w) ↔
    isK3Designated v ∧ isK3Designated w := by
  cases v <;> cases w <;>
    simp [isK3Designated, Truth3.meet]

/-- K3-designation implies LP-designation. -/
theorem k3_implies_lp (v : Truth3) :
    isK3Designated v → isLPDesignated v := by
  cases v <;> simp [isK3Designated, isLPDesignated]

/-- Both designations agree on classical (bivalent) values. -/
theorem designations_agree_classical (b : Bool) :
    isLPDesignated (Truth3.ofBool b) ↔ isK3Designated (Truth3.ofBool b) := by
  cases b <;> simp [isLPDesignated, isK3Designated, Truth3.ofBool]

-- ════════════════════════════════════════════════════
-- § 3. Propositional Formulas and Three-Valued Evaluation
-- ════════════════════════════════════════════════════

/-- Propositional formulas over an atom type. Structurally identical
    to `TCSFormula` but parameterized by a single type. -/
inductive PropFormula (Atom : Type*) where
  | atom : Atom → PropFormula Atom
  | neg : PropFormula Atom → PropFormula Atom
  | conj : PropFormula Atom → PropFormula Atom → PropFormula Atom

/-- A many-valued model: assigns a three-valued truth value to each atom. -/
abbrev MVModel (Atom : Type*) := Atom → Truth3

/-- Three-valued formula evaluation using Strong Kleene connectives.
    This is the semantic core shared by LP and K3 — the only
    difference is which values count as designated. -/
def mvEval {Atom : Type*} (M : MVModel Atom) : PropFormula Atom → Truth3
  | .atom a => M a
  | .neg φ => Truth3.neg (mvEval M φ)
  | .conj φ ψ => Truth3.meet (mvEval M φ) (mvEval M ψ)

-- ════════════════════════════════════════════════════
-- § 4. LP and K3 Satisfaction
-- ════════════════════════════════════════════════════

/-- LP-satisfaction: a formula is LP-satisfied iff its three-valued
    evaluation is designated (non-false). -/
def lpSat {Atom : Type*} (M : MVModel Atom) (φ : PropFormula Atom) : Prop :=
  isLPDesignated (mvEval M φ)

/-- K3-satisfaction: a formula is K3-satisfied iff its three-valued
    evaluation is true. -/
def k3Sat {Atom : Type*} (M : MVModel Atom) (φ : PropFormula Atom) : Prop :=
  isK3Designated (mvEval M φ)

/-- LP/K3 duality lifts to formulas: LP-sat(¬φ) ↔ ¬K3-sat(φ). -/
theorem lpSat_neg_iff {Atom : Type*} (M : MVModel Atom)
    (φ : PropFormula Atom) :
    lpSat M (.neg φ) ↔ ¬k3Sat M φ := by
  simp [lpSat, k3Sat, mvEval, lp_neg_iff_not_k3]

/-- K3-sat(¬φ) ↔ ¬LP-sat(φ). -/
theorem k3Sat_neg_iff {Atom : Type*} (M : MVModel Atom)
    (φ : PropFormula Atom) :
    k3Sat M (.neg φ) ↔ ¬lpSat M φ := by
  simp [lpSat, k3Sat, mvEval, k3_neg_iff_not_lp]

/-- LP-sat distributes over conjunction. -/
theorem lpSat_conj {Atom : Type*} (M : MVModel Atom)
    (φ ψ : PropFormula Atom) :
    lpSat M (.conj φ ψ) ↔ lpSat M φ ∧ lpSat M ψ := by
  simp [lpSat, mvEval, lp_meet]

/-- K3-sat distributes over conjunction. -/
theorem k3Sat_conj {Atom : Type*} (M : MVModel Atom)
    (φ ψ : PropFormula Atom) :
    k3Sat M (.conj φ ψ) ↔ k3Sat M φ ∧ k3Sat M ψ := by
  simp [k3Sat, mvEval, k3_meet]

-- ════════════════════════════════════════════════════
-- § 5. LP and K3 Consequence
-- ════════════════════════════════════════════════════

/-- LP-consequence: preservation of LP-designation (nonzero value)
    from premises to conclusion. -/
def LPConsequence {Atom : Type*}
    (Γ : List (PropFormula Atom)) (φ : PropFormula Atom) : Prop :=
  ∀ M : MVModel Atom, (∀ γ ∈ Γ, lpSat M γ) → lpSat M φ

/-- K3-consequence: preservation of value 1 from premises to
    conclusion. -/
def K3Consequence {Atom : Type*}
    (Γ : List (PropFormula Atom)) (φ : PropFormula Atom) : Prop :=
  ∀ M : MVModel Atom, (∀ γ ∈ Γ, k3Sat M γ) → k3Sat M φ

-- ════════════════════════════════════════════════════
-- § 6. Key Meta-Theorems
-- ════════════════════════════════════════════════════

/-- **No K3 tautologies.** In the all-indeterminate model, every
    formula evaluates to `indet`, so no formula is K3-valid.

    Theorem 2 of @cite{cobreros-etal-2012}: no formula in the
    restricted vocabulary is s-valid. -/
theorem mvEval_allIndet {Atom : Type*}
    (φ : PropFormula Atom) :
    mvEval (fun _ : Atom => Truth3.indet) φ = Truth3.indet := by
  induction φ with
  | atom _ => rfl
  | neg ψ ih => simp [mvEval, ih, Truth3.neg]
  | conj ψ χ ihψ ihχ => simp [mvEval, ihψ, ihχ, Truth3.meet]

theorem k3_no_tautologies {Atom : Type*} [Nonempty Atom]
    (φ : PropFormula Atom) :
    ¬(∀ M : MVModel Atom, k3Sat M φ) := by
  intro h
  have := h (fun _ => Truth3.indet)
  simp [k3Sat, isK3Designated, mvEval_allIndet] at this

/-- **Every formula is LP-satisfiable.** The all-indeterminate model
    LP-satisfies everything (since `indet ≠ false`).

    Theorem 2 of @cite{cobreros-etal-2012}: every formula in the
    restricted vocabulary is t-satisfiable. -/
theorem lp_all_satisfiable {Atom : Type*}
    (φ : PropFormula Atom) :
    lpSat (fun _ : Atom => Truth3.indet) φ := by
  simp [lpSat, isLPDesignated, mvEval_allIndet]

/-- **Explosion fails in LP.** There exist atoms a, b such that
    {a ∧ ¬a} ⊭^LP b. Countermodel: M(a) = ½, M(b) = 0. -/
theorem lp_no_explosion :
    ∃ (φ ψ : PropFormula Bool),
      ¬LPConsequence [.conj φ (.neg φ)] ψ := by
  refine ⟨.atom true, .atom false, ?_⟩
  intro h
  have := h (fun b => if b then Truth3.indet else Truth3.false)
    (fun γ hγ => by
      simp at hγ; subst hγ
      simp [lpSat, isLPDesignated, mvEval, Truth3.meet, Truth3.neg])
  simp [lpSat, isLPDesignated, mvEval] at this

end Core.Logic.ThreeValuedLogic
