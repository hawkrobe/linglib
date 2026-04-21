import Linglib.Core.Situation
import Linglib.Theories.Semantics.Causation.Interpretation

/-!
# Glass 2023: Anna Karenina Principle and *cause*
@cite{glass-2023b}

Using the Anna Karenina Principle to explain why *cause* favors
negative-sentiment complements. Semantics and Pragmatics 16, Article 6.

## Core contributions

1. Cross-cuts necessity/sufficiency into **local** (∃ background) vs
   **global** (∀ backgrounds) variants, reusing the existing parameterized
   definitions from @cite{nadathur-lauer-2020}.

2. Shows that **global sufficiency licenses inference under uncertainty**
   while global necessity does not — the key asymmetry (Table 2).

3. Proposes that *cause* **entails** local sufficiency and only
   **implicates** local necessity — reversing @cite{nadathur-lauer-2020}'s
   assignment where *cause* entails necessity.

4. Links the asymmetry to sentiment via the **Anna Karenina Principle**
   (Diamond 1997): desirable outcomes get conjunctive models
   (multiple necessary factors), undesirable outcomes get disjunctive
   models (single sufficient factors), so *C causes E* is true in
   more contexts when *E* is bad.

## Integration

Glass's proposed truth conditions for *cause* are truth-conditionally
identical to @cite{nadathur-lauer-2020}'s *make* — both reduce to
`causallySufficient`. This means Glass proposes collapsing the
`Causative.cause` / `Causative.make` distinction at
the semantic level, relegating the difference to pragmatic implicature.
-/

namespace Glass2023

open Core (Situation)

open Core.Causal
open Semantics.Causation.Sufficiency
open Semantics.Causation.Necessity
open Core.Verbs (Causative)
open Semantics.Causation.Interpretation
open Semantics.Causation.CCSelection

-- ============================================================
-- § 1. Local vs Global Necessity and Sufficiency (defs 8–11)
-- ============================================================

/-- Helper: a variable that is undetermined has no value. -/
private theorem hasValue_of_get_none {s : Situation} {v : Variable} {b : Bool}
    (h : s.get v = none) : s.hasValue v b = false := by
  simp only [Situation.hasValue, Situation.get] at *; rw [h]; rfl

/-- **Globally sufficient** (@cite{glass-2023b} def 11): C guarantees E
    no matter what other upstream variables are set to.

    Quantifies over all backgrounds that leave C and E undetermined,
    then delegates to `causallySufficient`. -/
def GloballySufficient (dyn : CausalDynamics) (cause effect : Variable) : Prop :=
  ∀ bg : Situation, bg.get cause = none → bg.get effect = none →
    causallySufficient dyn bg cause effect = true

/-- **Locally sufficient** (@cite{glass-2023b} def 10): there exists
    some background (with E undetermined) where adding C guarantees E.

    The constraint `bg.get effect = none` excludes degenerate backgrounds
    where the effect is already true, mirroring `GloballySufficient`. -/
def LocallySufficient (dyn : CausalDynamics) (cause effect : Variable) : Prop :=
  ∃ bg : Situation, bg.get effect = none ∧
    causallySufficient dyn bg cause effect = true

/-- **Globally necessary** (@cite{glass-2023b} def 9): without C,
    E never develops, regardless of other variables.

    This is Glass's simple counterfactual test: for all backgrounds
    where C is absent, E doesn't develop. This is weaker than
    @cite{nadathur-2024} Def 10b (`causallyNecessary`), which adds
    precondition and achievability checks. -/
def GloballyNecessary (dyn : CausalDynamics) (cause effect : Variable) : Prop :=
  ∀ bg : Situation, bg.get cause = none → bg.get effect = none →
    (normalDevelopment dyn bg).hasValue effect true = false

/-- **Locally necessary** (@cite{glass-2023b} def 8): there exists
    some background where E requires C — i.e., removing C blocks E. -/
def LocallyNecessary (dyn : CausalDynamics) (cause effect : Variable) : Prop :=
  ∃ bg : Situation, bg.get cause = none ∧ bg.get effect = none ∧
    (normalDevelopment dyn bg).hasValue effect true = false

-- ============================================================
-- § 2. Entailment: Global → Local (Glass (21a)–(22a))
-- ============================================================

/-- Global sufficiency entails local sufficiency (@cite{glass-2023b} (22a)). -/
theorem global_sufficient_implies_local {dyn : CausalDynamics}
    {cause effect : Variable} (h : GloballySufficient dyn cause effect) :
    LocallySufficient dyn cause effect :=
  ⟨Situation.empty, rfl, h Situation.empty rfl rfl⟩

/-- Global necessity entails local necessity (@cite{glass-2023b} (21a)). -/
theorem global_necessary_implies_local {dyn : CausalDynamics}
    {cause effect : Variable} (h : GloballyNecessary dyn cause effect) :
    LocallyNecessary dyn cause effect :=
  ⟨Situation.empty, rfl, rfl, h Situation.empty rfl rfl⟩

-- ============================================================
-- § 2b. Non-entailment: Local ↛ Global (Glass (21b)–(22b))
-- ============================================================

/-! The local/global distinction is non-trivial: local sufficiency does
    NOT imply global, and local necessity does NOT imply global.

    Witness for (22b): in the conjunctive model (A∧B→C), A is locally
    sufficient (with B=true) but not globally sufficient (B unknown).

    Witness for (21b): in the disjunctive model (A∨B→C), A is locally
    necessary (with B absent, only A can produce C) but not globally
    necessary (with B present, C develops without A). -/

/-- Local sufficiency does NOT imply global sufficiency
    (@cite{glass-2023b} (22b)).

    Witness: conjunctive model. A is locally sufficient (when B=true)
    but not globally sufficient (empty background is counterexample). -/
theorem local_sufficient_not_implies_global :
    ∃ (dyn : CausalDynamics) (c e : Variable),
      LocallySufficient dyn c e ∧ ¬ GloballySufficient dyn c e := by
  let a := mkVar "a"
  let b := mkVar "b"
  let c := mkVar "c"
  refine ⟨CausalDynamics.conjunctiveCausation a b c, a, c, ?_, ?_⟩
  · exact ⟨Situation.empty.extend b true, rfl,
      conjunctive_sufficient_with_other a b c (by decide) (by decide) (by decide)⟩
  · intro h
    have h1 := h Situation.empty rfl rfl
    have h2 : causallySufficient (CausalDynamics.conjunctiveCausation a b c)
        Situation.empty a c = false :=
      conjunctive_neither_sufficient_alone a b c (by decide) (by decide) (by decide)
    rw [h2] at h1
    exact absurd h1 (by decide)

/-- Local necessity does NOT imply global necessity
    (@cite{glass-2023b} (21b)).

    Witness: disjunctive model. A is locally necessary (when B is
    absent: without A, no law fires, so C doesn't develop). But A is
    NOT globally necessary: with B=true in background, the law B→C
    fires and C develops without A. -/
theorem local_necessary_not_implies_global :
    ∃ (dyn : CausalDynamics) (c e : Variable),
      LocallyNecessary dyn c e ∧ ¬ GloballyNecessary dyn c e := by
  let a := mkVar "a"
  let b := mkVar "b"
  let c := mkVar "c"
  refine ⟨CausalDynamics.disjunctiveCausation a b c, a, c, ?_, ?_⟩
  · -- Local: empty background — without a, no law fires, c stays undetermined
    refine ⟨Situation.empty, rfl, rfl, ?_⟩
    · -- normalDevelopment of empty situation: no preconditions met → fixpoint
      show (normalDevelopment (CausalDynamics.disjunctiveCausation a b c)
        Situation.empty).hasValue c true = false
      suffices hfix : isFixpoint (CausalDynamics.disjunctiveCausation a b c)
          Situation.empty = true by
        rw [normalDevelopment_of_fixpoint hfix]; rfl
      simp only [isFixpoint, CausalDynamics.disjunctiveCausation,
        CausalLaw.simple, List.all_cons, List.all_nil, Bool.and_true,
        CausalLaw.preconditionsMet, List.all_cons, List.all_nil, Bool.and_true,
        Situation.hasValue, Situation.empty]; rfl
  · -- Not global: background {b = true} → law b→c fires → c develops without a
    intro h
    have hBg : (Situation.empty.extend b true).get a = none := by
      simp [Situation.get, Situation.extend]; decide
    have hBgC : (Situation.empty.extend b true).get c = none := by
      simp [Situation.get, Situation.extend]; decide
    have := h (Situation.empty.extend b true) hBg hBgC
    -- normalDevelopment with b=true: law b→c fires, c becomes true
    have hContra : (normalDevelopment (CausalDynamics.disjunctiveCausation a b c)
        (Situation.empty.extend b true)).hasValue c true = true := by
      set dyn := CausalDynamics.disjunctiveCausation a b c
      set bg := Situation.empty.extend b true
      have hfix : isFixpoint dyn (applyLawsOnce dyn bg) = true := by
        simp only [dyn, bg, isFixpoint, applyLawsOnce, CausalDynamics.disjunctiveCausation,
          CausalLaw.simple, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet,
          List.all_cons, List.all_nil, Bool.and_true,
          Situation.hasValue, Situation.extend, Situation.empty]
        split_ifs <;> simp_all
      change (normalDevelopment dyn bg 100).hasValue c true = true
      rw [show (100 : Nat) = 99 + 1 from rfl,
        normalDevelopment_fixpoint_after_one _ _ hfix]
      simp only [dyn, bg, applyLawsOnce, CausalDynamics.disjunctiveCausation,
        CausalLaw.simple, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet,
        List.all_cons, List.all_nil, Bool.and_true,
        Situation.hasValue, Situation.extend, Situation.empty]
      split_ifs <;> simp_all
    rw [hContra] at this
    exact absurd this (by decide)

-- ============================================================
-- § 3. Conjunctive Model — Glass's Lightbulb (Tables 1–2)
-- ============================================================

/-! The lightbulb has two switches: the light is on iff both are on.
    This is `CausalDynamics.conjunctiveCausation`, which already exists
    in `Core.Causal`. -/

/-- In a conjunctive model (A ∧ B → C), A is **globally necessary** for C:
    without A, the law can never fire, so C never develops.

    Proof: A is required by the law's preconditions. If A is undetermined
    in bg, no law sets it, so `preconditionsMet` fails, bg is a fixpoint,
    and `normalDevelopment` returns bg with C still undetermined. -/
theorem conjunctive_globally_necessary (a b c : Variable) :
    GloballyNecessary (CausalDynamics.conjunctiveCausation a b c) a c := by
  intro bg ha hc
  suffices hfix : isFixpoint (CausalDynamics.conjunctiveCausation a b c) bg = true by
    rw [normalDevelopment_of_fixpoint hfix]
    exact hasValue_of_get_none hc
  simp only [isFixpoint, CausalDynamics.conjunctiveCausation,
    CausalLaw.conjunctive, List.all_cons, List.all_nil, Bool.and_true]
  simp only [CausalLaw.preconditionsMet, List.all_cons, List.all_nil, Bool.and_true]
  have : bg.hasValue a true = false := hasValue_of_get_none ha
  simp [this]

/-- In a conjunctive model, A is **NOT globally sufficient** for C:
    the empty background (B undetermined) is a counterexample.

    Reuses `conjunctive_neither_sufficient_alone` from
    @cite{nadathur-lauer-2020}. -/
theorem conjunctive_not_globally_sufficient (a b c : Variable)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ GloballySufficient (CausalDynamics.conjunctiveCausation a b c) a c := by
  intro h
  have h1 := h Situation.empty rfl rfl
  have h2 : causallySufficient (CausalDynamics.conjunctiveCausation a b c)
      Situation.empty a c = false :=
    conjunctive_neither_sufficient_alone a b c hab hac hbc
  rw [h2] at h1
  exact absurd h1 (by decide)

/-- In a conjunctive model, A **is** locally sufficient for C:
    the background {B = true} is a witness.

    Reuses `conjunctive_sufficient_with_other`. -/
theorem conjunctive_locally_sufficient (a b c : Variable)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    LocallySufficient (CausalDynamics.conjunctiveCausation a b c) a c :=
  ⟨Situation.empty.extend b true,
   by show (Situation.empty.extend b true).get c = none
      simp only [Situation.get, Situation.extend, Situation.empty]
      simp [show c ≠ b from Ne.symm hbc],
   conjunctive_sufficient_with_other a b c hab hac hbc⟩

/-- **Table 2 left column** (@cite{glass-2023b}): in the conjunctive
    model, A is globally necessary but not globally sufficient.

    This means "A causes C" (positive outcome) is only true when
    all variables are known — it fails under uncertainty because
    local sufficiency requires knowledge of B. -/
theorem conjunctive_asymmetry (a b c : Variable)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    GloballyNecessary (CausalDynamics.conjunctiveCausation a b c) a c ∧
    ¬ GloballySufficient (CausalDynamics.conjunctiveCausation a b c) a c :=
  ⟨conjunctive_globally_necessary a b c,
   conjunctive_not_globally_sufficient a b c hab hac hbc⟩

-- ============================================================
-- § 4. Disjunctive Model — Contrast Case (Table 2 right column)
-- ============================================================

/-! In the disjunctive model (A ∨ B → C), each disjunct is
    individually globally sufficient: A alone guarantees C regardless
    of B. This contrasts with the conjunctive model.

    The disjunctive model also represents the **negative-polarity dual**
    of the conjunctive model (von Wright 1974): if A∧B→C, then
    ¬A∨¬B→¬C — the absence of any necessary factor is individually
    sufficient for the absence of the positive outcome. -/

/-- In a disjunctive model, A is **globally sufficient** for C:
    the law A → C fires whenever A = true, regardless of B.

    Proof: direct fixpoint argument. After one round of law application,
    `simple a c` fires (since A = true), setting C = true. Both laws
    have effect C, so the result is a fixpoint. -/
theorem disjunctive_globally_sufficient (a b c : Variable) :
    GloballySufficient (CausalDynamics.disjunctiveCausation a b c) a c := by
  intro bg ha hc
  show (normalDevelopment (CausalDynamics.disjunctiveCausation a b c)
    (bg.extend a true)).hasValue c true = true
  -- After one round, c = true: first law (simple a c) fires since a = true
  have hZ : (applyLawsOnce (CausalDynamics.disjunctiveCausation a b c)
      (bg.extend a true)).hasValue c true = true := by
    simp only [applyLawsOnce, CausalDynamics.disjunctiveCausation,
      CausalLaw.simple, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet,
      List.all_cons, List.all_nil, Bool.and_true,
      Situation.hasValue, Situation.extend]
    split_ifs <;> simp_all
  -- Both laws have effect (c, true) → fixpoint once c = true
  have hFix : isFixpoint (CausalDynamics.disjunctiveCausation a b c)
      (applyLawsOnce (CausalDynamics.disjunctiveCausation a b c)
        (bg.extend a true)) = true := by
    simp only [isFixpoint, CausalDynamics.disjunctiveCausation,
      CausalLaw.simple, List.all_cons, List.all_nil, Bool.and_true,
      applyLawsOnce, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet,
      Situation.hasValue, Situation.extend]
    split_ifs <;> simp_all
  change (normalDevelopment (CausalDynamics.disjunctiveCausation a b c)
    (bg.extend a true) 100).hasValue c true = true
  rw [show (100 : Nat) = 99 + 1 from rfl,
    normalDevelopment_fixpoint_after_one _ _ hFix]
  exact hZ

/-- In a disjunctive model, A is **NOT globally necessary** for C:
    with B present, C develops without A.

    This is the complement of `conjunctive_globally_necessary` —
    necessity fails precisely where sufficiency succeeds in the
    dual model. -/
theorem disjunctive_not_globally_necessary (a b c : Variable)
    (hab : a ≠ b) (hbc : b ≠ c) :
    ¬ GloballyNecessary (CausalDynamics.disjunctiveCausation a b c) a c := by
  intro h
  have hBg : (Situation.empty.extend b true).get a = none := by
    simp only [Situation.get, Situation.extend, Situation.empty]
    simp [show a ≠ b from hab]
  have hBgC : (Situation.empty.extend b true).get c = none := by
    simp only [Situation.get, Situation.extend, Situation.empty]
    simp [show c ≠ b from Ne.symm hbc]
  have := h (Situation.empty.extend b true) hBg hBgC
  -- But b→c fires, so c develops
  have hContra : (normalDevelopment (CausalDynamics.disjunctiveCausation a b c)
      (Situation.empty.extend b true)).hasValue c true = true := by
    set dyn := CausalDynamics.disjunctiveCausation a b c
    set bg := Situation.empty.extend b true
    have hfix : isFixpoint dyn (applyLawsOnce dyn bg) = true := by
      simp only [dyn, bg, isFixpoint, applyLawsOnce, CausalDynamics.disjunctiveCausation,
        CausalLaw.simple, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet,
        List.all_cons, List.all_nil, Bool.and_true,
        Situation.hasValue, Situation.extend, Situation.empty]
      split_ifs <;> simp_all
    change (normalDevelopment dyn bg 100).hasValue c true = true
    rw [show (100 : Nat) = 99 + 1 from rfl,
      normalDevelopment_fixpoint_after_one _ _ hfix]
    simp only [dyn, bg, applyLawsOnce, CausalDynamics.disjunctiveCausation,
      CausalLaw.simple, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet,
      List.all_cons, List.all_nil, Bool.and_true,
      Situation.hasValue, Situation.extend, Situation.empty]
    split_ifs <;> simp_all
  rw [hContra] at this
  exact absurd this (by decide)

/-- **Table 2 right column** (@cite{glass-2023b}): in the disjunctive
    model, A is globally sufficient but not globally necessary.

    This is the dual of `conjunctive_asymmetry`. Together they
    show the fundamental asymmetry: global sufficiency licenses
    inference under uncertainty; global necessity does not. -/
theorem disjunctive_asymmetry (a b c : Variable)
    (hab : a ≠ b) (hbc : b ≠ c) :
    GloballySufficient (CausalDynamics.disjunctiveCausation a b c) a c ∧
    ¬ GloballyNecessary (CausalDynamics.disjunctiveCausation a b c) a c :=
  ⟨disjunctive_globally_sufficient a b c,
   disjunctive_not_globally_necessary a b c hab hbc⟩

-- ============================================================
-- § 5. Von Wright Duality (von Wright 1974, pp.9–10)
-- ============================================================

/-! von Wright 1974: Conjunctive and disjunctive models are
    mirror images. If A∧B→C, then ¬A∨¬B→¬C. In the SEM framework,
    this means `GloballyNecessary` on the conjunctive model is
    equivalent to global prevention: absence of A guarantees absence
    of C.

    We state this as a direct equivalence: `GloballyNecessary dyn a c`
    is the same as "for all backgrounds, normalDevelopment without a
    does not produce c." This IS the definition — the duality is
    baked into the SEM's fixpoint semantics where absence of a
    precondition prevents the law from firing.

    The substantive duality theorem connects the two model types:
    what is globally necessary in the conjunctive model is globally
    sufficient in its disjunctive dual, and vice versa. -/

/-- **Von Wright duality** (von Wright 1974): what is globally
    necessary in a conjunctive model corresponds to what is globally
    sufficient in the disjunctive dual.

    Concretely: A is globally necessary for C in A∧B→C, AND
    A is globally sufficient for C in A∨B→C. -/
theorem von_wright_duality (a b c : Variable) :
    GloballyNecessary (CausalDynamics.conjunctiveCausation a b c) a c ∧
    GloballySufficient (CausalDynamics.disjunctiveCausation a b c) a c :=
  ⟨conjunctive_globally_necessary a b c,
   disjunctive_globally_sufficient a b c⟩

-- ============================================================
-- § 6. Glass's Alternative Semantics for *cause* (def 12)
-- ============================================================

/-! @cite{glass-2023b} proposes that *cause* **entails** local sufficiency
    and only **implicates** local necessity. This reverses
    @cite{nadathur-lauer-2020}, where *cause* entails necessity.

    Glass's definition (12) has three parts:
    - (12a) Entails: C and E both hold in the actual world.
    - (12b) Entails: C is locally sufficient for E.
    - (12c) Implicates: C is at least possibly locally necessary for E.

    Glass argues (p.16) that (12a) and (12b) are equivalent given
    model-world alignment: if C and E both occur in a model where
    C is upstream of E, then the background must be set so that
    C combined with those settings guarantees E — i.e., C is locally
    sufficient. So the truth conditions reduce to `causallySufficient`.

    This makes Glass's *cause* truth-conditionally identical to
    @cite{nadathur-lauer-2020}'s *make*. -/

/-- Glass's proposed truth conditions for "C causes E" (def 12):
    C is locally sufficient for E. The requirement that C and E both
    hold (12a) is equivalent to local sufficiency (12b) given model-world
    alignment (@cite{glass-2023b} p.16). Necessity (12c) is conversationally
    implicated, not entailed. -/
def causeSemGlass (dyn : CausalDynamics) (bg : Situation)
    (cause effect : Variable) : Bool :=
  causallySufficient dyn bg cause effect

/-- Glass's *cause* is truth-conditionally identical to
    @cite{nadathur-lauer-2020}'s *make*. Both reduce to
    `causallySufficient`. -/
theorem glass_cause_is_make :
    causeSemGlass = makeSem := rfl

/-- Nadathur's `causeSem` (necessity + occurrence) entails
    Glass's `causeSemGlass` (sufficiency alone).

    This follows because `causeSem` conjoins effect occurrence
    (which is `causallySufficient`) with necessity. -/
theorem nadathur_implies_glass {dyn : CausalDynamics} {bg : Situation}
    {cause effect : Variable}
    (h : causeSem dyn bg cause effect = true) :
    causeSemGlass dyn bg cause effect = true := by
  simp only [causeSemGlass, causeSem, Bool.and_eq_true] at *
  exact h.1

/-- In a disjunctive model, the effect is entailed by the background
    when the second cause is already present — the precondition of
    @cite{nadathur-2024} Def 10b fails, making the first cause
    unnecessary. -/
private theorem disjunctive_effect_entailed (x y z : Variable) :
    (normalDevelopment (CausalDynamics.disjunctiveCausation x y z)
      (Situation.empty.extend y true)).hasValue z true = true := by
  set dyn := CausalDynamics.disjunctiveCausation x y z
  set bg := Situation.empty.extend y true
  have hfix : isFixpoint dyn (applyLawsOnce dyn bg) = true := by
    simp only [dyn, bg, isFixpoint, applyLawsOnce, CausalDynamics.disjunctiveCausation,
      CausalLaw.simple, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet,
      List.all_cons, List.all_nil, Bool.and_true,
      Situation.hasValue, Situation.extend, Situation.empty,
      Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true]
    split_ifs <;> simp_all
  change (normalDevelopment dyn bg 100).hasValue z true = true
  rw [show (100 : Nat) = 99 + 1 from rfl, normalDevelopment_fixpoint_after_one _ _ hfix]
  simp only [dyn, bg, applyLawsOnce, CausalDynamics.disjunctiveCausation,
    CausalLaw.simple, List.foldl, CausalLaw.apply, CausalLaw.preconditionsMet,
    List.all_cons, List.all_nil, Bool.and_true,
    Situation.hasValue, Situation.extend, Situation.empty]
  split_ifs <;> simp_all

set_option maxHeartbeats 800000 in
/-- The converse fails: Glass's analysis is strictly weaker.

    Witness: disjunctive model with backup cause present.
    A is sufficient (law A → C fires), but A is not necessary
    (backup cause B would produce C anyway).

    Uses `disjunctive_effect_entailed` to show the precondition
    of @cite{nadathur-2024} Def 10b fails (effect already entailed). -/
theorem glass_strictly_weaker :
    ∃ (dyn : CausalDynamics) (bg : Situation) (c e : Variable),
      causeSemGlass dyn bg c e = true ∧ causeSem dyn bg c e = false := by
  let x := mkVar "x"
  let y := mkVar "y"
  let z := mkVar "z"
  let dyn := CausalDynamics.disjunctiveCausation x y z
  let bg := Situation.empty.extend y true
  refine ⟨dyn, bg, x, z, ?_, ?_⟩
  · -- Glass: x is sufficient (monotonicity from empty)
    exact sufficiency_monotone_positive dyn Situation.empty x y z
      (disjunctive_isPositive x y z)
      (disjunctive_each_sufficient x y z (by decide))
  · -- Nadathur: causeSem requires necessity, which fails
    -- Effect z is already entailed by bg (y fires simple y z)
    have hEntailed := disjunctive_effect_entailed x y z
    simp only [causeSem, Bool.and_eq_false_iff]
    right
    -- causallyNecessary returns false because effect already entailed
    show causallyNecessary (CausalDynamics.disjunctiveCausation x y z)
      (Situation.empty.extend y true) x z = false
    unfold causallyNecessary
    simp only [hEntailed, Bool.or_true, ↓reduceIte]

-- ============================================================
-- § 7. Bridge to Causative and CC-Selection
-- ============================================================

/-! Glass's proposal has a direct structural consequence for the
    causative verb lexicon: if *cause* = `causallySufficient`, then
    `Causative.cause` and `Causative.make` have the
    same truth conditions on Glass's analysis.

    On @cite{nadathur-lauer-2020}'s analysis they differ:
    `.cause.toSemantics = causeSem` (necessity),
    `.make.toSemantics = makeSem` (sufficiency).

    On Glass's analysis, both map to `makeSem`. -/

/-- Glass's *cause* = `Causative.make.toSemantics`.

    This is the key bridge: on Glass's analysis, the truth-conditional
    content of *cause* is identical to that of *make*. The difference
    is pragmatic — *cause* implicates necessity. -/
theorem glass_cause_equals_builder_make :
    causeSemGlass = Causative.make.toSemantics := rfl

/-- Glass's *cause* = `CCSelectionMode.completionOfSufficientSet.toSemantics`.

    On Glass's analysis, *cause* selects the completing condition of
    a sufficient set — the same selection mode as *make*, *force*,
    and *enable* in @cite{baglini-bar-asher-siegal-2025}. -/
theorem glass_cause_equals_completion_mode :
    causeSemGlass = CCSelectionMode.completionOfSufficientSet.toSemantics := rfl

/-- Glass and Nadathur agree that *cause* and *make* differ, but
    disagree about WHERE the difference lies:
    - Nadathur: truth-conditional (cause = necessity, make = sufficiency)
    - Glass: pragmatic (both = sufficiency; cause implicates necessity)

    Formally: Nadathur's builder maps cause ≠ make, while Glass's
    proposed semantics would map both to `makeSem`. -/
theorem glass_nadathur_disagreement :
    Causative.cause.toSemantics ≠ Causative.make.toSemantics ∧
    causeSemGlass = Causative.make.toSemantics := by
  constructor
  · -- Nadathur: cause ≠ make (witnessed by overdetermination)
    have ⟨dyn, s, c, e, hne⟩ := truth_conditionally_distinct
    exact fun h => hne (by simp only [Causative.toSemantics] at h ⊢; rw [h])
  · rfl

-- ============================================================
-- § 8. Anna Karenina Principle + Sentiment (Sections 5–6, Table 3)
-- ============================================================

/-! The Anna Karenina Principle (Diamond 1997): good outcomes
    have many individually necessary-but-insufficient causes (conjunctive),
    while bad outcomes have single sufficient causes (disjunctive).

    Combined with the asymmetry from §§ 3–4 and the von Wright duality:
    - "C causes success" requires certainty about ALL factors
      (conjunctive: globally necessary, not globally sufficient)
    - "C causes failure" holds even under uncertainty
      (disjunctive: globally sufficient, not globally necessary)
    - Therefore *cause* co-occurs with negative complements more often.

    We model this concretely with work/luck/success, where:
    - Success = conjunctive model: work ∧ luck → success
    - Failure = disjunctive dual: ¬work ∨ ¬luck → ¬success

    The failure side is formalized using the disjunctive model with
    negated variables: laziness ∨ unluckiness → failure. By the von
    Wright duality, this is the mirror image of the success model. -/

section AnnaKarenina

private def work := mkVar "work"
private def luck := mkVar "luck"
private def success := mkVar "success"

-- Negative-polarity variables for the dual model
private def laziness := mkVar "laziness"
private def unluckiness := mkVar "unluckiness"
private def failure := mkVar "failure"

/-- The success model: work ∧ luck → success (conjunctive). -/
private def successModel := CausalDynamics.conjunctiveCausation work luck success

/-- The failure model: laziness ∨ unluckiness → failure (disjunctive).
    This is the von Wright dual of the success model. -/
private def failureModel := CausalDynamics.disjunctiveCausation laziness unluckiness failure

/-! ### Positive outcome: "work causes success" -/

/-- Work is globally necessary for success: without work,
    success never develops regardless of luck. -/
theorem work_globally_necessary :
    GloballyNecessary successModel work success :=
  conjunctive_globally_necessary work luck success

/-- Work is NOT globally sufficient for success: without knowing
    whether luck obtains, we cannot infer success from work alone. -/
theorem work_not_globally_sufficient :
    ¬ GloballySufficient successModel work success :=
  conjunctive_not_globally_sufficient work luck success
    (by decide) (by decide) (by decide)

/-- Work IS locally sufficient: when luck is present, work guarantees
    success. This is the condition under which "work causes success"
    is true on Glass's analysis. -/
theorem work_locally_sufficient :
    LocallySufficient successModel work success :=
  conjunctive_locally_sufficient work luck success
    (by decide) (by decide) (by decide)

/-! ### Negative outcome: "laziness causes failure" -/

/-- Laziness is globally sufficient for failure: the law laziness→failure
    fires regardless of unluckiness. -/
theorem laziness_globally_sufficient :
    GloballySufficient failureModel laziness failure :=
  disjunctive_globally_sufficient laziness unluckiness failure

/-- Laziness is NOT globally necessary for failure: unluckiness alone
    also causes failure. -/
theorem laziness_not_globally_necessary :
    ¬ GloballyNecessary failureModel laziness failure :=
  disjunctive_not_globally_necessary laziness unluckiness failure
    (by decide) (by decide)

/-! ### The sentiment prediction (Table 3) -/

/-- **Sentiment prediction** (@cite{glass-2023b} Table 3):

    "Work causes success" requires full certainty about all factors
    (globally necessary but NOT globally sufficient — fails under
    uncertainty). "Laziness causes failure" holds even under uncertainty
    (globally sufficient — true regardless of what else is known).

    This asymmetry, combined with the Anna Karenina Principle linking
    desirable outcomes to conjunctive models and undesirable outcomes
    to disjunctive models, explains why *cause* disproportionately
    co-occurs with negative-sentiment complements. -/
theorem sentiment_asymmetry :
    -- Positive outcome: cause true under certainty only
    (GloballyNecessary successModel work success ∧
     ¬ GloballySufficient successModel work success) ∧
    -- Negative outcome: cause true even under uncertainty
    (GloballySufficient failureModel laziness failure ∧
     ¬ GloballyNecessary failureModel laziness failure) :=
  ⟨⟨work_globally_necessary, work_not_globally_sufficient⟩,
   ⟨laziness_globally_sufficient, laziness_not_globally_necessary⟩⟩

end AnnaKarenina

end Glass2023
