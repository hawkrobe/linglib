import Linglib.Core.Causal.SEM.Defs

/-!
# Structural Equation Model: Queries, Intervention, and Counterfactuals
@cite{nadathur-lauer-2020} @cite{nadathur-2024}

Pearl's `do`-operator and the counterfactual queries built from it.

- `developsToBe` / `developsToTrue` / `factuallyDeveloped` — convenience
  predicates on the result of `normalDevelopment`
- `hasDirectLaw` / `hasIndependentSource` / `allVariables` /
  `innerVariables` — structural graph queries
- `intervene` / `manipulates` — Pearl's `do(X = val)` and the
  interventionist criterion for causation
- `causallySufficient` (@cite{nadathur-lauer-2020} Def 23)
- `isConsistentSuper` (@cite{nadathur-2024} Def 9b) — per-variable
  consistency of supersituations
- `causallyNecessary` (@cite{nadathur-2024} Def 10b) — but-for with
  precondition + achievability
- `simple_law_necessity` — structured proof that `c → e` makes `c`
  necessary for `e` against the empty background

All counterfactual queries are `Prop`-valued with `Decidable` instances
auto-derived from the underlying `Bool` computations, so they can be
used both in propositional reasoning (`obtain`, `intro`) and in
decidable contexts (`decide`, `if`).
-/

namespace Core.Causal

-- ============================================================
-- § Convenience Predicates
-- ============================================================

/-- A variable develops to a specific value. -/
def developsToBe (dyn : CausalDynamics) (s : Situation) (v : Variable) (val : Bool) : Prop :=
  (normalDevelopment dyn s).hasValue v val = true

instance (dyn : CausalDynamics) (s : Situation) (v : Variable) (val : Bool) :
    Decidable (developsToBe dyn s v val) :=
  inferInstanceAs (Decidable (_ = true))

/-- A variable becomes true after normal development. -/
def developsToTrue (dyn : CausalDynamics) (s : Situation) (v : Variable) : Prop :=
  developsToBe dyn s v true

instance (dyn : CausalDynamics) (s : Situation) (v : Variable) :
    Decidable (developsToTrue dyn s v) :=
  inferInstanceAs (Decidable (developsToBe ..))

/-- The cause is present and the effect holds after normal development.

    Shared primitive for `actuallyCaused` (Necessity.lean) and
    `complementActualized` (Ability.lean). -/
def factuallyDeveloped (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Prop :=
  s.hasValue cause true = true ∧
    (normalDevelopment dyn s).hasValue effect true = true

instance (dyn : CausalDynamics) (s : Situation) (cause effect : Variable) :
    Decidable (factuallyDeveloped dyn s cause effect) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- ============================================================
-- § Structural Graph Queries
-- ============================================================

/-- Some causal law directly connects `cause` to `effect`. -/
def hasDirectLaw (dyn : CausalDynamics) (cause effect : Variable) : Prop :=
  (dyn.laws.any fun law =>
    law.preconditions.any (fun (v, _) => v == cause) && law.effect == effect) = true

instance (dyn : CausalDynamics) (cause effect : Variable) :
    Decidable (hasDirectLaw dyn cause effect) :=
  inferInstanceAs (Decidable (_ = true))

/-- The intermediate has a causal law not depending on `cause`. -/
def hasIndependentSource (dyn : CausalDynamics)
    (cause intermediate : Variable) : Prop :=
  (dyn.laws.any fun law =>
    law.effect == intermediate &&
    !(law.preconditions.any (fun (v, _) => v == cause))) = true

instance (dyn : CausalDynamics) (cause intermediate : Variable) :
    Decidable (hasIndependentSource dyn cause intermediate) :=
  inferInstanceAs (Decidable (_ = true))

/-- All variables mentioned in a dynamics (preconditions and effects). -/
def allVariables (dyn : CausalDynamics) : List Variable :=
  (dyn.laws.flatMap fun law =>
    law.effect :: law.preconditions.map (·.1)).eraseDups

/-- Inner (endogenous) variables: those appearing as effects of laws. -/
def innerVariables (dyn : CausalDynamics) : List Variable :=
  (dyn.laws.map (·.effect)).eraseDups

-- ============================================================
-- § Intervention (Pearl's do-operator)
-- ============================================================

/-- **Intervene**: Pearl's do(X = val).

    Sets variable `target` to `val` and removes all laws that would
    determine `target`, so the intervention overrides the structural
    equations rather than being overwritten by them. -/
def intervene (dyn : CausalDynamics) (s : Situation)
    (target : Variable) (val : Bool) : CausalDynamics × Situation :=
  let dyn' : CausalDynamics := ⟨dyn.laws.filter (·.effect != target)⟩
  let s' := s.extend target val
  (dyn', s')

/-- **Manipulates**: intervening on `cause` changes the value of `effect`.

    Compares normal development under do(cause = true) vs do(cause = false).
    If the effect's value differs, then `cause` manipulates `effect`.

    This is the interventionist criterion for causation:
    X causes Y iff there exists an intervention on X that changes Y. -/
def manipulates (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Prop :=
  let (dynT, sT) := intervene dyn s cause true
  let (dynF, sF) := intervene dyn s cause false
  (normalDevelopment dynT sT).get effect ≠ (normalDevelopment dynF sF).get effect

instance (dyn : CausalDynamics) (s : Situation) (cause effect : Variable) :
    Decidable (manipulates dyn s cause effect) :=
  inferInstanceAs (Decidable (_ ≠ _))

-- ============================================================
-- § Counterfactual Queries (@cite{nadathur-lauer-2020} Definitions 23-24)
-- ============================================================

/-- **Causal Sufficiency** (@cite{nadathur-lauer-2020}, Definition 23).
    C is causally sufficient for E in situation s iff adding C and
    developing normally produces E. -/
def causallySufficient (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Prop :=
  (normalDevelopment dyn (s.extend cause true)).hasValue effect true = true

instance (dyn : CausalDynamics) (s : Situation) (cause effect : Variable) :
    Decidable (causallySufficient dyn s cause effect) :=
  inferInstanceAs (Decidable (_ = true))

/-- `s'` is a consistent supersituation of `base` under dynamics `dyn`.
    (@cite{nadathur-2024} Definition 9b)

    For each inner variable newly determined in `s'` (not in `base`),
    the dynamics from `base` must not entail the opposite value.

    **Approximation**: this is a per-variable check — it verifies each inner
    variable independently against the development of `base`, not the joint
    development of `s'`. This is sound (anything inconsistent per-variable is
    also inconsistent jointly) but conservative: it may admit supersituations
    that become inconsistent only through variable interactions. For the small
    models in @cite{nadathur-lauer-2020} this is adequate. -/
def isConsistentSuper (dyn : CausalDynamics) (base s' : Situation)
    (innerVars : List Variable) : Prop :=
  (innerVars.all fun x =>
    let developed := normalDevelopment dyn base
    match base.get x, s'.get x with
    | none, some true  => !developed.hasValue x false
    | none, some false => !developed.hasValue x true
    | _, _ => true) = true

instance (dyn : CausalDynamics) (base s' : Situation) (innerVars : List Variable) :
    Decidable (isConsistentSuper dyn base s' innerVars) :=
  inferInstanceAs (Decidable (_ = true))

/-- Free-extension list: variables to allow ranging in a supersituation,
    excluding `effect` (the one being tested) and any variable already
    determined in `base`. Shared by `achievable` and `noAlternative`. -/
def freeExtensions (dyn : CausalDynamics) (base : Situation)
    (effect : Variable) : List Variable :=
  (allVariables dyn).filter fun v =>
    v != effect && (base.get v).isNone

namespace causallyNecessary

/-- **Precondition** of @cite{nadathur-2024} Definition 10b: neither
    `cause` nor `effect` is already entailed by `s` under `dyn`. -/
def precondition (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Prop :=
  (normalDevelopment dyn s).hasValue cause true = false ∧
  (normalDevelopment dyn s).hasValue effect true = false

instance (dyn : CausalDynamics) (s : Situation) (cause effect : Variable) :
    Decidable (precondition dyn s cause effect) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **Achievability** clause (i) of @cite{nadathur-2024} Definition 10b:
    some consistent supersituation of `s[cause ↦ true]` (with `effect`
    left undetermined) develops to make `effect` true. -/
def achievable (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Prop :=
  let sCause := s.extend cause true
  ∃ s' ∈ sCause.allExtensions (freeExtensions dyn sCause effect),
    isConsistentSuper dyn sCause s' (innerVariables dyn) ∧
    (normalDevelopment dyn s').hasValue effect true = true

instance (dyn : CausalDynamics) (s : Situation) (cause effect : Variable) :
    Decidable (achievable dyn s cause effect) :=
  List.decidableBEx _ _

/-- **But-for** clause (ii) of @cite{nadathur-2024} Definition 10b: every
    consistent supersituation of `s` (with `effect` left undetermined)
    that achieves `effect` also has `cause` true — i.e., there is no
    `cause`-free path to the effect. -/
def noAlternative (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Prop :=
  ∀ s' ∈ s.allExtensions (freeExtensions dyn s effect),
    isConsistentSuper dyn s s' (innerVariables dyn) →
    (normalDevelopment dyn s').hasValue effect true = true →
    (normalDevelopment dyn s').hasValue cause true = true

instance (dyn : CausalDynamics) (s : Situation) (cause effect : Variable) :
    Decidable (noAlternative dyn s cause effect) :=
  List.decidableBAll _ _

end causallyNecessary

/-- **Causal Necessity** (@cite{nadathur-2024} Definition 10b).

    ⟨cause, true⟩ is causally necessary for ⟨effect, true⟩ relative
    to situation `s` under dynamics `dyn` iff:

    - **Precondition**: `s ⊭_D ⟨cause, true⟩` and `s ⊭_D ⟨effect, true⟩`
    - **(i) Achievability**: `s[cause ↦ true]` has a consistent
      supersituation `s'` with `effect ∉ dom(s')` where `s' ⊨_D ⟨effect, true⟩`
    - **(ii) But-for**: no consistent supersituation `s'` of `s` with
      `effect ∉ dom(s')` satisfies `s' ⊨_D ⟨effect, true⟩` while
      `s' ⊭_D ⟨cause, true⟩`

    This supersedes the simple but-for test from @cite{nadathur-lauer-2020}
    Definition 24. The key improvement: the precondition prevents vacuous
    necessity when cause/effect are already entailed, and achievability
    ensures the effect is reachable before testing but-for. -/
def causallyNecessary (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Prop :=
  causallyNecessary.precondition dyn s cause effect ∧
  causallyNecessary.achievable dyn s cause effect ∧
  causallyNecessary.noAlternative dyn s cause effect

instance (dyn : CausalDynamics) (s : Situation) (cause effect : Variable) :
    Decidable (causallyNecessary dyn s cause effect) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

-- ============================================================
-- § Structural lemmas on `Situation` operations
-- ============================================================

/-- Extending at `w ≠ v` doesn't affect the value of `v`. -/
theorem Situation.extend_get_ne {s : Situation} {v w : Variable} {val : Bool}
    (h : v ≠ w) : (s.extend w val).get v = s.get v := by
  unfold Situation.get Situation.extend
  simp only
  rw [show (v == w) = false from beq_false_of_ne h]; rfl

/-- The empty situation has no determined values. -/
@[simp] theorem Situation.empty_hasValue (v : Variable) (b : Bool) :
    Situation.empty.hasValue v b = false := by
  simp [Situation.hasValue, Situation.empty, Option.none_beq_some]

/-- Variables not in the extension list keep their `none` value through
    `allExtensions`. -/
theorem Situation.allExtensions_preserves_none (s : Situation) (vars : List Variable)
    (v : Variable) (hv : v ∉ vars) (hs : s.get v = none) :
    ∀ s' ∈ s.allExtensions vars, s'.get v = none := by
  induction vars generalizing s with
  | nil =>
    intro s' hs'
    simp [Situation.allExtensions] at hs'
    subst hs'; exact hs
  | cons w ws ih =>
    intro s' hs'
    have hw : v ≠ w := fun h => hv (h ▸ .head _)
    have hws : v ∉ ws := fun h => hv (.tail _ h)
    have hRest : ∀ t ∈ s.allExtensions ws, t.get v = none := ih s hws hs
    change s' ∈ s.allExtensions (w :: ws) at hs'
    simp only [Situation.allExtensions] at hs'
    rw [List.mem_append, List.mem_append] at hs'
    rcases hs' with (hs' | hs') | hs'
    · exact hRest s' hs'
    · have ⟨t, ht, heq⟩ := List.mem_map.mp hs'
      rw [← heq, Situation.extend_get_ne hw]; exact hRest t ht
    · have ⟨t, ht, heq⟩ := List.mem_map.mp hs'
      rw [← heq, Situation.extend_get_ne hw]; exact hRest t ht

/-- Any situation is a consistent supersituation of itself. -/
theorem isConsistentSuper_self (dyn : CausalDynamics) (s : Situation)
    (vars : List Variable) :
    isConsistentSuper dyn s s vars := by
  show (vars.all _) = true
  apply List.all_eq_true.mpr
  intro x _
  simp only [Situation.get]
  cases s.valuation x <;> simp

-- ============================================================
-- § Simple-law necessity
-- ============================================================

/-- Normal development for a single simple law `c → e`: fires once if
    `c` is true, leaves the situation alone otherwise. -/
theorem normalDevelopment_simple (c e : Variable) (s : Situation) :
    normalDevelopment ⟨[CausalLaw.simple c e]⟩ s =
      if s.hasValue c true = true then s.extend e true else s := by
  rcases Bool.eq_false_or_eq_true (s.hasValue c true) with hc | hc
  · rw [if_pos hc]
    have hApp : applyLawsOnce ⟨[CausalLaw.simple c e]⟩ s = s.extend e true := by
      simp only [applyLawsOnce, CausalLaw.simple, List.foldl, CausalLaw.apply,
                 CausalLaw.preconditionsMet, List.all_cons, List.all_nil,
                 Bool.and_true, hc, cond_true]
    have hFix : isFixpoint ⟨[CausalLaw.simple c e]⟩
        (applyLawsOnce ⟨[CausalLaw.simple c e]⟩ s) = true := by
      rw [hApp]
      simp only [isFixpoint, CausalLaw.simple, List.all_cons, List.all_nil,
                 Bool.and_true, CausalLaw.preconditionsMet,
                 Situation.extend_hasValue_same, beq_self_eq_true, Bool.or_true]
    change normalDevelopment _ _ 100 = _
    rw [show (100 : Nat) = 99 + 1 from rfl, normalDevelopment_succ_fix hFix, hApp]
  · rw [if_neg (by rw [hc]; decide)]
    have hFix : isFixpoint ⟨[CausalLaw.simple c e]⟩ s = true := by
      simp only [isFixpoint, CausalLaw.simple, List.all_cons, List.all_nil,
                 Bool.and_true, CausalLaw.preconditionsMet,
                 hc, Bool.not_false, Bool.true_or]
    exact normalDevelopment_of_fixpoint hFix _

private theorem eraseDupsBy_loop_subset {α : Type} [BEq α]
    (eq : α → α → Bool) (l acc : List α) :
    ∀ v ∈ List.eraseDupsBy.loop eq l acc, v ∈ l ∨ v ∈ acc := by
  induction l generalizing acc with
  | nil => intro v h; right; exact List.mem_reverse.mp h
  | cons a as ih =>
    intro v h; unfold List.eraseDupsBy.loop at h; split at h
    · rcases ih acc v h with h' | h'
      · left; exact List.mem_cons_of_mem _ h'
      · right; exact h'
    · rcases ih (a :: acc) v h with h' | h'
      · left; exact List.mem_cons_of_mem _ h'
      · rcases List.mem_cons.mp h' with rfl | h''
        · left; exact .head _
        · right; exact h''

private theorem allVars_mem_simple (c e : Variable) (v : Variable)
    (hv : v ∈ allVariables ⟨[CausalLaw.simple c e]⟩) : v = e ∨ v = c := by
  simp only [allVariables, CausalLaw.simple, List.flatMap, List.map,
             List.eraseDups, List.eraseDupsBy] at hv
  rcases eraseDupsBy_loop_subset _ [e, c] [] v hv with h | h
  · simp [List.mem_cons] at h; exact h
  · simp at h

private theorem innerVars_simple (c e : Variable) :
    innerVariables ⟨[CausalLaw.simple c e]⟩ = [e] := by
  simp only [innerVariables, CausalLaw.simple, List.map, List.eraseDups, List.eraseDupsBy]
  unfold List.eraseDupsBy.loop; simp
  unfold List.eraseDupsBy.loop; simp

private theorem freeExtensions_simple_cause (c e : Variable) :
    freeExtensions ⟨[CausalLaw.simple c e]⟩ (Situation.empty.extend c true) e = [] := by
  rw [freeExtensions, List.filter_eq_nil_iff]
  intro v hv
  rcases allVars_mem_simple c e v hv with rfl | rfl
  · simp
  · simp [Situation.get, Situation.extend, Option.isNone]

private theorem e_not_in_freeExtensions_empty (c e : Variable) :
    e ∉ freeExtensions ⟨[CausalLaw.simple c e]⟩ Situation.empty e := by
  intro h
  rw [freeExtensions, List.mem_filter] at h
  simp at h

/-- For a simple causal law `c → e`, the precondition holds against
    `Situation.empty`: `normalDevelopment(empty) = empty`, which has no
    determined values. -/
private theorem simple_precondition (c e : Variable) :
    causallyNecessary.precondition ⟨[CausalLaw.simple c e]⟩ Situation.empty c e := by
  rw [causallyNecessary.precondition, normalDevelopment_simple]
  simp [Situation.empty_hasValue]

/-- For a simple causal law `c → e`, achievability holds against
    `Situation.empty`: extending with `c = true` fires the law and produces
    `e = true`. -/
private theorem simple_achievable (c e : Variable) :
    causallyNecessary.achievable ⟨[CausalLaw.simple c e]⟩ Situation.empty c e := by
  rw [causallyNecessary.achievable]
  refine ⟨Situation.empty.extend c true, ?_, ?_, ?_⟩
  · rw [freeExtensions_simple_cause]
    simp [Situation.allExtensions]
  · exact isConsistentSuper_self _ _ _
  · rw [normalDevelopment_simple]
    simp [Situation.extend_hasValue_same]

/-- For a simple causal law `c → e`, the but-for clause holds against
    `Situation.empty`: every supersituation that achieves `e = true` must
    have `c = true` (because the only way to fire the law is via `c`). -/
private theorem simple_noAlternative (c e : Variable) :
    causallyNecessary.noAlternative ⟨[CausalLaw.simple c e]⟩ Situation.empty c e := by
  rw [causallyNecessary.noAlternative]
  intro s' hs' _ hE
  -- s' is in allExtensions of empty over [c], so s'.get e = none
  have hGetE : s'.get e = none :=
    Situation.allExtensions_preserves_none Situation.empty _ e
      (e_not_in_freeExtensions_empty c e)
      (by simp [Situation.get, Situation.empty]) s' hs'
  -- Case-split on whether s'.hasValue c true
  -- Note: `Bool.eq_false_or_eq_true` yields `_ = true ∨ _ = false` (true first)
  rcases Bool.eq_false_or_eq_true (s'.hasValue c true) with hc | hc
  · -- c is true in s' → normalDev preserves it → goal holds
    rw [normalDevelopment_simple, if_pos hc]
    by_cases hce : c = e
    · subst hce; exact Situation.extend_hasValue_same
    · rw [Situation.extend_hasValue_diff hce]; exact hc
  · -- c is false in s' → law doesn't fire → normalDev s' = s' → e = none, contradicting hE
    rw [normalDevelopment_simple, if_neg (by rw [hc]; decide)] at hE
    have : s'.hasValue e true = false := by
      simp only [Situation.hasValue]; rw [show s'.valuation e = s'.get e from rfl, hGetE]; rfl
    rw [this] at hE; exact absurd hE (by decide)

/-- For a simple causal law `c → e`, the cause is necessary for the effect
    relative to the empty background under @cite{nadathur-2024} Definition 10b.

    The argument:
    1. **Precondition**: `normalDevelopment(empty)` = empty, so neither cause
       nor effect is entailed
    2. **Achievability**: extending with `c=true` fires the law → `e=true`
    3. **But-for**: every consistent supersituation of empty either has
       `c=true` (preserves cause) or has `c≠true` (law doesn't fire,
       `e` stays undetermined) -/
theorem simple_law_necessity (c e : Variable) :
    causallyNecessary ⟨[CausalLaw.simple c e]⟩ Situation.empty c e :=
  ⟨simple_precondition c e, simple_achievable c e, simple_noAlternative c e⟩

end Core.Causal
