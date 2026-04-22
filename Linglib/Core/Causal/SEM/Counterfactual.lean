import Linglib.Core.Causal.SEM.Monotonicity

/-!
# Structural Equation Model: Queries, Intervention, and Counterfactuals
@cite{nadathur-lauer-2020} @cite{nadathur-2024} @cite{schulz-2011}

Pearl's `do`-operator and the counterfactual queries built from it.

- `developsToBe` / `developsToTrue` / `factuallyDeveloped` — convenience
  predicates on the result of `normalDevelopment`
- `hasDirectLaw` / `hasIndependentSource` — structural graph queries
- `intervene` / `manipulates` — Pearl's `do(X = val)` and the
  interventionist criterion for causation
- `causallySufficient` (@cite{nadathur-lauer-2020} Def 23)
- `isConsistentSuper` (@cite{nadathur-2024} Def 9b) — per-variable
  consistency of supersituations
- `causallyNecessary` (@cite{nadathur-2024} Def 10b) — but-for with
  precondition + achievability
- `simple_law_necessity` — structured proof that `c → e` makes `c`
  necessary for `e` against the empty background

All queries are well-defined for ANY dynamics — including those with
negative preconditions like `COM := MSG ∧ ¬BRK` (Schulz/Nadathur's
"potential obstacle" pattern). Termination of `normalDevelopment`
holds uniformly via the info-monotone state-space measure
(`Monotonicity.lean`); no positivity restriction.

All counterfactual queries are `Prop`-valued with `Decidable` instances
auto-derived.
-/

namespace Core.Causal

-- ════════════════════════════════════════════════════
-- § Convenience Predicates
-- ════════════════════════════════════════════════════

/-- A variable develops to a specific value. -/
def developsToBe (dyn : CausalDynamics) (s : Situation)
    (v : Variable) (val : Bool) : Prop :=
  (normalDevelopment dyn s).hasValue v val

instance (dyn : CausalDynamics) (s : Situation) (v : Variable) (val : Bool) :
    Decidable (developsToBe dyn s v val) :=
  inferInstanceAs (Decidable (Situation.hasValue ..))

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
  s.hasValue cause true ∧ (normalDevelopment dyn s).hasValue effect true

instance (dyn : CausalDynamics) (s : Situation) (cause effect : Variable) :
    Decidable (factuallyDeveloped dyn s cause effect) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- ════════════════════════════════════════════════════
-- § Structural Graph Queries
-- ════════════════════════════════════════════════════

/-- Some causal law directly connects `cause` to `effect`. -/
def hasDirectLaw (dyn : CausalDynamics) (cause effect : Variable) : Prop :=
  ∃ law ∈ dyn.laws, (∃ p ∈ law.preconditions, p.1 = cause) ∧ law.effect = effect

instance (dyn : CausalDynamics) (cause effect : Variable) :
    Decidable (hasDirectLaw dyn cause effect) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The intermediate has a causal law not depending on `cause`. -/
def hasIndependentSource (dyn : CausalDynamics)
    (cause intermediate : Variable) : Prop :=
  ∃ law ∈ dyn.laws, law.effect = intermediate ∧
    ¬ ∃ p ∈ law.preconditions, p.1 = cause

instance (dyn : CausalDynamics) (cause intermediate : Variable) :
    Decidable (hasIndependentSource dyn cause intermediate) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

-- ════════════════════════════════════════════════════
-- § Intervention (Pearl's do-operator)
-- ════════════════════════════════════════════════════

/-- **Intervene**: Pearl's do(X = val).

    Sets variable `target` to `val` and removes all laws that would
    determine `target`, so the intervention overrides the structural
    equations rather than being blocked by them. -/
def intervene (dyn : CausalDynamics) (s : Situation)
    (target : Variable) (val : Bool) : CausalDynamics × Situation :=
  let dyn' : CausalDynamics := ⟨dyn.laws.filter (·.effect != target)⟩
  let s' := s.extend target val
  (dyn', s')

/-- **Manipulates**: intervening on `cause` changes the value of `effect`.

    Compares normal development under do(cause = true) vs do(cause = false).
    If the effect's value differs, then `cause` manipulates `effect`.

    This is the interventionist criterion for causation. -/
def manipulates (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Prop :=
  (normalDevelopment (intervene dyn s cause true).1
      (intervene dyn s cause true).2).get effect ≠
  (normalDevelopment (intervene dyn s cause false).1
      (intervene dyn s cause false).2).get effect

instance (dyn : CausalDynamics) (s : Situation) (cause effect : Variable) :
    Decidable (manipulates dyn s cause effect) :=
  inferInstanceAs (Decidable (_ ≠ _))

-- ════════════════════════════════════════════════════
-- § Counterfactual Queries (@cite{nadathur-lauer-2020} Definitions 23-24)
-- ════════════════════════════════════════════════════

/-- **Causal Sufficiency** (@cite{nadathur-lauer-2020}, Definition 23).
    C is causally sufficient for E in situation s iff adding C and
    developing normally produces E. -/
def causallySufficient (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Prop :=
  (normalDevelopment dyn (s.extend cause true)).hasValue effect true

instance (dyn : CausalDynamics) (s : Situation) (cause effect : Variable) :
    Decidable (causallySufficient dyn s cause effect) :=
  inferInstanceAs (Decidable (Situation.hasValue ..))

/-- `s'` is a consistent supersituation of `base` under dynamics `dyn`.
    (@cite{nadathur-2024} Definition 9b)

    For each inner variable newly determined in `s'` (not in `base`),
    the dynamics from `base` must not entail the opposite value.

    **Approximation**: per-variable check — verifies each inner variable
    independently against the development of `base`, not the joint
    development of `s'`. -/
def isConsistentSuper (dyn : CausalDynamics) (base s' : Situation)
    (innerVars : List Variable) : Prop :=
  ∀ x ∈ innerVars,
    (base.get x = none → s'.get x = some true →
      ¬ (normalDevelopment dyn base).hasValue x false) ∧
    (base.get x = none → s'.get x = some false →
      ¬ (normalDevelopment dyn base).hasValue x true)

instance (dyn : CausalDynamics) (base s' : Situation) (innerVars : List Variable) :
    Decidable (isConsistentSuper dyn base s' innerVars) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

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
  ¬ (normalDevelopment dyn s).hasValue cause true ∧
  ¬ (normalDevelopment dyn s).hasValue effect true

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
    (normalDevelopment dyn s').hasValue effect true

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
    (normalDevelopment dyn s').hasValue effect true →
    (normalDevelopment dyn s').hasValue cause true

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
    Definition 24. -/
def causallyNecessary (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Prop :=
  causallyNecessary.precondition dyn s cause effect ∧
  causallyNecessary.achievable dyn s cause effect ∧
  causallyNecessary.noAlternative dyn s cause effect

instance (dyn : CausalDynamics) (s : Situation) (cause effect : Variable) :
    Decidable (causallyNecessary dyn s cause effect) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

-- ════════════════════════════════════════════════════
-- § Structural lemmas on `Situation` operations
-- ════════════════════════════════════════════════════

/-- The empty situation has no determined values. -/
@[simp] theorem Situation.empty_hasValue (v : Variable) (b : Bool) :
    ¬ Situation.empty.hasValue v b := by
  simp [Situation.hasValue, Situation.empty]

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
theorem isConsistentSuper_self (dyn : CausalDynamics)
    (s : Situation) (vars : List Variable) :
    isConsistentSuper dyn s s vars := by
  intro x _
  refine ⟨?_, ?_⟩
  · intro hBase hS'; rw [show s.get x = s.valuation x from rfl] at hBase hS'
    rw [hBase] at hS'; cases hS'
  · intro hBase hS'; rw [show s.get x = s.valuation x from rfl] at hBase hS'
    rw [hBase] at hS'; cases hS'

-- ════════════════════════════════════════════════════
-- § Simple-law necessity
-- ════════════════════════════════════════════════════

/-- Normal development for a single simple law `c → e`: fires once if
    `c` is true and `e` is undetermined; otherwise no-op. -/
theorem normalDevelopment_simple (c e : Variable) (s : Situation) :
    normalDevelopment ⟨[CausalLaw.simple c e]⟩ s =
      if s.hasValue c true ∧ s.get e = none then s.extend e true else s := by
  by_cases hcase : s.hasValue c true ∧ s.get e = none
  · obtain ⟨hc, hge⟩ := hcase
    have hMet : (CausalLaw.simple c e).preconditionsMet s := by
      intro p hp
      simp only [CausalLaw.simple, List.mem_singleton] at hp
      rw [hp]; exact hc
    have hApp : applyLawsOnce ⟨[CausalLaw.simple c e]⟩ s = s.extend e true := by
      show (CausalLaw.simple c e).apply s = s.extend e true
      exact CausalLaw.apply_of_met_undetermined hMet hge
    have hFixApp : isFixpoint ⟨[CausalLaw.simple c e]⟩ (s.extend e true) := by
      intro law hLaw _
      simp only [List.mem_singleton] at hLaw
      rw [hLaw]
      change (s.extend e true).get e ≠ none
      rw [Situation.extend_get_same]; simp
    have hSNotFix : ¬ isFixpoint ⟨[CausalLaw.simple c e]⟩ s := by
      intro hFix
      exact hFix (CausalLaw.simple c e) (List.mem_singleton.mpr rfl) hMet hge
    rw [normalDevelopment_of_not_fixpoint hSNotFix, hApp,
        normalDevelopment_of_fixpoint hFixApp]
    rw [if_pos ⟨hc, hge⟩]
  · -- Not (hasValue c true ∧ get e = none) → fixpoint at s
    have hFix : isFixpoint ⟨[CausalLaw.simple c e]⟩ s := by
      intro law hLaw hMet hNone
      simp only [List.mem_singleton] at hLaw
      rw [hLaw] at hMet hNone
      apply hcase
      refine ⟨?_, hNone⟩
      have := hMet (c, true) (by simp [CausalLaw.simple])
      exact this
    rw [normalDevelopment_of_fixpoint hFix, if_neg hcase]

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

private theorem freeExtensions_simple_cause (c e : Variable) :
    freeExtensions ⟨[CausalLaw.simple c e]⟩ (Situation.empty.extend c true) e = [] := by
  rw [freeExtensions, List.filter_eq_nil_iff]
  intro v hv
  rcases allVars_mem_simple c e v hv with rfl | rfl
  · simp
  · simp [Situation.get, Situation.extend, Option.isNone]

-- ════════════════════════════════════════════════════
-- § Closed forms for `disjunctive` / `conjunctive` / `chain`
-- ════════════════════════════════════════════════════

/-! Sibling lemmas to `normalDevelopment_simple` for the standard
    multi-law shapes. Each gives the fixpoint that `normalDevelopment`
    converges to under specific background assumptions, avoiding the
    foldl-step-by-step reasoning at the call site. -/

/-- For the disjunctive dynamics `[a→c, b→c]`, if `a` is true and `c` is
    undetermined, `c` becomes true via the first law. -/
theorem normalDevelopment_disjunctive_left {a b c : Variable} (hac : a ≠ c)
    (s : Situation) (ha : s.hasValue a true) (hc : s.get c = none) :
    (normalDevelopment (CausalDynamics.disjunctiveCausation a b c) s).hasValue c true := by
  -- Step 1: simple a c fires (a=true, c=none) → c becomes true
  have hMet1 : (CausalLaw.simple a c).preconditionsMet s := by
    intro p hp; simp only [CausalLaw.simple, List.mem_singleton] at hp
    rw [hp]; exact ha
  have hStep1 : (CausalLaw.simple a c).apply s = s.extend c true :=
    CausalLaw.apply_of_met_undetermined hMet1 hc
  -- Step 2: simple b c sees c determined → no-op
  have hStep2 : (CausalLaw.simple b c).apply (s.extend c true) = s.extend c true := by
    apply CausalLaw.apply_of_determined
    exact Situation.extend_get_same _ _ _
  have hApp : applyLawsOnce (CausalDynamics.disjunctiveCausation a b c) s
              = s.extend c true := by
    show ([CausalLaw.simple a c, CausalLaw.simple b c].foldl _ s) = _
    simp only [List.foldl_cons, List.foldl_nil]; rw [hStep1, hStep2]
  -- The result is a fixpoint (both laws have effect c, c is determined)
  have hFix : isFixpoint (CausalDynamics.disjunctiveCausation a b c) (s.extend c true) := by
    intro law hLaw _ hNone
    have hEffectC : law.effect = c := by
      simp only [CausalDynamics.disjunctiveCausation, List.mem_cons,
                 List.not_mem_nil, or_false] at hLaw
      rcases hLaw with hL | hL <;> (subst hL; rfl)
    rw [hEffectC, Situation.extend_get_same] at hNone; cases hNone
  rw [normalDevelopment_eq_applyLawsOnce_of_fixpoint _ _ (hApp ▸ hFix), hApp]
  show (s.extend c true).hasValue c true
  rw [Situation.extend_hasValue_same]

/-- For the disjunctive dynamics `[a→c, b→c]`, if `b` is true and `c` is
    undetermined, `c` becomes true (via the second law if the first
    doesn't fire, or via the first if it happens to). -/
theorem normalDevelopment_disjunctive_right {a b c : Variable}
    (hac : a ≠ c) (hbc : b ≠ c)
    (s : Situation) (hb : s.hasValue b true) (hc : s.get c = none) :
    (normalDevelopment (CausalDynamics.disjunctiveCausation a b c) s).hasValue c true := by
  -- Two cases on whether the first law (a→c) fires
  by_cases hMet1 : (CausalLaw.simple a c).preconditionsMet s
  · -- a=true: first law fires, sets c=true; second law no-ops
    have hStep1 : (CausalLaw.simple a c).apply s = s.extend c true :=
      CausalLaw.apply_of_met_undetermined hMet1 hc
    have hStep2 : (CausalLaw.simple b c).apply (s.extend c true) = s.extend c true := by
      apply CausalLaw.apply_of_determined; exact Situation.extend_get_same _ _ _
    have hApp : applyLawsOnce (CausalDynamics.disjunctiveCausation a b c) s
                = s.extend c true := by
      show ([CausalLaw.simple a c, CausalLaw.simple b c].foldl _ s) = _
      simp only [List.foldl_cons, List.foldl_nil]; rw [hStep1, hStep2]
    have hFix : isFixpoint (CausalDynamics.disjunctiveCausation a b c) (s.extend c true) := by
      intro law hLaw _ hNone
      have hEffectC : law.effect = c := by
        simp only [CausalDynamics.disjunctiveCausation, List.mem_cons,
                   List.not_mem_nil, or_false] at hLaw
        rcases hLaw with hL | hL <;> (subst hL; rfl)
      rw [hEffectC, Situation.extend_get_same] at hNone; cases hNone
    rw [normalDevelopment_eq_applyLawsOnce_of_fixpoint _ _ (hApp ▸ hFix), hApp]
    show (s.extend c true).hasValue c true
    rw [Situation.extend_hasValue_same]
  · -- ¬a=true: first law no-ops; second law fires (b=true, c=none)
    have hStep1 : (CausalLaw.simple a c).apply s = s := CausalLaw.apply_of_not_met hMet1
    have hMet2 : (CausalLaw.simple b c).preconditionsMet s := by
      intro p hp; simp only [CausalLaw.simple, List.mem_singleton] at hp
      rw [hp]; exact hb
    have hStep2 : (CausalLaw.simple b c).apply s = s.extend c true :=
      CausalLaw.apply_of_met_undetermined hMet2 hc
    have hApp : applyLawsOnce (CausalDynamics.disjunctiveCausation a b c) s
                = s.extend c true := by
      show ([CausalLaw.simple a c, CausalLaw.simple b c].foldl _ s) = _
      simp only [List.foldl_cons, List.foldl_nil]; rw [hStep1, hStep2]
    have hFix : isFixpoint (CausalDynamics.disjunctiveCausation a b c) (s.extend c true) := by
      intro law hLaw _ hNone
      have hEffectC : law.effect = c := by
        simp only [CausalDynamics.disjunctiveCausation, List.mem_cons,
                   List.not_mem_nil, or_false] at hLaw
        rcases hLaw with hL | hL <;> (subst hL; rfl)
      rw [hEffectC, Situation.extend_get_same] at hNone; cases hNone
    rw [normalDevelopment_eq_applyLawsOnce_of_fixpoint _ _ (hApp ▸ hFix), hApp]
    show (s.extend c true).hasValue c true
    rw [Situation.extend_hasValue_same]

/-- For the conjunctive dynamics `[a∧b→c]`, if `a` is undetermined,
    no law can fire and `s` is a fixpoint. -/
theorem normalDevelopment_conjunctive_blocked {a b c : Variable}
    (s : Situation) (ha : s.get a = none) :
    normalDevelopment (CausalDynamics.conjunctiveCausation a b c) s = s := by
  apply normalDevelopment_of_fixpoint
  intro law hLaw hMet _
  have hL : law = CausalLaw.conjunctive a b c := by
    simp only [CausalDynamics.conjunctiveCausation, List.mem_cons,
               List.not_mem_nil, or_false] at hLaw
    exact hLaw
  rw [hL] at hMet
  -- hMet (a, true) requires s.hasValue a true, but s.get a = none
  have hMetA := hMet (a, true) (by simp [CausalLaw.conjunctive])
  unfold Situation.hasValue at hMetA
  rw [show s.valuation a = s.get a from rfl, ha] at hMetA
  cases hMetA

private theorem e_not_in_freeExtensions_empty (c e : Variable) :
    e ∉ freeExtensions ⟨[CausalLaw.simple c e]⟩ Situation.empty e := by
  intro h
  rw [freeExtensions, List.mem_filter] at h
  simp at h

/-- For a simple causal law `c → e`, the precondition holds against
    `Situation.empty`: `normalDevelopment(empty) = empty`. -/
private theorem simple_precondition (c e : Variable) :
    causallyNecessary.precondition ⟨[CausalLaw.simple c e]⟩ Situation.empty c e := by
  unfold causallyNecessary.precondition
  rw [normalDevelopment_simple]
  have hCond : ¬ (Situation.empty.hasValue c true ∧ Situation.empty.get e = none) :=
    fun ⟨hc, _⟩ => Situation.empty_hasValue c true hc
  rw [if_neg hCond]
  exact ⟨Situation.empty_hasValue c true, Situation.empty_hasValue e true⟩

/-- For a simple causal law `c → e`, achievability holds against
    `Situation.empty`. -/
private theorem simple_achievable (c e : Variable) :
    causallyNecessary.achievable ⟨[CausalLaw.simple c e]⟩ Situation.empty c e := by
  unfold causallyNecessary.achievable
  refine ⟨Situation.empty.extend c true, ?_, ?_, ?_⟩
  · rw [freeExtensions_simple_cause]; simp [Situation.allExtensions]
  · exact isConsistentSuper_self _ _ _
  · rw [normalDevelopment_simple]
    by_cases hce : c = e
    · subst hce
      -- c = e: extending makes c determined; condition `c=true ∧ get c = none` fails
      have h1 : (Situation.empty.extend c true).hasValue c true := by
        unfold Situation.hasValue Situation.extend; simp
      have h2 : (Situation.empty.extend c true).get c = some true := by
        rw [Situation.extend_get_same]
      rw [if_neg (by intro ⟨_, hne⟩; rw [h2] at hne; cases hne)]
      exact h1
    · have h1 : (Situation.empty.extend c true).hasValue c true := by
        unfold Situation.hasValue Situation.extend; simp
      have h2 : (Situation.empty.extend c true).get e = none := by
        rw [Situation.extend_get_ne (Ne.symm hce)]; rfl
      rw [if_pos ⟨h1, h2⟩]
      unfold Situation.hasValue Situation.extend; simp

/-- For a simple causal law `c → e`, the but-for clause holds against
    `Situation.empty`. -/
private theorem simple_noAlternative (c e : Variable) :
    causallyNecessary.noAlternative ⟨[CausalLaw.simple c e]⟩ Situation.empty c e := by
  unfold causallyNecessary.noAlternative
  intro s' hs' _ hE
  have hGetE : s'.get e = none :=
    Situation.allExtensions_preserves_none Situation.empty _ e
      (e_not_in_freeExtensions_empty c e)
      (by simp [Situation.get, Situation.empty]) s' hs'
  by_cases hc : s'.hasValue c true
  · -- c true in s' → preserved through normalDevelopment
    rw [normalDevelopment_simple]
    rw [if_pos ⟨hc, hGetE⟩]
    by_cases hce : c = e
    · subst hce
      -- c = e contradicts hGetE
      unfold Situation.hasValue at hc
      rw [show s'.valuation c = s'.get c from rfl, hGetE] at hc
      cases hc
    · rw [Situation.extend_hasValue_diff hce]; exact hc
  · -- c not true in s' → law doesn't fire → e stays none → contradicts hE
    have hE' := hE
    rw [normalDevelopment_simple] at hE'
    rw [if_neg (fun ⟨h, _⟩ => hc h)] at hE'
    have : ¬ s'.hasValue e true := by
      unfold Situation.hasValue
      rw [show s'.valuation e = s'.get e from rfl, hGetE]
      intro h; cases h
    exact absurd hE' this

/-- For a simple causal law `c → e`, the cause is necessary for the effect
    relative to the empty background under @cite{nadathur-2024} Definition 10b. -/
theorem simple_law_necessity (c e : Variable) :
    causallyNecessary ⟨[CausalLaw.simple c e]⟩ Situation.empty c e :=
  ⟨simple_precondition c e, simple_achievable c e, simple_noAlternative c e⟩

-- ════════════════════════════════════════════════════
-- § Def 12a/b — situation-based necessity & sufficiency
-- § Def 13   — actual cause
-- ════════════════════════════════════════════════════

/-! `causallySufficient`/`causallyNecessary` above are @cite{nadathur-2024}
    Definitions 10a/b — necessity and sufficiency of **facts** ⟨X, x⟩.

    The complementary notions are Definitions 12a/b — necessity and
    sufficiency of **situations** s. Where Def 10b asks "is fact ⟨c, true⟩
    necessary for fact ⟨e, true⟩?", Def 12b asks "is the whole situation s
    necessary for fact ⟨e, true⟩?" — i.e., is s's specific configuration of
    causal ancestors essential, or could a perturbation still produce e?

    Def 12b is the right notion for scenarios like
    @cite{bar-asher-siegal-2026}'s door — "did handle-turning (as a
    situation with handle=1, lock=0) cause the door to open?" — where
    the question is about the whole multi-variable situation, not a
    single fact. -/

/-- **Causal sufficiency of a situation** (@cite{nadathur-2024} Def 12a).
    `s ▷_D ⟨X, x⟩` iff `s ⊨_D ⟨X, x⟩` — definitionally `developsToBe`. -/
abbrev situationallySufficient (dyn : CausalDynamics) (s : Situation)
    (X : Variable) (x : Bool) : Prop :=
  developsToBe dyn s X x

/-- **Causal necessity of a situation** (@cite{nadathur-2024} Def 12b).

    `s ◁_D ⟨X, x⟩` iff for any situation `s'` with:
    - (i) `dom(s) ∩ Anc(X) ⊆ dom(s') ∩ Anc(X)` — s' covers s on ancestors
    - (ii) `∃Y ∈ dom(s) ∩ Anc(X) with s(Y) ≠ s'(Y)` — s' disagrees on some ancestor
    - (iii) `s'(X) ≠ x` — s' doesn't directly fix X to x

    we have `s' ⊭_D ⟨X, x⟩` — s' fails to causally entail the fact.

    Intuitively: every causally-consistent way of bringing about ⟨X, x⟩
    that perturbs s's ancestor commitments must fail. -/
def situationallyNecessary (dyn : CausalDynamics) (s : Situation)
    (X : Variable) (x : Bool) : Prop :=
  let anc := causalAncestors dyn X
  ∀ s' : Situation,
    (∀ Y ∈ anc, s.get Y ≠ none → s'.get Y ≠ none) →
    (∃ Y ∈ anc, s.get Y ≠ none ∧ s.get Y ≠ s'.get Y) →
    s'.get X ≠ some x →
    ¬ (normalDevelopment dyn s').hasValue X x

/-- **Actual cause** (@cite{nadathur-2024} Def 13). Given a dynamics, a
    world `w`, and an inner variable `X`: situation `s` actually causes
    `⟨X, x⟩` iff `s(X) = u` (s doesn't fix X), `w(X) = x` (the world has
    the fact), and `w` is a supersituation of `s` over the relevant
    variable set `vars` (typically `allVariables dyn`).

    The `vars` parameter bounds the supersituation check to a finite set;
    for variables outside the dynamics' scope the question is vacuous.

    Footnote 10 of @cite{nadathur-2024} flags this as "puzzlingly weak" —
    it doesn't require s to be causally relevant to X — but the catalyst
    proposal of @cite{baglini-francez-2016} only consumes it for situations
    `s_F` that are independently established to be causally relevant. -/
def actuallyCauses (dyn : CausalDynamics) (s : Situation) (w : Situation)
    (vars : List Variable) (X : Variable) (x : Bool) : Prop :=
  s.get X = none ∧
  w.hasValue X x ∧
  ∀ Y ∈ vars, s.get Y ≠ none → s.get Y = w.get Y

instance (dyn : CausalDynamics) (s w : Situation) (vars : List Variable)
    (X : Variable) (x : Bool) :
    Decidable (actuallyCauses dyn s w vars X x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

-- ════════════════════════════════════════════════════
-- § Bridge: Def 10b (facts) ↔ Def 12b (situations)
-- ════════════════════════════════════════════════════

/-! Def 10b is fact-based: "is the *fact* ⟨c, true⟩ necessary for ⟨e, true⟩?"
    Def 12b is situation-based: "is the *situation* s necessary for ⟨e, true⟩?"

    The two notions are related but neither implies the other in general:
    - **10b ⇏ 12b**: on multi-pathway dynamics, even if a fact is the
      only "but-for" cause when extended with itself, the *situation*
      `empty.extend c true` may not be 12b-necessary because alternative
      pathways achieve the effect without it. The Bar-Asher Siegal door
      scenario (`BarAsherSiegal2026.handleSituation_not_situationally_necessary_full`)
      exhibits this.
    - **12b ⇏ 10b**: situation-based necessity quantifies over more
      alternatives than fact-based necessity, so a situation can be
      necessary in 12b's stronger sense while a single fact within it
      isn't 10b-necessary in isolation.

    On **single-pathway** dynamics (one law per inner variable), the
    two notions align — the singleton situation `{cause = true}` is
    12b-necessary iff the fact `⟨cause, true⟩` is 10b-necessary. -/

/-- On single-pathway dynamics, situation-based necessity (12b) of the
    singleton situation `{cause = true}` for the effect.

    The structural proof sidesteps reasoning about `causalAncestors`
    explicitly: condition (ii)'s witness must be in
    `dom(empty.extend c true) = {c}` (regardless of the ancestor list),
    so we extract `Y = c` from the situation's structure alone. With
    `s'.get c ≠ some true`, the simple law doesn't fire in
    `normalDevelopment`, so `e` stays undetermined; combined with
    condition (iii) we conclude. -/
theorem causallyNecessary_imp_situationallyNecessary_simple
    (c e : Variable) (hce : c ≠ e) :
    situationallyNecessary ⟨[CausalLaw.simple c e]⟩
      (Situation.empty.extend c true) e true := by
  intro s' _hCov hDis hNotE
  -- (ii) gives a witness Y in dom(empty.extend c true) ∩ Anc(e); the only
  -- variable in dom(empty.extend c true) is c (regardless of Anc).
  obtain ⟨Y, _hYAnc, hYSome, hYDis⟩ := hDis
  have hYc : Y = c := by
    by_contra hne
    apply hYSome
    rw [Situation.extend_get_ne hne]; rfl
  rw [hYc] at hYDis
  -- (empty.extend c true).get c = some true; combined with hYDis, s'.get c ≠ some true
  have hSomeC : (Situation.empty.extend c true).get c = some true :=
    Situation.extend_get_same _ _ _
  rw [hSomeC] at hYDis
  -- Use normalDevelopment_simple closed form
  rw [normalDevelopment_simple]
  have hNotCtrue : ¬ s'.hasValue c true := fun h => hYDis (by
    unfold Situation.hasValue at h
    rw [show s'.valuation c = s'.get c from rfl] at h
    exact h.symm)
  rw [if_neg (fun ⟨h, _⟩ => hNotCtrue h)]
  -- Goal: ¬ s'.hasValue e true; follows from hNotE
  intro h
  apply hNotE
  unfold Situation.hasValue at h
  rw [show s'.valuation e = s'.get e from rfl] at h
  exact h

-- ════════════════════════════════════════════════════
-- § Schema: CausalAccessibility (counterfactual access relations)
-- ════════════════════════════════════════════════════

/-! There is no single canonical "causal necessity" — Lewis 1973's
    counterfactual analysis, @cite{nadathur-2024}'s Def 10b but-for clause,
    @cite{halpern-pearl-2005}'s contingency-witness account, and
    @cite{beckers-vennekens-2018}'s production/dependence split all
    propose inequivalent notions. This schema makes the variation
    explicit: a `CausalAccessibility` packages a set of accessible
    alternatives `(dyn', s')` plus a consistency filter, and a single
    `.necessary` operator computes whichever notion of necessity that
    accessibility relation encodes.

    The construction parallels modal logic's "frame → necessity" pattern:
    different accessibility relations yield different ◻-operators.
    Bridge theorems witness that classical formulations
    (`causallyNecessary.noAlternative`, `lewisButFor`) are instances. -/

/-- A counterfactual accessibility relation: which `(dyn', s')`
    alternatives the necessity claim is evaluated against, plus a
    consistency filter selecting which ones count.

    Different instances correspond to different theoretical notions
    of causal necessity (Lewis, Nadathur 10b, Halpern-Pearl, ...).
    They all share the same `.necessary` operator: in every accessible
    alternative where the cause fails to develop, the effect must also
    fail to develop. -/
structure CausalAccessibility where
  /-- The accessible alternative `(dyn', s')` worlds for evaluating a
      necessity claim about `cause` for `effect` at `(dyn, s)`. -/
  access : CausalDynamics → Situation → (cause effect : Variable) →
           List (CausalDynamics × Situation)
  /-- Filter selecting which alternatives count toward the necessity claim. -/
  consistent : CausalDynamics → Situation → CausalDynamics → Situation → Prop
  /-- Decidability of the consistency filter (required for `Decidable`
      instances on `.necessary`). -/
  consistentDecidable : ∀ dyn s dyn' s', Decidable (consistent dyn s dyn' s')

/-- **Necessity under accessibility relation `acc`**.

    In every alternative `(dyn', s') ∈ acc.access dyn s cause effect`
    selected by `acc.consistent`, if `cause` does not develop to `true`
    then `effect` does not develop to `true` either.

    Equivalently (contrapositive on the inner implication):
    every accessible-and-consistent alternative achieving the effect
    also achieves the cause. -/
def CausalAccessibility.necessary (acc : CausalAccessibility)
    (dyn : CausalDynamics) (s : Situation) (cause effect : Variable) : Prop :=
  ∀ alt ∈ acc.access dyn s cause effect,
    acc.consistent dyn s alt.1 alt.2 →
    ¬ (normalDevelopment alt.1 alt.2).hasValue cause true →
    ¬ (normalDevelopment alt.1 alt.2).hasValue effect true

instance (acc : CausalAccessibility) (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) :
    Decidable (acc.necessary dyn s cause effect) := by
  unfold CausalAccessibility.necessary
  haveI : ∀ alt : CausalDynamics × Situation,
      Decidable (acc.consistent dyn s alt.1 alt.2) :=
    fun alt => acc.consistentDecidable dyn s alt.1 alt.2
  exact List.decidableBAll _ _

/-- **Lewis 1973 counterfactual accessibility**.

    The unique alternative is `do(cause := false)` — Pearl's intervention
    that fixes the cause to `false` and removes its structural laws.
    All such alternatives count (trivial consistency).

    Under this accessibility, `.necessary` says: when we counterfactually
    set the cause to `false`, the effect fails to develop. -/
def CausalAccessibility.lewis : CausalAccessibility where
  access dyn s cause _effect := [intervene dyn s cause false]
  consistent _ _ _ _ := True
  consistentDecidable _ _ _ _ := inferInstance

/-- **Nadathur 2024 Def 10b accessibility** (but-for clause).

    Alternatives are free extensions of `s` over variables other than
    `effect`, with the original dynamics unchanged. Consistency is
    @cite{nadathur-2024}'s per-variable `isConsistentSuper` filter. -/
def CausalAccessibility.nadathur10b : CausalAccessibility where
  access dyn s _cause effect :=
    (s.allExtensions (freeExtensions dyn s effect)).map (fun s' => (dyn, s'))
  consistent dyn s _dyn' s' := isConsistentSuper dyn s s' (innerVariables dyn)
  consistentDecidable _ _ _ _ := inferInstance

/-- **Bridge: Def 10b but-for ↔ schema instance**.

    The classical `causallyNecessary.noAlternative` clause is exactly the
    `.necessary` operator for the `nadathur10b` accessibility relation. -/
theorem nadathur10b_necessary_iff_noAlternative
    (dyn : CausalDynamics) (s : Situation) (cause effect : Variable) :
    CausalAccessibility.nadathur10b.necessary dyn s cause effect ↔
    causallyNecessary.noAlternative dyn s cause effect := by
  unfold CausalAccessibility.necessary CausalAccessibility.nadathur10b
         causallyNecessary.noAlternative
  constructor
  · intro h s' hs' hCons hEff
    by_contra hNotC
    exact h (dyn, s') (List.mem_map.mpr ⟨s', hs', rfl⟩) hCons hNotC hEff
  · intro h alt hAlt hCons hNotC hEff
    obtain ⟨s', hs', heq⟩ := List.mem_map.mp hAlt
    rw [← heq] at hCons hNotC hEff
    exact hNotC (h s' hs' hCons hEff)

/-- After `intervene dyn s cause false`, the cause does not develop to `true`.

    Pearl's intervention sets `cause := false` in the situation and removes
    structural laws targeting `cause`. The intervened situation has
    `cause = false` (a determined value), and `normalDevelopment` preserves
    determined values (`normalDevelopment_preserves_hasValue`). So the cause
    stays `false` and cannot develop to `true`. -/
theorem intervene_cause_not_developed_to_true
    (dyn : CausalDynamics) (s : Situation) (cause : Variable) :
    let alt := intervene dyn s cause false
    ¬ (normalDevelopment alt.1 alt.2).hasValue cause true := by
  intro alt hT
  have hF : alt.2.hasValue cause false := by
    show (s.extend cause false).hasValue cause false
    exact Situation.extend_hasValue_same.mpr rfl
  have hFND : (normalDevelopment alt.1 alt.2).hasValue cause false :=
    normalDevelopment_preserves_hasValue _ _ _ _ hF
  -- valuation cause = some false ∧ valuation cause = some true → false
  unfold Situation.hasValue at hT hFND
  rw [hFND] at hT
  cases hT

/-- **Bridge: Lewis 1973 but-for ↔ schema instance**.

    Under the `lewis` accessibility, `.necessary` reduces to the classical
    Lewis but-for test: when we counterfactually intervene to set the cause
    to `false`, the effect fails to develop. The schema's
    `¬ cause-develops` hypothesis is automatically satisfied by
    `intervene_cause_not_developed_to_true`. -/
theorem lewis_necessary_iff_intervene_not_developed
    (dyn : CausalDynamics) (s : Situation) (cause effect : Variable) :
    CausalAccessibility.lewis.necessary dyn s cause effect ↔
    ¬ developsToBe (intervene dyn s cause false).1
        (intervene dyn s cause false).2 effect true := by
  unfold CausalAccessibility.necessary CausalAccessibility.lewis developsToBe
  simp only [List.mem_singleton, forall_eq]
  constructor
  · intro h
    exact h trivial (intervene_cause_not_developed_to_true dyn s cause)
  · intro h _ _; exact h

-- ════════════════════════════════════════════════════
-- § Schema instance: Halpern-Pearl 2005 (modified)
-- ════════════════════════════════════════════════════

/-! @cite{halpern-pearl-2005} (with @cite{halpern-2015}'s "modified"
    simplification of AC2) augments Lewis's intervention with a
    **witness set `W`** held at its actual-world values. The structure
    handles preemption (Suzy/Billy throwing rocks): with `W = {Billy}`
    held at his actual non-throw, intervening to make Suzy not throw
    leaves the target unbroken — so Suzy is HP-actual-cause even though
    not Lewis-but-for.

    HP's distinctive feature is the **existential** quantifier over `W`:
    `cause` is an HP-actual-cause iff *some* witness `W` makes the
    counterfactual succeed. This sits orthogonally to the schema's
    `.necessary` operator (which is universal over alternatives).
    The pattern: instantiate one accessibility per `W` (each with a
    singleton access list) via `hpFixed`, and existentially quantify
    over `W` at the predicate level via `hpActualCause`. -/

/-- **Halpern-Pearl 2005 (modified) accessibility**, parameterized by a
    witness set `W` and an assignment `wValues` of values to `W`.

    The unique alternative is `do(cause := false)` augmented with each
    `v ∈ W` extended to `wValues.get v` (typically the actual-world
    value, i.e., from `normalDevelopment dyn s`). Trivial consistency.

    Specializing to `W = []` recovers `CausalAccessibility.lewis`. -/
def CausalAccessibility.hpFixed (W : List Variable) (wValues : Situation) :
    CausalAccessibility where
  access dyn s cause _effect :=
    let (dyn', s') := intervene dyn s cause false
    let s'' := W.foldl (fun acc v =>
                          match wValues.get v with
                          | some b => acc.extend v b
                          | none => acc) s'
    [(dyn', s'')]
  consistent _ _ _ _ := True
  consistentDecidable _ _ _ _ := inferInstance

/-- **Bridge: empty witness ⇒ Lewis**. With `W = []`, HP collapses to
    Lewis: the foldl is identity, so the unique alternative is exactly
    `intervene dyn s cause false`. -/
theorem hpFixed_empty_eq_lewis (wValues : Situation) :
    CausalAccessibility.hpFixed [] wValues = CausalAccessibility.lewis := rfl

/-- **Halpern-Pearl modified actual cause** (@cite{halpern-pearl-2005}
    + @cite{halpern-2015}).

    `cause` is an HP-actual-cause of `effect = true` at `(dyn, s)` iff:
    - **AC1**: both `cause` and `effect` actually develop to `true`
      under normal development from `s`.
    - **AC2-modified**: ∃ witness set `W` (with `cause ∉ W`,
      `effect ∉ W`) such that intervening to set `cause := false`
      while holding `W` at its actual-world values
      (`normalDevelopment dyn s`) makes `effect` fail to develop.

    AC3 (minimality of cause) is omitted here — the singleton-cause
    formulation makes it trivial.

    Captures preemption cases that Lewis misses: Lewis is the `W = []`
    instance, while HP can witness with non-empty `W` (Suzy's throw
    necessary given Billy's actual non-throw). -/
def hpActualCause (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Prop :=
  developsToBe dyn s cause true ∧
  developsToBe dyn s effect true ∧
  ∃ W : List Variable, cause ∉ W ∧ effect ∉ W ∧
    (CausalAccessibility.hpFixed W (normalDevelopment dyn s)).necessary
      dyn s cause effect

/-- **Lewis ⇒ HP**. Every Lewis-but-for cause is HP-modified-actual-cause
    (witnessed by the empty `W`). The converse fails on preemption
    scenarios — that asymmetry is precisely HP's contribution over
    Lewis. AC1 (both actually develop) must be supplied separately
    because Lewis-but-for doesn't entail it. -/
theorem lewis_implies_hp
    (dyn : CausalDynamics) (s : Situation) (cause effect : Variable)
    (hCauseAct : developsToBe dyn s cause true)
    (hEffectAct : developsToBe dyn s effect true)
    (hLewis : CausalAccessibility.lewis.necessary dyn s cause effect) :
    hpActualCause dyn s cause effect :=
  ⟨hCauseAct, hEffectAct, [], List.not_mem_nil, List.not_mem_nil,
    (hpFixed_empty_eq_lewis (normalDevelopment dyn s)).symm ▸ hLewis⟩

end Core.Causal
