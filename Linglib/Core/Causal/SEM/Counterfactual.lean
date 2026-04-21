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
- `extractProfile` — packages sufficient/necessary/direct
- `simple_law_necessity` — structured proof that `c → e` makes `c`
  necessary for `e` against the empty background
-/

namespace Core.Causal

-- ============================================================
-- § Convenience Functions
-- ============================================================

/-- Check if a variable develops to a specific value. -/
def developsToBe (dyn : CausalDynamics) (s : Situation) (v : Variable) (val : Bool) : Bool :=
  (normalDevelopment dyn s).hasValue v val

/-- Check if a variable becomes true after normal development. -/
def developsToTrue (dyn : CausalDynamics) (s : Situation) (v : Variable) : Bool :=
  developsToBe dyn s v true

/-- The cause is present and the effect holds after normal development.

    Shared primitive for `actuallyCaused` (Necessity.lean) and
    `complementActualized` (Ability.lean). -/
def factuallyDeveloped (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Bool :=
  s.hasValue cause true &&
  (normalDevelopment dyn s).hasValue effect true

/-- `factuallyDeveloped` unfolds to a conjunction of two `hasValue` checks. -/
theorem factuallyDeveloped_iff (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) :
    factuallyDeveloped dyn s cause effect =
      (s.hasValue cause true && (normalDevelopment dyn s).hasValue effect true) := rfl

-- ============================================================
-- § Structural Graph Queries
-- ============================================================

/-- Does any causal law directly connect `cause` to `effect`? -/
def hasDirectLaw (dyn : CausalDynamics) (cause effect : Variable) : Bool :=
  dyn.laws.any fun law =>
    law.preconditions.any (fun (v, _) => v == cause) && law.effect == effect

/-- Does the intermediate have a causal law not depending on `cause`? -/
def hasIndependentSource (dyn : CausalDynamics)
    (cause intermediate : Variable) : Bool :=
  dyn.laws.any fun law =>
    law.effect == intermediate &&
    !(law.preconditions.any (fun (v, _) => v == cause))

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

/-- **Manipulates**: Does intervening on `cause` change the value of `effect`?

    Compares normal development under do(cause = true) vs do(cause = false).
    If the effect's value differs, then `cause` manipulates `effect`.

    This is the interventionist criterion for causation:
    X causes Y iff there exists an intervention on X that changes Y. -/
def manipulates (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Bool :=
  let (dynT, sT) := intervene dyn s cause true
  let (dynF, sF) := intervene dyn s cause false
  let valT := (normalDevelopment dynT sT).get effect
  let valF := (normalDevelopment dynF sF).get effect
  valT != valF

-- ============================================================
-- § Counterfactual Queries (@cite{nadathur-lauer-2020} Definitions 23-24)
-- ============================================================

/-- **Causal Sufficiency** (@cite{nadathur-lauer-2020}, Definition 23).
    C is causally sufficient for E in situation s iff adding C and
    developing normally produces E. -/
def causallySufficient (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Bool :=
  let sWithCause := s.extend cause true
  let developed := normalDevelopment dyn sWithCause
  developed.hasValue effect true

/-- Is `s'` a consistent supersituation of `base` under dynamics `dyn`?
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
    (innerVars : List Variable) : Bool :=
  let developed := normalDevelopment dyn base
  innerVars.all fun x =>
    match base.get x, s'.get x with
    | none, some true  => !developed.hasValue x false
    | none, some false => !developed.hasValue x true
    | _, _ => true

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
    (cause effect : Variable) : Bool :=
  let devS := normalDevelopment dyn s
  -- Precondition: neither cause nor effect already entailed by s
  if devS.hasValue cause true || devS.hasValue effect true then false
  else
    let innerVars := innerVariables dyn
    let allVars := allVariables dyn
    -- (i) Achievability: ∃ consistent supersituation of s[cause↦true]
    --     with effect ∉ dom(s') where s' ⊨_D ⟨effect, true⟩
    let sCause := s.extend cause true
    let freeI := allVars.filter fun v =>
      v != effect && (sCause.get v).isNone
    let achievable := (sCause.allExtensions freeI).any fun s' =>
      isConsistentSuper dyn sCause s' innerVars &&
      (normalDevelopment dyn s').hasValue effect true
    -- (ii) But-for: no consistent supersituation of s with
    --      effect ∉ dom(s') achieves effect without cause
    let freeII := allVars.filter fun v =>
      v != effect && (s.get v).isNone
    let hasAlternative := (s.allExtensions freeII).any fun s' =>
      isConsistentSuper dyn s s' innerVars &&
      (normalDevelopment dyn s').hasValue effect true &&
      !(normalDevelopment dyn s').hasValue cause true
    achievable && !hasAlternative

/-- Causal profile: packages the counterfactual properties of a
    cause-effect pair in a structural model. -/
structure CausalProfile where
  sufficient : Bool
  necessary : Bool
  direct : Bool
  deriving DecidableEq, Repr

/-- Extract the causal profile of a cause-effect pair. -/
def extractProfile (dyn : CausalDynamics) (bg : Situation)
    (cause effect : Variable) : CausalProfile :=
  { sufficient := causallySufficient dyn bg cause effect
  , necessary := causallyNecessary dyn bg cause effect
  , direct := hasDirectLaw dyn cause effect }

-- ============================================================
-- § Simple-law necessity (structured proof)
-- ============================================================

private theorem normalDevelopment_simple (c e : Variable) (s : Situation) :
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

private theorem extend_get_ne {s : Situation} {v w : Variable} {val : Bool} (h : v ≠ w) :
    (s.extend w val).get v = s.get v := by
  unfold Situation.get Situation.extend
  simp only
  rw [show (v == w) = false from beq_false_of_ne h]; rfl

private theorem allExtensions_preserves_none (s : Situation) (vars : List Variable)
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
      rw [← heq, extend_get_ne hw]; exact hRest t ht
    · have ⟨t, ht, heq⟩ := List.mem_map.mp hs'
      rw [← heq, extend_get_ne hw]; exact hRest t ht

private theorem empty_hasValue_false' (v : Variable) (b : Bool) :
    Situation.empty.hasValue v b = false := by
  simp [Situation.hasValue, Situation.empty, Option.none_beq_some]

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

private theorem freeI_eq_nil (c e : Variable) :
    (allVariables ⟨[CausalLaw.simple c e]⟩).filter
      (fun v => v != e && ((Situation.empty.extend c true).get v).isNone) = [] := by
  rw [List.filter_eq_nil_iff]
  intro v hv
  rcases allVars_mem_simple c e v hv with rfl | rfl
  · simp
  · simp [Situation.get, Situation.extend, Option.isNone]

private theorem isConsistentSuper_self' (dyn : CausalDynamics) (s : Situation)
    (vars : List Variable) :
    isConsistentSuper dyn s s vars = true := by
  simp only [isConsistentSuper]
  apply List.all_eq_true.mpr
  intro x _
  simp only [Situation.get]
  cases s.valuation x <;> simp

private theorem e_not_in_freeII (c e : Variable) :
    e ∉ (allVariables ⟨[CausalLaw.simple c e]⟩).filter
      (fun v => v != e && (Situation.empty.get v).isNone) := by
  intro h
  rw [List.mem_filter] at h
  simp at h

set_option maxHeartbeats 3200000 in
/-- For a simple causal law `c → e`, the cause is necessary for the effect
    relative to the empty background under @cite{nadathur-2024} Definition 10b.

    The argument:
    1. **Precondition**: `normalDevelopment(empty)` = empty, so neither cause
       nor effect is entailed
    2. **Achievability**: extending with `c=true` fires the law → `e=true`
    3. **But-for**: every consistent supersituation of empty either (a) has
       `c=true`, in which case normalDev preserves it (blocking the
       `¬cause` conjunct), or (b) has `c≠true`, in which case the law
       doesn't fire and `e` remains unset (blocking the `effect` conjunct) -/
theorem simple_law_necessity (c e : Variable) :
    causallyNecessary ⟨[CausalLaw.simple c e]⟩ Situation.empty c e = true := by
  simp only [causallyNecessary]
  have hDevEmpty : normalDevelopment ⟨[CausalLaw.simple c e]⟩ Situation.empty = Situation.empty := by
    rw [normalDevelopment_simple]; simp [empty_hasValue_false']
  rw [hDevEmpty]
  simp only [empty_hasValue_false', Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  rw [freeI_eq_nil]
  simp only [Situation.allExtensions, List.any_cons, List.any_nil, Bool.or_false]
  rw [innerVars_simple, isConsistentSuper_self']
  simp only [Bool.true_and]
  have hDevCause : (normalDevelopment ⟨[CausalLaw.simple c e]⟩
      (Situation.empty.extend c true)).hasValue e true = true := by
    rw [normalDevelopment_simple]
    simp [Situation.extend_hasValue_same]
  rw [hDevCause]; simp only [Bool.true_and]
  suffices hAlt : (Situation.empty.allExtensions
      ((allVariables ⟨[CausalLaw.simple c e]⟩).filter
        (fun v => v != e && (Situation.empty.get v).isNone))).any
      (fun s' => isConsistentSuper ⟨[CausalLaw.simple c e]⟩ Situation.empty s' [e] &&
        (normalDevelopment ⟨[CausalLaw.simple c e]⟩ s').hasValue e true &&
        !(normalDevelopment ⟨[CausalLaw.simple c e]⟩ s').hasValue c true) = false by
    rw [hAlt]; rfl
  rw [List.any_eq_false]
  intro s' hs'
  have hGetE : s'.get e = none :=
    allExtensions_preserves_none Situation.empty _ e (e_not_in_freeII c e)
      (by simp [Situation.get, Situation.empty]) s' hs'
  rcases Bool.eq_false_or_eq_true (s'.hasValue c true) with hc | hc
  · rw [normalDevelopment_simple]
    simp only [hc, ↓reduceIte]
    by_cases hce : c = e
    · subst hce
      simp [Situation.extend_hasValue_same, Bool.and_true, Bool.not_true]
    · simp [Situation.extend_hasValue_diff hce, hc, Bool.not_true, Bool.and_false]
  · rw [normalDevelopment_simple]
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    have hE : s'.hasValue e true = false := by
      simp only [Situation.hasValue]
      rw [show s'.valuation e = s'.get e from rfl, hGetE]
      rfl
    simp [hE]

end Core.Causal
