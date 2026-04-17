import Linglib.Theories.Semantics.Verb.Roots.Typology

/-!
# Entailment Closure on Roots

@cite{beavers-koontz-garboden-2020}

`Root.entailments` is the *base* entailment set: atoms asserted directly
by the lexicographer. But @cite{beavers-koontz-garboden-2020}'s typology
treats roots as *networks* of entailments, where some atoms entail
others. The transitive closure of the base under such network rules is
the root's full entailment set.

This file provides:

1. `EntailmentRules`: a function `LexEntailment → List LexEntailment`
   giving the atoms each premise atom directly entails.
2. `closure`: one closure step (single inference). Iterating to a
   fixpoint is unnecessary for the rules we currently codify because
   none chains.
3. `bkgRules`: the documented B&K-G rules. Currently a single rule:
   `becomesState s ⇒ hasState s` (a change-of-state to `s` entails the
   resulting state attribution `s`).
4. `Root.closedEntailments` and `Root.closedFeatureSignature`: the
   closure-derived counterparts of `entailments`/`featureSignature`.

The infrastructure is designed so that adding a new B&K-G inference
(e.g., `volitional ⇒ sentient`, `contact ⇒ motion`) is a one-line
extension — no proofs need to be redone.
-/

namespace Semantics.Verb.Roots

-- ════════════════════════════════════════════════════
-- § 1. Closure Rules
-- ════════════════════════════════════════════════════

/-- A rule set: each atom maps to the atoms it directly entails. -/
abbrev EntailmentRules := LexEntailment → List LexEntailment

/-- One closure step: adjoin to `atoms` everything any rule fires from
    an atom in `atoms`. Result is `atoms` followed by all derived atoms.
    Duplicates are not removed (they are inert under `List.any` /
    `List.contains` queries used downstream). -/
def closeStep (rules : EntailmentRules) (atoms : List LexEntailment) :
    List LexEntailment :=
  atoms ++ atoms.flatMap rules

/-- The closure of `atoms` under `rules`. We iterate `closeStep` once;
    rules in `bkgRules` are non-chaining so a single step suffices. If a
    chain rule is later added, increase the iteration count and re-prove
    `closure_idempotent`. -/
def closure (rules : EntailmentRules) (atoms : List LexEntailment) :
    List LexEntailment :=
  closeStep rules atoms

-- ════════════════════════════════════════════════════
-- § 2. B&K-G Rules
-- ════════════════════════════════════════════════════

/-- The documented B&K-G entailment rules. Currently:
    - `becomesState s ⇒ hasState s`: a change of state to `s` entails
      that `s` holds at the post-state, so the root attributes `s`.

    Other candidate rules (`volitional ⇒ sentient`, `contact ⇒ motion`)
    are debated in the literature and intentionally omitted until they
    can be argued for from primary sources. -/
def bkgRules : EntailmentRules
  | .becomesState s => [.hasState s]
  | _ => []

/-- Every atom produced by `bkgRules` is a state-attribution. -/
theorem bkgRules_only_state (a b : LexEntailment) (h : a ∈ bkgRules b) :
    a.isState = true := by
  cases b <;> simp [bkgRules] at h
  obtain rfl := h
  rfl

-- ════════════════════════════════════════════════════
-- § 3. Closed Entailments and Signature
-- ════════════════════════════════════════════════════

namespace Root

/-- The B&K-G closure of the root's base entailments. -/
def closedEntailments (r : Root) : List LexEntailment :=
  closure bkgRules r.entailments

/-- The feature signature computed over the *closure* of the root's
    entailments. For the current `bkgRules`, this differs from
    `featureSignature` only in the `state` field: any root with a
    `becomesState` atom in its base set acquires `state = true`. -/
def closedFeatureSignature (r : Root) : FeatureSignature :=
  { state  := r.closedEntailments.any LexEntailment.isState
  , manner := r.closedEntailments.any LexEntailment.isManner
  , result := r.closedEntailments.any LexEntailment.isBecome
  , cause  := r.closedEntailments.any LexEntailment.isCause }

end Root

-- ════════════════════════════════════════════════════
-- § 4. Structural Properties of Closure
-- ════════════════════════════════════════════════════

/-- Closure preserves all base atoms: the base list is a prefix of the
    closure. -/
theorem closure_includes (rules : EntailmentRules)
    (atoms : List LexEntailment) (a : LexEntailment) (h : a ∈ atoms) :
    a ∈ closure rules atoms := by
  unfold closure closeStep
  exact List.mem_append_left _ h

/-- Adding the closure step never makes `any p` go from `true` to
    `false` — closure is monotone for `List.any`. -/
theorem closure_any_of_any (rules : EntailmentRules)
    (atoms : List LexEntailment) (p : LexEntailment → Bool)
    (h : atoms.any p = true) :
    (closure rules atoms).any p = true := by
  unfold closure closeStep
  rw [List.any_append, h, Bool.true_or]

-- ════════════════════════════════════════════════════
-- § 5. Bridge to Base Signature
-- ════════════════════════════════════════════════════

/-- Helper: bkgRules-derived atoms can never satisfy a predicate `p`
    that is false on every state-attribution atom. -/
private theorem flatMap_bkgRules_any_eq_false (atoms : List LexEntailment)
    (p : LexEntailment → Bool)
    (hp : ∀ s : String, p (LexEntailment.hasState s) = false) :
    (atoms.flatMap bkgRules).any p = false := by
  apply List.any_eq_false.mpr
  intro a ha
  rcases List.mem_flatMap.mp ha with ⟨b, _, hb⟩
  cases b <;> simp [bkgRules] at hb
  obtain rfl := hb
  simp [hp]

/-- Closed and base signatures agree on `manner`. -/
theorem closedFeatureSignature_manner (r : Root) :
    r.closedFeatureSignature.manner = r.featureSignature.manner := by
  show r.closedEntailments.any LexEntailment.isManner =
    r.entailments.any LexEntailment.isManner
  unfold Root.closedEntailments closure closeStep
  rw [List.any_append,
      flatMap_bkgRules_any_eq_false r.entailments _ (fun _ => rfl),
      Bool.or_false]

/-- Closed and base signatures agree on `result`. -/
theorem closedFeatureSignature_result (r : Root) :
    r.closedFeatureSignature.result = r.featureSignature.result := by
  show r.closedEntailments.any LexEntailment.isBecome =
    r.entailments.any LexEntailment.isBecome
  unfold Root.closedEntailments closure closeStep
  rw [List.any_append,
      flatMap_bkgRules_any_eq_false r.entailments _ (fun _ => rfl),
      Bool.or_false]

/-- Closed and base signatures agree on `cause`. -/
theorem closedFeatureSignature_cause (r : Root) :
    r.closedFeatureSignature.cause = r.featureSignature.cause := by
  show r.closedEntailments.any LexEntailment.isCause =
    r.entailments.any LexEntailment.isCause
  unfold Root.closedEntailments closure closeStep
  rw [List.any_append,
      flatMap_bkgRules_any_eq_false r.entailments _ (fun _ => rfl),
      Bool.or_false]

/-- Closure can only add `state`: if the base says `state = true`, the
    closure agrees; if base says `false`, closure may say `true`. -/
theorem closedFeatureSignature_state_of_base (r : Root)
    (h : r.featureSignature.state = true) :
    r.closedFeatureSignature.state = true := by
  show r.closedEntailments.any LexEntailment.isState = true
  exact closure_any_of_any bkgRules r.entailments _ h

/-- The principal closure consequence: every `becomesState s` in the
    base entailment set forces `state = true` in the closed signature. -/
theorem closedFeatureSignature_state_of_becomes (r : Root) (s : String)
    (h : LexEntailment.becomesState s ∈ r.entailments) :
    r.closedFeatureSignature.state = true := by
  show r.closedEntailments.any LexEntailment.isState = true
  unfold Root.closedEntailments closure closeStep
  rw [List.any_append]
  apply Bool.or_eq_true_iff.mpr
  right
  apply List.any_eq_true.mpr
  refine ⟨LexEntailment.hasState s, ?_, rfl⟩
  apply List.mem_flatMap.mpr
  exact ⟨LexEntailment.becomesState s, h, by simp [bkgRules]⟩

/-- Closure adds state atoms exactly when the base set has a
    `becomesState` atom. So the closed `state` field is the disjunction
    of base `state` and base `result`. -/
theorem closedFeatureSignature_state_eq (r : Root) :
    r.closedFeatureSignature.state =
      (r.featureSignature.state || r.featureSignature.result) := by
  show r.closedEntailments.any LexEntailment.isState =
    (r.entailments.any LexEntailment.isState ||
      r.entailments.any LexEntailment.isBecome)
  unfold Root.closedEntailments closure closeStep
  rw [List.any_append]
  congr 1
  -- (flatMap bkgRules).any isState = entailments.any isBecome
  apply Bool.eq_iff_iff.mpr
  refine ⟨?_, ?_⟩
  · intro hflat
    rcases List.any_eq_true.mp hflat with ⟨a, ha, hp⟩
    rcases List.mem_flatMap.mp ha with ⟨b, hb, hab⟩
    cases b <;> simp [bkgRules] at hab
    obtain rfl := hab
    apply List.any_eq_true.mpr
    exact ⟨_, hb, rfl⟩
  · intro hbase
    rcases List.any_eq_true.mp hbase with ⟨a, ha, hp⟩
    cases a <;> simp [LexEntailment.isBecome] at hp
    rename_i s
    apply List.any_eq_true.mpr
    refine ⟨LexEntailment.hasState s, ?_, rfl⟩
    apply List.mem_flatMap.mpr
    exact ⟨LexEntailment.becomesState s, ha, by simp [bkgRules]⟩

end Semantics.Verb.Roots
