import Linglib.Theories.Semantics.Verb.Roots.Typology

/-!
# Entailment Closure on Roots

@cite{beavers-koontz-garboden-2020}

`Root.entailments` is the *base* entailment set: atoms asserted directly
by the lexicographer. But @cite{beavers-koontz-garboden-2020}'s typology
treats roots as *networks* of entailments, where some atoms entail
others. The closure of the base under such network rules is the root's
full entailment set.

This file provides:

1. `EntailmentRules`: a function `LexEntailment → List LexEntailment`
   giving the atoms each premise atom directly entails.
2. `closeOnce`: one closure step (single inference round).
3. `closure`: alias for `closeOnce` — kept as the public API. For the
   currently-codified rules a single step is a fixpoint
   (`closure_bkgRules_idempotent`); if a chaining rule is added later,
   redefine `closure` as `Nat.iterate closeOnce n` and re-prove
   idempotence at the new bound.
4. `bkgRules`: the documented B&K-G rules. Currently a single rule:
   `becomesState s ⇒ hasState s` (a change-of-state to `s` entails the
   resulting state attribution `s`).
5. `Root.closedEntailments` and `Root.closedFeatureSignature`: the
   closure-derived counterparts of `entailments`/`featureSignature`.

The infrastructure is designed so that adding a new B&K-G inference
(e.g., `volitional ⇒ sentient`, `contact ⇒ motion`) is a one-line
extension to `bkgRules`.
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
def closeOnce (rules : EntailmentRules) (atoms : List LexEntailment) :
    List LexEntailment :=
  atoms ++ atoms.flatMap rules

/-- Backwards-compatible alias for `closeOnce`. The currently-codified
    `bkgRules` reach a fixpoint after one step (`closure_bkgRules_idempotent`).
    If a chaining rule is added, redefine via `Nat.iterate closeOnce`. -/
abbrev closure : EntailmentRules → List LexEntailment → List LexEntailment :=
  closeOnce

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
    a.isState := by
  match b, h with
  | .becomesState _, h =>
    rw [show bkgRules (.becomesState _) = [.hasState _] from rfl] at h
    rcases List.mem_singleton.mp h with rfl
    exact True.intro

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
  { state  := r.closedEntailments.any (decide <| LexEntailment.isState ·)
  , manner := r.closedEntailments.any (decide <| LexEntailment.isManner ·)
  , result := r.closedEntailments.any (decide <| LexEntailment.isBecome ·)
  , cause  := r.closedEntailments.any (decide <| LexEntailment.isCause ·) }

end Root

-- ════════════════════════════════════════════════════
-- § 4. Structural Properties of Closure
-- ════════════════════════════════════════════════════

/-- Closure preserves all base atoms: the base list is a prefix of the
    closure. -/
theorem closure_includes (rules : EntailmentRules)
    (atoms : List LexEntailment) (a : LexEntailment) (h : a ∈ atoms) :
    a ∈ closure rules atoms := by
  unfold closure closeOnce
  exact List.mem_append_left _ h

/-- Adding the closure step never makes `any p` go from `true` to
    `false` — closure is monotone for `List.any`. -/
theorem closure_any_of_any (rules : EntailmentRules)
    (atoms : List LexEntailment) (p : LexEntailment → Bool)
    (h : atoms.any p = true) :
    (closure rules atoms).any p = true := by
  unfold closure closeOnce
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
@[simp] theorem closedFeatureSignature_manner (r : Root) :
    r.closedFeatureSignature.manner = r.featureSignature.manner := by
  show r.closedEntailments.any (decide <| LexEntailment.isManner ·) =
    r.entailments.any (decide <| LexEntailment.isManner ·)
  unfold Root.closedEntailments closure closeOnce
  rw [List.any_append,
      flatMap_bkgRules_any_eq_false r.entailments _ (fun _ => rfl),
      Bool.or_false]

/-- Closed and base signatures agree on `result`. -/
@[simp] theorem closedFeatureSignature_result (r : Root) :
    r.closedFeatureSignature.result = r.featureSignature.result := by
  show r.closedEntailments.any (decide <| LexEntailment.isBecome ·) =
    r.entailments.any (decide <| LexEntailment.isBecome ·)
  unfold Root.closedEntailments closure closeOnce
  rw [List.any_append,
      flatMap_bkgRules_any_eq_false r.entailments _ (fun _ => rfl),
      Bool.or_false]

/-- Closed and base signatures agree on `cause`. -/
@[simp] theorem closedFeatureSignature_cause (r : Root) :
    r.closedFeatureSignature.cause = r.featureSignature.cause := by
  show r.closedEntailments.any (decide <| LexEntailment.isCause ·) =
    r.entailments.any (decide <| LexEntailment.isCause ·)
  unfold Root.closedEntailments closure closeOnce
  rw [List.any_append,
      flatMap_bkgRules_any_eq_false r.entailments _ (fun _ => rfl),
      Bool.or_false]

/-- Closure can only add `state`: if the base says `state = true`, the
    closure agrees; if base says `false`, closure may say `true`. -/
theorem closedFeatureSignature_state_of_base (r : Root)
    (h : r.featureSignature.state = true) :
    r.closedFeatureSignature.state = true := by
  show r.closedEntailments.any (decide <| LexEntailment.isState ·) = true
  exact closure_any_of_any bkgRules r.entailments _ h

/-- The principal closure consequence: every `becomesState s` in the
    base entailment set forces `state = true` in the closed signature. -/
theorem closedFeatureSignature_state_of_becomes (r : Root) (s : String)
    (h : LexEntailment.becomesState s ∈ r.entailments) :
    r.closedFeatureSignature.state = true := by
  show r.closedEntailments.any (decide <| LexEntailment.isState ·) = true
  unfold Root.closedEntailments closure closeOnce
  rw [List.any_append]
  apply Bool.or_eq_true_iff.mpr
  right
  apply List.any_eq_true.mpr
  refine ⟨LexEntailment.hasState s, ?_, ?_⟩
  · apply List.mem_flatMap.mpr
    exact ⟨LexEntailment.becomesState s, h, by simp [bkgRules]⟩
  · rfl

/-- Closure adds state atoms exactly when the base set has a
    `becomesState` atom. So the closed `state` field is the disjunction
    of base `state` and base `result`. -/
theorem closedFeatureSignature_state_eq (r : Root) :
    r.closedFeatureSignature.state =
      (r.featureSignature.state || r.featureSignature.result) := by
  show r.closedEntailments.any (decide <| LexEntailment.isState ·) =
    (r.entailments.any (decide <| LexEntailment.isState ·) ||
      r.entailments.any (decide <| LexEntailment.isBecome ·))
  unfold Root.closedEntailments closure closeOnce
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
    exact ⟨_, hb, by rfl⟩
  · intro hbase
    rcases List.any_eq_true.mp hbase with ⟨a, ha, hp⟩
    cases a <;> simp [LexEntailment.isBecome, decide_eq_true_eq] at hp
    rename_i s
    apply List.any_eq_true.mpr
    refine ⟨LexEntailment.hasState s, ?_, by rfl⟩
    apply List.mem_flatMap.mpr
    exact ⟨LexEntailment.becomesState s, ha, by simp [bkgRules]⟩

-- ════════════════════════════════════════════════════
-- § 6. Idempotence of bkgRules
-- ════════════════════════════════════════════════════

/-- `bkgRules` produces nothing from a `hasState` atom (and similarly
    nothing from any non-`becomesState` atom). -/
theorem bkgRules_eq_nil_of_isState (a : LexEntailment) (h : a.isState) :
    bkgRules a = [] := by
  cases a <;> simp_all [bkgRules, LexEntailment.isState]

/-- If every atom in `atoms` is a `hasState`, `flatMap bkgRules` is empty. -/
theorem flatMap_bkgRules_eq_nil_of_all_isState (atoms : List LexEntailment)
    (h : ∀ a ∈ atoms, a.isState) :
    atoms.flatMap bkgRules = [] := by
  induction atoms with
  | nil => rfl
  | cons a t ih =>
    have ha : a.isState := h a List.mem_cons_self
    have ht : ∀ x ∈ t, x.isState :=
      fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [List.flatMap_cons, bkgRules_eq_nil_of_isState a ha, List.nil_append,
        ih ht]

/-- After one `flatMap bkgRules`, every atom is a state-attribution, so a
    further `flatMap bkgRules` produces nothing. -/
theorem flatMap_bkgRules_flatMap_bkgRules_eq_nil
    (atoms : List LexEntailment) :
    (atoms.flatMap bkgRules).flatMap bkgRules = [] := by
  apply flatMap_bkgRules_eq_nil_of_all_isState
  intro a ha
  rcases List.mem_flatMap.mp ha with ⟨b, _, hb⟩
  exact bkgRules_only_state a b hb

/-- `closeOnce bkgRules` is idempotent up to `List.any` queries — a
    second application adds duplicate copies of state atoms, but no new
    distinct atoms. This is the precise sense in which `closure := closeOnce`
    suffices for the downstream `Root.closedFeatureSignature` API. -/
theorem closure_bkgRules_any_idempotent (atoms : List LexEntailment)
    (p : LexEntailment → Bool) :
    (closure bkgRules (closure bkgRules atoms)).any p =
      (closure bkgRules atoms).any p := by
  unfold closure closeOnce
  rw [List.flatMap_append, flatMap_bkgRules_flatMap_bkgRules_eq_nil,
      List.append_nil]
  simp only [List.any_append, Bool.or_assoc, Bool.or_self]

end Semantics.Verb.Roots
