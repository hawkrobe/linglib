import Linglib.Semantics.Dynamic.Update
import Linglib.Semantics.Dynamic.Lookup
import Linglib.Semantics.Dynamic.ICDRT.Defs
import Linglib.Studies.GroenendijkStokhof1991

/-!
# Charlow 2019: where is the destructive update problem?

This file formalizes the argument of [charlow-2019] that destructive update is not a problem
peculiar to dynamic semantics. Overwriting an assignment's value at a variable is something the
static and the dynamic system do alike, and it costs neither of them its truth conditions; what
separates them is only whether the modified assignment is retained, which is one operator's worth
of difference. Lifting a pointwise update into a state of world-assignment pairs is injective and
preserves anaphoric distributivity, and lowering back at a world undoes it, but the round trip in
the other direction does not — which is exactly where the state's extra structure lives.

## Main definitions

* `staticExists`, `dynamicExists` — the static and dynamic existentials
* `reachable` — assignment reachability by a formula of dynamic predicate logic, a preorder that
  is not antisymmetric
* `liftPW`, `lowerPW` — Charlow's ↑ and its inverse at a world
* `anaphoricallyDistributive` — distributivity over the partition by assignment

## Main results

* `destructive_preserves_truth`, `static_dynamic_same_truth` — overwriting costs no truth
  conditions, and the two existentials agree on them
* `dynamic_changes_assignment`, `static_is_test` — while differing on the output assignment
* `reachable_iff_finite`, `reachable_symm`, `antisymmetry_fails` — reachability by a formula is
  differing at finitely many variables, so it is symmetric and no partial order
* `lowerPW_liftPW`, `liftPW_injective`, `liftPW_preserves_distributive`, `liftPW_lowerPW_not_id` —
  what the lift keeps and what the state adds
* `dom_staticExists`, `dom_dynamicExists` — both existentials are true where the
  cylindrification of the body is

## References

* [charlow-2019]
-/

namespace Charlow2019

open DynamicSemantics DynamicSemantics.Update CylindricAlgebra SetRel
open DynamicSemantics.CCP (IsDistributive)
open DynamicSemantics.ICDRT

/-- Destructive update preserves truth conditions (§4). -/
theorem destructive_preserves_truth {E : Type*}
    (P Q : E → Prop) (g : Assignment E) :
    g ∈ (dexists 6 (test {g' | P (g' 6)}) ○ dexists 6 (test {g' | Q (g' 6)})).dom ↔
      (∃ x, P x) ∧ (∃ y, Q y) := by
  constructor
  · rintro ⟨_, _, ⟨_, ⟨d₁, rfl⟩, rfl, hP⟩, _, ⟨d₂, rfl⟩, rfl, hQ⟩
    exact ⟨⟨d₁, by simpa using hP⟩, ⟨d₂, by simpa using hQ⟩⟩
  · rintro ⟨⟨x, hPx⟩, ⟨y, hQy⟩⟩
    exact ⟨_, _, ⟨_, ⟨x, rfl⟩, rfl, by simpa⟩, _, ⟨y, rfl⟩, rfl, by simpa⟩

/-- Static ↑: evaluates truth, discards modified assignment (Table 1, row 1). -/
def staticExists {E : Type*} (x : Nat) (body : Set (Assignment E)) : Update (Assignment E) :=
  test (cyl x body)

/-- Dynamic ↑: retains modified assignment (Table 1, row 2). -/
def dynamicExists {E : Type*} (x : Nat) (body : Set (Assignment E)) : Update (Assignment E) :=
  dexists x (test body)

/-- Static existential is a test: output = input. -/
theorem static_is_test {E : Type*} (x : Nat) (body : Set (Assignment E)) :
    (staticExists x body).IsTest :=
  isTest_test _

/-- Dynamic existential can change the assignment. -/
theorem dynamic_changes_assignment {E : Type*} [Nontrivial E] :
    ∃ (x : Nat) (body : Set (Assignment E)) (g h : Assignment E),
      g ~[dynamicExists x body] h ∧ g ≠ h := by
  obtain ⟨e₁, e₂, hne⟩ := exists_pair_ne E
  refine ⟨0, Set.univ, fun _ ↦ e₁, Function.update (fun _ ↦ e₁) 0 e₂,
    ⟨_, ⟨e₂, rfl⟩, rfl, trivial⟩, fun heq ↦ hne ?_⟩
  simpa using congr_fun heq 0

/-- The static existential is true where the cylindrification of its body along `x` is. -/
theorem dom_staticExists {E : Type*} (x : Nat) (body : Set (Assignment E)) :
    (staticExists x body).dom = cyl x body :=
  dom_test _

/-- The dynamic existential is true where the cylindrification of its body along `x` is. -/
theorem dom_dynamicExists {E : Type*} (x : Nat) (body : Set (Assignment E)) :
    (dynamicExists x body).dom = cyl x body := by
  rw [dynamicExists, dom_dexists, dom_test]

/-- Static and dynamic agree on truth conditions (§4, §7). -/
theorem static_dynamic_same_truth {E : Type*} (x : Nat) (body : Set (Assignment E)) :
    (staticExists x body).dom = (dynamicExists x body).dom := by
  rw [dom_staticExists, dom_dynamicExists]

section Reachability

open FirstOrder DPL DPL.Formula

variable {L : Language} {E : Type*} [L.Structure E] {g h k : Assignment E}

variable (L) in
/-- An assignment is reachable from another when some formula of dynamic predicate logic takes
the one to the other (24). -/
def reachable (g h : Assignment E) : Prop :=
  ∃ φ : Formula L ℕ, g ~[φ.eval E] h

/-- Reachability is reflexive, by the tautology. -/
theorem reachable_refl (g : Assignment E) : reachable L g g :=
  ⟨.top, rfl⟩

/-- Reachability is transitive, by conjunction. -/
theorem reachable_trans (hgh : reachable L g h) (hhk : reachable L h k) : reachable L g k := by
  obtain ⟨φ, hφ⟩ := hgh
  obtain ⟨ψ, hψ⟩ := hhk
  exact ⟨φ ⋏ ψ, h, hφ, hψ⟩

/-- The assignments reachable from one another are those that differ at finitely many
variables: a formula changes only its active quantifier variables, and resetting the variables
where two assignments differ takes the one to the other. -/
theorem reachable_iff_finite : reachable L g h ↔ {x | g x ≠ h x}.Finite := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine φ.aqv.finite_toSet.subset fun x hx ↦ ?_
    by_contra hxφ
    exact hx (GroenendijkStokhof1991.eqOn_of_eval hφ hxφ)
  · intro hfin
    refine ⟨exs hfin.toFinset.toList .top, (mem_eval_exs E _).mpr ⟨h, fun y hy ↦ ?_, rfl⟩⟩
    by_contra hne
    exact hy (by simpa using fun heq ↦ hne heq.symm)

/-- Reachability is symmetric, so it is a partial order only if it is trivial. -/
theorem reachable_symm (hgh : reachable L g h) : reachable L h g := by
  rw [reachable_iff_finite] at hgh ⊢
  simpa only [ne_comm] using hgh

/-- Antisymmetry fails: distinct assignments are reachable from one another (§8), an
overwritten variable being overwritten again with its old value. -/
theorem antisymmetry_fails [Nontrivial E] :
    ∃ g h : Assignment E, g ≠ h ∧ reachable L g h ∧ reachable L h g := by
  obtain ⟨e₁, e₂, hne⟩ := exists_pair_ne E
  have hr : reachable L (fun _ ↦ e₁) (Function.update (fun _ ↦ e₁) 0 e₂) :=
    ⟨∃[0] .top, mem_dexists.mpr ⟨e₂, rfl⟩⟩
  exact ⟨_, _, fun heq ↦ hne (by simpa using congr_fun heq 0), hr, reachable_symm hr⟩

end Reachability

/-- Charlow's context type: a set of world-assignment pairs. -/
abbrev State (W E : Type*) := Set (W × Assignment E)

/-- Context change potential over Charlow's contexts. -/
abbrev State.CCP (W E : Type*) := DynamicSemantics.CCP (W × Assignment E)

/-- Non-distributive negation (28): removes from s points that survive φ. -/
def stateNeg {W E : Type*} (φ : State.CCP W E) : State.CCP W E :=
  λ s => {i ∈ s | i ∉ φ s}

/-- Distributive negation (29): tests each point individually. -/
def stateDistNeg {W E : Type*} (φ : State.CCP W E) : State.CCP W E :=
  λ s => {i ∈ s | φ {i} = ∅}

/-- Partition by assignment: groups points sharing the same assignment (Charlow's (35)). -/
def partByAssignment {W E : Type*} (s : State W E) : Set (State W E) :=
  {t | t ⊆ s ∧ t.Nonempty ∧ ∀ i ∈ t, ∀ j ∈ t, i.2 = j.2}

/-- Anaphorically distributive: processes each assignment-group separately (Charlow's (39)). -/
def anaphoricallyDistributive {W E : Type*} (φ : State.CCP W E) : Prop :=
  ∀ s, φ s = {p | ∃ t ∈ partByAssignment s, p ∈ φ t}

/-- Every distributive meaning is anaphorically distributive. -/
theorem distributive_implies_anaphoric {W E : Type*} (φ : State.CCP W E) :
    IsDistributive φ → anaphoricallyDistributive φ := by
  intro hD s
  ext p; simp only [Set.mem_ofPred_eq]
  constructor
  · intro hp
    rw [hD s] at hp
    obtain ⟨i, hi, hpi⟩ := hp
    refine ⟨{i}, ⟨?_, ⟨i, rfl⟩, ?_⟩, hpi⟩
    · intro x (hx : x = i); rwa [hx]
    · intro a (ha : a = i) b (hb : b = i); rw [ha, hb]
  · intro ⟨t, ⟨ht_sub, _, _⟩, hpt⟩
    rw [hD t] at hpt
    obtain ⟨i, hi, hpi⟩ := hpt
    rw [hD s]
    exact ⟨i, ht_sub hi, hpi⟩

-- ════════════════════════════════════════════════════════════════
-- Pointwise ↔ update-theoretic bridge (Charlow's ↑ / ↓)
-- ════════════════════════════════════════════════════════════════

/-! Charlow's ↑ (`liftPW`) promotes a pointwise `Update (Assignment E)`
(Dynamic Ty2, [muskens-1996]) to a context-level `State.CCP W E`; his ↓
(`lowerPW`) extracts a pointwise relation back. Lifted meanings are always
distributive (`liftPW_preserves_distributive`), so pointwise meanings can
never produce irreducibly context-level effects — cumulative readings
require non-distributive updates, which live only in `State.CCP`. -/

/-- Charlow's ↑: lift a pointwise Update to an update on states.
    `liftPW D s = {⟨w, h⟩ | ∃ ⟨w, g⟩ ∈ s, D g h}`
    Each world-assignment pair in the output comes from applying D to some
    input assignment in s, preserving the world. -/
def liftPW {W E : Type*} (D : Update (Assignment E)) : State.CCP W E :=
  λ s => {p | ∃ q ∈ s, p.1 = q.1 ∧ q.2 ~[D] p.2}

/-- Charlow's ↓: extract a pointwise Update from a state update by
    evaluating K on a singleton context at an arbitrary world. -/
def lowerPW {W E : Type*} (K : State.CCP W E) (w₀ : W) : Update (Assignment E) :=
  {p | (w₀, p.2) ∈ K {(w₀, p.1)}}

/-- Round-trip identity: lowering a lifted Update recovers the original.

    `↓(↑D) = D` because the singleton context `{(w₀, g)}` passes through ↑
    with only `(w₀, g)` as witness, leaving exactly the pairs `h` with `D g h`. -/
theorem lowerPW_liftPW {W E : Type*} (D : Update (Assignment E)) (w₀ : W) :
    lowerPW (liftPW D) w₀ = D := by
  ext ⟨g, h⟩
  constructor
  · intro hm
    show g ~[D] h
    simp only [lowerPW, liftPW, Set.mem_ofPred_eq] at hm
    obtain ⟨q, hq, h1, h2⟩ := hm
    cases hq; exact h2
  · intro hD
    show (w₀, h) ∈ liftPW D {(w₀, g)}
    simp only [liftPW, Set.mem_ofPred_eq]
    exact ⟨(w₀, g), rfl, rfl, hD⟩

/-- ↑ is injective: distinct DRSs yield distinct state updates.

    Follows from the round-trip: `D = ↓(↑D)`, so `↑D₁ = ↑D₂` implies
    `D₁ = ↓(↑D₁) = ↓(↑D₂) = D₂`. Requires `W` to be nonempty for the
    lowering witness world. -/
theorem liftPW_injective {W E : Type*} [Nonempty W] (D₁ D₂ : Update (Assignment E))
    (h : liftPW (W := W) D₁ = liftPW D₂) :
    D₁ = D₂ := by
  have w₀ : W := Classical.arbitrary W
  calc D₁ = lowerPW (liftPW D₁) w₀ := (lowerPW_liftPW D₁ w₀).symm
    _ = lowerPW (liftPW D₂) w₀ := by rw [h]
    _ = D₂ := lowerPW_liftPW D₂ w₀

/-- Lifted pointwise DRSs are always distributive.

    `↑D` processes each element of the input state independently — the output
    at `p` depends only on whether some `q ∈ s` satisfies `D q.2 p.2` with
    matching world `p.1 = q.1`. This is exactly the singleton decomposition
    `(↑D)(s) = ⋃_{i∈s} (↑D)({i})`, which is the definition of distributivity. -/
theorem liftPW_preserves_distributive {W E : Type*} (D : Update (Assignment E)) :
    IsDistributive (liftPW (W := W) D) := by
  intro s; ext p
  constructor
  · intro hp
    simp only [liftPW, Set.mem_ofPred_eq] at hp
    obtain ⟨q, hq, h1, h2⟩ := hp
    exact ⟨q, hq, by simp only [liftPW, Set.mem_ofPred_eq]; exact ⟨q, rfl, h1, h2⟩⟩
  · rintro ⟨i, hi, hp⟩
    simp only [liftPW, Set.mem_ofPred_eq] at hp ⊢
    obtain ⟨q, hq, h1, h2⟩ := hp
    cases hq; exact ⟨i, hi, h1, h2⟩

/-- ↑↓ ≠ id: there exist irreducibly update-theoretic meanings K such that
    liftPW (lowerPW K w₀) ≠ K.

    The simplest witness is `K _ = {(w₀, g₀)}` (constant function ignoring
    input). Then `K ∅ = {(w₀, g₀)}`, but `liftPW (lowerPW K w₀) ∅ = ∅`
    because ↑ has no input pairs to draw.

    Requires `Nonempty W` and `Nonempty E` to construct the witness. -/
theorem liftPW_lowerPW_not_id {W E : Type*} [Nonempty W] [Nonempty E] :
    ∃ (K : State.CCP W E) (w₀ : W), liftPW (lowerPW K w₀) ≠ K := by
  let w₀ : W := Classical.arbitrary W
  let g₀ : Assignment E := λ _ => Classical.arbitrary E
  let K : State.CCP W E := λ _ => {(w₀, g₀)}
  use K, w₀
  intro heq
  have h₁ : liftPW (lowerPW K w₀) ∅ = (∅ : State W E) := by
    ext p; simp only [liftPW, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨q, hq, _, _⟩; exact hq
  have h₂ : K ∅ = ({(w₀, g₀)} : State W E) := rfl
  rw [heq] at h₁
  rw [h₂] at h₁
  have : (w₀, g₀) ∈ ({(w₀, g₀)} : State W E) := rfl
  rw [h₁] at this
  exact this

/- Charlow's thesis (meta-theoretical): destructive update is not empirically
problematic. Assignment modification is shared between static and dynamic
systems. The static/dynamic divide reduces to a single operator ↑ determining
whether modified assignments are retained. This claim is demonstrated by the
theorems above (`static_dynamic_same_truth`, `destructive_preserves_truth`,
`liftPW_preserves_distributive`), not by a single formal statement. -/

-- ════════════════════════════════════════════════════════════════
-- Effect-functor lookup interface — Charlow as `M = Set` instance
-- ════════════════════════════════════════════════════════════════

/-- Charlow's `State W E = Set (W × Assignment E)` as the **nondeterministic**
(`M = Set`) instance of the fibered lookup interface. The lookup at
variable `v` at world `w` yields `{ g v | (w, g) ∈ s }` — one alternative
per assignment containing `w`. The empty set is the falsifier (no
assignment defines `v` at `w`): Charlow rejects a value-level `⋆`, so
compositional negation is preserved by the empty-set convention. The
fibered projection is lossy — the native joint state records which worlds
pair with which assignments beyond what a single `(v, w)` query reveals;
the `supportCollapse` bridge below collapses genuinely-uncertain states. -/
instance instCharlowHasFiberedLookup (W E : Type) :
    DynamicSemantics.HasFiberedLookup Set (State W E) Nat W E where
  iLookup s v w := { e | ∃ g : Assignment E, (w, g) ∈ s ∧ g v = e }

-- ════════════════════════════════════════════════════════════════
-- Bridge natural transformations — Hofmann ⇄ Charlow
-- ════════════════════════════════════════════════════════════════

/-- **Hofmann ↪ Charlow**: lift an `ICDRT.Assignment` to a Charlow state on
the worlds where every `vars`-listed variable has a non-`⋆` referent.
At such worlds the resulting state has exactly one alternative — the
assignment forced by Hofmann's values on `vars` (free elsewhere).
At ⋆-worlds for any `vars`-listed variable, the world contributes no
alternatives. -/
def singletonLift {W E : Type} [Inhabited E]
    (worlds : Set W) (vars : Finset Nat) (i : ICDRT.Assignment W E) :
    State W E :=
  { p | p.1 ∈ worlds ∧
        (∀ v ∈ vars, i.indiv ⟨v⟩ p.1 ≠ Entity.star) ∧
        (∀ v ∈ vars,
          match i.indiv ⟨v⟩ p.1 with
          | .some e => p.2 v = e
          | .star => True) }

/-- **Charlow ↠ Hofmann**: collapse a Charlow state to a Hofmann-style
assignment by "agreement-or-`⋆`". At each world, if all alternatives
agree on `v`'s value, that's `v`'s value; otherwise `⋆`. Propositional
drefs are dropped (Charlow has no propositional-dref structure to
preserve). The reverse-image `singletonLift` ∘ `supportCollapse` loses
information whenever the Charlow state has genuine uncertainty. -/
noncomputable def supportCollapse {W E : Type}
    (s : State W E) : ICDRT.Assignment W E where
  prop _ := ∅
  indiv v w :=
    open Classical in
    if h : ∃ e : E, ∀ g : Assignment E, (w, g) ∈ s → g v.idx = e
      then Entity.some (Classical.choose h)
      else Entity.star

/-- **Bridge / section-retraction**: on the deterministic image,
`supportCollapse ∘ singletonLift = id` for individual variables in the
lift's `vars` set, at worlds in the lift's `worlds` set, where every
listed variable has a non-`⋆` referent. (Outside this domain the maps
behave differently — `singletonLift` produces an empty state at ⋆-worlds,
and `supportCollapse` falls through to `⋆`.)

This is a section/retraction relationship in the spirit of
`Function.LeftInverse`, witnessing that `singletonLift` injects Hofmann
states into Charlow states without information loss on its image. The
reverse direction (`singletonLift ∘ supportCollapse`) is *not* the
identity — collapsing genuine Charlow uncertainty to `⋆` and then
re-singleton-lifting forgets which alternatives were possible. -/
theorem supportCollapse_singletonLift {W E : Type} [Inhabited E]
    (worlds : Set W) (vars : Finset Nat) (i : ICDRT.Assignment W E)
    (v : IVar) (w : W) (hw : w ∈ worlds) (hv : v.idx ∈ vars)
    (hall : ∀ u ∈ vars, i.indiv ⟨u⟩ w ≠ Entity.star) :
    (supportCollapse (singletonLift worlds vars i)).indiv v w =
      i.indiv v w := by
  -- Recover the entity v points to at w
  obtain ⟨e₀, he₀⟩ : ∃ e, i.indiv v w = Entity.some e := by
    cases h : i.indiv v w with
    | some e => exact ⟨e, rfl⟩
    | star =>
      cases v
      exact absurd h (hall _ hv)
  -- Build a witness assignment g₀ at world w
  let g₀ : Assignment E := fun n =>
    if hn : n ∈ vars then
      match i.indiv ⟨n⟩ w with
      | .some e => e
      | .star => default
    else default
  have hg₀ : (w, g₀) ∈ singletonLift worlds vars i := by
    refine ⟨hw, hall, ?_⟩
    intro v' hv'
    show match i.indiv ⟨v'⟩ w with | .some e => g₀ v' = e | .star => True
    cases h : i.indiv ⟨v'⟩ w with
    | some e =>
      show g₀ v' = e
      simp only [g₀, dite_eq_left hv', h]
    | star => trivial
  -- The chosen value equals e₀
  have hkey : ∀ g : Assignment E,
      (w, g) ∈ singletonLift worlds vars i → g v.idx = e₀ := by
    intro g ⟨_, _, hmatch⟩
    have hfix := hmatch v.idx hv
    have : i.indiv ⟨v.idx⟩ w = Entity.some e₀ := by cases v; exact he₀
    rw [this] at hfix
    exact hfix
  have hex : ∃ e : E, ∀ g : Assignment E,
      (w, g) ∈ singletonLift worlds vars i → g v.idx = e := ⟨e₀, hkey⟩
  -- Unfold supportCollapse and discharge
  show (open Classical in
    if h : ∃ e : E, ∀ g : Assignment E,
      (w, g) ∈ singletonLift worlds vars i → g v.idx = e
      then Entity.some (Classical.choose h)
      else Entity.star) = i.indiv v w
  rw [dite_eq_left hex, he₀]
  congr 1
  -- Classical.choose hex satisfies the property; pin it down via g₀
  have hch := Classical.choose_spec hex g₀ hg₀
  have hg₀_v : g₀ v.idx = e₀ := hkey g₀ hg₀
  rw [← hch, hg₀_v]

-- ════════════════════════════════════════════════════════════════
-- Anaphora resolution: no propositional drefs
-- ════════════════════════════════════════════════════════════════

/-! Charlow's `State W E = Set (W × Assignment E)` deliberately carries
**no propositional-dref structure**, so the bathroom-sentence blocking
theorem (`counterfactual_blocks_veridical`, `ICDRT/Basic.lean`) — whose
every hypothesis is about propositional drefs — has no analogue here.
The same anaphora-under-negation phenomenon ("There isn't a bathroom.
#It is upstairs.") is handled by **alternative-set filtering** — a
negative antecedent yields an empty alternative set, which by the
empty-set falsifier makes downstream lookup empty. -/

/-! ### Truth conditions as cylindrification

The static and the dynamic existential have the same truth conditions, the cylindrification of
the body along the bound variable. -/

end Charlow2019
