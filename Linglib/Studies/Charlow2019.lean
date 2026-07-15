import Linglib.Semantics.Dynamic.DPL
import Linglib.Semantics.Dynamic.ContextChange
import Linglib.Semantics.Dynamic.Lookup
import Linglib.Semantics.Dynamic.ICDRT.Defs
import Linglib.Core.Logic.CylindricAlgebra

/-!
# Charlow (2019): Where Is the Destructive Update Problem?
[charlow-2019]

Destructive update is not empirically problematic: assignment modification
is shared between static and dynamic systems. The static/dynamic divide
reduces to a single operator ↑ determining whether modified assignments
are retained.
-/

namespace Semantics.Dynamic.Charlow2019

open DPL
open Semantics.Dynamic.Core

/-- Truth at an assignment: K True at g ⟺ ∃h. K g h (Charlow's (7)). -/
def trueAt {E : Type*} (K : DPLRel E) (g : Assignment E) : Prop :=
  ∃ h, K g h

/-- `DPLRel.exists_`'s inline pointwise update equals `Function.update`. -/
private theorem update_eq_ite {E : Type*} (g : Assignment E) (x : Nat) (d : E) :
    (fun n => if n = x then d else g n) = Function.update g x d := by
  funext n; simp [Function.update_apply]

/-- Destructive update preserves truth conditions (§4). -/
theorem destructive_preserves_truth {E : Type*}
    (P Q : E → Prop) (g : Assignment E) :
    trueAt (DPLRel.conj
      (DPLRel.exists_ 6 (DPLRel.atom (λ g' => P (g' 6))))
      (DPLRel.exists_ 6 (DPLRel.atom (λ g' => Q (g' 6)))))
    g ↔ (∃ x, P x) ∧ (∃ y, Q y) := by
  simp only [trueAt, DPLRel.conj, DPLRel.exists_, DPLRel.atom]
  constructor
  · rintro ⟨h, k, ⟨d₁, hk, hP⟩, d₂, hh, hQ⟩
    subst hk; subst hh
    exact ⟨⟨d₁, by simpa using hP⟩, ⟨d₂, by simpa using hQ⟩⟩
  · rintro ⟨⟨x, hPx⟩, ⟨y, hQy⟩⟩
    exact ⟨Function.update (Function.update g 6 x) 6 y, Function.update g 6 x,
      ⟨x, update_eq_ite g 6 x, by simpa⟩,
      y, update_eq_ite (Function.update g 6 x) 6 y, by simpa⟩

/-- Static ↑: evaluates truth, discards modified assignment (Table 1, row 1). -/
def staticExists {E : Type*} (x : Nat) (body : Assignment E → Prop) : DPLRel E :=
  DPLRel.atom (λ g => ∃ d : E, body (Function.update g x d))

/-- Dynamic ↑: retains modified assignment (Table 1, row 2). -/
def dynamicExists {E : Type*} (x : Nat) (body : Assignment E → Prop) : DPLRel E :=
  DPLRel.exists_ x (DPLRel.atom (λ g => body g))

/-- Static existential is a test: output = input. -/
theorem static_is_test {E : Type*} (x : Nat) (body : Assignment E → Prop)
    (g h : Assignment E) :
    staticExists x body g h → g = h := by
  intro ⟨heq, _⟩; exact heq

/-- Dynamic existential can change the assignment. -/
theorem dynamic_changes_assignment {E : Type*} [Nontrivial E] :
    ∃ (x : Nat) (body : Assignment E → Prop) (g h : Assignment E),
      dynamicExists x body g h ∧ g ≠ h := by
  obtain ⟨e₁, e₂, hne⟩ := exists_pair_ne E
  refine ⟨0, λ _ => True, λ _ => e₁, Function.update (λ _ => e₁) 0 e₂, ?_⟩
  constructor
  · exact ⟨e₂, update_eq_ite _ 0 e₂, trivial⟩
  · intro heq; exact hne (congr_fun heq 0 |>.symm ▸ by simp)

/-- Static and dynamic agree on truth conditions (§4, §7). -/
theorem static_dynamic_same_truth {E : Type*}
    (x : Nat) (body : Assignment E → Prop) (g : Assignment E) :
    trueAt (staticExists x body) g ↔ trueAt (dynamicExists x body) g := by
  simp only [trueAt, staticExists, dynamicExists, DPLRel.atom, DPLRel.exists_]
  constructor
  · rintro ⟨h, heq, d, hbody⟩
    subst heq
    exact ⟨Function.update g x d, d, update_eq_ite g x d,
      (update_eq_ite g x d).symm ▸ hbody⟩
  · rintro ⟨_, d, _, hbody⟩
    exact ⟨g, rfl, d, update_eq_ite g x d ▸ hbody⟩

/-- Reachable: h is reachable from g via some DPL formula (Charlow's (24)). -/
def reachable {E : Type*} (g h : Assignment E) : Prop :=
  ∃ φ : DPLRel E, φ g h

/-- Reachability is reflexive. -/
theorem reachable_refl {E : Type*} (g : Assignment E) : reachable g g :=
  ⟨DPLRel.atom (λ _ => True), rfl, trivial⟩

/-- Reachability is transitive (via dynamic conjunction). -/
theorem reachable_trans {E : Type*} {g h k : Assignment E}
    (hgh : reachable g h) (hhk : reachable h k) : reachable g k := by
  obtain ⟨φ, hφ⟩ := hgh
  obtain ⟨ψ, hψ⟩ := hhk
  exact ⟨DPLRel.conj φ ψ, h, hφ, hψ⟩

/-- Antisymmetry fails: distinct assignments can be mutually reachable (§8). -/
theorem antisymmetry_fails {E : Type*} [Nontrivial E] :
    ∃ (g h : Assignment E), g ≠ h ∧ reachable g h ∧ reachable h g := by
  obtain ⟨e₁, e₂, hne⟩ := exists_pair_ne E
  let g : Assignment E := λ _ => e₁
  let h : Assignment E := Function.update g 0 e₂
  refine ⟨g, h, ?_, ?_, ?_⟩
  · intro heq; exact hne (by simpa [g, h] using congr_fun heq 0)
  · exact ⟨DPLRel.exists_ 0 (DPLRel.atom (λ g' => g' 0 = e₂)),
           e₂, update_eq_ite g 0 e₂, by simp⟩
  · refine ⟨DPLRel.exists_ 0 (DPLRel.atom (λ g' => g' 0 = e₁)),
            e₁, ?_, by simp⟩
    funext n
    by_cases hn : n = 0 <;> simp [hn, g, h, Function.update_apply]

/-- Charlow's context type: a set of world-assignment pairs. -/
abbrev State (W E : Type*) := Set (W × Assignment E)

/-- Context change potential over Charlow's contexts. -/
abbrev State.CCP (W E : Type*) := Semantics.Dynamic.Core.CCP (W × Assignment E)

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
  ext p; simp only [Set.mem_setOf_eq]
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
  λ s => {p | ∃ q ∈ s, p.1 = q.1 ∧ D q.2 p.2}

/-- Charlow's ↓: extract a pointwise Update from a state update by
    evaluating K on a singleton context at an arbitrary world. -/
def lowerPW {W E : Type*} (K : State.CCP W E) (w₀ : W) : Update (Assignment E) :=
  λ g h => (w₀, h) ∈ K {(w₀, g)}

/-- Round-trip identity: lowering a lifted Update recovers the original.

    `↓(↑D) = D` because the singleton context `{(w₀, g)}` passes through ↑
    with only `(w₀, g)` as witness, leaving exactly the pairs `h` with `D g h`. -/
theorem lowerPW_liftPW {W E : Type*} (D : Update (Assignment E)) (w₀ : W) :
    lowerPW (liftPW D) w₀ = D := by
  ext g h
  constructor
  · intro hm
    show D g h
    simp only [lowerPW, liftPW, Set.mem_setOf_eq] at hm
    obtain ⟨q, hq, h1, h2⟩ := hm
    cases hq; exact h2
  · intro hD
    show (w₀, h) ∈ liftPW D {(w₀, g)}
    simp only [liftPW, Set.mem_setOf_eq]
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
    simp only [liftPW, Set.mem_setOf_eq] at hp
    obtain ⟨q, hq, h1, h2⟩ := hp
    exact ⟨q, hq, by simp only [liftPW, Set.mem_setOf_eq]; exact ⟨q, rfl, h1, h2⟩⟩
  · rintro ⟨i, hi, hp⟩
    simp only [liftPW, Set.mem_setOf_eq] at hp ⊢
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
    ext p; simp only [liftPW, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
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
    Semantics.Dynamic.Context.HasFiberedLookup Set (State W E) Nat W E where
  iLookup s v w := { e | ∃ g : Assignment E, (w, g) ∈ s ∧ g v = e }

-- ════════════════════════════════════════════════════════════════
-- Bridge natural transformations — Hofmann ⇄ Charlow
-- ════════════════════════════════════════════════════════════════

/-- **Hofmann ↪ Charlow**: lift an `ICDRTAssignment` to a Charlow state on
the worlds where every `vars`-listed variable has a non-`⋆` referent.
At such worlds the resulting state has exactly one alternative — the
assignment forced by Hofmann's values on `vars` (free elsewhere).
At ⋆-worlds for any `vars`-listed variable, the world contributes no
alternatives. -/
def singletonLift {W E : Type} [Inhabited E]
    (worlds : Set W) (vars : Finset Nat) (i : ICDRTAssignment W E) :
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
    (s : State W E) : ICDRTAssignment W E where
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
    (worlds : Set W) (vars : Finset Nat) (i : ICDRTAssignment W E)
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
      simp only [g₀, dif_pos hv', h]
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
  rw [dif_pos hex, he₀]
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

-- ════════════════════════════════════════════════════════════════
-- § Cylindric algebra bridges
-- ════════════════════════════════════════════════════════════════
--
-- Charlow's `staticExists` / `dynamicExists` predicates have an
-- algebraic interpretation: both reduce to `cylindrify` from
-- `Core.CylindricAlgebra`. These bridges previously lived in
-- `Linglib/Core/Logic/CylindricAlgebra/DynamicSemantics.lean`, but a Core
-- file importing from Studies inverted the substrate→Studies dependency arrow.
-- They live here now: a Studies file importing the Core substrate it
-- depends on is layering-legal.

section CylindricAlgebraBridges

open Core.CylindricAlgebra
open Semantics.Dynamic.DPL

/-- Static existential truth = cylindrification.

Charlow's `staticExists x body` tests whether `∃ d, body(g[x↦d])`,
which is exactly `cylindrify x body`. -/
theorem charlow_static_eq_cylindrify {E : Type*}
    (x : Nat) (body : Assignment E → Prop) (g : Assignment E) :
    trueAt (staticExists x body) g ↔ cylindrify x body g := by
  simp only [trueAt, staticExists, DPLRel.atom, cylindrify]
  exact ⟨fun ⟨_, rfl, d, hb⟩ => ⟨d, hb⟩, fun ⟨d, hb⟩ => ⟨g, rfl, d, hb⟩⟩

/-- Dynamic existential truth = cylindrification (same truth conditions). -/
theorem charlow_dynamic_eq_cylindrify {E : Type*}
    (x : Nat) (body : Assignment E → Prop) (g : Assignment E) :
    trueAt (dynamicExists x body) g ↔ cylindrify x body g := by
  rw [← static_dynamic_same_truth]
  exact charlow_static_eq_cylindrify x body g

end CylindricAlgebraBridges

end Semantics.Dynamic.Charlow2019
