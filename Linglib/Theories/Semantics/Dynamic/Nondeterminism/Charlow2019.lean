/-
Where is the destructive update problem?.

Destructive update is not empirically problematic: assignment modification
is shared between static and dynamic systems. The static/dynamic divide
reduces to a single operator ↑ determining whether modified assignments
are retained.

-/

import Linglib.Theories.Semantics.Dynamic.DPL.Basic
import Linglib.Theories.Semantics.Dynamic.Core.CCP
import Linglib.Theories.Semantics.Dynamic.Context

namespace Semantics.Dynamic.Charlow2019

open DPL
open Semantics.Dynamic.Core

/-- Truth at an assignment: K True at g ⟺ ∃h. K g h (Charlow's (7)). -/
def trueAt {E : Type*} (K : DPLRel E) (g : Assignment E) : Prop :=
  ∃ h, K g h

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
    exact ⟨(g.update 6 x).update 6 y, g.update 6 x,
      ⟨x, rfl, by simpa⟩, y, rfl, by simpa⟩

/-- Static ↑: evaluates truth, discards modified assignment (Table 1, row 1). -/
def staticExists {E : Type*} (x : Nat) (body : Assignment E → Prop) : DPLRel E :=
  DPLRel.atom (λ g => ∃ d : E, body (Assignment.update g x d))

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
  refine ⟨0, λ _ => True, λ _ => e₁, Assignment.update (λ _ => e₁) 0 e₂, ?_⟩
  constructor
  · exact ⟨e₂, rfl, trivial⟩
  · intro heq; exact hne (congr_fun heq 0 |>.symm ▸ by simp)

/-- Static and dynamic agree on truth conditions (§4, §7). -/
theorem static_dynamic_same_truth {E : Type*}
    (x : Nat) (body : Assignment E → Prop) (g : Assignment E) :
    trueAt (staticExists x body) g ↔ trueAt (dynamicExists x body) g := by
  simp only [trueAt, staticExists, dynamicExists, DPLRel.atom, DPLRel.exists_]
  constructor
  · rintro ⟨h, heq, d, hbody⟩
    subst heq
    exact ⟨g.update x d, d, rfl, hbody⟩
  · rintro ⟨_, d, _, hbody⟩
    exact ⟨g, rfl, d, hbody⟩

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
  let h : Assignment E := Assignment.update g 0 e₂
  refine ⟨g, h, ?_, ?_, ?_⟩
  · intro heq; exact hne (by simpa using congr_fun heq 0)
  · exact ⟨DPLRel.exists_ 0 (DPLRel.atom (λ g' => g' 0 = e₂)),
           e₂, rfl, by simp⟩
  · refine ⟨DPLRel.exists_ 0 (DPLRel.atom (λ g' => g' 0 = e₁)),
            e₁, ?_, by simp⟩
    funext n; dsimp [h, g, Assignment.update]; split <;> rfl

/-- Non-distributive negation (28): removes from s points that survive φ. -/
def stateNeg {W E : Type*} (φ : StateCCP W E) : StateCCP W E :=
  λ s => {i ∈ s | i ∉ φ s}

/-- Distributive negation (29): tests each point individually. -/
def stateDistNeg {W E : Type*} (φ : StateCCP W E) : StateCCP W E :=
  λ s => {i ∈ s | φ {i} = ∅}

/-- Partition by assignment: groups points sharing the same assignment (Charlow's (35)). -/
def partByAssignment {W E : Type*} (s : State W E) : Set (State W E) :=
  {t | t ⊆ s ∧ t.Nonempty ∧ ∀ i ∈ t, ∀ j ∈ t, i.2 = j.2}

/-- Anaphorically distributive: processes each assignment-group separately (Charlow's (39)). -/
def anaphoricallyDistributive {W E : Type*} (φ : StateCCP W E) : Prop :=
  ∀ s, φ s = {p | ∃ t ∈ partByAssignment s, p ∈ φ t}

/-- Every distributive meaning is anaphorically distributive. -/
theorem distributive_implies_anaphoric {W E : Type*} (φ : StateCCP W E) :
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

/- Charlow's thesis (meta-theoretical): destructive update is not empirically
problematic. Assignment modification is shared between static and dynamic
systems. The static/dynamic divide reduces to a single operator ↑ determining
whether modified assignments are retained. This claim is demonstrated by the
theorems above (`static_dynamic_same_truth`, `destructive_preserves_truth`),
not by a single formal statement. -/

-- ════════════════════════════════════════════════════════════════
-- Effect-functor lookup interface — Charlow as `M = Set` instance
-- ════════════════════════════════════════════════════════════════

/-- Charlow's `State W E = Set (W × Assignment E)` as the **nondeterministic**
(`M = Set`) instance of the unified lookup interface. The lookup at
variable `v` at world `w` yields `{ g v | (w, g) ∈ s }` — one alternative
per assignment containing `w`. Empty set is the falsifier (no assignment
defines `v` at `w`).

## SEAM (Falsifier, Seam 1): Charlow commits to `∅` as the no-referent
case. Bivalence is rejected — there is no `Entity.star` analog at the
value level. Compositional negation is preserved by the empty-set
convention; bridge to Hofmann via `supportCollapse` collapses
genuinely-uncertain states. -/
instance instCharlowHasFiberedLookup (W E : Type) :
    Semantics.Dynamic.Context.HasFiberedLookup Set (State W E) Nat W E where
  iLookup s v w := { e | ∃ g : Assignment E, (w, g) ∈ s ∧ g v = e }

/-- **Charlow as joint-state**: `State W E = Set (W × Assignment E)` is
*natively* a joint set over (world, assignment) pairs — no marginalization
needed. The `joint` field is essentially the identity, modulo rendering
`Assignment E = Nat → E` as the function `V → E` expected by the
typeclass.

## SEAM (Seam 2): This declaration commits Charlow empirically to having
joint structure to lose. The fibered `iLookup` projection of this state
is lossy — it discards which worlds were paired with which assignments
beyond what a single `(v, w)` query reveals. -/
instance instCharlowHasJointState (W E : Type) :
    Semantics.Dynamic.Context.HasJointState Set (State W E) Nat W E where
  joint s := s

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
-- ## SEAM 6 (Anaphora resolution mechanism) — concretized
-- ════════════════════════════════════════════════════════════════

/-! Charlow's `State W E = Set (W × Assignment E)` deliberately carries
**no propositional-dref structure**. Anaphora-under-negation phenomena
that ICDRT solves by propositional drefs (e.g. the bathroom-sentence
theorem `Semantics.Dynamic.Context.counterfactual_blocks_veridical`)
are solved here by **alternative-set filtering** — a negative
antecedent yields an empty alternative set, which by the empty-set
falsifier (Seam 1) makes downstream lookup empty.

Concretely: Charlow does **not** instantiate `HasPropDrefs`, and
the typeclass theorem `counterfactual_blocks_veridical` (which lives
over `[HasPropDrefs Ctx P W]` only — independent of the effect functor
`M`) does not apply here. Attempting to write
`HasPropDrefs (State W E) P W` would require inventing a `pLookup`
that doesn't exist in Charlow's framework.

This is **the seam working as intended**: the unification at
`HasFiberedLookup` (the lookup signature) is honest, and the divergence
at the resolution-mechanism layer is preserved as a typeclass-instance
gap, not papered over by a phony `pLookup` definition. The ICDRT and
Charlow analyses of the same empirical phenomenon (e.g.
"There isn't a bathroom. #It is upstairs.") thus live as
non-interreducible theorems in their respective files. -/

end Semantics.Dynamic.Charlow2019
