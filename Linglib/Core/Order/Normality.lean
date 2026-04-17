import Mathlib.Data.Set.Basic

/-!
# Normality Orderings
@cite{kraus-magidor-1990} @cite{veltman-1996} @cite{rudin-2025a}

A normality ordering is a preorder on worlds encoding relative normalcy.
This structure appears in four places across formal semantics:

1. **@cite{kratzer-1981}**: ordering sources induce normality orderings
   for modal semantics (`Theories/Semantics/Modality/Kratzer.lean`)
2. **@cite{kraus-magidor-1990}**: plausibility orderings interpret
   default consequence, System P (`Core/Logic/BeliefRevision.lean`)
3. **@cite{veltman-1996}**: expectation patterns are normality orderings that
   get dynamically refined (`Theories/Semantics/Dynamic/UpdateSemantics/`)
4. **@cite{rudin-2025a}**: ordering-source updates for epistemic modals
   (`Theories/Semantics/Dynamic/Epistemic/`)

This module extracts the common mathematical core. The `PlausibilityOrder`
in `BeliefRevision.lean` adds a smoothness condition (every satisfiable
proposition has minimal elements); for finite types smoothness is automatic,
and `NormalityOrder` captures the shared preorder structure without it.

## Key definitions

- `NormalityOrder W`: preorder on worlds (reflexive, transitive)
- `optimal`: most normal worlds in a domain
- `refine`: promote φ-worlds — @cite{veltman-1996}'s key operation
- `connected`: every two worlds are comparable (totality)
- `fromProps`: construct from ordering source — @cite{kratzer-1981}'s pattern
- `respects` / persistence: defaults survive further updates
-/

namespace Core.Order

/-- A normality ordering: a preorder on worlds.
    `le w v` means w is at least as normal as v. -/
structure NormalityOrder (W : Type*) where
  le : W → W → Prop
  le_refl : ∀ w, le w w
  le_trans : ∀ u v w, le u v → le v w → le u w

namespace NormalityOrder

variable {W : Type*}

/-- Extensionality: two normality orderings are equal iff they agree on
    all pairs. Uses `propext` and `funext`. -/
@[ext]
theorem ext {a b : NormalityOrder W}
    (h : ∀ w v, a.le w v ↔ b.le w v) : a = b := by
  have hle : a.le = b.le := funext fun w => funext fun v => propext (h w v)
  cases a; cases b; simp only [mk.injEq]; exact hle

/-- An ordering is **connected** (total) if every two worlds are
    comparable: for all w, v, either w ≤ v or v ≤ w. -/
def connected (no : NormalityOrder W) : Prop :=
  ∀ w v, no.le w v ∨ no.le v w

/-- The total ordering: all worlds equally normal. This is the initial
    state before any defaults have been processed. -/
def total : NormalityOrder W where
  le := fun _ _ => True
  le_refl _ := True.intro
  le_trans _ _ _ _ _ := True.intro

/-- Strict normality: w is strictly more normal than v. -/
@[reducible] def slt (no : NormalityOrder W) (w v : W) : Prop :=
  no.le w v ∧ ¬no.le v w

/-- Optimal (most normal) worlds in a domain: those with no strictly
    more normal world in the domain.

    Equivalent to `PlausibilityOrder.minimal` in `BeliefRevision.lean`
    and to @cite{veltman-1996}'s opt_ε(σ). -/
def optimal (no : NormalityOrder W) (d : Set W) : Set W :=
  { w ∈ d | ∀ v ∈ d, no.le v w → no.le w v }

/-- Optimal worlds are in the domain. -/
theorem optimal_subset (no : NormalityOrder W) (d : Set W) :
    no.optimal d ⊆ d := fun _ hw => hw.1

/-- The total ordering is connected. -/
theorem total_connected : (total : NormalityOrder W).connected :=
  fun _ _ => Or.inl True.intro

/-- Under the total ordering, every world in the domain is optimal. -/
theorem total_all_optimal (d : Set W) :
    NormalityOrder.total.optimal d = d := by
  ext w
  simp only [optimal, total, Set.mem_setOf_eq]
  exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, fun _ _ _ => True.intro⟩⟩


-- ═══ Refinement ═══

/-- **Refinement**: promote φ-worlds in the normality ordering.

    After `refine no φ`, a non-φ-world can no longer be as normal as a
    φ-world: w ≤' v iff (w ≤ v) ∧ (φ v → φ w).

    This is @cite{veltman-1996}'s key operation. "Normally φ" updates the
    expectation pattern by intersecting with {⟨w,v⟩ : φ v → φ w}. -/
def refine (no : NormalityOrder W) (φ : W → Prop) : NormalityOrder W where
  le w v := no.le w v ∧ (φ v → φ w)
  le_refl w := ⟨no.le_refl w, id⟩
  le_trans u v w := fun ⟨huv, hφuv⟩ ⟨hvw, hφvw⟩ =>
    ⟨no.le_trans u v w huv hvw, fun hw => hφuv (hφvw hw)⟩

/-- Refinement strengthens: the refined ordering implies the original. -/
theorem refine_le_imp (no : NormalityOrder W) (φ : W → Prop)
    {w v : W} (h : (no.refine φ).le w v) : no.le w v := h.1

/-- After refinement by φ, a non-φ-world cannot be as normal as a φ-world. -/
theorem refine_separates (no : NormalityOrder W) (φ : W → Prop)
    {w v : W} (hv : φ v) (hw : ¬φ w) :
    ¬(no.refine φ).le w v :=
  fun ⟨_, h⟩ => hw (h hv)

/-- After refinement, if v was ≤ w and v is a φ-world while w is not,
    then v strictly dominates w. -/
theorem refine_promotes (no : NormalityOrder W) (φ : W → Prop)
    {w v : W} (hv : φ v) (hw : ¬φ w) (hle : no.le v w) :
    (no.refine φ).slt v w :=
  ⟨⟨hle, fun _ => hv⟩, refine_separates no φ hv hw⟩


-- ═══ Respect and Persistence ═══

/-- An ordering **respects** φ if it already promotes φ-worlds:
    whenever w ≤ v and v satisfies φ, then w satisfies φ too.

    This captures @cite{veltman-1996}'s notion of "accepting" a default:
    σ accepts "normally φ" iff σ's pattern already respects φ. -/
def respects (no : NormalityOrder W) (φ : W → Prop) : Prop :=
  ∀ w v, no.le w v → φ v → φ w

/-- Refinement by φ always produces an ordering that respects φ. -/
theorem refine_respects (no : NormalityOrder W) (φ : W → Prop) :
    (no.refine φ).respects φ := fun _ _ ⟨_, h⟩ => h

/-- **Persistence**: if an ordering respects φ, further refinement by
    any ψ still respects φ. Defaults are not undone by later defaults.

    @cite{veltman-1996}, Proposition 3.6(iv). -/
theorem refine_preserves_respects (no : NormalityOrder W) (φ ψ : W → Prop)
    (h : no.respects φ) : (no.refine ψ).respects φ :=
  fun w v ⟨hle, _⟩ => h w v hle

/-- When an ordering respects φ, its restriction to φ-worlds is the same
    as the full ordering: refinement is idempotent on respected defaults. -/
theorem respects_refine_iff (no : NormalityOrder W) (φ : W → Prop)
    (h : no.respects φ) {w v : W} :
    (no.refine φ).le w v ↔ no.le w v :=
  ⟨fun ⟨hle, _⟩ => hle, fun hle => ⟨hle, h w v hle⟩⟩


/-- **Idempotency**: refining by φ twice is the same as refining once.

    @cite{veltman-1996}, Proposition 3.6(ii): (ε ∘ e) ∘ e = ε ∘ e. -/
theorem refine_idempotent (no : NormalityOrder W) (φ : W → Prop) :
    (no.refine φ).refine φ = no.refine φ :=
  ext fun _ _ => (respects_refine_iff (no.refine φ) φ (refine_respects no φ))

/-- **Commutativity**: the order of refinements doesn't matter.

    Follows from refinement being intersection with a set of pairs:
    (ε ∘ e₁) ∘ e₂ = ε ∩ R(e₁) ∩ R(e₂) = (ε ∘ e₂) ∘ e₁. -/
theorem refine_comm (no : NormalityOrder W) (φ ψ : W → Prop) :
    (no.refine φ).refine ψ = (no.refine ψ).refine φ :=
  ext fun _ _ => ⟨fun ⟨⟨h, hφ⟩, hψ⟩ => ⟨⟨h, hψ⟩, hφ⟩,
                  fun ⟨⟨h, hψ⟩, hφ⟩ => ⟨⟨h, hφ⟩, hψ⟩⟩

/-- Refining by the universal property is the identity. -/
theorem refine_univ (no : NormalityOrder W) :
    no.refine (fun _ => True) = no :=
  ext fun _ _ => ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, fun _ => True.intro⟩⟩

/-- Refining by the empty property is the identity (vacuously). -/
theorem refine_empty (no : NormalityOrder W) :
    no.refine (fun _ => False) = no :=
  ext fun _ _ => ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, fun hf => hf.elim⟩⟩

/-- **Respecting ordering equality**: if an ordering respects φ, then
    refining by φ gives back the same ordering.

    @cite{veltman-1996}: ε ∘ e = ε when e is already a default in ε. -/
theorem refine_of_respects (no : NormalityOrder W) (φ : W → Prop)
    (h : no.respects φ) : no.refine φ = no :=
  ext fun _ _ => respects_refine_iff no φ h


-- ═══ Connectedness and Optimality ═══

/-- Under a **connected** ordering that respects φ, all optimal worlds
    in a domain satisfy φ — provided the domain has at least one φ-world.

    This generalizes `refine_total_optimal` beyond the total ordering.
    Connectedness is essential: without it, a non-φ-world can be optimal
    by being incomparable with all φ-worlds.

    Note: @cite{veltman-1996} Proposition 3.4(i) states this without the
    connectedness assumption, but his proof implicitly relies on states
    being reachable from the total ordering, which ensures connectedness
    after a single refinement. After multiple refinements by "crossing"
    properties, connectedness can fail and the result no longer holds
    for arbitrary respecting orderings. -/
theorem optimal_of_respects_connected (no : NormalityOrder W)
    (φ : W → Prop) (d : Set W) (hresp : no.respects φ)
    (hconn : no.connected) (hex : ∃ w ∈ d, φ w) :
    no.optimal d ⊆ { w ∈ d | φ w } := by
  intro w ⟨hwd, hopt⟩
  obtain ⟨v, hvd, hφv⟩ := hex
  refine ⟨hwd, ?_⟩
  rcases hconn w v with hwv | hvw
  · exact hresp w v hwv hφv
  · exact hresp w v (hopt v hvd hvw) hφv


-- ═══ Key Theorem ═══

/-- **Refinement makes φ-worlds optimal.** Starting from the total
    ordering, refining by φ makes the optimal worlds in any domain d
    exactly the φ-worlds in d — provided at least one φ-world exists.

    This is the mathematical core of Veltman's system: "normally φ"
    followed by "presumably φ" succeeds, because refinement guarantees
    φ-worlds become the most normal. -/
theorem refine_total_optimal (φ : W → Prop) (d : Set W)
    (hex : ∃ w ∈ d, φ w) :
    (total.refine φ).optimal d = { w ∈ d | φ w } := by
  ext w
  constructor
  · -- → : optimal implies φ
    intro ⟨hwd, hopt⟩
    obtain ⟨v, hvd, hφv⟩ := hex
    refine ⟨hwd, ?_⟩
    by_contra hnφw
    -- v ≤' w: total gives True, φ w → φ v is vacuous since ¬φ w
    have hle : (total.refine φ).le v w :=
      ⟨True.intro, fun h => absurd h hnφw⟩
    -- By optimality: w ≤' v, giving φ v → φ w. With φ v → φ w. Contradiction.
    exact hnφw ((hopt v hvd hle).2 hφv)
  · -- ← : φ-world is optimal
    intro ⟨hwd, hφw⟩
    exact ⟨hwd, fun _ _ _ => ⟨True.intro, fun _ => hφw⟩⟩

/-- An optimal φ-world under `no` remains optimal under `no.refine φ`.

    If w is optimal in d (no world in d strictly dominates it) and w
    satisfies φ, then w is still optimal in d after refinement by φ.
    This is the core lemma for coherence preservation (Proposition 4.7):
    refinement can't destroy the optimality of worlds that satisfy the
    refinement property. -/
theorem optimal_refine_of_mem (no : NormalityOrder W) (φ : W → Prop)
    (d : Set W) {w : W} (hopt : w ∈ no.optimal d) (hφ : φ w) :
    w ∈ (no.refine φ).optimal d :=
  ⟨hopt.1, fun v hv ⟨hle, _⟩ => ⟨hopt.2 v hv hle, fun _ => hφ⟩⟩

/-- Refinement preserves nonemptiness of optimal sets when the original
    optimal set contains φ-worlds. -/
theorem optimal_refine_nonempty (no : NormalityOrder W) (φ : W → Prop)
    (d : Set W) (hex : ∃ w ∈ no.optimal d, φ w) :
    (no.refine φ).optimal d |>.Nonempty := by
  obtain ⟨w, hopt, hφ⟩ := hex
  exact ⟨w, optimal_refine_of_mem no φ d hopt hφ⟩

/-- When the ordering respects φ, no non-φ-world can dominate a φ-world.
    Combined with optimality, this constrains which worlds can be optimal. -/
theorem respects_no_domination (no : NormalityOrder W) (φ : W → Prop)
    (hresp : no.respects φ) {w v : W} (hv : φ v) (hw : ¬φ w) :
    ¬no.le w v :=
  fun hle => hw (hresp w v hle hv)


-- ═══ Construction from Propositions ═══

/-- Construct a normality ordering from a list of propositions.
    w ≤ v iff every proposition satisfied by v is also satisfied by w.

    This is @cite{kratzer-1981}'s ordering source construction:
    {p ∈ A : v ∈ p} ⊆ {p ∈ A : w ∈ p}.

    Equivalent to `atLeastAsGoodAs` in `Modality/Kratzer.lean` (computable)
    and `kratzerPlausibility` in `BeliefRevision.lean` (with smoothness). -/
def fromProps (props : List (W → Bool)) : NormalityOrder W where
  le w v := ∀ p ∈ props, p v = true → p w = true
  le_refl _ _ _ h := h
  le_trans _ _ _ huv hvw p hp hpw := huv p hp (hvw p hp hpw)

/-- The empty ordering source gives the total ordering. -/
theorem fromProps_nil {w v : W} : (fromProps ([] : List (W → Bool))).le w v :=
  fun _ h => nomatch h

/-- Adding a proposition to the ordering source refines it. -/
theorem fromProps_cons_le (p : W → Bool) (ps : List (W → Bool))
    {w v : W} (h : (fromProps (p :: ps)).le w v) :
    (fromProps ps).le w v :=
  fun q hq => h q (List.mem_cons_of_mem p hq)

/-- Refining from the total ordering always gives a connected ordering.

    In the total ordering, every pair is related in both directions.
    After one refinement by φ, the ordering `(φ v → φ w)` is still
    connected because material implication between truth values always
    holds in at least one direction.

    This does NOT generalize to arbitrary connected orderings: if only
    `w ≤ v` holds (not `v ≤ w`) and φ(v), ¬φ(w), neither refined
    direction holds. And after two refinements by "crossing" properties,
    connectedness can fail entirely. -/
theorem refine_total_connected (φ : W → Prop) :
    (total.refine φ : NormalityOrder W).connected := by
  intro w v
  by_cases hφw : φ w
  · left; exact ⟨True.intro, fun _ => hφw⟩
  · by_cases hφv : φ v
    · right; exact ⟨True.intro, fun h => absurd h hφw⟩
    · left; exact ⟨True.intro, fun h => absurd h hφv⟩

-- ═══ Darwiche-Pearl Representation Conditions ═══

/-! @cite{darwiche-pearl-1997}, Definition 8. Conditions on how a total
    pre-order (faithful assignment) may change under revision by μ.
    These are the representation-theorem equivalents of the iterated
    revision postulates C1–C4. They constrain how *any* ordering-based
    semantics — Kratzer modals, Lewis conditionals, Veltman defaults —
    should evolve under discourse update.

    `prior` and `post` are the orderings before and after revision by μ.
    Lower in the ordering = more normal/plausible. -/

/-- CR1: The ordering among μ-worlds is preserved. -/
@[reducible] def satisfies_CR1 (prior post : NormalityOrder W) (μ : W → Bool) : Prop :=
  ∀ w v, μ w = true → μ v = true →
    (prior.le w v ↔ post.le w v)

/-- CR2: The ordering among ¬μ-worlds is preserved. -/
@[reducible] def satisfies_CR2 (prior post : NormalityOrder W) (μ : W → Bool) : Prop :=
  ∀ w v, μ w = false → μ v = false →
    (prior.le w v ↔ post.le w v)

/-- CR3: If a μ-world was strictly below a ¬μ-world, it stays strictly below. -/
@[reducible] def satisfies_CR3 (prior post : NormalityOrder W) (μ : W → Bool) : Prop :=
  ∀ w v, μ w = true → μ v = false →
    prior.slt w v → post.slt w v

/-- CR4: If a μ-world was ≤ a ¬μ-world, it stays ≤. -/
@[reducible] def satisfies_CR4 (prior post : NormalityOrder W) (μ : W → Bool) : Prop :=
  ∀ w v, μ w = true → μ v = false →
    prior.le w v → post.le w v

end NormalityOrder
end Core.Order
