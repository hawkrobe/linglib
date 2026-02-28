import Linglib.Core.Order.Normality
import Linglib.Theories.Semantics.Dynamic.Effects.Default.Basic

/-!
# Expectation Frames — Veltman (1996) §4

@cite{veltman-1996}

Veltman calls §4 "the heart of the paper." Where §3 uses a single
normality ordering for all domains, §4 introduces **expectation frames**:
functions assigning a *per-domain* normality ordering. This enables
conditional defaults — "if φ then normally ψ" — where the ordering
is refined only for the φ-domain.

The key insight is the definition of **normal worlds** (Definition 4.3):
a world w is normal in πd not just when w is optimal in d under πd,
but when w is top-ranked in *every* subdomain d' ⊆ d containing w,
under πd'. This is how specificity works — a more specific exception
(governing a subdomain) can override a general default (governing a
superdomain) without the general default needing to "know about" the
exception.

## Key definitions

- `ExpFrame W`: function `Set W → NormalityOrder W`
- `ExpFrame.normal`: Def 4.3 — check all subdomains, not just d
- `ExpFrame.coherent`: Def 4.3(iii) — every non-empty d has normals
- `ExpFrame.refineAt`: Def 4.5 — refine pattern at domain d only
- `FrameState`: expectation state with a frame
- `condDefault`: Def 4.6 — conditional default update

## Key results

- `refineAt_preserves_coherent`: Prop 4.7 — coherence characterization
- `refineAt_comm_same`: refinement at one domain commutes
- `refineAt_comm_diff`: refinements at different domains commute

## Connection to §3

The unconditional "normally ψ" is "(ψ ∨ ¬ψ) ⇝ ψ", so it refines the
frame at d = W. The `ExpState` from `Basic.lean` corresponds to a
`FrameState` with a *constant* frame. For constant frames with
connected orderings, the §4 `normal` definition reduces to §3's
`optimal` (since `optimal` and "top in all subdomains" coincide
when every ordering is connected).
-/

namespace Semantics.Dynamic.Default

open Core.Order (NormalityOrder)

variable {W : Type*}


-- ═══ Expectation Frames ═══

/-- An **expectation frame**: a function assigning a normality ordering
    to each domain (subset of worlds).

    Veltman (1996), Definition 4.2: π assigns to every d ⊆ W an
    expectation pattern πd. Different domains may have different
    orderings — this is what enables conditional defaults. -/
structure ExpFrame (W : Type*) where
  /-- The per-domain normality ordering -/
  pattern : Set W → NormalityOrder W

/-- Extensionality for frames: two frames are equal iff they assign
    the same ordering to every domain. -/
@[ext]
theorem ExpFrame.ext {π₁ π₂ : ExpFrame W}
    (h : ∀ d, π₁.pattern d = π₂.pattern d) : π₁ = π₂ := by
  cases π₁; cases π₂; congr; funext d; exact h d

/-- The **normal worlds** in a domain under the frame.

    Veltman (1996), Definition 4.3(i–ii): w is normal in πd iff w ∈ d
    and for every subdomain d' ⊆ d such that w ∈ d', w is at least as
    normal as every v ∈ d' under πd'.

    This is stronger than just being optimal in d under πd: w must be
    top-ranked in *every* subdomain's pattern, not just the top-level
    one. This is how specificity works — a more specific exception
    (governing a subdomain) overrides a general default by making the
    world non-normal at the subdomain level. -/
def ExpFrame.normal (π : ExpFrame W) (d : Set W) : Set W :=
  { w ∈ d | ∀ d', d' ⊆ d → w ∈ d' → ∀ v ∈ d', (π.pattern d').le w v }

/-- A frame is **coherent** if every non-empty domain has at least
    one normal world.

    Veltman (1996), Definition 4.3(iii). -/
def ExpFrame.coherent (π : ExpFrame W) : Prop :=
  ∀ d : Set W, d.Nonempty → (π.normal d).Nonempty

/-- e is a **default in πd** iff d ∩ e ≠ ∅ and πd already respects e.

    Veltman (1996), Definition 4.2(ii): e is a default in πd iff
    d ∩ e ≠ ∅ and πd ∘ e = πd. Since `refine_of_respects` gives
    the latter iff `respects`, we use `respects` directly. -/
def ExpFrame.isDefault (π : ExpFrame W) (d : Set W) (e : W → Prop) :
    Prop :=
  (∃ w ∈ d, e w) ∧ (π.pattern d).respects e

/-- The **constant frame**: assigns the same ordering to every domain.
    This embeds §3's single-ordering setup into the §4 framework. -/
def ExpFrame.const (no : NormalityOrder W) : ExpFrame W :=
  ⟨fun _ => no⟩

/-- The **total frame**: assigns the total ordering to every domain.
    The initial state before any defaults have been processed. -/
def ExpFrame.total : ExpFrame W :=
  ExpFrame.const NormalityOrder.total


-- ═══ Frame Refinement ═══

open Classical in
/-- **Frame refinement**: refine the ordering at domain d only.

    Veltman (1996), Definition 4.5(ii):
    - π_{d∘e}(d') = πd' if d' ≠ d
    - π_{d∘e}(d) = πd ∘ e

    Unlike our earlier (incorrect) version that refined all d' ⊇ d,
    this modifies *only* the pattern at d. The effect on superdomains
    comes automatically through the `normal` computation, which checks
    all subdomains — so a refinement at d changes which worlds count as
    normal in any d' ⊇ d. -/
noncomputable def ExpFrame.refineAt (π : ExpFrame W) (d : Set W)
    (e : W → Prop) : ExpFrame W :=
  ⟨fun d' => if d' = d then (π.pattern d).refine e else π.pattern d'⟩

/-- Domains other than d are unchanged by refinement. -/
theorem ExpFrame.refineAt_unchanged (π : ExpFrame W) (d : Set W)
    (e : W → Prop) (d' : Set W) (h : d' ≠ d) :
    (π.refineAt d e).pattern d' = π.pattern d' := by
  unfold refineAt; exact if_neg h

/-- The target domain gets its ordering refined. -/
theorem ExpFrame.refineAt_target (π : ExpFrame W) (d : Set W)
    (e : W → Prop) :
    (π.refineAt d e).pattern d = (π.pattern d).refine e := by
  unfold refineAt; exact if_pos rfl


-- ═══ Frame State ═══

/-- An **expectation state with frame**: an information state paired
    with an expectation frame.

    Veltman's §4 notation: σ = ⟨π, s⟩ where π is a frame and
    s ⊆ W is the information state. This generalizes `ExpState`
    from §3 (which uses a single ordering). -/
structure FrameState (W : Type*) where
  /-- The information state -/
  info : Set W
  /-- The expectation frame -/
  frame : ExpFrame W

/-- Normal worlds in the current state: the most normal worlds
    in the info state according to the frame. -/
def FrameState.normal (σ : FrameState W) : Set W :=
  σ.frame.normal σ.info

/-- The initial frame state: all worlds possible, total frame. -/
def FrameState.init : FrameState W where
  info := Set.univ
  frame := ExpFrame.total

/-- Embed a §3 `ExpState` as a `FrameState` with constant frame. -/
def FrameState.ofExpState (σ : ExpState W) : FrameState W :=
  ⟨σ.info, ExpFrame.const σ.order⟩


-- ═══ Conditional Default Update ═══

section Classical
open Classical

/-- **Conditional default update**: "if φ then normally ψ".

    Veltman (1996), Definition 4.6. Given σ = ⟨π, s⟩:
    - Let d = ‖φ‖ — the set of *all* φ-worlds (not just those in s)
    - If d ∩ ‖ψ‖ = ∅, crash (the default is vacuous)
    - If π_{d∘ψ} is incoherent, crash
    - Otherwise, result is ⟨π_{d∘ψ}, s⟩

    Note: d = ‖φ‖ over all of W, not ‖φ‖ ∩ s. The frame is about the
    space of possible worlds; the info state restricts which are
    epistemically accessible but doesn't determine the default domain. -/
noncomputable def condDefault (φ ψ : W → Prop) (σ : FrameState W) :
    FrameState W :=
  let d : Set W := { w | φ w }
  let π' := σ.frame.refineAt d ψ
  if ¬(∃ w, φ w ∧ ψ w) then
    ⟨∅, σ.frame⟩  -- crash: d ∩ ‖ψ‖ = ∅
  else if ¬π'.coherent then
    ⟨∅, σ.frame⟩  -- crash: refined frame incoherent
  else
    ⟨σ.info, π'⟩

/-- **Unconditional default**: "normally ψ" = "(ψ ∨ ¬ψ) ⇝ ψ".

    Refines the frame at d = W (all worlds). -/
noncomputable def normallyFrame (ψ : W → Prop) (σ : FrameState W) :
    FrameState W :=
  condDefault (fun _ => True) ψ σ

/-- **Assertion** in the frame setting: eliminate non-φ-worlds. -/
def assertFrame (φ : W → Prop) (σ : FrameState W) : FrameState W :=
  ⟨{ w ∈ σ.info | φ w }, σ.frame⟩

/-- **Presumably test** in the frame setting: passes iff all normal
    worlds satisfy φ. -/
noncomputable def presumablyFrame (φ : W → Prop) (σ : FrameState W) :
    FrameState W :=
  if ∀ w ∈ σ.normal, φ w then σ else ⟨∅, σ.frame⟩

end Classical


-- ═══ Basic Properties ═══

/-- Assertion preserves the frame. -/
theorem assertFrame_preserves_frame (φ : W → Prop) (σ : FrameState W) :
    (assertFrame φ σ).frame = σ.frame := rfl

/-- Normal worlds are in the domain. -/
theorem ExpFrame.normal_subset (π : ExpFrame W) (d : Set W) :
    π.normal d ⊆ d := fun _ hw => hw.1


-- ═══ Frame Refinement Properties ═══

/-- **Commutativity at one domain**: refining by e₁ then e₂ at the same
    domain gives the same result as the reverse order. -/
theorem ExpFrame.refineAt_comm_same (π : ExpFrame W) (d : Set W)
    (e₁ e₂ : W → Prop) :
    (π.refineAt d e₁).refineAt d e₂ =
    (π.refineAt d e₂).refineAt d e₁ := by
  apply ExpFrame.ext; intro d'
  by_cases hd : d' = d
  · subst hd
    simp only [refineAt_target]
    exact NormalityOrder.refine_comm _ _ _
  · simp only [refineAt_unchanged _ d _ d' hd]

/-- **Commutativity at different domains**: refinements at da ≠ db
    commute trivially — they modify different entries. -/
theorem ExpFrame.refineAt_comm_diff (π : ExpFrame W) (da db : Set W)
    (ea eb : W → Prop) (h : da ≠ db) :
    (π.refineAt da ea).refineAt db eb =
    (π.refineAt db eb).refineAt da ea := by
  apply ExpFrame.ext; intro d'
  simp only [refineAt]
  by_cases hda : d' = da <;> by_cases hdb : d' = db
  · exact absurd (hda ▸ hdb) h
  · simp only [hda, h, Ne.symm h, if_true, if_false]
  · simp only [hdb, h, Ne.symm h, if_true, if_false]
  · simp only [hda, hdb, if_false]

/-- **Idempotency at frame level**: refining at d by e twice is the
    same as refining once. -/
theorem ExpFrame.refineAt_idempotent (π : ExpFrame W) (d : Set W)
    (e : W → Prop) :
    (π.refineAt d e).refineAt d e = π.refineAt d e := by
  apply ExpFrame.ext; intro d'
  by_cases hd : d' = d
  · subst hd
    simp only [refineAt_target]
    exact NormalityOrder.refine_idempotent _ _
  · simp only [refineAt_unchanged _ d _ d' hd]

/-- If πd already respects e, refinement at d is a no-op. -/
theorem ExpFrame.refineAt_of_respects (π : ExpFrame W) (d : Set W)
    (e : W → Prop) (h : (π.pattern d).respects e) :
    π.refineAt d e = π := by
  apply ExpFrame.ext; intro d'
  by_cases hd : d' = d
  · subst hd
    rw [refineAt_target]
    exact NormalityOrder.refine_of_respects _ _ h
  · exact refineAt_unchanged _ d _ d' hd

/-- After refinement at d, the pattern at d respects e. -/
theorem ExpFrame.refineAt_creates_respect (π : ExpFrame W) (d : Set W)
    (e : W → Prop) :
    ((π.refineAt d e).pattern d).respects e := by
  rw [refineAt_target]
  exact NormalityOrder.refine_respects _ _


-- ═══ Coherence Preservation ═══

/-- Refinement can only remove normal worlds, never add them.
    Because `refineAt` either preserves or strengthens the ordering
    at each subdomain, the normal condition is harder to satisfy. -/
theorem ExpFrame.refineAt_normal_mono (π : ExpFrame W) (d : Set W)
    (e : W → Prop) (d₀ : Set W) :
    (π.refineAt d e).normal d₀ ⊆ π.normal d₀ := by
  intro w ⟨hwd₀, hdom⟩
  refine ⟨hwd₀, fun d' hd' hwd' v hv => ?_⟩
  have h := hdom d' hd' hwd' v hv
  by_cases hd'_eq : d' = d
  · subst hd'_eq; rw [refineAt_target] at h; exact h.1
  · rw [refineAt_unchanged _ _ _ _ hd'_eq] at h; exact h

/-- **Coherence characterization** (Proposition 4.7): given coherent π
    with d ∩ e ≠ ∅, the refined frame π_{d∘e} is coherent iff there is
    no d' ⊇ d such that nπd' ⊆ d \ e.

    The condition "nπd' ⊆ d \ e" means all normal d'-worlds are in d
    but fail e. If this holds, refinement at d makes those worlds
    non-top (they don't satisfy e), potentially leaving no normals in
    the refined frame.

    Note: nπd' here uses the *original* frame π's normals, not the
    refined frame's. -/
theorem ExpFrame.refineAt_coherent_iff (π : ExpFrame W) (d : Set W)
    (e : W → Prop) (hcoh : π.coherent)
    (hne : ∃ w ∈ d, e w) :
    (π.refineAt d e).coherent ↔
    ¬∃ d', d ⊆ d' ∧ π.normal d' ⊆ { w ∈ d | ¬e w } := by
  obtain ⟨v₀, hv₀d, hev₀⟩ := hne
  constructor
  · -- →: refined coherent → no bad superdomain
    intro hcoh_ref ⟨d₀, hd_sub, hnorm_sub⟩
    have hd₀_ne : d₀.Nonempty := ⟨v₀, hd_sub hv₀d⟩
    obtain ⟨w, hw_ref⟩ := hcoh_ref d₀ hd₀_ne
    -- w is also normal in π (monotonicity), so w ∈ d ∧ ¬e w
    obtain ⟨hwd, hne_w⟩ := hnorm_sub (refineAt_normal_mono π d e d₀ hw_ref)
    -- But the refined pattern at d forces e w (using the e-witness v₀)
    have h := hw_ref.2 d hd_sub hwd v₀ hv₀d
    rw [refineAt_target] at h
    exact hne_w (h.2 hev₀)
  · -- ←: no bad superdomain → refined coherent
    intro hno_bad d₀ hd₀_ne
    by_cases hd_sub : d ⊆ d₀
    · -- d ⊆ d₀: find a surviving normal world
      -- nπd₀ ⊄ d \ e, so ∃ w ∈ nπd₀ with w ∉ d \ e
      have ⟨w, hw_norm, hw_ok⟩ :
          ∃ w ∈ π.normal d₀, w ∉ ({ w ∈ d | ¬e w } : Set W) := by
        by_contra h
        exact hno_bad ⟨d₀, hd_sub, fun x hx => by_contra fun hx' => h ⟨x, hx, hx'⟩⟩
      -- hw_ok : ¬(w ∈ d ∧ ¬e w), i.e., w ∉ d ∨ e w
      refine ⟨w, hw_norm.1, fun d' hd' hwd' v hv => ?_⟩
      by_cases hd'_eq : d' = d
      · -- d' = d: refined pattern demands (πd).le ∧ (e v → e w)
        rw [hd'_eq, refineAt_target]
        constructor
        · have := hw_norm.2 d' hd' hwd' v hv; rwa [hd'_eq] at this
        · intro _; by_contra hne_w; rw [hd'_eq] at hwd'; exact hw_ok ⟨hwd', hne_w⟩
      · rw [refineAt_unchanged _ _ _ _ hd'_eq]
        exact hw_norm.2 d' hd' hwd' v hv
    · -- d ⊄ d₀: all subdomains ≠ d, patterns unchanged
      obtain ⟨w, hw⟩ := hcoh d₀ hd₀_ne
      refine ⟨w, hw.1, fun d' hd' hwd' v hv => ?_⟩
      have hd'_ne : d' ≠ d := fun heq => hd_sub (heq ▸ hd')
      rw [refineAt_unchanged _ _ _ _ hd'_ne]
      exact hw.2 d' hd' hwd' v hv


-- ═══ Connection to §3 ═══

/-- For a constant frame with a connected ordering, the §4 normal
    worlds in d coincide with §3's optimal worlds. This is because
    for connected orderings, "top in every subdomain" reduces to
    "optimal in d" — since optimal = top when the ordering is total
    or connected. -/
theorem ExpFrame.const_normal_of_connected (no : NormalityOrder W)
    (d : Set W) (hconn : no.connected) :
    (ExpFrame.const no).normal d = no.optimal d := by
  ext w
  simp only [normal, const, Set.mem_setOf_eq, NormalityOrder.optimal]
  constructor
  · -- normal → optimal: weaker condition
    intro ⟨hwd, hsub⟩
    exact ⟨hwd, fun v hv hle => hsub d Set.Subset.rfl hwd v hv⟩
  · -- optimal → normal (using connectedness)
    intro ⟨hwd, hopt⟩
    refine ⟨hwd, fun d' hd'd hwd' v hv => ?_⟩
    -- w, v ∈ d and the ordering is the same (constant frame)
    -- By connectedness: either le w v (done) or le v w
    rcases hconn w v with hwv | hvw
    · exact hwv
    · -- le v w, and v ∈ d' ⊆ d, so v ∈ d
      -- By optimality of w in d: le w v
      exact hopt v (hd'd hv) hvw


-- ═══ Applicability ═══

/-- **Applicability**: a default e applies to s within frame π.

    Veltman (1996), Definition 4.9: the d-default e applies to s iff
    there is no d' ⊇ s such that nπd' ⊆ d and the normal d'-worlds
    all fail e. Simplified for a single default: e applies to s if
    the frame can be coherently refined by e at d (from s's
    perspective). -/
def ExpFrame.applies (π : ExpFrame W) (d : Set W) (e : W → Prop)
    (s : Set W) : Prop :=
  s ⊆ d → ¬∃ d', s ⊆ d' ∧ π.normal d' ⊆ { w ∈ d | ¬e w }


end Semantics.Dynamic.Default
