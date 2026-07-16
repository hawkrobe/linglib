import Linglib.Core.Logic.TweetyNixon
import Linglib.Core.Order.Normality
import Linglib.Semantics.Dynamic.UpdateSemantics.Basic
import Linglib.Semantics.Dynamic.UpdateSemantics.Default
import Linglib.Semantics.Dynamic.State

/-!
# [veltman-1996] — Full Study

[veltman-1996]

Regression tests for [veltman-1996]'s update semantics with defaults,
together with the §4 expectation-frame apparatus they run on.

## §3 Examples (Examples 3.10)

Finite verification of the key properties of "normally" and "presumably"
over a 4-world type with atoms p, q.

## §4 Expectation Frames

Where §3 uses a single normality ordering for all domains, §4 (Veltman's
"heart of the paper") assigns a *per-domain* ordering via an **expectation
frame**, enabling conditional defaults "if φ then normally ψ". A world is
*normal* in a domain (Definition 4.3) when it is top-ranked in *every*
subdomain containing it — this is how a specific exception overrides a
general default without the general default knowing about it. Refinement
(`ExpFrame.refineAt`, Definition 4.5) modifies only the pattern at the
target domain; the effect on superdomains flows through the subdomain-
checking `normal`. For a constant frame with a connected ordering, §4
`normal` reduces to §3 `optimal`.

## §4 Specificity (Tweety Triangle & Nixon Diamond)

Expectation frames resolve specificity (Tweety) and conflicting
defaults (Nixon) using the subdomain-indexed normality check.

## §5 Inference Patterns

Conjunction of Consequents (CC) is valid for the default conditional ⇝.
Contraposition and Strengthening the Antecedent fail (counterexamples).

## §5–6 Generics Bridge

The normality ordering in update semantics plays the same role as
the normalcy predicate in the GEN operator for generic sentences.
-/

namespace Veltman1996

open Core.Logic.TweetyNixon
open UpdateSemantics.Default
open Core.Order
open Classical


-- ═══════════════════════════════════════════════════════════════════════
-- PQ WORLDS (shared across sections)
-- ═══════════════════════════════════════════════════════════════════════

/-- Four worlds determined by atoms p, q. -/
inductive PQWorld : Type where
  | w₀  -- ¬p, ¬q
  | w₁  -- p, ¬q
  | w₂  -- ¬p, q
  | w₃  -- p, q
  deriving DecidableEq, Repr

open PQWorld

instance : Fintype PQWorld :=
  ⟨⟨[w₀, w₁, w₂, w₃], by decide⟩, fun w => by cases w <;> decide⟩

def atomP : PQWorld → Prop
  | .w₁ | .w₃ => True
  | _ => False

def atomQ : PQWorld → Prop
  | .w₂ | .w₃ => True
  | _ => False

-- Atom truth values
private theorem atomP_w₀ : ¬atomP w₀ := id
private theorem atomP_w₁ : atomP w₁ := True.intro
private theorem atomP_w₂ : ¬atomP w₂ := id
private theorem atomP_w₃ : atomP w₃ := True.intro
private theorem atomQ_w₀ : ¬atomQ w₀ := id
private theorem atomQ_w₁ : ¬atomQ w₁ := id
private theorem atomQ_w₂ : atomQ w₂ := True.intro
private theorem atomQ_w₃ : atomQ w₃ := True.intro

/-- Initial expectation state: all worlds possible, all equally normal. -/
private def σ₀ : ExpState PQWorld := ExpState.init


-- ═══════════════════════════════════════════════════════════════════════
-- §3 EXAMPLES (Examples 3.10)
-- ═══════════════════════════════════════════════════════════════════════

section Examples310

-- ─── Example 3.10(i): Rules can have exceptions ───

/-- After "normally p", learning ¬p doesn't crash — the info state
    still has ¬p-worlds. Rules can have exceptions. -/
theorem ex310_i_exception :
    ((σ₀.promote atomP).assert (fun w => ¬atomP w)).info.Nonempty :=
  ⟨w₀, ⟨Set.mem_univ _, atomP_w₀⟩⟩

/-- After "normally p", the globally optimal worlds are exactly the
    p-worlds. So "normally ¬p" is unacceptable: no optimal world
    satisfies ¬p. This is [veltman-1996]'s coherence check
    (Definition 3.9). -/
theorem ex310_i_conflict :
    ¬∃ w ∈ Normality.optimal (σ₀.promote atomP).order Set.univ, ¬atomP w := by
  intro ⟨w, hw_opt, hnp⟩
  have hex : ∃ v ∈ (Set.univ : Set PQWorld), atomP v :=
    ⟨w₁, Set.mem_univ _, atomP_w₁⟩
  simp only [ExpState.promote, σ₀, ExpState.init] at hw_opt
  rw [Normality.refine_total_optimal atomP Set.univ hex] at hw_opt
  exact hnp hw_opt.2

-- ─── Example 3.10(ii): Exceptions defeat presumptions ───

/-- After "normally p" then learning ¬p, "presumably p" fails.
    The optimal worlds in {w | ¬p w} are all ¬p-worlds (mutually
    equivalent under the p-biased ordering).

    [veltman-1996], Examples 3.10(ii): normally p, ¬p ⊬ presumably p. -/
theorem ex310_ii_defeat :
    ¬∀ w ∈ ((σ₀.promote atomP).assert (fun w => ¬atomP w)).optimal,
      atomP w := by
  intro h
  apply h w₀
  simp only [ExpState.optimal, ExpState.assert, ExpState.promote, σ₀, ExpState.init,
    Normality.optimal]
  refine ⟨⟨Set.mem_univ _, atomP_w₀⟩, fun v ⟨_, hnpv⟩ _ => ?_⟩
  exact ⟨True.intro, fun hpv => absurd hpv hnpv⟩

/-- But exceptions don't destroy the rule: "normally p" still holds.

    [veltman-1996], Examples 3.10(ii): normally p, ¬p ⊩ normally p. -/
theorem ex310_ii_rule_persists :
    Normality.respects ((σ₀.promote atomP).assert (fun w => ¬atomP w)).order atomP :=
  persistence_assert (σ₀.promote atomP) atomP _ (normally_creates_respect σ₀ atomP)

-- ─── Example 3.10(iii): Irrelevant information ───

/-- Irrelevant information doesn't block presumptions: after
    "normally p" and learning q, "presumably p" still succeeds.

    [veltman-1996], Examples 3.10(iii): normally p, q ⊩ presumably p. -/
theorem ex310_iii_irrelevant :
    ∀ w ∈ ((σ₀.promote atomP).assert atomQ).optimal, atomP w := by
  intro w ⟨⟨_, hqw⟩, hopt⟩
  simp only [ExpState.promote, σ₀, ExpState.init] at hopt
  by_contra hnpw
  have hle : (Normality.refine Normality.total atomP).le w₃ w :=
    ⟨True.intro, fun _ => atomP_w₃⟩
  have hw₃_mem : w₃ ∈ ({w ∈ Set.univ | atomQ w} : Set PQWorld) :=
    ⟨Set.mem_univ _, atomQ_w₃⟩
  exact hnpw ((hopt hw₃_mem hle).2 atomP_w₃)

-- ─── Example 3.10(iv): Independent defaults ───

/-- One default being defeated doesn't affect unrelated defaults.

    [veltman-1996], Examples 3.10(iv):
    normally p, normally q, ¬p ⊩ presumably q. -/
theorem ex310_iv_independence :
    ∀ w ∈ (((σ₀.promote atomP).promote atomQ).assert (fun w => ¬atomP w)).optimal,
      atomQ w := by
  intro w ⟨⟨_, hnpw⟩, hopt⟩
  simp only [ExpState.promote, σ₀, ExpState.init] at hopt
  by_contra hnqw
  -- w₂ (¬p, q) dominates any ¬p ∧ ¬q world
  have hle : (Normality.refine (Normality.refine Normality.total atomP) atomQ).le w₂ w :=
    ⟨⟨True.intro, fun hpw => absurd hpw hnpw⟩, fun hqw => absurd hqw hnqw⟩
  have hw₂_mem : w₂ ∈ ({w ∈ Set.univ | ¬atomP w} : Set PQWorld) :=
    ⟨Set.mem_univ _, atomP_w₂⟩
  exact hnqw ((hopt hw₂_mem hle).2 atomQ_w₂)

-- ─── Example 3.10(v): Ambiguity ───

/-- When two defaults conflict with the facts, neither presumption
    goes through. w₂ (¬p, q) is optimal but ¬p, so "presumably p" fails.

    [veltman-1996], Examples 3.10(v):
    normally p, normally q, ¬(p ∧ q) ⊬ presumably p. -/
theorem ex310_v_ambiguity_p :
    ¬∀ w ∈ (((σ₀.promote atomP).promote atomQ).assert (fun w => ¬(atomP w ∧ atomQ w))).optimal,
      atomP w := by
  intro h
  apply h w₂
  simp only [ExpState.optimal, ExpState.assert, ExpState.promote, σ₀, ExpState.init,
    Normality.optimal]
  refine ⟨⟨Set.mem_univ _, fun ⟨hp, _⟩ => atomP_w₂ hp⟩, fun v ⟨_, hnpq⟩ hle => ?_⟩
  -- hle gives atomQ v (via the atomQ-refinement component evaluated at w₂)
  obtain ⟨⟨_, _⟩, hqv_imp⟩ := hle
  have hqv : atomQ v := hqv_imp atomQ_w₂
  show (Normality.refine (Normality.refine Normality.total atomP) atomQ).le w₂ v
  exact ⟨⟨True.intro, fun hpv => absurd ⟨hpv, hqv⟩ hnpq⟩, fun _ => atomQ_w₂⟩

/-- Symmetric: w₁ (p, ¬q) is optimal but ¬q, so "presumably q" fails.

    [veltman-1996], Examples 3.10(v):
    normally p, normally q, ¬(p ∧ q) ⊬ presumably q. -/
theorem ex310_v_ambiguity_q :
    ¬∀ w ∈ (((σ₀.promote atomP).promote atomQ).assert (fun w => ¬(atomP w ∧ atomQ w))).optimal,
      atomQ w := by
  intro h
  apply h w₁
  simp only [ExpState.optimal, ExpState.assert, ExpState.promote, σ₀, ExpState.init,
    Normality.optimal]
  refine ⟨⟨Set.mem_univ _, fun ⟨_, hq⟩ => atomQ_w₁ hq⟩, fun v ⟨_, hnpq⟩ hle => ?_⟩
  -- hle gives atomP v (via the atomP-refinement component evaluated at w₁)
  obtain ⟨⟨_, hpv_imp⟩, _⟩ := hle
  have hpv : atomP v := hpv_imp atomP_w₁
  show (Normality.refine (Normality.refine Normality.total atomP) atomQ).le w₁ v
  exact ⟨⟨True.intro, fun _ => atomP_w₁⟩, fun hqv => absurd ⟨hpv, hqv⟩ hnpq⟩

end Examples310


-- ═══════════════════════════════════════════════════════════════════════
-- §4 EXPECTATION FRAMES (apparatus)
-- ═══════════════════════════════════════════════════════════════════════

section ExpectationFrames

variable {W : Type*}

/-! ### Expectation frames -/

/-- An **expectation frame**: a function assigning a normality ordering
    to each domain (subset of worlds).

    [veltman-1996], Definition 4.2: π assigns to every d ⊆ W an
    expectation pattern πd. Different domains may have different
    orderings — this is what enables conditional defaults. -/
structure ExpFrame (W : Type*) where
  /-- The per-domain normality ordering -/
  pattern : Set W → Preorder W

/-- Extensionality for frames: two frames are equal iff they assign
    the same ordering to every domain. -/
@[ext]
theorem ExpFrame.ext {π₁ π₂ : ExpFrame W}
    (h : ∀ d, π₁.pattern d = π₂.pattern d) : π₁ = π₂ := by
  cases π₁; cases π₂; congr; funext d; exact h d

/-- The **normal worlds** in a domain under the frame.

    [veltman-1996], Definition 4.3(i–ii): w is normal in πd iff w ∈ d
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

    [veltman-1996], Definition 4.3(iii). -/
def ExpFrame.coherent (π : ExpFrame W) : Prop :=
  ∀ d : Set W, d.Nonempty → (π.normal d).Nonempty

/-- e is a **default in πd** iff d ∩ e ≠ ∅ and πd already respects e.

    [veltman-1996], Definition 4.2(ii): e is a default in πd iff
    d ∩ e ≠ ∅ and πd ∘ e = πd. Since `refine_of_respects` gives
    the latter iff `respects`, we use `respects` directly. -/
def ExpFrame.isDefault (π : ExpFrame W) (d : Set W) (e : W → Prop) :
    Prop :=
  (∃ w ∈ d, e w) ∧ Normality.respects (π.pattern d) e

/-- The **constant frame**: assigns the same ordering to every domain.
    This embeds §3's single-ordering setup into the §4 framework. -/
def ExpFrame.const (no : Preorder W) : ExpFrame W :=
  ⟨fun _ => no⟩

/-- The **total frame**: assigns the total ordering to every domain.
    The initial state before any defaults have been processed. -/
def ExpFrame.total : ExpFrame W :=
  ExpFrame.const Normality.total

/-! ### Frame refinement -/

/-- **Frame refinement**: refine the ordering at domain d only.

    [veltman-1996], Definition 4.5(ii):
    - π_{d∘e}(d') = πd' if d' ≠ d
    - π_{d∘e}(d) = πd ∘ e

    Unlike our earlier (incorrect) version that refined all d' ⊇ d,
    this modifies *only* the pattern at d. The effect on superdomains
    comes automatically through the `normal` computation, which checks
    all subdomains — so a refinement at d changes which worlds count as
    normal in any d' ⊇ d. -/
noncomputable def ExpFrame.refineAt (π : ExpFrame W) (d : Set W)
    (e : W → Prop) : ExpFrame W :=
  ⟨fun d' => if d' = d then Normality.refine (π.pattern d) e else π.pattern d'⟩

/-- Domains other than d are unchanged by refinement. -/
theorem ExpFrame.refineAt_unchanged (π : ExpFrame W) (d : Set W)
    (e : W → Prop) (d' : Set W) (h : d' ≠ d) :
    (π.refineAt d e).pattern d' = π.pattern d' := by
  unfold refineAt; exact if_neg h

/-- The target domain gets its ordering refined. -/
theorem ExpFrame.refineAt_target (π : ExpFrame W) (d : Set W)
    (e : W → Prop) :
    (π.refineAt d e).pattern d = Normality.refine (π.pattern d) e := by
  unfold refineAt; exact if_pos rfl

/-! ### Frame state -/

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

/-! ### Conditional default update -/

/-- **Conditional default update**: "if φ then normally ψ".

    [veltman-1996], Definition 4.6. Given σ = ⟨π, s⟩:
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

/-! ### Basic properties -/

/-- Assertion preserves the frame. -/
theorem assertFrame_preserves_frame (φ : W → Prop) (σ : FrameState W) :
    (assertFrame φ σ).frame = σ.frame := rfl

/-- Normal worlds are in the domain. -/
theorem ExpFrame.normal_subset (π : ExpFrame W) (d : Set W) :
    π.normal d ⊆ d := fun _ hw => hw.1

/-! ### Frame refinement properties -/

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
    exact Normality.refine_comm _ _ _
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
    exact Normality.refine_idempotent _ _
  · simp only [refineAt_unchanged _ d _ d' hd]

/-- If πd already respects e, refinement at d is a no-op. -/
theorem ExpFrame.refineAt_of_respects (π : ExpFrame W) (d : Set W)
    (e : W → Prop) (h : Normality.respects (π.pattern d) e) :
    π.refineAt d e = π := by
  apply ExpFrame.ext; intro d'
  by_cases hd : d' = d
  · subst hd
    rw [refineAt_target]
    exact Normality.refine_of_respects _ _ h
  · exact refineAt_unchanged _ d _ d' hd

/-- After refinement at d, the pattern at d respects e. -/
theorem ExpFrame.refineAt_creates_respect (π : ExpFrame W) (d : Set W)
    (e : W → Prop) :
    Normality.respects ((π.refineAt d e).pattern d) e := by
  rw [refineAt_target]
  exact Normality.refine_respects _ _

/-! ### Coherence preservation -/

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
    rw [refineAt_target, Normality.refine_le] at h
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
        rw [hd'_eq, refineAt_target, Normality.refine_le]
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

/-! ### Connection to §3 -/

/-- For a constant frame with a connected ordering, the §4 normal
    worlds in d coincide with §3's optimal worlds. This is because
    for connected orderings, "top in every subdomain" reduces to
    "optimal in d" — since optimal = top when the ordering is total
    or connected. -/
theorem ExpFrame.const_normal_of_connected (no : Preorder W)
    (d : Set W) (hconn : Normality.connected no) :
    (ExpFrame.const no).normal d = Normality.optimal no d := by
  ext w
  simp only [normal, const, Set.mem_setOf_eq, Normality.optimal]
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
      exact hopt (hd'd hv) hvw

/-! ### Applicability -/

/-- **Applicability**: a default e applies to s within frame π.

    [veltman-1996], Definition 4.9: the d-default e applies to s iff
    there is no d' ⊇ s such that nπd' ⊆ d and the normal d'-worlds
    all fail e. Simplified for a single default: e applies to s if
    the frame can be coherently refined by e at d (from s's
    perspective). -/
def ExpFrame.applies (π : ExpFrame W) (d : Set W) (e : W → Prop)
    (s : Set W) : Prop :=
  s ⊆ d → ¬∃ d', s ⊆ d' ∧ π.normal d' ⊆ { w ∈ d | ¬e w }

end ExpectationFrames


-- ═══════════════════════════════════════════════════════════════════════
-- §4 SPECIFICITY: TWEETY TRIANGLE
-- ═══════════════════════════════════════════════════════════════════════

section Tweety

open TweetyWorld

def birdDomain : Set TweetyWorld := { w | isBird w }
def penguinDomain : Set TweetyWorld := { w | isPenguin w }

/-- Ordering for the bird domain: promotes flying. -/
private def birdOrd : Preorder TweetyWorld :=
  Preorder.ofLE (fun w v => flies v → flies w) (fun _ => id)
    (fun _ _ _ huv hvw h => huv (hvw h))

/-- Ordering for the penguin domain: promotes ¬flying. -/
private def penguinOrd : Preorder TweetyWorld :=
  Preorder.ofLE (fun w v => ¬flies v → ¬flies w) (fun _ => id)
    (fun _ _ _ huv hvw h => huv (hvw h))

private noncomputable def tweetyPattern (d : Set TweetyWorld) :
    Preorder TweetyWorld :=
  if d = penguinDomain then penguinOrd
  else if d = birdDomain then birdOrd
  else Normality.total

noncomputable def tweetyFrame : ExpFrame TweetyWorld :=
  ⟨tweetyPattern⟩

private theorem pen_ne_bird : penguinDomain ≠ birdDomain := by
  intro h
  have : birdFlies ∈ penguinDomain :=
    h ▸ (show birdFlies ∈ birdDomain from True.intro)
  exact this

private theorem penguin_sub_bird : penguinDomain ⊆ birdDomain :=
  fun w hw => penguin_is_bird w hw

private theorem pat_penguin : tweetyPattern penguinDomain = penguinOrd :=
  if_pos rfl

private theorem pat_bird : tweetyPattern birdDomain = birdOrd := by
  unfold tweetyPattern
  rw [if_neg (Ne.symm pen_ne_bird), if_pos rfl]

private theorem pat_other (d : Set TweetyWorld)
    (hp : d ≠ penguinDomain) (hb : d ≠ birdDomain) :
    tweetyPattern d = Normality.total := by
  unfold tweetyPattern; rw [if_neg hp, if_neg hb]

private theorem sub_penguin_ne_bird (d : Set TweetyWorld)
    (h : d ⊆ penguinDomain) : d ≠ birdDomain := by
  intro heq; subst heq
  exact pen_ne_bird.symm (Set.Subset.antisymm h penguin_sub_bird)

/-- birdFlies is normal among birds. -/
theorem birdFlies_normal_in_birds :
    birdFlies ∈ tweetyFrame.normal birdDomain := by
  refine ⟨True.intro, fun d' hd' hwd' v _ => ?_⟩
  change (tweetyPattern d').le birdFlies v
  by_cases hp : d' = penguinDomain
  · subst hp; exact absurd hwd' id
  · by_cases hb : d' = birdDomain
    · subst hb; rw [pat_bird]; exact fun _ => True.intro
    · rw [pat_other d' hp hb]; exact True.intro

/-- penguinFlies is NOT normal among birds — specificity. -/
theorem penguinFlies_not_normal_in_birds :
    penguinFlies ∉ tweetyFrame.normal birdDomain := by
  intro ⟨_, hsub⟩
  have h := hsub penguinDomain penguin_sub_bird
    (show penguinFlies ∈ penguinDomain from True.intro)
    penguinNoFly (show penguinNoFly ∈ penguinDomain from True.intro)
  change (tweetyPattern penguinDomain).le penguinFlies penguinNoFly at h
  rw [pat_penguin] at h
  exact h id True.intro

/-- penguinNoFly is normal among penguins. -/
theorem penguinNoFly_normal_in_penguins :
    penguinNoFly ∈ tweetyFrame.normal penguinDomain := by
  refine ⟨True.intro, fun d' hd' hwd' v hv => ?_⟩
  change (tweetyPattern d').le penguinNoFly v
  by_cases hp : d' = penguinDomain
  · subst hp; rw [pat_penguin]; exact fun _ h => h
  · have hb : d' ≠ birdDomain := sub_penguin_ne_bird d' (hd'.trans (fun x h => h))
    rw [pat_other d' hp hb]; exact True.intro

end Tweety


-- ═══════════════════════════════════════════════════════════════════════
-- §4 CONFLICTING DEFAULTS: NIXON DIAMOND
-- ═══════════════════════════════════════════════════════════════════════

section Nixon

open NixonWorld

def quakerDomain : Set NixonWorld := { w | isQuaker w }
def repDomain : Set NixonWorld := { w | isRepublican w }

private def quakerOrd : Preorder NixonWorld :=
  Preorder.ofLE (fun w v => isPacifist v → isPacifist w) (fun _ => id)
    (fun _ _ _ huv hvw h => huv (hvw h))

private def repOrd : Preorder NixonWorld :=
  Preorder.ofLE (fun w v => ¬isPacifist v → ¬isPacifist w) (fun _ => id)
    (fun _ _ _ huv hvw h => huv (hvw h))

private noncomputable def nixonPattern (d : Set NixonWorld) :
    Preorder NixonWorld :=
  if d = quakerDomain then quakerOrd
  else if d = repDomain then repOrd
  else Normality.total

noncomputable def nixonFrame : ExpFrame NixonWorld :=
  ⟨nixonPattern⟩

private theorem quaker_ne_rep : quakerDomain ≠ repDomain := by
  intro h
  have : quakerPacifist ∈ repDomain :=
    h ▸ (show quakerPacifist ∈ quakerDomain from True.intro)
  exact this

private theorem npat_quaker : nixonPattern quakerDomain = quakerOrd :=
  if_pos rfl

private theorem npat_rep : nixonPattern repDomain = repOrd := by
  unfold nixonPattern; rw [if_neg (Ne.symm quaker_ne_rep), if_pos rfl]

/-- quakerPacifist is normal among Quakers. -/
theorem quakerPacifist_normal :
    quakerPacifist ∈ nixonFrame.normal quakerDomain := by
  refine ⟨True.intro, fun d' hd' hwd' v _ => ?_⟩
  change (nixonPattern d').le quakerPacifist v
  by_cases hq : d' = quakerDomain
  · subst hq; rw [npat_quaker]; exact fun _ => True.intro
  · by_cases hr : d' = repDomain
    · subst hr; exfalso; exact hwd'
    · unfold nixonPattern; rw [if_neg hq, if_neg hr]; exact True.intro

/-- repNotPacifist is normal among Republicans. -/
theorem repNotPacifist_normal :
    repNotPacifist ∈ nixonFrame.normal repDomain := by
  refine ⟨True.intro, fun d' hd' hwd' v _ => ?_⟩
  change (nixonPattern d').le repNotPacifist v
  by_cases hr : d' = repDomain
  · subst hr; rw [npat_rep]; exact fun _ h => h
  · by_cases hq : d' = quakerDomain
    · subst hq; exfalso; exact hwd'
    · unfold nixonPattern; rw [if_neg hq, if_neg hr]; exact True.intro

/-- quakerPacifist is NOT normal among Republicans (disjoint domains). -/
theorem quakerPacifist_not_normal_rep :
    quakerPacifist ∉ nixonFrame.normal repDomain := by
  intro ⟨hmem, _⟩; exact hmem

end Nixon


-- ═══════════════════════════════════════════════════════════════════════
-- §5 INFERENCE PATTERNS
-- ═══════════════════════════════════════════════════════════════════════

section InferencePatterns

variable {W : Type*}

-- ─── Valid: Conjunction of Consequents (CC) ───

/-- **Conjunction of Consequents (CC)**: after processing "if φ then
    normally ψ" and "if φ then normally χ", the ordering at the
    φ-domain already respects (ψ ∧ χ).

    This is the mathematical core of CC: sequential refinement by ψ
    and χ produces an ordering that promotes (ψ ∧ χ)-worlds.

    [veltman-1996], §5 (p.256): CC is valid. -/
theorem conjConsequents_respects (no : Preorder W)
    (ψ χ : W → Prop) :
    Normality.respects (Normality.refine (Normality.refine no ψ) χ)
      (fun w => ψ w ∧ χ w) := by
  intro w v ⟨⟨_, hψ⟩, hχ⟩ ⟨hψv, hχv⟩
  exact ⟨hψ hψv, hχ hχv⟩

/-- CC at the frame level: after two refinements at the same domain,
    further refinement by the conjunction is a no-op. -/
theorem conjConsequents_frame (π : ExpFrame W) (d : Set W)
    (ψ χ : W → Prop) :
    ((π.refineAt d ψ).refineAt d χ).refineAt d (fun w => ψ w ∧ χ w) =
    (π.refineAt d ψ).refineAt d χ := by
  apply ExpFrame.ext; intro d'
  by_cases hd : d' = d
  · subst hd
    simp only [ExpFrame.refineAt_target]
    exact Normality.refine_of_respects _ _ (conjConsequents_respects _ ψ χ)
  · simp only [ExpFrame.refineAt_unchanged _ _ _ _ hd]

-- ─── Invalid: Contraposition (counterexample) ───

/-- **Contraposition fails**: after "if p then normally q", w₁ (p, ¬q)
    is still normal among ¬q-worlds — the frame at d_¬q is untouched.

    If contraposition held, all normal ¬q-worlds would satisfy ¬p.
    But w₁ is a normal ¬q-world that satisfies p.

    [veltman-1996], §5 (p.255). -/
theorem contraposition_fails :
    let d_p := { w : PQWorld | atomP w }
    let d_nq := { w : PQWorld | ¬atomQ w }
    let π := (ExpFrame.total (W := PQWorld)).refineAt d_p atomQ
    -- w₁ is normal among ¬q-worlds but satisfies p
    w₁ ∈ π.normal d_nq ∧ atomP w₁ := by
  refine ⟨⟨atomQ_w₁, fun d' hd' hwd' v hv => ?_⟩, atomP_w₁⟩
  -- d' ⊆ d_nq, so d' ≠ d_p (w₃ ∈ d_p but w₃ ∉ d_nq since atomQ w₃)
  have hd'_ne : d' ≠ { w : PQWorld | atomP w } := by
    intro heq
    have h3 : w₃ ∈ d' := by rw [heq]; exact atomP_w₃
    exact absurd atomQ_w₃ (hd' h3)
  have heq := ExpFrame.refineAt_unchanged (ExpFrame.total (W := PQWorld))
    { w : PQWorld | atomP w } atomQ d' hd'_ne
  rw [heq]; exact True.intro

-- ─── Invalid: Strengthening the Antecedent (counterexample) ───

/-- **Strengthening the Antecedent fails**: after "if p then normally q",
    the frame at d_{p∧q} is untouched (since d_{p∧q} ≠ d_p).

    [veltman-1996], §5 (p.256). -/
theorem strengtheningAntecedent_fails :
    -- The domains are different: w₁ ∈ d_p but w₁ ∉ d_pq
    ({ w : PQWorld | atomP w } : Set PQWorld) ≠ { w | atomP w ∧ atomQ w } := by
  intro h
  have h1 : w₁ ∈ ({ w : PQWorld | atomP w } : Set PQWorld) := atomP_w₁
  rw [h] at h1
  exact atomQ_w₁ h1.2

-- ─── Defeasible Modus Tollens does NOT hold at the frame level ───

/-- **Defeasible Modus Tollens fails** for `ExpFrame.normal`:
    after "if p then normally q" and learning ¬q, w₁ (a p-world)
    is still normal among ¬q-worlds. No subdomain of d_nq = {w₀, w₁}
    equals d_p = {w₁, w₃}, so the refined ordering is never consulted.

    This shows that DMT requires the full dynamic derivation
    (processing the conditional, then asserting ¬q, then testing
    presumably ¬p) rather than a single `ExpFrame.normal` check. -/
theorem defeasible_modus_tollens_fails :
    let d_p := { w : PQWorld | atomP w }
    let π := (ExpFrame.total (W := PQWorld)).refineAt d_p atomQ
    -- w₁ is normal among ¬q-worlds despite being a p-world
    w₁ ∈ π.normal { w | ¬atomQ w } ∧ atomP w₁ := by
  refine ⟨⟨atomQ_w₁, fun d' hd' hwd' v hv => ?_⟩, atomP_w₁⟩
  -- d' ⊆ d_nq = {w₀, w₁}, so d' ≠ d_p = {w₁, w₃} (w₃ ∈ d_p \ d_nq)
  have hd'_ne : d' ≠ { w : PQWorld | atomP w } := by
    intro heq
    have h3 : w₃ ∈ d' := by rw [heq]; exact atomP_w₃
    exact absurd atomQ_w₃ (hd' h3)
  have heq := ExpFrame.refineAt_unchanged (ExpFrame.total (W := PQWorld))
    { w : PQWorld | atomP w } atomQ d' hd'_ne
  rw [heq]; exact True.intro

end InferencePatterns


-- ═══════════════════════════════════════════════════════════════════════
-- §5–6 GENERICS BRIDGE
-- ═══════════════════════════════════════════════════════════════════════

section GenericsBridge

variable {W : Type*}

/-- **Generics as defaults** ([veltman-1996], §5–6).

    The truth conditions of the GEN operator ("P's are normally Q"):
        ∀w ∈ optimal(d). scope(w)
    are exactly the conditions for the "presumably" test to pass
    in update semantics.

    This theorem witnesses the structural identity: "all optimal worlds
    in a domain satisfy the scope" is just the definition of optimality
    restated. The substantive bridge is that `Normality.optimal`
    provides the normalcy predicate for GEN, and `Normality.refine`
    provides the dynamic mechanism for learning new generic rules. -/
theorem optimal_as_normalcy (no : Preorder W) (d : Set W)
    (scope : W → Prop) :
    (∀ w ∈ Normality.optimal no d, scope w) ↔
    ∀ w, w ∈ d → (∀ v ∈ d, no.le v w → no.le w v) → scope w := by
  constructor
  · intro h w hwd hopt; exact h w ⟨hwd, hopt⟩
  · intro h w ⟨hwd, hopt⟩; exact h w hwd hopt

end GenericsBridge

/-! ### Update-semantics states as the referent-free stratum

Veltman's information states are bare sets of worlds. In the substrate
they are exactly the uniform states at the empty context:
`toIndexedState` embeds them constructively — no choice, no inhabitant
of `M`, unlike under the total-assignment rendering — the embedding
reverses into the informativeness order `⊑`, and propositional update
transports to point filtering. -/

section IndexedFiber

open DynamicSemantics UpdateSemantics

variable {W V M : Type*} {s t : Set W}

/-- A Veltman state as the referent-free state: its worlds, with nothing
yet introduced. -/
def toIndexedState (V M : Type*) (s : Set W) :
    DynamicSemantics.State W V M :=
  {p | p.world ∈ s ∧ ∀ v, p.assignment v = none}

@[simp] theorem mem_toIndexedState {p : Possibility W V (Option M)} :
    p ∈ toIndexedState V M s ↔
      p.world ∈ s ∧ ∀ v, p.assignment v = none := Iff.rfl

/-- The embedding lands in the empty stratum. -/
theorem uniformAt_toIndexedState :
    State.UniformAt ∅ (toIndexedState V M s) := fun p hp => by
  ext v
  simp [Possibility.dom, hp.2 v]

/-- The embedding is faithful on worldly content. -/
@[simp] theorem worlds_toIndexedState :
    worlds (toIndexedState V M s) = s := by
  ext w
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp.1
  · intro hw
    exact ⟨⟨w, fun _ => none⟩, ⟨hw, fun _ => rfl⟩, rfl⟩

/-- Eliminating worlds is gaining information: the embedding reverses
into `⊑`. -/
theorem toIndexedState_infoLe_iff :
    (toIndexedState V M s ⊑ toIndexedState V M t) ↔ t ⊆ s := by
  constructor
  · intro h w hw
    obtain ⟨p, hp, hpq⟩ := h ⟨w, fun _ => none⟩ ⟨hw, fun _ => rfl⟩
    have hs := hp.1
    rwa [hpq.1] at hs
  · rintro h q ⟨hq, hnone⟩
    exact ⟨q, ⟨h hq, hnone⟩, Possibility.Descendant.refl q⟩

/-- Propositional update ([veltman-1996]'s elimination) transports to
point filtering. -/
theorem toIndexedState_update_prop (φ : W → Prop) :
    toIndexedState V M (UpdateSemantics.Update.prop φ s) =
      {p ∈ toIndexedState V M s | φ p.world} :=
  Set.ext fun p => by
    simp only [mem_toIndexedState, Set.mem_sep_iff, Set.mem_setOf_eq,
      UpdateSemantics.Update.prop]
    tauto

end IndexedFiber

end Veltman1996
