import Linglib.Phenomena.DefaultReasoning.TweetyNixon
import Linglib.Theories.Semantics.Dynamic.UpdateSemantics.Frames

/-!
# @cite{veltman-1996} — Full Study

@cite{veltman-1996}

Regression tests for @cite{veltman-1996}'s update semantics with defaults.

## §3 Examples (Examples 3.10)

Finite verification of the key properties of "normally" and "presumably"
over a 4-world type with atoms p, q.

## §4 Specificity (Tweety Triangle & Nixon Diamond)

Expectation frames resolve specificity (Tweety) and conflicting
defaults (Nixon) using the subdomain-based normality check.

## §5 Inference Patterns

Conjunction of Consequents (CC) is valid for the default conditional ⇝.
Contraposition and Strengthening the Antecedent fail (counterexamples).

## §5–6 Generics Bridge

The normality ordering in update semantics plays the same role as
the normalcy predicate in the GEN operator for generic sentences.
-/

namespace Phenomena.DefaultReasoning.Studies.Veltman1996

open Phenomena.DefaultReasoning
open Semantics.Dynamic.Default
open Core.Order (NormalityOrder)
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
    (assertUpdate (fun w => ¬atomP w) (normallyUpdate atomP σ₀)).info.Nonempty :=
  ⟨w₀, ⟨Set.mem_univ _, atomP_w₀⟩⟩

/-- After "normally p", the globally optimal worlds are exactly the
    p-worlds. So "normally ¬p" is unacceptable: no optimal world
    satisfies ¬p. This is @cite{veltman-1996}'s coherence check
    (Definition 3.9). -/
theorem ex310_i_conflict :
    ¬∃ w ∈ (normallyUpdate atomP σ₀).order.optimal Set.univ, ¬atomP w := by
  intro ⟨w, hw_opt, hnp⟩
  have hex : ∃ v ∈ (Set.univ : Set PQWorld), atomP v :=
    ⟨w₁, Set.mem_univ _, atomP_w₁⟩
  simp only [normallyUpdate, σ₀, ExpState.init] at hw_opt
  rw [NormalityOrder.refine_total_optimal atomP Set.univ hex] at hw_opt
  exact hnp hw_opt.2

-- ─── Example 3.10(ii): Exceptions defeat presumptions ───

/-- After "normally p" then learning ¬p, "presumably p" fails.
    The optimal worlds in {w | ¬p w} are all ¬p-worlds (mutually
    equivalent under the p-biased ordering).

    @cite{veltman-1996}, Examples 3.10(ii): normally p, ¬p ⊬ presumably p. -/
theorem ex310_ii_defeat :
    ¬∀ w ∈ (assertUpdate (fun w => ¬atomP w) (normallyUpdate atomP σ₀)).optimal,
      atomP w := by
  intro h
  apply h w₀
  simp only [ExpState.optimal, assertUpdate, normallyUpdate, σ₀, ExpState.init,
    NormalityOrder.optimal]
  refine ⟨⟨Set.mem_univ _, atomP_w₀⟩, fun v ⟨_, hnpv⟩ _ => ?_⟩
  exact ⟨True.intro, fun hpv => absurd hpv hnpv⟩

/-- But exceptions don't destroy the rule: "normally p" still holds.

    @cite{veltman-1996}, Examples 3.10(ii): normally p, ¬p ⊩ normally p. -/
theorem ex310_ii_rule_persists :
    (assertUpdate (fun w => ¬atomP w) (normallyUpdate atomP σ₀)).order.respects atomP :=
  persistence_assert (normallyUpdate atomP σ₀) atomP _ (normally_creates_respect σ₀ atomP)

-- ─── Example 3.10(iii): Irrelevant information ───

/-- Irrelevant information doesn't block presumptions: after
    "normally p" and learning q, "presumably p" still succeeds.

    @cite{veltman-1996}, Examples 3.10(iii): normally p, q ⊩ presumably p. -/
theorem ex310_iii_irrelevant :
    ∀ w ∈ (assertUpdate atomQ (normallyUpdate atomP σ₀)).optimal, atomP w := by
  intro w ⟨⟨_, hqw⟩, hopt⟩
  simp only [normallyUpdate, σ₀, ExpState.init] at hopt
  by_contra hnpw
  have hle : (NormalityOrder.total.refine atomP).le w₃ w :=
    ⟨True.intro, fun _ => atomP_w₃⟩
  have hw₃_mem : w₃ ∈ ({w ∈ Set.univ | atomQ w} : Set PQWorld) :=
    ⟨Set.mem_univ _, atomQ_w₃⟩
  exact hnpw ((hopt w₃ hw₃_mem hle).2 atomP_w₃)

-- ─── Example 3.10(iv): Independent defaults ───

/-- One default being defeated doesn't affect unrelated defaults.

    @cite{veltman-1996}, Examples 3.10(iv):
    normally p, normally q, ¬p ⊩ presumably q. -/
theorem ex310_iv_independence :
    ∀ w ∈ (assertUpdate (fun w => ¬atomP w)
            (normallyUpdate atomQ (normallyUpdate atomP σ₀))).optimal,
      atomQ w := by
  intro w ⟨⟨_, hnpw⟩, hopt⟩
  simp only [normallyUpdate, σ₀, ExpState.init] at hopt
  by_contra hnqw
  -- w₂ (¬p, q) dominates any ¬p ∧ ¬q world
  have hle : ((NormalityOrder.total.refine atomP).refine atomQ).le w₂ w :=
    ⟨⟨True.intro, fun hpw => absurd hpw hnpw⟩, fun hqw => absurd hqw hnqw⟩
  have hw₂_mem : w₂ ∈ ({w ∈ Set.univ | ¬atomP w} : Set PQWorld) :=
    ⟨Set.mem_univ _, atomP_w₂⟩
  exact hnqw ((hopt w₂ hw₂_mem hle).2 atomQ_w₂)

-- ─── Example 3.10(v): Ambiguity ───

/-- When two defaults conflict with the facts, neither presumption
    goes through. w₂ (¬p, q) is optimal but ¬p, so "presumably p" fails.

    @cite{veltman-1996}, Examples 3.10(v):
    normally p, normally q, ¬(p ∧ q) ⊬ presumably p. -/
theorem ex310_v_ambiguity_p :
    ¬∀ w ∈ (assertUpdate (fun w => ¬(atomP w ∧ atomQ w))
             (normallyUpdate atomQ (normallyUpdate atomP σ₀))).optimal,
      atomP w := by
  intro h
  apply h w₂
  simp only [ExpState.optimal, assertUpdate, normallyUpdate, σ₀, ExpState.init,
    NormalityOrder.optimal]
  refine ⟨⟨Set.mem_univ _, fun ⟨hp, _⟩ => atomP_w₂ hp⟩, fun v ⟨_, hnpq⟩ hle => ?_⟩
  -- hle gives atomQ v (via the atomQ-refinement component evaluated at w₂)
  obtain ⟨⟨_, _⟩, hqv_imp⟩ := hle
  have hqv : atomQ v := hqv_imp atomQ_w₂
  show ((NormalityOrder.total.refine atomP).refine atomQ).le w₂ v
  exact ⟨⟨True.intro, fun hpv => absurd ⟨hpv, hqv⟩ hnpq⟩, fun _ => atomQ_w₂⟩

/-- Symmetric: w₁ (p, ¬q) is optimal but ¬q, so "presumably q" fails.

    @cite{veltman-1996}, Examples 3.10(v):
    normally p, normally q, ¬(p ∧ q) ⊬ presumably q. -/
theorem ex310_v_ambiguity_q :
    ¬∀ w ∈ (assertUpdate (fun w => ¬(atomP w ∧ atomQ w))
             (normallyUpdate atomQ (normallyUpdate atomP σ₀))).optimal,
      atomQ w := by
  intro h
  apply h w₁
  simp only [ExpState.optimal, assertUpdate, normallyUpdate, σ₀, ExpState.init,
    NormalityOrder.optimal]
  refine ⟨⟨Set.mem_univ _, fun ⟨_, hq⟩ => atomQ_w₁ hq⟩, fun v ⟨_, hnpq⟩ hle => ?_⟩
  -- hle gives atomP v (via the atomP-refinement component evaluated at w₁)
  obtain ⟨⟨_, hpv_imp⟩, _⟩ := hle
  have hpv : atomP v := hpv_imp atomP_w₁
  show ((NormalityOrder.total.refine atomP).refine atomQ).le w₁ v
  exact ⟨⟨True.intro, fun _ => atomP_w₁⟩, fun hqv => absurd ⟨hpv, hqv⟩ hnpq⟩

end Examples310


-- ═══════════════════════════════════════════════════════════════════════
-- §4 SPECIFICITY: TWEETY TRIANGLE
-- ═══════════════════════════════════════════════════════════════════════

section Tweety

open TweetyWorld

def birdDomain : Set TweetyWorld := { w | isBird w }
def penguinDomain : Set TweetyWorld := { w | isPenguin w }

/-- Ordering for the bird domain: promotes flying. -/
private def birdOrd : NormalityOrder TweetyWorld where
  le w v := (flies v → flies w)
  le_refl _ := id
  le_trans _ _ _ huv hvw h := huv (hvw h)

/-- Ordering for the penguin domain: promotes ¬flying. -/
private def penguinOrd : NormalityOrder TweetyWorld where
  le w v := (¬flies v → ¬flies w)
  le_refl _ := id
  le_trans _ _ _ huv hvw h := huv (hvw h)

private noncomputable def tweetyPattern (d : Set TweetyWorld) :
    NormalityOrder TweetyWorld :=
  if d = penguinDomain then penguinOrd
  else if d = birdDomain then birdOrd
  else NormalityOrder.total

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
    tweetyPattern d = NormalityOrder.total := by
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

private def quakerOrd : NormalityOrder NixonWorld where
  le w v := (isPacifist v → isPacifist w)
  le_refl _ := id
  le_trans _ _ _ huv hvw h := huv (hvw h)

private def repOrd : NormalityOrder NixonWorld where
  le w v := (¬isPacifist v → ¬isPacifist w)
  le_refl _ := id
  le_trans _ _ _ huv hvw h := huv (hvw h)

private noncomputable def nixonPattern (d : Set NixonWorld) :
    NormalityOrder NixonWorld :=
  if d = quakerDomain then quakerOrd
  else if d = repDomain then repOrd
  else NormalityOrder.total

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

    @cite{veltman-1996}, §5 (p.256): CC is valid. -/
theorem conjConsequents_respects (no : NormalityOrder W)
    (ψ χ : W → Prop) :
    ((no.refine ψ).refine χ).respects (fun w => ψ w ∧ χ w) := by
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
    exact NormalityOrder.refine_of_respects _ _ (conjConsequents_respects _ ψ χ)
  · simp only [ExpFrame.refineAt_unchanged _ _ _ _ hd]

-- ─── Invalid: Contraposition (counterexample) ───

/-- **Contraposition fails**: after "if p then normally q", w₁ (p, ¬q)
    is still normal among ¬q-worlds — the frame at d_¬q is untouched.

    If contraposition held, all normal ¬q-worlds would satisfy ¬p.
    But w₁ is a normal ¬q-world that satisfies p.

    @cite{veltman-1996}, §5 (p.255). -/
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
  simp only [ExpFrame.refineAt_unchanged _ _ _ _ hd'_ne, ExpFrame.total, ExpFrame.const]
  exact True.intro

-- ─── Invalid: Strengthening the Antecedent (counterexample) ───

/-- **Strengthening the Antecedent fails**: after "if p then normally q",
    the frame at d_{p∧q} is untouched (since d_{p∧q} ≠ d_p).

    @cite{veltman-1996}, §5 (p.256). -/
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
  simp only [ExpFrame.refineAt_unchanged _ _ _ _ hd'_ne, ExpFrame.total, ExpFrame.const]
  exact True.intro

end InferencePatterns


-- ═══════════════════════════════════════════════════════════════════════
-- §5–6 GENERICS BRIDGE
-- ═══════════════════════════════════════════════════════════════════════

section GenericsBridge

variable {W : Type*}

/-- **Generics as defaults** (@cite{veltman-1996}, §5–6).

    The truth conditions of the GEN operator ("P's are normally Q"):
        ∀w ∈ optimal(d). scope(w)
    are exactly the conditions for the "presumably" test to pass
    in update semantics.

    This theorem witnesses the structural identity: "all optimal worlds
    in a domain satisfy the scope" is just the definition of optimality
    restated. The substantive bridge is that `NormalityOrder.optimal`
    provides the normalcy predicate for GEN, and `NormalityOrder.refine`
    provides the dynamic mechanism for learning new generic rules. -/
theorem optimal_as_normalcy (no : NormalityOrder W) (d : Set W)
    (scope : W → Prop) :
    (∀ w ∈ no.optimal d, scope w) ↔
    ∀ w, w ∈ d → (∀ v ∈ d, no.le v w → no.le w v) → scope w := by
  constructor
  · intro h w hwd hopt; exact h w ⟨hwd, hopt⟩
  · intro h w ⟨hwd, hopt⟩; exact h w hwd hopt

end GenericsBridge


end Phenomena.DefaultReasoning.Studies.Veltman1996
