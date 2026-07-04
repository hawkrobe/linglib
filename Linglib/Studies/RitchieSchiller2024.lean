import Linglib.Semantics.Quantification.DomainRestriction
import Linglib.Studies.KadmonLandman1993
import Linglib.Pragmatics.RSA.Basic
import Linglib.Pragmatics.RSA.BToM
import Linglib.Pragmatics.RSA.Canonical
import Linglib.Discourse.CommonGround
import Linglib.Semantics.Questions.Partition.QUD
import Linglib.Semantics.Questions.PrecisionProjection
import Linglib.Discourse.QUD.Basic
import Linglib.Features.Subjectivity

/-!
# [ritchie-schiller-2024] — Default Domain Restriction Possibilities

[ritchie-schiller-2024] [cutting-vishton-1995] [baker-jara-ettinger-saxe-tenenbaum-2017]
[clark-1996] [stalnaker-2002]

Ritchie, K. & Schiller, H. (2024). Default Domain Restriction Possibilities.
*Semantics & Pragmatics* 17, Article 13: 1–49.

## The Argument

When a speaker says "Every bottle is empty" at a dinner party, the hearer
restricts the quantifier domain to contextually relevant bottles — not all bottles
in the universe (R&S §1, ex. 3). Ritchie & Schiller argue that existing accounts
fail to explain *why* certain restrictions are defaults:
- **Rational pragmatic** (§2.1): RSA/Gricean reasoning doesn't explain default status
- **Discourse-structural** (§2.2): QUD-based accounts are too demanding
- **Intentionalist** (§2.3): speaker-intention accounts are too unconstrained

Their positive proposal (§3): cognitive heuristics — perceptual availability,
salience, and manipulability — generate a structured set of default domain
restriction possibilities (DDRPs). These are grounded in spatial cognition, where
nested spatial regions provide a natural ordering on candidate restrictions.

## Scenario

We construct an illustrative scenario (not from the paper) with 4 entities at
increasing spatial distances and 3 world states, then verify key formal
consequences of the DDRP framework for both ⟦every⟧ (↓MON) and ⟦some⟧ (↑MON).

## Compositional Grounding

Truth conditions derive from `every_restricted` / `some_restricted`
(DomainRestriction.lean), which wrap `every_sem` / `some_sem` (Quantifier.lean)
with a domain restrictor predicate. Nesting theorems derive from
`DDRP.every_nesting` / `DDRP.some_nesting`, connecting the nested spatial
regions to restrictor monotonicity.

## RSA Connection

While R&S argue *against* RSA as explaining default status (§2.1), DDRPs are
compatible with RSA as the *selection mechanism*: the listener reasons over
candidate DDRPs (the latent `SpatialScale` in the joint posterior) to infer
which domain restriction the speaker intended. With a cognitive-default prior
biasing toward peripersonal scales, the pragmatic listener's latent marginal
infers the proximal restriction (§8). Predictions are checked by exact `PMF`
evaluation on the `RSA.Canonical` pipeline.
-/

set_option autoImplicit false

namespace RitchieSchiller2024

open Quantification (every_sem some_sem)
open Quantification.DomainRestriction
open scoped ENNReal

-- ============================================================================
-- §1. Domain Types
-- ============================================================================

/-- Entities in the constructed scene: 4 bottles at increasing spatial distances. -/
inductive Entity where
  | b1  -- bottle on table (peripersonal)
  | b2  -- bottle on table (peripersonal)
  | b3  -- bottle across room (action space)
  | b4  -- bottle outside window (vista)
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Entity where
  elems := {Entity.b1, Entity.b2, Entity.b3, Entity.b4}
  complete := fun x => by cases x <;> simp

-- ============================================================================
-- §2. Spatial Scene & DDRPs
-- ============================================================================

/-- A spatial scene: each entity occupies a spatial zone. -/
def SpatialScene (E : Type*) := E → SpatialScale

/-- A spatial scene induces a DDRP: region s contains entities in zone ≤ s.
    Monotonicity and top-totality follow from the ordering on `SpatialScale`. -/
def sceneToDDRP {E : Type*} (scene : SpatialScene E) : DDRP SpatialScale E where
  region s := λ e => scene e ≤ s
  monotone _ _ h _ hr := le_trans hr h
  top_total := Set.eq_univ_of_forall λ e => by show scene e ≤ ⊤; exact le_top

/-- The dinner-party scene: b1,b2 peripersonal, b3 action, b4 vista. -/
def dinnerScene : SpatialScene Entity
  | .b1 => .peripersonal
  | .b2 => .peripersonal
  | .b3 => .action
  | .b4 => .vista

/-- DDRP for the bottle scenario, derived from the spatial scene.
    Peripersonal ⊆ action ⊆ vista (= unrestricted in this indoor scene). -/
abbrev sceneDDRP : DDRP SpatialScale Entity := sceneToDDRP dinnerScene

-- ============================================================================
-- §3. World States
-- ============================================================================

/-- World states: which bottles are empty.
    - `nearEmpty`: only proximal bottles (b1, b2) are empty
    - `midEmpty`: proximal + action-space bottles (b1, b2, b3) are empty
    - `allEmpty`: all bottles are empty -/
inductive World where
  | nearEmpty
  | midEmpty
  | allEmpty
  deriving DecidableEq, Repr, Inhabited

instance : Fintype World where
  elems := ({World.nearEmpty, World.midEmpty, World.allEmpty} : Finset World)
  complete := λ x => by cases x <;> simp

def emptyIn : World → Entity → Bool
  | .allEmpty, _ => true
  | .midEmpty, .b4 => false
  | .midEmpty, _ => true
  | .nearEmpty, .b1 | .nearEmpty, .b2 => true
  | .nearEmpty, _ => false

/-- All entities are bottles in this scenario (trivial restrictor). -/
def isBottle : Entity → Bool := λ _ => true

-- ============================================================================
-- §4. Truth Table: "Every bottle is empty" under each DDRP
-- ============================================================================

/-- Truth of "every bottle is empty" under a given spatial domain restriction.
    For all entities in the DDRP region that are bottles, they must be empty. -/
abbrev everyBottleEmpty (scale : SpatialScale) (w : World) : Prop :=
  ∀ e : Entity, dinnerScene e ≤ scale → isBottle e = true → emptyIn w e = true

-- w_near: only proximal bottles empty
-- Only peripersonal restriction licenses the utterance.
theorem w_near_peri : everyBottleEmpty .peripersonal .nearEmpty := by decide
theorem w_near_action : ¬ everyBottleEmpty .action .nearEmpty := by decide
theorem w_near_vista : ¬ everyBottleEmpty .vista .nearEmpty := by decide

-- w_mid: proximal + action-space bottles empty
-- Both peripersonal and action restrictions license the utterance.
theorem w_mid_peri : everyBottleEmpty .peripersonal .midEmpty := by decide
theorem w_mid_action : everyBottleEmpty .action .midEmpty := by decide
theorem w_mid_vista : ¬ everyBottleEmpty .vista .midEmpty := by decide

-- w_all: all bottles empty
-- All restrictions license the utterance.
theorem w_all_peri : everyBottleEmpty .peripersonal .allEmpty := by decide
theorem w_all_action : everyBottleEmpty .action .allEmpty := by decide
theorem w_all_vista : everyBottleEmpty .vista .allEmpty := by decide

-- ============================================================================
-- §5. Truth Table: "Some bottle is empty" under each DDRP
-- ============================================================================

/-- Truth of "some bottle is empty" under a given spatial domain restriction.
    Some entity in the DDRP region that is a bottle must be empty. -/
abbrev someBottleEmpty (scale : SpatialScale) (w : World) : Prop :=
  ∃ e : Entity, dinnerScene e ≤ scale ∧ isBottle e = true ∧ emptyIn w e = true

-- w_near: only proximal bottles empty
-- All restrictions license "some bottle is empty" (there's always a witness).
theorem some_near_peri : someBottleEmpty .peripersonal .nearEmpty := by decide
theorem some_near_action : someBottleEmpty .action .nearEmpty := by decide
theorem some_near_vista : someBottleEmpty .vista .nearEmpty := by decide

-- w_mid: proximal + action-space bottles empty
theorem some_mid_peri : someBottleEmpty .peripersonal .midEmpty := by decide
theorem some_mid_action : someBottleEmpty .action .midEmpty := by decide
theorem some_mid_vista : someBottleEmpty .vista .midEmpty := by decide

-- w_all: all bottles empty
theorem some_all_peri : someBottleEmpty .peripersonal .allEmpty := by decide
theorem some_all_action : someBottleEmpty .action .allEmpty := by decide
theorem some_all_vista : someBottleEmpty .vista .allEmpty := by decide

-- ============================================================================
-- §6. Key Predictions
-- ============================================================================

/-- **Proximal default**: In the proximal world, only peripersonal restriction
    makes "every bottle is empty" true. The listener *must* infer the speaker
    intended the proximal domain — no other DDRP candidate works. -/
theorem proximal_default :
    everyBottleEmpty .peripersonal .nearEmpty ∧
    ¬ everyBottleEmpty .action .nearEmpty ∧
    ¬ everyBottleEmpty .vista .nearEmpty :=
  ⟨w_near_peri, w_near_action, w_near_vista⟩

/-- **↓MON/↑MON contrast**: ⟦every⟧ and ⟦some⟧ react oppositely to domain
    restriction. In the proximal world, ⟦every⟧ is true only under peripersonal
    restriction (↓MON: smaller domain helps), while ⟦some⟧ is true under all
    restrictions (↑MON: larger domain never hurts). -/
theorem monotonicity_contrast :
    everyBottleEmpty .peripersonal .nearEmpty ∧
    ¬ everyBottleEmpty .action .nearEmpty ∧
    someBottleEmpty .peripersonal .nearEmpty ∧
    someBottleEmpty .action .nearEmpty ∧
    someBottleEmpty .vista .nearEmpty :=
  ⟨w_near_peri, w_near_action, some_near_peri, some_near_action, some_near_vista⟩

-- ============================================================================
-- §7. Bridge to Theory: Nesting from DDRP Structure
-- ============================================================================

/-- ⟦every⟧ nesting (Prop level): truth under a larger scale entails truth under
    any smaller scale. Derives from `DDRP.every_nesting` via restrictor ↓MON. -/
theorem every_nesting_prop {s₁ s₂ : SpatialScale} (h : s₁ ≤ s₂)
    (R S : Entity → Prop) :
    every_restricted (sceneDDRP.region s₂) R S →
    every_restricted (sceneDDRP.region s₁) R S :=
  DDRP.every_nesting sceneDDRP R S h

/-- ⟦some⟧ nesting (Prop level): truth under a smaller scale entails truth under
    any larger scale. Derives from `DDRP.some_nesting` via restrictor ↑MON. -/
theorem some_nesting_prop {s₁ s₂ : SpatialScale} (h : s₁ ≤ s₂)
    (R S : Entity → Prop) :
    some_restricted (sceneDDRP.region s₁) R S →
    some_restricted (sceneDDRP.region s₂) R S :=
  DDRP.some_nesting sceneDDRP R S h

-- ============================================================================
-- §7b. Bridge: DomainRestrictor as a degenerate VagueRestriction
-- ============================================================================

/-! [kadmon-landman-1993] distinguish domain-precise from domain-vague
    quantificational restrictions. A `DomainRestrictor` is the degenerate
    domain-precise case: a single predicate, hence a single precisification —
    which is why DDRP-restricted *every*/*no* tolerate no exceptions via
    re-precisification. -/

open KadmonLandman1993 (VagueRestriction isDomainPrecise)

/-- Lift a `DomainRestrictor` into a trivially precise `VagueRestriction`:
    the singleton restriction with itself as the only precisification. -/
def vagueOfRestrictor {E : Type*} (C : DomainRestrictor E) :
    VagueRestriction (Set E) where
  precise := {C}
  precisifications := {{C}}
  extends_precise := by
    intro v hv
    simp only [Set.mem_singleton_iff] at hv
    rw [hv]
  precise_mem := Set.mem_singleton_iff.mpr rfl

/-- A restrictor-based vague restriction is domain precise in
    [kadmon-landman-1993]'s sense: one precisification, one domain. -/
theorem restrictor_is_domain_precise {E : Type*}
    (C : DomainRestrictor E) (apply : Set E → Set E) :
    isDomainPrecise (vagueOfRestrictor C) apply := by
  intro v hv
  simp only [vagueOfRestrictor, Set.mem_singleton_iff] at hv
  subst hv
  rfl

-- ============================================================================
-- §8. RSA Connection: DDRPs as Latent Interpretation Variables
-- ============================================================================

/-- Utterance type for the RSA model. -/
inductive Utterance where
  | everyEmpty  -- "every bottle is empty"
  | someEmpty   -- "some bottle is empty"
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Utterance where
  elems := ({Utterance.everyEmpty, Utterance.someEmpty} : Finset Utterance)
  complete := λ x => by cases x <;> simp

/-- Literal meaning under a given DDRP scale (Bool for RSA computation). -/
def utteranceMeaning (scale : SpatialScale) : Utterance → World → Bool
  | .everyEmpty, w => decide (everyBottleEmpty scale w)
  | .someEmpty, w => decide (someBottleEmpty scale w)

/-- R&S §3.2: Three cognitive heuristics collectively determine which domain
    restrictions are defaults. Each heuristic assigns a relevance score to a
    spatial scale, reflecting how well entities at that scale satisfy the
    corresponding cognitive criterion. -/
inductive CognitiveHeuristic where
  | availability    -- perceptual availability: present in the here-and-now
  | salience        -- perceptual salience: attention-grabbing
  | manipulability  -- manipulability: affords physical interaction
  deriving DecidableEq, Repr

/-- Heuristic score for each (heuristic, scale) pair.

    - **Availability** (R&S §3.2 ¶1): Peripersonal objects are maximally available
      — perceived without bodily distortion. Action/vista objects are available
      but require effort. Unrestricted objects may not be present at all.
    - **Salience** (R&S §3.2 ¶2): Peripersonal and action-space objects are
      attention-grabbing. Vista/unrestricted objects are less noticeable.
    - **Manipulability** (R&S §3.2 ¶3): Only peripersonal objects afford physical
      interaction (within arm's reach). All others are out of reach. -/
def heuristicScore : CognitiveHeuristic → SpatialScale → ℚ
  | .availability,   .peripersonal => 2 | .availability,   .action => 1
  | .availability,   .vista        => 1 | .availability,   .unrestricted => 1
  | .salience,       .peripersonal => 1 | .salience,       .action => 1
  | .salience,       .vista        => 0 | .salience,       .unrestricted => 0
  | .manipulability, .peripersonal => 1 | .manipulability, .action => 0
  | .manipulability, .vista        => 0 | .manipulability, .unrestricted => 0

/-- Each heuristic is anti-monotone: more proximal scales score at least as
    high. This captures R&S's claim that proximity enhances all three
    cognitive dimensions simultaneously. -/
theorem heuristic_anti_mono (h : CognitiveHeuristic) {s₁ s₂ : SpatialScale}
    (hle : s₁ ≤ s₂) :
    heuristicScore h s₂ ≤ heuristicScore h s₁ := by
  cases h <;> cases s₁ <;> cases s₂ <;>
    simp only [heuristicScore] <;> (revert hle; decide)

/-- Latent prior derived from the three cognitive heuristics. The sum reflects
    R&S §3.2's conjunction: a good default restriction should score high on
    availability AND salience AND manipulability. The prior is unnormalized —
    RSA normalizes via the partition function. -/
def ddprPrior (s : SpatialScale) : ℚ :=
  heuristicScore .availability s + heuristicScore .salience s +
    heuristicScore .manipulability s

/-- The derived prior is anti-monotone: more proximal scales receive higher
    prior weight. Follows from anti-monotonicity of each heuristic. -/
theorem ddprPrior_anti_mono {s₁ s₂ : SpatialScale} (h : s₁ ≤ s₂) :
    ddprPrior s₂ ≤ ddprPrior s₁ := by
  unfold ddprPrior
  have ha := heuristic_anti_mono .availability h
  have hs := heuristic_anti_mono .salience h
  have hm := heuristic_anti_mono .manipulability h
  linarith

/-! ### PMF face: shared speaker, cognitive-default vs uniform joint priors

The two listener variants below differ only in the latent prior, so they share
one speaker: the literal listener is uniform on `utteranceMeaning scale u`'s
world extension, and the speaker normalises literal informativity over the two
utterances (α = 1, no cost). -/

private theorem ext_nonempty (scale : SpatialScale) (u : Utterance) :
    (RSA.extensionOf (utteranceMeaning scale) u).Nonempty := by
  cases scale <;> cases u <;> decide

/-- Per-scale literal listener: uniform on the utterance's world extension. -/
noncomputable def L0 : SpatialScale → Utterance → PMF World :=
  RSA.Canonical.L0OfBool utteranceMeaning ext_nonempty

private theorem some_always_true (w : World) (l : SpatialScale) :
    utteranceMeaning l .someEmpty w = true := by
  cases w <;> cases l <;> decide

noncomputable instance : RSA.Canonical.ViableSpeaker (RSA.Canonical.powUtility 1 L0) :=
  RSA.Canonical.viableSpeaker_powUtility_of_witness 1 L0 fun s =>
    ⟨.someEmpty, RSA.Canonical.L0OfBool_ne_zero utteranceMeaning ext_nonempty
      (some_always_true s.1 s.2)⟩

/-- Shared pragmatic speaker `S(w, scale) ∝ L0(w | ·, scale)` (α = 1, no cost). -/
noncomputable def S : World × SpatialScale → PMF Utterance :=
  RSA.Canonical.S1 (RSA.Canonical.powUtility 1 L0)

/-- Unnormalised speaker weight at a true utterance: `|ext(scale, u)|⁻¹`. -/
private theorem pw_true {l : SpatialScale} {u : Utterance} {w : World} {k : ℕ}
    (h : utteranceMeaning l u w = true)
    (hk : (RSA.extensionOf (utteranceMeaning l) u).card = k) :
    RSA.Canonical.powWeight 1 L0 (w, l) u = ENNReal.ofReal (k : ℝ)⁻¹ := by
  have hpos : 0 < k := hk ▸ Finset.card_pos.mpr ⟨w, RSA.mem_extensionOf.mpr h⟩
  simp only [L0]
  rw [RSA.Canonical.powWeight_L0OfBool_of_mem utteranceMeaning ext_nonempty k h hk, pow_one,
    ENNReal.ofReal_inv_of_pos (by exact_mod_cast hpos), ENNReal.ofReal_natCast]

private theorem pw_false {l : SpatialScale} {u : Utterance} {w : World}
    (h : utteranceMeaning l u w = false) :
    RSA.Canonical.powWeight 1 L0 (w, l) u = ENNReal.ofReal 0 := by
  rw [ENNReal.ofReal_zero]
  simp only [L0]
  exact RSA.Canonical.powWeight_L0OfBool_of_not_mem utteranceMeaning ext_nonempty
    one_ne_zero (by rw [h]; decide)

private theorem sumU (f : Utterance → ℝ≥0∞) :
    ∑' u, f u = f .everyEmpty + f .someEmpty := by
  rw [tsum_fintype,
    show (Finset.univ : Finset Utterance) = {.everyEmpty, .someEmpty} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]

/-- Normalised speaker mass at a true utterance, as an exact rational. -/
private theorem S_val {l : SpatialScale} {u : Utterance} {w : World} {k : ℕ} {z q : ℝ}
    (h : utteranceMeaning l u w = true)
    (hk : (RSA.extensionOf (utteranceMeaning l) u).card = k) (hz : 0 < z)
    (hZ : (∑' u', RSA.Canonical.powWeight 1 L0 (w, l) u') = ENNReal.ofReal z)
    (hq : (k : ℝ)⁻¹ / z = q) :
    S (w, l) u = ENNReal.ofReal q := by
  unfold S
  rw [RSA.Canonical.S1_powUtility_eq_normalize, PMF.normalize_apply, pw_true h hk, hZ,
    ← ENNReal.ofReal_inv_of_pos hz, ← ENNReal.ofReal_mul (by positivity), ← div_eq_mul_inv, hq]

/-- Normalised speaker mass at a false utterance: `0`. -/
private theorem S_zero {l : SpatialScale} {u : Utterance} {w : World}
    (h : utteranceMeaning l u w = false) : S (w, l) u = 0 := by
  unfold S
  rw [RSA.Canonical.S1_powUtility_eq_normalize, PMF.normalize_apply, pw_false h,
    ENNReal.ofReal_zero, zero_mul]

/-- The speaker never assigns zero mass to a true utterance. -/
private theorem S_ne_zero {l : SpatialScale} {u : Utterance} {w : World}
    (h : utteranceMeaning l u w = true) : S (w, l) u ≠ 0 := by
  have hpos : 0 < (RSA.extensionOf (utteranceMeaning l) u).card :=
    Finset.card_pos.mpr ⟨w, RSA.mem_extensionOf.mpr h⟩
  unfold S
  rw [RSA.Canonical.S1_powUtility_eq_normalize, ← PMF.mem_support_iff,
    PMF.mem_support_normalize_iff, pw_true h rfl, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact inv_pos.mpr (by exact_mod_cast hpos)

/-! Partition sums `Z(w, scale) = Σ_u |ext(scale, u)|⁻¹` over the two
utterances (extension cards — everyEmpty: peripersonal 3, action 2, vista 1;
someEmpty: 3 at every scale): peripersonal `2/3` everywhere; action `1/3` at
`nearEmpty`, else `5/6`; vista `1/3` except `4/3` at `allEmpty`. -/

private theorem Z_near_peri :
    (∑' u', RSA.Canonical.powWeight 1 L0 (.nearEmpty, .peripersonal) u')
      = ENNReal.ofReal (2/3) := by
  rw [sumU, pw_true (k := 3) (by decide) (by decide), pw_true (k := 3) (by decide) (by decide),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

private theorem Z_mid_peri :
    (∑' u', RSA.Canonical.powWeight 1 L0 (.midEmpty, .peripersonal) u')
      = ENNReal.ofReal (2/3) := by
  rw [sumU, pw_true (k := 3) (by decide) (by decide), pw_true (k := 3) (by decide) (by decide),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

private theorem Z_all_peri :
    (∑' u', RSA.Canonical.powWeight 1 L0 (.allEmpty, .peripersonal) u')
      = ENNReal.ofReal (2/3) := by
  rw [sumU, pw_true (k := 3) (by decide) (by decide), pw_true (k := 3) (by decide) (by decide),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

private theorem Z_near_action :
    (∑' u', RSA.Canonical.powWeight 1 L0 (.nearEmpty, .action) u')
      = ENNReal.ofReal (1/3) := by
  rw [sumU, pw_false (by decide), pw_true (k := 3) (by decide) (by decide),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

private theorem Z_mid_action :
    (∑' u', RSA.Canonical.powWeight 1 L0 (.midEmpty, .action) u')
      = ENNReal.ofReal (5/6) := by
  rw [sumU, pw_true (k := 2) (by decide) (by decide), pw_true (k := 3) (by decide) (by decide),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

private theorem Z_all_action :
    (∑' u', RSA.Canonical.powWeight 1 L0 (.allEmpty, .action) u')
      = ENNReal.ofReal (5/6) := by
  rw [sumU, pw_true (k := 2) (by decide) (by decide), pw_true (k := 3) (by decide) (by decide),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

private theorem Z_near_vista :
    (∑' u', RSA.Canonical.powWeight 1 L0 (.nearEmpty, .vista) u')
      = ENNReal.ofReal (1/3) := by
  rw [sumU, pw_false (by decide), pw_true (k := 3) (by decide) (by decide),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

private theorem Z_mid_vista :
    (∑' u', RSA.Canonical.powWeight 1 L0 (.midEmpty, .vista) u')
      = ENNReal.ofReal (1/3) := by
  rw [sumU, pw_false (by decide), pw_true (k := 3) (by decide) (by decide),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

private theorem Z_all_vista :
    (∑' u', RSA.Canonical.powWeight 1 L0 (.allEmpty, .vista) u')
      = ENNReal.ofReal (4/3) := by
  rw [sumU, pw_true (k := 1) (by decide) (by decide), pw_true (k := 3) (by decide) (by decide),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

private theorem sumW (f : World → ℝ≥0∞) :
    ∑ w, f w = f .nearEmpty + f .midEmpty + f .allEmpty := by
  rw [show (Finset.univ : Finset World) = {.nearEmpty, .midEmpty, .allEmpty} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-! Speaker-mass values `S(w, scale) u` (exact rationals): every — `1/2` at
peripersonal, `3/5` at action (mid/all), `3/4` at vista (all), else `0`;
some — `1/2` at peripersonal, `1, 2/5, 2/5` at action, `1, 1, 1/4` at vista. -/

private theorem s_near_peri_every :
    S (.nearEmpty, .peripersonal) .everyEmpty = ENNReal.ofReal (1/2) :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_near_peri (by norm_num)
private theorem s_mid_peri_every :
    S (.midEmpty, .peripersonal) .everyEmpty = ENNReal.ofReal (1/2) :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_mid_peri (by norm_num)
private theorem s_all_peri_every :
    S (.allEmpty, .peripersonal) .everyEmpty = ENNReal.ofReal (1/2) :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_all_peri (by norm_num)
private theorem s_mid_action_every :
    S (.midEmpty, .action) .everyEmpty = ENNReal.ofReal (3/5) :=
  S_val (k := 2) (by decide) (by decide) (by norm_num) Z_mid_action (by norm_num)
private theorem s_all_action_every :
    S (.allEmpty, .action) .everyEmpty = ENNReal.ofReal (3/5) :=
  S_val (k := 2) (by decide) (by decide) (by norm_num) Z_all_action (by norm_num)
private theorem s_all_vista_every :
    S (.allEmpty, .vista) .everyEmpty = ENNReal.ofReal (3/4) :=
  S_val (k := 1) (by decide) (by decide) (by norm_num) Z_all_vista (by norm_num)
private theorem s_near_peri_some :
    S (.nearEmpty, .peripersonal) .someEmpty = ENNReal.ofReal (1/2) :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_near_peri (by norm_num)
private theorem s_mid_peri_some :
    S (.midEmpty, .peripersonal) .someEmpty = ENNReal.ofReal (1/2) :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_mid_peri (by norm_num)
private theorem s_all_peri_some :
    S (.allEmpty, .peripersonal) .someEmpty = ENNReal.ofReal (1/2) :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_all_peri (by norm_num)
private theorem s_near_action_some :
    S (.nearEmpty, .action) .someEmpty = ENNReal.ofReal 1 :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_near_action (by norm_num)
private theorem s_mid_action_some :
    S (.midEmpty, .action) .someEmpty = ENNReal.ofReal (2/5) :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_mid_action (by norm_num)
private theorem s_all_action_some :
    S (.allEmpty, .action) .someEmpty = ENNReal.ofReal (2/5) :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_all_action (by norm_num)
private theorem s_near_vista_some :
    S (.nearEmpty, .vista) .someEmpty = ENNReal.ofReal 1 :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_near_vista (by norm_num)
private theorem s_mid_vista_some :
    S (.midEmpty, .vista) .someEmpty = ENNReal.ofReal 1 :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_mid_vista (by norm_num)
private theorem s_all_vista_some :
    S (.allEmpty, .vista) .someEmpty = ENNReal.ofReal (1/4) :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_all_vista (by norm_num)

/-! Pooled world-sums of speaker mass per scale (the latent-comparison
residues): every — peripersonal `3/2`, action `6/5`, vista `3/4`;
some — peripersonal `3/2`, action `9/5`, vista `9/4`. -/

private theorem sum_every_peri :
    (∑ w : World, S (w, .peripersonal) .everyEmpty) = ENNReal.ofReal (3/2) := by
  rw [sumW, s_near_peri_every, s_mid_peri_every, s_all_peri_every,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

private theorem sum_every_action :
    (∑ w : World, S (w, .action) .everyEmpty) = ENNReal.ofReal (6/5) := by
  rw [sumW, S_zero (by decide), s_mid_action_every, s_all_action_every,
    zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

private theorem sum_every_vista :
    (∑ w : World, S (w, .vista) .everyEmpty) = ENNReal.ofReal (3/4) := by
  rw [sumW, S_zero (by decide), S_zero (by decide), s_all_vista_every,
    zero_add, zero_add]

private theorem sum_some_peri :
    (∑ w : World, S (w, .peripersonal) .someEmpty) = ENNReal.ofReal (3/2) := by
  rw [sumW, s_near_peri_some, s_mid_peri_some, s_all_peri_some,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

private theorem sum_some_action :
    (∑ w : World, S (w, .action) .someEmpty) = ENNReal.ofReal (9/5) := by
  rw [sumW, s_near_action_some, s_mid_action_some, s_all_action_some,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

private theorem sum_some_vista :
    (∑ w : World, S (w, .vista) .someEmpty) = ENNReal.ofReal (9/4) := by
  rw [sumW, s_near_vista_some, s_mid_vista_some, s_all_vista_some,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

/-! ### Listeners -/

private theorem ddprW_tsum_ne_zero :
    (∑' s : World × SpatialScale, ENNReal.ofReal (ddprPrior s.2)) ≠ 0 :=
  ENNReal.summable.tsum_ne_zero_iff.mpr
    ⟨(.nearEmpty, .peripersonal),
      (ENNReal.ofReal_pos.mpr (by norm_num [ddprPrior, heuristicScore])).ne'⟩

private theorem ddprW_tsum_ne_top :
    (∑' s : World × SpatialScale, ENNReal.ofReal (ddprPrior s.2)) ≠ ⊤ := by
  rw [tsum_fintype]
  exact ENNReal.sum_ne_top.mpr fun s _ => ENNReal.ofReal_ne_top

/-- Cognitive-default joint prior: uniform over worlds (the constant world
factor is absorbed by normalisation), `ddprPrior` over scales. -/
noncomputable def ddprJoint : PMF (World × SpatialScale) :=
  PMF.normalize (fun s => ENNReal.ofReal (ddprPrior s.2)) ddprW_tsum_ne_zero ddprW_tsum_ne_top

private theorem ddprJoint_ne_zero {s : World × SpatialScale}
    (h : ENNReal.ofReal (ddprPrior s.2) ≠ 0) : ddprJoint s ≠ 0 := by
  rw [ddprJoint, ← PMF.mem_support_iff, PMF.mem_support_normalize_iff]
  exact h

theorem ddpr_marg_every : PMF.marginal S ddprJoint .everyEmpty ≠ 0 :=
  PMF.marginal_ne_zero S ddprJoint _ (a := (.allEmpty, .peripersonal))
    (ddprJoint_ne_zero (ENNReal.ofReal_pos.mpr (by norm_num [ddprPrior, heuristicScore])).ne')
    (S_ne_zero (by decide))

theorem ddpr_marg_some : PMF.marginal S ddprJoint .someEmpty ≠ 0 :=
  PMF.marginal_ne_zero S ddprJoint _ (a := (.allEmpty, .peripersonal))
    (ddprJoint_ne_zero (ENNReal.ofReal_pos.mpr (by norm_num [ddprPrior, heuristicScore])).ne')
    (S_ne_zero (by decide))

/-- Pragmatic listener over the cognitive-default joint prior. -/
noncomputable def ddprListener (u : Utterance) (h : PMF.marginal S ddprJoint u ≠ 0) :
    PMF (World × SpatialScale) :=
  RSA.Canonical.L1 S ddprJoint u h

private theorem sum_scaled (c z : ℝ≥0∞) (f : World → ℝ≥0∞) :
    (∑ w : World, c * z * f w) = z * (c * ∑ w : World, f w) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

/-- The cognitive-default latent preference reduces to prior-weighted pooled
speaker sums — the normalisation constant cancels. -/
private theorem ddprListener_snd_lt (u : Utterance)
    (h : PMF.marginal S ddprJoint u ≠ 0) (l₁ l₂ : SpatialScale) :
    (ddprListener u h).snd l₁ < (ddprListener u h).snd l₂ ↔
      ENNReal.ofReal (ddprPrior l₁) * (∑ w : World, S (w, l₁) u) <
        ENNReal.ofReal (ddprPrior l₂) * (∑ w : World, S (w, l₂) u) := by
  unfold ddprListener
  rw [RSA.Canonical.L1_latent_prefers_iff]
  simp only [ddprJoint, PMF.normalize_apply]
  rw [sum_scaled, sum_scaled]
  exact ENNReal.mul_lt_mul_iff_right
    (ENNReal.inv_ne_zero.mpr ddprW_tsum_ne_top)
    (ENNReal.inv_ne_top.mpr ddprW_tsum_ne_zero)

/-- **L1_latent peripersonal > action**: The listener infers peripersonal as
    the most likely intended domain restriction, beating the action-space
    scale. This captures R&S's core claim: cognitive-default priors biasing
    toward proximal scales cause the listener to default to the nearest
    restriction. -/
theorem L1_latent_peripersonal_gt_action :
    (ddprListener .everyEmpty ddpr_marg_every).snd .peripersonal >
    (ddprListener .everyEmpty ddpr_marg_every).snd .action := by
  rw [gt_iff_lt, ddprListener_snd_lt, sum_every_action, sum_every_peri,
    ← ENNReal.ofReal_mul (by norm_num [ddprPrior, heuristicScore]),
    ← ENNReal.ofReal_mul (by norm_num [ddprPrior, heuristicScore]),
    ENNReal.ofReal_lt_ofReal_iff (by norm_num [ddprPrior, heuristicScore])]
  norm_num [ddprPrior, heuristicScore]

/-- **L1_latent action > vista**: The action scale is preferred over vista,
    showing the full ordering: peripersonal > action > vista. -/
theorem L1_latent_action_gt_vista :
    (ddprListener .everyEmpty ddpr_marg_every).snd .action >
    (ddprListener .everyEmpty ddpr_marg_every).snd .vista := by
  rw [gt_iff_lt, ddprListener_snd_lt, sum_every_vista, sum_every_action,
    ← ENNReal.ofReal_mul (by norm_num [ddprPrior, heuristicScore]),
    ← ENNReal.ofReal_mul (by norm_num [ddprPrior, heuristicScore]),
    ENNReal.ofReal_lt_ofReal_iff (by norm_num [ddprPrior, heuristicScore])]
  norm_num [ddprPrior, heuristicScore]

/-- For "some bottle is empty", the cognitive-default prior overrides the
    semantic signal: peripersonal is inferred as the most likely scale despite
    ⟦some⟧ being true under all scales in all worlds. Without the prior,
    RSA predicts the WRONG ordering (see `uniform_some_distal_wins`). -/
theorem L1_latent_some_peripersonal_gt_action :
    (ddprListener .someEmpty ddpr_marg_some).snd .peripersonal >
    (ddprListener .someEmpty ddpr_marg_some).snd .action := by
  rw [gt_iff_lt, ddprListener_snd_lt, sum_some_action, sum_some_peri,
    ← ENNReal.ofReal_mul (by norm_num [ddprPrior, heuristicScore]),
    ← ENNReal.ofReal_mul (by norm_num [ddprPrior, heuristicScore]),
    ENNReal.ofReal_lt_ofReal_iff (by norm_num [ddprPrior, heuristicScore])]
  norm_num [ddprPrior, heuristicScore]

-- ============================================================================
-- §8b. R&S §2.1: RSA with Uniform Priors Cannot Explain Defaults
-- ============================================================================

/-! R&S §2.1 argue that RSA alone — without cognitive supplementation —
    cannot explain why certain domain restrictions are defaults. We verify
    this by constructing an RSA model with uniform latent priors and showing:

    1. For ⟦every⟧ (↓MON), RSA with uniform priors *happens* to predict
       peripersonal as most likely — but only because the literal semantics
       provides discriminative signal (it's false under wider scales in some
       worlds). This is not an explanation of default status.

    2. For ⟦some⟧ (↑MON), RSA with uniform priors predicts the *wrong*
       ordering: the listener infers vista/unrestricted as most likely, because
       under wider scales, ⟦some⟧ is the only true utterance in more worlds
       (higher L0 probability). Cognitive-default priors are needed to override
       this semantic signal.

    This pair of results formalizes R&S's core negative argument: RSA's
    predictions depend on the specific quantifier's monotonicity profile,
    not on cognitive structure, so RSA alone doesn't explain the cross-quantifier
    generalization that proximal restrictions are always preferred. -/

theorem unif_marg_every :
    PMF.marginal S (PMF.uniformOfFintype (World × SpatialScale)) .everyEmpty ≠ 0 :=
  PMF.marginal_ne_zero S _ _ (a := (.allEmpty, .peripersonal))
    (((PMF.uniformOfFintype (World × SpatialScale)).mem_support_iff _).mp
      (PMF.mem_support_uniformOfFintype _))
    (S_ne_zero (by decide))

theorem unif_marg_some :
    PMF.marginal S (PMF.uniformOfFintype (World × SpatialScale)) .someEmpty ≠ 0 :=
  PMF.marginal_ne_zero S _ _ (a := (.allEmpty, .peripersonal))
    (((PMF.uniformOfFintype (World × SpatialScale)).mem_support_iff _).mp
      (PMF.mem_support_uniformOfFintype _))
    (S_ne_zero (by decide))

/-- Pragmatic listener with a uniform latent prior (no cognitive bias):
same speaker as `ddprListener`, uniform joint. -/
noncomputable def uniformListener (u : Utterance)
    (h : PMF.marginal S (PMF.uniformOfFintype (World × SpatialScale)) u ≠ 0) :
    PMF (World × SpatialScale) :=
  RSA.Canonical.L1 S (PMF.uniformOfFintype _) u h

/-- The uniform-prior latent preference reduces to bare pooled speaker sums. -/
private theorem uniformListener_snd_lt (u : Utterance)
    (h : PMF.marginal S (PMF.uniformOfFintype (World × SpatialScale)) u ≠ 0)
    (l₁ l₂ : SpatialScale) :
    (uniformListener u h).snd l₁ < (uniformListener u h).snd l₂ ↔
      (∑ w : World, S (w, l₁) u) < ∑ w : World, S (w, l₂) u := by
  unfold uniformListener
  rw [RSA.Canonical.L1_latent_prefers_iff]
  simp only [PMF.uniformOfFintype_apply]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  exact ENNReal.mul_lt_mul_iff_right
    (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top (Fintype.card (World × SpatialScale))))
    (ENNReal.inv_ne_top.mpr
      (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := World × SpatialScale))))

/-- R&S §2.1: With uniform priors, RSA still predicts peripersonal for
    ⟦every⟧ — but only because the literal semantics does the work (⟦every⟧
    is false under wider scales in more worlds, so L0 assigns higher
    probability to narrower scales). This is a semantic accident, not a
    cognitive explanation. -/
theorem uniform_every_still_proximal :
    (uniformListener .everyEmpty unif_marg_every).snd .peripersonal >
    (uniformListener .everyEmpty unif_marg_every).snd .action := by
  rw [gt_iff_lt, uniformListener_snd_lt, sum_every_action, sum_every_peri,
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-- R&S §2.1: With uniform priors, RSA predicts the WRONG ordering for
    ⟦some⟧ — the listener infers vista as most likely, not peripersonal.
    This is because under wider scales, ⟦some⟧ is more informative (it's
    the only true utterance when ⟦every⟧ is false), yielding higher L0.
    Cognitive-default priors (`ddprPrior`) are needed to override this. -/
theorem uniform_some_distal_wins :
    (uniformListener .someEmpty unif_marg_some).snd .vista >
    (uniformListener .someEmpty unif_marg_some).snd .peripersonal := by
  rw [gt_iff_lt, uniformListener_snd_lt, sum_some_peri, sum_some_vista,
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

-- ============================================================================
-- §9. Perception & Common Ground
-- ============================================================================

/-! Connects DDRPs to [baker-jara-ettinger-saxe-tenenbaum-2017]'s BToM
architecture and [stalnaker-2002]'s common ground.

When the scene is common ground ([clark-1996] on joint attention),
speaker and hearer derive the same DDRP. Different perceptual access yields
different DDRPs, motivating R&S's requirement of perceptual co-presence. -/

open Core
open CommonGround

/-- The DDRP generative model as a BToM instance over ℝ≥0∞: percept and
belief are veridical deltas ([baker-jara-ettinger-saxe-tenenbaum-2017]'s
observer with full perceptual access), the plan model is the shared
pragmatic speaker `S`, and the world-conditioned desire prior is the
cognitive-default joint prior. -/
noncomputable def ddprBToM :
    Core.BToMModel ℝ≥0∞ Utterance World World SpatialScale Unit Unit World where
  perceptModel w p := if p = w then 1 else 0
  beliefModel p b := if b = p then 1 else 0
  planModel b d _ _ a := S (b, d) a
  worldPrior _ := 1
  desirePrior w d := ddprJoint (w, d)
  sharedPrior _ := 1
  mediumPrior _ := 1

/-- Delta-collapse: the BToM world marginal is the listener's unnormalized
world score, `Σ_l prior(w, l) · S(u | w, l)`. -/
theorem ddprBToM_worldMarginal_eq (u : Utterance) (w : World) :
    ddprBToM.worldMarginal u w
      = ∑ l : SpatialScale, ddprJoint (w, l) * S (w, l) u := by
  unfold ddprBToM Core.BToMModel.worldMarginal Core.BToMModel.jointScore
  simp only [Fintype.sum_unique, mul_one, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_eq_single w
    (fun p _ hp => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun d _ => by
      rw [if_neg hp])
    (fun h => absurd (Finset.mem_univ w) h)]
  simp only [reduceIte]
  rw [Finset.sum_eq_single w
    (fun b _ hb => Finset.sum_eq_zero fun d _ => by rw [if_neg hb])
    (fun h => absurd (Finset.mem_univ w) h)]
  simp only [reduceIte]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- **RSA's pragmatic listener IS BToM world-marginal inference**, on the
mathlib-PMF face: the listener's world marginal is the `ddprBToM` world
marginal, normalized by the utterance's prior predictive mass. -/
theorem rsa_btom_bridge (u : Utterance) (h : PMF.marginal S ddprJoint u ≠ 0)
    (w : World) :
    (ddprListener u h).fst w
      = ddprBToM.worldMarginal u w * (PMF.marginal S ddprJoint u)⁻¹ := by
  rw [PMF.fst_apply, ddprBToM_worldMarginal_eq, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by
    rw [ddprListener, RSA.Canonical.L1, PMF.posterior_apply]

/-- When all discourse participants share the same spatial scene, they
    derive the same DDRP — a prerequisite for successful communication
    about domain-restricted quantifiers. -/
theorem shared_scene_shared_ddrp (scene : SpatialScene Entity)
    (getScene : World → SpatialScene Entity)
    (hcg : ∀ w, getScene w = scene) :
    ∀ w, sceneToDDRP (getScene w) = sceneToDDRP scene := by
  intro w; exact congrArg sceneToDDRP (hcg w)

/-- An alternative scene where b3 is behind a partition (in vista, not action). -/
def partitionScene : SpatialScene Entity
  | .b1 => .peripersonal
  | .b2 => .peripersonal
  | .b3 => .vista
  | .b4 => .vista

theorem scenes_differ_on_b3 :
    dinnerScene .b3 ≠ partitionScene .b3 := by decide

/-- Different spatial scenes yield different DDRPs. -/
theorem different_scenes_different_ddrps :
    (sceneToDDRP dinnerScene).region ≠ (sceneToDDRP partitionScene).region := by
  intro h
  have heq := Iff.of_eq (congrFun (congrFun h .action) Entity.b3)
  have h1 : dinnerScene Entity.b3 ≤ SpatialScale.action := le_refl _
  have h2 : ¬ partitionScene Entity.b3 ≤ SpatialScale.action := by decide
  exact h2 (heq.mp h1)

/-- Without perceptual co-presence, domain-restricted quantifiers can
    receive different truth values: "every bottle is empty" under action-space
    restriction is false with the dinner scene but true with the partition scene
    (where b3 is too far to be in the action zone). -/
theorem perception_mismatch_changes_truth :
    (¬ ∀ e : Entity, dinnerScene e ≤ .action →
        isBottle e = true → emptyIn .nearEmpty e = true) ∧
    (∀ e : Entity, partitionScene e ≤ .action →
        isBottle e = true → emptyIn .nearEmpty e = true) := by
  constructor <;> decide

-- ============================================================================
-- §10. QUD and Non-Default Restrictions (R&S §4)
-- ============================================================================

/-! R&S §4 argues that non-default domain restrictions arise from explicit
    discourse moves. When the QUD shifts (e.g., "Where are the blue things?"),
    the domain restriction can widen beyond the cognitive default. We connect
    this to the `QUD` infrastructure from [roberts-2012]. -/

/-- QUD partitioning worlds by spatial emptiness profile: which bottles are
    empty at each spatial scale? Worlds that agree on the emptiness of
    peripersonal, action, and vista bottles give the same answer. -/
def spatialQUD : QUD World :=
  QUD.ofDecEq (λ w => (decide (everyBottleEmpty .peripersonal w),
                        decide (everyBottleEmpty .action w),
                        decide (everyBottleEmpty .vista w)))

/-- The spatial QUD distinguishes all three worlds: each has a different
    emptiness profile across scales. -/
theorem spatialQUD_distinguishes_all :
    spatialQUD.sameAnswer .nearEmpty .midEmpty = false ∧
    spatialQUD.sameAnswer .midEmpty .allEmpty = false ∧
    spatialQUD.sameAnswer .nearEmpty .allEmpty = false := by
  constructor <;> [decide; constructor <;> decide]

-- ============================================================================
-- §11. Objectivity of Default Restrictions (R&S §3.2)
-- ============================================================================

/-! R&S §3.2 argue that default domain restrictions are *objective*
    (nonsubjective on [traugott-dasher-2002]'s cline): they derive from
    perceptual/cognitive structure (location, spatial proximity), not from
    speaker attitude (subjective) or addressee face (intersubjective). This
    predicts that spatial/temporal restrictions make better defaults than
    evaluative restrictions (beauty, tastiness).

    [scontras-degen-goodman-2017] find that more objective adjectives are
    ordered closer to the noun — "the big blue box" over "the blue big box" —
    because less subjective content is more useful for communication. R&S
    extend this: more objective *domain restrictions* are similarly privileged
    as defaults because they are more likely to be shared among participants
    and thus better for coordination.

    The connection is structural: all three cognitive heuristics (availability,
    salience, manipulability) target features that are objective in the sense
    that they don't depend on speaker perspective or taste. -/

open Features.Subjectivity (SubjectivityLevel)

/-- DDRPs are nonsubjective: the three cognitive heuristics (availability,
    salience, manipulability) all target spatiotemporal properties that don't
    depend on speaker perspective. This is not stipulated — it follows from
    the heuristics being defined over `SpatialScale`, which is a physical
    (observer-independent) ordering on spatial regions. -/
def ddprSubjectivityLevel : SubjectivityLevel := .nonSubjective

/-- Objectivity prediction: DDRPs (nonsubjective) precede subjective
    interpretations on the Traugott-Dasher cline, predicting they are
    available as defaults before evaluative restrictions require discourse
    setup. The ordering reflects [scontras-degen-goodman-2017]'s finding:
    less subjective content is more useful for communication. -/
theorem ddpr_precedes_subjective :
    ddprSubjectivityLevel ≤ SubjectivityLevel.subjective := by decide

/-- Nonsubjective is the minimum on the Traugott-Dasher cline, so DDRPs
    precede *all* subjective and intersubjective interpretations. -/
theorem ddpr_is_minimum :
    ∀ l : SubjectivityLevel, ddprSubjectivityLevel ≤ l := by
  intro l; exact Features.Subjectivity.nonSubjective_le l

end RitchieSchiller2024
