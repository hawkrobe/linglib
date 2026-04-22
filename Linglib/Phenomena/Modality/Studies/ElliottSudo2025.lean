import Linglib.Theories.Semantics.Dynamic.Bilateral.BUS

/-!
# Elliott & Sudo (2025): Free Choice with Anaphora
@cite{elliott-sudo-2025}

Bilateral Update Semantics (BUS) applied to bathroom disjunctions.

## The puzzle

Bathroom disjunction: "Either there's no bathroom or it's in a funny place."

From this, we infer:
1. It's possible there's no bathroom
2. It's possible there's a bathroom AND it's in a funny place

The pronoun "it" in the second disjunct is bound by the existential in the
negated first disjunct. This cross-disjunct anaphora is puzzling because:
- Standard FC: ◇(φ ∨ ψ) → ◇φ ∧ ◇ψ (no anaphoric connection)
- With anaphora: ◇(¬∃xφ ∨ ψ(x)) → ◇¬∃xφ ∧ ◇(∃x(φ ∧ ψ(x)))

## Solution

BUS + Modal Disjunction:
1. Disjunction semantics: φ ∨ ψ entails ◇φ ∧ ◇ψ
2. Negation swaps positive/negative: ¬∃xφ positive = ∃xφ negative
3. Cross-disjunct binding: x introduced in ¬∃xφ is visible to ψ(x)

## Key results

- Modified FC: ◇(φ ∨ ψ) ⊨ ◇φ ∧ ◇(¬φ ∧ ψ)
- FC with anaphora: bathroom inference pattern
- Dual prohibition: ¬◇φ ∧ ¬◇ψ ⊨ ¬(φ ∨ ψ) (preserved)

The paper's general `disjPos1`/`disjPos2` (eq. 92) simplify for the
bathroom case (eqs. 93-94):
- `disjPos1` ⊆ `s[∃ₓB(x)]⁻` (eq. 93)
- `disjPos2` ⊆ `s[∃ₓB(x)]⁺[F(x)]⁺` (eq. 94)

Under these simplification conditions, the general FC preconditions
(both disjPos nonempty) yield the bathroom inference.
-/

namespace Phenomena.Modality.Studies.ElliottSudo2025

open Semantics.Dynamic.Core
open Semantics.Dynamic
open Classical

variable {W E : Type*}

-- ============================================================================
-- § 1. Modality concepts
-- ============================================================================

/-- Possibility: state s makes ◇φ true iff s[φ]⁺ is consistent.
Equivalent to checking `(BUSDen.diamond φ).positive s` is non-empty. -/
def possible (φ : BilateralDen W E) (s : InfoState W E) : Prop :=
  (φ.positive s).consistent

/-- Necessity: state s makes □φ true iff s subsists in s[φ]⁺. -/
def necessary (φ : BilateralDen W E) (s : InfoState W E) : Prop :=
  s ⪯ φ.positive s

/-- Impossibility: ¬◇φ iff s[φ]⁺ is empty. -/
def impossible (φ : BilateralDen W E) (s : InfoState W E) : Prop :=
  ¬(φ.positive s).consistent

theorem impossible_iff_empty (φ : BilateralDen W E) (s : InfoState W E) :
    impossible φ s ↔ φ.positive s = ∅ := by
  simp only [impossible, InfoState.consistent, Set.not_nonempty_iff_eq_empty]

/-- Diamond positive = s when φ is possible, ∅ otherwise. -/
theorem diamond_positive_eq (φ : BilateralDen W E) (s : InfoState W E) :
    (BUS.BUSDen.diamond φ).positive s =
    if possible φ s then s else ∅ := by
  simp only [possible, BUS.BUSDen.diamond]; rfl

-- ============================================================================
-- § 2. Modal disjunction (anaphora-sensitive, eq. 96)
-- ============================================================================

/-- Standard disjunction: the basic bilateral disjunction without FC
preconditions. -/
def disjStd (φ ψ : BilateralDen W E) : BilateralDen W E :=
  BilateralDen.disj φ ψ

/-- The part of the standard disjunction positive update that the first
disjunct is responsible for: the (1,*) row of the Strong Kleene truth table.

`s[φ ∨ ψ]₁⁺ = s[φ]⁺[ψ]⁺ ∪ s[φ]⁺[ψ]⁻ ∪ s[φ]⁺[ψ]?`

Every possibility in `s[φ]⁺` is verified by φ, and then classified by ψ
into one of three truth values. (eq. 92a) -/
def disjPos1 (φ ψ : BilateralDen W E) (s : InfoState W E) : InfoState W E :=
  ψ.positive (φ.positive s)
  ∪ ψ.negative (φ.positive s)
  ∪ ψ.unknownUpdate (φ.positive s)

/-- The part of the standard disjunction positive update that the second
disjunct is responsible for: the (*,1) column of the Strong Kleene truth
table.

`s[φ ∨ ψ]₂⁺ = s[φ]⁺[ψ]⁺ ∪ s[φ]⁻[ψ]⁺ ∪ s[φ]?[ψ]⁺`

The key term for cross-disjunct anaphora is `s[φ]⁻[ψ]⁺`: when
`φ = ¬∃x.P(x)`, `s[φ]⁻ = s[∃x.P(x)]⁺` by DNE, introducing the
discourse referent for binding across disjuncts. (eq. 92b) -/
def disjPos2 (φ ψ : BilateralDen W E) (s : InfoState W E) : InfoState W E :=
  ψ.positive (φ.positive s)
  ∪ ψ.positive (φ.negative s)
  ∪ ψ.positive (φ.unknownUpdate s)

/-- Modal Disjunction (anaphora-sensitive version): semantic disjunction
that validates FC with anaphora.

Modal disjunction adds a precondition to the positive update requiring
that each disjunct contribute at least some possibilities. This
semantically derives FC without pragmatic reasoning. (eq. 96) -/
def disjModal (φ ψ : BilateralDen W E) : BilateralDen W E :=
  { positive := λ s =>
      if (disjPos1 φ ψ s).Nonempty ∧ (disjPos2 φ ψ s).Nonempty then
        (disjStd φ ψ).positive s
      else ∅
  , negative := (disjStd φ ψ).negative }

notation:60 φ " ∨ᶠᶜ " ψ => disjModal φ ψ

-- ============================================================================
-- § 3. Structural properties of disjPos1 / disjPos2
-- ============================================================================

/-- The partition property guarantees `φ.positive s ⊆ disjPos1 φ ψ s`:
every possibility verified by φ ends up in disjPos1 (classified by ψ as
true, false, or unknown). -/
theorem subset_disjPos1 (φ ψ : BilateralDen W E) (s : InfoState W E) :
    φ.positive s ⊆ disjPos1 φ ψ s := by
  intro p hp
  unfold disjPos1
  exact BilateralDen.partition ψ (φ.positive s) hp

/-- Similarly, `ψ.positive (φ.negative s) ⊆ disjPos2 φ ψ s` via the middle
term. -/
theorem neg_subset_disjPos2 (φ ψ : BilateralDen W E) (s : InfoState W E) :
    ψ.positive (φ.negative s) ⊆ disjPos2 φ ψ s := by
  intro p hp
  exact Set.mem_union_left _ (Set.mem_union_right _ hp)

-- ============================================================================
-- § 4. FC theorems (general)
-- ============================================================================

/-- FC preconditions: if the modal disjunction is possible, both disjuncts
contribute possibilities. (eq. 96) -/
theorem fc_preconditions (φ ψ : BilateralDen W E) (s : InfoState W E)
    (h : possible (φ ∨ᶠᶜ ψ) s) :
    (disjPos1 φ ψ s).Nonempty ∧ (disjPos2 φ ψ s).Nonempty := by
  unfold possible InfoState.consistent at h
  unfold disjModal at h
  by_cases hcond : (disjPos1 φ ψ s).Nonempty ∧ (disjPos2 φ ψ s).Nonempty
  · exact hcond
  · simp only [hcond, ↓reduceIte] at h
    exact (Set.not_nonempty_empty h).elim

/-- Extract disjPos1 nonemptiness from FC possibility. -/
theorem fc_disjPos1_nonempty (φ ψ : BilateralDen W E) (s : InfoState W E)
    (h : possible (φ ∨ᶠᶜ ψ) s) :
    (disjPos1 φ ψ s).Nonempty :=
  (fc_preconditions φ ψ s h).1

/-- Extract disjPos2 nonemptiness from FC possibility. -/
theorem fc_disjPos2_nonempty (φ ψ : BilateralDen W E) (s : InfoState W E)
    (h : possible (φ ∨ᶠᶜ ψ) s) :
    (disjPos2 φ ψ s).Nonempty :=
  (fc_preconditions φ ψ s h).2

-- ============================================================================
-- § 5. Dual prohibition
-- ============================================================================

/-- Dual prohibition via disjPos1: if disjPos1 is empty (first disjunct
contributes nothing), modal disjunction is impossible. -/
theorem dual_prohibition_disjPos1 (φ ψ : BilateralDen W E) (s : InfoState W E)
    (h : ¬(disjPos1 φ ψ s).Nonempty) :
    impossible (φ ∨ᶠᶜ ψ) s := by
  intro hc
  have ⟨h1, _⟩ := fc_preconditions φ ψ s hc
  exact absurd h1 h

/-- Dual prohibition via disjPos2: if disjPos2 is empty (second disjunct
contributes nothing), modal disjunction is impossible. -/
theorem dual_prohibition_disjPos2 (φ ψ : BilateralDen W E) (s : InfoState W E)
    (h : ¬(disjPos2 φ ψ s).Nonempty) :
    impossible (φ ∨ᶠᶜ ψ) s := by
  intro hc
  have ⟨_, h2⟩ := fc_preconditions φ ψ s hc
  exact absurd h2 h

-- ============================================================================
-- § 6. Structural results (DNE, negation, binding)
-- ============================================================================

/-- In BUS, negation swaps positive and negative updates. -/
theorem negation_swaps_dims (φ : BilateralDen W E) (s : InfoState W E) :
    (BilateralDen.neg φ).positive s = φ.negative s ∧
    (BilateralDen.neg φ).negative s = φ.positive s := by
  simp only [BilateralDen.neg, and_self]

/-- Negated existential has existential in negative dimension. -/
theorem exists_in_neg_dimension (x : Nat) (dom : Set E)
    (φ : BilateralDen W E) (s : InfoState W E) :
    (BilateralDen.neg (BilateralDen.exists_ x dom φ)).negative s =
    (BilateralDen.exists_ x dom φ).positive s := by
  simp only [BilateralDen.neg]

/-- DNE preserves binding. -/
theorem dne_preserves_binding (x : Nat) (dom : Set E)
    (φ ψ : BilateralDen W E) (s : InfoState W E) :
    (BilateralDen.conj (BilateralDen.neg (BilateralDen.neg
        (BilateralDen.exists_ x dom φ))) ψ).positive s =
    (BilateralDen.conj (BilateralDen.exists_ x dom φ) ψ).positive s := by
  simp only [BilateralDen.neg_neg]

/-- Egli's theorem (positive): `(∃x.φ) ∧ ψ ⊆ ∃x(φ ∧ ψ)` for positive
updates. The positive direction holds because conjunction sequences
through the existential's positive update. -/
theorem egli_positive (x : Nat) (domain : Set E) (φ ψ : BilateralDen W E)
    (s : InfoState W E) :
    ((BilateralDen.exists_ x domain φ) ⊙ ψ).positive s ⊆
    (BilateralDen.exists_ x domain (φ ⊙ ψ)).positive s := by
  intro p hp
  exact hp

-- ============================================================================
-- § 7. Bathroom configuration
-- ============================================================================

/-- The bathroom disjunction configuration.

"Either there's no bathroom or it's in a funny place" -/
structure BathroomConfig (W E : Type*) where
  /-- The existential: ∃x.bathroom(x) -/
  bathroom : BilateralDen W E
  /-- The predicate on x: funny-place(x) -/
  funnyPlace : BilateralDen W E
  /-- The variable bound by the existential -/
  x : Nat

/-- The bathroom disjunction sentence: ¬∃x.bathroom(x) ∨ᶠᶜ funny-place(x) -/
def bathroomSentence (cfg : BathroomConfig W E) : BilateralDen W E :=
  (BilateralDen.neg cfg.bathroom) ∨ᶠᶜ cfg.funnyPlace

-- ============================================================================
-- § 8. FC with anaphora (bathroom-specific)
-- ============================================================================

/-- DNE as structural equality: ¬¬φ = φ. -/
theorem anaphora_via_dne (cfg : BathroomConfig W E) :
    BilateralDen.neg (BilateralDen.neg cfg.bathroom) = cfg.bathroom := by
  simp only [BilateralDen.neg_neg]

/-- FC with anaphora: the bathroom disjunction inference.

Eqs. 93-94 show that for bathroom disjunctions, the general
`disjPos1`/`disjPos2` (eq. 92) simplify so that:
- `disjPos1` reduces to `bath.negative s` (possible there's no bathroom)
- `disjPos2` reduces to `funnyPlace.positive (bath.positive s)` (possible
  there's a bathroom in a funny place)

The hypotheses `h_dp1` and `h_dp2` encode these simplifications: the
general forms are contained in the simplified forms, so nonemptiness
of the general forms transfers to the simplified forms.

These hold when `funnyPlace` is eliminative (output ⊆ input), as is the
case for atomic predicates (`pred1`). -/
theorem fc_with_anaphora (cfg : BathroomConfig W E) (s : InfoState W E)
    (h_poss : possible (bathroomSentence cfg) s)
    (h_dp1 : disjPos1 (BilateralDen.neg cfg.bathroom) cfg.funnyPlace s ⊆
             cfg.bathroom.negative s)
    (h_dp2 : disjPos2 (BilateralDen.neg cfg.bathroom) cfg.funnyPlace s ⊆
             cfg.funnyPlace.positive (cfg.bathroom.positive s)) :
    (cfg.bathroom.negative s).Nonempty ∧
    (cfg.funnyPlace.positive (cfg.bathroom.positive s)).Nonempty := by
  obtain ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩⟩ := fc_preconditions _ _ s h_poss
  exact ⟨⟨p1, h_dp1 hp1⟩, ⟨p2, h_dp2 hp2⟩⟩

-- ============================================================================
-- § 9. Concrete example
-- ============================================================================

inductive BathroomWorld where
  | noBathroom
  | bathroomNormal
  | bathroomFunny
  deriving DecidableEq, Repr

inductive BathroomEntity where
  | theBathroom
  deriving DecidableEq, Repr

def isBathroom : BathroomEntity → BathroomWorld → Prop
  | .theBathroom, .noBathroom => False
  | .theBathroom, _ => True

instance (e : BathroomEntity) (w : BathroomWorld) : Decidable (isBathroom e w) := by
  cases e <;> cases w <;> (unfold isBathroom; infer_instance)

def inFunnyPlace : BathroomEntity → BathroomWorld → Prop
  | .theBathroom, .bathroomFunny => True
  | _, _ => False

instance (e : BathroomEntity) (w : BathroomWorld) : Decidable (inFunnyPlace e w) := by
  cases e <;> cases w <;> (unfold inFunnyPlace; infer_instance)

def exampleBathroomConfig : BathroomConfig BathroomWorld BathroomEntity :=
  { bathroom := BilateralDen.exists_ 0 Set.univ (BilateralDen.pred1 isBathroom 0)
  , funnyPlace := BilateralDen.pred1 inFunnyPlace 0
  , x := 0 }

end Phenomena.Modality.Studies.ElliottSudo2025
