import Linglib.Semantics.Dynamic.UpdateSemantics.Bilateral
import Linglib.Semantics.Dynamic.DPL
import Linglib.Studies.GroenendijkStokhof1991
import Linglib.Data.Examples.ElliottSudo2025

/-!
# Elliott & Sudo (2025): Free Choice with Anaphora
[elliott-sudo-2025]

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

- Modified FC: ◇(φ ∨ ψ) ⊨ ◇φ ∧ ◇(¬φ ∧ ψ) (the paper's (95))
- FC with anaphora: bathroom inference pattern
- Dual prohibition: ¬◇φ ∧ ¬◇ψ ⊨ ¬(φ ∨ ψ) (preserved)

The paper's `disjPos1`/`disjPos2` (eq. 92) recover the standard positive
update as their union (`disjStd_positive_eq`, eq. 92c) and simplify for
the bathroom case (eqs. 93–94):
- `disjPos1` ⊆ `s[∃ₓB(x)]⁻` (eq. 93)
- `disjPos2` ⊆ `s[∃ₓB(x)]⁺[F(x)]⁺` (eq. 94)

Under these simplification conditions, the general FC preconditions
(both disjPos nonempty, eq. 96) yield the bathroom inference.
-/

namespace ElliottSudo2025

open DynamicSemantics
open Classical

variable {W E : Type*}

/-! ### Bilateral Update Semantics

BUS ([elliott-2023], [elliott-sudo-2025]): dynamic semantics with two update
dimensions (positive, negative) that validates DNE and handles cross-disjunct
anaphora. A `BUSDen` is a `BilateralDen` at register-form variables; the
operations here add presupposition (`hasGap`, `defined`), entailment
(`strawsonEntails`, `strongEntails`), and epistemic modality (`diamond`,
`box`, the paper's (73)/(77)). -/

/-- BUS denotation: a bilateral denotation over register-keyed possibilities. -/
abbrev BUSDen (W : Type*) (E : Type*) := BilateralDen W ℕ E

namespace BUSDen

variable {s : Set (Possibility W ℕ (Option E))}

/-- Truth-value gap: presupposition failure. -/
def hasGap (φ : BUSDen W E) (s : Set (Possibility W ℕ (Option E))) : Prop :=
  φ.positive s ∪ φ.negative s ⊂ s

/-- Sentence is defined (no presupposition failure). -/
def defined (φ : BUSDen W E) (s : Set (Possibility W ℕ (Option E))) : Prop :=
  φ.positive s ∪ φ.negative s = s

/-- Strong Kleene conjunction. -/
def skConj (φ ψ : BUSDen W E) : BUSDen W E := BilateralDen.conj φ ψ

/-- Presupposition-preserving conjunction. -/
def pConj (φ ψ : BUSDen W E) : BUSDen W E where
  positive s := ψ.positive (φ.positive s)
  negative s :=
    φ.negative s ∪ (s \ (φ.positive s ∪ φ.negative s)) ∪
      (φ.positive s ∩ ψ.negative (φ.positive s))

/-- Strawson entailment: φ entails ψ when φ is defined and true. -/
def strawsonEntails (φ ψ : BUSDen W E) : Prop :=
  ∀ s : Set (Possibility W ℕ (Option E)),
    defined φ s →
    (φ.positive s).Nonempty →
    (φ.positive s) ⊆ ψ.positive (φ.positive s)

/-- Strong entailment: φ entails ψ with no presupposition failure. -/
def strongEntails (φ ψ : BUSDen W E) : Prop :=
  ∀ s : Set (Possibility W ℕ (Option E)),
    (φ.positive s).Nonempty →
    defined ψ (φ.positive s) ∧
    (φ.positive s) ⊆ ψ.positive (φ.positive s)

theorem neg_positive_eq_negative (φ : BUSDen W E) :
    (BilateralDen.neg φ).positive s = φ.negative s := rfl

theorem neg_negative_eq_positive (φ : BUSDen W E) :
    (BilateralDen.neg φ).negative s = φ.positive s := rfl

theorem disj_negative (φ ψ : BUSDen W E) :
    (BilateralDen.disj φ ψ).negative s = ψ.negative (φ.negative s) := rfl

/--
Epistemic possibility ([elliott-sudo-2025], (73)): the positive update
returns `s` when the prejacent's positive update is consistent; the
negative update returns `s` when the denial is already implicit in `s`,
modulo introduced anaphoric information — state-level subsistence.
-/
def diamond (φ : BUSDen W E) : BUSDen W E where
  positive s := {_i ∈ s | (φ.positive s).Nonempty}
  negative s := {_i ∈ s | s ⪯ φ.negative s}

/--
Epistemic necessity ([elliott-sudo-2025], (77)): the dual, □φ = ¬◇¬φ.
-/
def box (φ : BUSDen W E) : BUSDen W E :=
  BilateralDen.neg (diamond (BilateralDen.neg φ))

@[inherit_doc diamond] prefix:max "◇ᵇ" => diamond
@[inherit_doc box] prefix:max "□ᵇ" => box

/-- The diamond's positive update as a conditional: `s` if the prejacent
is possible, absurd otherwise. -/
theorem diamond_positive_eq (φ : BUSDen W E) (s) :
    (◇ᵇφ).positive s = if (φ.positive s).Nonempty then s else ∅ := by
  by_cases h : (φ.positive s).Nonempty <;> simp [diamond, h]

/-- The diamond's negative update as a conditional. -/
theorem diamond_negative_eq (φ : BUSDen W E) (s) :
    (◇ᵇφ).negative s = if s ⪯ φ.negative s then s else ∅ := by
  by_cases h : s ⪯ φ.negative s <;> simp [diamond, h]

/-- Diamond positive is a test (returns s or ∅). -/
theorem diamond_positive_isTest (φ : BUSDen W E) :
    IsTest (◇ᵇφ).positive (S := Possibility W ℕ (Option E)) := by
  intro s
  rw [diamond_positive_eq]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Diamond negative is a test (returns s or ∅). -/
theorem diamond_negative_isTest (φ : BUSDen W E) :
    IsTest (◇ᵇφ).negative (S := Possibility W ℕ (Option E)) := by
  intro s
  rw [diamond_negative_eq]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Diamond positive is eliminative (from IsTest). -/
theorem diamond_positive_eliminative (φ : BUSDen W E) :
    IsEliminative (◇ᵇφ).positive (S := Possibility W ℕ (Option E)) :=
  test_eliminative _ (diamond_positive_isTest φ)

/-- Diamond positive subset (convenience form). -/
theorem diamond_positive_subset (φ : BUSDen W E) (s) :
    (◇ᵇφ).positive s ⊆ s :=
  diamond_positive_eliminative φ s

/-- Diamond negative is eliminative (from IsTest). -/
theorem diamond_negative_eliminative (φ : BUSDen W E) :
    IsEliminative (◇ᵇφ).negative (S := Possibility W ℕ (Option E)) :=
  test_eliminative _ (diamond_negative_isTest φ)

/-- Diamond negative subset (convenience form). -/
theorem diamond_negative_subset (φ : BUSDen W E) (s) :
    (◇ᵇφ).negative s ⊆ s :=
  diamond_negative_eliminative φ s

/-- Box positive is eliminative (□φ = ¬◇¬φ, so positive = diamond negative of ¬φ). -/
theorem box_positive_eliminative (φ : BUSDen W E) :
    IsEliminative (□ᵇφ).positive (S := Possibility W ℕ (Option E)) :=
  diamond_negative_eliminative (BilateralDen.neg φ)

/-- Box negative is eliminative. -/
theorem box_negative_eliminative (φ : BUSDen W E) :
    IsEliminative (□ᵇφ).negative (S := Possibility W ℕ (Option E)) :=
  diamond_positive_eliminative (BilateralDen.neg φ)

end BUSDen

/-! ### Modality concepts -/

variable {s : Set (Possibility W ℕ (Option E))}

/-- Possibility: state s makes ◇φ true iff s[φ]⁺ is consistent. -/
def possible (φ : BUSDen W E) (s : Set (Possibility W ℕ (Option E))) : Prop :=
  (φ.positive s).Nonempty

/-- Necessity: state s makes □φ true iff s subsists in s[φ]⁺. -/
def necessary (φ : BUSDen W E) (s : Set (Possibility W ℕ (Option E))) : Prop :=
  s ⪯ φ.positive s

/-- Impossibility: ¬◇φ iff s[φ]⁺ is empty. -/
def impossible (φ : BUSDen W E) (s : Set (Possibility W ℕ (Option E))) : Prop :=
  ¬(φ.positive s).Nonempty

theorem impossible_iff_empty (φ : BUSDen W E) :
    impossible φ s ↔ φ.positive s = ∅ := by
  simp only [impossible, Set.not_nonempty_iff_eq_empty]

/-! ### Modal disjunction (anaphora-sensitive) -/

/-- Standard disjunction: the basic bilateral disjunction without FC
preconditions. -/
def disjStd (φ ψ : BUSDen W E) : BUSDen W E :=
  BilateralDen.disj φ ψ

/-- The part of the standard disjunction positive update that the first
disjunct is responsible for: the (1,*) row of the Strong Kleene truth table.

`s[φ ∨ ψ]₁⁺ = s[φ]⁺[ψ]⁺ ∪ s[φ]⁺[ψ]⁻ ∪ s[φ]⁺[ψ]?`

Every possibility in `s[φ]⁺` is verified by φ, and then classified by ψ
into one of three truth values. (eq. 92a) -/
def disjPos1 (φ ψ : BUSDen W E) (s : Set (Possibility W ℕ (Option E))) :
    Set (Possibility W ℕ (Option E)) :=
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
def disjPos2 (φ ψ : BUSDen W E) (s : Set (Possibility W ℕ (Option E))) :
    Set (Possibility W ℕ (Option E)) :=
  ψ.positive (φ.positive s)
  ∪ ψ.positive (φ.negative s)
  ∪ ψ.positive (φ.unknownUpdate s)

/-- (92c): the standard positive update is the union of the parts the two
disjuncts are responsible for. -/
theorem disjStd_positive_eq (φ ψ : BUSDen W E) (s) :
    (disjStd φ ψ).positive s = disjPos1 φ ψ s ∪ disjPos2 φ ψ s := by
  ext p
  simp only [disjStd, BilateralDen.disj, disjPos1, disjPos2, Set.mem_union]
  tauto

/-- Modal Disjunction (anaphora-sensitive version, eq. 96): semantic
disjunction that validates FC with anaphora, adding the precondition that
each disjunct contribute at least some possibilities. This semantically
derives FC without pragmatic reasoning. -/
def disjModal (φ ψ : BUSDen W E) : BUSDen W E where
  positive s :=
    if (disjPos1 φ ψ s).Nonempty ∧ (disjPos2 φ ψ s).Nonempty then
      (disjStd φ ψ).positive s
    else ∅
  negative := (disjStd φ ψ).negative

@[inherit_doc] notation:60 φ " ∨ᶠᶜ " ψ => disjModal φ ψ

/-- `ψ.positive (φ.negative s) ⊆ disjPos2 φ ψ s` via the middle term. -/
theorem neg_subset_disjPos2 (φ ψ : BUSDen W E) (s) :
    ψ.positive (φ.negative s) ⊆ disjPos2 φ ψ s := fun _ hp =>
  Set.mem_union_left _ (Set.mem_union_right _ hp)

/-! ### Free choice theorems (general) -/

/-- FC preconditions: if the modal disjunction is possible, both disjuncts
contribute possibilities. (eq. 96) -/
theorem fc_preconditions (φ ψ : BUSDen W E)
    (h : possible (φ ∨ᶠᶜ ψ) s) :
    (disjPos1 φ ψ s).Nonempty ∧ (disjPos2 φ ψ s).Nonempty := by
  unfold possible disjModal at h
  by_cases hcond : (disjPos1 φ ψ s).Nonempty ∧ (disjPos2 φ ψ s).Nonempty
  · exact hcond
  · simp only [hcond, ↓reduceIte] at h
    exact (Set.not_nonempty_empty h).elim

/-- Extract disjPos1 nonemptiness from FC possibility. -/
theorem fc_disjPos1_nonempty (φ ψ : BUSDen W E)
    (h : possible (φ ∨ᶠᶜ ψ) s) :
    (disjPos1 φ ψ s).Nonempty :=
  (fc_preconditions φ ψ h).1

/-- Extract disjPos2 nonemptiness from FC possibility. -/
theorem fc_disjPos2_nonempty (φ ψ : BUSDen W E)
    (h : possible (φ ∨ᶠᶜ ψ) s) :
    (disjPos2 φ ψ s).Nonempty :=
  (fc_preconditions φ ψ h).2

/-! ### Dual prohibition -/

/-- Dual prohibition via disjPos1: if disjPos1 is empty (first disjunct
contributes nothing), modal disjunction is impossible. -/
theorem dual_prohibition_disjPos1 (φ ψ : BUSDen W E)
    (h : ¬(disjPos1 φ ψ s).Nonempty) :
    impossible (φ ∨ᶠᶜ ψ) s := fun hc =>
  absurd (fc_preconditions φ ψ hc).1 h

/-- Dual prohibition via disjPos2: if disjPos2 is empty (second disjunct
contributes nothing), modal disjunction is impossible. -/
theorem dual_prohibition_disjPos2 (φ ψ : BUSDen W E)
    (h : ¬(disjPos2 φ ψ s).Nonempty) :
    impossible (φ ∨ᶠᶜ ψ) s := fun hc =>
  absurd (fc_preconditions φ ψ hc).2 h

/-! ### Structural results (DNE, negation, binding) -/

/-- In BUS, negation swaps positive and negative updates. -/
theorem negation_swaps_dims (φ : BUSDen W E) :
    (BilateralDen.neg φ).positive s = φ.negative s ∧
    (BilateralDen.neg φ).negative s = φ.positive s :=
  ⟨rfl, rfl⟩

/-- Negated existential has existential in negative dimension. -/
theorem exists_in_neg_dimension (x : Nat) (φ : BUSDen W E) :
    (BilateralDen.neg (BilateralDen.exists_ x φ)).negative s =
    (BilateralDen.exists_ x φ).positive s := rfl

/-- DNE preserves binding. -/
theorem dne_preserves_binding (x : Nat) (φ ψ : BUSDen W E) :
    (BilateralDen.conj (BilateralDen.neg (BilateralDen.neg
        (BilateralDen.exists_ x φ))) ψ).positive s =
    (BilateralDen.conj (BilateralDen.exists_ x φ) ψ).positive s := rfl

/-- Divergence from DPL on doubly negated indefinites. The discourse
`Examples.double_negation` ("It's not the case that John didn't see a
bird. It was singing.") is judged acceptable; BUS derives the binding
because `¬¬φ = φ` (`dne_preserves_binding`), whereas in DPL negation is
a test, so `¬¬∃xφ ≠ ∃xφ` and the discourse referent never escapes. -/
theorem dpl_diverges_on_double_negation [Nontrivial E] :
    Examples.double_negation.judgment = .acceptable ∧
    ∃ (x : Nat) (φ : DPL.DPLRel E),
      DPL.DPLRel.neg (.neg (.exists_ x φ)) ≠ .exists_ x φ :=
  ⟨rfl, GroenendijkStokhof1991.dne_fails_anaphora⟩

/-! ### Bathroom configuration -/

/-- The bathroom disjunction configuration.

"Either there's no bathroom or it's in a funny place" -/
structure BathroomConfig (W E : Type*) where
  /-- The existential: ∃x.bathroom(x) -/
  bathroom : BUSDen W E
  /-- The predicate on x: funny-place(x) -/
  funnyPlace : BUSDen W E
  /-- The variable bound by the existential -/
  x : Nat

/-- The bathroom disjunction sentence: ¬∃x.bathroom(x) ∨ᶠᶜ funny-place(x) -/
def bathroomSentence (cfg : BathroomConfig W E) : BUSDen W E :=
  (BilateralDen.neg cfg.bathroom) ∨ᶠᶜ cfg.funnyPlace

/-! ### Free choice with anaphora (bathroom-specific) -/

/-- DNE as structural equality: ¬¬φ = φ. -/
theorem anaphora_via_dne (cfg : BathroomConfig W E) :
    BilateralDen.neg (BilateralDen.neg cfg.bathroom) = cfg.bathroom :=
  BilateralDen.neg_neg cfg.bathroom

/-- FC with anaphora: the bathroom disjunction inference.

Eqs. 93-94 show that for bathroom disjunctions, the general
`disjPos1`/`disjPos2` (eq. 92) simplify so that:
- `disjPos1` reduces to `bath.negative s` (possible there's no bathroom)
- `disjPos2` reduces to `funnyPlace.positive (bath.positive s)` (possible
  there's a bathroom in a funny place)

The hypotheses `h_dp1` and `h_dp2` encode these simplifications: the
general forms are contained in the simplified forms, so nonemptiness
of the general forms transfers to the simplified forms. -/
theorem fc_with_anaphora (cfg : BathroomConfig W E)
    (s : Set (Possibility W ℕ (Option E)))
    (h_poss : possible (bathroomSentence cfg) s)
    (h_dp1 : disjPos1 (BilateralDen.neg cfg.bathroom) cfg.funnyPlace s ⊆
             cfg.bathroom.negative s)
    (h_dp2 : disjPos2 (BilateralDen.neg cfg.bathroom) cfg.funnyPlace s ⊆
             cfg.funnyPlace.positive (cfg.bathroom.positive s)) :
    (cfg.bathroom.negative s).Nonempty ∧
    (cfg.funnyPlace.positive (cfg.bathroom.positive s)).Nonempty := by
  obtain ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩⟩ := fc_preconditions _ _ h_poss
  exact ⟨⟨p1, h_dp1 hp1⟩, ⟨p2, h_dp2 hp2⟩⟩

/-! ### The paper's partial-familiarity state (56)

[elliott-sudo-2025]'s (56): a state where `x` is defined at four
possibilities and undefined at `(w∅, [])`, so `x` is only *partially*
familiar. The atomic sentence `P(x)` gaps at exactly the undefined
possibility, so assertability (54) fails — the situation a uniform-base
state cannot represent. -/

section PartialFamiliarity

inductive PWorld where
  | wa | wb | w0
  deriving DecidableEq

inductive PEntity where
  | a | b
  deriving DecidableEq

/-- `a` is `P` at `wa`, `b` is `P` at `wb`, nothing is `P` at `w0`. -/
def pHolds : PEntity → PWorld → Prop
  | .a, .wa => True
  | .b, .wb => True
  | _, _ => False

/-- The paper's `[x → e]`: register 0 defined, all else `∗`. -/
def xTo (e : PEntity) : ℕ → Option PEntity :=
  fun n => if n = 0 then some e else none

/-- The paper's `[]`: everything `∗`. -/
def blank : ℕ → Option PEntity := fun _ => none

open PWorld in
/-- The state of (56). -/
def s56 : Set (Possibility PWorld ℕ (Option PEntity)) :=
  {⟨wa, xTo .a⟩, ⟨wa, xTo .b⟩, ⟨wb, xTo .a⟩, ⟨wb, xTo .b⟩, ⟨w0, blank⟩}

/-- Positive consistency: `(wa, [x → a])` survives assertion (56a). -/
theorem mem_positive_s56 :
    (⟨.wa, xTo .a⟩ : Possibility PWorld ℕ (Option PEntity)) ∈
      (BilateralDen.pred1 pHolds 0).positive s56 :=
  ⟨by simp [s56], .a, rfl, trivial⟩

/-- The gap: `(w∅, [])` subsists in neither dimension, so it is in the
unknown update (56c). -/
theorem gap_mem_unknownUpdate_s56 :
    (⟨.w0, blank⟩ : Possibility PWorld ℕ (Option PEntity)) ∈
      (BilateralDen.pred1 pHolds 0).unknownUpdate s56 := by
  refine ⟨by simp [s56], ?_, ?_⟩ <;>
  · rintro ⟨q, ⟨hq, e, he, -⟩, hw, -⟩
    rcases (by simpa [s56] using hq : q = _ ∨ q = _ ∨ q = _ ∨ q = _ ∨ q = _)
      with rfl | rfl | rfl | rfl | rfl <;> simp_all [blank]

/-- (56)'s upshot: `P(x)` is not assertable at the partially familiar
state. -/
theorem not_assertable_s56 :
    ¬(BilateralDen.pred1 pHolds 0).assertable s56 := fun h =>
  Set.notMem_empty _ (h ▸ gap_mem_unknownUpdate_s56)

/-- `x` is not familiar at (56)'s state — familiarity fails, and by
`not_assertable_s56` so does assertability; the paper's point is that the
converse can fail (assertability is strictly weaker). -/
theorem not_familiar_s56 : ¬Familiar s56 0 := fun h =>
  h ⟨.w0, blank⟩ (by simp [s56]) rfl

end PartialFamiliarity

/-! ### Concrete example -/

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

def inFunnyPlace : BathroomEntity → BathroomWorld → Prop
  | .theBathroom, .bathroomFunny => True
  | _, _ => False

def exampleBathroomConfig : BathroomConfig BathroomWorld BathroomEntity :=
  { bathroom := BilateralDen.exists_ 0 (BilateralDen.pred1 isBathroom 0)
  , funnyPlace := BilateralDen.pred1 inFunnyPlace 0
  , x := 0 }

end ElliottSudo2025
