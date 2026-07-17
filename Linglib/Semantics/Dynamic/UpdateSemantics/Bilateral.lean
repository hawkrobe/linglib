import Linglib.Semantics.Dynamic.State
import Linglib.Semantics.Dynamic.Update
import Linglib.Core.Logic.Bilateral.Defs
import Mathlib.Algebra.Group.Defs

/-!
# Bilateral Update Semantics
[elliott-sudo-2025], [krahmer-muskens-1995]

Bilateral Update Semantics (BUS, [elliott-sudo-2025]'s formulation, with
[krahmer-muskens-1995]'s bilateral DRT as ancestor): update semantics
where each sentence carries a positive and a negative update dimension,
validating Double Negation Elimination (negation swaps the dimensions)
and cross-disjunct anaphora.

States are Heimian (the paper's Def. 3.1): sets of world-assignment
pairs whose assignments are `Part E`-valued — `⊥` is the paper's `∗`,
so definedness is per-possibility and non-uniform.
This is strictly more expressive than the indexed `State` of `State.lean`:
a uniform base cannot represent partially familiar states, on which the
paper's separation of assertability (54) from Heimian familiarity rests.

## Main definitions

- subsistence (Def. 3.3, after [groenendijk-stokhof-veltman-1996]),
  rendered as the lower closure: membership for points, `≤` of
  closures for states.
- `Familiar`: familiarity (Def. 3.2) — defined at every possibility,
  values free; worldly information (Def. 3.1's 𝒲) is the image
  `Possibility.world '' s`.
- `randomAssign`: the paper's `s[εₓ]` (43); novelty is not encoded.
- `BilateralDen` with `atom`, `pred1`, `pred2`, `neg` (`~`), `conj`
  (`⊙`, (61)), `disj` (`⊕`, (64)), `exists_` ((44)–(45)), `forall_`.
- `unknownUpdate` (`s[φ]?`, (53)) and `assertable` ((54)).
- `supports`, `entails` (`⊨ᵇ`): subsistence-based support.

## Main results

- `neg_neg`: DNE is definitional.
- `partition`, `partition_assertable`: every possibility subsists
  positively, subsists negatively, or is unknown.
- `de_morgan_disj`, `de_morgan_conj`: de Morgan's laws, unlike in
  standard dynamic semantics. (Descendance, subsistence, `Familiar`,
  and random assignment now live at the root, in `State.lean` — this
  file's vocabulary became the module's.)
- `egli`: Egli's theorem for the positive dimension, definitionally.
- `isBilateral`: the update algebra is a bilateral logic in the sense of
  `Core.Logic.Bilateral`.

## Implementation notes

Descent requires the larger point to *extend* the assignment, per
[groenendijk-stokhof-veltman-1996]; [elliott-sudo-2025]'s Def. 3.3
phrases the clause as domain inclusion, and their examples do not
discriminate. The paper overloads `≺` for possibility-in-state and
state-in-state subsistence (their fn. on (73)); here both are the
lower closure — membership for points, `≤` of closures for states.

The empirical comparison against full ICDRT is in
`Studies/Hofmann2025.lean`; against PLA in `Studies/Dekker2012.lean`.
-/

namespace DynamicSemantics

variable {W V E : Type*}

/-! ### Bilateral denotations -/

/-- A bilateral denotation: a positive dimension `s[φ]⁺` (what survives
assertion) and a negative dimension `s[φ]⁻` (what survives denial).
Standard dynamic semantics has only the former; the latter is what makes
DNE and cross-disjunct anaphora work. -/
@[ext] structure BilateralDen (W V E : Type*) where
  /-- Positive update: the result of asserting the sentence. -/
  positive : Set (Possibility W V (Part E)) → Set (Possibility W V (Part E))
  /-- Negative update: the result of denying the sentence. -/
  negative : Set (Possibility W V (Part E)) → Set (Possibility W V (Part E))

namespace BilateralDen

variable {φ ψ : BilateralDen W V E} {s : Set (Possibility W V (Part E))}
  {p : Possibility W V (Part E)}

/-- Worldly atom: keep the possibilities where the proposition holds
(positively) or fails (negatively). -/
def atom (pred : W → Prop) : BilateralDen W V E where
  positive s := {p ∈ s | pred p.world}
  negative s := {p ∈ s | ¬ pred p.world}

/-- Unary atomic predication at `t`. Atoms are *partial*: a possibility
where `t` is undefined survives in neither dimension
([elliott-sudo-2025]'s definedness clause for atomic sentences). -/
def pred1 (P : E → W → Prop) (t : V) : BilateralDen W V E where
  positive s := {p ∈ s | ∃ e ∈ p.assignment t, P e p.world}
  negative s := {p ∈ s | ∃ e ∈ p.assignment t, ¬ P e p.world}

/-- Binary atomic predication at `t₁`, `t₂`; partial like `pred1`. -/
def pred2 (P : E → E → W → Prop) (t₁ t₂ : V) : BilateralDen W V E where
  positive s := {p ∈ s | ∃ e₁ ∈ p.assignment t₁,
    ∃ e₂ ∈ p.assignment t₂, P e₁ e₂ p.world}
  negative s := {p ∈ s | ∃ e₁ ∈ p.assignment t₁,
    ∃ e₂ ∈ p.assignment t₂, ¬ P e₁ e₂ p.world}

/-- Negation swaps the dimensions: `s[¬φ]⁺ = s[φ]⁻` and `s[¬φ]⁻ = s[φ]⁺`.
Negation does not "push in" — this is the key insight of bilateralism. -/
def neg (φ : BilateralDen W V E) : BilateralDen W V E where
  positive := φ.negative
  negative := φ.positive

@[inherit_doc] prefix:max "~" => neg

/-- Double negation is the identity, definitionally. -/
@[simp] theorem neg_neg (φ : BilateralDen W V E) : ~~φ = φ := rfl

theorem dne_positive (φ : BilateralDen W V E) (s) :
    (~~φ).positive s = φ.positive s := rfl

theorem dne_negative (φ : BilateralDen W V E) (s) :
    (~~φ).negative s = φ.negative s := rfl

theorem neg_involutive :
    Function.Involutive (neg : BilateralDen W V E → BilateralDen W V E) :=
  neg_neg

/-! ### The unknown update and assertability -/

/-- The *unknown* update `s[φ]?` ([elliott-sudo-2025], (53)): the
possibilities of `s` that subsist in neither dimension — the dynamic
analogue of the third Strong Kleene truth value. -/
def unknownUpdate (φ : BilateralDen W V E)
    (s : Set (Possibility W V (Part E))) : Set (Possibility W V (Part E)) :=
  {p ∈ s | p ∉ lowerClosure (φ.positive s) ∧ p ∉ lowerClosure (φ.negative s)}

/-- Assertability ([elliott-sudo-2025], (54)): the unknown update is
empty — every possibility is accounted for by one of the dimensions.
Strictly weaker than Heimian familiarity. -/
def assertable (φ : BilateralDen W V E)
    (c : Set (Possibility W V (Part E))) : Prop :=
  φ.unknownUpdate c = ∅

/-- The unknown update is invariant under negation. -/
theorem unknownUpdate_neg (φ : BilateralDen W V E) (s) :
    (~φ).unknownUpdate s = φ.unknownUpdate s := by
  ext p
  simp only [unknownUpdate, neg, Set.mem_setOf_eq,
    and_comm (a := p ∉ lowerClosure (φ.negative s))]

/-- Worldly atoms never gap. -/
theorem unknownUpdate_atom (pred : W → Prop) (s) :
    (atom pred (V := V) (E := E)).unknownUpdate s = ∅ := by
  ext p
  simp only [unknownUpdate, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false, not_and]
  intro hp hpos hneg
  by_cases h : pred p.world
  · exact hpos (subset_lowerClosure ⟨hp, h⟩)
  · exact hneg (subset_lowerClosure ⟨hp, h⟩)

/-- Every possibility subsists positively, subsists negatively, or is
unknown. -/
theorem partition (φ : BilateralDen W V E) (hp : p ∈ s) :
    p ∈ lowerClosure (φ.positive s) ∨ p ∈ lowerClosure (φ.negative s) ∨ p ∈ φ.unknownUpdate s := by
  by_cases h1 : p ∈ lowerClosure (φ.positive s)
  · exact Or.inl h1
  · by_cases h2 : p ∈ lowerClosure (φ.negative s)
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨hp, h1, h2⟩)

/-- Under assertability, every possibility subsists in one of the
dimensions. -/
theorem partition_assertable (h : φ.assertable s) (hp : p ∈ s) :
    p ∈ lowerClosure (φ.positive s) ∨ p ∈ lowerClosure (φ.negative s) := by
  rcases partition φ hp with h1 | h2 | h3
  · exact Or.inl h1
  · exact Or.inr h2
  · rw [assertable] at h
    exact absurd (h ▸ h3) (Set.notMem_empty p)

/-! ### Connectives -/

/-- Conjunction ([elliott-sudo-2025], (61)): the positive update
sequences the positive dimensions (the one verifying Strong Kleene cell);
the negative update is the union of the dynamic falsifications, one per
falsifying cell. -/
def conj (φ ψ : BilateralDen W V E) : BilateralDen W V E where
  positive s := ψ.positive (φ.positive s)
  negative s :=
    ψ.positive (φ.negative s) ∪ ψ.negative (φ.negative s)
      ∪ ψ.unknownUpdate (φ.negative s) ∪ ψ.negative (φ.positive s)
      ∪ ψ.negative (φ.unknownUpdate s)

@[inherit_doc] infixl:65 " ⊙ " => conj

/-- Disjunction ([elliott-sudo-2025], (64)): verification via the first
disjunct (the `s[φ]⁺` row) or via the second (the `[ψ]⁺` column); denial
is sequential. The state-passing `ψ.positive (φ.negative s)` term is what
makes bathroom disjunctions work: by DNE, `s[¬∃xP(x)]⁻ = s[∃xP(x)]⁺`
introduces the referent for the second disjunct. -/
def disj (φ ψ : BilateralDen W V E) : BilateralDen W V E where
  positive s :=
    ψ.positive (φ.positive s) ∪ ψ.negative (φ.positive s)
      ∪ ψ.unknownUpdate (φ.positive s) ∪ ψ.positive (φ.negative s)
      ∪ ψ.positive (φ.unknownUpdate s)
  negative s := ψ.negative (φ.negative s)

@[inherit_doc] infixl:60 " ⊕ " => disj

/-- Conjunction associates in the positive dimension. -/
theorem conj_assoc_positive (φ ψ χ : BilateralDen W V E) (s) :
    ((φ ⊙ ψ) ⊙ χ).positive s = (φ ⊙ (ψ ⊙ χ)).positive s := rfl

/-- De Morgan: `¬(φ ∨ ψ)` and `¬φ ∧ ¬ψ` agree positively, definitionally. -/
theorem de_morgan_disj (φ ψ : BilateralDen W V E) (s) :
    (~(φ ⊕ ψ)).positive s = ((~φ) ⊙ (~ψ)).positive s := rfl

/-- De Morgan: `¬(φ ∧ ψ)` and `¬φ ∨ ¬ψ` agree positively. -/
theorem de_morgan_conj (φ ψ : BilateralDen W V E) (s) :
    (~(φ ⊙ ψ)).positive s = ((~φ) ⊕ (~ψ)).positive s := by
  have h := unknownUpdate_neg φ s
  have h' := unknownUpdate_neg ψ (φ.negative s)
  show ψ.positive (φ.negative s) ∪ ψ.negative (φ.negative s)
      ∪ ψ.unknownUpdate (φ.negative s) ∪ ψ.negative (φ.positive s)
      ∪ ψ.negative (φ.unknownUpdate s)
    = ψ.negative (φ.negative s) ∪ ψ.positive (φ.negative s)
      ∪ (~ψ).unknownUpdate (φ.negative s) ∪ ψ.negative (φ.positive s)
      ∪ ψ.negative ((~φ).unknownUpdate s)
  rw [h, h',
    Set.union_comm (ψ.negative (φ.negative s)) (ψ.positive (φ.negative s))]

/-! ### Quantifiers -/

section Quantifiers
variable [DecidableEq V]

/-- Existential quantification ([elliott-sudo-2025], (44)–(45)): the
positive update introduces the referent by random assignment and asserts
the scope; the negative update merely removes possibilities — it retains
those of `s` whose world falsifies the existential classically, and
introduces no anaphoric information. -/
def exists_ (x : V) (φ : BilateralDen W V E) : BilateralDen W V E where
  positive s := φ.positive (State.randomAssign s x)
  negative s :=
    {p ∈ s | p.world ∉ Possibility.world '' φ.positive (State.randomAssign s x) ∧
      p.world ∈ Possibility.world '' φ.negative (State.randomAssign s x)}

/-- Universal quantification, by de Morgan duality: `∀x φ = ¬∃x ¬φ`. -/
def forall_ (x : V) (φ : BilateralDen W V E) : BilateralDen W V E :=
  ~(exists_ x (~φ))

/-- Egli's theorem, definitionally: an existential scoping over a
conjunction binds into the second conjunct, `(∃x φ) ∧ ψ = ∃x (φ ∧ ψ)` in
the positive dimension — the key property for cross-sentential anaphora. -/
theorem egli (x : V) (φ ψ : BilateralDen W V E) (s) :
    ((exists_ x φ) ⊙ ψ).positive s = (exists_ x (φ ⊙ ψ)).positive s := rfl

end Quantifiers

/-! ### Support and entailment -/

/-- Bilateral support: the positive update is consistent and the state
subsists in it. -/
def supports (s : Set (Possibility W V (Part E)))
    (φ : BilateralDen W V E) : Prop :=
  (φ.positive s).Nonempty ∧ lowerClosure s ≤ lowerClosure (φ.positive s)

/-- Bilateral entailment: every consistent positive update of `φ`
supports `ψ`. -/
def entails (φ ψ : BilateralDen W V E) : Prop :=
  ∀ s : Set (Possibility W V (Part E)),
    (φ.positive s).Nonempty → supports (φ.positive s) ψ

@[inherit_doc] notation:50 φ " ⊨ᵇ " ψ => entails φ ψ

/-! ### Structural lemmas -/

theorem atom_complementary (pred : W → Prop) (s : Set (Possibility W V (Part E))) :
    (atom pred (E := E)).positive s ∪ (atom pred).negative s = s := by
  ext p
  simp only [atom, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro h
    by_cases hp : pred p.world
    · exact Or.inl ⟨h, hp⟩
    · exact Or.inr ⟨h, hp⟩

theorem atom_disjoint (pred : W → Prop) (s : Set (Possibility W V (Part E))) :
    (atom pred (E := E)).positive s ∩ (atom pred).negative s = ∅ := by
  ext p
  exact ⟨fun ⟨⟨_, hp⟩, ⟨_, hnp⟩⟩ => absurd hp hnp, False.elim⟩

theorem atom_positive_monotone (pred : W → Prop) :
    Monotone (atom pred (V := V) (E := E)).positive :=
  sep_monotone _

theorem atom_negative_monotone (pred : W → Prop) :
    Monotone (atom pred (V := V) (E := E)).negative :=
  sep_monotone _

theorem atom_positive_eliminative (pred : W → Prop) :
    CCP.IsEliminative (atom pred (V := V) (E := E)).positive :=
  sep_eliminative _

theorem atom_negative_eliminative (pred : W → Prop) :
    CCP.IsEliminative (atom pred (V := V) (E := E)).negative :=
  sep_eliminative _

theorem pred1_positive_monotone (P : E → W → Prop) (t : V) :
    Monotone (pred1 P t (W := W)).positive :=
  sep_monotone _

theorem pred1_negative_monotone (P : E → W → Prop) (t : V) :
    Monotone (pred1 P t (W := W)).negative :=
  sep_monotone _

theorem pred1_positive_eliminative (P : E → W → Prop) (t : V) :
    CCP.IsEliminative (pred1 P t (W := W)).positive :=
  sep_eliminative _

theorem pred1_negative_eliminative (P : E → W → Prop) (t : V) :
    CCP.IsEliminative (pred1 P t (W := W)).negative :=
  sep_eliminative _

theorem pred2_positive_eliminative (P : E → E → W → Prop) (t₁ t₂ : V) :
    CCP.IsEliminative (pred2 P t₁ t₂ (W := W)).positive :=
  sep_eliminative _

theorem pred2_negative_eliminative (P : E → E → W → Prop) (t₁ t₂ : V) :
    CCP.IsEliminative (pred2 P t₁ t₂ (W := W)).negative :=
  sep_eliminative _

/-! ### The bilateral algebra -/

/-- View a bilateral denotation as a pair of updates. -/
def toPair (φ : BilateralDen W V E) :=
  (φ.positive, φ.negative)

/-- Construct a bilateral denotation from a pair of updates. -/
def ofPair (u : (Set (Possibility W V (Part E)) → Set (Possibility W V (Part E))) ×
    (Set (Possibility W V (Part E)) → Set (Possibility W V (Part E)))) :
    BilateralDen W V E where
  positive := u.1
  negative := u.2

theorem toPair_ofPair (u) : toPair (ofPair (W := W) (V := V) (E := E) u) = u := rfl

theorem ofPair_toPair (φ : BilateralDen W V E) : ofPair (toPair φ) = φ := rfl

/-- Negation is the swap on pairs; DNE is `swap ∘ swap = id`. -/
theorem neg_eq_swap (φ : BilateralDen W V E) :
    toPair (~φ) = Prod.swap (toPair φ) := rfl

instance : InvolutiveNeg (BilateralDen W V E) where
  neg := neg
  neg_neg := neg_neg

/-- BUS is a paraconsistent bilateral logic (`Core.Logic.Bilateral`): the
denotation is the formula, the dimensions are the projections, and `neg`
swaps them by definition. -/
theorem isBilateral :
    Core.Logic.Bilateral.IsBilateral
      (Form := BilateralDen W V E)
      (Result := Set (Possibility W V (Part E)) → Set (Possibility W V (Part E)))
      (·.positive) (·.negative) neg where
  positive_negate _ := rfl
  negative_negate _ := rfl

/-- The pointwise order: both dimensions componentwise. -/
instance : PartialOrder (BilateralDen W V E) where
  le φ ψ := (∀ s, φ.positive s ≤ ψ.positive s) ∧ (∀ s, φ.negative s ≤ ψ.negative s)
  le_refl _ := ⟨fun _ => le_refl _, fun _ => le_refl _⟩
  le_trans _ _ _ h1 h2 :=
    ⟨fun s => le_trans (h1.1 s) (h2.1 s), fun s => le_trans (h1.2 s) (h2.2 s)⟩
  le_antisymm _ _ h1 h2 := BilateralDen.ext
    (funext fun s => le_antisymm (h1.1 s) (h2.1 s))
    (funext fun s => le_antisymm (h1.2 s) (h2.2 s))

/-- Negation is monotone: the swap rearranges the componentwise checks. -/
theorem neg_monotone : Monotone (neg : BilateralDen W V E → BilateralDen W V E) :=
  fun _ _ ⟨hp, hn⟩ => ⟨hn, hp⟩

/-- Negation preserves and reflects the order. -/
theorem neg_le_neg_iff : ~φ ≤ ~ψ ↔ φ ≤ ψ :=
  ⟨fun ⟨hp, hn⟩ => ⟨hn, hp⟩, fun ⟨hp, hn⟩ => ⟨hn, hp⟩⟩

end BilateralDen

end DynamicSemantics
