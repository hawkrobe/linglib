import Mathlib.Tactic.DeriveFintype
import Linglib.Core.Logic.Aristotelian.Basic

/-!
# Antonymy — Contradictory vs Contrary Distinction

[cruse-1986] [horn-1989] [kennedy-2007]

The classical lexical-semantic distinction between two kinds of opposite
pairs:

**Contradictories** (e.g., *clean* / *dirty*) — cannot both be true and
cannot both be false. Negation of one entails the other:
*not clean* ⟹ *dirty*. No extension gap between the two standards.

**Contraries** (e.g., *tall* / *short*, *large* / *small*) — cannot both
be true but can both be false. Negation of one does NOT entail the other:
*not large* ⊭ *small*. Extension gap between the two standards.

Note: The type is named `NegationType` for backward compatibility with
existing call sites; the linguistically accurate name is *antonymy
type*. The file is named `Antonymy.lean` to signal the right concept.
-/

namespace Features

/-- Antonymy type: contradictory (no gap) vs contrary (gap).

    See `Antonymy.lean` module docstring for the diagnostics. Used in
    gradable-adjective semantics to distinguish licensing patterns of
    the two-threshold model.

    Antonymy is genuinely binary (an antonym pair is *either* contradictory *or*
    contrary — never subcontrary or unconnected), so this stays a 2-case type;
    `NegationType.toOpposition` embeds it as the `{contradictory, contrary}` slice
    of the substrate's `Aristotelian.OppositionRel`, and `AntonymPrediction`'s
    `isContradictory_*Denot` ground the tag in the real opposition between the
    adjective denotations. -/
inductive NegationType where
  | contradictory
  | contrary
  deriving Repr, DecidableEq, Fintype

/-- Embed the antonymy type into the substrate's opposition relation: an antonym
pair occupies exactly the `contradictory` or `contrary` cell of `OppositionRel`. -/
def NegationType.toOpposition : NegationType → Aristotelian.OppositionRel
  | .contradictory => .contradictory
  | .contrary      => .contrary

instance : Coe NegationType Aristotelian.OppositionRel := ⟨NegationType.toOpposition⟩

theorem NegationType.toOpposition_injective :
    Function.Injective NegationType.toOpposition := by
  intro a b h; cases a <;> cases b <;> simp_all [NegationType.toOpposition]

/-- The image of `toOpposition` is exactly the two antonym cells of `OppositionRel`. -/
theorem NegationType.range_toOpposition (r : Aristotelian.OppositionRel) :
    (∃ n : NegationType, n.toOpposition = r) ↔ r = .contradictory ∨ r = .contrary := by
  constructor
  · rintro ⟨n, rfl⟩; cases n <;> simp [NegationType.toOpposition]
  · rintro (rfl | rfl)
    exacts [⟨.contradictory, rfl⟩, ⟨.contrary, rfl⟩]

/-- Predicted behaviour of an antonymic adjective pair under sentential
    negation: do positive and negative forms diverge under polarity
    (asymmetric — gap-licensed strengthening) or behave in parallel
    (symmetric — no gap available)?

    Used as the codomain of prediction signatures in studies of negated
    antonymic adjectives (Horn 1989, Krifka 2007, Tessler & Franke 2019,
    Alexandropoulou & Gotzner 2024). Anchored in
    `Semantics/Gradability/AntonymPrediction.lean`'s
    `predictionForAntonymy` map and its substrate witness theorems. -/
inductive Asymmetry where
  | asymmetric    -- diverging behavior under polarity
  | symmetric     -- parallel behavior under polarity
  deriving Repr, DecidableEq, Fintype

end Features
