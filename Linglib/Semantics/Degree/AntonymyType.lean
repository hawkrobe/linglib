import Mathlib.Tactic.DeriveFintype
import Linglib.Core.Order.Aristotelian

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

The relation between a positive form and its antonym is `AntonymRelation`.
-/

namespace Degree

/-- Antonymy type: contradictory (no gap) vs contrary (gap).

    See `Antonymy.lean` module docstring for the diagnostics. Used in
    gradable-adjective semantics to distinguish licensing patterns of
    the two-threshold model.

    Antonymy is genuinely binary (an antonym pair is *either* contradictory *or*
    contrary — never subcontrary or unconnected), so this stays a 2-case type;
    `AntonymRelation.toOpposition` embeds it as the `{contradictory, contrary}` slice
    of the substrate's `Aristotelian.OppositionRel`, and `Degree.Antonymy`'s
    `isContradictory_*Ty.Domain` ground the tag in the real opposition between the
    adjective denotations. -/
inductive AntonymRelation where
  | contradictory
  | contrary
  deriving Repr, DecidableEq, Fintype

/-- Embed the antonymy type into the substrate's opposition relation: an antonym
pair occupies exactly the `contradictory` or `contrary` cell of `OppositionRel`. -/
def AntonymRelation.toOpposition : AntonymRelation → Aristotelian.OppositionRel
  | .contradictory => .contradictory
  | .contrary      => .contrary

instance : Coe AntonymRelation Aristotelian.OppositionRel := ⟨AntonymRelation.toOpposition⟩

theorem AntonymRelation.toOpposition_injective :
    Function.Injective AntonymRelation.toOpposition := by
  intro a b h; cases a <;> cases b <;> simp_all [AntonymRelation.toOpposition]

/-- The image of `toOpposition` is exactly the two antonym cells of `OppositionRel`. -/
theorem AntonymRelation.range_toOpposition (r : Aristotelian.OppositionRel) :
    (∃ n : AntonymRelation, n.toOpposition = r) ↔ r = .contradictory ∨ r = .contrary := by
  constructor
  · rintro ⟨n, rfl⟩; cases n <;> simp [AntonymRelation.toOpposition]
  · rintro (rfl | rfl)
    exacts [⟨.contradictory, rfl⟩, ⟨.contrary, rfl⟩]

/-- Interpretation pattern of an antonymic adjective pair under sentential
    negation: the negated positive and negated negative forms diverge
    (asymmetric) or behave in parallel (symmetric). The codomain of the
    prediction signatures in studies of negated antonyms. -/
inductive Asymmetry where
  | asymmetric    -- diverging behavior under polarity
  | symmetric     -- parallel behavior under polarity
  deriving Repr, DecidableEq, Fintype

end Degree
