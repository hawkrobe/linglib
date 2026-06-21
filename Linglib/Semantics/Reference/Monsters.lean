import Linglib.Semantics.Reference.Kaplan

/-!
# Kaplan's Anti-Monster Thesis (Tower Formulation)
[anand-nevins-2004] [kaplan-1989] [schlenker-2003]

[kaplan-1989]'s anti-monster thesis: the claim that natural language
operators are *content operators* (shifting circumstances of evaluation)
rather than *context operators* (shifting contexts of utterance).

Under the tower analysis, a monster is a shift that destabilizes some
expression — it changes what an access pattern resolves to (`IsTowerMonster`,
the ∃-projection of `AccessPattern.Stable`; equivalently a non-identity
shift). Kaplan's thesis for English says attitude verbs push identity shifts —
they embed without changing the context of utterance — so English indexicals,
which read from the origin, are stable under embedding (`IsKaplanCompliant`,
the dual ∀-projection of `Stable` in `Reference/Kaplan.lean`).

Cross-linguistic counterexamples
are languages where attitude verbs push non-identity shifts (e.g.,
`attitudeShift` changes the agent to the attitude holder).

## Key Definitions

- `IsTowerMonster`: a shift where apply c != c for some c
- `kaplansThesisAsTower`: English embedding verbs push identity shifts

Schlenker's monstrous `Say_m` operator lives in `Attitudes/ContextQuantification.lean`
as `sayM` (with `ctxBox` its context-meaning specialization); this file is about the
monster *predicate* and Kaplan's thesis, not the operator.

-/

namespace Semantics.Reference.Monsters

open Semantics.Context

-- ════════════════════════════════════════════════════════════════
-- § Tower Monster
-- ════════════════════════════════════════════════════════════════

/-- A context shift is a *tower monster* when it destabilizes the innermost
    reader: pushing it changes what the canonical local access pattern
    (`AccessPattern.innermostReader`) resolves to. This is the
    ∃-over-expressions projection of `AccessPattern.Stable` — the innermost
    reader is its universal witness, since a push only ever changes the
    innermost context — dual to Kaplan-compliance's ∀-over-operators projection
    (`IsKaplanCompliant`). Equivalently (`isTowerMonster_iff_exists`) the shift
    moves some context: `∃ c, σ.apply c ≠ c`.

    Under the tower analysis, monsters are exactly the non-identity shifts.
    English attitude verbs push identity shifts (not monsters); Amharic
    attitude verbs push attitude shifts (monsters). -/
def IsTowerMonster {C : Type*} (σ : ContextShift C) : Prop :=
  ¬ (AccessPattern.innermostReader C).Stable σ

/-- A shift is a monster iff it moves some context: the pointwise
    characterization recovering the direct form `∃ c, σ.apply c ≠ c`. -/
theorem isTowerMonster_iff_exists {C : Type*} (σ : ContextShift C) :
    IsTowerMonster σ ↔ ∃ c, σ.apply c ≠ c := by
  simp only [IsTowerMonster, AccessPattern.Stable, not_forall,
    AccessPattern.innermostReader_resolve, ContextTower.push_innermost]
  constructor
  · rintro ⟨t, ht⟩; exact ⟨t.innermost, ht⟩
  · rintro ⟨c, hc⟩; exact ⟨ContextTower.root c, by simpa using hc⟩

/-- Monsterhood depends only on the shift's action `apply`, not its label:
    shifts with equal `apply` are monsters together. -/
theorem isTowerMonster_congr {C : Type*} {σ τ : ContextShift C}
    (h : σ.apply = τ.apply) : IsTowerMonster σ ↔ IsTowerMonster τ := by
  simp only [isTowerMonster_iff_exists, h]

/-- The identity shift is not a monster. -/
theorem identityShift_not_monster {W : Type*} {E : Type*} {P : Type*} {T : Type*} :
    ¬ IsTowerMonster (identityShift (W := W) (E := E) (P := P) (T := T)) := by
  rw [isTowerMonster_iff_exists]
  rintro ⟨c, h⟩
  exact h (identityShift_apply c)

/-- An attitude shift is a monster when the holder differs from some
    context's agent. -/
theorem attitudeShift_is_monster {W : Type*} {E : Type*} {P : Type*} {T : Type*}
    (holder : E) (attWorld : W) (c : KContext W E P T)
    (hAgent : c.agent ≠ holder) :
    IsTowerMonster (attitudeShift (P := P) (T := T) holder attWorld) := by
  rw [isTowerMonster_iff_exists]
  refine ⟨c, fun h => hAgent ?_⟩
  simpa using (congrArg KContext.agent h).symm

-- ════════════════════════════════════════════════════════════════
-- § Kaplan's Thesis (Tower Formulation)
-- ════════════════════════════════════════════════════════════════

/-- Kaplan's thesis as a tower property: embedding verbs in a language push
    shifts that are not monsters (i.e., identity shifts).

    For English, this means all attitude verbs push `identityShift`:
    "John said that I am happy" evaluates "I" at the original context,
    because the embedding verb didn't shift anything.

    The `embeddingShifts` parameter lists the shifts that the language's
    embedding verbs produce. The thesis holds iff none of them is a monster. -/
def KaplansThesisHolds {C : Type*} (embeddingShifts : List (ContextShift C)) : Prop :=
  ∀ σ ∈ embeddingShifts, ¬ IsTowerMonster σ

/-- English embedding verbs push identity shifts. Kaplan's thesis holds. -/
theorem kaplansThesisAsTower {W : Type*} {E : Type*} {P : Type*} {T : Type*} :
    KaplansThesisHolds
      [identityShift (W := W) (E := E) (P := P) (T := T)] := by
  intro σ hMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
  rw [hMem]
  exact identityShift_not_monster

end Semantics.Reference.Monsters
