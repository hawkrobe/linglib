import Linglib.Core.Semantics.Proposition

/-!
# Postsuppositions
@cite{brasoveanu-2009} @cite{lauer-2009} @cite{glass-2025}

Output-context constraints: conditions on the Common Ground *after* an
utterance updates it, as opposed to presuppositions which constrain
the *input* context.

@cite{glass-2025} argues that Mandarin yǐwéi has a postsupposition
◇¬p — after accepting "x yǐwéi p", the CG must be compatible with ¬p.
This is distinct from a presupposition (input-context condition) and
cannot be derived from veridicality alone.
-/

namespace Core.Postsupposition

/-- A postsupposition: a constraint on the output context after a
    discourse update.

    Unlike presuppositions (input-context constraints on `PrProp.presup`),
    postsuppositions constrain what must hold of the context *after* the
    at-issue content updates it.

    The `condition` takes a context set (as `List W`) and the embedded
    proposition `p`, returning whether the output-context requirement holds. -/
structure Postsupposition (W : Type*) where
  condition : List W → (W → Bool) → Bool

namespace Postsupposition

variable {W : Type*}

/-- No postsupposition (trivially satisfied). -/
def none : Postsupposition W := ⟨fun _ _ => true⟩

/-- Weak contrafactive postsupposition: the output context must be
    compatible with ¬p. That is, at least one world in the output
    context has p false.

    This is yǐwéi's ◇¬p (@cite{glass-2025}, @cite{glass-2023}). -/
def weakContrafactive : Postsupposition W :=
  ⟨fun cs p => cs.any (!p ·)⟩

/-- Strong contrafactive postsupposition: the output context must
    entail ¬p. That is, all worlds in the output context have p false.

    This is the hypothetical *contra* verb's requirement — UNATTESTED. -/
def strongContrafactive : Postsupposition W :=
  ⟨fun cs p => cs.all (!p ·)⟩

/-- Check satisfaction against a concrete context set and proposition. -/
def satisfied (ps : Postsupposition W) (outputCtx : List W) (p : W → Bool) : Bool :=
  ps.condition outputCtx p

/-- The trivial postsupposition is always satisfied. -/
theorem none_always_satisfied (cs : List W) (p : W → Bool) :
    none.satisfied cs p = true := rfl

/-- Strong contrafactivity entails weak contrafactivity (for nonempty contexts):
    if CG ⊨ ¬p (all worlds have ¬p), then CG ◇ ¬p (some world has ¬p).
    This captures @cite{glass-2025}'s key observation that yǐwéi's requirement
    is strictly weaker than the hypothetical *contra* verb's. -/
theorem strong_entails_weak (cs : List W) (p : W → Bool) (hne : cs ≠ []) :
    strongContrafactive.satisfied cs p = true →
    weakContrafactive.satisfied cs p = true := by
  simp only [satisfied, strongContrafactive, weakContrafactive]
  intro h
  match cs, hne with
  | w :: ws, _ =>
    simp only [List.any_cons, List.all_cons, Bool.and_eq_true] at *
    exact Bool.or_eq_true_iff.mpr (.inl h.1)

/-- Weak contrafactivity does NOT entail strong: a context can be
    compatible with ¬p without entailing ¬p. -/
theorem weak_not_entails_strong :
    ∃ (cs : List Bool) (p : Bool → Bool),
      weakContrafactive.satisfied cs p = true ∧
      strongContrafactive.satisfied cs p = false :=
  ⟨[true, false], id, rfl, rfl⟩

end Postsupposition
end Core.Postsupposition
