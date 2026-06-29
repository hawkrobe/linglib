import Mathlib.Tactic.Simps.Basic

/-!
# The `rsa` simp set

Registered here, separately from the lemmas it tags: Lean cannot use an attribute
in the same file where it is declared (the same split as `pmf_eval_simps` in
`Core/Probability/Eval.lean`, and mathlib's `Mathlib/Tactic/Attr/Register.lean`).

The partition-cancelling RSA decomposition lemmas in `RSA/Operators.lean` and
`RSA/Canonical.lean` are tagged `@[rsa]`. `simp [rsa]` rewrites an `S1`/`L1`
*preference* goal (`S1 x < S1 y`, `(L1 …).fst w₁ < …`) to its structural
score/posterior comparison — the normalisation factor cancels by rewriting, not by
evaluating a state-space sum. This is the migration API replacing `rsa_predict`
reflection with simplification: a migrated prediction is `by simp [rsa]` down to a
condition closed by a *theorem*, not a `decide`/`norm_num` over a sum.
-/

/-- Simp set of the partition-cancelling RSA decomposition lemmas
(`S1`/`L1` preference ↔ score/posterior comparison). -/
register_simp_attr rsa
