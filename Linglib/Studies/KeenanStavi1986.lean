import Linglib.Semantics.Quantification.Counting
import Linglib.Fragments.English.Toy

/-!
# Keenan & Stavi (1986): A Semantic Characterization of Determiners

[keenan-stavi-1986] characterize the possible determiner denotations of
natural language as the conservative functions, and classify which
determiners are existential. This file holds the toy-witnessed
counterexamples to those properties for specific determiners: the
artificial `m_sem` fails conservativity, and `every`/`most` fail
existentiality. The witness type is the toy fragment's `ToyEntity`.

The property definitions (`Conservative`, `Existential`) live in
`Semantics.Quantification`; positive results for English determiners
live there and in `Studies/BarwiseCooper1981.lean`.
-/

namespace KeenanStavi1986

open Quantification
open Semantics.Montague (ToyEntity)
open Semantics.Montague.ToyLexicon (student_sem thing_sem)

/-- `m_sem` is not conservative: it inspects `B` outside `A`. -/
theorem m_not_conservative : ¬ Conservative (m_sem (α := ToyEntity)) := by
  -- TODO: pick A = `student_sem` and B chosen so |A| = |B| but |A ∩ B| < |A|,
  -- giving M(A,B) ↔ false yet M(A, A ∩ B) ↔ true.
  sorry

/-- `⟦every⟧` is NOT existential (K&S §3.3). -/
theorem every_not_existential : ¬ Existential (every_sem (α := ToyEntity)) := by
  intro h
  have hFwd := (h thing_sem student_sem).mpr
  have : every_sem (fun x => thing_sem x ∧ student_sem x) (fun _ => True) := by
    intro x _; trivial
  exact absurd (hFwd this ToyEntity.pizza trivial) id

/-- `⟦most⟧` is NOT existential (K&S §3.3). -/
theorem most_not_existential : ¬ Existential (most_sem (α := ToyEntity)) := by
  -- TODO: witness most(student, sleeps) on toy domain where |student ∩ sleeps|
  -- = |student \ sleeps| = 1, then most(student ∩ sleeps, True) is true (1 > 0)
  -- but most(student, sleeps) is false (1 > 1 fails).
  sorry

end KeenanStavi1986
