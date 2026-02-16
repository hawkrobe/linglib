import Linglib.Theories.DynamicSemantics.Core.DynamicTy2
import Mathlib.Data.Fintype.Basic

/-!
# Post-Suppositional Dynamic GQs

Charlow's (2021) §5: bi-dimensional meanings using a Writer-like monad.
A `PostSupp S A` carries both a value and accumulated post-suppositional
content (a DRS that constrains but doesn't change the assignment).

Modified numerals like "exactly 3" contribute their cardinality test as
post-suppositional content, which is resolved after maximization. This
automatically produces cumulative readings because post-suppositions
from different quantifiers compose independently.

## References

- Charlow, S. (2021). Post-suppositions and semantic theory. *L&P* 44, 701–765.
  §5, equations 53–58; Appendix B, equations 120–121.
- Brasoveanu, A. (2012). Modified numerals as post-suppositions.
-/

namespace DynamicSemantics.DynamicGQ.PostSuppositional

open DynamicSemantics.Core.DynamicTy2

variable {S : Type*}

/-- Bi-dimensional meaning: a value paired with post-suppositional content.
    The post-supposition is a DRS that will be conjoined at the discourse level,
    after all scope-taking is done. -/
structure PostSupp (S : Type*) (A : Type*) where
  /-- The "at-issue" value -/
  val : A
  /-- Accumulated post-suppositional content -/
  postsup : DRS S

/-- Pure: trivial post-supposition (equation 120).
    The post-suppositional DRS is the identity (test True). -/
def PostSupp.pure {S A : Type*} (a : A) : PostSupp S A :=
  ⟨a, test (λ _ => True)⟩

/-- Bind: sequence post-suppositions via dseq (equation 121).
    Post-suppositional content accumulates via dynamic conjunction. -/
def PostSupp.bind {S A B : Type*} (m : PostSupp S A) (f : A → PostSupp S B) : PostSupp S B :=
  let result := f m.val
  ⟨result.val, dseq m.postsup result.postsup⟩

/-- Map: apply a function to the at-issue value, preserving post-suppositions. -/
def PostSupp.map {S A B : Type*} (f : A → B) (m : PostSupp S A) : PostSupp S B :=
  ⟨f m.val, m.postsup⟩

/-- Reify (bullet operator, equation 58): conjoin value and post-supposition.
    For a `PostSupp S (DRS S)`, this produces a single DRS by sequencing
    the at-issue DRS with the post-suppositional constraint. -/
def PostSupp.reify (p : PostSupp S (DRS S)) : DRS S :=
  dseq p.val p.postsup

/-- Truth at an assignment for bi-dimensional meanings (equation 56):
    the at-issue content and post-suppositional content must both be satisfiable. -/
def PostSupp.trueAt (p : PostSupp S (DRS S)) (i : S) : Prop :=
  ∃ (j : S), p.val i j ∧ ∃ (k : S), p.postsup j k

/-- "Exactly N" as post-suppositional meaning (equation 53):
    `⟨M_v(E^v P ; []), n_v⟩`
    The at-issue content introduces and maximizes v; the cardinality test
    is the post-supposition. -/
def exactlyN_postsup {S E : Type*} [AssignmentStructure S E] [PartialOrder E] [Fintype E]
    (v : Dref S E) (P : E → Prop) (n : Nat)
    (Mvar' : Dref S E → DRS S → DRS S)
    (Evar' : Dref S E → (E → Prop) → DRS S)
    (CardTest' : Dref S E → Nat → DRS S) : PostSupp S (DRS S) :=
  ⟨Mvar' v (Evar' v P), CardTest' v n⟩

-- ════════════════════════════════════════════════════
-- § Monad Laws
-- ════════════════════════════════════════════════════

/-- Left identity for PostSupp bind. -/
theorem PostSupp.bind_left_id {S A B : Type*} (a : A) (f : A → PostSupp S B) :
    PostSupp.bind (PostSupp.pure a) f = f a := by
  simp only [PostSupp.bind, PostSupp.pure]
  -- dseq (test fun _ => True) (f a).postsup = (f a).postsup
  -- because ∃ h, (i = h ∧ True) ∧ D h j  ↔  D i j
  have : dseq (test λ _ => True) (f a).postsup = (f a).postsup := by
    funext i j; simp [dseq, test]
  simp [this]

/-- Reify of a pure post-supposition recovers the original DRS
    (modulo the trivial True test). -/
theorem PostSupp.reify_pure {S : Type*} (D : DRS S) :
    PostSupp.reify (PostSupp.pure D) = dseq D (test (λ _ => True)) := by
  rfl

/-- Post-suppositional combination yields cumulative readings.
    TODO: Formalize the full derivation. -/
theorem postsup_cumulative {S E : Type*} [AssignmentStructure S E]
    [PartialOrder E] [Fintype E] :
    ∀ (v u : Dref S E) (_boys _movies : E → Prop),
    True := by
  intro _ _ _ _; trivial

end DynamicSemantics.DynamicGQ.PostSuppositional
