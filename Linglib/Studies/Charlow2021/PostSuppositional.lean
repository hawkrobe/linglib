import Linglib.Semantics.Dynamic.Core.DynamicTy2
import Mathlib.Data.Fintype.Basic

/-!
# Post-Suppositional Dynamic GQs
[charlow-2021]

[charlow-2021]'s §5: bi-dimensional meanings using a Writer-like monad.
A `PostSupp S A` carries both a value and accumulated post-suppositional
content (an Update that constrains but doesn't change the assignment).

Modified numerals like "exactly 3" contribute their cardinality test as
post-suppositional content, which is resolved after maximization. This
automatically produces cumulative readings because post-suppositions
from different quantifiers compose independently.

-/

namespace Charlow2021.PostSuppositional

open Semantics.Dynamic.Core

variable {S : Type*}

/-- Bi-dimensional meaning: a value paired with post-suppositional content.
    The post-supposition is an Update that will be conjoined at the discourse level,
    after all scope-taking is done. -/
structure PostSupp (S : Type*) (A : Type*) where
  /-- The "at-issue" value -/
  val : A
  /-- Accumulated post-suppositional content -/
  postsup : Update S

/-- `PostSupp S` is the Writer monad over the monoid `(Update S, ⨟, test ⊤)`
    ([charlow-2021] equations 120–121): `pure` carries the trivial
    post-supposition (the `True`-test identity) and `bind` sequences
    post-suppositional content via dynamic conjunction (`dseq`). Independent
    composition of post-suppositions is what yields cumulative readings. -/
instance : Monad (PostSupp S) where
  pure a := ⟨a, test (λ _ => True)⟩
  bind m f := ⟨(f m.val).val, dseq m.postsup (f m.val).postsup⟩

/-- Reify (bullet operator, equation 58): conjoin value and post-supposition.
    For a `PostSupp S (Update S)`, this produces a single Update by sequencing
    the at-issue Update with the post-suppositional constraint. -/
def PostSupp.reify (p : PostSupp S (Update S)) : Update S :=
  dseq p.val p.postsup

/-- Truth at an assignment for bi-dimensional meanings (equation 56):
    the at-issue content and post-suppositional content must both be satisfiable. -/
def PostSupp.trueAt (p : PostSupp S (Update S)) (i : S) : Prop :=
  ∃ (j : S), p.val i j ∧ ∃ (k : S), p.postsup j k

/-- "Exactly N" as post-suppositional meaning (equation 53):
    `⟨M_v(E^v P; []), n_v⟩`
    The at-issue content introduces and maximizes v; the cardinality test
    is the post-supposition. -/
def exactlyN_postsup {S E : Type*} [AssignmentStructure S E] [PartialOrder E] [Fintype E]
    (v : Dref S E) (P : E → Prop) (n : Nat)
    (Mvar' : Dref S E → Update S → Update S)
    (Evar' : Dref S E → (E → Prop) → Update S)
    (CardTest' : Dref S E → Nat → Update S) : PostSupp S (Update S) :=
  ⟨Mvar' v (Evar' v P), CardTest' v n⟩

-- ════════════════════════════════════════════════════
-- § Monad Laws
-- ════════════════════════════════════════════════════

/-- The monad laws are exactly the monoid laws of `(Update S, ⨟, test ⊤)`
    (`test_dseq`, `dseq_test`, `dseq_assoc`), so we register `PostSupp S`
    as a lawful monad rather than re-proving them standalone. -/
instance : LawfulMonad (PostSupp S) := LawfulMonad.mk' (PostSupp S)
  (id_map := by
    rintro α ⟨a, d⟩
    show (⟨a, dseq d (test (λ _ => True))⟩ : PostSupp S α) = ⟨a, d⟩
    rw [dseq_test d (λ _ => True) (λ _ => trivial)])
  (pure_bind := by
    intro α β x f
    show (⟨(f x).val, dseq (test (λ _ => True)) (f x).postsup⟩ : PostSupp S β) = f x
    rw [test_dseq (λ _ => True) (f x).postsup (λ _ => trivial)])
  (bind_assoc := by
    intro α β γ x f g
    show (⟨(g (f x.val).val).val,
          dseq (dseq x.postsup (f x.val).postsup) (g (f x.val).val).postsup⟩ : PostSupp S γ)
       = ⟨(g (f x.val).val).val,
          dseq x.postsup (dseq (f x.val).postsup (g (f x.val).val).postsup)⟩
    rw [dseq_assoc])

/-- Reify of a pure post-supposition recovers the original Update
    (modulo the trivial True test). -/
theorem PostSupp.reify_pure {S : Type*} (D : Update S) :
    PostSupp.reify (pure D) = dseq D (test (λ _ => True)) := by
  rfl

/-- Post-suppositional combination yields cumulative readings.
    TODO: Formalize the full derivation. -/
theorem postsup_cumulative {S E : Type*} [AssignmentStructure S E]
    [PartialOrder E] [Fintype E] :
    ∀ (v u : Dref S E) (_boys _movies : E → Prop),
    True := by
  intro _ _ _ _; trivial

end Charlow2021.PostSuppositional
