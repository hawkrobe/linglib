import Linglib.Morphology.Paradigm.Contiguity

/-!
# Case paradigms
[caha-2009] [bobaljik-2012]

Framework-neutral substrate for allomorphy patterns over the four core
cases (NOM, ACC, GEN, DAT): the n = 4 specialization of
`Morphology.Paradigm`, mirroring `Morphology/Paradigm/Degree.lean` for
degree. `AllomorphyPattern` is the ergonomic record form;
`AllomorphyPattern.toParadigm` connects it to the general substrate, and
the decidable `IsContiguous` / `ViolatesABA` predicates are defined
through that projection, so the generic theory applies by construction.

What *explains* the *ABA gap is contested between DM (post-syntactic
VI + Elsewhere ordering — [bobaljik-2012]) and Nanosyntax (phrasal
spellout + Superset Principle — [caha-2009]). This file commits to
neither; per-paper analyses live in `Studies/`. Case-hierarchy
adjacency and inventory relations live with the Blake-rank API in
`Features/Case/Basic.lean`.
-/

namespace Morphology.Case.Allomorphy



-- ============================================================================
-- § 1: AllomorphyPattern + *ABA
-- ============================================================================

/-- An allomorphy pattern over the four core cases (NOM, ACC, GEN, DAT),
    represented as a form-class index for each case. -/
structure AllomorphyPattern where
  nom : Nat
  acc : Nat
  gen : Nat
  dat : Nat
  deriving DecidableEq, Repr

/-- The general-substrate form of an allomorphy pattern: the n = 4
    instance of `Morphology.Paradigm`. -/
def AllomorphyPattern.toParadigm (p : AllomorphyPattern) :
    Morphology.Paradigm 4 ℕ :=
  ![p.nom, p.acc, p.gen, p.dat]

/-- Is a pattern contiguous? Each form class occupies a contiguous span
    on the hierarchy — the generic
    `Morphology.IsContiguous` (`Paradigm/Contiguity.lean`), by construction. -/
def AllomorphyPattern.IsContiguous (p : AllomorphyPattern) : Prop :=
  Morphology.IsContiguous p.toParadigm

instance (p : AllomorphyPattern) : Decidable p.IsContiguous :=
  inferInstanceAs (Decidable (Morphology.IsContiguous _))

/-- A pattern violates *ABA: some form class recurs across a distinct
    intervening one. Equivalent to ¬IsContiguous. -/
def AllomorphyPattern.ViolatesABA (p : AllomorphyPattern) : Prop :=
  ¬ p.IsContiguous

instance (p : AllomorphyPattern) : Decidable p.ViolatesABA :=
  inferInstanceAs (Decidable (¬ _))

-- ============================================================================
-- § 2: *ABA Verification on Concrete Patterns
-- ============================================================================

def abbPattern : AllomorphyPattern := ⟨0, 1, 1, 1⟩
def aabPattern : AllomorphyPattern := ⟨0, 0, 0, 1⟩
def aabbPattern : AllomorphyPattern := ⟨0, 0, 1, 1⟩
def ababPattern : AllomorphyPattern := ⟨0, 1, 0, 1⟩
def abaPattern : AllomorphyPattern := ⟨0, 1, 0, 0⟩
def babPattern : AllomorphyPattern := ⟨1, 0, 1, 0⟩
def uniformPattern : AllomorphyPattern := ⟨0, 0, 0, 0⟩

/-! Smoke tests for the named patterns: each evaluates as the
    AllomorphyPattern shape its name implies. Demoted from `theorem`
    to `example` because nothing in the codebase consumes them by
    name. -/

example : abbPattern.IsContiguous := by decide
example : ¬ abbPattern.ViolatesABA := by decide
example : aabPattern.IsContiguous := by decide
example : aabbPattern.IsContiguous := by decide
example : ababPattern.ViolatesABA := by decide
example : ¬ ababPattern.IsContiguous := by decide
example : abaPattern.ViolatesABA := by decide
example : babPattern.ViolatesABA := by decide
example : uniformPattern.IsContiguous := by decide

-- ============================================================================
-- § 3: Literature pattern examples
-- ============================================================================

/-! Five fixed `AllomorphyPattern` shapes that show up in the
    syncretism literature. Demoted to `example` for the same reason as
    the smoke tests above: no by-name consumers. -/

example : (AllomorphyPattern.mk 0 0 1 1).IsContiguous := by decide
example : (AllomorphyPattern.mk 0 1 0 1).ViolatesABA := by decide
example : (AllomorphyPattern.mk 0 1 1 2).IsContiguous := by decide
example : (AllomorphyPattern.mk 0 1 2 2).IsContiguous := by decide
example : (AllomorphyPattern.mk 0 1 1 0).ViolatesABA := by decide

end Morphology.Case.Allomorphy
