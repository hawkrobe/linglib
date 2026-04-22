import Mathlib.Data.Set.Card
import Linglib.Theories.Semantics.Classifier.Defs
import Linglib.Theories.Semantics.Classifier.TypeN

/-!
# Composition Rules for Sudo (2016)
@cite{sudo-2016} @cite{chierchia-1998}

The compositional apparatus that allows numerals (type `⟨s,n⟩`) and
classifier-modified numeral phrases (type `⟨s,⟨e,t⟩⟩` after classifier
application) to combine with noun denotations.

## Sudo's Three Type-Shifters

- **∪-operator** (Sudo eq. 10): `∪(λw. n) = λw. λx. |{y ⊑ x : atomic_w(y)}| = n`.
  Lifts a numeral intension `⟨s,n⟩` to a predicate `⟨s,⟨e,t⟩⟩` over entities
  with exactly `n` atomic parts.
- **∩-operator** (Sudo eq. 24): the partial inverse of ∪. Maps certain
  properties back to numeral intensions.
- The composition rules **∪-Shifted PM** (eq. 11), **∪-Shifted FA v1/v2**
  (eqs. 19a, 19b, 26a, 26b), and **∩-Shifted FA** (eq. 26c) lift Heim &
  Kratzer's standard FA / PM by inserting ∪/∩ at type mismatches.

## The Blocking Principle (Chierchia 1998, applied by Sudo 2016 §2.3)

The crucial cross-linguistic asymmetry is that Sudo's ∪-operator is
**blocked in Japanese** by the presence of overt classifiers in the
lexicon — but **available in English**, where there is no equivalent
overt operator. This is Chierchia (1998)'s Blocking Principle applied
to a phonologically silent type-shifter on numerals.

We formalize blocking as an `UpAvailability` enum derived from whether
the language has classifiers in its lexicon. The downstream consequence —
that predicative numerals like *"The guests are twelve"* (English ✓) vs
*"okyakusan-wa juu-ni-da"* (Japanese ✗, Sudo eq. 15) — is then a
corollary, not a stipulation.

## Scope

This file defines the type signatures and the blocking machinery.
The presupposition-tracking compositional rules (PM/FA with full
domain-of-definition checking per Sudo eqs. 11/19/26) are out of scope
for the first pass; they require partial-function plumbing that is
peripheral to the cross-paper argument the file is meant to enable.
-/

namespace Semantics.Classifier

universe u v

variable {W : Type u} {E : Type v} [PartialOrder E]

/-- Sudo's ∪-operator on numeral intensions (eq. 10):
    `∪(n)(w)(x)` iff `x` has exactly `n w` atomic ⊑-parts according to
    the contextually-supplied atomicity predicate `atomic`.

    In the type-theoretic semantics literature this is a type shift
    `⟨s,n⟩ → ⟨s,⟨e,t⟩⟩`. -/
def upNum (atomic : Core.Intension W (E → Prop)) (n : NumeralIntens W) :
    Core.Intension W (E → Prop) :=
  fun w x => {y : E | y ≤ x ∧ atomic w y}.ncard = n w

@[simp] lemma upNum_apply (atomic : Core.Intension W (E → Prop))
    (n : NumeralIntens W) (w : W) (x : E) :
    upNum atomic n w x ↔ {y : E | y ≤ x ∧ atomic w y}.ncard = n w := Iff.rfl

/-- Sudo's ∩-operator (eq. 24): a partial inverse of `upNum`.
    `downNum P w` returns the cardinality of atomic `P`-parts of any element of
    `P w`, packaged as a `Option ℕ` to model partiality (Sudo notes ∩ is only
    defined for "certain properties").

    This is a placeholder signature; a fuller treatment would parameterize
    over a uniqueness-of-cardinality witness and would establish ∪ ∘ ∩ = id
    on the property image of ∪. Marked `noncomputable` because the inverse
    of an arbitrary intensional property is not constructively decidable. -/
noncomputable def downNum (atomic P : Core.Intension W (E → Prop)) (w : W) :
    Option ℕ :=
  open Classical in
  if h : ∃ x, P w x then
    some {y : E | y ≤ h.choose ∧ atomic w y}.ncard
  else none

/-- Whether the silent ∪-shift on numerals is available in a language.

    Sudo (2016, §2.3) follows Chierchia (1998)'s Blocking Principle: a
    silent operator is blocked when there are overt lexical items playing
    the same role. In Japanese, the classifiers `-rin`/`-hiki`/`-nin`/...
    play the role ∪ would play (turning numerals into predicates), so ∪
    is blocked. In English, no such overt items exist, so ∪ is available. -/
inductive UpAvailability where
  /-- No overt classifier blocks the silent ∪-operator (English-like). -/
  | available
  /-- An overt classifier in the lexicon blocks ∪ (Japanese-like). -/
  | blocked
  deriving DecidableEq, Repr

/-- Derivation of `UpAvailability` from lexicon facts:
    ∪ is available iff the language has no classifiers in its lexicon.

    This is *not* a stipulation about which languages allow predicative
    numerals — it is a derivation of that fact from the deeper Blocking
    Principle. Whether a particular language has classifiers is a fragment-
    level fact (`Fragments.{Lang}.Classifiers.allClassifiers`); whether
    predicative numerals are licit is a downstream consequence. -/
def upAvailability (hasOvertClassifiers : Bool) : UpAvailability :=
  if hasOvertClassifiers then .blocked else .available

@[simp] lemma upAvailability_true :
    upAvailability true = .blocked := rfl

@[simp] lemma upAvailability_false :
    upAvailability false = .available := rfl

/-- A language with overt classifiers blocks the silent ∪-shift.
    The empirical content (Sudo eq. 15: *"okyakusan-wa juu-ni-da"* in
    Japanese) is a downstream consequence of this. -/
theorem classifiers_block_up :
    upAvailability true = .blocked := rfl

/-- A language without overt classifiers leaves the silent ∪-shift available.
    The empirical content (Sudo eq. 13: *"The number of guests is twelve"*
    in English) follows. -/
theorem no_classifiers_leave_up_available :
    upAvailability false = .available := rfl

end Semantics.Classifier
