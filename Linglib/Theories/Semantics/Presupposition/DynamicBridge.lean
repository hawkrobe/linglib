import Linglib.Core.Semantics.Presupposition
import Linglib.Theories.Semantics.Dynamic.Core.CCP

/-!
# PrProp ↔ CCP Bridge
@cite{heim-1983} @cite{beaver-2001}

Connects the two parallel representations of presupposition in linglib:

1. **Static** (`PrProp W`): a pair of `W → Bool` functions (presup + assertion)
2. **Dynamic** (`CCP W`): a context change potential `Set W → Set W`

@cite{beaver-2001}'s entire book is about the relationship between these
two views. The static (trivalent/partial) and dynamic (CCP) approaches
make the same predictions for the basic connectives — this module proves
that correspondence.

## Key Conversions

- `PrProp.presupTest`: CCP that filters out worlds where presup fails
- `PrProp.assertFilter`: CCP that filters out worlds where assertion fails
- `PrProp.toCCP`: composition of presupTest then assertFilter

## Key Theorems

- `toCCP_preserves_impFilter`: filtering implication via PrProp agrees with
  sequential CCP composition
- `presupTest_is_eliminative`: presupposition tests only remove worlds
-/

namespace Semantics.Presupposition.DynamicBridge

open Core.Presupposition
open Core.Proposition
open Semantics.Dynamic.Core

variable {W : Type*}

-- ════════════════════════════════════════════════════════════════
-- § 1. PrProp → CCP Conversions
-- ════════════════════════════════════════════════════════════════

/-- Presupposition test CCP: keeps only worlds where the presupposition holds.
    This is the definedness condition of the PrProp. -/
def PrProp.presupTest (p : PrProp W) : CCP W :=
  λ s => { w ∈ s | p.presup w = true }

/-- Assertion filter CCP: keeps only worlds where the assertion holds.
    This is the at-issue content of the PrProp. -/
def PrProp.assertFilter (p : PrProp W) : CCP W :=
  λ s => { w ∈ s | p.assertion w = true }

/-- Full CCP for a PrProp: test presupposition, then filter by assertion.
    This treats presupposition failure as rejection (Strong Kleene behavior).

    Equivalent to: `{ w ∈ s | p.presup w ∧ p.assertion w }`. -/
def PrProp.toCCP (p : PrProp W) : CCP W :=
  CCP.seq p.presupTest p.assertFilter

-- ════════════════════════════════════════════════════════════════
-- § 2. Basic Properties
-- ════════════════════════════════════════════════════════════════

/-- Presupposition tests are eliminative: they only remove worlds. -/
theorem presupTest_eliminative (p : PrProp W) :
    IsEliminative p.presupTest :=
  λ _ _ hw => hw.1

/-- Assertion filters are eliminative. -/
theorem assertFilter_eliminative (p : PrProp W) :
    IsEliminative p.assertFilter :=
  λ _ _ hw => hw.1

/-- The full toCCP is eliminative (composition of eliminatives). -/
theorem toCCP_eliminative (p : PrProp W) :
    IsEliminative p.toCCP :=
  eliminative_seq _ _ (presupTest_eliminative p) (assertFilter_eliminative p)

/-- Membership in presupTest output. -/
theorem mem_presupTest (p : PrProp W) (s : Set W) (w : W) :
    w ∈ p.presupTest s ↔ w ∈ s ∧ p.presup w = true := Iff.rfl

/-- Membership in assertFilter output. -/
theorem mem_assertFilter (p : PrProp W) (s : Set W) (w : W) :
    w ∈ p.assertFilter s ↔ w ∈ s ∧ p.assertion w = true := Iff.rfl

/-- Membership in toCCP output. -/
theorem mem_toCCP (p : PrProp W) (s : Set W) (w : W) :
    w ∈ p.toCCP s ↔ w ∈ s ∧ p.presup w = true ∧ p.assertion w = true := by
  simp only [PrProp.toCCP, CCP.seq, PrProp.assertFilter, PrProp.presupTest,
             Set.mem_sep_iff]
  constructor
  · rintro ⟨⟨hw, hp⟩, ha⟩; exact ⟨hw, hp, ha⟩
  · rintro ⟨hw, hp, ha⟩; exact ⟨⟨hw, hp⟩, ha⟩

-- ════════════════════════════════════════════════════════════════
-- § 3. Correspondence: Filtering Connectives ↔ CCP Composition
-- ════════════════════════════════════════════════════════════════

/-- Negation correspondence: PrProp.neg.toCCP filters by
    ¬assertion (when presup holds), matching dynamic negation's
    test behavior for eliminative operations. -/
theorem neg_toCCP (p : PrProp W) (s : Set W) (w : W) :
    w ∈ (PrProp.neg p).toCCP s ↔
    w ∈ s ∧ p.presup w = true ∧ p.assertion w = false := by
  simp only [mem_toCCP, PrProp.neg]
  constructor
  · rintro ⟨hw, hp, ha⟩
    exact ⟨hw, hp, by cases p.assertion w <;> simp_all⟩
  · rintro ⟨hw, hp, ha⟩
    exact ⟨hw, hp, by simp [ha]⟩

/-- **Filtering implication via PrProp agrees with CCP composition.**

    When the global context entails p's presupposition, the filtering
    implication `impFilter p q` applied to the context yields the same
    result as first updating with p's assertion (creating the local
    context for q), then testing q's presupposition.

    This is the core correspondence of @cite{beaver-2001} Ch. 3:
    Heim's CCP filtering = Karttunen's heritage = static filtering
    connectives, all in agreement for the basic cases. -/
theorem impFilter_presup_matches_local_context
    (p q : PrProp W) (s : Set W)
    (h_presup : ∀ w ∈ s, p.presup w = true) :
    (∀ w ∈ s, (PrProp.impFilter p q).presup w = true) ↔
    (∀ w ∈ s, p.assertion w = true → q.presup w = true) := by
  constructor
  · intro hfilt w hw ha
    have := hfilt w hw
    simp only [PrProp.impFilter, h_presup w hw, Bool.true_and] at this
    cases hq : q.presup w
    · simp [ha, hq] at this
    · rfl
  · intro hlocal w hw
    simp only [PrProp.impFilter, h_presup w hw, Bool.true_and]
    cases ha : p.assertion w
    · simp
    · simp [hlocal w hw ha]

-- ════════════════════════════════════════════════════════════════
-- § 4. Context Support Bridge
-- ════════════════════════════════════════════════════════════════

/-- A context (set of worlds) supports a PrProp's presupposition
    iff the presupTest is the identity on that context. -/
theorem supports_presup_iff_presupTest_id (p : PrProp W) (s : Set W) :
    (∀ w ∈ s, p.presup w = true) ↔ p.presupTest s = s := by
  constructor
  · intro h
    ext w
    simp only [PrProp.presupTest, Set.mem_sep_iff]
    exact ⟨λ ⟨hw, _⟩ => hw, λ hw => ⟨hw, h w hw⟩⟩
  · intro h w hw
    have : w ∈ p.presupTest s := by rw [h]; exact hw
    exact this.2

end Semantics.Presupposition.DynamicBridge
