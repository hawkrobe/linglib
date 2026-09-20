import Linglib.Semantics.Quantification.Numerals.Basic
import Mathlib.Order.Interval.Set.Defs

/-!
# Spector (2013): Bare Numerals and Scalar Implicatures

This file formalizes the comparison of accounts of bare numerals in [spector-2013]. On the
neo-Gricean account ([horn-1972]) a numeral means *at least n* and the *exactly* reading is
a scalar implicature; on the underspecification account ([carston-1988]) context selects
among *at least*, *exactly* and *at most*; on the exactly-only account ([breheny-2008]) the
numeral means *exactly n* and the other readings are contextual by-products; on the
ambiguity account, lexical in [geurts-2006] and through a covert exhaustivity operator in
[chierchia-fox-spector-2012], the numeral has both an *at least* and an *exactly* reading.
The paper's three generalizations are that *at least* readings are available in every
embedded environment, *exactly* readings in every environment, and *at most* readings only
in downward-entailing ones. The readings are the intervals `Comparison.ge.interval`,
`Comparison.eq.interval` and `Comparison.le.interval` of the degree substrate; the exhaustivity
operator `exh` asserts its prejacent and denies every stronger numeral alternative, and on the
numeral itself it is the exact reading (`exh_iff_bare`, the substrate's `exhNumeral`).

The theorems are symbolic in the numeral. Under a necessity modal the neo-Gricean wide-scope
implicature is weaker than the exact reading (`necessity_implicature_of_exact`,
`necessity_implicature_ne_exact`); under negation the account predicts an indirect
implicature, *exactly n − 1*, that is not perceived (`indirect_implicature`), and cannot
reach the *at most* reading of the tax-exemption conditional, since a strengthening must
entail the literal meaning (`atMost_reading_not_entails_literal`). The lexical *at most*
entry under a possibility modal is satisfied by any small accessible value
(`poss_atMost_of_le`), while the neo-Gricean derivation gives the intended bound
(`poss_implicature_iff`). The exactly-only account reaches the *at most* and *at least*
readings of the conditionals through law-like background knowledge (`exact_extends_downward`,
`exact_extends_upward`) but cannot weaken the exact reading in upward-entailing contexts,
where the *in fact, five* continuation is consistent only with *at least*, nor in degree
uses like the voting age, where the exact reading under necessity is false and the
exhaustified *at least* reading says the minimum (`not_nec_exact_Ici`, `nec_Ici_exh_iff`).
The ambiguity account derives the third generalization: unembedded, *at most* does not
entail *exactly*, so no background can strengthen the exact reading to it
(`atMost_not_entails_exact`), while under negation it does (`not_atMost_imp_not_exact`).
The exhaustivity operator scoping below or above a possibility modal yields three readings
of which a lexical ambiguity provides two (`wide_scope_ne_narrow`, `narrow_ne_base`), and
the intermediate embedded implicature of the professor example is the parse between the
contradictory *at least* parse and the vacuous *exactly* parse (`intermediate_parse_iff`).

## Implementation notes

Modal environments are quantification over a set of accessible values, the counts or
degrees compatible with the requirement or permission. `exh` denies every stronger
alternative; for the antitone families of numeral readings this is the denial of the next
numeral alone (`exh_iff_succ`), which is how the paper computes it. Prosodic marking, the
metalinguistic use of negation, and the acquisition and processing evidence the paper
reviews are not formalized.

## References

* [spector-2013]
* [horn-1972]
* [carston-1988]
* [breheny-2008]
* [geurts-2006]
* [chierchia-fox-spector-2012]
-/

namespace Spector2013

open Numerals Degree Set

/-! ### Environments and exhaustification -/

/-- Necessity over the accessible values `A` holds when every one of them is among `I`. -/
def nec (A I : Set ℕ) : Prop := ∀ k ∈ A, k ∈ I

/-- Possibility over the accessible values `A` holds when one of them is among `I`. -/
def poss (A I : Set ℕ) : Prop := ∃ k ∈ A, k ∈ I

/-- The exhaustivity operator on a family of sentences indexed by the numeral: the prejacent
holds and no stronger numeral alternative does. -/
def exh (φ : ℕ → Prop) (m : ℕ) : Prop := φ m ∧ ∀ m' > m, ¬ φ m'

/-- For an antitone family exhaustification denies the next numeral alone. -/
theorem exh_iff_succ {φ : ℕ → Prop} (hφ : Antitone φ) (m : ℕ) :
    exh φ m ↔ φ m ∧ ¬ φ (m + 1) := by
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, h' _ (Nat.lt_succ_self m)⟩
  · rintro ⟨h, h'⟩
    exact ⟨h, fun _ hm' hφ' ↦ h' (hφ (Nat.succ_le_of_lt hm') hφ')⟩

theorem antitone_atLeast (k : ℕ) : Antitone (fun m ↦ k ∈ Comparison.ge.interval m) :=
  fun _ _ h hk ↦ by simp only [Comparison.interval_ge, mem_Ici] at *; omega

theorem antitone_nec (A : Set ℕ) : Antitone (fun m ↦ nec A (Comparison.ge.interval m)) :=
  fun _ _ h hb k hk ↦ antitone_atLeast k h (hb k hk)

theorem antitone_poss (A : Set ℕ) : Antitone (fun m ↦ poss A (Comparison.ge.interval m)) :=
  fun _ _ h ⟨k, hk, hkb⟩ ↦ ⟨k, hk, antitone_atLeast k h hkb⟩

/-- On the numeral itself the operator is the substrate's `exhNumeral`. -/
theorem exhNumeral_iff_exh (m k : ℕ) :
    k ∈ exhNumeral m ↔ exh (fun m ↦ k ∈ Comparison.ge.interval m) m := by
  rw [exh_iff_succ (antitone_atLeast k)]
  exact Iff.rfl

/-- Exhaustifying the *at least* reading is the *exactly* reading, the second
generalization's source. -/
theorem exh_iff_bare (m k : ℕ) :
    exh (fun m ↦ k ∈ Comparison.ge.interval m) m ↔ k ∈ Comparison.eq.interval m :=
  (exhNumeral_iff_exh m k).symm.trans (by rw [exhNumeral_eq])

theorem exact_imp_atLeast {m k : ℕ} (h : k ∈ Comparison.eq.interval m) :
    k ∈ Comparison.ge.interval m :=
  (mem_singleton_iff.1 h).ge

/-! ### The neo-Gricean account -/

/-- Under a necessity modal the exact reading entails the wide-scope implicature: required to
solve exactly three entails required to solve at least three and not required to solve at
least four. -/
theorem necessity_implicature_of_exact {A : Set ℕ} (hA : A.Nonempty) {m : ℕ}
    (h : nec A (Comparison.eq.interval m)) : exh (fun m ↦ nec A (Comparison.ge.interval m)) m := by
  rw [exh_iff_succ (antitone_nec A)]
  refine ⟨fun k hk ↦ exact_imp_atLeast (h k hk), fun hall ↦ ?_⟩
  obtain ⟨k, hk⟩ := hA
  have h1 := h k hk
  have h2 := hall k hk
  simp only [Comparison.interval_eq, mem_singleton_iff, Comparison.interval_ge, mem_Ici] at h1 h2
  omega

/-- The converse fails: the requirement may be met by three or four, so the numeral loses
its exact reading under the modal while the implicature is still triggered. -/
theorem necessity_implicature_ne_exact (m : ℕ) :
    ∃ A : Set ℕ, exh (fun m ↦ nec A (Comparison.ge.interval m)) m ∧
      ¬ nec A (Comparison.eq.interval m) := by
  refine ⟨{m, m + 1}, ?_, fun hall ↦ ?_⟩
  · rw [exh_iff_succ (antitone_nec _)]
    refine ⟨fun k hk ↦ ?_, fun hall ↦ ?_⟩
    · rcases hk with rfl | rfl <;> simp
    · have := hall m (Or.inl rfl)
      simp only [Comparison.interval_ge, mem_Ici] at this
      omega
  · have := hall (m + 1) (Or.inr rfl)
    simp at this

/-- Under negation the scale reverses: the alternative with the next numeral is weaker. -/
theorem neg_reversal (m k : ℕ) :
    k ∉ Comparison.ge.interval m → k ∉ Comparison.ge.interval (m + 1) :=
  fun h h' ↦ h (antitone_atLeast k (Nat.le_succ m) h')

/-- The indirect implicature the account predicts for *Peter didn't solve n + 1 problems*:
denying the stronger alternative *didn't solve n* yields *exactly n*, which is not
perceived. -/
theorem indirect_implicature (m k : ℕ) :
    (k ∉ Comparison.ge.interval (m + 1) ∧ ¬ k ∉ Comparison.ge.interval m) ↔
      k ∈ Comparison.eq.interval m := by
  simp only [Comparison.interval_ge, mem_Ici, Comparison.interval_eq, mem_singleton_iff, not_not]
  constructor <;> intro h <;> omega

/-- A pragmatic strengthening entails the literal meaning, so the *at most* reading of *if
you have three children, you do not qualify* is out of the account's reach: it does not
entail the *at least* reading's consequence that more than three disqualify. -/
theorem atMost_reading_not_entails_literal (m : ℕ) :
    ∃ B : ℕ → Prop, (∀ k ∈ Comparison.le.interval m, ¬ B k) ∧
      ¬ ∀ k ∈ Comparison.gt.interval m, ¬ B k :=
  ⟨(m < ·), fun k hk hB ↦ by simp only [Comparison.interval_le, mem_Iic] at hk; omega,
    fun h ↦ h (m + 1) (Nat.lt_succ_self m) (Nat.lt_succ_self m)⟩

/-! ### The underspecification account -/

/-- The lexical *at most* entry under a possibility modal is satisfied by any accessible
value at or below the numeral: *Sue can have 2000 calories* would be true as soon as she can
have one. -/
theorem poss_atMost_of_le {A : Set ℕ} {k m : ℕ} (hk : k ∈ A) (h : k ≤ m) :
    poss A (Comparison.le.interval m) :=
  ⟨k, hk, h⟩

/-- The intended reading is the neo-Gricean one: the *at least* reading under the
possibility modal, exhaustified, says that no accessible value exceeds the numeral. -/
theorem poss_implicature_iff (A : Set ℕ) (m : ℕ) :
    exh (fun m ↦ poss A (Comparison.ge.interval m)) m ↔
      poss A (Comparison.ge.interval m) ∧ nec A (Comparison.le.interval m) := by
  rw [exh_iff_succ (antitone_poss A)]
  simp only [poss, nec, Comparison.interval_ge, mem_Ici, Comparison.interval_le, mem_Iic,
    not_exists, not_and]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, fun k hk ↦ by have := h2 k hk; omega⟩

/-! ### The exactly-only account -/

/-- With a law-like background that is monotone in the count, the exact reading of the
antecedent extends downward: if exactly three children disqualify, so do fewer. -/
theorem exact_extends_downward {B : ℕ → Prop} (hB : ∀ k k', k ≤ k' → B k → B k') {m : ℕ}
    (h : ¬ B m) : ∀ k, k ∈ Comparison.le.interval m → ¬ B k :=
  fun k hk hBk ↦ h (hB k m hk hBk)

/-- And upward: if exactly three children qualify, so do more. -/
theorem exact_extends_upward {B : ℕ → Prop} (hB : ∀ k k', k ≤ k' → B k → B k') {m : ℕ}
    (h : B m) : ∀ k, k ∈ Comparison.ge.interval m → B k :=
  fun k hk ↦ hB m k hk h

/-- In an upward-entailing context no background can weaken the exact reading, which
entails the *at least* reading: *I have four chairs; in fact, I have five* is consistent
only with the latter. -/
theorem atLeast_of_exact_background {B : ℕ → Prop} {m k : ℕ}
    (h : k ∈ Comparison.eq.interval m) (_ : B k) :
    k ∈ Comparison.ge.interval m :=
  exact_imp_atLeast h

/-- In a degree use the exact reading under necessity is false whenever more than the
numeral is admitted: *one has to be exactly 18* is not what the voting rule says. -/
theorem not_nec_exact_Ici (m : ℕ) : ¬ nec (Ici m) (Comparison.eq.interval m) := fun h ↦ by
  have := h (m + 1) (Nat.le_succ m)
  simp at this

theorem nec_Ici_atLeast (m : ℕ) : nec (Ici m) (Comparison.ge.interval m) := fun _ hk ↦ hk

/-- The exhaustified *at least* reading under necessity says that the numeral is the
minimum required. -/
theorem nec_Ici_exh_iff (n m : ℕ) :
    exh (fun m ↦ nec (Ici n) (Comparison.ge.interval m)) m ↔ n = m := by
  rw [exh_iff_succ (antitone_nec _)]
  simp only [nec, mem_Ici, Comparison.interval_ge]
  constructor
  · rintro ⟨h1, h2⟩
    have := h1 n le_rfl
    by_contra hne
    exact h2 fun k hk ↦ by omega
  · rintro rfl
    exact ⟨fun _ hk ↦ hk, fun h ↦ by have := h n le_rfl; omega⟩

/-! ### The ambiguity account and the third generalization -/

/-- Unembedded, the *at most* reading does not entail the exact reading, so no background
knowledge can produce it by strengthening. -/
theorem atMost_not_entails_exact {m : ℕ} (hm : 0 < m) :
    ¬ ∀ k, k ∈ Comparison.le.interval m → k ∈ Comparison.eq.interval m := fun h ↦ by
  have := h 0 (Nat.zero_le m)
  simp only [Comparison.interval_eq, mem_singleton_iff] at this
  omega

/-- Under negation it does: *nobody read four or fewer* entails *nobody read exactly four*,
which is why the *at most* reading surfaces only in downward-entailing environments. -/
theorem not_atMost_imp_not_exact {m k : ℕ} (h : k ∉ Comparison.le.interval m) :
    k ∉ Comparison.eq.interval m :=
  fun h' ↦ h (mem_singleton_iff.1 h').le

/-! ### Exhaustivity operators and embedded implicatures -/

theorem poss_exact_imp_poss_atLeast {A : Set ℕ} {m : ℕ} (h : poss A (Comparison.eq.interval m)) :
    poss A (Comparison.ge.interval m) :=
  let ⟨k, hk, h⟩ := h
  ⟨k, hk, exact_imp_atLeast h⟩

/-- The operator above the modal, *possible at least n and not possible at least n + 1*,
differs from the operator below it, *possible exactly n*: the former fails, the latter
holds, when both `n` and `n + 1` are possible. -/
theorem wide_scope_ne_narrow (m : ℕ) :
    ∃ A : Set ℕ, poss A (Comparison.eq.interval m) ∧
      ¬ exh (fun m ↦ poss A (Comparison.ge.interval m)) m := by
  refine ⟨{m, m + 1}, ⟨m, Or.inl rfl, rfl⟩, ?_⟩
  rw [exh_iff_succ (antitone_poss _)]
  rintro ⟨-, h⟩
  exact h ⟨m + 1, Or.inr rfl, mem_Ici.2 le_rfl⟩

/-- And the operator below the modal differs from its absence: when only `n + 1` is
possible, *possible at least n* holds and *possible exactly n* does not. -/
theorem narrow_ne_base (m : ℕ) :
    ∃ A : Set ℕ, poss A (Comparison.ge.interval m) ∧ ¬ poss A (Comparison.eq.interval m) := by
  refine ⟨{m + 1}, ⟨m + 1, rfl, Nat.le_succ m⟩, ?_⟩
  rintro ⟨k, hk, h⟩
  rw [mem_singleton_iff] at hk
  subst hk
  simp at h

section Intermediate

variable {S : Type*} (n : S → ℕ) (managed : S → Prop) (m : ℕ)

/-- The professor sentence on the *at least* parse contradicts its continuation *but not when
she asked us to solve more*: the situations demanding more are situations demanding at least
the numeral. -/
theorem atLeast_parse_contradiction
    (h : ∀ s, nec (Ici (n s)) (Comparison.ge.interval m) → managed s) :
    ¬ ∃ s, m < n s ∧ ¬ managed s := by
  rintro ⟨s, hs, hm⟩
  exact hm (h s fun k (hk : n s ≤ k) ↦ show m ≤ k by omega)

/-- The *exactly* parse is vacuous when more than the demanded number may always be
solved. -/
theorem exact_parse_vacuous (s : S) : ¬ nec (Ici (n s)) (Comparison.eq.interval m) := fun h ↦ by
  have := h (n s + m + 1) (by simp only [mem_Ici]; omega)
  simp only [Comparison.interval_eq, mem_singleton_iff] at this
  omega

/-- The intermediate embedded implicature, the operator between *whenever* and *demanded*,
restricts the quantification to the situations whose minimum is the numeral. -/
theorem intermediate_parse_iff :
    (∀ s, exh (fun m ↦ nec (Ici (n s)) (Comparison.ge.interval m)) m → managed s) ↔
      ∀ s, n s = m → managed s := by
  simp only [nec_Ici_exh_iff]

end Intermediate

end Spector2013
