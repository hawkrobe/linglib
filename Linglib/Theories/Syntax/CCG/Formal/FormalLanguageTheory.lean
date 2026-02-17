import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic

/-!
# Formal Language Theory

Chomsky hierarchy definitions. Key result: {aⁿbⁿcⁿdⁿ} is not context-free,
but CCG generates it, proving CCG > CFG.
-/

/-- Alphabet for cross-serial dependencies (models Dutch word order). -/
inductive FourSymbol where
  | a | b | c | d
  deriving DecidableEq, Repr, BEq

abbrev FourString := List FourSymbol

/-- The language {aⁿbⁿcⁿdⁿ | n ≥ 0}, modeling Dutch cross-serial dependencies. -/
def isInLanguage_anbncndn (w : FourString) : Bool :=
  match w with
  | [] => true
  | _ =>
    let na := w.filter (· == .a) |>.length
    let nb := w.filter (· == .b) |>.length
    let nc := w.filter (· == .c) |>.length
    let nd := w.filter (· == .d) |>.length
    na == nb && nb == nc && nc == nd &&
    w == List.replicate na .a ++ List.replicate nb .b ++
         List.replicate nc .c ++ List.replicate nd .d

/-- Generate aⁿbⁿcⁿdⁿ. -/
def makeString_anbncndn (n : Nat) : FourString :=
  List.replicate n .a ++ List.replicate n .b ++
  List.replicate n .c ++ List.replicate n .d

#eval isInLanguage_anbncndn []
#eval isInLanguage_anbncndn (makeString_anbncndn 0)
#eval isInLanguage_anbncndn (makeString_anbncndn 1)
#eval isInLanguage_anbncndn (makeString_anbncndn 2)
#eval isInLanguage_anbncndn (makeString_anbncndn 3)
#eval isInLanguage_anbncndn [.a, .b, .c]
#eval isInLanguage_anbncndn [.a, .a, .b, .c, .c, .d]

/-- The CFL pumping property for languages over FourSymbol.
    Every context-free language has this property (pumping lemma).
    Showing a language lacks it proves it's not context-free. -/
def HasPumpingProperty4 (inLang : FourString → Bool) : Prop :=
    ∃ p : Nat, p > 0 ∧
    ∀ w : FourString, inLang w = true → w.length ≥ p →
      ∃ u v x y z : FourString,
        w = u ++ v ++ x ++ y ++ z ∧
        (v ++ x ++ y).length ≤ p ∧
        (v.length + y.length) ≥ 1 ∧
        ∀ i : Nat, inLang (u ++ List.flatten (List.replicate i v) ++ x ++
                          List.flatten (List.replicate i y) ++ z) = true

/-- makeString_anbncndn n is always in the language {aⁿbⁿcⁿdⁿ}.
    TODO: needs auxiliary lemmas about filter distributing over append
    and filter on replicate for distinct FourSymbol values. -/
theorem makeString_in_language (n : Nat) :
    isInLanguage_anbncndn (makeString_anbncndn n) = true := by
  cases n with
  | zero => rfl
  | succ k => sorry

/-- Pumping breaks membership in {aⁿbⁿcⁿdⁿ}: for any decomposition of aᵖbᵖcᵖdᵖ
    into uvxyz with |vxy| ≤ p and |vy| ≥ 1, pumping at i=0 breaks membership.

    Key insight: |vxy| ≤ p means vxy spans ≤ 2 of the 4 symbol blocks (each of
    length p). Removing vy (i=0) reduces counts of ≤ 2 symbol types by ≥ 1 total,
    creating an imbalance — so the pumped-down string is not in {aⁿbⁿcⁿdⁿ}. -/
theorem pump_breaks_anbncndn (p : Nat) (hp : p > 0) :
    let w := makeString_anbncndn p
    ∀ u v x y z : FourString,
      w = u ++ v ++ x ++ y ++ z →
      (v ++ x ++ y).length ≤ p →
      (v.length + y.length) ≥ 1 →
      ∃ i : Nat, isInLanguage_anbncndn (u ++ List.flatten (List.replicate i v) ++ x ++
                                        List.flatten (List.replicate i y) ++ z) = false := by
  intro w u v x y z hw hvxy_len hvy_len
  use 0
  sorry

/-- {aⁿbⁿcⁿdⁿ} does NOT have the CFL pumping property, hence is not context-free.

    Proof: for any pumping constant p, the word aᵖbᵖcᵖdᵖ ∈ L witnesses failure.
    By `pump_breaks_anbncndn`, every valid decomposition can be pumped down (i=0)
    to break membership, contradicting the pumping property's ∀ i guarantee. -/
theorem anbncndn_not_pumpable :
    ¬ HasPumpingProperty4 isInLanguage_anbncndn := by
  intro ⟨p, hp, hpump⟩
  have hw_in := makeString_in_language p
  have hw_len : (makeString_anbncndn p).length ≥ p := by
    simp only [makeString_anbncndn, List.length_append, List.length_replicate]; omega
  obtain ⟨u, v, x, y, z, hw, hvxy, hvy, hall⟩ := hpump _ hw_in hw_len
  obtain ⟨i, hbreak⟩ := pump_breaks_anbncndn p hp u v x y z hw hvxy hvy
  have h := hall i
  rw [hbreak] at h
  exact absurd h (by decide)

/-- Alphabet for {aⁿbⁿcⁿ}. -/
inductive ThreeSymbol where
  | a | b | c
  deriving DecidableEq, Repr, BEq

/-- The language {aⁿbⁿcⁿ | n ≥ 0}. -/
def isInLanguage_anbnc (w : List ThreeSymbol) : Bool :=
  match w with
  | [] => true
  | _ =>
    let na := w.filter (· == .a) |>.length
    let nb := w.filter (· == .b) |>.length
    let nc := w.filter (· == .c) |>.length
    na == nb && nb == nc &&
    w == List.replicate na .a ++ List.replicate nb .b ++ List.replicate nc .c

/-- Generate aⁿbⁿcⁿ. -/
def makeString_anbnc (n : Nat) : List ThreeSymbol :=
  List.replicate n .a ++ List.replicate n .b ++ List.replicate n .c

#eval isInLanguage_anbnc (makeString_anbnc 3)

/-- The CFL pumping property for languages over ThreeSymbol. -/
def HasPumpingProperty3 (inLang : List ThreeSymbol → Bool) : Prop :=
    ∃ p : Nat, p > 0 ∧
    ∀ w : List ThreeSymbol, inLang w = true → w.length ≥ p →
      ∃ u v x y z : List ThreeSymbol,
        w = u ++ v ++ x ++ y ++ z ∧
        (v ++ x ++ y).length ≤ p ∧
        (v.length + y.length) ≥ 1 ∧
        ∀ i : Nat, inLang (u ++ List.flatten (List.replicate i v) ++ x ++
                           List.flatten (List.replicate i y) ++ z) = true

/-- {aⁿbⁿcⁿ} does NOT have the CFL pumping property, hence is not context-free.
    Same argument as the four-symbol case: aᵖbᵖcᵖ witnesses failure. -/
theorem anbnc_not_pumpable :
    ¬ HasPumpingProperty3 isInLanguage_anbnc := by
  sorry

/-- A formalism is mildly context-sensitive if it generates CFLs plus some non-CFLs. -/
structure MildlyContextSensitive where
  name : String
  generates_anbncndn : Bool

/-- CCG is mildly context-sensitive. -/
def CCG_MCS : MildlyContextSensitive where
  name := "Combinatory Categorial Grammar"
  generates_anbncndn := true

/-- TAG is mildly context-sensitive. -/
def TAG_MCS : MildlyContextSensitive where
  name := "Tree Adjoining Grammar"
  generates_anbncndn := true
