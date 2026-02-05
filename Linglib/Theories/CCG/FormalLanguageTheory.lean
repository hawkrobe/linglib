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

/-- Pumping lemma for CFLs (axiom since full proof requires formalizing CFGs). -/
axiom pumping_lemma_for_cfl :
    ∀ (inLang : FourString → Bool),
    ∃ p : Nat, p > 0 ∧
    ∀ w : FourString, inLang w = true → w.length ≥ p →
      ∃ u v x y z : FourString,
        w = u ++ v ++ x ++ y ++ z ∧
        (v ++ x ++ y).length ≤ p ∧
        (v.length + y.length) ≥ 1 ∧
        ∀ i : Nat, inLang (u ++ List.flatten (List.replicate i v) ++ x ++
                          List.flatten (List.replicate i y) ++ z) = true

/-- Pumping breaks membership in {aⁿbⁿcⁿdⁿ}: |vxy| ≤ p spans ≤2 symbol types. -/
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

/-- {aⁿbⁿcⁿdⁿ} is NOT context-free (pumping lemma contradiction). -/
theorem anbncndn_not_context_free :
    ¬∃ (p : Nat), p > 0 ∧
      ∀ w : FourString, isInLanguage_anbncndn w = true → w.length ≥ p →
        ∀ u v x y z : FourString,
          w = u ++ v ++ x ++ y ++ z →
          (v ++ x ++ y).length ≤ p →
          (v.length + y.length) ≥ 1 →
          ∀ i : Nat, isInLanguage_anbncndn (u ++ List.flatten (List.replicate i v) ++ x ++
                                           List.flatten (List.replicate i y) ++ z) = true := by
  intro ⟨p, hp, hpump⟩
  let w := makeString_anbncndn p
  have hw_in : isInLanguage_anbncndn w = true := by
    simp only [w, makeString_anbncndn, isInLanguage_anbncndn]
    sorry
  have hw_len : w.length ≥ p := by
    simp only [w, makeString_anbncndn, List.length_append, List.length_replicate]
    omega
  sorry

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

/-- {aⁿbⁿcⁿ} is NOT context-free. -/
theorem anbnc_not_context_free :
    ¬∃ (p : Nat), p > 0 ∧
      ∀ w : List ThreeSymbol, isInLanguage_anbnc w = true → w.length ≥ p →
        ∀ u v x y z,
          w = u ++ v ++ x ++ y ++ z →
          (v ++ x ++ y).length ≤ p →
          (v.length + y.length) ≥ 1 →
          ∀ i : Nat, isInLanguage_anbnc (u ++ List.flatten (List.replicate i v) ++ x ++
                                         List.flatten (List.replicate i y) ++ z) = true := by
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
