/-
# Minimalist Clause Structure

Basic phrase structure and linearization for the Minimalist Program.

## Main definitions

- `Position`, `dominates`, `structurallyPrecedes`
- `HeadPosition`, `TPosition`, `tPronouncedAt`

## References

- Chomsky, N. (1995). "The Minimalist Program"
-/

import Linglib.Core.Word

namespace Minimalism

/-- Positions in the clause structure -/
inductive Position where
  | specCP
  | headC
  | specTP
  | headT
  | specvP
  | headv
  | headV
  deriving Repr, DecidableEq
def dominates : Position → Position → Bool
  | .specCP, p => p != .specCP
  | .headC, p => p != .specCP && p != .headC
  | .specTP, p => p == .specvP || p == .headv || p == .headV
  | .headT, p => p == .specvP || p == .headv || p == .headV
  | .specvP, p => p == .headv || p == .headV
  | .headv, .headV => true
  | _, _ => false

/-- Structural precedence in English (Spec-Head-Complement order) -/
def structurallyPrecedes : Position → Position → Bool
  | .specCP, .headC => true
  | .specCP, .specTP => true
  | .specCP, .headT => true
  | .specCP, .specvP => true
  | .specCP, .headv => true
  | .specCP, .headV => true
  | .headC, .specTP => true
  | .headC, .headT => true
  | .headC, .specvP => true
  | .headC, .headv => true
  | .headC, .headV => true
  | .specTP, .headT => true
  | .specTP, .specvP => true
  | .specTP, .headv => true
  | .specTP, .headV => true
  | .headT, .specvP => true
  | .headT, .headv => true
  | .headT, .headV => true
  | .specvP, .headv => true
  | .specvP, .headV => true
  | .headv, .headV => true
  | _, _ => false
theorem subject_precedes_t_base : structurallyPrecedes .specTP .headT = true := rfl
theorem c_precedes_subject : structurallyPrecedes .headC .specTP = true := rfl
theorem c_precedes_t : structurallyPrecedes .headC .headT = true := rfl
theorem spec_cp_is_first :
    structurallyPrecedes .specCP .headC = true ∧
    structurallyPrecedes .specCP .specTP = true ∧
    structurallyPrecedes .specCP .headT = true := ⟨rfl, rfl, rfl⟩
inductive HeadPosition where
  | base : Position → HeadPosition
  | movedTo : Position → HeadPosition
  deriving Repr, DecidableEq

inductive TPosition where
  | inT
  | inC
  deriving Repr, DecidableEq
def tPronouncedAt (tPos : TPosition) : Position :=
  match tPos with
  | .inT => .headT
  | .inC => .headC

theorem t_to_c_precedes_subject : structurallyPrecedes (tPronouncedAt .inC) .specTP = true := rfl
theorem subject_precedes_t_no_movement : structurallyPrecedes .specTP (tPronouncedAt .inT) = true := rfl
theorem t_to_c_reverses_order :
    structurallyPrecedes .specTP .headT = true ∧
    structurallyPrecedes .headC .specTP = true := ⟨rfl, rfl⟩

def tPrecedesSubject (tPos : TPosition) : Bool :=
  structurallyPrecedes (tPronouncedAt tPos) .specTP
def subjectPrecedesT (tPos : TPosition) : Bool :=
  structurallyPrecedes .specTP (tPronouncedAt tPos)

theorem t_to_c_gives_t_first : tPrecedesSubject .inC = true := rfl
theorem no_movement_gives_subj_first : subjectPrecedesT .inT = true := rfl

end Minimalism
