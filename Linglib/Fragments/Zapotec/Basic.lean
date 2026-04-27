import Linglib.Theories.Interfaces.SyntaxSemantics.Minimalist.PhiSemantics

/-!
# Santiago Laxopa Zapotec (Otomanguean) — Pronoun Fragment
@cite{toosarvandani-2023}

Six-individual domain modeling the 4-way animacy system of Santiago Laxopa
Zapotec: elder / non-elder human / animal / inanimate. This instantiates
`Minimalist.PhiSemantics.PhiDomain` and derives the full pronoun inventory from
Table 1 of @cite{toosarvandani-2023}.
-/

namespace Fragments.Zapotec

open Minimalist.PhiSemantics

-- ============================================================================
-- § 1: Individual Domain
-- ============================================================================

/-- Six representative individuals spanning the animacy hierarchy.
    - `i` = speaker, `u` = addressee (SAPs, inherently human)
    - `e` = elder (human, senior kinship)
    - `h` = non-elder human
    - `a` = animal
    - `o` = inanimate object -/
inductive ZapInd where
  | i | u | e | h | a | o
  deriving DecidableEq, Repr

instance : Fintype ZapInd where
  elems := {.i, .u, .e, .h, .a, .o}
  complete := by intro x; cases x <;> simp

-- ============================================================================
-- § 2: PhiDomain Instance
-- ============================================================================

/-- Santiago Laxopa Zapotec domain with 4-way animacy. -/
def zapotecDomain : PhiDomain where
  Ind := ZapInd
  speaker := .i
  addressee := .u
  isElder := fun | .e => true | _ => false
  isHuman := fun | .i | .u | .e | .h => true | _ => false
  isAnimate := fun | .i | .u | .e | .h | .a => true | _ => false
  elder_human := by intro x; cases x <;> simp
  human_animate := by intro x; cases x <;> simp
  speaker_human := by rfl
  addressee_human := by rfl
  speaker_ne := by intro h; cases h

-- ============================================================================
-- § 3: Abbreviations
-- ============================================================================

/-- Abbreviation for the Zapotec domain. -/
abbrev zd := zapotecDomain

end Fragments.Zapotec
