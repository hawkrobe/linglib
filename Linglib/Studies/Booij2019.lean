/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.Construction.Schema
import Linglib.Morphology.Morphotactics.CVTemplate
import Linglib.Core.Order.Flat
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Booij (2019): The role of schemas in Construction Morphology

This file formalizes [booij-2019]'s templatic and second-order schemas as coindexed schemas
read through subscriptings of template slots. A templatic schema is a description over root
consonants and vowel constants, and a consonant that occupies two slots, the gemination of the
Damascus Arabic occupation template `C₁aC₂C₂aaC₃` of (2), is a subscripting that is not
injective: an item instantiates the schema exactly when its vowels are the template's and the
two geminate slots are filled alike (`occupation_instantiatesAt_iff`). The subscripting is the
association of the autosegmental template: the slots it coindexes are the slots associated
to one melody element (`occupationSub_eq_iff_assoc_eq`), and the association spells out the
word (`xabbaazMatch_spellout`).

Second-order schemas relate two templates over one root. Javanese partial reduplication (13)
copies the initial consonant into the reduplicant, so the reduplicant repeats one variable and
shares it with the base (`reduplication_pairs_iff`); the Egyptian Arabic comparative (16) pairs
an adjective with the comparative template over the same three consonants
(`comparative_pairs_iff`), so *kibiir* pairs with *akbar* and not with *atxan*.

## Implementation notes

* Slots are `Fin n` positions and items are slot-indexed segments on a flat carrier. A variable
  standing for a sequence of sounds, the paper's `y`, is one slot valued in the residue.
* The higher-order schema for Dutch *-er* and the affixoid discussion are not formalized.

## References

* [booij-2019]
* [mccarthy-1981]
-/

namespace Booij2019

open Morphology Morphology.Construction

/-! ### The occupation template `C₁aC₂C₂aaC₃` -/

/-- The Arabic segments cited: the consonants of (1) and (15) and the vowels. -/
inductive ArSeg
  | x | b | z | d | m | w | s | k | r | t | n
  | a | aa | i | ii
  deriving DecidableEq

/-- The parts of the occupation template (2): three root consonants and two vowel constants. -/
inductive OccPart
  | c1 | c2 | c3 | a | aa
  deriving DecidableEq

/-- The occupation schema (2): the vowels pinned, the root consonants open. -/
def occupation : Schema OccPart (Flat ArSeg) :=
  ⟨λ | .a => ↑ArSeg.a | .aa => ↑ArSeg.aa | _ => ⊥, {.c1, .c2, .c3}⟩

/-- The six slots of `C₁aC₂C₂aaC₃` subscripted by parts: the second consonant occupies
two. -/
def occupationSub : Fin 6 → OccPart := ![.c1, .a, .c2, .c2, .aa, .c3]

/-- The occupation nouns (1). -/
def xabbaaz : Fin 6 → Flat ArSeg :=
  ![↑ArSeg.x, ↑ArSeg.a, ↑ArSeg.b, ↑ArSeg.b, ↑ArSeg.aa, ↑ArSeg.z]
def xaddaam : Fin 6 → Flat ArSeg :=
  ![↑ArSeg.x, ↑ArSeg.a, ↑ArSeg.d, ↑ArSeg.d, ↑ArSeg.aa, ↑ArSeg.m]
def bawwaab : Fin 6 → Flat ArSeg :=
  ![↑ArSeg.b, ↑ArSeg.a, ↑ArSeg.w, ↑ArSeg.w, ↑ArSeg.aa, ↑ArSeg.b]
def sammaak : Fin 6 → Flat ArSeg :=
  ![↑ArSeg.s, ↑ArSeg.a, ↑ArSeg.m, ↑ArSeg.m, ↑ArSeg.aa, ↑ArSeg.k]

/-- An item instantiates the occupation schema exactly when its vowels are the template's and
the two slots of the second consonant are filled alike: gemination is a subscripting that is
not injective. -/
theorem occupation_instantiatesAt_iff {w : Fin 6 → Flat ArSeg} :
    occupation.InstantiatesAt occupationSub w ↔
      w 1 = ↑ArSeg.a ∧ w 4 = ↑ArSeg.aa ∧ w 2 = w 3 := by
  rw [Schema.instantiatesAt_iff]
  constructor
  · rintro ⟨hc, hf⟩
    exact ⟨Flat.coe_le_iff.1 (hc 1), Flat.coe_le_iff.1 (hc 4), hf (by decide)⟩
  · rintro ⟨h1, h4, h23⟩
    refine ⟨λ i => ?_, λ i j hij => ?_⟩
    · fin_cases i <;> first | exact bot_le | exact h1.ge | exact h4.ge
    · fin_cases i <;> fin_cases j <;>
        first | rfl | exact h23 | exact h23.symm | exact absurd hij (by decide)

/-- The nouns of (1) instantiate the template. -/
theorem occupation_nouns :
    occupation.InstantiatesAt occupationSub xabbaaz ∧
      occupation.InstantiatesAt occupationSub xaddaam ∧
        occupation.InstantiatesAt occupationSub bawwaab ∧
          occupation.InstantiatesAt occupationSub sammaak := by
  simp only [occupation_instantiatesAt_iff]
  decide

/-- A form with distinct medial consonants matches the vowels but not the gemination. -/
theorem not_occupation_of_ne_medial :
    ¬ occupation.InstantiatesAt occupationSub
      ![↑ArSeg.x, ↑ArSeg.a, ↑ArSeg.b, ↑ArSeg.d, ↑ArSeg.aa, ↑ArSeg.z] := by
  rw [occupation_instantiatesAt_iff]
  decide

/-! ### The subscripting as autosegmental association -/

/-- The template of (2) as a CV skeleton. -/
def occupationTemplate : CVTemplate := ⟨[.C, .V, .C, .C, .V, .C]⟩

/-- *xabbaaz* as the association of the root /x b z/ and the vocalism /a aa/ to the template:
the second root consonant is associated to two slots. -/
def xabbaazMatch : TemplateMatch ArSeg where
  root := ⟨[.x, .b, .z]⟩
  vocalism := [.a, .aa]
  template := occupationTemplate
  associations :=
    [⟨.root, 0, 0⟩, ⟨.vocalism, 0, 1⟩, ⟨.root, 1, 2⟩, ⟨.root, 1, 3⟩,
      ⟨.vocalism, 1, 4⟩, ⟨.root, 2, 5⟩]

/-- The melody element a slot is associated to. -/
def xabbaazAssoc (i : Fin 6) : Option (AssocSource × Nat) :=
  (xabbaazMatch.associations.find? (·.slotIndex == i.val)).map λ a => (a.source, a.melodyIndex)

/-- The association lines spell out *xabbaaz*. -/
theorem xabbaazMatch_spellout :
    xabbaazMatch.spellout.map ((↑) : ArSeg → Flat ArSeg) = List.ofFn xabbaaz := by
  decide

/-- The subscripting and the association agree: two slots carry the same part exactly when
they are associated to the same melody element. -/
theorem occupationSub_eq_iff_assoc_eq (i j : Fin 6) :
    occupationSub i = occupationSub j ↔ xabbaazAssoc i = xabbaazAssoc j := by
  fin_cases i <;> fin_cases j <;> decide

/-! ### Javanese partial reduplication -/

/-- The pieces of the Javanese words (12): the initial consonants, the schwa, and the residues
the paper's variable `y` stands for. -/
inductive JvPiece
  | t | j | g | schwa | amu | awah | eni
  deriving DecidableEq

/-- The parts of the reduplication schema (13): the copied consonant, the schwa constant, and
the residue. -/
inductive RedPart
  | c1 | schwa | y
  deriving DecidableEq

/-- The reduplication schema (13): the schwa pinned, the consonant and the residue open. -/
def reduplication : Schema RedPart (Flat JvPiece) :=
  ⟨λ | .schwa => ↑JvPiece.schwa | _ => ⊥, {.c1, .y}⟩

/-- The reduplicant `C₁əC₁y`: the initial consonant occupies two slots. -/
def redSub : Fin 4 → RedPart := ![.c1, .schwa, .c1, .y]

/-- The base `C₁y`. -/
def baseSub : Fin 2 → RedPart := ![.c1, .y]

/-- A reduplicant and a base are a paired instantiation of (13) exactly when the reduplicant
has the schwa, copies its initial consonant, and shares consonant and residue with the base. -/
theorem reduplication_pairs_iff {r : Fin 4 → Flat JvPiece} {b : Fin 2 → Flat JvPiece} :
    reduplication.InstantiatesAt (Sum.elim redSub baseSub) (Sum.elim r b) ↔
      r 1 = ↑JvPiece.schwa ∧ r 0 = r 2 ∧ r 0 = b 0 ∧ r 3 = b 1 := by
  rw [Schema.instantiatesAt_elim_iff]
  constructor
  · rintro ⟨hr, -, hf, -, h⟩
    exact ⟨Flat.coe_le_iff.1 (hr 1), hf (by decide), h 0 0 (by decide), h 3 1 (by decide)⟩
  · rintro ⟨h1, h02, h0, h3⟩
    refine ⟨λ i => ?_, λ i => ?_, λ i j hij => ?_, λ i j hij => ?_, λ i j hij => ?_⟩
    · fin_cases i <;> first | exact bot_le | exact h1.ge
    · fin_cases i <;> exact bot_le
    · fin_cases i <;> fin_cases j <;>
        first | rfl | exact h02 | exact h02.symm | exact absurd hij (by decide)
    · fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)
    · fin_cases i <;> fin_cases j <;>
        first | exact h0 | exact h02.symm.trans h0 | exact h3 | exact absurd hij (by decide)

/-- The verbs of (12) with their bases. -/
theorem reduplication_verbs :
    reduplication.InstantiatesAt (Sum.elim redSub baseSub)
        (Sum.elim ![↑JvPiece.t, ↑JvPiece.schwa, ↑JvPiece.t, ↑JvPiece.amu]
          ![↑JvPiece.t, ↑JvPiece.amu]) ∧
      reduplication.InstantiatesAt (Sum.elim redSub baseSub)
        (Sum.elim ![↑JvPiece.j, ↑JvPiece.schwa, ↑JvPiece.j, ↑JvPiece.awah]
          ![↑JvPiece.j, ↑JvPiece.awah]) ∧
      reduplication.InstantiatesAt (Sum.elim redSub baseSub)
        (Sum.elim ![↑JvPiece.g, ↑JvPiece.schwa, ↑JvPiece.g, ↑JvPiece.eni]
          ![↑JvPiece.g, ↑JvPiece.eni]) := by
  simp only [reduplication_pairs_iff]
  decide

/-! ### The Egyptian Arabic comparative -/

/-- The parts of the comparative schema (16): three root consonants, the adjective's two open
vowels, and the comparative's constant `a`. -/
inductive CmpPart
  | c1 | c2 | c3 | v1 | v2 | a
  deriving DecidableEq

/-- The comparative schema (16): the comparative vowel pinned, all else open. -/
def comparative : Schema CmpPart (Flat ArSeg) :=
  ⟨λ | .a => ↑ArSeg.a | _ => ⊥, {.c1, .c2, .c3, .v1, .v2}⟩

/-- The adjective template `C₁VC₂VC₃`. -/
def adjSub : Fin 5 → CmpPart := ![.c1, .v1, .c2, .v2, .c3]

/-- The comparative template `aC₁C₂aC₃`. -/
def cmpSub : Fin 5 → CmpPart := ![.a, .c1, .c2, .a, .c3]

/-- An adjective and a comparative are a paired instantiation of (16) exactly when the
comparative has its vowels and the two share their three consonants. -/
theorem comparative_pairs_iff {p q : Fin 5 → Flat ArSeg} :
    comparative.InstantiatesAt (Sum.elim adjSub cmpSub) (Sum.elim p q) ↔
      q 0 = ↑ArSeg.a ∧ q 3 = ↑ArSeg.a ∧ p 0 = q 1 ∧ p 2 = q 2 ∧ p 4 = q 4 := by
  rw [Schema.instantiatesAt_elim_iff]
  constructor
  · rintro ⟨-, hq, -, -, h⟩
    exact ⟨Flat.coe_le_iff.1 (hq 0), Flat.coe_le_iff.1 (hq 3), h 0 1 (by decide),
      h 2 2 (by decide), h 4 4 (by decide)⟩
  · rintro ⟨h0, h3, h01, h22, h44⟩
    refine ⟨λ i => ?_, λ i => ?_, λ i j hij => ?_, λ i j hij => ?_, λ i j hij => ?_⟩
    · fin_cases i <;> exact bot_le
    · fin_cases i <;> first | exact bot_le | exact h0.ge | exact h3.ge
    · fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)
    · fin_cases i <;> fin_cases j <;>
        first | rfl | exact h0.trans h3.symm | exact h3.trans h0.symm | exact absurd hij (by decide)
    · fin_cases i <;> fin_cases j <;>
        first | exact h01 | exact h22 | exact h44 | exact absurd hij (by decide)

/-- The pairs of (15). -/
def kibiir : Fin 5 → Flat ArSeg := ![↑ArSeg.k, ↑ArSeg.i, ↑ArSeg.b, ↑ArSeg.ii, ↑ArSeg.r]
def akbar : Fin 5 → Flat ArSeg := ![↑ArSeg.a, ↑ArSeg.k, ↑ArSeg.b, ↑ArSeg.a, ↑ArSeg.r]
def tixiin : Fin 5 → Flat ArSeg := ![↑ArSeg.t, ↑ArSeg.i, ↑ArSeg.x, ↑ArSeg.ii, ↑ArSeg.n]
def atxan : Fin 5 → Flat ArSeg := ![↑ArSeg.a, ↑ArSeg.t, ↑ArSeg.x, ↑ArSeg.a, ↑ArSeg.n]

/-- *kibiir* pairs with *akbar* and *tixiin* with *atxan*, and *kibiir* not with *atxan*. -/
theorem comparative_pairs :
    comparative.InstantiatesAt (Sum.elim adjSub cmpSub) (Sum.elim kibiir akbar) ∧
      comparative.InstantiatesAt (Sum.elim adjSub cmpSub) (Sum.elim tixiin atxan) ∧
        ¬ comparative.InstantiatesAt (Sum.elim adjSub cmpSub) (Sum.elim kibiir atxan) := by
  simp only [comparative_pairs_iff]
  decide

end Booij2019
