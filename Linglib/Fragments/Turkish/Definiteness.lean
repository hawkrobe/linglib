import Linglib.Fragments.Turkish.Case

/-!
# Turkish Definiteness and Specificity
@cite{goksel-kerslake-2005}

Turkish lacks definite and indefinite articles. Instead, definiteness and
specificity are marked by **accusative case** and **word order**
(@cite{goksel-kerslake-2005} Ch 14, 22).

## The ACC/bare alternation

| Form | Marking | Interpretation |
|------|---------|---------------|
| ACC-marked: *kitab-ı okudum* | -(y)I | definite or specific indefinite |
| Bare: *kitap okudum* | zero | nonspecific indefinite |

## Positional constraints

Bare (nonspecific) objects must appear **immediately preverbal**; they form
a tight prosodic and syntactic unit with the verb (pseudo-incorporation).
ACC-marked objects can appear in any preverbal position (scramble freely).

## Connection to differential object marking

This is a canonical instance of **differential object marking** (DOM):
definite/specific objects receive overt case, nonspecific ones do not.
The Turkish pattern is often cited in @cite{aissen-2003} as a paradigm
case of specificity-driven DOM.
-/

namespace Fragments.Turkish.Definiteness

/-- Object marking types in Turkish. -/
inductive ObjectMarking where
  | accusative    -- -(y)I: definite or specific indefinite
  | bare          -- zero: nonspecific indefinite
  deriving DecidableEq, Repr

/-- Referential properties of Turkish direct objects. -/
inductive Specificity where
  | definite
  | specificIndef
  | nonspecificIndef
  deriving DecidableEq, Repr

/-- Which specificities are compatible with each marking type? -/
def compatible : ObjectMarking → Specificity → Bool
  | .accusative, .definite        => true
  | .accusative, .specificIndef   => true
  | .accusative, .nonspecificIndef => false
  | .bare,       .definite        => false
  | .bare,       .specificIndef   => false
  | .bare,       .nonspecificIndef => true

/-- Must this object type appear immediately preverbal? -/
def mustBePreverbal : ObjectMarking → Bool
  | .bare => true
  | .accusative => false

-- ============================================================================
-- § Verification
-- ============================================================================

/-- ACC required for definite objects. -/
theorem definite_requires_acc :
    compatible .bare .definite = false ∧
    compatible .accusative .definite = true := ⟨rfl, rfl⟩

/-- Bare objects are always nonspecific. -/
theorem bare_is_nonspecific :
    compatible .bare .nonspecificIndef = true ∧
    compatible .bare .specificIndef = false ∧
    compatible .bare .definite = false := ⟨rfl, rfl, rfl⟩

/-- ACC covers both definite and specific indefinite. -/
theorem acc_covers_specific :
    compatible .accusative .definite = true ∧
    compatible .accusative .specificIndef = true := ⟨rfl, rfl⟩

/-- ACC does not cover nonspecific indefinites (DOM gap). -/
theorem acc_excludes_nonspecific :
    compatible .accusative .nonspecificIndef = false := rfl

/-- Bare objects must be preverbal; ACC objects are positionally free. -/
theorem bare_preverbal : mustBePreverbal .bare = true := rfl
theorem acc_free : mustBePreverbal .accusative = false := rfl

/-- The accusative case is in the Turkish case inventory. -/
theorem acc_in_inventory :
    .acc ∈ Fragments.Turkish.Case.caseInventory := by decide

end Fragments.Turkish.Definiteness
