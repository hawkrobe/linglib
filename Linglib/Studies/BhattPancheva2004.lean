import Linglib.Data.Examples.BhattPancheva2004
import Linglib.Studies.Heim2001
import Linglib.Syntax.Minimalist.Movement.HeimKennedy
import Linglib.Syntax.Tree.Basic
import Linglib.Core.Order.Branching
import Linglib.Semantics.Quantification.Defs

/-!
# Bhatt and Pancheva (2004): Late Merger of Degree Clauses

This file formalizes [bhatt-pancheva-2004], the proposal that a degree clause, the *than*- or
*as*-phrase, is merged countercyclically as the complement of the degree head after the head has
raised to its scope position, so that the surface site of the clause marks the scope of the
comparison. The Heim–Kennedy constraint of [heim-2000] filters the LFs of degree movement, (24):
the reading (22b) it excludes has the universal quantifier between the DegP and its trace
(`hkc_22`), and without an *exactly*-differential or *less* the movement over *require* and
*allow* has no truth-conditional effect, (30), the monotone collapse of [heim-2000]. The
Extraposition-Scope Generalization, (39), refines [williams-1974]: the scope of the degree head
is at least as high as the site of its clause, by countercyclic merger, and exactly as high
(`at_least_as_high`, `exactly_as_high`); the reading of (43) with *-er* over the *before*-clause
puts the clause between the DegP and its trace (`hkc_43`), so (44), whose clause site puts the
DegP above the *before*-clause, is out. Merger at the scope position derives the Ellipsis-Scope
Generalization, (59), on the four LFs of (62), and the Condition C–Scope Generalization on the
LFs of (69): the pronoun c-commands the name in the degree clause exactly when the comparison
scopes below the matrix predicate (`conditionC_scope`). Section 7 derives late merger and its
"exactly as high" half from Trace Conversion and the nonconservativity of *-er*, (84): the
converted lower copy intersects the degree clause into the second argument, harmless for a
conservative quantifier, (82), but a contradiction for *-er*, (86) (`erSem_not_conservative`), so
the clause merges only at the DegP's ultimate scope position, (90).

## Implementation notes

* LFs are category-free trees at the paper's bracketing, `Syntax.Tree Unit String`, with
  non-branching and elided material written as one leaf; scope is `Branching.cCommandAt` and the
  constraint `Minimalist.IsHeimKennedy` on it.
* The comparative of (84) is `erSem`, proper inclusion of degree sets, and (85) is its value on
  [kennedy-1999]'s positive extents; Trace Conversion itself is not formalized, only the second
  argument it hands `-er`.
* Section 4.2 is [heim-2000]'s result and is `Heim2001.forall_collapse`; the ordering constraint
  between *than*- and result clauses, (48) and (50), and the ellipsis resolution of Section 6.3
  are recorded as rows.

## References

* [bhatt-pancheva-2004]
* [heim-2000]
* [williams-1974]
* [lebeaux-1988]
* [kennedy-1999]
-/

namespace BhattPancheva2004

open Core.Order Core.Order.Branching Data.Examples Degree Minimalist Set Syntax Syntax.Tree

/-! ### The Heim–Kennedy constraint (Section 4.1) -/

/-- The LF (22a) of *every girl is exactly 1 inch taller than that*, the quantifier over the
DegP: `[every girl [λx [[DegP exactly 1 inch -er than that] [λd [x is d-tall]]]]]`. -/
def lf22a : Tree Unit String :=
  bin (leaf "every girl") (binder 1 (bin (bin (leaf "exactly 1 inch -er") (leaf "than that"))
    (binder 2 (bin (leaf "x is") (bin (tr 2) (leaf "tall"))))))

/-- The LF (22b), the DegP over the quantifier:
`[[DegP exactly 1 inch -er than that] [λd [every girl [λx [x is d-tall]]]]]`. -/
def lf22b : Tree Unit String :=
  bin (bin (leaf "exactly 1 inch -er") (leaf "than that"))
    (binder 2 (bin (leaf "every girl") (binder 1 (bin (leaf "x is") (bin (tr 2) (leaf "tall"))))))

/-- (24) admits (22a) and excludes (22b), where the quantifier's scope contains the degree trace
but not the DegP, the configuration (25). -/
theorem hkc_22 :
    IsHeimKennedy (cCommandAt lf22a) ⟨[0]⟩ ⟨[1, 0, 0]⟩ ⟨[1, 0, 1, 0, 1, 0]⟩ ∧
      ¬ IsHeimKennedy (cCommandAt lf22b) ⟨[1, 0, 0]⟩ ⟨[0]⟩ ⟨[1, 0, 1, 0, 1, 0]⟩ := by
  constructor <;> decide

/-! ### The Extraposition-Scope Generalization (Section 5.2) -/

/-- The LF (43a) of *Mary climbed higher than 1,000 feet before you did*, the *before*-clause over
the DegP: `[[Mary [[climbed [t high]] [DegP -er than 1,000 feet]]] [before you did]]`. -/
def lf43a : Tree Unit String :=
  bin (bin (leaf "Mary") (bin (bin (leaf "climbed") (bin (tr 1) (leaf "high")))
    (bin (leaf "-er") (leaf "than 1,000 feet")))) (leaf "before you did")

/-- The LF (43b), the DegP over the *before*-clause:
`[[[Mary [climbed [t high]]] [before you did]] [DegP -er than 1,000 feet]]`. -/
def lf43b : Tree Unit String :=
  bin (bin (bin (leaf "Mary") (bin (leaf "climbed") (bin (tr 1) (leaf "high"))))
    (leaf "before you did")) (bin (leaf "-er") (leaf "than 1,000 feet"))

/-- (43) has the reading with the *before*-clause over the comparison and not the reading with the
comparison over the *before*-clause, in which the *before*-clause's scope contains the degree
trace but not the DegP; (44), whose clause is merged above the *before*-clause, has only the LF
(43b). -/
theorem hkc_43 :
    IsHeimKennedy (cCommandAt lf43a) ⟨[1]⟩ ⟨[0, 1, 1]⟩ ⟨[0, 1, 0, 1, 0]⟩ ∧
      ¬ IsHeimKennedy (cCommandAt lf43b) ⟨[0, 1]⟩ ⟨[1]⟩ ⟨[0, 0, 1, 1, 0]⟩ := by
  constructor <;> decide

/-- The site of an extraposed clause relative to the operator the comparison may scope over. -/
inductive Site
  | low
  | high
  deriving DecidableEq, Repr

/-- An extraposition datum: the clause's site, whether its associate is the bare DegP rather than a
comparative DP, and whether the comparison's narrow and wide scope readings are available. -/
structure Row where
  site : Site
  degP : Bool
  narrow : Bool
  wide : Bool
  deriving DecidableEq, Repr

/-- A row from the paper's features. -/
def Row.ofExample (e : LinguisticExample) : Option Row := do
  let site ← match e.feature? "site" with
    | some "low" => some Site.low
    | some "high" => some Site.high
    | _ => none
  let mover ← e.feature? "mover"
  let narrow ← e.feature? "narrow_scope"
  let wide ← e.feature? "wide_scope"
  some ⟨site, mover = "DegP", narrow = "available", wide = "available"⟩

/-- The extraposition data of Section 5.2, (41) to (46) and (53) to (54). -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- (38), the half of (39) countercyclic merger derives: a clause merged above an operator leaves
the comparison no scope below it, (42), (44), (46), (53b) and (54b). -/
theorem at_least_as_high : ∀ r ∈ rows, r.site = .high → r.narrow = false := by decide

/-- The other half of (39): a bare DegP whose clause is merged below an operator has no scope
above it, (43), (53a) and (54a), whereas a comparative DP raises with its clause, (41) and
(45). -/
theorem exactly_as_high :
    (∀ r ∈ rows, r.degP = true → r.site = .low → r.wide = false) ∧
      ∀ r ∈ rows, r.degP = false → r.site = .low → r.wide = true := by
  decide

/-! ### Ellipsis and Condition C mark the scope of the comparison (Section 6) -/

/-- An LF of *her father tells her to work harder than Mary's boss does*, (62) and (69): the tree
and the positions of the DegP, the degree clause, the pronoun, the matrix predicate and the
matrix and embedded VPs. -/
structure TellLF where
  tree : Tree Unit String
  degP : TreePath
  clause : TreePath
  pronoun : TreePath
  tells : TreePath
  matrixVP : TreePath
  embeddedVP : TreePath

/-- The clause merged low, at the embedded clause, (69a):
`[her father [tells [her [[λd PRO to work d-hard] [-er than Mary's boss does]]]]]`. -/
def low : TellLF where
  tree := bin (leaf "her father") (bin (leaf "tells") (bin (leaf "her")
    (bin (binder 1 (bin (leaf "PRO to work") (bin (tr 1) (leaf "hard"))))
      (bin (leaf "-er") (leaf "than Mary's boss does")))))
  degP := ⟨[1, 1, 1, 1]⟩
  clause := ⟨[1, 1, 1, 1, 1]⟩
  pronoun := ⟨[1, 1, 0]⟩
  tells := ⟨[1, 0]⟩
  matrixVP := ⟨[1]⟩
  embeddedVP := ⟨[1, 1, 1, 0, 0]⟩

/-- The clause merged high, at the matrix clause, (69c):
`[[λd her father tells her to work d-hard] [-er than Mary's boss does]]`. -/
def high : TellLF where
  tree := bin (binder 1 (bin (leaf "her father") (bin (leaf "tells") (bin (leaf "her")
    (bin (leaf "PRO to work") (bin (tr 1) (leaf "hard")))))))
    (bin (leaf "-er") (leaf "than Mary's boss does"))
  degP := ⟨[1]⟩
  clause := ⟨[1, 1]⟩
  pronoun := ⟨[0, 0, 1, 1, 0]⟩
  tells := ⟨[0, 0, 1, 0]⟩
  matrixVP := ⟨[0, 0, 1]⟩
  embeddedVP := ⟨[0, 0, 1, 1, 1]⟩

/-- The Ellipsis-Scope Generalization, (59), on the LFs of (62): the scope of the DegP contains
the embedded VP at either site and the matrix VP only at the high site, so the reading (62b),
the clause merged low with the matrix VP elided, is the one missing. -/
theorem ellipsisScope :
    (∀ lf ∈ [low, high], (lf.degP, lf.embeddedVP) ∈ cCommandAt lf.tree) ∧
      (low.degP, low.matrixVP) ∉ cCommandAt low.tree ∧
      (high.degP, high.matrixVP) ∈ cCommandAt high.tree := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The Condition C–Scope Generalization, (69) and (70): the pronoun c-commands the name in the
degree clause exactly when the comparison does not scope over the matrix predicate. -/
theorem conditionC_scope :
    ∀ lf ∈ [low, high],
      (lf.pronoun, lf.clause) ∈ cCommandAt lf.tree ↔ (lf.degP, lf.tells) ∉ cCommandAt lf.tree := by
  decide

/-! ### Nonconservativity forces late merger (Section 7) -/

variable {Entity D : Type*}

/-- The comparative degree quantifier, (84): its first argument, the degree clause, is a proper
subset of its second. -/
def erSem (A B : Set D) : Prop := A ⊂ B

/-- (85): on [kennedy-1999]'s positive extents `-er` compares the measures. -/
theorem erSem_Iic_iff [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    erSem (Iic (μ b)) (Iic (μ a)) ↔ comparativeSem μ a b .positive :=
  (comparative_iff_Iic_ssubset μ a b).symm

/-- (86) and (87): Trace Conversion of an early-merged degree clause intersects it into the second
argument, and `A ⊂ A ∩ B` is a contradiction. -/
theorem erSem_inter_contradictory (A B : Set D) : ¬ erSem A (A ∩ B) :=
  λ h => h.not_subset inter_subset_left

/-- (82) against (86): a conservative quantifier is unaffected by the intersection, and `-er` is
not conservative. -/
theorem erSem_not_conservative [Nonempty D] : ¬ Quantification.Conservative (erSem (D := D)) :=
  λ h => erSem_inter_contradictory ∅ univ ((h (∅ : Set D) univ).1 (empty_ssubset.2 univ_nonempty))

end BhattPancheva2004
