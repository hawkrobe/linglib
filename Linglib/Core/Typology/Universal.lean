import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# Implicational universals and 2×2 contingency tables

@cite{greenberg-1963} @cite{dryer-1992}

A Greenbergian implicational universal of the form "if a language is φ then
it is also ψ" is the claim that the *Type IV* cell of a 2×2 contingency
table (φ ∧ ¬ψ) is empty over the relevant language sample. This file gives
the minimal, sample-polymorphic API for stating, computing, and bridging
implicational universals to their tetrachoric form.

## Design

* `ImplicationalUniversal P Q s : Prop` — the universal claim "every `l ∈ s`
  with property `P` also has property `Q`" over a `Finset` sample.
* `ContingencyTable` — named-field 2×2 cell counts (`pp pn np nn : ℕ`),
  preferred over an opaque `Fin 4 → ℕ`.
* `Finset.contingency` — derive a `ContingencyTable` from a sample by
  counting elements that satisfy each combination of `P` and `Q`.
* `implicational_iff_no_typeIV` — the bridge: `ImplicationalUniversal P Q s`
  holds iff the table's Type IV cell (`pn`) is zero. The load-bearing
  theorem that keeps tetrachoric and propositional formulations in sync.

The language type is left abstract (`α`); concrete samples instantiate it
to the appropriate Fragment-derived profile type
(`Core.Typology.WordOrder.WordOrderProfile`, etc.).

## Decidability over literal samples

`decide` on `ImplicationalUniversal P Q {a, b, …}` routes through
`Finset.decidableBAll` → `Multiset` → `Quot.mk` and may exhaust kernel
recursion depth on samples larger than a handful. Two mathlib-blessed
fixes for consumers:

* `simp only [Finset.forall_mem_insert, Finset.forall_mem_empty] <;> decide`
  — structural decomposition into a conjunction of per-language goals.
* `set_option maxRecDepth N in theorem ...` — brute-force; mathlib uses
  this idiom for similar `Finset.decide` sites.
-/

universe u

variable {α : Type u}

namespace Core.Typology

/-- A 2×2 tetrachoric contingency table.

    Cells are named for whether the two predicates hold (`p`) or fail (`n`):

    | cell | row P | column Q |
    |------|-------|----------|
    | `pp` | true  | true     |
    | `pn` | true  | false    | (← Type IV: the gap an implicational universal forbids)
    | `np` | false | true     |
    | `nn` | false | false    |

    For an implication `P → Q`, the Type IV cell is `pn`: languages that
    have `P` but lack `Q` are the counterexamples. -/
structure ContingencyTable where
  /-- Both predicates hold. -/
  pp : ℕ
  /-- `P` holds, `Q` fails — the Type IV (counterexample) cell. -/
  pn : ℕ
  /-- `P` fails, `Q` holds. -/
  np : ℕ
  /-- Both predicates fail. -/
  nn : ℕ
  deriving Repr, DecidableEq

namespace ContingencyTable

/-- Total number of languages tabulated. -/
def total (t : ContingencyTable) : ℕ := t.pp + t.pn + t.np + t.nn

/-- Marginal count of languages with `P`. -/
def rowP (t : ContingencyTable) : ℕ := t.pp + t.pn

/-- Marginal count of languages with `Q`. -/
def colQ (t : ContingencyTable) : ℕ := t.pp + t.np

end ContingencyTable

/-- Greenbergian implicational universal: every language in sample `s` that
    satisfies `P` also satisfies `Q`. The "no Type IV gap" formulation,
    `(Finset.contingency s P Q).pn = 0`, is logically equivalent (see
    `implicational_iff_no_typeIV`). -/
def ImplicationalUniversal (P Q : α → Prop) (s : Finset α) : Prop :=
  ∀ l ∈ s, P l → Q l

instance (P Q : α → Prop) (s : Finset α) [DecidablePred P] [DecidablePred Q] :
    Decidable (ImplicationalUniversal P Q s) :=
  Finset.decidableDforallFinset

end Core.Typology

/-- Build a 2×2 contingency table by counting elements of `s` that satisfy
    each combination of `P` and `Q`. -/
def Finset.contingency (s : Finset α) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] : Core.Typology.ContingencyTable :=
  { pp := (s.filter (fun l =>  P l ∧  Q l)).card
    pn := (s.filter (fun l =>  P l ∧ ¬Q l)).card
    np := (s.filter (fun l => ¬P l ∧  Q l)).card
    nn := (s.filter (fun l => ¬P l ∧ ¬Q l)).card }

namespace Core.Typology

/-- Bridge between the propositional and tetrachoric formulations: an
    implicational universal holds iff its Type IV cell is empty.

    @cite{greenberg-1963}'s reformulation of "P implies Q" as "no language
    is P-but-not-Q" — same content, expressed once as a universal statement
    and once as a count-zero claim. -/
theorem implicational_iff_no_typeIV
    (s : Finset α) (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] :
    ImplicationalUniversal P Q s ↔ (s.contingency P Q).pn = 0 := by
  unfold ImplicationalUniversal Finset.contingency
  simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, not_and, not_not]

end Core.Typology
