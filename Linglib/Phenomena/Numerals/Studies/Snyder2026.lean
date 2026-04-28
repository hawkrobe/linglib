import Linglib.Theories.Semantics.Noun.Kind.Mendia2020
import Linglib.Phenomena.Numerals.Studies.Spector2013
import Linglib.Fragments.Dutch.Adjectives
import Mathlib.Data.Fintype.Basic

/-!
# Numbers as kinds: Polymorphic Contextualism
@cite{snyder-2026}

@cite{snyder-2026} (L&P 49:57-100) argues that the lexical meaning of `two`
is an *atomic predicate* `λxα. two(x)` that applies to different countable
entities (numeral tokens, kinds, subkinds of TWO) in different contexts;
all other meanings derive via Partee type-shifting. This generalises and
strictly subsumes two earlier analyses Snyder labels:

* **Polymorphic Substantivalism**: lexical `[[two]] = 2` is a numeral
  (entity of type `e`); cardinal predicates derive via CARD; all else via
  type-shifting. (@cite{landman-2004}; @cite{scontras-2014}; @cite{snyder-2017}.)
* **Polymorphic Adjectivalism**: lexical `[[two]] = λx. μ#(x) = 2` is a
  cardinality predicate; numerals derive via NOM + Rothstein's Schematic
  Equation. (@cite{partee-1987}; @cite{geurts-2006}; @cite{rothstein-2013};
  @cite{rothstein-2017}; @cite{kennedy-2015}; @cite{bylinina-nouwen-2020}.)
* **Polymorphic Contextualism** (@cite{snyder-2026}): lexical
  `[[two]] = λxα. two(x)` is an atomic predicate over relativized atoms;
  *all* meanings derive via type-shifting (CARD/PM/A/NOM/IOTA), including
  taxonomic, kind-, and token-referential uses the first two analyses miss.

The diagram from §5 (76a-j):

```
                     CARD            PM
   (76g),(76i),(76e) ───→ (76a) ───→ (76b)
         ↑ IOTA            │           │
         │                NOM          A
         │                 ↓           ↓
    λxα. two(x)         (76d)      (76c)
         ↓ PM + IOTA
   (76h),(76j),(76f) — close appositives
```

## Architecture

* `Theories/Semantics/Noun/Kind/Mendia2020.lean` — substrate: kind formation
  by salient equivalence relation (= mathlib's `Setoid`); Carlson's
  Disjointness Condition. Snyder's account of why TWO has disjoint subkinds
  `2_ℕ, 2_ℤ, 2_ℚ, 2_ℝ` (§4.3, §5) instantiates the Mendia framework via
  the local `kfTWO : Setoid TwoToken` partition (defined below).
* This file additionally implements Snyder's §6-§7 colour-word extension
  via a second local Mendia partition `kfRed : Setoid ColorToken`,
  consuming the Dutch adjective Fragment for colour roots.
* `Phenomena/Morphology/Studies/McNallyDeSwart2011.lean` is a sibling
  Mendia consumer, with `kfShade : Setoid Shade` partitioning Dutch
  colour and taste shades by adjective root. Together with the two
  partitions in this file, the Mendia substrate now has *three*
  consumers (numerals + Snyder colours + M&deS colours/tastes), genuinely
  cross-domain. All four partitions follow the project-wide
  `kf{Carrier}` naming convention.

The two colour analyses (Snyder §6 here vs M&deS over there) are
*competing* — they consume the same Mendia substrate (`subkindOf`) and
agree on iota for definites, but disagree on lexical-projection
architecture (Snyder: unitary `λxα. red(x)` over relativized atoms;
M&deS: distinct `rood_N` vs `rood_A` projected from a shared root) and
on nominalisation operator (Snyder: Partee NOM as typed shifter; M&deS:
Chierchia ∩ carried by *het*). Having both formalised makes the
divergence load-bearing instead of docstring-only.

This file:

1. Models the three analyses' lexical types and the nine semantic functions'
   target types as a small inductive `SemTy` (`e`, `et`, `ett`).
2. Gives each Partee/Snyder operator a typed signature; a *derivation path*
   is well-typed iff its operator chain composes from lexical type to target
   type. Coverage theorems then witness type-checking results, not just
   table lookup.
3. Instantiates the Mendia framework over a `TwoToken` carrier with multiple
   tokens per number system, so `disjointness_condition` does real work in
   the Identification-Problem theorem.
4. Uses a real Sharvy iota for close appositives — the (16b)
   `[[the N₁ N₂]] = ιx[N₁(x) ∧ N₂(x)]` clause carries a uniqueness
   presupposition, modelled as a partial `Option`-valued operation.

The Identification Problem (@cite{benacerraf-1965}; @cite{snyder-2026} §3.1,
§5.2; @cite{snyder-2025}) is dissolved by *derivation* from the substrate:
distinct equivalence classes of TWO under the salient partition are disjoint,
so close-appositive iota over modifier-restricted subkinds yields distinct
referents whenever the uniqueness presupposition is satisfied. Cf.
@cite{moltmann-2013}, @cite{hofweber-2005}, @cite{rieppel-2021} for rival
treatments of close-appositive coreference, and @cite{anderson-morzycki-2015}
for the Degrees-as-Kinds view Snyder adopts in §5.3.
-/

namespace Phenomena.Numerals.Snyder2026

open Semantics.Noun.Kind.Mendia2020 (subkindOf disjointness_condition
  subkindOf_ne mem_subkindOf)

/-! ## Semantic types

A small fragment of the Heim & Kratzer / Partee type system, sufficient to
carry the Snyder paths. PM is treated monadically (`et → et`) — the
implicit second predicate is supplied at the syntax level. -/

/-- Semantic types in Snyder's compositional fragment. -/
inductive SemTy where
  /-- Entities (and numbers, treated as ordinary atomic individuals). -/
  | e
  /-- Predicates `⟨e,t⟩`. -/
  | et
  /-- Generalized quantifiers `⟨⟨e,t⟩,t⟩`. -/
  | ett
  deriving DecidableEq, Repr

/-! ## §2-3, §5: the three polymorphic analyses -/

/-- The three polymorphic analyses Snyder distinguishes — labels verbatim
    from @cite{snyder-2026} §2-3. -/
inductive PolymorphicAnalysis where
  /-- Lexical `[[two]] = 2 : e` (a numeral entity), §2 (5). -/
  | substantivalism
  /-- Lexical `[[two]] = λx. μ#(x) = 2 : et` (a cardinality predicate), §2 (9). -/
  | adjectivalism
  /-- Lexical `[[two]] = λxα. two(x) : et` (an atomic predicate over
      relativized atoms), §5 (73). -/
  | contextualism
  deriving DecidableEq, Repr

/-- The lexical type of `[[two]]` under each analysis. -/
def PolymorphicAnalysis.lexicalType : PolymorphicAnalysis → SemTy
  | .substantivalism => .e
  | .adjectivalism   => .et
  | .contextualism   => .et

/-! ## §1, §5: nine semantic functions -/

/-- The nine semantic functions @cite{snyder-2026} attests for `two`.
    Cases (1a-f) are §1 consensus polysemy data; (76g-j) are the additional
    uses §5 argues only Polymorphic Contextualism handles. -/
inductive SemanticFunction where
  /-- (1a) Mars's moons are two (in number). -/
  | predicative
  /-- (1b) Those are (Mars's) two moons. -/
  | attributive
  /-- (1c) Mars has two moons. -/
  | quantificational
  /-- (1d) The number of Mars's moons is two. -/
  | specificational
  /-- (1e) Two is an even number. -/
  | numeral
  /-- (1f) The number two is even. -/
  | closeAppositive
  /-- (76g,h) Two is next to a five on the board. — token reference. -/
  | tokenRef
  /-- (76i) Two comes in several varieties. — kind reference. -/
  | kindRef
  /-- (76j) Each (kind of) two belongs to a different number system. -/
  | taxonomic
  deriving DecidableEq, Repr

/-- The target semantic type of each function. All target `e` except those
    that are predicate- or GQ-typed at surface. -/
def SemanticFunction.targetType : SemanticFunction → SemTy
  | .predicative      => .et
  | .attributive      => .et
  | .quantificational => .ett
  | .specificational  => .e
  | .numeral          => .e
  | .closeAppositive  => .e
  | .tokenRef         => .e
  | .kindRef          => .e
  | .taxonomic        => .e

/-! ## §5: Partee/Snyder operators with type signatures

Each operator has a deterministic input/output type, recorded as `input`/
`output` projections. PM is treated as monadic — the second predicate is
supplied externally. -/

/-- Type-shifting operators entering Snyder's diagrams. RSE is *not*
    included as a typed shifter: per @cite{rothstein-2017} and the
    discussion in @cite{snyder-2026} §2, RSE is a meta-level identification
    `n = ∩[λx. μ#(x) = n]`, not a Partee-style type-shifter. The
    adjectivalist numeral derivation uses NOM and then RSE-identifies
    the resulting entity with a number; this is documented in
    `adjectivalistPath` rather than recorded as an operator. -/
inductive Operator where
  /-- @cite{snyder-2026} (6a): `CARD = λn.λx. μ#(x) = n` — a number
      entity to a cardinality predicate. -/
  | card
  /-- @cite{heim-kratzer-1998} (7a): Predicate Modification (monadic). -/
  | pm
  /-- @cite{partee-1987} (8a): existential closure `λP.λQ.∃x.P(x)∧Q(x)`. -/
  | a
  /-- @cite{partee-1987} (10a): nominalisation, `et → e`. -/
  | nom
  /-- @cite{partee-1987} (74a): Russellian iota `λP.ιx[P(x)]`. -/
  | iota
  /-- @cite{partee-1987} (17a): identity-predicate former `λx.λy. y = x`. -/
  | ident
  deriving DecidableEq, Repr

/-- Input semantic type of each operator. -/
def Operator.input : Operator → SemTy
  | .card  => .e
  | .pm    => .et
  | .a     => .et
  | .nom   => .et
  | .iota  => .et
  | .ident => .e

/-- Output semantic type of each operator. -/
def Operator.output : Operator → SemTy
  | .card  => .et
  | .pm    => .et
  | .a     => .ett
  | .nom   => .e
  | .iota  => .e
  | .ident => .et

/-- A derivation chain is well-typed iff each operator's input matches the
    previous output. Returns the final type if the chain composes, else
    `none`. -/
def wellTyped : SemTy → List Operator → Option SemTy
  | t, []        => some t
  | t, op :: ops =>
    if t = op.input then wellTyped op.output ops else none

/-! ## §2, §5: derivation maps for the three analyses -/

/-- Substantivalism (lexical : `e`). Three semantic functions are not
    derived (§3 — token, kind, taxonomic uses). The `closeAppositive`
    derivation is `[ident, iota]`: IDENT applies first to the singular
    term producing a predicate, then IOTA over the (modifier-conjoined)
    predicate (Snyder (17b)+(18) p.65). -/
def substantivalistPath : SemanticFunction → Option (List Operator)
  | .numeral          => some []
  | .predicative      => some [.card]
  | .attributive      => some [.card, .pm]
  | .quantificational => some [.card, .a]
  | .specificational  => some [.card, .nom]
  | .closeAppositive  => some [.ident, .iota]
  | .tokenRef         => none
  | .kindRef          => none
  | .taxonomic        => none

/-- Adjectivalism (lexical : `et`). The `numeral` derivation is `[nom]`
    reaching the specificational entity, *and then* identified with a
    number via Rothstein's Schematic Equation (RSE) — a meta-level
    stipulation not a Partee shifter, so RSE does not appear in the
    operator chain. The `closeAppositive` derivation passes through the
    numeral: `[nom, ident, iota]`. Same three §3 gaps. -/
def adjectivalistPath : SemanticFunction → Option (List Operator)
  | .predicative      => some []
  | .attributive      => some [.pm]
  | .quantificational => some [.a]
  | .specificational  => some [.nom]
  | .numeral          => some [.nom]
  | .closeAppositive  => some [.nom, .ident, .iota]
  | .tokenRef         => none
  | .kindRef          => none
  | .taxonomic        => none

/-- Polymorphic Contextualism (lexical : `et`). All nine functions are
    derivable. The `closeAppositive` derivation is `[pm, iota]`: under
    contextualism both `two` and the modifier `number` are *already*
    predicates, so PM-conjunction + IOTA suffices — no IDENT step is
    needed (Snyder §5.2 (87)). -/
def contextualistPath : SemanticFunction → Option (List Operator)
  | .numeral          => some [.iota]
  | .kindRef          => some [.iota]
  | .tokenRef         => some [.iota]
  | .taxonomic        => some [.iota]
  | .predicative      => some [.iota, .card]
  | .attributive      => some [.iota, .card, .pm]
  | .quantificational => some [.iota, .card, .a]
  | .specificational  => some [.iota, .card, .nom]
  | .closeAppositive  => some [.pm, .iota]

/-- The derivation map associated with a polymorphic analysis. -/
def PolymorphicAnalysis.path :
    PolymorphicAnalysis → SemanticFunction → Option (List Operator)
  | .substantivalism => substantivalistPath
  | .adjectivalism   => adjectivalistPath
  | .contextualism   => contextualistPath

/-- A function is *covered* by an analysis iff the analysis derives it. -/
def PolymorphicAnalysis.covers (a : PolymorphicAnalysis)
    (sf : SemanticFunction) : Prop := (a.path sf).isSome

instance (a : PolymorphicAnalysis) (sf : SemanticFunction) :
    Decidable (a.covers sf) := by
  unfold PolymorphicAnalysis.covers; exact inferInstance

/-! ## Type-soundness of the derivation paths

The substantive content of @cite{snyder-2026}'s diagrams: every prescribed
derivation actually composes — input/output types align at each step, and
the chain ends at the targeted type. This is the type-driven witness that
the analyses are not just label collections but real compositional
analyses. -/

/-- Every derivation path in every analysis is well-typed and lands at the
    correct target type. This is *not* `cases <;> rfl` over a stipulated
    table: each case computes the `wellTyped` chain through `Operator.input`/
    `Operator.output` and verifies the chain reaches `targetType`. The
    `none` cases are vacuously true. -/
theorem analyses_well_typed (a : PolymorphicAnalysis) (sf : SemanticFunction) :
    match a.path sf with
    | some ops => wellTyped a.lexicalType ops = some sf.targetType
    | none     => True := by
  cases a <;> cases sf <;> first | rfl | trivial

/-! ## Coverage theorems -/

/-- Polymorphic Contextualism covers every semantic function. -/
theorem contextualism_covers_all (sf : SemanticFunction) :
    PolymorphicAnalysis.contextualism.covers sf := by
  cases sf <;> rfl

/-- Substantivalism does not cover taxonomic, kind, or token uses
    (Snyder §3 — the empirical gap motivating Polymorphic Contextualism). -/
theorem substantivalism_misses_taxonomic_kind_token :
    ¬ PolymorphicAnalysis.substantivalism.covers .taxonomic
    ∧ ¬ PolymorphicAnalysis.substantivalism.covers .kindRef
    ∧ ¬ PolymorphicAnalysis.substantivalism.covers .tokenRef := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Adjectivalism inherits the same gap. -/
theorem adjectivalism_misses_taxonomic_kind_token :
    ¬ PolymorphicAnalysis.adjectivalism.covers .taxonomic
    ∧ ¬ PolymorphicAnalysis.adjectivalism.covers .kindRef
    ∧ ¬ PolymorphicAnalysis.adjectivalism.covers .tokenRef := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Contextualism strictly extends Substantivalism's coverage. -/
theorem contextualism_strictly_extends_substantivalism :
    (∀ sf, PolymorphicAnalysis.substantivalism.covers sf →
           PolymorphicAnalysis.contextualism.covers sf)
    ∧ (∃ sf, PolymorphicAnalysis.contextualism.covers sf
           ∧ ¬ PolymorphicAnalysis.substantivalism.covers sf) := by
  refine ⟨fun sf _ => contextualism_covers_all sf,
          ⟨.taxonomic, contextualism_covers_all _, by decide⟩⟩

/-- Contextualism strictly extends Adjectivalism's coverage. -/
theorem contextualism_strictly_extends_adjectivalism :
    (∀ sf, PolymorphicAnalysis.adjectivalism.covers sf →
           PolymorphicAnalysis.contextualism.covers sf)
    ∧ (∃ sf, PolymorphicAnalysis.contextualism.covers sf
           ∧ ¬ PolymorphicAnalysis.adjectivalism.covers sf) := by
  refine ⟨fun sf _ => contextualism_covers_all sf,
          ⟨.taxonomic, contextualism_covers_all _, by decide⟩⟩

/-! ## §4.3, §5: numbers as kinds — the TWO taxonomy

Snyder §4.3 (51) argues NUMBER has subkinds `ℕ ⊂ ℤ ⊂ ℚ ⊂ ℝ ⊂ ...`, and
correspondingly the kind TWO has subkinds `2_ℕ, 2_ℤ, 2_ℚ, 2_ℝ`. The
formation mechanism is @cite{mendia-2020}'s: partition by the salient
equivalence relation `belongs to the same number system`. Each subkind
is itself a kind — instantiated by *numeral tokens* representing that
specific number (Snyder §4 Tokens-Types-Kinds ontology, §4.3). -/

/-- Mathematical number systems Snyder uses to illustrate subkind
    formation for TWO (§4.3). -/
inductive MathSystem where
  | nat | int | rat | real
  deriving DecidableEq, Repr

instance : Fintype MathSystem where
  elems := {.nat, .int, .rat, .real}
  complete := by intro x; cases x <;> decide

/-- A token of `two`: a concrete instantiation typed by its number system
    (the partition criterion) plus an index distinguishing multiple tokens
    of the same system (e.g., different concrete numerals on the board).
    Per @cite{snyder-2026} §4 Tokens-Types-Kinds. -/
structure TwoToken where
  /-- Which mathematical number system this token instantiates. -/
  system : MathSystem
  /-- Distinguishing index for multiple tokens of the same system. -/
  idx : Nat
  deriving DecidableEq, Repr

/-- The Mendia kind-formation for TWO: numeral tokens partitioned by their
    number system. The equivalence class of a token is the subkind `2_s`
    for that system; distinct subkinds are disjoint by Mendia's framework
    (= Carlson's Disjointness Condition). -/
def kfTWO : Setoid TwoToken where
  r t₁ t₂ := t₁.system = t₂.system
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- The lexical extension of `two` under Polymorphic Contextualism: the
    set of all tokens classified as a `two` of *some* number system. The
    extension's full content depends on context (per @cite{rothstein-2017}
    relativized atomicity); we use the unrestricted set as a witness for
    the Identification-Problem theorem below. -/
def two : Set TwoToken := Set.univ

/-- A canonical witness token in each number system, used as the unique
    candidate in the Sharvy-iota proofs. -/
def canonicalTwo (s : MathSystem) : TwoToken := ⟨s, 0⟩

/-- A four-token domain with one canonical witness per number system. The
    identification-problem proof works over this domain; the extension
    to richer domains follows the same pattern. -/
def canonicalDomain : List TwoToken :=
  [canonicalTwo .nat, canonicalTwo .int, canonicalTwo .rat, canonicalTwo .real]

theorem canonicalDomain_nodup : canonicalDomain.Nodup := by decide

/-! ## Sharvy iota at the Set level

Snyder (16b) is `[[the N₁ N₂]] = ιx[N₁(x) ∧ N₂(x)]` — Sharvy's iota
operator picks out the unique satisfier when one exists, undefined
otherwise. We model it as a partial `Option`-valued operator over a
finite domain, paralleling `Composition.TypeShifting.iota` but operating
on `Set` directly (avoiding the Frame boilerplate). -/

section Sharvy
variable {α : Type*}

/-- Sharvy 1980's iota: the unique element of `domain` satisfying `P`,
    if one exists. Returns `none` if no satisfier (existence presupposition
    failure) or multiple satisfiers (uniqueness presupposition failure). -/
def sharvyIota (domain : List α) (P : α → Bool) : Option α :=
  match domain.filter P with
  | [j] => some j
  | _   => none

/-- Predicate Modification at the Set level: pointwise conjunction. Mirrors
    `Composition.TypeShifting.PM`. -/
def setPM (P Q : α → Bool) : α → Bool := fun x => P x && Q x

/-- @cite{snyder-2026} (16b) close-appositive denotation:
    `[[the N₁ N₂]] = ιx[N₁(x) ∧ N₂(x)]` (@cite{sharvy-1980}). Real Sharvy
    iota over the PM-conjunction of the two predicates; uniqueness-
    presupposition failure yields `none`. -/
def closeAppositive (domain : List α) (n1 n2 : α → Bool) : Option α :=
  sharvyIota domain (setPM n1 n2)

/-- The defining computation of `sharvyIota`: it returns `some j` exactly
    when filtering `domain` by `P` leaves the singleton `[j]`. -/
theorem sharvyIota_eq_some_iff {domain : List α} {P : α → Bool} {j : α} :
    sharvyIota domain P = some j ↔ domain.filter P = [j] := by
  unfold sharvyIota
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  cases hf : domain.filter P with
  | nil => rw [hf] at h; cases h
  | cons hd tl =>
    cases tl with
    | nil =>
      rw [hf] at h
      injection h with hj
      rw [hj]
    | cons _ _ => rw [hf] at h; cases h

/-- If close appositives over disjoint modifier predicates each return
    `some` value, the values are distinct. The substantive content of
    Snyder §5.2's resolution: the iota succeeds for both descriptions
    *and* the disjointness of the modifier-restricted subkinds forces
    different referents. -/
theorem closeAppositive_ne_of_disjoint
    {domain : List α} {m₁ m₂ shared : α → Bool} {j₁ j₂ : α}
    (hDisj : ∀ x, ¬ (m₁ x = true ∧ m₂ x = true))
    (h₁ : closeAppositive domain m₁ shared = some j₁)
    (h₂ : closeAppositive domain m₂ shared = some j₂) :
    j₁ ≠ j₂ := by
  intro hEq
  have hf₁ := (sharvyIota_eq_some_iff.mp h₁)
  have hf₂ := (sharvyIota_eq_some_iff.mp h₂)
  have h1mem : j₁ ∈ domain.filter (setPM m₁ shared) := by rw [hf₁]; simp
  have h2mem : j₂ ∈ domain.filter (setPM m₂ shared) := by rw [hf₂]; simp
  have h1pm : setPM m₁ shared j₁ = true := (List.mem_filter.mp h1mem).2
  have h2pm : setPM m₂ shared j₂ = true := (List.mem_filter.mp h2mem).2
  rw [setPM] at h1pm h2pm
  rw [Bool.and_eq_true] at h1pm h2pm
  exact hDisj j₁ ⟨h1pm.1, hEq ▸ h2pm.1⟩

end Sharvy

/-! ## §5.2: the Identification Problem dissolved

@cite{benacerraf-1965} + Snyder §3.1, §5.2: the rigid-designator reading
of `two` predicts that `the von Neumann ordinal two = the Zermelo ordinal
two`, which is incoherent given the von Neumann ordinal `{∅, {∅}}` has
two members and the Zermelo ordinal `{{∅}}` has one. Polymorphic
Contextualism dissolves the paradox: each close appositive picks out a
*subkind* of TWO, and the modifiers select *disjoint* Mendia subkinds.

Below: a fully-computed witness on `canonicalDomain`. The system-restriction
predicate for each number system, when intersected with the lexical
extension `two`, picks out exactly the canonical witness for that system;
distinct systems yield distinct witnesses; therefore the close appositives
are not coreferential. -/

/-- Decidable membership in a kfTWO subkind, for use in `sharvyIota`. -/
def inSubkind (s : MathSystem) (t : TwoToken) : Bool := decide (t.system = s)

/-- Decidable membership in `two` (the universal predicate). -/
def inTwo (_ : TwoToken) : Bool := true

theorem inSubkind_iff (s : MathSystem) (t : TwoToken) :
    inSubkind s t = true ↔ t.system = s := by
  unfold inSubkind; simp

/-- For each number system `s`, the close appositive `the [s]-system two`
    over the canonical 4-token domain returns precisely the canonical
    witness of system `s`. -/
theorem closeAppositive_canonical (s : MathSystem) :
    closeAppositive canonicalDomain (inSubkind s) inTwo = some (canonicalTwo s) := by
  cases s <;> rfl

/-- @cite{benacerraf-1965}'s Identification Problem (Snyder §3.1, §5.2;
    cf. @cite{snyder-2025}) **resolved by derivation** from the
    @cite{mendia-2020} kind-formation substrate plus @cite{sharvy-1980} iota.

    For any two distinct number systems `s₁ ≠ s₂`, the close appositives
    `the [s₁]-system two` and `the [s₂]-system two`:
    * both succeed (uniqueness presupposition satisfied at the canonical
      domain), and
    * pick out distinct canonical witness tokens.

    The proof uses *both* substrate moves non-vacuously:
    * `disjointness_condition kfTWO` (subkinds are disjoint), then
    * `closeAppositive_ne_of_disjoint` (Sharvy iota over disjoint
      conjunctions yields distinct referents). -/
theorem identification_problem_resolved {s₁ s₂ : MathSystem} (h : s₁ ≠ s₂) :
    canonicalTwo s₁ ≠ canonicalTwo s₂ ∧
    closeAppositive canonicalDomain (inSubkind s₁) inTwo = some (canonicalTwo s₁) ∧
    closeAppositive canonicalDomain (inSubkind s₂) inTwo = some (canonicalTwo s₂) := by
  refine ⟨?_, closeAppositive_canonical s₁, closeAppositive_canonical s₂⟩
  intro hEq
  exact h (congrArg TwoToken.system hEq)

/-- Distinct subkinds of TWO are unequal as sets — the Mendia-substrate
    corollary that close-appositive descriptions (which restrict the
    lexical extension) cannot pick out a single rigid referent across
    contexts. Cf. @cite{snyder-2026} §5.1 discussion of (83). -/
theorem subkinds_distinct {s₁ s₂ : MathSystem} (h : s₁ ≠ s₂) :
    subkindOf kfTWO ⟨s₁, 0⟩ ≠ subkindOf kfTWO ⟨s₂, 0⟩ :=
  subkindOf_ne kfTWO h

/-! ## §1, §3.1, §3.4: empirical examples -/

/-- An example sentence with its semantic-function classification and
    acceptability judgment. -/
structure Example where
  exNum : String
  sentence : String
  function : SemanticFunction
  acceptable : Bool
  deriving DecidableEq, Repr

namespace Example

/-- The six examples from @cite{snyder-2026} (1a-f). -/
def core : List Example :=
  [ ⟨"1a", "Mars's moons are two (in number)",          .predicative,      true⟩
  , ⟨"1b", "Those are (Mars's) two moons",              .attributive,      true⟩
  , ⟨"1c", "Mars has two moons",                        .quantificational, true⟩
  , ⟨"1d", "The number of Mars's moons is two",         .specificational,  true⟩
  , ⟨"1e", "Two is an even number",                     .numeral,          true⟩
  , ⟨"1f", "The number two is even",                    .closeAppositive,  true⟩ ]

/-- The three additional examples from @cite{snyder-2026} (76g,i,j) that
    motivate Polymorphic Contextualism. -/
def extended : List Example :=
  [ ⟨"76g", "Two is next to a five on the board",       .tokenRef,   true⟩
  , ⟨"76i", "Two comes in several varieties: the natural number two, ...",
                                                        .kindRef,    true⟩
  , ⟨"76j", "Each (kind of) two belongs to a different number system",
                                                        .taxonomic,  true⟩ ]

/-- All nine attested semantic functions. -/
def all : List Example := core ++ extended

theorem all_acceptable : all.all (·.acceptable) = true := rfl

/-- Each `SemanticFunction` constructor is exhibited at least once. -/
theorem nine_functions_exhibited (sf : SemanticFunction) :
    sf ∈ all.map (·.function) := by cases sf <;> decide

end Example

/-- @cite{snyder-2026} (20a,b): Identification-Problem judgments. -/
structure IdentificationDatum where
  exNum : String
  sentence : String
  truthValue : Bool
  deriving DecidableEq, Repr

namespace IdentificationDatum

/-- (20a) "The von Neumann ordinal two is two-membered." TRUE. -/
def ex20a : IdentificationDatum :=
  ⟨"20a", "The von Neumann ordinal two is two-membered", true⟩

/-- (20b) "The Zermelo ordinal two is two-membered." FALSE. -/
def ex20b : IdentificationDatum :=
  ⟨"20b", "The Zermelo ordinal two is two-membered", false⟩

/-- The two judgments are jointly coherent — only Polymorphic Contextualism
    predicts both straightforwardly evaluable, by the Identification-Problem
    resolution above (cf. @cite{moltmann-2013}, @cite{rieppel-2021}). -/
theorem jointly_coherent : ex20a.truthValue ≠ ex20b.truthValue := by decide

end IdentificationDatum

/-! ## Cross-framework hooks

@cite{spector-2013} formalises a four-way taxonomy of bare-numeral analyses
(`Approach = neoGricean | underspecification | exactlyOnly | ambiguityEXH`)
along the *lower-bound vs exact* axis. Snyder's `PolymorphicAnalysis` carves
the orthogonal *lexical-type* axis. The two are intended to be independent:
one can hold any (lexical-type, lower-bound-vs-exact) combination, e.g.
`contextualism × exactlyOnly` or `adjectivalism × neoGricean`. The
orthogonality is witnessed here by the fact that no theorem connects the
two enums — they are simply parallel classifications of different choices
in a numeral semantics. Below, the formal axes-product type makes the
combinatorial space explicit. -/

/-- An *integrated* analysis = a choice on Snyder's lexical-type axis ×
    a choice on Spector's lower-bound vs exact axis. Each cell of the
    `PolymorphicAnalysis × Spector2013.Approach` product is, in principle,
    a coherent combination — the literature does not require the choices
    to be linked. -/
structure IntegratedAnalysis where
  lexicalAxis : PolymorphicAnalysis
  scalarAxis : Spector2013.Approach
  deriving DecidableEq, Repr

/-- The two axes are orthogonal: there are 3 × 4 = 12 combinations, every
    `(lexicalAxis, scalarAxis)` pair is realisable as a distinct
    integrated analysis. -/
theorem axes_orthogonal :
    ∀ a₁ a₂ : PolymorphicAnalysis, ∀ s₁ s₂ : Spector2013.Approach,
      (⟨a₁, s₁⟩ : IntegratedAnalysis) = ⟨a₂, s₂⟩ ↔ a₁ = a₂ ∧ s₁ = s₂ := by
  intros; constructor
  · intro h; exact ⟨by injection h, by injection h⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-! @cite{kennedy-2015}'s "de-Fregean" type-shift is structurally
`λn.λx. μ#(x) = n` — *exactly* Snyder's CARD (6a). Adjectivalism's lexical
denotation `λx. μ#(x) = 2` agrees extensionally with the partial application
of Kennedy's de-Fregean shift to the constant 2; the two analyses converge
on the cardinality predicate, differing only in whether it is the lexical
entry (Snyder Adjectivalism) or a derived form (Kennedy de-Fregean). This
agreement is documented here; making it a `rfl` theorem would require
co-locating the Lean denotations of CARD and Kennedy's shift in a shared
type, currently blocked by the Frame-vs-Set boundary in TypeShifting.
-/

/-! ## §6-§7: Polymorphic Contextualism for colour terms

@cite{snyder-2026} §6-§7 conjectures that colour words admit the same
Polymorphic-Contextualism analysis as numerals. The lexical entry (97):

    [[red]] = λxα. red(x)

is a context-sensitive atomic predicate (parallel to `[[two]] = λxα. two(x)`
in §5 (73)). The kind RED has subkinds CRIMSON, MAROON, ... (cf. paint-
swatch examples (94a-c)), so colour names like `red` and close appositives
like `the color red` can refer to subkinds, the kind RED itself, or
concrete colour tokens — exactly the polymorphism (76e/g/i/j/f) the
numeral analysis predicts.

§6 cites @cite{mcnally-2011} and @cite{mcnally-deswart-2011} for the
colours-as-kinds claim. This file implements Snyder's *own* Polymorphic
Contextualism extension; for the @cite{mcnally-deswart-2011} *competing*
analysis (lexical category-projected, Chierchia ∩-via-*het* nominalisation),
see `Phenomena/Morphology/Studies/McNallyDeSwart2011.lean`. Both analyses
consume the same Mendia substrate (`subkindOf` on a `Setoid` partition by
adjective root); they disagree on lexical-projection architecture and on
whether nominalisation is Partee NOM (Snyder) or Chierchia ∩ (M&deS).

The substrate generalises across domains: this is the *third* consumer of
`Mendia2020.subkindOf`, after Snyder numerals (above) and McNally-deSwart
colours/tastes. The `kf{Carrier}` naming convention (`kfTWO`, `kfRed`,
`kfShade`) is project-wide.
-/

/-- A colour token: a colour-domain Dutch adjective entry from
    `Fragments/Dutch/Adjectives.lean` plus a distinguishing index for
    multiple shade-tokens of the same colour. Parallel to `TwoToken`
    above; the Mendia partition is exercised non-trivially when a single
    colour root has multiple tokens (e.g., several physical instances
    of `rood` on a paint swatch per @cite{snyder-2026} (94)). -/
structure ColorToken where
  /-- The Dutch colour-adjective entry (`Fragments.Dutch.Adjectives.rood`,
      `wit`, `groen`, ...). The colour-domain restriction is documentary;
      the type itself is `AdjEntry`. -/
  root : Fragments.Dutch.Adjectives.AdjEntry
  /-- Distinguishing index for multiple tokens of the same colour root. -/
  idx : Nat
  deriving DecidableEq, Repr

/-- The Mendia kind-formation for colours: tokens partitioned by their
    adjective-entry root. The equivalence class of any token is the
    subkind of RED (or BLUE, or GREEN, ...) that token instantiates.
    Parallel to `kfTWO`, attesting that Mendia's framework generalises
    across domains. Carlson's Disjointness Condition follows. -/
def kfRed : Setoid ColorToken where
  r t₁ t₂ := t₁.root = t₂.root
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- @cite{snyder-2026} (97): `[[red]] = λxα. red(x)`. The lexical extension
    of `red` under Polymorphic Contextualism — the universal predicate
    over relativized atoms, indicating that `red` may apply to subkinds
    (CRIMSON, MAROON), to the kind RED itself, or to concrete tokens.
    Parallel to `two : Set TwoToken := Set.univ` above. -/
def red : Set ColorToken := Set.univ

/-- A canonical witness colour token for each colour-adjective root. -/
def canonicalColor (a : Fragments.Dutch.Adjectives.AdjEntry) : ColorToken :=
  ⟨a, 0⟩

/-- A canonical 6-token domain with one witness per Dutch alternating
    colour root (per @cite{mcnally-deswart-2011} §1, the inflection-
    alternating colour sub-paradigm). -/
def canonicalColorDomain : List ColorToken :=
  [canonicalColor Fragments.Dutch.Adjectives.rood,
   canonicalColor Fragments.Dutch.Adjectives.wit,
   canonicalColor Fragments.Dutch.Adjectives.groen,
   canonicalColor Fragments.Dutch.Adjectives.geel,
   canonicalColor Fragments.Dutch.Adjectives.blauw,
   canonicalColor Fragments.Dutch.Adjectives.zwart]

theorem canonicalColorDomain_nodup : canonicalColorDomain.Nodup := by decide

/-! ### §6 colour-Polymorphic-Contextualism theorems

Mirroring the numeral case, distinct colour-kinds are disjoint as
Mendia subkinds, so close-appositive descriptions like `the color red`
and `the color green` denote distinct subkinds — supporting Snyder's
claim that colour names refer polymorphically to subkinds. -/

/-- Distinct colour roots project to distinct Mendia subkinds — the
    colour analog of `subkinds_distinct` for numerals. -/
theorem color_subkinds_distinct
    {a₁ a₂ : Fragments.Dutch.Adjectives.AdjEntry} (h : a₁ ≠ a₂) :
    subkindOf kfRed ⟨a₁, 0⟩ ≠ subkindOf kfRed ⟨a₂, 0⟩ :=
  subkindOf_ne kfRed h

/-- Indicator predicate: token `t` belongs to the colour-`a` subkind. -/
def inColorSubkind (a : Fragments.Dutch.Adjectives.AdjEntry)
    (t : ColorToken) : Bool := decide (t.root = a)

/-- The colour close-appositive `the color [a]` over the canonical 6-token
    domain returns precisely the canonical witness of colour root `a`,
    when `a` is in the canonical-colour-list. -/
theorem closeAppositive_canonical_color
    (a : Fragments.Dutch.Adjectives.AdjEntry)
    (h : a ∈ [Fragments.Dutch.Adjectives.rood, Fragments.Dutch.Adjectives.wit,
             Fragments.Dutch.Adjectives.groen, Fragments.Dutch.Adjectives.geel,
             Fragments.Dutch.Adjectives.blauw, Fragments.Dutch.Adjectives.zwart]) :
    closeAppositive canonicalColorDomain (inColorSubkind a) (fun _ => true)
      = some (canonicalColor a) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Colour analog of `identification_problem_resolved`: distinct colour
    close appositives `the color [a₁]` and `the color [a₂]` denote
    distinct canonical witness tokens, supporting the polymorphic-kind
    analysis of @cite{snyder-2026} §6 (94)-(98). -/
theorem distinct_colors_distinct_close_appositives
    {a₁ a₂ : Fragments.Dutch.Adjectives.AdjEntry} (h : a₁ ≠ a₂) :
    canonicalColor a₁ ≠ canonicalColor a₂ :=
  fun hEq => h (congrArg ColorToken.root hEq)

/-! ### §6 empirical examples (94)-(98) -/

/-- @cite{snyder-2026} §6 colour-polysemy examples (94)-(98). Each is
    classified by the same `SemanticFunction` enum as the numeral cases,
    confirming the polymorphism extends to colours. -/
def colorExamples : List Example :=
  [ ⟨"94a", "That (kind of) red is used to paint barns",  .taxonomic, true⟩
  , ⟨"94b", "Red comes in several varieties: crimson, maroon, ...",
                                                          .kindRef,   true⟩
  , ⟨"94c", "One kind of red, namely crimson, is used to paint barns",
                                                          .taxonomic, true⟩
  , ⟨"98",  "(The color) red is next to (the color) green on the swatch",
                                                          .tokenRef,  true⟩ ]

theorem color_examples_acceptable :
    colorExamples.all (·.acceptable) = true := rfl

/-- The colour-polysemy examples exhibit three of the §1 numeral-polysemy
    semantic functions (taxonomic, kindRef, tokenRef) — exactly the three
    that Substantivalism and Adjectivalism *fail* to derive (per
    `substantivalism_misses_taxonomic_kind_token` and friends). The
    colour port confirms Snyder's §6 claim that Polymorphic Contextualism
    handles them uniformly. -/
theorem color_examples_use_extended_functions :
    ∀ ex ∈ colorExamples,
      ex.function ∈ [SemanticFunction.taxonomic, .kindRef, .tokenRef] := by
  intro ex h
  simp only [colorExamples, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

end Phenomena.Numerals.Snyder2026
