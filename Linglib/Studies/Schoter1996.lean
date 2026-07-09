import Linglib.Core.Logic.Bilattice.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Bool.Basic

/-!
# Schöter's evidential bilattices: `PRESUP` and the evidential progression
[schoter-1996]

[schoter-1996]'s Evidential Bilattice Logic analyzes natural-language entailment,
implicature, and presupposition by climbing a progression of evidential
bilattices `S ⊙ S` (`Bilattice.Evidential`): `classical ⊂` Kleene-3 `⊂ FOUR ⊂
PRESUP` (Fig. 1). A value is a pair `(for, against)` of degrees of evidence
drawn from a chain `S` — the paper writes `⟨a, b⟩` for `(against, for)`
(reversing Fitting's coordinate order, as its fn. to §2.1 notes); this file
keeps the library's `(for, against)` = Fitting order throughout.

This file is the second consumer of the `Bilattice` substrate (the first is
`Studies.Fitting1994`, which shows Kleene-3 = the consistent fragment of `FOUR`).
It formalizes the paper's *value level*:

* **`PRESUP := Evidential (Fin 3)`** — evidence from the 3-chain `0 < ½ < 1`
  (§2.1): the nine values `U, T, F, I, P⁺, P⁻, C, D⁺, D⁻`. The orderings and
  inversions of Defs 1–2 are the substrate's `≤`/`≤ₖ`, `Product.neg`, and
  `Evidential.conf`; the meets and joins of Def 3 are `⊓`/`⊔`/`⊗`/`⊕`.
* **`embed : FOUR → PRESUP`** — `FOUR` is a sub-bilattice of `PRESUP`
  (order-preserving in both `≤` and `≤ₖ`): Schöter's "`FOUR` is a sublattice
  of all bilattices."
* **partitions of the evidential space** (§2.2) — `Bilattice.Evidential`'s
  consistent/classical fragments plus the paper's designated (`Designated`)
  and semi-designated (`SemiDesignated`) subspaces, with their order-theoretic
  characterizations and the closure facts of §2.2.
* **value-level connectives** — Fitting's guard `φ : ψ` (Def 4), the
  semi-designation function `σ` (Def 5), the value-level `presumably` operator
  `π` (Def 14, clause 2), and the evidential-weighting function `f⋆` (Def 16)
  onto the constants of [ginsberg-1988]'s `DEFAULT` bilattice.

Scope: the value space, the progression, and the value-level operators.
Schöter's epistemic-state apparatus (setups, evidential links, assertion /
evaluation / closure, `FOEBL`/`FOMEBL`, and the §4 data analyses that run on
the implemented engine) is out of scope.
-/

open Bilattice

namespace Schoter1996

/-- Schöter's `PRESUP` (§2.1): the evidential bilattice over the 3-chain
`Fin 3 ~ {0, ½, 1}` — `FOUR` with defeasible/presumed values added. -/
abbrev PRESUP := Evidential (Fin 3)

namespace PRESUP

/-- `⊥`: no information (a presupposition gap). -/
def U : PRESUP := .mk 0 0
/-- Definite truth (full evidence for, none against). -/
def T : PRESUP := .mk 2 0
/-- Definite falsity. -/
def F : PRESUP := .mk 0 2
/-- Inconsistent / overdefined (a glut). -/
def I : PRESUP := .mk 2 2
/-- Presumably true: defeasible (`½`) evidence for, none against. -/
def Pplus : PRESUP := .mk 1 0
/-- Presumably false. -/
def Pminus : PRESUP := .mk 0 1
/-- Confused: conflicting defeasible evidence — "not as strong a contradiction
as `I`" (§2.1). -/
def C : PRESUP := .mk 1 1
/-- Defeated default `D⁺`: default evidence for falsity overridden by definite
evidence for truth (§2.1). -/
def Dplus : PRESUP := .mk 2 1
/-- Defeated default `D⁻`: default evidence for truth overridden by definite
negative evidence (§2.1). -/
def Dminus : PRESUP := .mk 1 2

/-- Conflation on `PRESUP`, complementing on the chain by `Fin.rev`. -/
@[reducible] def conf (x : PRESUP) : PRESUP := Evidential.conf Fin.rev x
/-- The consistent (non-glut) fragment of `PRESUP`. -/
@[reducible] def Consistent (x : PRESUP) : Prop := Evidential.Consistent Fin.rev x

end PRESUP

/-- `Bool ↪ Fin 3`: `false ↦ 0` (no evidence), `true ↦ 2` (full evidence). -/
def boolToFin3 : Bool → Fin 3 := fun b => if b then 2 else 0

/-- The embedding of `FOUR` into `PRESUP` (definite values only). -/
def embed (x : FOUR) : PRESUP := .mk (boolToFin3 x.pro) (boolToFin3 x.con)

/-- **`FOUR ⊂ PRESUP`, truth order**: the embedding preserves and reflects `≤`. -/
theorem embed_le (x y : FOUR) : x ≤ y ↔ embed x ≤ embed y := by
  obtain ⟨xa, xb⟩ := x; obtain ⟨ya, yb⟩ := y
  cases xa <;> cases xb <;> cases ya <;> cases yb <;> decide

/-- **`FOUR ⊂ PRESUP`, knowledge order**: the embedding preserves and reflects
`≤ₖ`. -/
theorem embed_kLE (x y : FOUR) : x ≤ₖ y ↔ embed x ≤ₖ embed y := by
  obtain ⟨xa, xb⟩ := x; obtain ⟨ya, yb⟩ := y
  cases xa <;> cases xb <;> cases ya <;> cases yb <;> decide

/-- A presupposition gap (`U`) and a defeasible presumption (`P⁺`) are both
*consistent*; only the overdefined glut `I` is excluded. So `PRESUP` keeps the
gap-based presupposition logic and layers defeasible values on top. -/
theorem gap_and_presumption_consistent :
    PRESUP.Consistent PRESUP.U ∧ PRESUP.Consistent PRESUP.Pplus
      ∧ ¬ PRESUP.Consistent PRESUP.I := by
  decide

/-! ### Partitions of the evidential space (§2.2)

The classical and consistent subspaces are Fitting's (`Evidential.IsClassical`,
`Evidential.Consistent`); the designated and semi-designated subspaces are the
paper's, with their footnote characterizations `DES = {x | t ≤ₖ x}` and
`SEMI = {x | ¬x ≤ x, U <ₖ x}` proved as order-theoretic facts. -/

section Partitions

variable {S : Type*} [LinearOrder S] [BoundedOrder S]

/-- Designated values (§2.2): maximal positive evidence, `DES = {⟨a, b⟩ | b = 1}`. -/
@[reducible] def Designated (x : Evidential S) : Prop := x.pro = ⊤

/-- Semi-designated values (§2.2): some positive evidence, at least as strong
as the negative evidence — `SEMI = {⟨a, b⟩ | a ≤ b, 0 < b}`. -/
@[reducible] def SemiDesignated (x : Evidential S) : Prop :=
  x.con ≤ x.pro ∧ ⊥ < x.pro

/-- The footnote characterization of designation: a value is designated iff it
is knowledge-above the truth top, `DES = {x | t ≤ₖ x}` (§2.2). -/
theorem designated_iff_top_kLE {x : Evidential S} :
    Designated x ↔ (⊤ : Evidential S) ≤ₖ x :=
  ⟨fun h => ⟨h.ge, bot_le⟩, fun h => le_antisymm le_top h.1⟩

/-- The footnote characterization of semi-designation: a value is
semi-designated iff it is truer than its negation and contains some
information, `SEMI = {x | ¬x ≤ x, U <ₖ x}` (§2.2). -/
theorem semiDesignated_iff {x : Evidential S} :
    SemiDesignated x ↔ Product.neg x ≤ x ∧ (⊥ : Know (Evidential S)) < toKnow x := by
  constructor
  · rintro ⟨hle, hlt⟩
    exact ⟨⟨hle, hle⟩, bot_lt_iff_ne_bot.mpr fun h => hlt.ne' (congrArg Prod.fst h)⟩
  · rintro ⟨hneg, hlt⟩
    refine ⟨hneg.1, bot_lt_iff_ne_bot.mpr fun hp => hlt.ne' ?_⟩
    exact Prod.ext hp (le_bot_iff.mp (hneg.1.trans hp.le))

/-- `PRESUP`'s designated subspace is `{T, D⁺, I}` (§2.2). -/
theorem designated_cases :
    ∀ x : PRESUP, Designated x ↔ x = PRESUP.T ∨ x = PRESUP.Dplus ∨ x = PRESUP.I := by
  decide

/-- `PRESUP`'s semi-designated subspace is `{P⁺, C, T, D⁺, I}` (§2.2). -/
theorem semiDesignated_cases :
    ∀ x : PRESUP, SemiDesignated x ↔ x = PRESUP.Pplus ∨ x = PRESUP.C ∨ x = PRESUP.T
      ∨ x = PRESUP.Dplus ∨ x = PRESUP.I := by
  decide

/-- On `FOUR` — no defeasible evidence — semi-designation collapses to
designation, `SEMI = DES` (§2.2). -/
theorem four_semiDesignated_iff_designated :
    ∀ x : FOUR, SemiDesignated x ↔ Designated x := by
  decide

/-- The consistent fragment of `FOUR` is closed under negation, the truth
operations, and consensus `⊗` (§2.2). -/
theorem four_consistent_closed :
    ∀ x y : FOUR, FOUR.Consistent x → FOUR.Consistent y →
      FOUR.Consistent (Product.neg x) ∧ FOUR.Consistent (x ⊓ y)
        ∧ FOUR.Consistent (x ⊔ y) ∧ FOUR.Consistent (x ⊗ y) := by
  decide

/-- ...but not under gullibility `⊕`: credulously combining consistent evidence
can produce the glut — paraconsistency is localized rather than absent. -/
theorem four_consistent_not_closed_kSup :
    ¬ ∀ x y : FOUR, FOUR.Consistent x → FOUR.Consistent y →
      FOUR.Consistent (x ⊕ y) := by
  decide

/-- The classical fragment of `FOUR` is closed under negation and the truth
operations (§2.2): the classical subspace supports classical logic. -/
theorem four_isClassical_closed :
    ∀ x y : FOUR, FOUR.IsClassical x → FOUR.IsClassical y →
      FOUR.IsClassical (Product.neg x) ∧ FOUR.IsClassical (x ⊓ y)
        ∧ FOUR.IsClassical (x ⊔ y) := by
  decide

end Partitions

/-! ### Value-level connectives (Defs 4, 5, 14, 16)

The recursive evaluation clauses of Def 14 are value-functional except for the
inference-link connective: clause 1 is `Product.neg`, clauses 3–4 are `⊓`/`⊔`,
clause 5 is Fitting's guard, and clause 2 (the `presumably` operator `π`) is
built from the guard and the semi-designation function `σ`. -/

section Connectives

open Evidential (guard)

variable {S : Type*} [LinearOrder S] [BoundedOrder S]

/-- The semi-designation function `σ` ([schoter-1996] Def 5): `T` on the
semi-designated values, `F` elsewhere. -/
def semiDesignation (x : Evidential S) : Evidential S :=
  if SemiDesignated x then .mk ⊤ ⊥ else .mk ⊥ ⊤

/-- The value-level `presumably` operator `π` ([schoter-1996] Def 14, clause 2):
`σ(v) : T ⊕ σ(¬v) : F` — presumably-true if the value is semi-designated,
presumably-false if its negation is, informationally unified. -/
def presumably (v : Evidential S) : Evidential S :=
  (guard (semiDesignation v) (.mk ⊤ ⊥) ⊕
    guard (semiDesignation (Product.neg v)) (.mk ⊥ ⊤) : Evidential S)

example : presumably PRESUP.Pplus = PRESUP.T := by decide
example : presumably PRESUP.T = PRESUP.T := by decide
example : presumably PRESUP.F = PRESUP.F := by decide
example : presumably PRESUP.U = PRESUP.U := by decide
example : presumably PRESUP.I = PRESUP.I := by decide

/-- The evidential-weighting function `f⋆` ([schoter-1996] Def 16): suppresses
the dominated evidence, so only the dominant evidence figures in evaluation. -/
def weight (x : Evidential S) : Evidential S :=
  if x.con < x.pro then .mk x.pro ⊥ else if x.pro < x.con then .mk ⊥ x.con else x

/-- Weighting evaluates a defeated default as the definite value that defeated
it (Def 16): `f⋆(D⁺) = T`. -/
theorem weight_dplus : weight PRESUP.Dplus = PRESUP.T := by decide

/-- `f⋆(D⁻) = F`. -/
theorem weight_dminus : weight PRESUP.Dminus = PRESUP.F := by decide

/-- `f⋆` maps `PRESUP` onto the seven constants of [ginsberg-1988]'s `DEFAULT`
bilattice (Def 16). -/
theorem weight_mem_default :
    ∀ x : PRESUP, weight x ∈ [PRESUP.U, PRESUP.Pminus, PRESUP.Pplus, PRESUP.C,
      PRESUP.F, PRESUP.T, PRESUP.I] := by
  decide

/-- The weighting is *not* a bilattice homomorphism onto `DEFAULT` (Def 16):
it fails to commute with gullibility `⊕`. -/
theorem weight_not_kSup_hom :
    ¬ ∀ x y : PRESUP, weight (x ⊕ y) = (weight x ⊕ weight y : PRESUP) := by
  decide

end Connectives

end Schoter1996
