import Mathlib.Data.Set.Basic
import Linglib.Semantics.Tense.Pronoun
import Linglib.Semantics.Quantification.Basic
import Linglib.Semantics.Reference.Nominal

/-!
# Tense as a typed lexical object

[sharvit-2014] argues tense comes in two cross-linguistic semantic types ((30), p. 274):
*pronominal* (after [partee-1973]; an element of `D_i`) and *quantificational* (a Priorean
operator over time-predicates). They diverge on past-under-past in *before*-clauses, where
quantificational past triggers Inherent Presupposition Failure under [beaver-condoravdi-2003]'s
`before` (`Tense.TemporalConnectives.Before`); the cross-linguistic typology ((98), (99)) is
in `Studies.Sharvit2014`.

## Main definitions

* `Tense.LexicalType` — pronominal vs quantificational tense.
* `Tense.pronominalLookup` — the pronominal-past partial lookup ((30a)).
* `Tense.quantificationalPast` — the quantificational past, the GQ `some` over `K` ((30b)).
-/

namespace Tense

/-- [sharvit-2014]'s two semantic types of tense ((30)). -/
inductive LexicalType
  /-- Pronominal: an element of `D_i`, two-indexed `past_{j,k}`. -/
  | pronominal
  /-- Quantificational: an operator over time-predicates. -/
  | quantificational
  deriving DecidableEq, Repr

/-- The two semantic types are distinct. ([sharvit-2014]'s language-level no-mixing
    constraint — a language has tenses of just one type — lives in `Studies.Sharvit2014`.) -/
theorem LexicalType.pronominal_ne_quantificational :
    LexicalType.pronominal ≠ LexicalType.quantificational :=
  nofun

/-- [sharvit-2014] (30a): pronominal-past lookup `[[past_{j,k}]]^g`. Indices `j`
    (evaluation), `k` (referential); defined iff `g k < g j`, then `g k`. Uses `Option`
    (not `Part`/`PFun`) as the domain is decidable; the shape is `Option.guard`. -/
def pronominalLookup {Time : Type*} [LT Time] [DecidableLT Time]
    (g : ℕ → Time) (j k : ℕ) : Option Time :=
  if g k < g j then some (g k) else none

/-- The pronominal past denotes the referential index when defined. -/
@[simp]
theorem pronominalLookup_eq_some_iff {Time : Type*} [LT Time]
    [DecidableLT Time] (g : ℕ → Time) (j k : ℕ) (t : Time) :
    pronominalLookup g j k = some t ↔ g k < g j ∧ g k = t := by
  unfold pronominalLookup; split <;> simp_all

/-- The pronominal past is undefined exactly when the constraint fails. -/
@[simp]
theorem pronominalLookup_eq_none_iff {Time : Type*} [LT Time]
    [DecidableLT Time] (g : ℕ → Time) (j k : ℕ) :
    pronominalLookup g j k = none ↔ ¬ g k < g j := by
  unfold pronominalLookup; split <;> simp_all

/-- A tense pronoun is a nominal denotation over `Time` ([partee-1973]): the
    referent selector is the total assignment lookup `resolve`, the intrinsic
    presupposition is the tense constraint. Entity pronouns
    (`Semantics.Reference.PronounDenotation`) are the same `NominalDenot`
    construction over `Entity`, so "tense is a pronoun" holds by construction. -/
def TensePronoun.toNominalDenot {Time : Type*} [LinearOrder Time]
    (tp : TensePronoun) :
    Semantics.Reference.NominalDenot (TemporalAssignment Time) PUnit Time where
  presup := fun g _ => tp.fullPresupposition g
  selector := fun g _ => some (tp.resolve g)

@[simp] theorem TensePronoun.toNominalDenot_presup {Time : Type*} [LinearOrder Time]
    (tp : TensePronoun) (g : TemporalAssignment Time) (w : PUnit) :
    tp.toNominalDenot.presup g w = tp.fullPresupposition g := rfl

@[simp] theorem TensePronoun.toNominalDenot_selector {Time : Type*} [LinearOrder Time]
    (tp : TensePronoun) (g : TemporalAssignment Time) (w : PUnit) :
    tp.toNominalDenot.selector g w = some (tp.resolve g) := rfl

/-- The two codebase formalizations of [partee-1973] pronominal tense coincide:
    `pronominalLookup` is the presupposition-gated referent of the tense pronoun's
    `NominalDenot` (`TensePronoun.toNominalDenot`), for any binding `mode`. -/
theorem pronominalLookup_eq_some_iff_tensePronoun {Time : Type*} [LinearOrder Time]
    (g : TemporalAssignment Time) (j k : ℕ) (t : Time) (mode : TenseInterpretation) :
    pronominalLookup g j k = some t ↔
      (TensePronoun.mk k past mode j).toNominalDenot.presup g ⟨⟩ ∧
      (TensePronoun.mk k past mode j).toNominalDenot.selector g ⟨⟩ = some t := by
  simp only [TensePronoun.toNominalDenot_presup, TensePronoun.toNominalDenot_selector,
    TensePronoun.fullPresupposition, TensePronoun.resolve, TensePronoun.evalTime,
    interpTense, Tense.past, Core.Order.holds_before, Option.some.injEq]
  exact pronominalLookup_eq_some_iff g j k t

/-- [sharvit-2014] (30b): quantificational past as the generalized quantifier
    `some` (`Quantification.some_sem`) over the contextual restrictor `K`,
    with scope "precedes `t` and satisfies `p`". Definitionally
    `∃ t' ∈ K, t' < t ∧ p t'`. -/
def quantificationalPast {Time : Type*} [LT Time]
    (K : Set Time) (p : Time → Prop) (t : Time) : Prop :=
  Quantification.some_sem (· ∈ K) (fun t' => t' < t ∧ p t')

/-- Monotone in the body predicate — inherited from scope-monotonicity of `some`
    (`Quantification.some_scope_up`), not reproved. -/
theorem quantificationalPast_mono {Time : Type*} [LT Time]
    {K : Set Time} {p q : Time → Prop} (h : ∀ t, p t → q t) {t : Time} :
    quantificationalPast K p t → quantificationalPast K q t :=
  Quantification.some_scope_up _ _ _ fun _ hS => ⟨hS.1, h _ hS.2⟩

end Tense
