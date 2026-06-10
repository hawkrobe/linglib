import Linglib.Core.Logic.Modal.QBSML.Defs

/-!
# Pragmatic enrichment for QBSML

[aloni-vanormondt-2023] [aloni-2022]

The first-order extension of BSML's pragmatic enrichment function `[·]⁺`
([aloni-2022] Definition 6), adding quantifier cases. Per
[aloni-vanormondt-2023] Definition 4.13, `[·]⁺` recursively inserts
`NE` conjuncts into every clause of an NE-free formula:

    [Pt₁...tₙ]⁺  =  Pt₁...tₙ ∧ NE
    [¬φ]⁺        =  ¬[φ]⁺ ∧ NE
    [φ ∧ ψ]⁺     =  ([φ]⁺ ∧ [ψ]⁺) ∧ NE
    [φ ∨ ψ]⁺     =  ([φ]⁺ ∨ [ψ]⁺) ∧ NE
    [◇φ]⁺        =  ◇[φ]⁺ ∧ NE
    [∃xφ]⁺       =  ∃x[φ]⁺ ∧ NE
    [∀xφ]⁺       =  ∀x[φ]⁺ ∧ NE

(`□` is derived as `¬◇¬`, so it carries no separate enrichment clause here.)

The intuition ([aloni-2022]'s "neglect-zero" hypothesis): conversational
participants systematically ignore empty configurations when interpreting,
so each clause must witness a non-empty state. Combined with split
disjunction, this derives ignorance, distribution, free choice, and the
behaviour-under-negation pattern — the QBSML free-choice facts proved in
`Studies/AloniVanOrmondt2023/FreeChoice.lean` (`narrowScopeFC_Q`,
`negationStrip_Q`).

## Main declarations

* `QBSMLFormula.enrich` — the enrichment function `[·]⁺`.
* `enriched_support_implies_nonempty` — a state supporting an enriched
  formula is non-empty (the `NE` conjunct guards every clause).
* `antiSupport_strip_ne`, `antiSupport_conj_ne_iff` — anti-support of
  `φ ∧ NE` reduces to anti-support of `φ`; the workhorse of the free-choice
  derivations in `Studies/AloniVanOrmondt2023/FreeChoice.lean`.

## Implementation notes

`enrich` is total on `QBSMLFormula` for definitional convenience, but `[·]⁺`
is defined only on the NE-free fragment in both papers, so the `.ne` case is
a filler convention. The construction is structurally identical to BSML's
`Core/Logic/Modal/BSML/Enrichment.lean` but operates on `QBSMLFormula Var Pred`
(quantifiers, predicate atoms) rather than `BSMLFormula Atom`. The two are
kept parallel rather than unified: a shared "team-semantic formula language
with an `NE` constructor" abstraction awaits a third instance, per the family
roadmap in `Core/Logic/Team/Algebra.lean`.
-/

namespace Core.Logic.Modal.QBSML

variable {Var Pred : Type*}

/-! ### The enrichment function -/

/-- Pragmatic enrichment `[·]⁺` for QBSML formulas ([aloni-vanormondt-2023]
    Definition 4.13). Recursively conjoins `NE` to every clause. -/
def QBSMLFormula.enrich : QBSMLFormula Var Pred → QBSMLFormula Var Pred
  | .pred P x   => .conj (.pred P x) .ne
  | .ne         => .ne  -- totality filler; enrichment is defined only on the NE-free fragment
  | .neg φ      => .conj (.neg φ.enrich) .ne
  | .conj φ ψ   => .conj (.conj φ.enrich ψ.enrich) .ne
  | .disj φ ψ   => .conj (.disj φ.enrich ψ.enrich) .ne
  | .poss φ     => .conj (.poss φ.enrich) .ne
  | .exi x φ    => .conj (.exi x φ.enrich) .ne
  | .univ x φ   => .conj (.univ x φ.enrich) .ne

/-! ### Enriched support forces non-emptiness -/

variable {W Domain : Type*}
variable [DecidableEq W]
variable [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain]

/-- A QBSML state supporting an enriched formula must be non-empty. The NE
    conjunct guards every clause of `enrich φ`, forcing the witnessing state
    to satisfy `Nonempty`. -/
theorem enriched_support_implies_nonempty (M : QBSMLModel W Domain Pred)
    (φ : QBSMLFormula Var Pred) (s : Finset (Index W Var Domain))
    (h : support M φ.enrich s) : s.Nonempty := by
  cases φ with
  | ne => exact h
  | _  => exact h.2

/-! ### Stripping NE from anti-support -/

/-- Anti-support of `φ ∧ NE` implies anti-support of `φ`. The split partitions
    the state as `t₁ ∪ t₂` with `antiSupport NE t₂` forcing `t₂ = ∅`, hence
    `t₁ = s`. The QBSML analogue of `BSML/Enrichment`'s `antiSupport_strip_ne`;
    the workhorse of the free-choice derivations in
    `Studies/AloniVanOrmondt2023/FreeChoice.lean`. -/
theorem antiSupport_strip_ne (M : QBSMLModel W Domain Pred)
    (φ : QBSMLFormula Var Pred) (s : Finset (Index W Var Domain))
    (h : antiSupport M (.conj φ .ne) s) :
    antiSupport M φ s := by
  obtain ⟨t₁, t₂, hunion, h₁, h₂⟩ := h
  -- h₂ : t₂ = ∅, so t₁ = s
  subst h₂
  have heq : t₁ = s := (Finset.union_empty t₁).symm.trans hunion
  subst heq; exact h₁

/-- Anti-support of `φ` implies anti-support of `φ ∧ NE` via the trivial
    split `(s, ∅)`. The reverse direction of `antiSupport_strip_ne`. -/
theorem antiSupport_conj_ne_of_antiSupport (M : QBSMLModel W Domain Pred)
    (φ : QBSMLFormula Var Pred) (s : Finset (Index W Var Domain))
    (h : antiSupport M φ s) :
    antiSupport M (.conj φ .ne) s :=
  ⟨s, ∅, Core.Logic.Team.splitsAs_self_empty s, h, rfl⟩

/-- Anti-support of `φ ∧ NE` ↔ anti-support of `φ`. -/
theorem antiSupport_conj_ne_iff (M : QBSMLModel W Domain Pred)
    (φ : QBSMLFormula Var Pred) (s : Finset (Index W Var Domain)) :
    antiSupport M (.conj φ .ne) s ↔ antiSupport M φ s :=
  ⟨antiSupport_strip_ne M φ s, antiSupport_conj_ne_of_antiSupport M φ s⟩

end Core.Logic.Modal.QBSML
