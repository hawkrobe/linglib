import Linglib.Theories.Discourse.Centering.Basic

/-!
# Centering Theory — Rule 1 (Pronominalization Constraint) and Variants
@cite{grosz-joshi-weinstein-1995} @cite{gordon-grosz-gilliom-1993}
@cite{poesio-stevenson-eugenio-hitzeman-2004}

@cite{poesio-stevenson-eugenio-hitzeman-2004} §2.3.2 (p. 314-315)
distinguish three versions of Rule 1 from the Centering literature,
each making a different empirical claim about when pronominalization
is required:

- **Rule 1 (GJW 95)**: if any CF in `Cf(U_{i-1})` is pronominalized
  in `U_i`, then `Cb(U_i)` is pronominalized too. The standard
  centering formulation (@cite{grosz-joshi-weinstein-1995} §3).
  *Conditional* on some pronominalization occurring at all.

- **Rule 1 (GJW 83)**: if `Cb(U_i) = Cb(U_{i-1})`, a pronoun should
  be used. The earlier Grosz-Joshi-Weinstein 1983 formulation,
  conditioning on CB *stability* across utterances rather than on
  the presence of any pronominalization.

- **Rule 1 (Gordon)**: the CB should always be pronominalized.
  @cite{gordon-grosz-gilliom-1993}'s reading-time experiments
  motivate this stronger claim — they observe a "repeated-name
  penalty" (RNP) when an entity that should be CB is realized as a
  proper name instead of a pronoun. *Unconditional* on the CB.

PSDH's empirical evaluation (Table 8, p. 333) finds:
- Rule 1 (GJW 95): 96.7% of utterances satisfy it under vanilla
- Rule 1 (GJW 83): 81% satisfy it
- Rule 1 (Gordon): only 44.5% satisfy it — far too strong as an
  unconditional claim

Following mathlib's "variants as separate `Prop`s with implications"
pattern (cf. `Convex` / `StrictConvex` / `MidpointConvex`), each
variant is its own predicate with `Decidable` instance, plus
implication theorems where they hold. NOT a `Rule1Variant` enum +
parameterized def — that would obscure the distinct conceptual
content of each version.

This file *extracts* the Rule 1 content from the older `Rules.lean`
(which was a single file mixing Rule 1 and Rule 2). Rule 2 variants
live in the sibling `Rule2.lean`.
-/

set_option autoImplicit false

namespace Discourse.Centering

variable {E R : Type}

-- ════════════════════════════════════════════════════
-- § 1. Rule 1 (GJW 1995) — the standard formulation
-- ════════════════════════════════════════════════════

/-- @cite{grosz-joshi-weinstein-1995} **Rule 1** (the standard /
    "GJW 95" version per @cite{poesio-stevenson-eugenio-hitzeman-2004}
    §2.3.2): if any element of `Cf(U_{i-1})` is realized by a pronoun
    in `U_i`, then `Cb(U_i)` is realized by a pronoun also.

    Vacuously satisfied when no Cb exists. The constraint is
    *conditional* — it says nothing about whether the Cb *must* be
    pronominalized when no other entity is. Rule 1 only constrains
    what happens when pronominalization is used at all.

    PSDH find this version is **robust**: ≤8% of utterances violate it
    across all parameter instantiations they test (Table 8, p. 333). -/
def Rule1GJW95 [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] [Pronominalizes U E]
    (prev : Utterance E R) (cur : U) : Prop :=
  match cb prev cur with
  | none => True
  | some curCb =>
    (∃ e ∈ prev.cf, pronominalizes cur e) → pronominalizes cur curCb

instance Rule1GJW95.decidable [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] [Pronominalizes U E]
    (prev : Utterance E R) (cur : U) :
    Decidable (Rule1GJW95 prev cur) := by
  unfold Rule1GJW95
  cases cb prev cur <;> infer_instance

-- ════════════════════════════════════════════════════
-- § 2. Rule 1 (GJW 1983) — conditional on CB stability
-- ════════════════════════════════════════════════════

/-- @cite{grosz-joshi-weinstein-1995} report this earlier
    @cite{poesio-stevenson-eugenio-hitzeman-2004} §2.3.2 (p. 314)
    formulation: "If the CB of the current utterance is the same as
    the CB of the previous utterance, a pronoun should be used."

    Conditional on **CB stability** across the utterance pair. The
    `prevCb` parameter is the CB of `prev` (the "previous" CB, which
    requires a further-back utterance to compute via the standard
    `cb prevPrev prev`); we take it as an explicit `Option E`
    parameter rather than recomputing it, mirroring how
    `classifyTransitionExtended` takes `prevCb` explicitly.

    PSDH Table 8 p. 333: 81% of vanilla-instantiation utterances
    satisfy this version. -/
def Rule1GJW83 [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] [Pronominalizes U E]
    (prev : Utterance E R) (cur : U) (prevCb : Option E) : Prop :=
  match cb prev cur with
  | none => True
  | some curCb =>
    if prevCb = some curCb then pronominalizes cur curCb else True

instance Rule1GJW83.decidable [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] [Pronominalizes U E]
    (prev : Utterance E R) (cur : U) (prevCb : Option E) :
    Decidable (Rule1GJW83 prev cur prevCb) := by
  unfold Rule1GJW83
  cases cb prev cur <;> infer_instance

-- ════════════════════════════════════════════════════
-- § 3. Rule 1 (Gordon, Grosz, Gilliom 1993) — unconditional
-- ════════════════════════════════════════════════════

/-- @cite{gordon-grosz-gilliom-1993} formulation per
    @cite{poesio-stevenson-eugenio-hitzeman-2004} §2.3.2 (p. 315):
    "The CB should be pronominalized." Unconditional on the
    presence of pronominalization in `U_i`.

    Motivated by the **repeated-name penalty** (RNP):
    @cite{gordon-grosz-gilliom-1993}'s reading-time experiments
    found increased reading times when proper names were used to
    realize entities that should have been the CB. Gordon et al.
    take this as evidence that the CB *should* be a pronoun, not
    just *may* be one when other entities are.

    PSDH find this version is *much* too strong: only 44.5% of
    vanilla-instantiation utterances satisfy it (Table 8 p. 333) —
    by far the most-violated of the three Rule 1 variants. -/
def Rule1Gordon [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] [Pronominalizes U E]
    (prev : Utterance E R) (cur : U) : Prop :=
  match cb prev cur with
  | none => True
  | some curCb => pronominalizes cur curCb

instance Rule1Gordon.decidable [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] [Pronominalizes U E]
    (prev : Utterance E R) (cur : U) :
    Decidable (Rule1Gordon prev cur) := by
  unfold Rule1Gordon
  cases cb prev cur <;> infer_instance

-- ════════════════════════════════════════════════════
-- § 4. Implication theorems
-- ════════════════════════════════════════════════════

/-- **Gordon ⇒ GJW 95** (unconditional). If the CB is always
    pronominalized (Gordon), then certainly whenever some CF is
    pronominalized, the CB is too (GJW 95). The implication is
    one-directional: GJW 95 has cases not covered by Gordon
    (specifically, the "no pronouns at all" case where GJW 95 is
    vacuously satisfied but Gordon is violated).

    Corollary: the empirical Gordon-violation rate is an *upper bound*
    on the GJW 95 violation rate — consistent with PSDH Table 8 (44.5%
    Gordon-satisfying ≤ 96.7% GJW 95-satisfying, equivalently
    55.5% Gordon-violating ≥ 3.3% GJW 95-violating). -/
theorem Rule1Gordon_implies_GJW95 [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] [Pronominalizes U E]
    {prev : Utterance E R} {cur : U}
    (h : Rule1Gordon prev cur) : Rule1GJW95 prev cur := by
  unfold Rule1Gordon at h
  unfold Rule1GJW95
  cases hcb : cb prev cur with
  | none => trivial
  | some curCb =>
    rw [hcb] at h
    intro _
    exact h

end Discourse.Centering
