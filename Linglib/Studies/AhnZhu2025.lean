/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.ArgumentStructure.Relational
import Linglib.Features.Definiteness
import Linglib.Studies.Jenks2018
import Linglib.Data.Examples.AhnZhu2025

/-!
# Ahn & Zhu (2025): A bridge to definiteness
[ahn-zhu-2025]

Mandarin lacks a definite article; it marks definiteness with **bare nouns** and
with **demonstrative descriptions** (*na*-CL-N). [ahn-zhu-2025] use *bridging* —
the licensing of a definite whose referent was not introduced in the context — to
probe which mechanism underlies each form, and propose that the demonstrative
*na* is a **relationalizing definite**.

## The analysis (eq. 48, eq. 44a)

The paper's denotations are built on [schwarz-2009]'s situation-semantic definite
article and [jenks-2018]'s ι type-shifter; [barker-2011]'s relationalizer `π` and
detransitivizer `Ex` (and [vikner-jensen-2002]'s `Prag`) supply the relational
sub-component. Writing `sᵣ` for the resource situation:

* bare definite (eq. 44a): `⟦bare P⟧ = λsᵣ. ιx[P(x)(sᵣ)]` — the unique `P` in `sᵣ`
  (situational uniqueness; Schwarz-weak).
* *na* definite (eq. 48): `⟦na P⟧ = λsᵣ. λz. ιx[π(P)(z)(x)(sᵣ)] = ιx[P(x)(sᵣ) ∧ R(z,x)(sᵣ)]`
  — the unique `x` that is `P` **and** bears the contextual relation `R` to the
  index `z`. Here `ι` (uniqueness) is the *definiteness*; `π` (relationalization)
  is what *na* adds.

## Layered grounding

This file is a thin consumer of `Semantics/ArgumentStructure/Relational.lean`
(Barker's `π`, `Ex`, `iotaPresupposition`, `naSemantics`, `bareSemantics`,
`CanFillRelatum`). It does **not** re-implement them. `ι` is modelled by the
substrate's `iotaPresupposition` (the existence-and-uniqueness presupposition a
definite carries); the felicity of a definite is the holding of that
presupposition.

## Main results

* `na_restores_uniqueness` — the keystone. When a sortal noun `P` is *not*
  situationally unique (≥ 2 satisfiers), the bare definite's uniqueness
  presupposition fails, but adding `R(z, ·)` via `π` (= *na*) narrows the
  extension to a singleton, so the *na* definite is felicitous. The bridging
  asymmetry is a consequence of `π` restoring uniqueness, not a stipulation.
* `relational_bare_felicitous` — a lexically relational noun supplies its own
  relatum (eq. 57–58: covert possessor / Mandarin argument-drop), so bare bridging
  is licensed without *na*.
* `bridge_licensed_iff` — the Study-4 2×2 as a derived fact over the substrate's
  `CanFillRelatum`: relational bridging is licensed iff *na* applies **or** the
  noun is lexically relational (i.e. fails exactly at bare + non-relational).
* `diverges_from_jenks_on_bare_relational` — [ahn-zhu-2025] vs [jenks-2018]: Ahn &
  Zhu license bare relational bridging, whereas Jenks's `Index!` (Maximize
  Presupposition) strictly prefers the indexed *na* form whenever an antecedent is
  available. The two accounts assign opposite status to the bare relational cell.
-/

namespace AhnZhu2025

open ArgumentStructure.Relational
open Features.Definiteness

variable {E S : Type*}

/-! ### The two definite-forming routes (eq. 44a, eq. 48) -/

/-- Felicity of a **bare** definite (eq. 44a): the uniqueness presupposition of
the noun alone. *bare P* denotes the unique `x` with `P x` in `s` — situational
uniqueness (Schwarz-weak / [jenks-2018]'s ι). -/
def bareDefiniteFelicitous (P : Pred1 E S) (s : S) : Prop :=
  iotaPresupposition (bareSemantics P) s

/-- Felicity of a **na** definite (eq. 48): the uniqueness presupposition of the
relationalized predicate `π P R`. *na P* (with index `z`) denotes the unique `x`
with `P x ∧ R z x` in `s`. The `ι` is the definiteness; the `π` is what *na*
adds. -/
def naDefiniteFelicitous (P : Pred1 E S) (R : Pred2 E S) (z : E) (s : S) : Prop :=
  iotaPresupposition (naSemantics P R z) s

/-! ### The relationalizer restores uniqueness -/

/-- **Keystone.** A sortal noun `P` that is *not* situationally unique (two
distinct satisfiers) cannot head a bare definite — its uniqueness presupposition
fails. But *na* conjoins the contextual relation `R(z, ·)` via `π`, and if that
narrows the extension to a singleton, the *na* definite **is** felicitous.

This is [ahn-zhu-2025]'s bridging asymmetry *derived* from the denotations: the
gap between bare and *na* is `π` restoring the `ι` presupposition, not a
stipulation. -/
theorem na_restores_uniqueness
    (P : Pred1 E S) (R : Pred2 E S) (z : E) (s : S)
    (hAmbiguous : ∃ a b, a ≠ b ∧ P a s ∧ P b s)
    (hDisambiguated : ∃! x, P x s ∧ R z x s) :
    ¬ bareDefiniteFelicitous P s ∧ naDefiniteFelicitous P R z s := by
  refine ⟨?_, ?_⟩
  · rintro ⟨x, _, huniq⟩
    obtain ⟨a, b, hab, ha, hb⟩ := hAmbiguous
    exact hab ((huniq a ha).trans (huniq b hb).symm)
  · obtain ⟨x, hx, huniq⟩ := hDisambiguated
    exact ⟨x, hx, huniq⟩

/-- A lexically **relational** noun (a `Pred2`) supplies its own relatum: with the
antecedent `z` filling the internal argument (eq. 57–58: covert possessor /
Mandarin argument-drop), the bare definite's uniqueness presupposition can be met
without *na*. This is why bare relational bridging is licensed. -/
theorem relational_bare_felicitous
    (Rel : Pred2 E S) (z : E) (s : S)
    (hUnique : ∃! x, Rel z x s) :
    bareDefiniteFelicitous (fun x => Rel z x) s := by
  obtain ⟨x, hx, huniq⟩ := hUnique
  exact ⟨x, hx, huniq⟩

/-! ### The bridging asymmetry as `InterpretationSource` (Study 4) -/

/-- The interpretation source of a bridged definite, *computed* from whether the
noun is lexically relational and whether *na* (`π`) applies. The source is
derived, not stipulated: it is the substrate's `InterpretationSource`. -/
def bridgeSource (lexicallyRelational naApplies : Bool) : InterpretationSource :=
  if naApplies then .appliedPi
  else if lexicallyRelational then .lexicalRelation
  else .noRelation

/-- **Study 4, derived.** Relational bridging is licensed (`CanFillRelatum`)
exactly when *na* applies **or** the noun is lexically relational — i.e. it fails
only in the bare + non-relational cell. This is the 2×2 that [ahn-zhu-2025]'s
Study 4 confirms, read off the computed `InterpretationSource`. -/
theorem bridge_licensed_iff (lexRel naApp : Bool) :
    CanFillRelatum (bridgeSource lexRel naApp) ↔ (naApp = true ∨ lexRel = true) := by
  cases naApp <;> cases lexRel <;> simp [bridgeSource, CanFillRelatum]

/-- The decisive Study-4 cell: a **bare, non-relational** noun cannot relationally
bridge — no *na*, no lexical relation, so no relatum slot. -/
theorem bare_nonrelational_cannot_bridge :
    ¬ CanFillRelatum (bridgeSource false false) := by
  simp [bridgeSource, CanFillRelatum]

/-! ### Shared bridging split ([schwarz-2009] / [jenks-2018]) -/

/-- [ahn-zhu-2025] inherit Schwarz's bridging split, shared with [jenks-2018] via
the common `Features.Definiteness.bridgingPresupType`: part-whole bridging is the
uniqueness route (bare ι; bare nouns suffice), relational bridging the familiarity
route (the relatum index; *na* or a lexical relation). -/
theorem inherits_schwarz_bridging_split :
    bridgingPresupType .partWhole = .uniqueness ∧
    bridgingPresupType .relational = .familiarity :=
  ⟨rfl, rfl⟩

/-! ### Divergence from [jenks-2018] -/

/-- **Divergence from [jenks-2018]** (the comparison [ahn-zhu-2025] §4 draws).

Ahn & Zhu license a **bare** relational definite: a lexically relational noun
supplies its own relatum, so the uniqueness presupposition is met without *na*
(`relational_bare_felicitous`).

[jenks-2018]'s `Index!` (a Maximize-Presupposition instance) instead requires the
indexed *na* form **whenever an antecedent is available** — so it strictly
disprefers the bare form in exactly this cell (`Jenks2018.index_prefers_indexed_when_available`).

The two accounts thus assign opposite status to the bare relational-bridging form:
Ahn & Zhu predict it licensed; Jenks predicts it blocked. Both halves below are
derived from each account's own machinery. -/
theorem diverges_from_jenks_on_bare_relational
    (Rel : Pred2 E S) (z : E) (s : S) (hUnique : ∃! x, Rel z x s) :
    -- Ahn & Zhu: bare relational definite is felicitous (no *na* needed)
    bareDefiniteFelicitous (fun x => Rel z x) s ∧
    -- Jenks: Index! strictly prefers the indexed *na* form when an antecedent exists
    Jenks2018.indexConstraint { isIndexed := true,  indexAvailable := true } <
      Jenks2018.indexConstraint { isIndexed := false, indexAvailable := true } :=
  ⟨relational_bare_felicitous Rel z s hUnique,
   Jenks2018.index_prefers_indexed_when_available⟩

/-! ### Data: the bridging felicity rows (`Data/Examples/AhnZhu2025.json`) -/

section Data

open Data.Examples

/-- Value of a `paperFeatures` key, if present. -/
private def featureOf (row : LinguisticExample) (key : String) : Option String :=
  (row.paperFeatures.find? (·.1 == key)).map (·.2)

/-- *na*-CL is acceptable in every condition (both bridging types, both noun
types) — *na* itself is the relationalizer, so it always supplies the relatum
slot (`bridge_licensed_iff`, `naApp = true`). -/
theorem naCL_rows_acceptable :
    ∀ row ∈ Examples.all, featureOf row "definite_form" = some "naCL" →
      row.judgment = .acceptable := by decide

/-- Bare + **relational** noun bridges (Study 4): the lexically 2-place noun
supplies its own relatum (`relational_bare_felicitous`). -/
theorem bare_relational_noun_bridges :
    ∀ row ∈ Examples.all,
      featureOf row "definite_form" = some "bare" →
      featureOf row "bridging_type" = some "relational" →
      featureOf row "noun_arity" = some "relational" →
      row.judgment = .acceptable := by decide

/-- **The decisive Study-4 cell.** Bare + **non-relational** noun in relational
bridging is degraded — a bare noun licenses relational bridging *only* if the noun
is lexically relational (`bare_nonrelational_cannot_bridge`). Marginal, not out:
the cell is rated below its rivals but not at floor. -/
theorem bare_nonrelational_noun_degraded :
    ∀ row ∈ Examples.all,
      featureOf row "definite_form" = some "bare" →
      featureOf row "bridging_type" = some "relational" →
      featureOf row "noun_arity" = some "sortal" →
      row.judgment = .marginal := by decide

/-- English demonstrative *that* is **degraded but not ungrammatical** in bridging
(Study 2): economy-blocked because the definite competes, not a hard constraint.
Modelled as `.marginal` (the paper's gradient ~4.3–5.0/7 finding), in contrast to
English *the*, which is acceptable. -/
theorem english_that_degraded :
    ∀ row ∈ Examples.all, featureOf row "definite_form" = some "that" →
      row.judgment = .marginal := by decide

/-- English definite *the* bridges freely (Study 2 baseline). -/
theorem english_the_acceptable :
    ∀ row ∈ Examples.all, featureOf row "definite_form" = some "the" →
      row.judgment = .acceptable := by decide

end Data

end AhnZhu2025
