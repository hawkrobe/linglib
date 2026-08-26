import Linglib.Semantics.Possessive.Basic
import Linglib.Studies.Jenks2018
import Linglib.Data.Examples.AhnZhu2025

/-!
# Bridging with Mandarin bare nouns and demonstratives

Mandarin marks definiteness with bare nouns and with *na*-CL-N demonstrative descriptions. Ahn
and Zhu probe which mechanism each form carries through bridging, a definite whose referent was
never mentioned: part-whole bridging is resolvable by situational uniqueness, relational bridging
needs an anaphoric relatum. Four studies find that both forms bridge both ways, with a preference
for bare nouns in part-whole bridging; that English *that* is degraded where *na* is not; and,
decisively, that a bare noun bridges relationally only when the noun is lexically relational
(*zuozhe* 'author' but not *xiaoshuo-jia* 'novelist'), while *na* bridges with either. Neither an
anti-uniqueness presupposition on *na* nor an Index! principle forcing the indexed form whenever
an antecedent is available survives the data.

The analysis keeps the uniqueness ι for the bare noun and re-analyses *na* as a relationalizing
definite whose restrictor is the π-shifted noun, `ιx[P(x)(sᵣ) ∧ R(z,x)(sᵣ)]` for a contextual
relation `R` and an index `z`. That restrictor is `Possessive.viaModifier z P R` (`na`); a
relational noun with its relatum dropped is `Possessive.viaArgument z Rel`; felicity is the
substrate's `iotaPresupposition`. `na_of_two_satisfiers` shows the relation restoring uniqueness
where the bare ι fails, `na_identity_iff` recovers the strong article as the identity-relation
case, and `na_iff_bare_of_related` isolates the situations where `R` is redundant and the two
forms compete on economy, which covers part-whole bridging (`na_seat_redundant`) and the moon.
The Study 4 item runs through both routes: the bare non-relational noun fails
(`bare_novelist_fails`) while `na_novelist`, `bare_author` and `na_ex_author` each pick the
author. `index_contradicted_by_bare_relational` states the comparison drawn with Index!, and the
closing theorems check the Studies' rows: *na* bridges everywhere (`na_bridges`), the bare noun
bridges relationally exactly with a relational noun (`bare_relational_iff_lexical`), English
*that* is never fully acceptable in bridging (`that_degraded`), and the *of* and *de*
diagnostics classify the nouns (`of_iff_relational`, `de_of_relational`).

## References

* [ahn-zhu-2025]
* [barker-2011]
* [jenks-2018]
* [schwarz-2009]
* [dayal-jiang-2023]
* [bremmers-etal-2022]
* [vikner-jensen-2002]
-/

namespace AhnZhu2025

open ArgumentStructure.Relational Possessive

variable {E S : Type*} (P : E → S → Prop) (R : E → E → S → Prop) (z : E) (s : S)

/-! ### Bare nouns and *na* -/

/-- The *na* restrictor `na P R z x s ↔ P x s ∧ R z x s`: the noun relationalized by `π` with
the index `z` in the relatum slot; the definite `ιx[P(x)(sᵣ) ∧ R(z,x)(sᵣ)]` is its
`iotaPresupposition`. -/
abbrev na : E → S → Prop := viaModifier z P R

/-- Two satisfiers of the noun defeat the bare noun's uniqueness presupposition; the relation to
the index can restore it. -/
theorem na_of_two_satisfiers (h : ∃ a b, a ≠ b ∧ P a s ∧ P b s) (hR : ∃! x, P x s ∧ R z x s) :
    ¬ iotaPresupposition P s ∧ iotaPresupposition (na P R z) s :=
  ⟨fun ⟨_, _, hu⟩ => let ⟨_, _, hab, ha, hb⟩ := h; hab ((hu _ ha).trans (hu _ hb).symm), hR⟩

/-- With the identity relation *na* is the strong article: felicitous iff the indexed entity is
`P`. -/
theorem na_identity_iff : iotaPresupposition (na P (fun a b _ => a = b) z) s ↔ P z s :=
  ⟨fun ⟨_, ⟨h, hz⟩, _⟩ => hz ▸ h, fun h => ⟨z, ⟨h, rfl⟩, fun _ hy => hy.2.symm⟩⟩

/-- When every `P` in `s` bears `R` to the index, the relation is redundant: *na* and the bare
noun have the same extension. -/
theorem na_iff_bare_of_related (h : ∀ x, P x s → R z x s) (x : E) : na P R z x s ↔ P x s :=
  ⟨And.left, fun hx => ⟨hx, h x hx⟩⟩

theorem iotaPresupposition_na_iff (h : ∀ x, P x s → R z x s) :
    iotaPresupposition (na P R z) s ↔ iotaPresupposition P s :=
  existsUnique_congr (na_iff_bare_of_related P R z s h)

/-! ### Part-whole bridging: bike and seat -/

/-- The bike and its seat. -/
inductive Thing | bike | seat
  deriving DecidableEq

/-- *chezuo* 'seat'. -/
def seat : Thing → Unit → Prop := fun x _ => x = .seat

/-- `partOf z x`: `x` is a part of `z`. -/
def partOf : Thing → Thing → Unit → Prop := fun z x _ => z = .bike ∧ x = .seat

/-- The bare *chezuo* picks the unique seat of the situation. -/
theorem bare_seat : iotaPresupposition seat () := ⟨.seat, rfl, fun _ h => h⟩

/-- *na ge chezuo* with `R` resolved to part-of has the same extension as the bare noun, so the
demonstrative's restriction is redundant and economy prefers the bare noun. -/
theorem na_seat_redundant (x : Thing) : na seat partOf .bike x () ↔ seat x () :=
  na_iff_bare_of_related seat partOf .bike () (fun _ h => ⟨rfl, h⟩) x

/-! ### Relational bridging: the novel, its author, and another novelist -/

/-- The novel found, its author, and another novelist. -/
inductive Ind | theNovel | itsAuthor | anotherNovelist
  deriving DecidableEq

/-- *xiaoshuo-jia* 'novelist', a sortal noun true of both novelists. -/
def novelist : Ind → Unit → Prop := fun x _ => x = .itsAuthor ∨ x = .anotherNovelist

/-- *zuozhe* 'author': `author z x` holds when `x` is an author of `z`. -/
def author : Ind → Ind → Unit → Prop := fun z x _ => z = .theNovel ∧ x = .itsAuthor

/-- The bare non-relational noun has no relatum slot, and situational uniqueness fails with two
novelists. -/
theorem bare_novelist_fails : ¬ iotaPresupposition novelist () := by
  rintro ⟨x, -, hu⟩
  exact absurd ((hu _ (Or.inl rfl)).trans (hu _ (Or.inr rfl)).symm) (by decide)

/-- *na wei xiaoshuo-jia*: the demonstrative supplies the relatum, and `R` resolved to authorship
picks the author. -/
theorem na_novelist : iotaPresupposition (na novelist author .theNovel) () :=
  ⟨.itsAuthor, ⟨Or.inl rfl, rfl, rfl⟩, fun _ hy => hy.2.2⟩

/-- The bare *zuozhe* with its relatum argument covertly filled by the novel. -/
theorem bare_author : iotaPresupposition (viaArgument .theNovel author) () :=
  ⟨.itsAuthor, ⟨rfl, rfl⟩, fun _ hy => hy.2⟩

/-- *na wei zuozhe*: the relational noun detransitivized by `Ex` and re-relationalized by *na*. -/
theorem na_ex_author : iotaPresupposition (na (ExPossessor author) author .theNovel) () :=
  ⟨.itsAuthor, ⟨⟨.theNovel, rfl, rfl⟩, rfl, rfl⟩, fun _ hy => hy.2.2⟩

/-! ### The Studies' rows -/

/-- *na* is acceptable in every bridging row, part-whole and relational, with sortal and
relational nouns alike. -/
theorem na_bridges :
    ∀ row ∈ Examples.all, row.feature? "definite_form" = some "naCL" →
      row.feature? "bridging_type" ≠ some "none" → row.judgment = .acceptable := by decide

theorem bare_partWhole :
    ∀ row ∈ Examples.all, row.feature? "definite_form" = some "bare" →
      row.feature? "bridging_type" = some "partWhole" → row.judgment = .acceptable := by decide

/-- A bare noun bridges relationally exactly when the noun is lexically relational. -/
theorem bare_relational_iff_lexical :
    ∀ row ∈ Examples.all, row.feature? "definite_form" = some "bare" →
      row.feature? "bridging_type" = some "relational" →
      (row.judgment = .acceptable ↔ row.feature? "noun_arity" = some "relational") := by decide

/-- Index! ranks the indexed form strictly above the bare one whenever an antecedent is
available, predicting complementary distribution; the bare noun is nonetheless acceptable with
every relational noun in the relational-bridging rows. -/
theorem index_contradicted_by_bare_relational :
    Jenks2018.indexConstraint ⟨true, true⟩ < Jenks2018.indexConstraint ⟨false, true⟩ ∧
    ∀ row ∈ Examples.all, row.feature? "definite_form" = some "bare" →
      row.feature? "bridging_type" = some "relational" →
      row.feature? "noun_arity" = some "relational" → row.judgment = .acceptable :=
  ⟨Jenks2018.index_prefers_indexed_when_available,
   fun row h h₁ h₂ => (bare_relational_iff_lexical row h h₁ h₂).2⟩

/-- English *that* is never fully acceptable in a bridging row, while its deferred deictic use
is. -/
theorem that_degraded :
    ∀ row ∈ Examples.all, row.feature? "definite_form" = some "that" →
      row.feature? "bridging_type" ≠ some "none" → row.judgment ≠ .acceptable := by decide

theorem the_acceptable :
    ∀ row ∈ Examples.all, row.feature? "definite_form" = some "the" →
      row.judgment = .acceptable := by decide

/-- The English *of*-possessive classifies the nouns: it is grammatical exactly with a relational
noun. -/
theorem of_iff_relational :
    ∀ row ∈ Examples.all, row.feature? "diagnostic" = some "of" →
      (row.judgment = .acceptable ↔ row.feature? "noun_arity" = some "relational") := by decide

/-- Mandarin *de* admits every relational noun; the converse fails, since the sortal *hua*
'flower' passes too. -/
theorem de_of_relational :
    ∀ row ∈ Examples.all, row.feature? "diagnostic" = some "de" →
      row.feature? "noun_arity" = some "relational" → row.judgment = .acceptable := by decide

end AhnZhu2025
