module

public import Linglib.Syntax.Minimalist.FormCopy

/-!
# Manzini (2026): The FormCopy Theory of Control: Remarks on Landau

Manzini defends the Form Copy theory of control against Landau's challenges by unifying control
with raising: the two have the same derived structure, differing only in the distribution of
theta roles, since Form Copy relates identical inscriptions whatever derivation produced them. A
verb with both construals shows it. Italian *dovere* 'must' is a control verb on its root reading
and a raising verb on its epistemic one (31), and the two parses of *Gianni deve berlo*, one
merging *Gianni* twice and one leaving a copy by Internal Merge, are structurally identical, with
the same pair of positions related by Form Copy (`dovere_transfer`). The unification has a cost
Manzini draws herself: a condition stated on the structure Transfer sees cannot tell the parses
apart (`structural_iff`), so partial control without partial raising must come from the
derivational history (§5.2).

## Implementation notes

The theta roles that separate the parses, two on the root reading and one on the epistemic, are
not represented. The overt controlled pronouns Landau cites are, for Manzini, partial copies of
the controller (fn. 5); Form Copy as defined relates only structurally identical inscriptions,
so they fall outside it (`Landau2024b.pronoun_not_mem_copyRel`).

## References

* [manzini-2026]
* [landau-2024b]
* [chomsky-etal-2023]
-/

@[expose] public section

namespace Manzini2026

open Minimalist SyntacticObject

/-- A token of the simple lexical item of category `c` selecting `sel`, pronounced `pf`. -/
def tok (c : Cat) (sel : SelStack) (pf : String) (i : ℕ) : LIToken :=
  ⟨.simple c sel (phonForm := pf), i⟩

/-- *Gianni*, the matrix subject of (31a). -/
def gianni : SyntacticObject := leaf (tok .N [] "Gianni" 0)

/-- *Gianni* from a fresh token, the embedded subject of the root parse. -/
def gianni' : SyntacticObject := leaf (tok .N [] "Gianni" 3)

/-- *berlo* 'drink it'. -/
noncomputable def berlo : SyntacticObject :=
  merge (leaf (tok .V [.D] "bere" 4)) (leaf (tok .D [] "lo" 5))

/-- The root parse of (31a), a control structure: *Gianni* is merged into the theta positions of
both *dovere* and *bere*. -/
noncomputable def rootParse : SyntacticObject :=
  merge gianni (merge (leaf (tok .V [.V] "deve" 1)) (merge gianni' berlo))

/-- (31a) on the epistemic reading of *dovere* that (31b) shows, a raising structure: *Gianni*
is merged once and its copy left in the embedded subject position by Internal Merge. -/
noncomputable def epistemicParse : SyntacticObject :=
  merge gianni (merge (leaf (tok .V [.V] "deve" 1)) (merge gianni berlo))

/-- The two parses of (31a) coincide at Transfer: they are structurally identical, and Form Copy
relates the matrix subject to the embedded one in each, a repetition in the root parse and the
Internal Merge copy in the epistemic one. -/
theorem dovere_transfer :
    StructurallyIdentical rootParse epistemicParse ∧ (gianni, gianni') ∈ rootParse.copyRel ∧
      (gianni, gianni) ∈ epistemicParse.copyRel :=
  ⟨.merge rfl (.merge rfl (.merge (by simp [gianni, gianni', tok, StructurallyIdentical]) rfl)),
    mk_mem_copyRel_merge (by simp [containsOrEq_iff_eq_or_contains])
      (by simp [gianni, gianni', tok, StructurallyIdentical]),
    self_mem_copyRel_merge (by simp [containsOrEq_iff_eq_or_contains])⟩

/-- A condition on the structure Transfer sees holds of the root parse exactly when it holds of
the epistemic one, so what separates control from raising, partial control among it, must be read
off the derivation (§5.2). -/
theorem structural_iff (P : SyntacticObject → Prop)
    (hP : ∀ a b, StructurallyIdentical a b → (P a ↔ P b)) : P rootParse ↔ P epistemicParse :=
  hP _ _ dovere_transfer.1

end Manzini2026
