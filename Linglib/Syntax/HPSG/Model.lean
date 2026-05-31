import Linglib.Syntax.HPSG.Description
import Linglib.Syntax.HPSG.Basic

/-!
# A worked HPSG signature, the Head Feature Principle, and a computational bridge
@cite{richter-2000}, @cite{richter-2024}, @cite{pollard-sag-1994}

A small HPSG signature fragment in the RSRL substrate (`Signature.lean`, `Interpretation.lean`,
`Description.lean`), the **Head Feature Principle** as a description, worked head-complement
models showing the principle is a genuine constraint (one satisfying, one violating it), and a
lemma relating the project's *computational* HPSG core (`HPSG.HeadCompRule.hfp`) to a sort-level
description in the induced model — a deliberately partial bridge (the grammar's HFP is token
identity, which value equality does not entail; see below).

## Main declarations

* `HPSG.RSRL.hpsgSig` — a minimal HPSG signature over the sort hierarchy `HSort`, with
  attributes `CAT`/`HD` and appropriateness `happrop`.
* `HPSG.RSRL.hfp` / `hpsgGrammar` — the Head Feature Principle and the one-principle grammar.
* `HPSG.RSRL.posModel` / `negModel` — head-complement structures that satisfy / violate the
  HFP (both well-typed): the principle filters.
* `HPSG.RSRL.toInterp_categoryAgreement_of_hfp` — from the computational `HeadCompRule.hfp`, the
  induced model satisfies a category sort-agreement description (strictly weaker than the
  grammar's token-identity HFP; see Implementation notes).

## Implementation notes

* **Granularity.** The canonical HFP (@cite{pollard-sag-1994}; @cite{richter-2024}, Ch. 3, (3a))
  shares the **HEAD** value along `SYNSEM|LOC|CAT|HEAD` and is **token identity**. PR1 works at
  the **CAT** granularity along a flattened `CAT`/`HD` path, because that is what the project's
  computational `HPSG.HeadCompRule.hfp` (`result.synsem.cat = head.synsem.cat`) exposes; the
  worked models still use token identity (`pathEq`). Note CAT-sharing is a valence-free
  *fragment stand-in*, not a faithful coarsening: full CAT contains the valence features, so
  sharing all of CAT mother-to-head would wrongly force valence identity (the Valence
  Principle's job). The fragment has no valence attribute, so nothing breaks here; refining to
  the HEAD value under the full feature geometry is later work.
* **The computational bridge is partial.** `toInterp_categoryAgreement_of_hfp` reflects the
  value-equality `HeadCompRule.hfp` only as a sort-agreement, not as the grammar's
  token-identity `pathEq` HFP — value equality and token identity are genuinely different
  notions. A faithful bridge is deferred (see that theorem's docstring).
* Only `hpsgSig` is `@[reducible]` (so its projections resolve in instance search); the models
  are plain `def`s, and the `decide`-checked examples expose their carriers with `unfold`.
-/

namespace HPSG.RSRL

/-! ### A minimal HPSG sort hierarchy and signature -/

/-- Sorts of the worked fragment. `category` generalises the category species
`nounCat`/`verbCat`/`otherCat`; `headedPhrase`/`word` are the sign species. -/
inductive HSort where
  | top | sign | phrase | headedPhrase | word | category | nounCat | verbCat | otherCat
  deriving DecidableEq, Fintype, Repr

/-- Attributes of the worked fragment: `CAT` (a sign's category) and `HD` (the head daughter
of a headed phrase). -/
inductive HAttr where
  | CAT | HD
  deriving DecidableEq, Fintype, Repr

/-- Subsumption as a boolean relation: `hleB a b` is "`a` is at least as specific as `b`". -/
def hleB : HSort → HSort → Bool
  | _, .top => true
  | .word, .sign => true
  | .phrase, .sign => true
  | .headedPhrase, .phrase => true
  | .headedPhrase, .sign => true
  | .nounCat, .category => true
  | .verbCat, .category => true
  | .otherCat, .category => true
  | a, b => decide (a = b)

private theorem hleB_refl : ∀ a, hleB a a = true := by decide
private theorem hleB_trans :
    ∀ a b c, hleB a b = true → hleB b c = true → hleB a c = true := by decide
private theorem hleB_antisymm : ∀ a b, hleB a b = true → hleB b a = true → a = b := by decide

/-- The sort hierarchy as a `PartialOrder` (`a ≤ b` = "`a` at least as specific as `b`"). -/
instance : PartialOrder HSort where
  le a b := hleB a b = true
  le_refl := hleB_refl
  le_trans := hleB_trans
  le_antisymm := hleB_antisymm

instance : DecidableLE HSort := fun a b => inferInstanceAs (Decidable (hleB a b = true))

/-- Appropriateness: `CAT` is appropriate to every sign (value `category`); `HD` to headed
phrases (value `sign`). Categories are attributeless. -/
def happrop : HSort → HAttr → Option HSort
  | .sign, .CAT => some .category
  | .phrase, .CAT => some .category
  | .headedPhrase, .CAT => some .category
  | .word, .CAT => some .category
  | .headedPhrase, .HD => some .sign
  | _, _ => none

private theorem happrop_inh : ∀ (σ₁ σ₂ : HSort) (α : HAttr) (τ₁ : HSort),
    σ₂ ≤ σ₁ → happrop σ₁ α = some τ₁ → ∃ τ₂, happrop σ₂ α = some τ₂ ∧ τ₂ ≤ τ₁ := by decide

/-- The worked HPSG signature. Reducible so its projections (`Attr`, `approp`) resolve in
instance search; the models below are plain `def`s. -/
@[reducible] def hpsgSig : Signature HSort where
  Attr := HAttr
  Rel := Empty
  arity := fun e => e.elim
  approp := happrop
  approp_inherits := fun {σ₁ σ₂ α τ₁} => happrop_inh σ₁ σ₂ α τ₁

/-! ### The Head Feature Principle -/

/-- The **Head Feature Principle** (@cite{pollard-sag-1994}; @cite{richter-2024}, Ch. 3, (3a)),
at CAT granularity: a headed phrase shares its category (path `CAT`) with its head daughter
(path `HD CAT`), as token identity (`pathEq`). -/
def hfp : Desc hpsgSig :=
  .imp (.sortAssign [] .headedPhrase) (.pathEq [.CAT] [.HD, .CAT])

/-- The one-principle grammar of the worked fragment. -/
def hpsgGrammar : Grammar hpsgSig := [hfp]

/-! ### Worked head-complement structures (entities: mother, head daughter, two categories) -/

/-- Entities of a worked head-complement structure. -/
inductive Ent where
  | mother | headDtr | catM | catH
  deriving DecidableEq, Fintype, Repr

/-- A well-formed head-complement structure: the mother and its head daughter point at one
shared category entity, so the Head Feature Principle holds. -/
def posModel : Interpretation hpsgSig where
  U := Ent
  S := fun
    | .mother => .headedPhrase
    | .headDtr => .word
    | .catM => .nounCat
    | .catH => .nounCat
  A := fun a u => match a, u with
    | .CAT, .mother => some .catM
    | .CAT, .headDtr => some .catM
    | .HD, .mother => some .headDtr
    | _, _ => none
  R := fun e => e.elim

/-- The well-formed structure satisfies the Head Feature Principle. -/
example : posModel.Models hpsgGrammar := by unfold posModel; decide

/-- The well-formed structure is totally well-typed. -/
example : posModel.WellTyped := by unfold posModel; decide

/-- An ill-formed structure: the head daughter's category differs from the mother's, so the
HFP fails — the principle is a genuine filter, not vacuously satisfied. -/
def negModel : Interpretation hpsgSig where
  U := Ent
  S := fun
    | .mother => .headedPhrase
    | .headDtr => .word
    | .catM => .nounCat
    | .catH => .verbCat
  A := fun a u => match a, u with
    | .CAT, .mother => some .catM
    | .CAT, .headDtr => some .catH
    | .HD, .mother => some .headDtr
    | _, _ => none
  R := fun e => e.elim

/-- The ill-formed structure violates the Head Feature Principle. -/
example : ¬ negModel.Models hpsgGrammar := by unfold negModel; decide

/-- It is nonetheless well-typed: it only violates the *principle*, not the signature. -/
example : negModel.WellTyped := by unfold negModel; decide

/-! ### A partial bridge to the computational HPSG core -/

/-- A category species for each UD category. -/
def catSpecies : UD.UPOS → HSort
  | .NOUN => .nounCat
  | .VERB => .verbCat
  | _ => .otherCat

/-- The interpretation induced by a head-complement rule: a mother and a head daughter, each
with its own category entity whose species is `catSpecies` of the rule's category value. -/
def toInterp (r : HPSG.HeadCompRule) : Interpretation hpsgSig where
  U := Ent
  S := fun
    | .mother => .headedPhrase
    | .headDtr => .word
    | .catM => catSpecies r.result.synsem.cat
    | .catH => catSpecies r.head.synsem.cat
  A := fun a u => match a, u with
    | .CAT, .mother => some .catM
    | .CAT, .headDtr => some .catH
    | .HD, .mother => some .headDtr
    | _, _ => none
  R := fun e => e.elim

/-- From the project's computational HFP (`HPSG.HeadCompRule.hfp`: a head-complement rule's
mother and head daughter share their category *value*), the induced interpretation satisfies a
category **sort-agreement** description — the head daughter's category sort is the mother's.
The proof discharges on `r.hfp`.

**This is strictly weaker than, and distinct from, the grammar's Head Feature Principle**
(`hfp`), which is **token identity** (`pathEq`). Value equality does not entail token identity,
so this does NOT establish `(toInterp r).Models hpsgGrammar`: `toInterp` gives the mother and
head daughter *distinct* category entities (`catM`/`catH`), which the grammar's `pathEq` HFP
rejects even when their sorts agree. A faithful computational↔token-identity bridge (where the
induced model structure-shares the category object) is future work. -/
theorem toInterp_categoryAgreement_of_hfp (r : HPSG.HeadCompRule) :
    (toInterp r).satisfies .mother
      (.sortAssign [.HD, .CAT] (catSpecies r.result.synsem.cat)) := by
  show catSpecies r.head.synsem.cat ≤ catSpecies r.result.synsem.cat
  rw [r.hfp]

end HPSG.RSRL
