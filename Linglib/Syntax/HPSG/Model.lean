import Linglib.Syntax.HPSG.Description
import Linglib.Syntax.HPSG.Basic

/-!
# A worked HPSG signature, the Head Feature Principle, and a computational bridge
[richter-2000], [richter-2024], [pollard-sag-1994]

A minimal HPSG signature fragment over the RSRL substrate, the **Head Feature Principle** as a
description, two worked head-complement models (one satisfying, one violating the HFP) showing
the principle genuinely filters, and a deliberately partial bridge from the project's
*computational* HPSG core (`HPSG.HeadCompRule.hfp`) to a sort-agreement description.

The HFP here works at **CAT** granularity (what `HeadCompRule.hfp` exposes), a valence-free
stand-in for the canonical **HEAD**-value sharing ([pollard-sag-1994]). The bridge is
partial: `HeadCompRule.hfp` is value equality, the grammar's `pathEq` HFP is token identity —
genuinely different notions, so the bridge proves only sort-agreement (see that theorem). Only
`hpsgSig` is `@[reducible]`; the models are plain `def`s with explicit carrier instances.
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

/-- The sort hierarchy as a `PartialOrder` (`a ≤ b` = "`a` at least as specific as `b`"). -/
instance : PartialOrder HSort :=
  partialOrderOfBool hleB (by decide) (by decide) (by decide)

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

/-- The **Head Feature Principle** ([pollard-sag-1994]; [richter-2024], Ch. 3, (3a)),
at CAT granularity: a headed phrase shares its category (path `CAT`) with its head daughter
(path `HD CAT`), as token identity (`pathEq`). The mother is the described entity `:`; `CAT`
and `HD CAT` are `:`-rooted paths (`Term.path`). -/
def hfp : Desc hpsgSig :=
  .imp (.sortAssign .colon .headedPhrase) (.pathEq (.path [.CAT]) (.path [.HD, .CAT]))

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

-- Explicit `Fintype`/`DecidableEq` on the carrier so `decide` resolves the decision instances
-- *without* unfolding `posModel` (which would reduce `.R` and unmatch the empty-relation
-- instance below). The kernel still unfolds `posModel` when evaluating `decide`.
instance : Fintype posModel.U := inferInstanceAs (Fintype Ent)
instance : DecidableEq posModel.U := inferInstanceAs (DecidableEq Ent)

/-- The well-formed structure satisfies the Head Feature Principle. -/
example : posModel.Models hpsgGrammar := by decide

/-- The well-formed structure is totally well-typed. -/
example : posModel.WellTyped := by decide

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

instance : Fintype negModel.U := inferInstanceAs (Fintype Ent)
instance : DecidableEq negModel.U := inferInstanceAs (DecidableEq Ent)

/-- The ill-formed structure violates the Head Feature Principle. -/
example : ¬ negModel.Models hpsgGrammar := by decide

/-- It is nonetheless well-typed: it only violates the *principle*, not the signature. -/
example : negModel.WellTyped := by decide

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
rejects even when their sorts agree. The faithful computational↔token-identity bridge — where the
induced model structure-shares the category object — is `toInterpShared` below. -/
theorem toInterp_categoryAgreement_of_hfp (r : HPSG.HeadCompRule)
    (ass : Nat → (toInterp r).U) :
    (toInterp r).satisfies ass .mother
      (.sortAssign (.path [.HD, .CAT]) (catSpecies r.result.synsem.cat)) := by
  show catSpecies r.head.synsem.cat ≤ catSpecies r.result.synsem.cat
  rw [r.hfp]

/-! ### A faithful structure-sharing bridge

`toInterp` mapped a head-complement rule to a model with *distinct* category entities, so the
token-identity HFP could not hold (only sort agreement). `toInterpShared` instead **structure-shares**
the category object — the mother and head daughter point at one entity — so the grammar's `pathEq` HFP
is realized, and that sharing is justified by the rule's value-equality HFP (`r.hfp`). -/

/-- A category species is never a phrase sort, so it can never trigger the headed-phrase HFP. -/
private theorem catSpecies_not_headedPhrase (c : UD.UPOS) :
    ¬ (catSpecies c ≤ HSort.headedPhrase) := by
  cases c <;> decide

/-- The interpretation induced by a head-complement rule that **structure-shares** the category
object: the mother and head daughter both point at one category entity (`catM`, species from the head
daughter). Unlike `toInterp`'s distinct `catM`/`catH`, this realizes the token-identity HFP. -/
def toInterpShared (r : HPSG.HeadCompRule) : Interpretation hpsgSig where
  U := Ent
  S := fun
    | .mother => .headedPhrase
    | .headDtr => .word
    | .catM => catSpecies r.head.synsem.cat
    | .catH => catSpecies r.result.synsem.cat
  A := fun a u => match a, u with
    | .CAT, .mother => some .catM
    | .CAT, .headDtr => some .catM     -- structure sharing: both daughters point at one category
    | .HD, .mother => some .headDtr
    | _, _ => none
  R := fun e => e.elim

/-- **The faithful bridge.** The structure-sharing induced model satisfies the grammar's
token-identity Head Feature Principle — the mother and head daughter genuinely share one category
object, not merely agree in sort — which `toInterp` could not establish. -/
theorem toInterpShared_models_hfp (r : HPSG.HeadCompRule) :
    (toInterpShared r).Models hpsgGrammar := by
  intro u d hd
  simp only [hpsgGrammar, List.mem_singleton] at hd
  subst hd
  cases u with
  | mother => exact fun _ => rfl                              -- HFP holds: both daughters share catM
  | headDtr =>                                                -- word ⋨ headed-phrase
    exact fun h => absurd (show HSort.word ≤ HSort.headedPhrase from h) (by decide)
  | catM => exact fun h => absurd h (catSpecies_not_headedPhrase r.head.synsem.cat)
  | catH => exact fun h => absurd h (catSpecies_not_headedPhrase r.result.synsem.cat)

/-- The structure-sharing is *justified* by the computational value-equality HFP (`r.hfp`): the
mother's and head daughter's category species coincide, so collapsing them to one object loses no
information. Where `toInterp` recovers only sort agreement (`toInterp_categoryAgreement_of_hfp`), this
recovers genuine token identity. -/
theorem toInterpShared_faithful_of_hfp (r : HPSG.HeadCompRule) :
    catSpecies r.result.synsem.cat = catSpecies r.head.synsem.cat := by
  rw [r.hfp]

end HPSG.RSRL
