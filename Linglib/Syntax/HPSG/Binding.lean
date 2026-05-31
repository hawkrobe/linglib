import Linglib.Syntax.HPSG.Description
import Mathlib.Tactic.DeriveFintype

/-!
# HPSG Binding Theory (Principles A & B) in RSRL
@cite{pollard-sag-1994}, @cite{richter-2000}, @cite{richter-2024}

The first *relational, quantified* HPSG principles in the RSRL substrate, exercising the
`rel`/`ex`/`all` machinery of `Description.lean`. Following the HPSG Binding Theory
(@cite{pollard-sag-1994}; @cite{muller-2024-binding}, Ch. 20):

* **local o-command** ((11)): `Y` locally o-commands `Z` iff `Y` is less oblique than `Z` —
  precedes it on the same ARG-ST list. Here it is the relation `locO` (interpreted per model).
* **o-bind** ((13)): `Y` o-binds `Z` iff coindexed *and* o-commands. **Coindexation is token
  identity** of the `INDEX` objects (`pathEq` on `INDEX`), the RSRL-faithful reading.
* **Principle A** ((15)): a locally o-commanded anaphor must be locally o-bound.
* **Principle B** ((15)): a personal pronoun must be locally o-free (not locally o-bound).

## Implementation notes

* **Simplification.** ARG-ST is modeled via `SUBJ`/`OBJ` attributes on the sign (its argument
  synsems are components of the sign, so component quantification reaches them) and `locO` is
  interpreted directly per model. Deriving `locO` from a `FIRST`/`REST` list and the obliqueness
  order is a faithful refinement (the `list`/`nelist` machinery); `locO`-as-a-relation already
  exercises the relational+quantified description language on real binding content.
* The nom-obj hierarchy (`ana`/`ppro`/`npro` ⊑ `synsem`) keys the principles by sort.
* **Computational bridge deferred.** A bridge to the project's computational binding
  (`Syntax/HPSG/Coreference.lean`'s `computeCoreferenceStatus`) is future work: that layer
  encodes coindexation as `index : Option Nat` *value* equality over `Word`-based clauses,
  whereas the RSRL principles here use *token identity* (`pathEq` on `INDEX`) over abstract
  entities — the same value-vs-token gap flagged for the HFP bridge. Aligning them needs the
  computational layer to encode structure-sharing.
-/

namespace HPSG.RSRL.Binding

/-! ### Signature: nom-obj hierarchy, INDEX, and the o-command relation -/

/-- Sorts: a `sign`, `synsem` objects with the nom-obj species (`ana`/`ppro`/`npro`), and an
atomic `idx` (referential index). -/
inductive BSort | top | sign | synsem | ana | ppro | npro | idx
  deriving DecidableEq, Fintype, Repr

/-- Attributes: `SUBJ`/`OBJ` (a sign's arguments — a flattened ARG-ST) and `IDX` (a synsem's
referential index). -/
inductive BAttr | SUBJ | OBJ | IDX deriving DecidableEq, Fintype, Repr

/-- One relation: local o-command, `locO` (arity 2). -/
inductive BRel | locO deriving DecidableEq, Fintype, Repr

/-- Subsumption: the nom-obj species are `≤ synsem`; everything `≤ top`. -/
def bleB : BSort → BSort → Bool
  | _, .top => true
  | .ana, .synsem => true
  | .ppro, .synsem => true
  | .npro, .synsem => true
  | a, b => decide (a = b)

private theorem bleB_refl : ∀ a, bleB a a = true := by decide
private theorem bleB_trans :
    ∀ a b c, bleB a b = true → bleB b c = true → bleB a c = true := by decide
private theorem bleB_antisymm : ∀ a b, bleB a b = true → bleB b a = true → a = b := by decide

instance : PartialOrder BSort where
  le a b := bleB a b = true
  le_refl := bleB_refl
  le_trans := bleB_trans
  le_antisymm := bleB_antisymm

instance : DecidableLE BSort := fun a b => inferInstanceAs (Decidable (bleB a b = true))

def bapprop : BSort → BAttr → Option BSort
  | .sign, .SUBJ => some .synsem
  | .sign, .OBJ => some .synsem
  | .synsem, .IDX => some .idx
  | .ana, .IDX => some .idx
  | .ppro, .IDX => some .idx
  | .npro, .IDX => some .idx
  | _, _ => none

private theorem bapprop_inh : ∀ (σ₁ σ₂ : BSort) (α : BAttr) (τ₁ : BSort),
    σ₂ ≤ σ₁ → bapprop σ₁ α = some τ₁ → ∃ τ₂, bapprop σ₂ α = some τ₂ ∧ τ₂ ≤ τ₁ := by decide

@[reducible] def bindingSig : Signature BSort where
  Attr := BAttr
  Rel := BRel
  arity := fun _ => 2
  approp := bapprop
  approp_inherits := fun {σ₁ σ₂ α τ₁} => bapprop_inh σ₁ σ₂ α τ₁

/-! ### Principles A and B as descriptions

Variables: `0` is the bound synsem `x`; `1` is the candidate binder `y`. `IDX(x) ≈ IDX(y)` is
coindexation (token identity). -/

/-- Coindexation of the entities at variables `x` and `y`: token identity of their `INDEX`. -/
def coindexed (x y : Nat) : Desc bindingSig :=
  .pathEq (.feat (.var x) .IDX) (.feat (.var y) .IDX)

/-- `y` locally o-binds `x`: `locO(y, x)` and they are coindexed. -/
def locallyOBinds (y x : Nat) : Desc bindingSig :=
  .and (.rel .locO [.var y, .var x]) (coindexed x y)

/-- **Principle A**: a locally o-commanded anaphor must be locally o-bound. For every
component `x`: if `x` is an anaphor and some component `y` locally o-commands it, then some
component `y` locally o-binds it. -/
def principleA : Desc bindingSig :=
  .all 0 (.imp
    (.and (.sortAssign (.var 0) .ana) (.ex 1 (.rel .locO [.var 1, .var 0])))
    (.ex 1 (locallyOBinds 1 0)))

/-- **Principle B**: a personal pronoun must be locally o-free — no component locally o-binds
it. -/
def principleB : Desc bindingSig :=
  .all 0 (.imp (.sortAssign (.var 0) .ppro)
    (.neg (.ex 1 (locallyOBinds 1 0))))

/-- The binding fragment's grammar. -/
def bindingGrammar : Grammar bindingSig := [principleA, principleB]

/-! ### Worked model: *Mary likes herself* (grammatical) -/

/-- Entities of *Mary likes herself*: the verb sign, the subject (`mary`, an `npro`), the
object (`herself`, an `ana`), and one shared index `i`. -/
inductive GEnt | s | mary | herself | i deriving DecidableEq, Fintype, Repr

/-- *Mary likes herself*: `mary` and `herself` share the index `i` (coindexed), and `mary`
locally o-commands `herself` (it is less oblique). -/
def maryLikesHerself : Interpretation bindingSig where
  U := GEnt
  S := fun
    | .s => .sign
    | .mary => .npro
    | .herself => .ana
    | .i => .idx
  A := fun a u => match a, u with
    | .SUBJ, .s => some .mary
    | .OBJ, .s => some .herself
    | .IDX, .mary => some .i
    | .IDX, .herself => some .i
    | _, _ => none
  R := fun _ args => args = [GEnt.mary, GEnt.herself]

instance : Fintype maryLikesHerself.U := inferInstanceAs (Fintype GEnt)
instance : DecidableEq maryLikesHerself.U := inferInstanceAs (DecidableEq GEnt)
instance (ρ : bindingSig.Rel) : DecidablePred (maryLikesHerself.R ρ) :=
  fun args => inferInstanceAs (Decidable (args = [GEnt.mary, GEnt.herself]))

/-- *Mary likes herself* satisfies Principle A: `herself` (an anaphor) is locally o-commanded
by `mary`, and `mary` locally o-binds it (coindexed via the shared index `i`). -/
example : maryLikesHerself.Models [principleA] := by decide

/-- It also satisfies the whole binding grammar (Principle B is vacuous: no pronoun). -/
example : maryLikesHerself.Models bindingGrammar := by decide

/-! ### Worked model: *Mary likes himself* (gender clash — Principle A violated) -/

/-- Entities with two *distinct* indices `iM`, `iH`: `mary` and `himself` are not coindexed. -/
inductive HEnt | s | mary | himself | iM | iH deriving DecidableEq, Fintype, Repr

/-- *Mary likes himself*: `mary` locally o-commands the anaphor `himself`, but their indices
differ (gender clash), so `himself` is not locally o-bound — Principle A is violated. -/
def maryLikesHimself : Interpretation bindingSig where
  U := HEnt
  S := fun
    | .s => .sign
    | .mary => .npro
    | .himself => .ana
    | .iM => .idx
    | .iH => .idx
  A := fun a u => match a, u with
    | .SUBJ, .s => some .mary
    | .OBJ, .s => some .himself
    | .IDX, .mary => some .iM
    | .IDX, .himself => some .iH
    | _, _ => none
  R := fun _ args => args = [HEnt.mary, HEnt.himself]

instance : Fintype maryLikesHimself.U := inferInstanceAs (Fintype HEnt)
instance : DecidableEq maryLikesHimself.U := inferInstanceAs (DecidableEq HEnt)
instance (ρ : bindingSig.Rel) : DecidablePred (maryLikesHimself.R ρ) :=
  fun args => inferInstanceAs (Decidable (args = [HEnt.mary, HEnt.himself]))

/-- *Mary likes himself* violates Principle A — a genuine filter, not vacuously satisfied. -/
example : ¬ maryLikesHimself.Models [principleA] := by decide

/-! ### Worked model: *Mary likes her* coindexed (Principle B violated) -/

/-- Entities with `her` a personal pronoun (`ppro`) sharing the index `i` with `mary`. -/
inductive PEnt | s | mary | her | i deriving DecidableEq, Fintype, Repr

/-- *Mary likes her_i* with `her` coindexed with `mary`: `mary` locally o-binds the pronoun
`her`, so `her` is not locally o-free — Principle B is violated. -/
def maryLikesHer : Interpretation bindingSig where
  U := PEnt
  S := fun
    | .s => .sign
    | .mary => .npro
    | .her => .ppro
    | .i => .idx
  A := fun a u => match a, u with
    | .SUBJ, .s => some .mary
    | .OBJ, .s => some .her
    | .IDX, .mary => some .i
    | .IDX, .her => some .i
    | _, _ => none
  R := fun _ args => args = [PEnt.mary, PEnt.her]

instance : Fintype maryLikesHer.U := inferInstanceAs (Fintype PEnt)
instance : DecidableEq maryLikesHer.U := inferInstanceAs (DecidableEq PEnt)
instance (ρ : bindingSig.Rel) : DecidablePred (maryLikesHer.R ρ) :=
  fun args => inferInstanceAs (Decidable (args = [PEnt.mary, PEnt.her]))

/-- A coindexed pronoun violates Principle B. -/
example : ¬ maryLikesHer.Models [principleB] := by decide

end HPSG.RSRL.Binding
