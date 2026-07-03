import Linglib.Semantics.Kinds.NominalMappingParameter
import Linglib.Studies.Krifka2004
import Linglib.Data.Examples.LeBruynDeSwart2022

/-!
# Exceptional wide scope of bare nominals
[le-bruyn-de-swart-2022]

Le Bruyn & de Swart, "Exceptional wide scope of bare nominals" (Semantics & Pragmatics
2022). Bare nominals normally take obligatory narrow scope — one of the strongest
arguments for the kinds approach. But **scrambled** bare plurals in Dutch/German
unambiguously take *wide* scope over negation and quantifiers, *while keeping kind
reference*. This adjudicates two accounts:

* [chierchia-1998] (with [dayal-2004]): bare plurals denote kinds; the existential comes
  from Derived Kind Predication, which is *local*, so scope is position-invariant and
  cannot be wide (`NMP.chierchia_position_invariant`).
* [krifka-2004]: bare plurals are properties; the existential type shift is a *local type
  repair* at the surface position, so a scrambled (raised) bare plural scopes wide
  (`Krifka2004.scope_follows_position`).

Both accounts share one existential closure (`NMP.existsClose`) and differ only in where
negation sits: Chierchia always keeps it outside (`¬ ∃`), Krifka lets it move inside under
scrambling (`∃ ¬`). The scrambling data falsify the kinds approach's locality and confirm
Krifka's position-sensitive shift. Wide scope and kind reference are dissociable.

## Main declarations
* `chierchia_invariant_krifka_sensitive` — the theoretical crux: Chierchia's DKP is
  position-invariant for *every* model, while Krifka's ∃-shift diverges on *some* model
* `theories_agree_unscrambled` / `theories_diverge_on_scrambling` — on a concrete two-book
  model the accounts agree on the unscrambled reading and disagree on the scrambled one
* `krifka_matches_scrambling_data` — Krifka's wide-scope reading matches the Dutch
  *boeken niet uitgelezen* datum (`Data/Examples/LeBruynDeSwart2022.json`)
* `scrambled_keeps_kind_reference` — scrambling affects scope, not kindhood
-/

namespace LeBruynDeSwart2022

open Data.Examples
open Semantics.Kinds.NMP
  (chierchiaDerivScrambled chierchiaDerivUnscrambled chierchia_position_invariant)
open Krifka2004 (krifkaDerivScrambled krifkaDerivUnscrambled scope_follows_position)

/-- Judgment of a named reading, if recorded. -/
def readingOf (row : LinguisticExample) (name : String) : Option Features.Judgment :=
  (row.readings.find? (·.1 == name)).map (·.2)

/-! ### The theoretical crux

Chierchia's Derived Kind Predication introduces the existential *locally*, so negation
always scopes outside it and scrambled = unscrambled. Krifka's existential type shift sits
at the bare NP's surface position, so the two can diverge. -/

/-- The accounts make categorically different scope predictions: Chierchia's derivation is
position-invariant for *every* domain, property, and predicate, whereas Krifka's diverges
scrambled vs. unscrambled on *some* model. -/
theorem chierchia_invariant_krifka_sensitive :
    (∀ (Entity : Type) (kind : List Entity) (P Q : Entity → Prop),
       chierchiaDerivScrambled kind P Q = chierchiaDerivUnscrambled kind P Q) ∧
    (∃ (Entity : Type) (dom : List Entity) (P Q : Entity → Prop),
       krifkaDerivScrambled dom P Q ≠ krifkaDerivUnscrambled dom P Q) :=
  ⟨fun _ kind P Q => chierchia_position_invariant kind P Q, scope_follows_position⟩

/-! ### A concrete model: two books, one finished

Le Bruyn & de Swart's *Het klopt dat ik boeken niet heb uitgelezen* ("it's true that there
are books I didn't finish"): with two books, one finished and one not, the scrambled bare
plural is true (there is an unfinished book) but the unscrambled reading is false (it would
mean "I finished no books"). -/

inductive Book where
  | b1
  | b2
  deriving DecidableEq, Repr

def bookDomain : List Book := [.b1, .b2]

/-- "books" — true of every book. -/
def isBook : Book → Prop := fun _ => True

/-- "finished" — true of `b1`, false of `b2`. -/
def finished : Book → Prop := fun b => b = .b1

-- Krifka distinguishes the positions: unscrambled narrow (false), scrambled wide (true).
example : ¬ krifkaDerivUnscrambled bookDomain isBook finished := by
  unfold krifkaDerivUnscrambled isBook finished bookDomain; decide
example : krifkaDerivScrambled bookDomain isBook finished := by
  unfold krifkaDerivScrambled isBook finished bookDomain; decide

-- Chierchia collapses them: both narrow (false), by DKP locality.
example : ¬ chierchiaDerivScrambled bookDomain isBook finished := by
  unfold chierchiaDerivScrambled isBook finished bookDomain; decide

/-! ### The decisive divergence -/

/-- The accounts agree on the unscrambled reading: both are `¬ ∃ x ∈ dom, P x ∧ Q x`. -/
theorem theories_agree_unscrambled :
    chierchiaDerivUnscrambled bookDomain isBook finished =
      krifkaDerivUnscrambled bookDomain isBook finished :=
  rfl

/-- …but diverge on the scrambled reading: Chierchia keeps narrow scope (`false`) where
Krifka derives wide scope (`true`). -/
theorem theories_diverge_on_scrambling :
    chierchiaDerivScrambled bookDomain isBook finished ≠
      krifkaDerivScrambled bookDomain isBook finished := by
  intro h
  have hk : krifkaDerivScrambled bookDomain isBook finished := by
    unfold krifkaDerivScrambled isBook finished bookDomain; decide
  rw [← h] at hk
  have hc : ¬ chierchiaDerivScrambled bookDomain isBook finished := by
    unfold chierchiaDerivScrambled isBook finished bookDomain; decide
  exact hc hk

/-- Krifka's scrambled reading is wide, matching the Dutch datum
(`Examples.boeken_niet_uitgelezen`): there are books I didn't finish. -/
theorem krifka_matches_scrambling_data :
    krifkaDerivScrambled bookDomain isBook finished ∧
    readingOf Examples.boeken_niet_uitgelezen "wide_scope" = some .acceptable ∧
    readingOf Examples.boeken_niet_uitgelezen "narrow_scope" = some .unacceptable :=
  ⟨by unfold krifkaDerivScrambled isBook finished bookDomain; decide, rfl, rfl⟩

/-! ### Wide scope and kind reference are dissociable -/

/-- A scrambled bare plural can still be kind-referring (the *haten* 'hate' cases,
`Examples.boeken_gehaat`): scrambling affects scope, not kindhood. -/
theorem scrambled_keeps_kind_reference :
    Examples.boeken_gehaat.feature? "position" = some "scrambled" ∧
    readingOf Examples.boeken_gehaat "kind_reference" = some .acceptable := ⟨rfl, rfl⟩

end LeBruynDeSwart2022
