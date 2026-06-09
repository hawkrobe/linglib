import Linglib.Semantics.Kinds.NominalMappingParameter
import Linglib.Studies.Krifka2004
import Linglib.Phenomena.Generics.KindReference

/-!
# Exceptional wide scope of bare nominals
[le-bruyn-de-swart-2022]

Le Bruyn & de Swart, "Exceptional wide scope of bare nominals" (Semantics & Pragmatics
2022). Bare nominals normally take obligatory narrow scope — one of the strongest
arguments for the kinds approach. But **scrambled** bare plurals in Dutch/German
unambiguously take *wide* scope over negation and quantifiers, *while keeping kind
reference*. This adjudicates two accounts:

* [chierchia-1998] (with [dayal-2004]): bare plurals denote kinds; the existential
  comes from Derived Kind Predication, which is *local*, so scope is position-invariant
  and cannot be wide (`NMP.chierchia_position_invariant`).
* [krifka-2004]: bare plurals are properties; the existential type shift is a *local
  type repair* at the surface position, so a scrambled (raised) bare plural scopes wide
  (`Krifka2004.scope_follows_position`).

The scrambling data falsify the kinds approach's locality and confirm Krifka's
position-sensitive shift. Wide scope and kind reference turn out to be dissociable: a
scrambled bare plural with a kind-level predicate (*haten* 'hate') keeps its kind
reading.

## Main declarations
* `chierchia_invariant_krifka_sensitive` — the theoretical crux: Chierchia's DKP is
  position-invariant for *every* model, while Krifka's ∃-shift diverges on *some* model
* `theories_diverge_on_scrambling` — on a concrete two-book model the accounts agree on
  the unscrambled reading and disagree on the scrambled one
* `krifka_matches_scrambling_data` — Krifka's wide-scope prediction matches the Dutch
  datum `dutchScrambledBoeken`
* `scrambled_keeps_kind_reference` — scrambling affects scope, not kindhood
-/

namespace LeBruynDeSwart2022

open Semantics.Kinds.NMP
  (KindExtension ChierchiaVP chierchiaDerivScrambled chierchiaDerivUnscrambled
   chierchia_position_invariant)
open Krifka2004
  (KrifkaProp KrifkaVP existsShiftApply krifkaDerivScrambled krifkaDerivUnscrambled
   scope_follows_position)
open Phenomena.Generics.KindReference (dutchScrambledBoeken dutchScrambledKindBoeken)

/-! ### The theoretical crux

Chierchia's Derived Kind Predication is *local*: the existential is introduced where
the kind meets the predicate, regardless of surface position, so scrambled and
unscrambled derivations coincide. Krifka's existential type shift instead sits at the
bare NP's surface position, so the two can diverge. -/

/-- The accounts make categorically different scope predictions: Chierchia's derivation
is position-invariant for *every* kind and VP, whereas Krifka's diverges scrambled vs.
unscrambled on *some* model. -/
theorem chierchia_invariant_krifka_sensitive :
    (∀ {Entity World : Type} (kind : KindExtension Entity World)
       (vp : ChierchiaVP Entity World),
       chierchiaDerivScrambled kind vp = chierchiaDerivUnscrambled kind vp) ∧
    (∃ (Entity World : Type) (w : World) (domain : List Entity)
       (prop : KrifkaProp Entity World) (vp : KrifkaVP Entity World),
       krifkaDerivScrambled domain prop vp w ≠ krifkaDerivUnscrambled domain prop vp w) :=
  ⟨fun kind vp => chierchia_position_invariant kind vp, scope_follows_position⟩

/-! ### A concrete model: two books, one finished

Le Bruyn & de Swart's *Het klopt dat ik boeken niet heb uitgelezen* ("it's true that
there are books I didn't finish"): with two books, one finished and one not, the
scrambled bare plural is true (there is an unfinished book) but the unscrambled reading
is false (it would mean "I finished no books"). -/

inductive Book where
  | b1
  | b2
  deriving DecidableEq, Repr

def bookDomain : List Book := [.b1, .b2]

/-- "books" as a property (true of every book). -/
def isBook : KrifkaProp Book Unit := fun _ _ => true

/-- "finished": b1 finished, b2 not. -/
def finishedVP : KrifkaVP Book Unit := fun b _ =>
  match b with
  | .b1 => true
  | .b2 => false

/-- The same world as a kind extension (Chierchia's input). -/
def bookKind : KindExtension Book Unit := fun _ => bookDomain

/-- The VP as Chierchia's object-level predicate (same data as Krifka's). -/
def finishedChierchia : ChierchiaVP Book Unit := finishedVP

-- Krifka distinguishes the two positions: narrow (false) vs wide (true).
example : krifkaDerivUnscrambled bookDomain isBook finishedVP () = false := rfl
example : krifkaDerivScrambled bookDomain isBook finishedVP () = true := rfl

-- Chierchia collapses them: both narrow (false), by DKP locality.
example : chierchiaDerivUnscrambled bookKind finishedChierchia () = false := rfl
example : chierchiaDerivScrambled bookKind finishedChierchia () = false := rfl

/-! ### The decisive divergence -/

/-- The accounts agree on the unscrambled reading but diverge on the scrambled one:
Chierchia keeps narrow scope (`false`) where Krifka derives wide scope (`true`). -/
theorem theories_diverge_on_scrambling :
    chierchiaDerivUnscrambled bookKind finishedChierchia () =
        krifkaDerivUnscrambled bookDomain isBook finishedVP () ∧
    chierchiaDerivScrambled bookKind finishedChierchia () ≠
        krifkaDerivScrambled bookDomain isBook finishedVP () := by
  refine ⟨rfl, ?_⟩
  decide

/-- Krifka's wide-scope prediction for the scrambled bare plural matches the Dutch
datum (`dutchScrambledBoeken.wideOK`): there are books I didn't finish. -/
theorem krifka_matches_scrambling_data :
    krifkaDerivScrambled bookDomain isBook finishedVP () = dutchScrambledBoeken.wideOK :=
  rfl

/-! ### Wide scope and kind reference are dissociable -/

/-- A scrambled bare plural can still be kind-referring (the *haten* 'hate' cases):
scrambling affects scope, not kindhood. -/
theorem scrambled_keeps_kind_reference :
    dutchScrambledKindBoeken.position = .scrambled ∧
    dutchScrambledKindBoeken.kindReferenceOK = true := by
  simp [dutchScrambledKindBoeken]

end LeBruynDeSwart2022
