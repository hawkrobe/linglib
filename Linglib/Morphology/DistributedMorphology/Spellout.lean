import Linglib.Morphology.DistributedMorphology.Fusion
import Linglib.Morphology.DistributedMorphology.Impoverishment

/-!
# The spell-out pipeline

The PF branch of the Y-model at the domain level: a spell-out domain is
the sequence of terminals the syntax hands over, the postsyntactic modules
transform it, and Vocabulary Insertion realizes what survives, each
position in its neighborhood; the module inventory and its ordering follow
the Basque morphotactics. The focus-level rule types
(`ImpoverishmentRule` and kin) rewrite one terminal inside
its `Neighborhood`; the operations here move, remove, and merge the
terminals themselves, which no focus-level rule can express.

Each operation carries its position-count law, so terminal/exponent
misalignment is arithmetic: neighborhood rewriting and terminal
metathesis preserve the count, obliteration and fusion decrease it, and
`Spellout.length_pf` says insertion positions equal terminals after the
modules — Fission multiplies exponents within a position (`scansion`),
not positions. `winner?_retreat` (`VocabularyInsertion/Basic.lean`) supplies the
insertion-side ordering law.

Consumers: `Studies/Middleton2026.lean` (Basque whole-terminal rules and
the Ondarru ordering witness), `Studies/HalleMarantz1993.lean` (Tns+Agr
fusion feeding one insertion).

## Main declarations

* `SpelloutDomain`, `mapNeighborhoods` — the domain and the zipper lift
  of focus-level rewriting
* `ObliterationRule`, `TerminalMetathesisRule` — whole-terminal deletion
  (Obliteration) and adjacent-terminal swap, with first-match applicators
  and count laws
* `FusionRule.applyFirstAdjacent` — the domain lift of Fusion
* `Spellout` — the module sequence plus insertion in context; `run`, `pf`,
  `runModules_append`

## Todo

* The LF branch: an `Interpreted` extension whose interpretation reads
  the input domain (the Y-model separation by type), seeded by the
  domain-level allosemy licensing of `Studies/Benz2025.lean`.
* Stratifying the module list by linearization — Lowering before,
  Local Dislocation after.

## References

* [M. Halle and A. Marantz, *Distributed Morphology and the pieces of
  inflection*][halle-marantz-1993]
* [K. Arregi and A. Nevins, *Morphotactics*][arregi-nevins-2012]
* [D. Embick and R. Noyer, *Movement operations after syntax*][embick-noyer-2001]
-/

namespace DistributedMorphology


/-- A spell-out domain: the linear sequence of terminals handed over by
the syntax at spell-out. -/
abbrev SpelloutDomain (Bundle : Type*) := List Bundle

variable {Bundle Ctx : Type*}

/-- Apply `f` to every terminal in its neighborhood: position `i` sees the
earlier terminals as `leftCtx` and the later ones as `rightCtx`, nearest
first. The domain lift of a focus-level rule such as Impoverishment, and of
Vocabulary Insertion. -/
def mapNeighborhoods {C : Type*} (f : Neighborhood Bundle → C)
    (d : SpelloutDomain Bundle) : List C :=
  d.mapIdx fun i b => f ⟨b, (d.take i).reverse, d.drop (i + 1)⟩

/-- Neighborhood rewriting preserves the number of terminals. -/
@[simp] theorem length_mapNeighborhoods {C : Type*} (f : Neighborhood Bundle → C)
    (d : SpelloutDomain Bundle) :
    (mapNeighborhoods f d).length = d.length := by
  simp [mapNeighborhoods]

/-- A whole-terminal deletion rule — [arregi-nevins-2012]'s Obliteration:
the terminal whose neighborhood satisfies `condition` is removed
outright. The focus-level `ImpoverishmentRule` deletes a feature inside a
terminal; this rule deletes the terminal. -/
structure ObliterationRule (Bundle : Type*) where
  /-- Does the rule fire at this neighborhood? -/
  condition : Neighborhood Bundle → Prop
  /-- Decidability witness for `condition`. -/
  decCond : DecidablePred condition

namespace ObliterationRule

instance (rule : ObliterationRule Bundle) (n : Neighborhood Bundle) :
    Decidable (rule.condition n) := rule.decCond n

/-- Build an obliteration rule from a Boolean condition. -/
def ofBool (cond : Neighborhood Bundle → Bool) : ObliterationRule Bundle where
  condition n := cond n = true
  decCond n := inferInstanceAs (Decidable (cond n = true))

/-- Apply the rule, scanning left to right: the first terminal whose
neighborhood fires is dropped; otherwise the domain is unchanged.
`leftCtx` is accumulated nearest first. -/
def apply (rule : ObliterationRule Bundle) (d : SpelloutDomain Bundle) :
    SpelloutDomain Bundle :=
  go [] d
where
  /-- Scan with the already-passed terminals in `left`, nearest first. -/
  go : List Bundle → SpelloutDomain Bundle → SpelloutDomain Bundle
  | left, [] => left.reverse
  | left, t :: rest =>
    if rule.condition ⟨t, left, rest⟩ then left.reverse ++ rest
    else go (t :: left) rest

private theorem length_go_le (rule : ObliterationRule Bundle) :
    ∀ (rest left : List Bundle),
      (apply.go rule left rest).length ≤ left.length + rest.length := by
  intro rest
  induction rest with
  | nil => intro left; simp [apply.go]
  | cons t rest ih =>
    intro left
    rw [apply.go]
    split
    · simp only [List.length_append, List.length_reverse, List.length_cons]
      omega
    · have := ih (t :: left)
      simp only [List.length_cons] at this ⊢
      omega

/-- Obliteration never increases the number of terminals. -/
theorem length_apply_le (rule : ObliterationRule Bundle)
    (d : SpelloutDomain Bundle) : (rule.apply d).length ≤ d.length := by
  simpa [apply] using length_go_le rule d []

end ObliterationRule

/-- An adjacent-terminal swap rule — the terminal-order metathesis of
[arregi-nevins-2012]'s Metathesis module (Basque Ergative Metathesis,
[middleton-2026] (13)). `condition` sees the terminals left of the pair
(nearest first), the pair itself, and the terminals to its right. -/
structure TerminalMetathesisRule (Bundle : Type*) where
  /-- Does the rule swap the pair `t₁ t₂` in this context? -/
  condition : List Bundle → Bundle → Bundle → List Bundle → Prop
  /-- Decidability witness for `condition`. -/
  decCond : ∀ left t₁ t₂ right, Decidable (condition left t₁ t₂ right)

namespace TerminalMetathesisRule

instance (rule : TerminalMetathesisRule Bundle) (left) (t₁ t₂ : Bundle)
    (right) : Decidable (rule.condition left t₁ t₂ right) :=
  rule.decCond left t₁ t₂ right

/-- Build a terminal-metathesis rule from a Boolean condition. -/
def ofBool (cond : List Bundle → Bundle → Bundle → List Bundle → Bool) :
    TerminalMetathesisRule Bundle where
  condition left t₁ t₂ right := cond left t₁ t₂ right = true
  decCond left t₁ t₂ right :=
    inferInstanceAs (Decidable (cond left t₁ t₂ right = true))

/-- Apply the rule, scanning left to right: the first adjacent pair whose
context fires is swapped; otherwise the domain is unchanged. -/
def apply (rule : TerminalMetathesisRule Bundle)
    (d : SpelloutDomain Bundle) : SpelloutDomain Bundle :=
  go [] d
where
  /-- Scan with the already-passed terminals in `left`, nearest first. -/
  go : List Bundle → SpelloutDomain Bundle → SpelloutDomain Bundle
  | left, [] => left.reverse
  | left, [t] => left.reverse ++ [t]
  | left, t₁ :: t₂ :: rest =>
    if rule.condition left t₁ t₂ rest then left.reverse ++ t₂ :: t₁ :: rest
    else go (t₁ :: left) (t₂ :: rest)

private theorem length_go (rule : TerminalMetathesisRule Bundle) :
    ∀ (rest left : List Bundle),
      (apply.go rule left rest).length = left.length + rest.length := by
  intro rest
  induction rest with
  | nil => intro left; simp [apply.go]
  | cons t rest ih =>
    intro left
    cases rest with
    | nil => simp [apply.go]
    | cons t₂ rest' =>
      rw [apply.go]
      split
      · simp
      · have := ih (t :: left)
        simp only [List.length_cons] at this ⊢
        omega

/-- Terminal metathesis preserves the number of terminals. -/
@[simp] theorem length_apply (rule : TerminalMetathesisRule Bundle)
    (d : SpelloutDomain Bundle) : (rule.apply d).length = d.length := by
  simpa [apply] using length_go rule d []

end TerminalMetathesisRule

namespace FusionRule

variable {F : Type*}

/-- The domain lift of Fusion: fuse the first adjacent pair the rule
licenses; otherwise the domain is unchanged. -/
def applyFirstAdjacent (rule : FusionRule F) :
    SpelloutDomain (List F) → SpelloutDomain (List F)
  | [] => []
  | [b] => [b]
  | b₁ :: b₂ :: rest =>
    if rule.condition b₁ b₂ then (b₁ ++ b₂) :: rest
    else b₁ :: applyFirstAdjacent rule (b₂ :: rest)

/-- Fusion never increases the number of terminals. -/
theorem length_applyFirstAdjacent_le (rule : FusionRule F) :
    ∀ d : SpelloutDomain (List F), (rule.applyFirstAdjacent d).length ≤ d.length
  | [] => by simp [applyFirstAdjacent]
  | [b] => by simp [applyFirstAdjacent]
  | b₁ :: b₂ :: rest => by
    rw [applyFirstAdjacent]
    split
    · simp
    · have := length_applyFirstAdjacent_le rule (b₂ :: rest)
      simp only [List.length_cons] at this ⊢
      omega

end FusionRule

/-- Run an ordered module sequence over a domain. The order of the list
is the theory's architectural claim ([arregi-nevins-2012]'s strict
sequence; the Basque ordering witness in `Studies/Middleton2026.lean`
shows reordering it has empirical content). -/
def runModules (modules : List (SpelloutDomain Bundle → SpelloutDomain Bundle))
    (d : SpelloutDomain Bundle) : SpelloutDomain Bundle :=
  modules.foldl (fun d m => m d) d

/-- Module sequences compose by concatenation. -/
theorem runModules_append
    (m₁ m₂ : List (SpelloutDomain Bundle → SpelloutDomain Bundle))
    (d : SpelloutDomain Bundle) :
    runModules (m₁ ++ m₂) d = runModules m₂ (runModules m₁ d) := by
  simp [runModules, List.foldl_append]

@[simp] theorem runModules_nil (d : SpelloutDomain Bundle) :
    runModules ([] : List (SpelloutDomain Bundle → SpelloutDomain Bundle)) d
      = d := rfl

/-- A PF-branch pipeline over a spell-out domain: the ordered
postsyntactic modules, then Vocabulary Insertion at each surviving
position, in its neighborhood. -/
structure Spellout (Bundle F : Type*) where
  /-- The ordered postsyntactic module sequence. -/
  modules : List (SpelloutDomain Bundle → SpelloutDomain Bundle)
  /-- The exponents inserted at a position, seeing its neighbors: one,
  several under Fission (`scansion`), none at a non-licensed position. -/
  insert : Neighborhood Bundle → List F

namespace Spellout

variable {F : Type*}

/-- The domain after the module sequence. -/
def run (s : Spellout Bundle F) (d : SpelloutDomain Bundle) :
    SpelloutDomain Bundle :=
  runModules s.modules d

/-- The PF output: one insertion slot per surviving position. -/
def pf (s : Spellout Bundle F) (d : SpelloutDomain Bundle) :
    List (List F) :=
  mapNeighborhoods s.insert (s.run d)

/-- Exponent slots equal terminals after the modules: the exponent count
diverges from the syntactic terminal count only through the modules. -/
@[simp] theorem length_pf (s : Spellout Bundle F) (d : SpelloutDomain Bundle) :
    (s.pf d).length = (s.run d).length := by
  simp [pf]

end Spellout

end DistributedMorphology
