import Linglib.Semantics.Reference.Monsters

/-!
# Kocurek, Jerzak & Rudolph 2020: Against Conventional Wisdom (c-monsters)
[kocurek-jerzak-rudolph-2020]

Kocurek, A. W., Jerzak, E. & Rudolph, R. E. (2020). Against conventional
wisdom. *Philosophers' Imprint* 20(22), 1–27.

## Defining commitment

KJR argue that what they call **Conventional Wisdom** — the thesis that
"truth at a scenario (counterfactual or otherwise) is evaluated relative
to our (or the speaker's) actual linguistic conventions, even if those
conventions diverge from the ones adopted in that scenario" (KJR p.2) —
is FALSE. Certain embedded clauses can characterize conditions on the
linguistic conventions in force rather than on the non-linguistic world.
KJR call the embedding expressions **c-monsters**.

To accommodate c-monsters, KJR propose a substantial revision of the
semantic architecture: replace worlds (as points of evaluation and
objects of propositional attitudes) with **world-convention pairs**.
Standard subject-predicate sentences then express something like
**diagonal content** — propositions about whatever the conventions
pick out for each predicate.

This stub encodes KJR's commitment to (i) rejecting Conventional Wisdom,
(ii) world-convention pairs as evaluation points, (iii) the c-monstrous
behaviour of certain embedding expressions.

## K-G's disagreement (paper §4, p.24-25)

K-G accepts the same c-monster data (paper examples (4), (29)-(32) on
Pluto-as-planet conditionals) but argues for a much less revisionary
analysis. The c-monstrous behaviour is explained by positing a covert
diagonalizer `†` that operates on the existing quotative interpretation
function `⟨*⟩` — no replacement of worlds with world-convention pairs
required. K-G's covert apparatus 𝔐 + † preserves Conventional Wisdom
for ordinary subject-predicate sentences while giving c-monstrous
readings only where † is present.

The two analyses make incompatible architectural commitments:
- **KJR**: worlds → world-convention pairs (semantic revision)
- **K-G**: worlds unchanged, add covert † at specific operator sites

This stub is sufficient to host the inequality theorem in
`KirkGiannini2024.lean`.

## Note on scope

Stub formalisation. Encodes (Conventional Wisdom)-rejection and the
world-convention pair architecture. Does NOT formalise KJR's full
semantics for counterfactuals over WC-pairs, nor the empirical data on
embedding expressions identified as c-monsters.

Imports `Semantics/Reference/Monsters.lean` to mark Kaplan's
thesis as the prior commitment KJR also reject (Kaplan's thesis is the
no-context-shifting variant; Conventional Wisdom is the
no-convention-shifting variant — KJR reject the latter).
-/

set_option autoImplicit false

namespace KocurekJerzakRudolph2020

/-- A linguistic convention: an assignment of extensions to predicates
    (parameterized by predicate type and entity domain). -/
structure Convention (Pred Entity W : Type) where
  /-- The convention's extension function. -/
  ext : Pred → Entity → W → Prop

/-- **KJR's evaluation point: a world-convention pair.** Replaces the
    standard `World`-only architecture. Propositional attitudes hold
    over WC-pairs; conditionals shift the convention component. -/
structure WC (W Pred Entity : Type) where
  world : W
  conv : Convention Pred Entity W

/-- **KJR's diagonal content for a predicate.** At a WC-pair `⟨w, c⟩`,
    the predicate `p` applied to entity `e` is evaluated using `c`'s
    extension at `w`, NOT using the actual-world convention. This is
    where Conventional Wisdom fails. -/
def diagContent {W Pred Entity : Type} (p : Pred) (e : Entity)
    (wc : WC W Pred Entity) : Prop :=
  wc.conv.ext p e wc.world

/-- **(Conventional Wisdom) — the thesis KJR reject.** For all
    predicates, evaluations should use the actual-world convention
    `c_actual`, not the convention component of the evaluation point. -/
def ConventionalWisdom {W Pred Entity : Type} (c_actual : Convention Pred Entity W) : Prop :=
  ∀ (p : Pred) (e : Entity) (wc : WC W Pred Entity),
    diagContent p e wc ↔ c_actual.ext p e wc.world

/-- **KJR's central claim: Conventional Wisdom fails.** There exist
    convention pairs where the actual-world convention diverges from
    the WC-pair's convention, producing different extensions. -/
theorem conventional_wisdom_fails
    {W Pred Entity : Type} [Inhabited W] [Inhabited Pred] [Inhabited Entity]
    (c_actual c_alt : Convention Pred Entity W)
    (p : Pred) (e : Entity) (w : W)
    (h_diff : c_actual.ext p e w ≠ c_alt.ext p e w) :
    ¬ ConventionalWisdom c_actual := by
  intro h_cw
  have := h_cw p e ⟨w, c_alt⟩
  simp [diagContent] at this
  exact h_diff (propext this.symm)

/-- **KJR's c-monster predicate.** An embedding expression is a
    c-monster if it can produce readings on which the embedded predicate
    is evaluated using a NON-actual convention. -/
def IsCMonster {W Pred Entity : Type}
    (embed : (WC W Pred Entity → Prop) → WC W Pred Entity → Prop)
    (c_actual : Convention Pred Entity W) : Prop :=
  ∃ (p : Pred) (e : Entity) (wc : WC W Pred Entity),
    embed (diagContent p e) wc ∧ wc.conv ≠ c_actual

/-- **The Pluto example schematized.** The counterfactual operator
    "could have been" applied to "planet" produces a c-monstrous reading
    where 'planet' is evaluated using a NON-actual convention (one that
    classifies Pluto as a planet, against the post-2006 actual
    convention). KJR's analysis: the antecedent of the counterfactual
    shifts the convention component of the WC-pair. -/
def pluto_could_have_been_planet_via_convention_shift
    {W Pred Entity : Type} (planet : Pred) (pluto : Entity)
    (c_post2006 c_pre2006 : Convention Pred Entity W) (w : W)
    (h_post : ¬ c_post2006.ext planet pluto w)
    (h_pre  : c_pre2006.ext planet pluto w) :
    ∃ (wc : WC W Pred Entity),
      diagContent planet pluto wc ∧ wc.conv ≠ c_post2006 :=
  ⟨⟨w, c_pre2006⟩, h_pre, λ heq => h_post (heq ▸ h_pre)⟩

end KocurekJerzakRudolph2020
