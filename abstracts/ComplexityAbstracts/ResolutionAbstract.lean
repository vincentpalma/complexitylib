/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.ResolutionBridge

/-! # A formal abstract of Haken's resolution lower bound

The pigeonhole principle with `n + 1` pigeons and `n` holes has a CNF of polynomial size in `n`,
but its resolution refutations need exponentially many lines in `n`. This file defines the
exact line-proof rule and pigeonhole formula and states
Haken's lower bound, following the Beame–Pitassi bottleneck argument.

A reader can inspect the definitions and theorem statements here without reading proof
implementations: `#check_abstract` audits their dependencies, and Lean checks the proofs through
`ResolutionBridge`. No internal library model is allowlisted. Proof size counts certificate
lines, including input-clause lines; it does not measure solver runtime.

## References

* [J. A. Robinson, *A machine-oriented logic based on the resolution principle*][Robinson1965]
* [A. Haken, *The intractability of resolution*][Haken1985]
* [P. Beame, T. Pitassi, *Simplified and improved resolution lower bounds*][BeamePitassi1996]
* [S. Jukna, *Boolean Function Complexity*, Chapter 18][Jukna2012]
-/

namespace ComplexityTests.Abstracts.ResolutionAbstract

/-! ## CNF formulas and resolution certificates

A literal is a variable paired with its Boolean polarity. A clause is a disjunction of its
literals, represented by a finite set so that order and repetition are immaterial.
Input formulas retain list syntax; a resolution proof uses their finite sets of literals.
-/

/-- A clause over variables `V`. -/
abbrev Clause (V : Type) := Finset (V × Bool)

/-- A formula in conjunctive normal form, as list syntax for its input clauses. -/
abbrev CNF (V : Type) := List (List (V × Bool))

/-- An assignment satisfies every clause when each clause contains a matching literal. -/
def Satisfiable {V : Type} (φ : CNF V) : Prop :=
  ∃ σ : V → Bool, ∀ c ∈ φ, ∃ l ∈ c, σ l.1 = l.2

/-- A resolution proof is listed last line first. A new line is an input clause or is obtained
from two earlier lines by erasing the positive pivot from the first and the negative pivot
from the second, then taking their union. Both pivot literals are required. Input clauses are
converted to finite sets; there is no weakening rule. -/
def IsProof {V : Type} [DecidableEq V] (φ : CNF V) : List (Clause V) → Prop
  | [] => True
  | c :: ls => IsProof φ ls ∧ (c ∈ (φ.map List.toFinset).toFinset ∨ ∃ v c₁ c₂,
      c₁ ∈ ls ∧ c₂ ∈ ls ∧ (v, true) ∈ c₁ ∧ (v, false) ∈ c₂ ∧
      c = c₁.erase (v, true) ∪ c₂.erase (v, false))

/-- A refutation derives the empty clause using at most `s` lines. -/
def RefutableInSize {V : Type} [DecidableEq V] (φ : CNF V) (s : ℕ) : Prop :=
  ∃ ls, IsProof φ ls ∧ ∅ ∈ ls ∧ ls.length ≤ s

/-! ## The non-onto pigeonhole formula

Variables `(i,j)` assert that pigeon `i` uses hole `j`. There is one positive clause per pigeon
and a negative clause for each pair of distinct pigeons and each hole. No clause requires a hole
to be occupied, and no clause prohibits one pigeon from occupying several holes.
-/

/-- The formula for `m` pigeons and `n` holes. -/
def pigeonhole (m n : ℕ) : CNF (Fin m × Fin n) :=
  (List.finRange m).map (fun i => (List.finRange n).map fun j => ((i, j), true)) ++
    (List.finRange n).flatMap fun j => (List.finRange m).flatMap fun i =>
      ((List.finRange m).filter (i < ·)).map fun i' => [((i, j), false), ((i', j), false)]

/-- Pigeonhole instances are satisfiable exactly when there are at least as many holes as
pigeons. In particular, the refuted family below is unsatisfiable for every `n`, including zero. -/
theorem pigeonhole_satisfiable (m n : ℕ) : Satisfiable (pigeonhole m n) ↔ m ≤ n :=
  ResolutionBridge.pigeonhole_satisfiable m n

/-- **Haken:** every resolution refutation with `s` lines of the formula for `n + 1` pigeons
and `n` holes satisfies `2^(floor(n/24)) ≤ s`. The exponential parameter is the number of holes,
not the length of an encoding of the CNF. The proof follows the Beame–Pitassi bottleneck
argument. -/
theorem haken {n s : ℕ} (hs : RefutableInSize (pigeonhole (n + 1) n) s) :
    2 ^ (n / 24) ≤ s :=
  ResolutionBridge.haken_of_rules IsProof
    ⟨fun _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩ hs

/--
info: 'ComplexityTests.Abstracts.ResolutionAbstract.haken' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms haken

/--
info: abstract audit passed for `ComplexityTests.Abstracts.ResolutionAbstract`: 12 root
declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.ResolutionAbstract

end ComplexityTests.Abstracts.ResolutionAbstract
