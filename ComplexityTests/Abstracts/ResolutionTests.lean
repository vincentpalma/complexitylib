/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import ComplexityAbstracts.ResolutionAbstract

/-!
# Regression tests for the finite-clause Resolution abstract

The public recursive proof predicate accepts reordered and repeated input literals and merges
shared non-pivot literals by union. The zero-hole boundary has a one-line refutation, and every
refutation still counts at least one line.
-/

namespace ComplexityTests.Abstracts.ResolutionTests

open ComplexityTests.Abstracts.ResolutionAbstract

/-- Input clauses are compared as finite sets, including at the literal-order boundary. -/
example : IsProof ([[(0, true), (1, false), (0, true)]] : CNF ℕ)
    [{(1, false), (0, true)}] :=
  ⟨trivial, Or.inl (by decide)⟩

/-- A common non-pivot literal occurs only once in the finite resolvent. -/
example : IsProof ([[(0, true), (1, false)], [(0, false), (1, false)]] : CNF ℕ)
    [{(1, false)}, {(0, true), (1, false)}, {(0, false), (1, false)}] := by
  refine ⟨⟨⟨trivial, Or.inl (by decide)⟩, Or.inl (by decide)⟩,
    Or.inr ⟨0, {(0, true), (1, false)}, {(0, false), (1, false)},
      by decide, by decide, by decide, by decide, by decide⟩⟩

/-- A pigeon with no holes gives an empty input clause and exactly one proof line suffices. -/
example : RefutableInSize (pigeonhole 1 0) 1 :=
  ⟨[∅], ⟨trivial, Or.inl (by decide)⟩, by simp, by decide⟩

example : ¬ RefutableInSize (pigeonhole 1 0) 0 := by
  rintro ⟨ls, -, hnil, hlen⟩
  have := List.length_pos_of_mem hnil
  omega

end ComplexityTests.Abstracts.ResolutionTests
