/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.FiniteClause
public import Complexity.Logics.Propositional.CNF.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time comparison of finite-clause representations

List clauses are executable representations of finite clauses. Their encoded size charges every
literal occurrence and the entire encoding of its variable, although their mathematical width
counts distinct literals. Comparing representations does not choose an ordering of a finite set.

## Main results

* `Cslib.Logic.PL.Clause.computableInPolyTime_sameLiterals`: extensional clause comparison is
  polynomial-time for every fixed variable encoding.
-/

public section

namespace Cslib.Logic.PL

open Turing.MultiTapeTM ComputableInPolyTime

/-- Extensional comparison of two list representations is polynomial-time, including on lists
with repeated literals. Time is measured in their complete encoded lengths. -/
@[fun_prop]
theorem Clause.computableInPolyTime_sameLiterals {V : Type} [DecidableEq V]
    (enc : V ↪ List Bool) :
    ComputableInPolyTime (fun p : Clause V × Clause V => p.1.sameLiterals p.2)
      (encPair (encList (encPair enc encBool)) (encList (encPair enc encBool))) encBool := by
  have hforward : ComputableInPolyTime
      (fun p : Clause V × Clause V => p.1.all fun l => decide (l ∈ p.2))
      (encPair (encList (encPair enc encBool)) (encList (encPair enc encBool))) encBool :=
    allWithEncoding (decide_mem (fst _ _) (snd _ _)) (snd _ _) (fst _ _)
  have hbackward : ComputableInPolyTime
      (fun p : Clause V × Clause V => p.2.all fun l => decide (l ∈ p.1))
      (encPair (encList (encPair enc encBool)) (encList (encPair enc encBool))) encBool :=
    allWithEncoding (decide_mem (fst _ _) (snd _ _)) (fst _ _) (snd _ _)
  exact ComputableTidilyInPolyTime.bool_and.computableInPolyTime.comp
    (hforward.prod hbackward)

end Cslib.Logic.PL
