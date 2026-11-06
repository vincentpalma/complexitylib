/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.Resolution.TreeLike
import Complexity.Logics.Propositional.Resolution.SizeWidth
import Complexity.Logics.Propositional.Resolution.DAG

/-!
# Tests: resolution proofs, tree-like resolution and the size–width tradeoff

Widths of clauses with repeated literals; a concrete resolution refutation, its size and width;
a tree-like refutation, its decision tree and the decision tree's refutation; restrictions of a
proof; exact tree-to-line size and width preservation, compared with a DAG sharing a premise;
and instances of the hypotheses of the size–width theorems.
-/

namespace ComplexityTests.ProofComplexity.Resolution

open Cslib Cslib.Logic Cslib.Logic.InferenceSystem Cslib.Logic.PL

/-! ### Width -/

/-- Repeated literals count once; complementary literals count twice. -/
example :
    FiniteClause.width ({(0, true), (0, true), (1, false)} : FiniteClause ℕ) = 2 ∧
    FiniteClause.width ({(0, true), (0, false)} : FiniteClause ℕ) = 2 := by
  decide

/-- Input syntax may reorder and repeat literals without changing its mathematical clauses. -/
example :
    CNF.toClauseSet ([[(0, true), (1, false), (0, true)]] : CNF ℕ) =
      CNF.toClauseSet ([[(1, false), (0, true)]] : CNF ℕ) := by
  decide

/-- Resolution merges a shared non-pivot literal into a single literal. -/
example :
    FiniteClause.resolvent ({(0, true), (1, false)} : FiniteClause ℕ)
      {(0, false), (1, false)} 0 = {(1, false)} := by
  decide

/-! ### A refutation -/

/-- `x₀ ∧ (¬x₀ ∨ x₁) ∧ ¬x₁`. -/
private def φ : ClauseSet ℕ := {{(0, true)}, {(0, false), (1, true)}, {(1, false)}}

/-- Resolve `x₀` with `¬x₀ ∨ x₁` to `x₁`, and `x₁` with `¬x₁` to the empty clause. -/
private def proof : List (FiniteClause ℕ) :=
  [∅, {(1, true)}, {(1, false)}, {(0, false), (1, true)}, {(0, true)}]

example :
    FiniteClause.resolvent ({(0, true)} : FiniteClause ℕ) {(0, false), (1, true)} 0 = {(1, true)} ∧
    FiniteClause.resolvent ({(1, true)} : FiniteClause ℕ) {(1, false)} 1 = ∅ := by
  decide

private theorem isProof : φ.IsProof proof := by
  have h₃ : φ.IsProof [{(1, false)}, {(0, false), (1, true)}, {(0, true)}] :=
    ((ClauseSet.IsProof.nil.mem (by decide)).mem (by decide)).mem (by decide)
  have h₄ := h₃.resolvent (c₁ := {(0, true)}) (c₂ := {(0, false), (1, true)}) 0 (by decide)
    (by decide) (by decide) (by decide)
  have h₅ := h₄.resolvent (c₁ := {(1, true)}) (c₂ := {(1, false)}) 1 (by decide) (by decide)
    (by decide) (by decide)
  exact h₅

example :
    φ.RefutableInSize 5 ∧
    φ.RefutableInWidth 2 ∧
    ¬ φ.Satisfiable ∧
    φ.restrict 1 false = {{(0, true)}, {(0, false)}} :=
  ⟨⟨proof, isProof, by decide, le_rfl⟩,
    ⟨proof, isProof, by decide, by decide⟩,
    ClauseSet.exists_refutableInSize_iff_not_satisfiable.1 ⟨5, proof, isProof, by decide, le_rfl⟩,
    by decide⟩

example : ∃ ls, (φ.restrict 1 false).IsProof ls ∧ ∅ ∈ ls ∧ ls.length ≤ 5 := by
  obtain ⟨ls, h, hlen, hsub, -⟩ := isProof.restrict 1 false
  obtain ⟨c, hc, hsub'⟩ := hsub ∅ (by decide) (by decide)
  obtain rfl : c = ∅ := Finset.eq_empty_iff_forall_notMem.2 fun l hl => by simpa using hsub' l hl
  exact ⟨ls, h, hc, hlen.trans (by decide)⟩

/-- Restricting `φ` by the partial assignment fixing `x₁ ↦ false` gives the same two clauses. -/
example : φ.restrictBy (fun v => if v = 1 then some false else none) =
    {{(0, true)}, {(0, false)}} := by
  decide

example : ∃ ls, (φ.restrictBy (fun v => if v = 1 then some false else none)).IsProof ls ∧
    ∅ ∈ ls ∧ ls.length ≤ 5 := by
  obtain ⟨ls, h, hsub, ks, hks, -, hF⟩ :=
    isProof.restrictBy (fun v => if v = 1 then some false else none)
  obtain ⟨c, hc, hsub'⟩ := hsub ∅ (by decide) (by decide)
  obtain rfl : c = ∅ := Finset.eq_empty_iff_forall_notMem.2 fun l hl => by simpa using hsub' l hl
  exact ⟨ls, h, hc, hF.length_eq.trans_le (hks.length_le.trans (by decide))⟩

/-! ### Tree-like refutations and decision trees -/

/-- `x₀ ∧ ¬x₀`. -/
private def ψ : ClauseSet ℕ := {{(0, true)}, {(0, false)}}

/-- The tree-like refutation of `ψ`, resolving its two clauses. -/
private def treeRefutation : ψ.Derivation ∅ :=
  .resolvent (c₁ := {(0, true)}) (c₂ := {(0, false)}) 0 (.mem (by decide)) (.mem (by decide))
    (by decide) (by decide)

example :
    treeRefutation.size = 3 ∧
    treeRefutation.toDecisionTree = .node 0 (.leaf {(0, true)}) (.leaf {(0, false)}) ∧
    treeRefutation.toDecisionTree.FindsFalsifiedClause ψ :=
  ⟨rfl, rfl, treeRefutation.findsFalsifiedClause_toDecisionTree⟩

/-- A DPLL tree querying `x₀` twice finds a falsified clause; it gives a tree-like refutation. -/
private def dpllTree : DecisionTree ℕ (FiniteClause ℕ) :=
  .node 0 (.leaf {(0, true)}) (.node 0 (.leaf {(0, true)}) (.leaf {(0, false)}))

private theorem findsFalsifiedClause_dpllTree : dpllTree.FindsFalsifiedClause ψ := fun σ => by
  cases h : σ 0 <;>
    simp [dpllTree, DecisionTree.eval, h, ψ, FiniteClause.eval, FiniteClause.Sat]

example : ∃ d : ψ.Derivation ∅, d.size + 1 ≤ 6 :=
  findsFalsifiedClause_dpllTree.exists_derivation

/-! ### Exact tree linearization and DAG sharing -/

/-- `x₀ ∧ (¬x₀ ∨ x₁) ∧ (¬x₀ ∨ ¬x₁)`. Both resolution branches use `x₀`. -/
private def sharingFormula : ClauseSet ℕ :=
  {{(0, true)}, {(0, false), (1, true)}, {(0, false), (1, false)}}

/-- Resolving both binary clauses with `x₀` and then resolving their unit conclusions unfolds
the common premise into two leaves. -/
private def sharingTree : sharingFormula.Derivation ∅ :=
  .resolvent (c₁ := {(1, true)}) (c₂ := {(1, false)}) 1
    (.resolvent (c₁ := {(0, true)}) (c₂ := {(0, false), (1, true)}) 0
      (.mem (by decide)) (.mem (by decide)) (by decide) (by decide))
    (.resolvent (c₁ := {(0, true)}) (c₂ := {(0, false), (1, false)}) 0
      (.mem (by decide)) (.mem (by decide)) (by decide) (by decide))
    (by decide) (by decide)

/-- Both branches point to the same last input line: tail indices `3` and `2` identify the
single occurrence of `x₀`. All indices are relative to the line's earlier tail. -/
private def sharingDAG : Cslib.Logic.PL.Resolution.DAG ℕ :=
  [⟨∅, some (0, 1, 1)⟩,
   ⟨{(1, true)}, some (3, 1, 0)⟩,
   ⟨{(1, false)}, some (2, 1, 0)⟩,
   ⟨{(0, false), (1, true)}, none⟩,
   ⟨{(0, false), (1, false)}, none⟩,
   ⟨{(0, true)}, none⟩]

private theorem valid_sharingDAG : sharingDAG.Valid sharingFormula := by
  simp [sharingDAG, sharingFormula, Cslib.Logic.PL.Resolution.DAG.Valid,
    Cslib.Logic.PL.Resolution.Annotation.Valid, Cslib.Logic.PL.Resolution.DAG.clauses,
    FiniteClause.resolvent]

/-- The tree has seven nodes and its canonical proof has seven lines. The DAG has six nodes
because it shares `x₀`; tree linearization retains the two occurrences. -/
example :
    sharingTree.size = 7 ∧ sharingTree.toLines.length = 7 ∧ sharingDAG.size = 6 ∧
    sharingTree.toLines.count {(0, true)} = 2 ∧ sharingDAG.clauses.count {(0, true)} = 1 ∧
    sharingFormula.IsProof sharingTree.toLines ∧ sharingFormula.IsProof sharingDAG.clauses :=
  ⟨by decide, by decide, by decide, by decide, by decide,
    sharingTree.isProof_toLines, valid_sharingDAG.isProof⟩

/-- The maximum width is two in both representations; the tree-to-line theorem also rejects
width one, rather than merely preserving an upper bound. -/
example :
    sharingTree.width = 2 ∧ sharingDAG.WidthLE 2 ∧ ¬ sharingDAG.WidthLE 1 ∧
    (∀ c ∈ sharingTree.toLines, c.width ≤ 2) ∧
    ¬ (∀ c ∈ sharingTree.toLines, c.width ≤ 1) ∧
    sharingFormula.RefutableInWidth 2 :=
  ⟨by decide,
    by unfold Cslib.Logic.PL.Resolution.DAG.WidthLE; decide,
    by unfold Cslib.Logic.PL.Resolution.DAG.WidthLE; decide,
    (sharingTree.width_le_iff 2).1 (by decide),
    fun h => (by decide : ¬ sharingTree.width ≤ 1) ((sharingTree.width_le_iff 1).2 h),
    sharingTree.refutableInWidth⟩

example : ∃ ls, ψ.IsProof ls ∧ ∅ ∈ ls ∧ ls.length = 3 := treeRefutation.exists_isProof

/-! ### CSLib `InferenceSystem` bridge -/

private def inferenceRefutation : ⇓(ψ, (∅ : FiniteClause ℕ)) := treeRefutation

private def setRefutation : {d // d ∈ ψ}⇓(∅ : FiniteClause ℕ) := treeRefutation

example :
    InferenceSystem.Derivable (ψ, (∅ : FiniteClause ℕ)) ∧
    InferenceSystem.DerivableIn {d | d ∈ ψ} (∅ : FiniteClause ℕ) ∧
    (ψ.Derives ∅ ↔ InferenceSystem.Derivable (ψ, (∅ : FiniteClause ℕ))) ∧
    (ψ.Derives ∅ ↔ InferenceSystem.DerivableIn {d | d ∈ ψ} (∅ : FiniteClause ℕ)) ∧
    ψ.Derives ∅ :=
  ⟨⟨inferenceRefutation⟩, ⟨setRefutation⟩, ClauseSet.derives_iff_derivable,
    ClauseSet.derives_iff_derivableIn,
    ClauseSet.derives_iff_derivable.2 ⟨inferenceRefutation⟩⟩

/-! ### The size–width tradeoff -/

/-- Short tree-like refutations are narrow (`3 ≤ 2 ^ 2` nodes give width at most `1 + 2`), and the
size–width tradeoff bounds refutation width from refutation size. -/
example :
    ψ.RefutableInWidth 3 ∧
    ψ.RefutableInWidth (max 1 1 + 2) ∧
    ∃ w : ℕ, φ.RefutableInWidth w ∧ (w : ℝ) ≤ 2 + 2 * √(2 * 2 * Real.log 5) + 2 := by
  refine ⟨ClauseSet.RefutableInWidth.of_derivation (k := 1) (b := 2) (by decide) treeRefutation
      rfl (by decide),
    ClauseSet.RefutableInWidth.of_refutableInSize (s := 3) (N := 1) (by decide) (by decide)
      treeRefutation.refutableInSize (by decide), ?_⟩
  exact_mod_cast ClauseSet.exists_refutableInWidth_le_of_refutableInSize (k := 2) (N := 2)
    (by decide) (by decide) ⟨proof, isProof, by decide, le_rfl⟩

/-- The size–width theorem includes the boundary case of no variables and one proof line. -/
example : ∃ w : ℕ, ClauseSet.RefutableInWidth ({∅} : ClauseSet ℕ) w ∧ (w : ℝ) ≤ 2 := by
  have hs : ClauseSet.RefutableInSize ({∅} : ClauseSet ℕ) 1 :=
    ⟨[∅], ClauseSet.IsProof.nil.mem (by simp), by simp, le_rfl⟩
  simpa using ClauseSet.exists_refutableInWidth_le_of_refutableInSize (k := 0) (N := 0)
    (by simp [FiniteClause.width]) (by decide) hs

/-- The empty, satisfiable formula has no resolution refutation. -/
example : ¬ ∃ s, ClauseSet.RefutableInSize (∅ : ClauseSet ℕ) s := by
  rw [ClauseSet.exists_refutableInSize_iff_not_satisfiable, not_not]
  exact ⟨fun _ => false, by simp [ClauseSet.Sat]⟩

end ComplexityTests.ProofComplexity.Resolution
