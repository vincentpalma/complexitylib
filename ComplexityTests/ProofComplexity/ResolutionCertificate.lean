/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import Complexity.Logics.Propositional.Resolution.Certificate.PolyTime
public import Complexity.Logics.Propositional.Resolution.Pigeonhole
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Resolution certificate regressions

Executable tests cover repeated literals and lines, shared premises, extensional input clauses,
wrong pivots and polarities, out-of-range binary indices, wrong resolvents, and empty proofs.
-/

public section

namespace ComplexityTests.ProofComplexity.ResolutionCertificate

open Cslib.Logic.PL Cslib.Logic.PL.Resolution Turing.MultiTapeTM

private def units : CNF ℕ := [[(0, true)], [(0, false)]]

private def repeated : Certificate ℕ := [[], [], [(0, true), (0, true)], [(0, false)]]

/-- Both empty lines reuse the same two input premises. -/
example : Certificate.annotate units repeated =
    [([], some (1, 2, 0)), ([], some (0, 1, 0)),
      ([(0, true), (0, true)], none), ([(0, false)], none)] := by decide

example : (Certificate.annotate units repeated).erase = repeated := by decide

example : (Certificate.annotate units repeated).denote.size = 4 := by decide

example : repeated.checkRefutation units = true := by decide

/-- Mathematical validity follows from the executable checker, retaining repeated lines. -/
example : units.toClauseSet.IsProof repeated.denote :=
  (Certificate.check_eq_true_iff units repeated).mp (by decide)

example : ¬ units.Satisfiable :=
  Certificate.not_satisfiable_of_checkRefutation (ls := repeated) (by decide)

/-- Accepted certificates feed the finite resource APIs directly, with the original line count. -/
example : units.toClauseSet.RefutableInSize 4 := by
  exact Certificate.refutableInSize_of_checkRefutation (ls := repeated) (by decide)

example : units.toClauseSet.RefutableInWidth 1 := by
  apply Certificate.refutableInWidth_of_checkRefutation (ls := repeated) (by decide)
  simp [repeated, FiniteClause.width]

/-- Every finite refutation has an accepted presentation whose raw lengths are its distinct
literal widths, rather than lengths inflated by repetitions. -/
example {formula : CNF ℕ} {lines : List (FiniteClause ℕ)}
    (hp : formula.toClauseSet.IsProof lines) (he : ∅ ∈ lines) :
    ∃ cert : Certificate ℕ, cert.checkRefutation formula = true ∧
      cert.length = lines.length ∧ ∀ c ∈ cert,
        c.Nodup ∧ c.length = FiniteClause.width c.toFinset := by
  obtain ⟨cert, hcert, hdenote, hwidth⟩ := Certificate.exists_checkRefutation hp he
  refine ⟨cert, hcert, ?_, hwidth⟩
  simpa only [Certificate.denote, List.length_map] using congrArg List.length hdenote

/-- Repeated occurrences have encoded cost, but do not increase finite-cardinal width. -/
example : (Certificate.annotate units repeated).denote.WidthLE 1 := by
  rw [Certificate.widthLE_annotate_iff]
  simp [Certificate.denote, repeated, FiniteClause.width]

private def wrongPivot : AnnotatedCertificate ℕ :=
  [([], some (0, 1, 1)), ([(0, true)], none), ([(0, false)], none)]

/-- Bad supplied pivots remain invalid even when erasure gives a valid bare refutation. -/
example : wrongPivot.checkRefutation units = false ∧
    wrongPivot.erase.checkRefutation units = true := by decide

private def wrongIndex : AnnotatedCertificate ℕ :=
  [([], some (2 ^ 64, 1, 0)), ([(0, true)], none), ([(0, false)], none)]

/-- Huge out-of-range binary references are rejected, without a validity promise. -/
example : wrongIndex.checkRefutation units = false ∧
    wrongIndex.erase.checkRefutation units = true := by decide

/-- Re-annotation may repair justifications, so it does not preserve arbitrary annotations. -/
example : Certificate.annotate units wrongPivot.erase ≠ wrongPivot := by decide

example : AnnotatedCertificate.check units
    [([], some (0, 0, 0)), ([(0, true)], none)] = false := by decide

example : AnnotatedCertificate.check units
    [([(0, true)], some (0, 1, 0)), ([(0, true)], none), ([(0, false)], none)] = false := by decide

example : AnnotatedCertificate.check units [([(1, true)], none)] = false := by decide

/-- A singleton cannot refer to itself: indices address the strictly earlier tail. -/
example : AnnotatedCertificate.check units [([], some (0, 0, 0))] = false := by decide

/-- Input clauses are compared extensionally, retaining both order and repeated occurrences. -/
example : AnnotatedCertificate.check ([[(0, true), (1, false)]] : CNF ℕ)
    [([(1, false), (0, true), (1, false)], none)] = true := by decide

/-- Using the same tautological premise twice is legal and does not create an empty clause. -/
example : AnnotatedCertificate.check ([[(0, true), (0, false)]] : CNF ℕ)
    [([(0, false), (0, true), (0, true)], some (0, 0, 0)),
      ([(0, true), (0, false)], none)] = true := by decide

/-- Empty sequences are proofs, but are rejected as refutations. -/
example : Certificate.check units [] = true ∧ Certificate.checkRefutation units [] = false := by
  decide

example : AnnotatedCertificate.check units [] = true ∧
    AnnotatedCertificate.checkRefutation units [] = false := by decide

/-- No variable inhabitant is needed for an input empty-clause refutation. -/
example : Certificate.checkRefutation ([[]] : CNF Empty) [[]] = true := by decide

example : Certificate.checkRefutation ([] : CNF Empty) [[]] = false := by decide

/-- Haken's existing lower bound applies to accepted raw certificates through the resource
bridge, without a separate certificate-specific lower-bound theorem. -/
example {n : ℕ} {cert : Certificate (Fin (n + 1) × Fin n)}
    (h : cert.checkRefutation (CNF.pigeonhole (n + 1) n) = true) :
    2 ^ (n / 24) ≤ cert.length :=
  CNF.two_pow_le_of_refutableInSize_pigeonhole
    (Certificate.refutableInSize_of_checkRefutation h)

/-- The same lower bound applies to the given annotated certificate, with no loss in line count. -/
example {n : ℕ} {cert : AnnotatedCertificate (Fin (n + 1) × Fin n)}
    (h : cert.checkRefutation (CNF.pigeonhole (n + 1) n) = true) :
    2 ^ (n / 24) ≤ cert.length :=
  CNF.two_pow_le_of_refutableInSize_pigeonhole
    (AnnotatedCertificate.refutableInSize_of_checkRefutation h)

/-- `fun_prop` composes the public plain certificates with binary natural variable names. -/
theorem computableInPolyTime_annotate_erase_and_check : ComputableInPolyTime
    (fun p : CNF ℕ × Certificate ℕ =>
      ((Certificate.annotate p.1 p.2).erase, Certificate.checkRefutation p.1 p.2))
    (encPair (encCertificate encNat) (encCertificate encNat))
    (encPair (encCertificate encNat) encBool) := by
  fun_prop

end ComplexityTests.ProofComplexity.ResolutionCertificate
