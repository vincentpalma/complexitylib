/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Resolution.DAG
import Mathlib.Data.List.GetD

/-!
# Computational representations of resolution certificates

Bare certificates are lists of raw list clauses. Their meaning is exactly `List.map List.toFinset`,
validated by the sole mathematical line calculus `ClauseSet.IsProof`. Annotated certificates add
tail-relative premise indices and pivots, and denote explicit finite-clause DAGs. Literal order,
repeated literals and repeated lines are retained in both computational representations.

`Certificate.annotate` finds input clauses extensionally and otherwise searches every pair of
earlier lines and every pivot occurring in the first. It keeps the raw clause sequence verbatim.
No enumeration of an abstract finite set is used by the algorithm. Malformed bare certificates
still receive annotations, but those annotations cannot validate to a mathematical proof.

## Main definitions

* `Cslib.Logic.PL.Resolution.Certificate`: raw list-clause certificates.
* `Cslib.Logic.PL.Resolution.AnnotatedCertificate`: raw clauses with explicit justifications.
* `Cslib.Logic.PL.Resolution.Certificate.denote`: the mathematical finite-clause sequence.
* `Cslib.Logic.PL.Resolution.Certificate.annotate`: executable premise and pivot search.

## Main results

* `Cslib.Logic.PL.Resolution.Certificate.annotate_valid_iff`: annotations validate exactly when
  the represented mathematical line sequence is a proof.
* `Cslib.Logic.PL.Resolution.Certificate.erase_annotate`: annotation preserves every raw line.
* `Cslib.Logic.PL.CNF.refutableInSize_iff_exists_certificate`,
  `Cslib.Logic.PL.CNF.refutableInWidth_iff_exists_certificate`: finite refutations and accepted
  raw certificates have exactly the same line-count and finite-width bounds.
* `Cslib.Logic.PL.CNF.refutableInSize_iff_exists_annotatedCertificate`,
  `Cslib.Logic.PL.CNF.refutableInWidth_iff_exists_annotatedCertificate`: the same resource
  correspondence for accepted annotated certificates.

Erasure translates valid annotated proofs to bare proofs. An invalid annotation can erase to a
valid bare proof, and re-annotation may choose different edges or pivots. The correspondence
preserves clause sequences, line counts and width; it makes no claim about preserving topology
or clause space. The refutation checkers additionally require an empty line.
-/

public section

namespace Cslib.Logic.PL.Resolution

variable {V : Type*} [DecidableEq V]

/-- A bare computational certificate. This is syntax, not a second resolution calculus. -/
abbrev Certificate (V : Type*) := List (Clause V)

/-- A certificate with explicit justifications; indices refer to the line's earlier tail. -/
abbrev AnnotatedCertificate (V : Type*) := List (Clause V × Annotation V)

namespace Certificate

/-- The mathematical line sequence represented by raw clauses. -/
@[expose] def denote (ls : Certificate V) : List (FiniteClause V) := ls.map List.toFinset

/-- Every finite-clause sequence has a raw representation with exactly that denotation. This is
only a representation-existence theorem; it asserts no algorithm for serializing abstract
finsets. -/
theorem exists_denote (lines : List (FiniteClause V)) :
    ∃ ls : Certificate V, ls.denote = lines := by
  refine ⟨lines.map Finset.toList, ?_⟩
  simp [denote, List.map_map, Function.comp_def]

/-- A raw list representing finite-set resolution. Only its denotation is used for validation. -/
@[expose] def resolveLiterals (positive negative : Clause V) (pivot : V) : Clause V :=
  positive.filter (fun l => decide (l ≠ (pivot, true))) ++
    negative.filter (fun l => decide (l ≠ (pivot, false)))

/-- Computing a raw resolvent and then forgetting order and multiplicity is finite-set
resolution. -/
@[simp] theorem toFinset_resolveLiterals (positive negative : Clause V) (pivot : V) :
    (resolveLiterals positive negative pivot).toFinset =
      FiniteClause.resolvent positive.toFinset negative.toFinset pivot := by
  ext l
  simp [resolveLiterals, FiniteClause.mem_resolvent]

/-- A search candidate carries its two raw premises with indices, and a pivot. The extra raw
premises are temporary search data; output annotations retain only the indices and pivot. -/
abbrev Candidate (V : Type*) := (Clause V × ℕ) × (Clause V × ℕ) × V

/-- Enumerate all earlier premise pairs, trying the variable of every literal in the first. -/
@[expose] def candidates (earlier : Certificate V) : List (Candidate V) :=
  earlier.zipIdx.flatMap fun positive => earlier.zipIdx.flatMap fun negative =>
    positive.1.map fun literal => (positive, negative, literal.1)

/-- The explicit premise indices and pivot carried by a candidate. -/
@[expose] def Candidate.annotation : Candidate V → ℕ × ℕ × V
  | ((_, positive), (_, negative), pivot) => (positive, negative, pivot)

/-- Test a candidate by pivot occurrence and equality of its finite-clause denotation. -/
@[expose] def Candidate.matches (conclusion : Clause V) : Candidate V → Bool
  | ((positive, _), (negative, _), pivot) =>
      decide ((pivot, true) ∈ positive) && decide ((pivot, false) ∈ negative) &&
        (resolveLiterals positive negative pivot).sameLiterals conclusion

/-- Find a justification without inspecting any noncomputable finite-set enumeration. An input
clause is preferred; a failed resolution search also returns `none`, which will fail validation
unless the represented clause is an input. -/
@[expose] def annotateLine (formula : CNF V) (earlier : Certificate V)
    (c : Clause V) : Annotation V :=
  if formula.any (fun d => d.sameLiterals c) then none
  else ((candidates earlier).find? (Candidate.matches c)).map Candidate.annotation

/-- Add justifications, retaining the last-to-first order of the bare certificate. -/
@[expose] def annotate (formula : CNF V) (ls : Certificate V) : AnnotatedCertificate V :=
  ls.zipIdx.map fun (c, index) => (c, annotateLine formula (ls.drop (index + 1)) c)

end Certificate

/-- Execute one explicit justification. Out-of-range premise indices are rejected. -/
@[expose] def Annotation.check (formula : CNF V) (earlier : Certificate V) (c : Clause V) :
    Annotation V → Bool
  | none => formula.any (fun d => d.sameLiterals c)
  | some (i, j, v) =>
      match earlier[i]?, earlier[j]? with
      | some positive, some negative =>
          Certificate.Candidate.matches c ((positive, i), (negative, j), v)
      | _, _ => false

namespace AnnotatedCertificate

/-- Erase annotations, keeping all raw list syntax. -/
@[expose] def erase (ls : AnnotatedCertificate V) : Certificate V := ls.map Prod.fst

/-- Interpret raw clauses as finite clauses while retaining their explicit justifications. -/
@[expose] def denote (ls : AnnotatedCertificate V) : DAG V :=
  ls.map fun (c, annotation) => ⟨c.toFinset, annotation⟩

/-- Every finite-clause DAG has a raw representation preserving its clauses, edges and pivots.
This existential statement does not certify efficient serialization of abstract finite sets. -/
theorem exists_denote (d : DAG V) : ∃ ls : AnnotatedCertificate V, ls.denote = d := by
  refine ⟨d.map (fun line => (line.clause.toList, line.annotation)), ?_⟩
  induction d with
  | nil => rfl
  | cons line earlier ih =>
    cases line
    simpa only [denote, List.map_cons, Finset.toList_toFinset] using congrArg (List.cons _) ih

/-- Check every raw line using only its earlier tail. -/
@[expose] def check (formula : CNF V) (ls : AnnotatedCertificate V) : Bool :=
  ls.zipIdx.all fun ((c, annotation), index) =>
    annotation.check formula (ls.erase.drop (index + 1)) c

/-- The mathematical clauses of an annotated certificate are exactly its erased denotation. -/
@[simp] theorem clauses_denote (ls : AnnotatedCertificate V) :
    ls.denote.clauses = (erase ls).denote := by
  simp [denote, DAG.clauses, erase, Certificate.denote, List.map_map, Function.comp_def]

/-- Interpreting annotations preserves the exact number of lines. -/
@[simp] theorem size_denote (ls : AnnotatedCertificate V) : ls.denote.size = ls.length :=
  List.length_map ..

omit [DecidableEq V] in
/-- Erasure preserves the exact number of lines. -/
@[simp] theorem length_erase (ls : AnnotatedCertificate V) : ls.erase.length = ls.length :=
  List.length_map ..

/-- The finite-cardinal width of every line is unchanged by erasing annotations. -/
theorem widthLE_denote_iff (ls : AnnotatedCertificate V) (w : ℕ) :
    ls.denote.WidthLE w ↔ ∀ c ∈ ls.erase, FiniteClause.width c.toFinset ≤ w := by
  simp [DAG.WidthLE, Certificate.denote]

/-- A valid annotated certificate denotes a proof of exactly its erased clause sequence. -/
theorem isProof_of_valid {formula : CNF V} {ls : AnnotatedCertificate V}
    (h : ls.denote.Valid formula.toClauseSet) : formula.toClauseSet.IsProof ls.erase.denote := by
  simpa only [clauses_denote] using h.isProof

end AnnotatedCertificate

namespace Certificate

variable {formula : CNF V} {earlier : Certificate V} {c : Clause V}

omit [DecidableEq V] in
/-- Every enumerated candidate uses precisely the earlier clauses named by its indices. -/
theorem mem_candidates {t : Candidate V} (ht : t ∈ candidates earlier) :
    earlier[t.1.2]? = some t.1.1 ∧ earlier[t.2.1.2]? = some t.2.1.1 := by
  obtain ⟨positive, hp, ht⟩ := List.mem_flatMap.1 ht
  obtain ⟨negative, hn, ht⟩ := List.mem_flatMap.1 ht
  obtain ⟨literal, _, rfl⟩ := List.mem_map.1 ht
  exact ⟨List.mem_zipIdx_iff_getElem?.1 hp, List.mem_zipIdx_iff_getElem?.1 hn⟩

omit [DecidableEq V] in
/-- Every legal resolution step among the earlier raw clauses occurs in the search. -/
theorem mem_candidates_of_getElem {i j : ℕ} (hi : i < earlier.length) (hj : j < earlier.length)
    {v : V} (hv : (v, true) ∈ earlier[i]) :
    ((earlier[i], i), (earlier[j], j), v) ∈ candidates earlier := by
  exact List.mem_flatMap.2 ⟨(earlier[i], i), List.mem_zipIdx_iff_getElem?.2 (by simp),
    List.mem_flatMap.2 ⟨(earlier[j], j), List.mem_zipIdx_iff_getElem?.2 (by simp),
      List.mem_map.2 ⟨(v, true), hv, rfl⟩⟩⟩

/-- Candidate validation is exactly the finite-clause resolution rule. -/
theorem Candidate.matches_eq_true_iff (positive negative : Clause V) (i j : ℕ) (v : V) :
    Candidate.matches c ((positive, i), (negative, j), v) = true ↔
      (v, true) ∈ positive.toFinset ∧ (v, false) ∈ negative.toFinset ∧
        c.toFinset = FiniteClause.resolvent positive.toFinset negative.toFinset v := by
  simp only [Candidate.matches, Bool.and_eq_true, decide_eq_true_eq,
    Clause.sameLiterals_eq_true_iff, toFinset_resolveLiterals, List.mem_toFinset]
  tauto

/-- Input-clause search compares finite clauses, independently of their order and repetitions. -/
theorem any_sameLiterals_eq_true_iff :
    formula.any (fun d => d.sameLiterals c) = true ↔ c.toFinset ∈ formula.toClauseSet := by
  simp only [List.any_eq_true, Clause.sameLiterals_eq_true_iff, CNF.mem_toClauseSet]

/-- Whenever a mathematical line has a justification, the executable scanner finds one. -/
theorem annotateLine_valid
    (h : c.toFinset ∈ formula.toClauseSet ∨
      ∃ c₁ ∈ earlier.denote, ∃ c₂ ∈ earlier.denote, ∃ v,
        (v, true) ∈ c₁ ∧ (v, false) ∈ c₂ ∧ c.toFinset = c₁.resolvent c₂ v) :
    (annotateLine formula earlier c).Valid formula.toClauseSet earlier.denote c.toFinset := by
  unfold annotateLine
  split_ifs with hinput
  · exact any_sameLiterals_eq_true_iff.mp hinput
  have hnot : c.toFinset ∉ formula.toClauseSet :=
    fun hc => hinput (any_sameLiterals_eq_true_iff.mpr hc)
  obtain ⟨c₁, h₁, c₂, h₂, v, hv₁, hv₂, hc⟩ := h.resolve_left hnot
  obtain ⟨positive, hp, rfl⟩ := List.mem_map.1 h₁
  obtain ⟨negative, hn, rfl⟩ := List.mem_map.1 h₂
  obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
  obtain ⟨j, hj, hnj⟩ := List.getElem_of_mem hn
  have hcandidate := mem_candidates_of_getElem hi hj (hpi.symm ▸ List.mem_toFinset.1 hv₁)
  have hmatches : Candidate.matches c ((earlier[i], i), (earlier[j], j), v) = true :=
    (Candidate.matches_eq_true_iff ..).mpr (by simpa only [hpi, hnj] using ⟨hv₁, hv₂, hc⟩)
  cases hfind : (candidates earlier).find? (Candidate.matches c) with
  | none => exact False.elim (List.find?_eq_none.1 hfind _ hcandidate hmatches)
  | some t =>
    have ht := mem_candidates (List.mem_of_find?_eq_some hfind)
    have hm := List.find?_some hfind
    rcases t with ⟨⟨positive, i⟩, ⟨negative, j⟩, v⟩
    obtain ⟨hv₁, hv₂, hc⟩ := (Candidate.matches_eq_true_iff ..).mp hm
    refine ⟨positive.toFinset, negative.toFinset, ?_, ?_, hv₁, hv₂, hc⟩
    · simp only [denote, List.getElem?_map, ht.1, Option.map_some]
    · simp only [denote, List.getElem?_map, ht.2, Option.map_some]

/-- Annotation of a new last line only inspects its earlier tail. -/
@[simp] theorem annotate_cons (formula : CNF V) (c : Clause V) (earlier : Certificate V) :
    annotate formula (c :: earlier) =
      (c, annotateLine formula earlier c) :: annotate formula earlier := by
  simp only [annotate, List.zipIdx_cons', List.map_cons, List.map_map]
  rfl

/-- Adding annotations preserves the raw clause sequence, including every literal occurrence. -/
@[simp] theorem erase_annotate (formula : CNF V) (ls : Certificate V) :
    (annotate formula ls).erase = ls := by
  induction ls with
  | nil => rfl
  | cons c earlier ih =>
      simpa only [annotate_cons, AnnotatedCertificate.erase, List.map_cons]
      using congrArg (List.cons c) ih

/-- Annotation is correct precisely for the bare certificates that denote mathematical proofs. -/
theorem annotate_valid_iff (formula : CNF V) (ls : Certificate V) :
    (annotate formula ls).denote.Valid formula.toClauseSet ↔
      formula.toClauseSet.IsProof ls.denote := by
  constructor
  · intro h
    simpa only [AnnotatedCertificate.clauses_denote, erase_annotate] using h.isProof
  · intro h
    induction ls with
    | nil => trivial
    | cons c earlier ih =>
      obtain ⟨htail, hline⟩ := ClauseSet.IsProof.cons_iff.mp h
      rw [annotate_cons]
      refine ⟨ih htail, ?_⟩
      change (annotateLine formula earlier c).Valid formula.toClauseSet
        (annotate formula earlier).denote.clauses c.toFinset
      rw [AnnotatedCertificate.clauses_denote, erase_annotate]
      exact annotateLine_valid hline

/-- Adding annotations preserves the exact number of lines. -/
@[simp] theorem length_annotate (formula : CNF V) (ls : Certificate V) :
    (annotate formula ls).length = ls.length := by
  simp [annotate]

/-- Width bounds count distinct literals and are exactly preserved by annotation. -/
theorem widthLE_annotate_iff (formula : CNF V) (ls : Certificate V) (w : ℕ) :
    (annotate formula ls).denote.WidthLE w ↔ ∀ c ∈ ls.denote, c.width ≤ w := by
  rw [DAG.WidthLE, AnnotatedCertificate.clauses_denote, erase_annotate]

end Certificate

/-- Executable annotation validation agrees with the mathematical resolution rule. -/
theorem Annotation.check_eq_true_iff (formula : CNF V) (earlier : Certificate V)
    (c : Clause V) (annotation : Annotation V) :
    annotation.check formula earlier c = true ↔
      annotation.Valid formula.toClauseSet earlier.denote c.toFinset := by
  rcases annotation with _ | ⟨i, j, v⟩
  · exact Certificate.any_sameLiterals_eq_true_iff
  · cases hp : earlier[i]? <;> cases hn : earlier[j]?
    all_goals simp [Annotation.check, Annotation.Valid, Certificate.denote,
      List.getElem?_map, hp, hn, Certificate.Candidate.matches_eq_true_iff]

namespace AnnotatedCertificate

/-- Checking a last line checks its earlier tail first and its own explicit justification. -/
@[simp] theorem check_cons (formula : CNF V) (c : Clause V) (annotation : Annotation V)
    (earlier : AnnotatedCertificate V) :
    check formula ((c, annotation) :: earlier) =
      (annotation.check formula earlier.erase c && check formula earlier) := by
  simp only [check, List.zipIdx_cons', List.all_cons, List.all_map]
  rfl

/-- The executable verifier accepts exactly the annotated finite-clause DAG proofs. -/
@[simp] theorem check_eq_true_iff (formula : CNF V) (ls : AnnotatedCertificate V) :
    ls.check formula = true ↔ ls.denote.Valid formula.toClauseSet := by
  induction ls with
  | nil => simp [check, denote, DAG.Valid]
  | cons line earlier ih =>
    rcases line with ⟨c, annotation⟩
    rw [check_cons, Bool.and_eq_true, ih, Annotation.check_eq_true_iff]
    change (_ ∧ _) ↔ ((denote earlier).Valid formula.toClauseSet ∧
      annotation.Valid formula.toClauseSet (denote earlier).clauses c.toFinset)
    rw [clauses_denote]
    exact and_comm

end AnnotatedCertificate

namespace Certificate

/-- Verify a bare certificate by finding and checking explicit justifications. -/
@[expose] def check (formula : CNF V) (ls : Certificate V) : Bool :=
  (annotate formula ls).check formula

/-- The bare verifier accepts exactly the finite-clause line proofs. -/
@[simp] theorem check_eq_true_iff (formula : CNF V) (ls : Certificate V) :
    ls.check formula = true ↔ formula.toClauseSet.IsProof ls.denote := by
  rw [check, AnnotatedCertificate.check_eq_true_iff, annotate_valid_iff]

/-- An empty raw clause occurs exactly when the denoted proof has an empty finite clause. -/
theorem any_isEmpty_eq_true_iff (ls : Certificate V) :
    ls.any List.isEmpty = true ↔ (∅ : FiniteClause V) ∈ ls.denote := by
  simp [denote, List.any_eq_true]

/-- Check a bare refutation: a valid line proof must also contain the empty clause. -/
@[expose] def checkRefutation (formula : CNF V) (ls : Certificate V) : Bool :=
  ls.check formula && ls.any List.isEmpty

/-- The bare refutation verifier accepts exactly line proofs containing the empty clause. -/
@[simp] theorem checkRefutation_eq_true_iff (formula : CNF V) (ls : Certificate V) :
    ls.checkRefutation formula = true ↔
      formula.toClauseSet.IsProof ls.denote ∧ (∅ : FiniteClause V) ∈ ls.denote := by
  rw [checkRefutation, Bool.and_eq_true, check_eq_true_iff, any_isEmpty_eq_true_iff]

/-- An accepted bare refutation proves unsatisfiability of the represented formula. -/
theorem not_satisfiable_of_checkRefutation {formula : CNF V} {ls : Certificate V}
    (h : ls.checkRefutation formula = true) : ¬ formula.Satisfiable := by
  obtain ⟨hp, he⟩ := (checkRefutation_eq_true_iff formula ls).mp h
  have hnot := ClauseSet.derives_empty_iff_not_satisfiable.mp (hp.derives he)
  exact fun hs => hnot ((CNF.satisfiable_toClauseSet_iff formula).mpr hs)

end Certificate

namespace AnnotatedCertificate

/-- Check an annotated refutation, retaining and validating its given edges and pivots. -/
@[expose] def checkRefutation (formula : CNF V) (ls : AnnotatedCertificate V) : Bool :=
  ls.check formula && ls.erase.any List.isEmpty

/-- The annotated refutation verifier validates the given DAG and requires an empty line. -/
@[simp] theorem checkRefutation_eq_true_iff (formula : CNF V) (ls : AnnotatedCertificate V) :
    ls.checkRefutation formula = true ↔
      ls.denote.Valid formula.toClauseSet ∧ (∅ : FiniteClause V) ∈ ls.denote.clauses := by
  rw [checkRefutation, Bool.and_eq_true, check_eq_true_iff,
    Certificate.any_isEmpty_eq_true_iff, clauses_denote]

/-- An accepted annotated refutation proves unsatisfiability; invalid annotations are rejected
even if their erasure happens to be a valid bare refutation. -/
theorem not_satisfiable_of_checkRefutation {formula : CNF V} {ls : AnnotatedCertificate V}
    (h : ls.checkRefutation formula = true) : ¬ formula.Satisfiable := by
  obtain ⟨hp, he⟩ := (checkRefutation_eq_true_iff formula ls).mp h
  apply Certificate.not_satisfiable_of_checkRefutation (ls := ls.erase)
  rw [Certificate.checkRefutation_eq_true_iff]
  exact ⟨isProof_of_valid hp, clauses_denote ls ▸ he⟩

/-- Erasure translates accepted annotated refutations to accepted bare refutations. The converse
fails for arbitrary annotations: bad edges and pivots can erase to a valid bare proof. -/
theorem checkRefutation_erase_of_checkRefutation {formula : CNF V}
    {ls : AnnotatedCertificate V} (h : ls.checkRefutation formula = true) :
    ls.erase.checkRefutation formula = true := by
  obtain ⟨hp, he⟩ := (checkRefutation_eq_true_iff formula ls).mp h
  rw [Certificate.checkRefutation_eq_true_iff]
  exact ⟨isProof_of_valid hp, clauses_denote ls ▸ he⟩

end AnnotatedCertificate

namespace Certificate

/-- Adding computed annotations preserves acceptance of bare refutations. -/
@[simp] theorem checkRefutation_annotate (formula : CNF V) (ls : Certificate V) :
    (annotate formula ls).checkRefutation formula = ls.checkRefutation formula := by
  rw [AnnotatedCertificate.checkRefutation, erase_annotate]
  rfl

end Certificate

end Cslib.Logic.PL.Resolution

namespace Cslib.Logic.PL.Resolution.Certificate

variable {V : Type*} [DecidableEq V] {formula : CNF V} {ls : Certificate V}

/-- An accepted certificate gives a finite refutation with exactly its number of raw lines. -/
theorem refutableInSize_of_checkRefutation (h : ls.checkRefutation formula = true) :
    formula.toClauseSet.RefutableInSize ls.length := by
  obtain ⟨hp, he⟩ := (checkRefutation_eq_true_iff formula ls).mp h
  exact ⟨ls.denote, hp, he, by simp [denote]⟩

/-- An accepted certificate with bounded distinct-literal widths gives a finite width-bounded
refutation. Literal repetitions in the raw syntax do not contribute to this width. -/
theorem refutableInWidth_of_checkRefutation {w : ℕ} (h : ls.checkRefutation formula = true)
    (hw : ∀ c ∈ ls, FiniteClause.width c.toFinset ≤ w) :
    formula.toClauseSet.RefutableInWidth w := by
  obtain ⟨hp, he⟩ := (checkRefutation_eq_true_iff formula ls).mp h
  refine ⟨ls.denote, hp, he, ?_⟩
  intro c hc
  obtain ⟨raw, hraw, rfl⟩ := List.mem_map.1 hc
  exact hw raw hraw

/-- Every finite refutation has an accepted raw presentation of its entire line sequence.
The chosen clauses have no repeated literals, so their raw lengths equal their finite widths.
This is existence only: finset enumeration occurs inside the proof, and no algorithm or bit-cost
bound for serializing abstract finite sets is asserted. -/
theorem exists_checkRefutation {lines : List (FiniteClause V)}
    (hp : formula.toClauseSet.IsProof lines) (he : ∅ ∈ lines) :
    ∃ cert : Certificate V, cert.checkRefutation formula = true ∧ cert.denote = lines ∧
      ∀ c ∈ cert, c.Nodup ∧ c.length = FiniteClause.width c.toFinset := by
  let cert : Certificate V := lines.map Finset.toList
  have hdenote : cert.denote = lines := by
    simp [cert, denote, List.map_map, Function.comp_def]
  refine ⟨cert, ?_, hdenote, ?_⟩
  · rw [checkRefutation_eq_true_iff, hdenote]
    exact ⟨hp, he⟩
  · intro c hc
    obtain ⟨finite, _, rfl⟩ := List.mem_map.1 hc
    exact ⟨Finset.nodup_toList finite, by simp [FiniteClause.width]⟩

end Cslib.Logic.PL.Resolution.Certificate

namespace Cslib.Logic.PL.Resolution.AnnotatedCertificate

variable {V : Type*} [DecidableEq V] {formula : CNF V} {ls : AnnotatedCertificate V}

/-- An accepted annotated certificate gives a finite refutation with the same line count. -/
theorem refutableInSize_of_checkRefutation (h : ls.checkRefutation formula = true) :
    formula.toClauseSet.RefutableInSize ls.length := by
  have hs := Certificate.refutableInSize_of_checkRefutation
    (checkRefutation_erase_of_checkRefutation h)
  simpa only [length_erase] using hs

/-- An accepted annotated certificate with bounded finite-clause widths gives a refutation
within precisely that width bound. -/
theorem refutableInWidth_of_checkRefutation {w : ℕ} (h : ls.checkRefutation formula = true)
    (hw : ls.denote.WidthLE w) : formula.toClauseSet.RefutableInWidth w := by
  obtain ⟨hp, he⟩ := (checkRefutation_eq_true_iff formula ls).mp h
  exact ⟨ls.denote.clauses, hp.isProof, he, hw⟩

end Cslib.Logic.PL.Resolution.AnnotatedCertificate

namespace Cslib.Logic.PL.CNF

open Resolution

variable {V : Type*} [DecidableEq V]

/-- Finite size-bounded refutations are exactly accepted raw certificates with the same line
bound. The existential direction asserts no computational finset serialization. -/
theorem refutableInSize_iff_exists_certificate (formula : CNF V) (s : ℕ) :
    formula.toClauseSet.RefutableInSize s ↔
      ∃ cert : Certificate V, cert.checkRefutation formula = true ∧ cert.length ≤ s := by
  constructor
  · rintro ⟨lines, hp, he, hsize⟩
    obtain ⟨cert, hcert, hdenote, _⟩ := Certificate.exists_checkRefutation hp he
    have hlength : cert.length = lines.length := by
      simpa only [Certificate.denote, List.length_map] using congrArg List.length hdenote
    exact ⟨cert, hcert, hlength.trans_le hsize⟩
  · rintro ⟨cert, hcert, hsize⟩
    exact (Certificate.refutableInSize_of_checkRefutation hcert).mono hsize

/-- Finite width-bounded refutations are exactly accepted raw certificates with the same
distinct-literal width bound, independently of raw literal multiplicity. -/
theorem refutableInWidth_iff_exists_certificate (formula : CNF V) (w : ℕ) :
    formula.toClauseSet.RefutableInWidth w ↔ ∃ cert : Certificate V,
      cert.checkRefutation formula = true ∧ ∀ c ∈ cert, FiniteClause.width c.toFinset ≤ w := by
  constructor
  · rintro ⟨lines, hp, he, hwidth⟩
    obtain ⟨cert, hcert, hdenote, _⟩ := Certificate.exists_checkRefutation hp he
    refine ⟨cert, hcert, fun c hc => hwidth c.toFinset ?_⟩
    exact hdenote ▸ List.mem_map.2 ⟨c, hc, rfl⟩
  · rintro ⟨cert, hcert, hwidth⟩
    exact Certificate.refutableInWidth_of_checkRefutation hcert hwidth

/-- Accepted annotated certificates and finite refutations have the same line-count bounds. -/
theorem refutableInSize_iff_exists_annotatedCertificate (formula : CNF V) (s : ℕ) :
    formula.toClauseSet.RefutableInSize s ↔
      ∃ cert : AnnotatedCertificate V, cert.checkRefutation formula = true ∧ cert.length ≤ s := by
  constructor
  · intro h
    obtain ⟨cert, hcert, hsize⟩ := (refutableInSize_iff_exists_certificate formula s).mp h
    refine ⟨Certificate.annotate formula cert, ?_, ?_⟩
    · simpa only [Certificate.checkRefutation_annotate] using hcert
    · simpa only [Certificate.length_annotate] using hsize
  · rintro ⟨cert, hcert, hsize⟩
    exact (AnnotatedCertificate.refutableInSize_of_checkRefutation hcert).mono hsize

/-- Accepted annotated certificates and finite refutations have the same finite-width bounds. -/
theorem refutableInWidth_iff_exists_annotatedCertificate (formula : CNF V) (w : ℕ) :
    formula.toClauseSet.RefutableInWidth w ↔ ∃ cert : AnnotatedCertificate V,
      cert.checkRefutation formula = true ∧ cert.denote.WidthLE w := by
  constructor
  · intro h
    obtain ⟨cert, hcert, hwidth⟩ := (refutableInWidth_iff_exists_certificate formula w).mp h
    refine ⟨Certificate.annotate formula cert, ?_, ?_⟩
    · simpa only [Certificate.checkRefutation_annotate] using hcert
    · rw [AnnotatedCertificate.widthLE_denote_iff, Certificate.erase_annotate]
      exact hwidth
  · rintro ⟨cert, hcert, hwidth⟩
    exact AnnotatedCertificate.refutableInWidth_of_checkRefutation hcert hwidth

end Cslib.Logic.PL.CNF
