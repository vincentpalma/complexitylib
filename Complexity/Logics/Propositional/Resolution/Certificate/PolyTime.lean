/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Resolution.Certificate
public import Complexity.Logics.Propositional.CNF.ClauseSetPolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time correspondence of resolution certificates

Bare clause-line certificates and annotated certificates admit polynomial-time translations in
both directions. `Certificate.annotate` adds explicit premise indices and pivots without changing
any raw clause. `AnnotatedCertificate.erase` removes those annotations. Their correctness is the
finite-set correspondence in `Resolution.Certificate`, rather than a separate list calculus.
These are proof simulations on valid certificates. Invalid annotations may erase to valid bare
proofs, and the translation back can choose different edges. No DAG topology or clause-space
preservation, or many-one reduction of arbitrary validity languages by erasure, is asserted.

Variables use any fixed binary-word encoding; in particular natural variable names use `encNat`.
Output premise indices use `encNat` too. Search positions are temporarily unary because they are
bounded by the raw list length; converting these positions to binary is certified. Time charges
the complete input formula and certificate encodings, including literal multiplicity and the
lengths of variable names, rather than finite-cardinal width or the number of lines alone.

## Main definitions

* `Cslib.Logic.PL.Resolution.encCertificate`: framed raw clause-line encoding.
* `Cslib.Logic.PL.Resolution.encAnnotatedCertificate`: binary indices and raw clauses.

## Main results

* `Cslib.Logic.PL.Resolution.Certificate.computableInPolyTime_annotate`: add annotations.
* `Cslib.Logic.PL.Resolution.AnnotatedCertificate.computableInPolyTime_erase`: erase annotations.
* `Cslib.Logic.PL.Resolution.Certificate.computableInPolyTime_checkRefutation`,
  `Cslib.Logic.PL.Resolution.AnnotatedCertificate.computableInPolyTime_checkRefutation`:
  polynomial-time refutation verifiers, also rejecting empty proofs.
-/

public section

namespace Cslib.Logic.PL.Resolution

open Turing.MultiTapeTM ComputableInPolyTime

variable {V : Type} [DecidableEq V]

/-- Encoding of bare certificates, charging every raw literal and its full variable encoding. -/
@[expose] def encCertificate (enc : V ↪ List Bool) : Certificate V ↪ List Bool :=
  encList (encList (encPair enc encBool))

/-- Encoding of annotations with binary premise indices. -/
@[expose] def encAnnotation (enc : V ↪ List Bool) : Annotation V ↪ List Bool :=
  encOption (encPair encNat (encPair encNat enc))

/-- Encoding of raw clauses with their binary premise indices and pivots. -/
@[expose] def encAnnotatedCertificate (enc : V ↪ List Bool) : AnnotatedCertificate V ↪ List Bool :=
  encList (encPair (encList (encPair enc encBool)) (encAnnotation enc))

namespace Certificate

variable {encV : V ↪ List Bool}

private theorem resolveLiterals_polyTime :
    ComputableInPolyTime (fun p : (Clause V × Clause V) × V =>
      resolveLiterals p.1.1 p.1.2 p.2)
      (encPair (encPair (encList (encPair encV encBool)) (encList (encPair encV encBool))) encV)
      (encList (encPair encV encBool)) := by
  have hq := id' (encIn := encPair
    (encPair (encList (encPair encV encBool)) (encList (encPair encV encBool))) encV)
  unfold resolveLiterals
  exact listAppend'
    (filterWithInput hq.fst'.fst'
      (decide_not (decide_eq' (snd _ _) ((fst _ _).snd'.prod (const true)))))
    (filterWithInput hq.fst'.snd'
      (decide_not (decide_eq' (snd _ _) ((fst _ _).snd'.prod (const false)))))

/-- The temporary search encoding uses bounded unary positions, retaining the raw premises. -/
@[expose] def encCandidate (enc : V ↪ List Bool) : Candidate V ↪ List Bool :=
  encPair (encPair (encList (encPair enc encBool)) encUnary)
    (encPair (encPair (encList (encPair enc encBool)) encUnary) enc)

omit [DecidableEq V] in
/-- Enumerating every raw premise pair and candidate pivot is polynomial-time in the complete
encoded input. Temporary indices are unary and bounded by the list length. -/
@[fun_prop]
theorem computableInPolyTime_candidates (enc : V ↪ List Bool) :
    ComputableInPolyTime (candidates (V := V)) (encCertificate enc)
      (encList (encCandidate enc)) := by
  have hzip :=
    (ComputableTidilyInPolyTime.zipIdx (encList (encPair enc encBool))).computableInPolyTime
  unfold candidates encCertificate encCandidate
  refine flatMapWithInput hzip (flatMapWithInput (hzip.comp (fst _ _))
    (mapWithInput (fst _ _).snd'.fst' ?_))
  exact (fst _ _).fst'.snd'.prod ((fst _ _).snd'.prod (snd _ _).fst')

private theorem matches_polyTime :
    ComputableInPolyTime (fun p : Clause V × Candidate V => Candidate.matches p.1 p.2)
      (encPair (encList (encPair encV encBool)) (encCandidate encV)) encBool := by
  have hq := id' (encIn := encPair (encList (encPair encV encBool)) (encCandidate encV))
  have hp := hq.snd'.fst'.fst'
  have hn := hq.snd'.snd'.fst'.fst'
  have hv := hq.snd'.snd'.snd'
  have hpos := decide_mem hp (hv.prod (const true))
  have hneg := decide_mem hn (hv.prod (const false))
  have heq := (Clause.computableInPolyTime_sameLiterals encV).comp
    ((resolveLiterals_polyTime.comp ((hp.prod hn).prod hv)).prod hq.fst')
  exact ComputableTidilyInPolyTime.bool_and.computableInPolyTime.comp
    ((ComputableTidilyInPolyTime.bool_and.computableInPolyTime.comp (hpos.prod hneg)).prod heq)

omit [DecidableEq V] in
private theorem annotation_polyTime :
    ComputableInPolyTime (Candidate.annotation (V := V)) (encCandidate encV)
      (encPair encNat (encPair encNat encV)) := by
  have hq := id' (encIn := encCandidate encV)
  have hbin := ComputableTidilyInPolyTime.unary_to_binary.computableInPolyTime
  exact (hbin.comp hq.fst'.snd').prod
    ((hbin.comp hq.snd'.fst'.snd').prod hq.snd'.snd')

private theorem annotateLine_polyTime :
    ComputableInPolyTime (fun p : CNF V × Certificate V × Clause V =>
      annotateLine p.1 p.2.1 p.2.2)
      (encPair (encCertificate encV)
        (encPair (encCertificate encV) (encList (encPair encV encBool))))
      (encAnnotation encV) := by
  have hq := id' (encIn := encPair (encCertificate encV)
    (encPair (encCertificate encV) (encList (encPair encV encBool))))
  have hinput := anyWithInput (test := fun (q : CNF V × Certificate V × Clause V) d =>
      d.sameLiterals q.2.2) hq.fst'
    ((Clause.computableInPolyTime_sameLiterals encV).comp
      ((snd _ _).prod (fst _ _).snd'.snd'))
  have hfind := findWithInput (test := fun (q : CNF V × Certificate V × Clause V) t =>
      Candidate.matches q.2.2 t) ((computableInPolyTime_candidates encV).comp hq.snd'.fst')
    (matches_polyTime.comp ((fst _ _).snd'.snd'.prod (snd _ _)))
  have hmap := optionElimWithInput (encC := encAnnotation encV)
    (body := fun (_ : CNF V × Certificate V × Clause V) t => some (Candidate.annotation t))
    hfind (const (none : Annotation V))
    ((optionSome (encPair encNat (encPair encNat encV))).comp
      (annotation_polyTime.comp (snd _ _)))
  unfold annotateLine
  refine ComputableInPolyTime.ite hinput (const none) ?_
  convert hmap using 1
  funext q
  dsimp only [Function.comp_apply]
  cases (candidates q.2.1).find? (Candidate.matches q.2.2) <;> rfl

/-- Annotating bare certificates is polynomial-time for the full framed input. Premise indices
are written in binary, and no finite-set enumeration is part of this algorithm. -/
@[fun_prop]
theorem computableInPolyTime_annotate (enc : V ↪ List Bool) :
    ComputableInPolyTime (fun p : CNF V × Certificate V => annotate p.1 p.2)
      (encPair (encCertificate enc) (encCertificate enc)) (encAnnotatedCertificate enc) := by
  have hq := id' (encIn := encPair (encCertificate enc) (encCertificate enc))
  have hzip :=
    (ComputableTidilyInPolyTime.zipIdx (encList (encPair enc encBool))).computableInPolyTime
  have hdrop := (ComputableTidilyInPolyTime.dropUnary
    (encA := encList (encPair enc encBool))
    (encL := encList (encList (encPair enc encBool)))).computableInPolyTime
  have hindex : ComputableInPolyTime
      (fun p : (CNF V × Certificate V) × (Clause V × ℕ) => p.2.2 + 1)
      (encPair (encPair (encCertificate enc) (encCertificate enc))
        (encPair (encList (encPair enc encBool)) encUnary)) encUnary :=
    unary_add' (snd _ _).snd' (const 1)
  unfold annotate encAnnotatedCertificate
  exact mapWithInput (hzip.comp hq.snd')
    ((snd _ _).fst'.prod (annotateLine_polyTime.comp
      ((fst _ _).fst'.prod
        ((hdrop.comp ((fst _ _).snd'.prod hindex)).prod (snd _ _).fst'))))

end Certificate

namespace AnnotatedCertificate

omit [DecidableEq V] in
/-- Removing explicit premises and pivots is polynomial-time and retains the raw clause sequence. -/
@[fun_prop]
theorem computableInPolyTime_erase (enc : V ↪ List Bool) :
    ComputableInPolyTime (erase (V := V)) (encAnnotatedCertificate enc) (encCertificate enc) :=
  map (fst _ _)

end AnnotatedCertificate

namespace Certificate

omit [DecidableEq V] in
/-- Optional lookup uses the existing capped binary-index machine, so an enormous out-of-range
index costs its encoded length rather than its numeric value. -/
private theorem lookup_polyTime (enc : V ↪ List Bool) :
    ComputableInPolyTime (fun p : Certificate V × ℕ => p.1[p.2]?)
      (encPair (encCertificate enc) encNat) (encOption (encList (encPair enc encBool))) := by
  have hlist : ComputableInPolyTime (fun p : Certificate V × ℕ => p.1.map some)
      (encPair (encCertificate enc) encNat)
      (encList (encOption (encList (encPair enc encBool)))) :=
    mapWithInput (fst _ _) ((optionSome _).comp (snd _ _))
  have hget := (ComputableTidilyInPolyTime.listGetD_binary
    (encA := encOption (encList (encPair enc encBool)))
    (encL := encList (encOption (encList (encPair enc encBool))))
    (none : Option (Clause V)) hlist.tidy
    (snd (encCertificate enc) encNat).tidy).computableInPolyTime
  convert hget using 1
  funext p
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases p.1[p.2]? <;> rfl

private theorem checkAnnotation_polyTime {encV : V ↪ List Bool} :
    ComputableInPolyTime (fun p : (CNF V × Certificate V × Clause V) × Annotation V =>
      p.2.check p.1.1 p.1.2.1 p.1.2.2)
      (encPair (encPair (encCertificate encV)
        (encPair (encCertificate encV) (encList (encPair encV encBool)))) (encAnnotation encV))
      encBool := by
  have hq := id' (encIn := encPair (encPair (encCertificate encV)
    (encPair (encCertificate encV) (encList (encPair encV encBool)))) (encAnnotation encV))
  have hinput := anyWithInput
    (test := fun (q : (CNF V × Certificate V × Clause V) × Annotation V) d =>
      d.sameLiterals q.1.2.2) hq.fst'.fst'
    ((Clause.computableInPolyTime_sameLiterals encV).comp
      ((snd _ _).prod (fst _ _).fst'.snd'.snd'))
  have hr := id' (encIn := encPair
    (encPair (encPair (encCertificate encV)
      (encPair (encCertificate encV) (encList (encPair encV encBool)))) (encAnnotation encV))
    (encPair encNat (encPair encNat encV)))
  have hi := hr.snd'.fst'
  have hj := hr.snd'.snd'.fst'
  have hv := hr.snd'.snd'.snd'
  have he := hr.fst'.fst'.snd'.fst'
  have hpos := (lookup_polyTime encV).comp (he.prod hi)
  have hneg := (lookup_polyTime encV).comp (he.prod hj)
  have hmatch := matches_polyTime (encV := encV)
  -- The candidate matcher ignores positions, so temporary dummy indices need no binary decode.
  let R := ((CNF V × Certificate V × Clause V) × Annotation V) × (ℕ × ℕ × V)
  have hbody := optionElimWithInput (encC := encBool)
    (body := fun (q : R) positive => (q.1.1.2.1[q.2.2.1]?).elim false fun negative =>
      Candidate.matches q.1.1.2.2 ((positive, 0), (negative, 0), q.2.2.2)) hpos (const false)
    (optionElimWithInput (encC := encBool)
      (body := fun (q : R × Clause V) negative =>
        Candidate.matches q.1.1.1.2.2 ((q.2, 0), (negative, 0), q.1.2.2.2))
      (hneg.comp (fst _ _)) (const false)
      (hmatch.comp
        (((fst _ _).fst'.fst'.fst'.snd'.snd').prod
          (((fst _ _).snd'.prod (const 0)).prod
            (((snd _ _).prod (const 0)).prod (fst _ _).fst'.snd'.snd'.snd')))))
  have hall := optionElimWithInput (encC := encBool)
    (body := fun (q : (CNF V × Certificate V × Clause V) × Annotation V) (r : ℕ × ℕ × V) =>
      (q.1.2.1[r.1]?).elim false fun positive => (q.1.2.1[r.2.1]?).elim false fun negative =>
        Candidate.matches q.1.2.2 ((positive, 0), (negative, 0), r.2.2))
    hq.snd' hinput hbody
  convert hall using 1
  funext p
  rcases p.2 with _ | ⟨i, j, v⟩
  · rfl
  · dsimp only [Function.comp_apply, Annotation.check, Option.elim_some]
    cases p.1.2.1[i]? <;> cases p.1.2.1[j]? <;> rfl

end Certificate

namespace AnnotatedCertificate

/-- Checking explicit certificates is polynomial-time in raw input bits, with binary premise
indices. No validity promise or bound on the numeric value of an index is required. -/
@[fun_prop]
theorem computableInPolyTime_check (enc : V ↪ List Bool) :
    ComputableInPolyTime (fun p : CNF V × AnnotatedCertificate V => check p.1 p.2)
      (encPair (encCertificate enc) (encAnnotatedCertificate enc)) encBool := by
  have hq := id' (encIn := encPair (encCertificate enc) (encAnnotatedCertificate enc))
  have hzip := (ComputableTidilyInPolyTime.zipIdx
    (encPair (encList (encPair enc encBool)) (encAnnotation enc))).computableInPolyTime
  have hdrop := (ComputableTidilyInPolyTime.dropUnary
    (encA := encList (encPair enc encBool))
    (encL := encList (encList (encPair enc encBool)))).computableInPolyTime
  have hindex := unary_add'
    (snd (encPair (encCertificate enc) (encAnnotatedCertificate enc))
      (encPair (encPair (encList (encPair enc encBool)) (encAnnotation enc)) encUnary)).snd'
    (const 1)
  have herase := (computableInPolyTime_erase enc).comp hq.snd'
  unfold check
  exact allWithEncoding
    (Certificate.checkAnnotation_polyTime.comp
      (((fst _ _).fst'.prod
        ((hdrop.comp ((herase.comp (fst _ _)).prod hindex)).prod (snd _ _).fst'.fst')).prod
          (snd _ _).fst'.snd')) id' (hzip.comp hq.snd')

end AnnotatedCertificate

namespace Certificate

/-- Verifying a bare clause-line certificate is polynomial-time by annotation and checking. -/
@[fun_prop]
theorem computableInPolyTime_check (enc : V ↪ List Bool) :
    ComputableInPolyTime (fun p : CNF V × Certificate V => check p.1 p.2)
      (encPair (encCertificate enc) (encCertificate enc)) encBool :=
  (AnnotatedCertificate.computableInPolyTime_check enc).comp
    ((fst _ _).prod (computableInPolyTime_annotate enc))

/-- Checking bare refutations additionally checks for an empty raw clause in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_checkRefutation (enc : V ↪ List Bool) :
    ComputableInPolyTime (fun p : CNF V × Certificate V => checkRefutation p.1 p.2)
      (encPair (encCertificate enc) (encCertificate enc)) encBool := by
  unfold checkRefutation
  exact ComputableTidilyInPolyTime.bool_and.computableInPolyTime.comp
    ((computableInPolyTime_check enc).prod
      (anyWithInput (snd _ _)
        ((ComputableTidilyInPolyTime.listIsEmpty' (encPair enc encBool)).computableInPolyTime.comp
          (snd _ _))))

end Certificate

namespace AnnotatedCertificate

/-- Annotated refutation checking is polynomial-time on arbitrary binary references and checks
for an empty line in addition to validating the given DAG. -/
@[fun_prop]
theorem computableInPolyTime_checkRefutation (enc : V ↪ List Bool) :
    ComputableInPolyTime (fun p : CNF V × AnnotatedCertificate V => checkRefutation p.1 p.2)
      (encPair (encCertificate enc) (encAnnotatedCertificate enc)) encBool := by
  unfold checkRefutation
  exact ComputableTidilyInPolyTime.bool_and.computableInPolyTime.comp
    ((computableInPolyTime_check enc).prod
      (anyWithInput ((computableInPolyTime_erase enc).comp (snd _ _))
        ((ComputableTidilyInPolyTime.listIsEmpty' (encPair enc encBool)).computableInPolyTime.comp
          (snd _ _))))

end AnnotatedCertificate

end Cslib.Logic.PL.Resolution
