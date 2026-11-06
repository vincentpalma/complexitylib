# Propositional models and resolution proof complexity

Complexitylib represents propositional syntax as concrete finite data and distinguishes satisfiability, derivability and resource-bounded proof objects. This supports reductions, model counting and lower bounds without identifying a proof's length with the time needed to find it. [complexitylib][complexitylib]

## CNF, CSP and quantified formulas

[CNF](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/CNF.lean#L67) is a list of clauses, each a list of signed variables. Ordering and repeated occurrences are retained. Several useful sizes coexist: clause count, literal-occurrence count, distinct-variable support, maximum clause width and serialized bit length. In a fixed-width SAT theorem the stated width convention must be checked; in resolution, width is explicitly the number of distinct literals.

The [ClauseSet](../../Complexity/Logics/Propositional/ClauseSet/Basic.lean) representation instead uses finite sets of finite sets of literals, so order and repetitions disappear. Its occurrence measure counts clauses mentioning a variable. List/set conversions preserve satisfying assignments but need separate size/occurrence lemmas. This is the mathematical representation used by sparsification and Resolution. `FiniteClause V` names a finite set of literals; list-based CNF remains the syntax for encodings and algorithms.

Support-based CNF model counting counts assignments to variables that occur. Declared-universe counting instead fixes a larger variable set and can include free choices for unused variables. The library supplies relabeling and exact gadget-counting bridges, so a reduction claiming preservation of counts must specify which convention it preserves. This distinction is particularly relevant to dense relabeling and the [native fixed-width counting endpoint](../machines-and-classes/native-counting.md).

[Constraint](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/CSP.lean#L69) has a relation alphabet and constraints consisting of a relation label plus a variable list. Semantics evaluates the label on the corresponding list of domain values. Arity is not enforced by the relation's type; a fixed-arity interpretation is an additional condition. Boolean/CNF translations and partition-function clients instantiate this generic semantic interface.

[QBF](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/QBF.lean#L76) uses named-variable Boolean quantifiers. Evaluating an existential or universal binder updates the assignment with both possible values and ORs or ANDs the results. Arithmetization and native/interactive-proof completeness clients live in their corresponding sections. This formula syntax does not by itself assert a resource bound for evaluation.

## The calculus, proof objects and certificates

Resolution uses finite sets of literals. For a pivot `v`, the resolvent is `C.erase (v, true) ∪ D.erase (v, false)`, requiring the positive pivot in `C` and the negative pivot in `D`. Union eliminates duplicates by construction. The calculus has no weakening rule. Soundness and refutation completeness relate derivability of the empty finite clause to unsatisfiability.

| Representation | What it supplies | Cost |
|---|---|---|
| [ClauseSet.Derives](../../Complexity/Logics/Propositional/Resolution.lean) | Derivability from finite-set input clauses by pivot resolution | No explicit proof size. |
| [ClauseSet.IsProof](../../Complexity/Logics/Propositional/Resolution/Proof.lean) | The legality of a sequence of finite clauses, listed last to first; each new line uses input clauses or lines in its tail | Number of lines, counting repeated lines separately; maximum finite-cardinal width. |
| [Resolution.DAG](../../Complexity/Logics/Propositional/Resolution/DAG.lean) | Finite clauses with explicit input justifications or two earlier-premise indices and a pivot | Exactly the same line sequence, line count and widths as its annotation erasure. |
| [ClauseSet.Derivation](../../Complexity/Logics/Propositional/Resolution/TreeLike.lean) | A tree with input leaves and binary resolution nodes | Tree-node count; canonical `toLines` has exactly that many lines and preserves maximum node width. |

Start from a list formula `φ : CNF V` by applying `φ.toClauseSet`. Satisfaction and variable support are preserved. Clause order and repeated input clauses do not affect the mathematical calculus. Within a proof, however, each line remains a distinct position: reusing a previous line represents sharing, while writing it twice counts two lines.

Computational certificates store lists of literals. Their mathematical interpretation maps each line through `List.toFinset`, preserving the number of lines and measuring width by the cardinality of each represented clause. Both axiom lookup and resolvent lookup compare finite clauses extensionally, so permutations and repeated literals cannot change proof validity. Encoded length and verification time still charge the actual stored literals and variable encodings. A line-count bound alone is not a bit-runtime bound. [The certificate layer](../../Complexity/Logics/Propositional/Resolution/Certificate.lean) proves the finite-set interpretation and exact line/width correspondence; [its polynomial-time module](../../Complexity/Logics/Propositional/Resolution/Certificate/PolyTime.lean) states the explicit variable, literal and binary premise-index encodings.

Erasing annotations forgets the chosen edges and pivots. Reannotation preserves valid lines and their widths, but may select another legal graph; this conversion supplies no graph-identity or clause-space guarantee. Validation of an annotated certificate checks its own supplied edges and pivots. A refutation additionally requires an empty line; the empty proof alone is not a refutation.

[CNF.Restriction](../../Complexity/Logics/Propositional/CNF/Restriction.lean) retains occurrence-preserving restriction of list syntax for algorithms. [Resolution.Restrict](../../Complexity/Logics/Propositional/Resolution/Restrict.lean) proves that interpreting restricted syntax gives the mathematical restriction. Restricting a proof never increases line count or finite-cardinal width. Lifting a restricted proof preserves its line count exactly and adds at most one literal per line.

A tree-like derivation yields a decision tree finding an input clause falsified by the assignment. Conversely, a suitable clause-search decision tree yields a refutation with at most `2 leaves - 1` nodes. The checked sharing example has seven tree nodes and six DAG lines at the same width two. Unfolding shared premises can enlarge a proof, so DAG line count and tree-node count are separate measures. Space-sensitive configurations require an explicit sequence of live-clause configurations; line count does not supply a clause-space bound.

Checked clients, including a shared nonpivot literal and input repetitions, are in [the Resolution tests](../../ComplexityTests/ProofComplexity/Resolution.lean) and [the selected abstract tests](../../ComplexityTests/Abstracts/ResolutionTests.lean).

## Major lower bounds and interpolation

[The pigeonhole development](../../Complexity/Logics/Propositional/Resolution/Pigeonhole.lean) formalizes Haken's exponential lower bound for `PHP^(n+1)_n`, using a simplified Beame–Pitassi-style argument. Its explicit finite endpoint gives at least `2^floor(n/24)` proof lines. Source documentation explains the critical-assignment measure and greedy restriction sequence. The result also lower-bounds tree-like resolution through the line/tree bridge.

[The Ben-Sasson–Wigderson tradeoff](../../Complexity/Logics/Propositional/Resolution/SizeWidth.lean) says that a clause set of initial width k on N variables with an s-line refutation has a refutation of width at most `k + 2 sqrt(2 N log s) + 2`. The contrapositive form yields an exponential line lower bound from a width lower bound. These constants and the logarithm/real square-root convention are explicit in the theorem.

[The Tseitin-expander result](../../Complexity/Logics/Propositional/Resolution/TseitinExpander.lean) combines a graph-expansion width lower bound with that tradeoff. It gives a family of linear-variable, constant-width unsatisfiable CNFs requiring exponentially many proof lines. The expansion witnesses are obtained nonconstructively from counting, and the source explicitly says so: existence of a hard family is proved, while an efficient explicit expander/formula generator is not supplied by that endpoint.

Interpolation modules extract circuits separating the two sides of a refuted conjunction. Monotone extraction supports clique/coloring lower-bound applications, and a separate polynomial-time file addresses encoded extraction. The distinction between semantic existence of an interpolant and a native efficient extraction algorithm follows the same design pattern as circuits and finite-model logic. See [interpolation](../../Complexity/Logics/Propositional/Resolution/Interpolation.lean), [monotone extraction](../../Complexity/Logics/Propositional/Resolution/Interpolation/MonotoneExtraction.lean) and [native extraction](../../Complexity/Logics/Propositional/Resolution/Interpolation/PolyTime.lean).

## Known Limitations

This section inventories resolution and its syntax clients. It does not reclassify PCPs or interactive proofs as resolution proof systems; their verifier and protocol models have separate owners. Proof size counts mathematical lines. Certificate bit length, verification time and clause space require their separately stated representation and resource bounds.

[complexitylib]: ../sources.md#complexitylib
