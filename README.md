# godel
This repository contains a formalization in Coq of an arithmetization of mathematics, in the style of Gödel. By mathematics we mean a theory expressed in the first-order predicate calculus, and strong enough to define the usual mathematical concepts (numbers, algebraic structures, spaces and so on). The ZFC set theory is an example of such a foundational theory. We encode formulas and proofs as natural numbers: for example if `P` is a closed proposition, the arithmetization transforms `P` into a natural number, and the question of proving `P` becomes the search of a natural number `n` such as `IsProof(P,n) = true`, where `IsProof : nat -> nat -> bool` is a total recursive function that computes whether `n` encodes of proof of `P`. Countably infinite signatures are allowed (the primitive operation and relation symbols).

The theoretical background can be found at <https://encyclopediaofmath.org/wiki/Arithmetization>.

To put more emphasis on natural numbers, `nat` is the only datatype used. Instead of algebraic datatypes representing formulas, the syntactic functions are defined directly on `nat`. These functions include checks that formulas are well-formed, substitutions of terms for free variables, checks of variable captures and checks of proofs. They are computable Coq functions, and are proven representable by &Sigma;<sub>1</sub> arithmetical formulas. This supports arithmetic as the meta-theory to do all mathematics, as stated precisely in the lemma `ArithmetizeProof`. However the Gödel numbers are so big that the computations do not terminate in practical time, and often stack overflow.

`IsProof` only assumes constructive logic by default. The excluded middle axiom schema can be added via `IsProof`'s `IsAxiom` parameter. This is done for example in the file PeanoAxioms.v, to pass from Heyting arithmetic to Peano arithmetic.

Gödel's first incompleteness theorem is proved in file IamNotProvable.v.

We also provide a model of `IsProof` together with the Heyting arithmetic axioms, to show that `IsProof` is consistent (assuming that Coq is consistent). If one wants to focus on the computational content of `IsProof`, we provide an extraction command for convenience in file ExtractProof.v. It makes around 1400 lines of OCaml, which can be read in a reasonable amount of time.

# Build instructions
This repository uses a plain `makefile`, its build command is `make`. It builds against Coq's current master branch.
