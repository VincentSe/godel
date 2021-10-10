(** Extraction of IsProof as an OCaml program, in file proof.ml.
    This shows in details how to compute IsProof. Actually we could use a much
    simpler programming language than OCaml, since IsProof is primitive recursive. *)

Require Extraction.
Require Import Proofs.
Require Import PeanoAxioms.

Definition IsProofWeakPeano := IsProof IsWeakPeanoAxiom.

Extraction "proof" IsProofWeakPeano.
