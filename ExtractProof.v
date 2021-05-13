(** Extraction of IsProof as an OCaml program, in file proof.ml. *)

Require Extraction.
Require Import Proofs.
Require Import PeanoAxioms.

Definition IsProofWeakPeano := IsProof IsWeakPeanoAxiom.

Extraction "proof" IsProofWeakPeano.
