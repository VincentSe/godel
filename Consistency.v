(** We first define IsProvedAsLprop IsAxiom, an arithmetic proposition that asserts
    the provability from IsAxiom. This yields lemma ArithmetizeProof, which
    shows that mathematics can be internalized in arithmetic.

    We then define IsConsistentAsLprop IsAxiom, an arithmetic proposition
    that asserts the consistency of IsAxiom. It is a Pi_1 formula, so it
    slightly overstates the consistency of IsAxiom. It forbids inconsistency
    proofs encoded by non-standard numbers, but that is not in the intuitive
    meaning of consistency. Therefore some consistent IsAxiom prove
    ~IsConsistentAsLprop IsAxiom. Also, Gödel's second incompleteness theorem
    shows that a consistent IsAxiom never proves IsConsistentAsLprop IsAxiom. *)

Require Import PeanoNat.
Require Import Formulas.
Require Import Substitutions.
Require Import PeanoAxioms.
Require Import Proofs.
Require Import HeytingModel.
Require Import ProofTactics.
Require Import HeytingRepresentation.
Require Import BetaRepr.
Require Import EnumSeqNat_repr.


(* Arithmetic formula with only one free variable X0,
   representing the provability from IsAxiom.
   IsProvedAsLprop(X0) := exists X1, IsProofRepresentation(X0,X1,1).
   We keep variable X0 free, instead of substituting a PAnat prop
   to make a closed formula, so that it can be composed in IsProvedArith. *)
Definition IsProvedAsLprop (IsAxiom : nat -> bool) : nat
  := Subst (PAnat 1) 2 (Lexists 1 (IsProofRepresented IsAxiom)).

Lemma IsProvedAsLpropIsLproposition : forall IsAxiom,
    IsLproposition (IsProvedAsLprop IsAxiom) = true.
Proof.
  intros IsAxiom.
  unfold IsProvedAsLprop.
  apply SubstIsLproposition.
  rewrite IsLproposition_exists.
  apply fr_propprop.
  apply IsLterm_PAnat.
Qed.

Lemma IsProvedAsLpropVars : forall IsAxiom v,
    0 < v -> VarOccursFreeInFormula v (IsProvedAsLprop IsAxiom) = false.
Proof.
  intros. unfold IsProvedAsLprop.
  destruct v. exfalso; inversion H. destruct v. 2: destruct v.
  - rewrite VarOccursFreeInFormula_SubstDiff.
    rewrite VarOccursFreeInFormula_exists. reflexivity.
    rewrite IsLproposition_exists.
    apply fr_propprop. discriminate.
    apply PAnat_closed.
  - apply VarOccursFreeInFormula_SubstIdem.
    rewrite IsLproposition_exists.
    apply fr_propprop.
    apply PAnat_closed.
  - rewrite VarOccursFreeInFormula_SubstDiff.
    rewrite VarOccursFreeInFormula_exists.
    apply fr_vars. do 3 apply le_n_S.
    apply le_0_n.
    rewrite IsLproposition_exists.
    apply fr_propprop.
    discriminate.
    apply PAnat_closed.
Qed.

(* This is the internalization of mathematics inside arithmetic :
   not only are the formulas numbers, but also is axioms can be replaced
   by arithmetic axioms. *)
Lemma ArithmetizeProof : forall (IsAxiom : nat -> bool) (f : nat),
    IsProved IsAxiom f
    <-> IsProved IsWeakHeytingAxiom
               (Subst (PAnat f) 0 (IsProvedAsLprop IsAxiom)).
Proof.
  intros IsAxiom f. split.
  - intros [pr prf].
    unfold IsProvedAsLprop.
    rewrite Subst_exists, Subst_exists.
    change (IsProved IsWeakHeytingAxiom
    (Lexists 1
       (Subst (PAnat f) 0 (Subst (PAnat 1) 2 (IsProofRepresented IsAxiom))))).
    apply (LexistsIntro IsWeakHeytingAxiom _ 1 (PAnat pr)).
    apply IsLterm_PAnat.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply fr_propprop.
    apply (IsLterm_PAnat 1).
    apply IsLterm_PAnat.
    apply IsFreeForSubst_PAnat.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply fr_propprop.
    apply (IsLterm_PAnat 1).
    apply IsLterm_PAnat.
    pose proof (IsProofRepresented_alt IsAxiom f pr true) as [rep _].
    specialize (rep prf).
    rewrite (SubstSubstDiffCommutes _ 0 2).
    rewrite (SubstSubstDiffCommutes _ 1 2). exact rep.
    discriminate.
    apply PAnat_closed.
    apply PAnat_closed.
    discriminate.
    apply PAnat_closed.
    apply PAnat_closed.
  - intro proofF.
    apply HAstandardModel_correction in proofF. 2: exact HAaxiomsSatisfied.
    specialize (proofF (fun _ => 0)).
    unfold IsProvedAsLprop in proofF.
    rewrite Subst_exists, Subst_exists in proofF.
    change (HAstandardModel
             (Lexists 1
                (Subst (PAnat f) 0
                   (Subst (PAnat 1) 2 (IsProofRepresented IsAxiom))))
             (fun _ : nat => 0)) in proofF.
    rewrite HAstandardModel_exists in proofF.
    destruct proofF as [proofF H].
    exists proofF.
    rewrite HAstandardModel_Subst, HAstandardModel_Subst in H.
    rewrite HAstandardModelTerm_PAnat, HAstandardModelTerm_PAnat in H.
    destruct (IsProof IsAxiom f proofF) eqn:des. reflexivity.
    pose proof (IsProofRepresented_sat IsAxiom f proofF true (fun _ => 0)) as rep.
    rewrite des in rep. destruct rep as [_ rep]. apply rep. clear rep.
    rewrite HAstandardModel_Subst, HAstandardModel_Subst, HAstandardModel_Subst,
    HAstandardModelTerm_PAnat, HAstandardModelTerm_PAnat,
    HAstandardModelTerm_PAnat.
    rewrite (HAstandardModel_ext
               _ _ (setValue 2 1 (setValue 0 f (setValue 1 proofF (fun _ : nat => 0))))).
    exact H.
    intro n; destruct n; [reflexivity| destruct n; reflexivity].
    apply IsFreeForSubst_PAnat.
    apply fr_propprop.
    apply IsFreeForSubst_PAnat.
    apply SubstIsLproposition.
    apply fr_propprop.
    apply IsLterm_PAnat.
    apply IsFreeForSubst_PAnat.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply fr_propprop.
    apply IsLterm_PAnat.
    apply IsLterm_PAnat.
    apply IsFreeForSubst_PAnat.
    apply fr_propprop.
    apply IsFreeForSubst_PAnat.
    apply SubstIsLproposition.
    apply fr_propprop.
    apply IsLterm_PAnat.
Qed.

(* This is the semantic version of the previous lemma.
   Satisfaction in the standard model of arithmetic is equivalent to
   provability from IsWeakHeytingAxiom for Sigma_1 formulas. *)
Lemma IsProvedAsLprop_sat : forall (IsAxiom : nat -> bool) (f : nat) (varValues : nat -> nat),
    IsProved IsAxiom f
    <-> HAstandardModel (Subst (PAnat f) 0 (IsProvedAsLprop IsAxiom)) varValues.
Proof.
  intros IsAxiom f.
  assert (IsLproposition (Lexists 1 (IsProofRepresented IsAxiom)) = true)
    as exprop.
  { rewrite IsLproposition_exists. apply fr_propprop. }
  split.
  - intros proofF.
    apply ArithmetizeProof in proofF.
    apply HAstandardModel_correction in proofF.
    apply proofF. exact HAaxiomsSatisfied.
  - intros fprovable.
    unfold IsProvedAsLprop in fprovable.
    rewrite HAstandardModel_Subst, HAstandardModel_Subst, HAstandardModel_exists
      in fprovable.
    rewrite HAstandardModelTerm_PAnat, HAstandardModelTerm_PAnat in fprovable.
    destruct fprovable as [proofF fprovable].
    exists proofF.
    destruct (IsProof IsAxiom f proofF) eqn:des. reflexivity.
    pose proof (IsProofRepresented_sat IsAxiom f proofF true varValues) as rep.
    rewrite des in rep. destruct rep as [_ rep]. apply rep. clear rep.
    rewrite HAstandardModel_Subst, HAstandardModel_Subst, HAstandardModel_Subst,
    HAstandardModelTerm_PAnat, HAstandardModelTerm_PAnat, HAstandardModelTerm_PAnat.
    rewrite (HAstandardModel_ext
               _ _ (setValue 1 proofF (setValue 2 1 (setValue 0 f varValues)))).
    exact fprovable.
    intro n; destruct n; reflexivity.
    apply IsFreeForSubst_PAnat.
    apply fr_propprop.
    apply IsFreeForSubst_PAnat.
    apply SubstIsLproposition.
    apply fr_propprop.
    apply IsLterm_PAnat.
    apply IsFreeForSubst_PAnat.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply fr_propprop.
    apply IsLterm_PAnat.
    apply IsLterm_PAnat.
    apply IsFreeForSubst_PAnat.
    exact exprop.
    apply IsFreeForSubst_PAnat.
    apply SubstIsLproposition.
    exact exprop.
    apply IsLterm_PAnat.
Qed.

(* Composition of IsProvedAsLprop with a proposition InterpArith that lifts
   arithmetic formulas into the language of IsAxiom. *)
Definition IsProvedArith (IsAxiom : nat -> bool) (InterpArithLprop : nat) : nat
  := ComposeRepr (IsProvedAsLprop IsAxiom) 0 InterpArithLprop 1.

Lemma IsProvedArithIsLprop : forall IsAxiom InterpArithLprop,
    IsLproposition InterpArithLprop = true
    -> IsLproposition (IsProvedArith IsAxiom InterpArithLprop) = true.
Proof.
  intros. apply ComposeReprLprop.
  apply IsProvedAsLpropIsLproposition. exact H.
Qed.

Lemma IsProvedArithVars : forall IsAxiom InterpArithLprop,
    IsLproposition InterpArithLprop = true
    -> (forall v, 2 <= v -> VarOccursFreeInFormula v InterpArithLprop = false)
    -> (forall v, 1 <= v -> VarOccursFreeInFormula v (IsProvedArith IsAxiom InterpArithLprop)
                    = false).
Proof.
  intros.
  unfold IsProvedArith; rewrite ComposeReprVars.
  destruct v. inversion H1. simpl. clear H1.
  rewrite IsProvedAsLpropVars. simpl.
  destruct v. simpl. rewrite Bool.andb_false_r. reflexivity.
  simpl. rewrite H0. reflexivity.
  apply le_n_S, le_n_S, le_0_n.
  apply le_n_S, le_0_n.
  apply IsProvedAsLpropIsLproposition. exact H.
Qed.

Lemma IsProvedArith_sat : forall (IsAxiom : nat -> bool)
                            (InterpArithLprop : nat) (InterpArith : nat -> nat)
                            (prop : nat) (varValues : nat -> nat),
    IsLproposition InterpArithLprop = true ->
    FormulaRepresents 1 InterpArith InterpArithLprop ->
    (IsProved IsAxiom (InterpArith prop)
     <-> HAstandardModel (Subst (PAnat prop) 0 (IsProvedArith IsAxiom InterpArithLprop))
                       varValues).
Proof.
  intros.
  pose (Nat.max (MaxVar (IsProvedAsLprop IsAxiom))
                (MaxVar InterpArithLprop)) as m.
  split.
  - intro fproof.
    apply (ComposeRepr_sat
             _ _ _ _ _ (IsProvedAsLpropIsLproposition IsAxiom) H H0).
    apply ArithmetizeProof in fproof.
    apply (HAstandardModel_correction IsWeakHeytingAxiom _ HAaxiomsSatisfied)
      in fproof.
    apply fproof.
  - intro fproof.
    unfold IsProvedArith in fproof.
    apply (ComposeRepr_sat
             _ _ _ _ _ (IsProvedAsLpropIsLproposition IsAxiom) H H0) in fproof.
    apply IsProvedAsLprop_sat in fproof. exact fproof.
Qed.

Definition IsConsistentAsLprop (IsAxiom : nat -> bool) : nat :=
  Lnot (Subst (PAnat (Lnot (Leq (Lvar 0) (Lvar 0)))) 0 (IsProvedAsLprop IsAxiom)).

Lemma IsConsistentAsLpropIsLproposition : forall IsAxiom,
    IsLproposition (IsConsistentAsLprop IsAxiom) = true.
Proof.
  intros IsAxiom.
  unfold IsConsistentAsLprop.
  rewrite IsLproposition_not.
  apply SubstIsLproposition.
  apply IsProvedAsLpropIsLproposition.
  apply IsLterm_PAnat.
Qed.

Lemma IsConsistentAsLpropClosed : forall IsAxiom v,
    VarOccursFreeInFormula v (IsConsistentAsLprop IsAxiom) = false.
Proof.
  intros. unfold IsConsistentAsLprop.
  rewrite VarOccursFreeInFormula_not.
  destruct v.
  apply VarOccursFreeInFormula_SubstIdem.
  apply IsProvedAsLpropIsLproposition.
  apply PAnat_closed.
  rewrite VarOccursFreeInFormula_SubstDiff.
  apply IsProvedAsLpropVars. apply le_n_S, le_0_n.
  apply IsProvedAsLpropIsLproposition.
  discriminate.
  apply PAnat_closed.
Qed.

(* As a Pi_1 formula, this does not extend to IsProved IsWeakHeytingAxiom,
   i.e. satisfaction in all models of arithmetic. *)
Lemma IsConsistentAsLprop_sat : forall (IsAxiom : nat -> bool) (varValues : nat -> nat),
    IsConsistent IsAxiom
    <-> HAstandardModel (IsConsistentAsLprop IsAxiom) varValues.
Proof.
  intros IsAxiom varValues. split.
  - intros IsAxiomConsistent.
    unfold IsConsistent, IsInconsistent in IsAxiomConsistent.
    unfold IsConsistentAsLprop.
    rewrite HAstandardModel_not. intro abs.
    apply IsProvedAsLprop_sat in abs. contradiction.
  - intros IsAxiomConsistent abs.
    unfold IsInconsistent in abs.
    unfold IsConsistentAsLprop in IsAxiomConsistent.
    rewrite HAstandardModel_not in IsAxiomConsistent.
    contradict IsAxiomConsistent.
    apply IsProvedAsLprop_sat. exact abs.
Qed.

Global Opaque IsProvedAsLprop.
