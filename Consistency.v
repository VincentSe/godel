(** We first define IsProvedAsLprop IsAxiom, an arithmetic proposition that asserts
    the provability from IsAxiom. This yields lemma ArithmetizeProof, which
    shows that mathematics can be internalized in arithmetic.

    We then define IsConsistentAsLprop IsAxiom, an arithmetic proposition
    that asserts the consistency of IsAxiom. It is a Pi_1 formula, so it
    slightly overstates the consistency of IsAxiom. It forbids inconsistency
    proofs encoded by non-standard numbers, and that goes beyond the intuitive
    meaning of consistency. Therefore some consistent IsAxiom prove
    ~IsConsistentAsLprop IsAxiom. Also, Gödel's second incompleteness theorem
    shows that a consistent IsAxiom never proves IsConsistentAsLprop IsAxiom. *)

Require Import PeanoNat.
Require Import EnumSeqNat.
Require Import Formulas.
Require Import Substitutions.
Require Import IsFreeForSubst.
Require Import PeanoAxioms.
Require Import Proofs.
Require Import HeytingModel.
Require Import ProofTactics.
Require Import HeytingRepresentation.
Require Import BoolRepresented.
Require Import BetaRepr.
Require Import EnumSeqNat_repr.
Require Import IsProof_repr.


(* Arithmetic formula with only one free variable X0,
   representing the provability from IsAxiom.
   IsProvedAsLprop(X0) := exists X1, IsProofRepresentation(X0,X1,1).
   We keep variable X0 free, instead of substituting a PAnat prop
   to make a closed formula, so that it can be composed in IsProvedArith. *)
Definition IsProvedAsLprop (IsAxiom : nat -> bool) (IsAxiomRep : FunctionRepresentedBool 1 IsAxiom) : nat
  := Subst (PAnat 1) 2 (Lexists 1 (IsProofRepresented IsAxiom IsAxiomRep)).

Lemma IsProvedAsLpropIsLproposition : forall IsAxiom IsAxiomRep,
    IsLproposition (IsProvedAsLprop IsAxiom IsAxiomRep) = true.
Proof.
  intros IsAxiom IsAxiomRep.
  unfold IsProvedAsLprop.
  apply SubstIsLproposition.
  rewrite IsLproposition_exists.
  apply fr_propprop.
  apply IsLterm_PAnat.
Qed.

Lemma IsProvedAsLpropVars : forall IsAxiom IsAxiomRep v,
    0 < v -> VarOccursFreeInFormula v (IsProvedAsLprop IsAxiom IsAxiomRep) = false.
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
Lemma ArithmetizeProof : forall (IsAxiom : nat -> bool) IsAxiomRep (f : nat),
    IsProved IsAxiom f
    <-> IsProved IsWeakHeytingAxiom
               (Subst (PAnat f) 0 (IsProvedAsLprop IsAxiom IsAxiomRep)).
Proof.
  intros IsAxiom IsAxiomRep f. split.
  - intros [pr prf].
    unfold IsProvedAsLprop.
    rewrite Subst_exists, Subst_exists.
    change (IsProved IsWeakHeytingAxiom
    (Lexists 1
       (Subst (PAnat f) 0 (Subst (PAnat 1) 2 (IsProofRepresented IsAxiom IsAxiomRep))))).
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
                   (Subst (PAnat 1) 2 (IsProofRepresented IsAxiom IsAxiomRep))))
             (fun _ : nat => 0)) in proofF.
    rewrite HAstandardModel_exists in proofF.
    destruct proofF as [proofF H].
    exists proofF.
    rewrite HAstandardModel_Subst, HAstandardModel_Subst in H.
    rewrite HAstandardModelTerm_PAnat, HAstandardModelTerm_PAnat in H.
    destruct (IsProof IsAxiom f proofF) eqn:des. reflexivity.
    pose proof (IsProofRepresented_sat IsAxiom f proofF true (fun _ => 0) IsAxiomRep)
      as rep.
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
Lemma IsProvedAsLprop_sat
  : forall (IsAxiom : nat -> bool) IsAxiomRep (f : nat) (varValues : nat -> nat),
    IsProved IsAxiom f
    <-> HAstandardModel (Subst (PAnat f) 0 (IsProvedAsLprop IsAxiom IsAxiomRep)) varValues.
Proof.
  intros IsAxiom IsAxiomRep f.
  assert (IsLproposition (Lexists 1 (IsProofRepresented IsAxiom IsAxiomRep)) = true)
    as exprop.
  { rewrite IsLproposition_exists. apply fr_propprop. }
  split.
  - intros proofF.
    apply (ArithmetizeProof IsAxiom IsAxiomRep) in proofF.
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
    pose proof (IsProofRepresented_sat IsAxiom f proofF true varValues IsAxiomRep)
      as rep.
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

(* Compose arithmetic predicate A with function f : nat -> nat,
   represented by proposition fProp, which yields another arithmetic predicate. *)
Definition ComposePropFunc (A fProp : nat) : nat :=
  let m := S (Nat.max (MaxVar A) (MaxVar fProp)) in
  Lexists m (Land (Subst (Lvar m) 1 fProp)
                  (Subst (Lvar m) 0 A)).

Lemma ComposePropFuncIsProp : forall prop B,
    IsLproposition prop = true
    -> IsLproposition B = true
    -> IsLproposition (ComposePropFunc prop B) = true.
Proof.
  intros. unfold ComposePropFunc.
  rewrite IsLproposition_exists.
  rewrite IsLproposition_and.
  rewrite SubstIsLproposition.
  apply SubstIsLproposition.
  exact H. apply IsLterm_var.
  exact H0. apply IsLterm_var.
Qed.

Lemma ComposePropFuncVars : forall prop B v,
    IsLproposition prop = true
    -> IsLproposition B = true
    -> (forall k, 1 <= k -> VarOccursFreeInFormula k prop = false)
    -> (forall k, 2 <= k -> VarOccursFreeInFormula k B = false)
    -> 0 < v
    -> VarOccursFreeInFormula v (ComposePropFunc prop B) = false.
Proof.
  intros. unfold ComposePropFunc.
  rewrite VarOccursFreeInFormula_exists.
  destruct (v =? S (Nat.max (MaxVar prop) (MaxVar B))) eqn:des.
  reflexivity. simpl.
  rewrite VarOccursFreeInFormula_and.
  apply Bool.orb_false_intro.
  destruct (Nat.eq_dec v 1).
  subst v.
  apply VarOccursFreeInFormula_SubstIdem. exact H0.
  rewrite VarOccursInTerm_var. exact des.
  rewrite VarOccursFreeInFormula_SubstDiff. 
  apply H2. destruct v.
  exfalso. inversion H3. destruct v.
  exfalso. apply n. reflexivity.
  apply le_n_S, le_n_S, le_0_n. exact H0. exact n.
  rewrite VarOccursInTerm_var. exact des.
  rewrite VarOccursFreeInFormula_SubstDiff. 
  apply H1, H3. exact H.
  intro abs. rewrite abs in H3. inversion H3.
  rewrite VarOccursInTerm_var. exact des.
Qed.

(* Composition of IsProvedAsLprop with a proposition InterpArith that lifts
   arithmetic formulas into the language of IsAxiom.
   IsProvedArith is intended as a predicate with Lvar 0 its only free variable. *)
Definition IsProvedArith (IsAxiom : nat -> bool) IsAxiomRep (InterpArithLprop : nat) : nat
  := ComposePropFunc (IsProvedAsLprop IsAxiom IsAxiomRep) InterpArithLprop.

Lemma IsProvedArithIsLprop : forall IsAxiom IsAxiomRep InterpArithLprop,
    IsLproposition InterpArithLprop = true
    -> IsLproposition (IsProvedArith IsAxiom IsAxiomRep InterpArithLprop) = true.
Proof.
  intros. apply ComposePropFuncIsProp.
  apply IsProvedAsLpropIsLproposition. 
  exact H.
Qed.

Lemma IsProvedArithVars : forall IsAxiom IsAxiomRep InterpArithLprop,
    IsLproposition InterpArithLprop = true
    (* InterpArithLprop represents a function nat -> nat *)
    -> (forall v, 2 <= v -> VarOccursFreeInFormula v InterpArithLprop = false)
    -> (forall v, 1 <= v -> VarOccursFreeInFormula v (IsProvedArith IsAxiom IsAxiomRep InterpArithLprop)
                    = false).
Proof.
  intros. 
  apply ComposePropFuncVars.
  apply IsProvedAsLpropIsLproposition.
  exact H.
  intros. apply IsProvedAsLpropVars, H2.
  intros. apply H0, H2. exact H1.
Qed.

Lemma ExistsUnique : forall (P : nat -> Prop) (k : nat),
    (forall n, P n -> n = k)
    -> (exists n, P n) <-> P k.
Proof.
  split.
  - intros [n H0]. specialize (H n H0).
    rewrite <- H. exact H0.
  - intro H0. exists k. exact H0.
Qed.

Lemma IsProvedArith_sat : forall (IsAxiom : nat -> bool) IsAxiomRep
                            (InterpArithLprop : nat) (InterpArith : nat -> nat)
                            (prop : nat) (varValues : nat -> nat),
    IsLproposition InterpArithLprop = true ->
    FormulaRepresents 1 InterpArith InterpArithLprop ->
    (IsProved IsAxiom (InterpArith prop)
     <-> HAstandardModel (Subst (PAnat prop) 0 (IsProvedArith IsAxiom IsAxiomRep InterpArithLprop))
                       varValues).
Proof.
  intros.
  pose (Nat.max (MaxVar (IsProvedAsLprop IsAxiom IsAxiomRep))
                (MaxVar InterpArithLprop)) as m.
  rewrite (IsProvedAsLprop_sat IsAxiom IsAxiomRep _ (setValue (S m) (InterpArith prop) varValues)).
  rewrite HAstandardModel_Subst, HAstandardModelTerm_PAnat.
  2: apply IsFreeForSubst_PAnat, IsProvedAsLpropIsLproposition.
  rewrite HAstandardModel_Subst, HAstandardModelTerm_PAnat.
  2: apply IsFreeForSubst_PAnat, IsProvedArithIsLprop, H.
  unfold IsProvedArith, ComposePropFunc; fold m.
  rewrite HAstandardModel_exists.
  rewrite (ExistsUnique _ (InterpArith prop)).
  rewrite HAstandardModel_and.
  rewrite HAstandardModel_Subst, HAstandardModelTerm_var.
  rewrite HAstandardModel_Subst, HAstandardModelTerm_var.
  unfold setValue at 4; rewrite Nat.eqb_refl.
  unfold setValue at 7; rewrite Nat.eqb_refl.
  split.
  - intro fproof. split.
    + pose proof (FormulaRepresents_alt
                    1 InterpArith _ (ConsNat prop (ConsNat (InterpArith prop) NilNat))
                    H0 H (InterpArith prop))
        as H1.
      simpl in H1.
      rewrite CoordConsHeadNat in H1.
      destruct H1 as [H1 _]. specialize (H1 eq_refl).
      apply (HAstandardModel_correction IsWeakHeytingAxiom _ HAaxiomsSatisfied)
        in H1.
      specialize (H1 (setValue (S m) (InterpArith prop) varValues)).
      rewrite HAstandardModel_Subst, HAstandardModelTerm_PAnat in H1. 
      rewrite HAstandardModel_Subst, HAstandardModelTerm_PAnat in H1. 
      rewrite (HAstandardModel_ext _ _ (setValue 0 prop
            (setValue 1 (InterpArith prop)
               (setValue (S m) (InterpArith prop) varValues)))).
      exact H1.
      intro n. unfold setValue.
      destruct n. reflexivity. simpl.
      destruct n.
      destruct m; reflexivity. reflexivity.
      apply IsFreeForSubst_PAnat. exact H.
      apply IsFreeForSubst_PAnat.
      apply SubstIsLproposition. exact H.
      apply IsLterm_PAnat.
    + rewrite (HAstandardModel_ext _ _ (setValue 0 (InterpArith prop)
                (setValue (S m) (InterpArith prop) varValues))).
      exact fproof.
      intro n; destruct n; reflexivity.
  - intros [_ fproof].
    rewrite (HAstandardModel_ext _ _ (setValue 0 (InterpArith prop)
                (setValue (S m) (InterpArith prop) (setValue 0 prop varValues)))).
    exact fproof.
    intro n. unfold setValue. destruct n; reflexivity.
  - apply MaxVarFreeSubst_var.
    apply IsProvedAsLpropIsLproposition.
    apply le_n_S, Nat.le_max_l.
  - apply MaxVarFreeSubst_var.
    apply H.
    apply le_n_S, Nat.le_max_r.
  - intros n H1. rewrite HAstandardModel_and in H1.
    destruct H1 as [H1 _].
    rewrite HAstandardModel_Subst, HAstandardModelTerm_var in H1.
    unfold setValue in H1 at 2; rewrite Nat.eqb_refl in H1.
    pose proof (FormulaRepresents_sat
                    1 InterpArith _ (ConsNat prop (ConsNat (InterpArith prop) NilNat))
                    H0 H n (setValue (S m) n varValues))
      as H2.
    simpl in H2. rewrite CoordConsHeadNat in H2.
    symmetry. apply H2. clear H2.
    rewrite HAstandardModel_Subst, HAstandardModelTerm_PAnat.
    rewrite HAstandardModel_Subst, HAstandardModelTerm_PAnat.
    rewrite (HAstandardModel_ext _ _ (setValue 1 n (setValue (S m) n (setValue 0 prop varValues)))).
    exact H1.
    intro k; destruct k; reflexivity.
    apply IsFreeForSubst_PAnat, H.
    apply IsFreeForSubst_PAnat.
    apply SubstIsLproposition. exact H.
    apply IsLterm_PAnat.
    apply MaxVarFreeSubst_var.
    apply H.
    apply le_n_S, Nat.le_max_r.
Qed.

Definition IsConsistentAsLprop (IsAxiom : nat -> bool) IsAxiomRep : nat :=
  Lnot (Subst (PAnat (Lnot (Leq (Lvar 0) (Lvar 0)))) 0 (IsProvedAsLprop IsAxiom IsAxiomRep)).

Lemma IsConsistentAsLpropIsLproposition : forall IsAxiom IsAxiomRep,
    IsLproposition (IsConsistentAsLprop IsAxiom IsAxiomRep) = true.
Proof.
  intros IsAxiom IsAxiomRep.
  unfold IsConsistentAsLprop.
  rewrite IsLproposition_not.
  apply SubstIsLproposition.
  apply IsProvedAsLpropIsLproposition.
  apply IsLterm_PAnat.
Qed.

Lemma IsConsistentAsLpropClosed : forall IsAxiom IsAxiomRep v,
    VarOccursFreeInFormula v (IsConsistentAsLprop IsAxiom IsAxiomRep) = false.
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
Lemma IsConsistentAsLprop_sat
  : forall (IsAxiom : nat -> bool) IsAxiomRep (varValues : nat -> nat),
    IsConsistent IsAxiom
    <-> HAstandardModel (IsConsistentAsLprop IsAxiom IsAxiomRep) varValues.
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
