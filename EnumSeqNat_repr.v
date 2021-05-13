Require Import PeanoNat.
Require Import Arith.Compare_dec.
Require Import EnumSeqNat.
Require Import Substitutions.
Require Import IsFreeForSubst.
Require Import Formulas.
Require Import Proofs.
Require Import ProofTactics.
Require Import PeanoAxioms.
Require Import HeytingModel.
Require Import HeytingRepresentation.
Require Import BetaRepr.

(* TODO prove Nat.eqb, CoordNat and LengthNat represented in new file EnumSeqNat_repr. *)

Lemma FunctionRepresentedDropVariable : forall (u : nat -> nat),
    FunctionRepresented 1 u
    -> FunctionRepresented 2 (fun _ j : nat => u j).
Proof.
  intros u urep.
  assert (1 <= MaxVar urep)%nat as mv.
  { destruct (le_lt_dec 1 (MaxVar urep)). exact l. exfalso.
    pose proof (MaxVarDoesNotOccurFree _ (fr_propprop _ _ urep) 1 l).
    pose proof (fr_freevar _ _ urep).
    rewrite H0 in H. discriminate H. } 
  assert (forall i:nat, S i =? i = false) as succdiff.
  { intro i. apply Nat.eqb_neq. intro abs.
    apply (Nat.lt_irrefl i). rewrite <- abs at 2. apply Nat.le_refl. }
  apply (Build_FunctionRepresented
           _ _ (let m := S (S (MaxVar urep)) in
                Lexists (S m)
                (Lexists m (Land (Leq (Lvar m) (Lvar 1))
                                 (Land (Leq (Lvar (S m)) (Lvar 2))
                                       (Subst (Lvar (S m)) 1 (Subst (Lvar m) 0 urep))))))).
  - intro args. simpl. apply LforallIntro.
    rewrite CoordTailNat.
    remember (CoordNat args 0) as i.
    remember (CoordNat args 1) as j.
    clear Heqj Heqi args.
    apply LandIntro.
    + rewrite Subst_exists; simpl.
      rewrite Subst_exists; simpl.
      rewrite Subst_exists; simpl.
      rewrite Subst_exists; simpl.
      reduce_subst; simpl.
      rewrite SubstTerm_var, SubstTerm_var, SubstTerm_var, SubstTerm_var; simpl.
      rewrite (Subst_nosubst _ 0).
      rewrite (Subst_nosubst _ 1).
      assert (S (S (MaxVar urep)) =? 2 = false).
      { destruct (MaxVar urep). inversion mv. reflexivity. } 
      apply LexistsElim_impl.
      unfold Leq. rewrite VarOccursFreeInFormula_rel2.
      rewrite VarOccursInTerm_var, PAnat_closed. reflexivity. 
      apply LforallIntro.
      apply LexistsElim_impl.
      unfold Leq. rewrite VarOccursFreeInFormula_rel2.
      rewrite VarOccursInTerm_var, PAnat_closed, H. reflexivity.
      apply LforallIntro, PushHypothesis, LeqElimSubstVarPAnat.
      reduce_islproposition. rewrite IsLterm_PAnat, SubstIsLproposition.
      reflexivity. apply SubstIsLproposition. apply fr_propprop.
      apply IsLterm_var. apply IsLterm_var.
      reduce_subst. rewrite (Nat.eqb_sym 2), H, SubstTerm_PAnat.
      rewrite succdiff.
      rewrite SubstSubstDiffCommutes.
      rewrite (SubstSubstNested _ (fr_propprop _ _ urep)), SubstTerm_var, Nat.eqb_refl.
      apply PushHypothesis.
      apply (LimpliesTrans _ _ (Leq (Lvar 2) (Lvar (S (S (S (MaxVar urep))))))).
      apply LeqSym_impl. apply IsLterm_var. apply IsLterm_var.
      apply LeqElimSubstVar.
      reduce_islproposition. rewrite IsLterm_PAnat, SubstIsLproposition.
      reflexivity. apply SubstIsLproposition. apply fr_propprop.
      apply IsLterm_PAnat. apply IsLterm_var. apply IsLterm_var.
      unfold Leq.
      rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2, Bool.andb_true_r.
      apply IsFreeForSubst_nosubst.
      apply SubstIsLproposition.
      apply SubstIsLproposition. apply fr_propprop.
      apply IsLterm_PAnat. apply IsLterm_var.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply fr_vars, Nat.le_refl. apply PAnat_closed.
      rewrite VarOccursInTerm_var. reflexivity.
      rewrite Subst_implies, Subst_eq, SubstTerm_var. simpl.
      rewrite SubstTerm_PAnat, Subst_nosubst.
      pose proof (fr_rep _ _ urep (ConsNat j NilNat)).
      simpl in H0. rewrite CoordConsHeadNat in H0.
      apply (LforallElim _ _ 1 (Lvar (S (S (S (MaxVar urep)))))) in H0.
      rewrite Subst_equiv, Subst_eq, SubstTerm_var in H0. simpl in H0.
      rewrite SubstTerm_PAnat in H0.
      apply LandElim1 in H0. exact H0.
      apply IsLterm_var. unfold Leq.
      rewrite IsFreeForSubst_equiv, IsFreeForSubst_rel2, Bool.andb_true_r.
      apply MaxVarFreeSubst_var.
      apply SubstIsLproposition. apply fr_propprop. apply IsLterm_PAnat.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_PAnat. simpl.
      apply le_S, le_S, Nat.le_refl.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply fr_vars, Nat.le_refl. apply PAnat_closed. 
      rewrite VarOccursInTerm_var. reflexivity.
      apply fr_vars, le_n_S, le_n_S, le_0_n.
      apply MaxVarFreeSubst_var. apply fr_propprop.
      apply le_S, Nat.le_refl.
      discriminate. apply PAnat_closed.
      rewrite VarOccursInTerm_var, Nat.eqb_sym. apply succdiff.
      apply VarOccursFreeInFormula_SubstIdem.
      apply SubstIsLproposition. apply fr_propprop.
      apply IsLterm_var. apply VarOccursInTerm_var.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstIdem.
      apply fr_propprop. apply VarOccursInTerm_var.
      apply VarOccursInTerm_var.
    + apply LeqElimSubstVarPAnat.
      apply SubstIsLproposition.
      apply SubstIsLproposition.
      reduce_islproposition. apply SubstIsLproposition.
      apply SubstIsLproposition. apply fr_propprop.
      apply IsLterm_var. apply IsLterm_var.
      apply IsLterm_PAnat. apply IsLterm_PAnat.
      rewrite Subst_exists; simpl.
      rewrite Subst_exists; simpl.
      rewrite (Subst_exists _ 0); simpl.
      rewrite Subst_and, Subst_eq, SubstTerm_var; simpl.
      rewrite SubstTerm_var; simpl. rewrite Subst_and, Subst_eq.
      rewrite SubstTerm_var; simpl.
      rewrite SubstTerm_var; simpl.
      rewrite (Subst_nosubst _ 0).
      rewrite Subst_exists; simpl.
      rewrite Subst_exists; simpl.
      rewrite Subst_exists; simpl. destruct (MaxVar urep) as [|m] eqn:des.
      inversion mv.
      simpl. 
      reduce_subst; simpl. rewrite SubstTerm_var, SubstTerm_var; simpl.
      rewrite SubstTerm_PAnat, SubstTerm_var; simpl.
      rewrite (Subst_nosubst _ 1).
      apply (LexistsIntro _ _ _ (PAnat (u j))).
      apply IsLterm_PAnat.
      reduce_islproposition. rewrite IsLterm_PAnat, IsLterm_PAnat.
      apply SubstIsLproposition.
      apply SubstIsLproposition.
      apply SubstIsLproposition. apply fr_propprop.
      apply IsLterm_var. apply IsLterm_var. apply IsLterm_PAnat.
      apply IsFreeForSubst_PAnat.
      reduce_islproposition.
      rewrite IsLterm_PAnat. rewrite IsLterm_PAnat.
      apply SubstIsLproposition.
      apply SubstIsLproposition.
      apply SubstIsLproposition. apply fr_propprop.
      apply IsLterm_var. apply IsLterm_var. apply IsLterm_PAnat.
      assert (S (S (S m)) =? S (S (S (S m))) = false).
      { apply Nat.eqb_neq. intro abs. apply (Nat.lt_irrefl (S (S (S m)))).
        rewrite abs at 2. apply Nat.le_refl. }
      rewrite Subst_exists, H, Subst_and, Subst_eq, SubstTerm_var, H.
      rewrite SubstTerm_PAnat, Subst_and, Subst_eq, SubstTerm_var, Nat.eqb_refl.
      rewrite SubstTerm_PAnat.
      apply (LexistsIntro _ _ _ (PAnat j)).
      apply IsLterm_PAnat.
      reduce_islproposition. rewrite IsLterm_PAnat, IsLterm_PAnat.
      apply SubstIsLproposition. 
      reduce_islproposition.
      apply SubstIsLproposition. 
      apply SubstIsLproposition. 
      apply SubstIsLproposition. apply fr_propprop.
      apply IsLterm_var. apply IsLterm_var.
      apply IsLterm_PAnat. apply IsLterm_PAnat.
      apply IsFreeForSubst_PAnat.
      reduce_islproposition. rewrite IsLterm_PAnat, IsLterm_PAnat.
      apply SubstIsLproposition. 
      apply SubstIsLproposition.
      apply SubstIsLproposition.
      apply SubstIsLproposition. apply fr_propprop.
      apply IsLterm_var. apply IsLterm_var.
      apply IsLterm_PAnat. apply IsLterm_PAnat.
      rewrite Subst_and, Subst_eq, SubstTerm_var, Nat.eqb_refl.
      rewrite SubstTerm_PAnat. apply LandIntro.
      apply LeqRefl, IsLterm_PAnat.
      rewrite Subst_and. apply LandIntro.
      rewrite Subst_eq, SubstTerm_PAnat. apply LeqRefl, IsLterm_PAnat.
      rewrite (Subst_nosubst _ 2).
      assert (IsLproposition (Subst (Lvar (S (S (S m)))) 0 urep) = true).
      { apply SubstIsLproposition. apply fr_propprop. apply IsLterm_var. }
      rewrite (SubstSubstNested _ H0), SubstTerm_var, Nat.eqb_refl. clear H0.
      rewrite SubstSubstDiffCommutes.
      rewrite (SubstSubstNested _ (fr_propprop _ _ urep)), SubstTerm_var, Nat.eqb_refl.
      pose proof (FormulaRepresents_alt
                    _ _ _ (ConsNat j NilNat) (fr_rep _ _ urep) (fr_propprop _ _ urep) (u j)).
      simpl in H0. rewrite CoordConsHeadNat in H0.
      apply H0. reflexivity.
      apply fr_vars. apply le_n_S, le_n_S, le_0_n. 
      apply MaxVarFreeSubst_var.
      apply fr_propprop.
      apply le_n_S.
      rewrite des. apply le_S, Nat.le_refl.
      discriminate. apply PAnat_closed. apply PAnat_closed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply fr_vars. apply le_n_S, le_n_S, le_0_n. 
      rewrite VarOccursInTerm_var, Nat.eqb_sym. exact H.
      apply MaxVarFreeSubst_var.
      apply SubstIsLproposition. apply fr_propprop. apply IsLterm_var.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_var. apply Nat.max_lub. apply Nat.le_refl. 
      rewrite des. apply le_S, le_S, Nat.le_refl.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply fr_vars. apply Nat.le_refl. apply VarOccursInTerm_var.
      apply VarOccursInTerm_var.
      apply VarOccursFreeInFormula_SubstIdem.
      apply SubstIsLproposition. apply fr_propprop.
      apply IsLterm_var. apply VarOccursInTerm_var.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstIdem.
      apply fr_propprop. apply VarOccursInTerm_var. apply VarOccursInTerm_var.
  - simpl. reduce_islproposition.
    rewrite SubstIsLproposition. reflexivity.
    apply SubstIsLproposition. apply fr_propprop.
    apply IsLterm_var. apply IsLterm_var.
  - intros v H. simpl.
    rewrite VarOccursFreeInFormula_exists.
    destruct (v =? S (S (S (MaxVar urep)))) eqn:des2. reflexivity. simpl.
    rewrite VarOccursFreeInFormula_exists.
    destruct (v =? S (S (MaxVar urep))) eqn:des. reflexivity. simpl.
    rewrite VarOccursFreeInFormula_and. apply Bool.orb_false_intro.
    unfold Leq. rewrite VarOccursFreeInFormula_rel2.
    rewrite VarOccursInTerm_var, VarOccursInTerm_var, des. simpl.
    apply Nat.eqb_neq. intro abs. rewrite abs in H.
    apply le_S_n in H. inversion H.
    rewrite VarOccursFreeInFormula_and. apply Bool.orb_false_intro.
    unfold Leq. rewrite VarOccursFreeInFormula_rel2.
    rewrite VarOccursInTerm_var, VarOccursInTerm_var, des2. simpl.
    apply Nat.eqb_neq. intro abs. rewrite abs in H.
    exact (Nat.lt_irrefl 2 H).
    apply VarOccursFreeInFormula_SubstClosed.
    apply VarOccursFreeInFormula_SubstClosed.
    apply fr_vars. apply (Nat.le_trans _ 3).
    apply le_S, Nat.le_refl. exact H.
    rewrite VarOccursInTerm_var. exact des.
    rewrite VarOccursInTerm_var. exact des2.
Qed.

Lemma sqrt_repr : FunctionRepresented 1 Nat.sqrt.
Proof.
  apply (Build_FunctionRepresented
           1 _ (Land (PAle (PAmult (Lvar 1) (Lvar 1)) (Lvar 0))
                     (PAle (PAsucc (Lvar 0))
                           (PAmult (PAsucc (Lvar 1)) (PAsucc (Lvar 1)))))).
  - intro args. simpl.
    generalize (CoordNat args 0) as i. intro i. clear args.
    apply LforallIntro.
    rewrite Subst_and, Subst_PAle, SubstTerm_PAmult, SubstTerm_var.
    simpl. rewrite SubstTerm_var. simpl.
    rewrite Subst_PAle, SubstTerm_PAsucc.
    rewrite SubstTerm_PAmult.
    rewrite SubstTerm_var, SubstTerm_PAsucc. simpl.
    rewrite SubstTerm_var. simpl.
    apply LandIntro.
    + shelve.
    + apply LeqElimSubstVarPAnat.
      unfold PAle, PAmult, PAsucc, PAzero. reduce_islproposition.
      rewrite IsLterm_PAnat. reflexivity.
      rewrite Subst_and. apply LandIntro.
      * rewrite Subst_PAle, SubstTerm_PAmult, SubstTerm_PAnat.
        rewrite SubstTerm_var. simpl.
        shelve.  (* closed formula without quantifiers by heyting model *)
      * rewrite Subst_PAle, SubstTerm_PAsucc.
        rewrite SubstTerm_PAmult, SubstTerm_PAsucc, SubstTerm_var.
        simpl. rewrite SubstTerm_PAnat.
        shelve. (* closed formula without quantifiers by heyting model *)
  - unfold PAle, PAmult, PAsucc. reduce_islproposition. reflexivity.
  - intros v H. unfold PAle, PAmult, PAsucc.
    rewrite VarOccursFreeInFormula_and, VarOccursFreeInFormula_rel2.
    rewrite VarOccursInTerm_op2.
    rewrite VarOccursFreeInFormula_rel2, VarOccursInTerm_op1.
    rewrite VarOccursInTerm_op2, VarOccursInTerm_op1.
    rewrite VarOccursInTerm_var, VarOccursInTerm_var.
    destruct v. inversion H. simpl.
    destruct v. exfalso. exact (Nat.lt_irrefl 1 H). reflexivity.
Admitted.

Lemma biggestTriangle_repr : FunctionRepresented 1 biggestTriangle.
Proof.
  pose proof div_repr.
  unfold biggestTriangle.
Admitted.

Lemma NthTailNat_repr : FunctionRepresented 2 NthTailNat.
Proof.
  pose proof (FunctionRepresented_2_ext ).
  apply (FunctionRepresented_2_ext
           (fun init => nat_rec (fun _ => nat) init (fun n k => TailNat k))).
  - apply nat_rec_repr. apply FunctionRepresentedDropVariable.
    shelve.
  - induction k. reflexivity. simpl.
    rewrite IHk. clear IHk. revert k n. induction k.
    reflexivity. intro n. simpl. rewrite IHk. reflexivity.
Admitted.


(* Move those to new file IsProof_repr *)

Lemma IsProofRepresented : forall (IsAxiom : nat -> bool),
    FunctionRepresented 2 (fun prop proof => if IsProof IsAxiom prop proof then 1 else 0)%nat.
Admitted.

Lemma SubstSelfZeroRepresented :
  FunctionRepresented 1 (fun prop : nat => Subst (PAnat prop) 0 prop).
Admitted.

Lemma IsProofRepresented_alt : forall IsAxiom (prop prf : nat) (b : bool),
    IsProof IsAxiom prop prf = b
    <-> IsProved IsWeakHeytingAxiom
               (Subst (PAnat (if b then 1 else 0)) 2
                      (Subst (PAnat prf) 1
                             (Subst (PAnat prop) 0 (IsProofRepresented IsAxiom)))).
Proof.
  intros.
  pose proof (FormulaRepresents_alt
                2
                _ _ (ConsNat prop (ConsNat prf NilNat))
                (fr_rep _ _ (IsProofRepresented IsAxiom))
                (fr_propprop _ _ _)
                (if b then 1 else 0)) as H.
  simpl in H.
  rewrite CoordTailNat, CoordConsHeadNat, CoordConsTailNat, CoordConsHeadNat in H.
  simpl in H.
  split.
  - intros. subst b. destruct H as [H _].
    specialize (H eq_refl). exact H.
  - intro H0. destruct H as [_ H]. specialize (H H0).
    destruct (IsProof IsAxiom prop prf), b; try reflexivity; try discriminate.
Qed.

Lemma IsProofRepresented_sat : forall IsAxiom (prop prf : nat) (b : bool) varValues,
    IsProof IsAxiom prop prf = b
    <-> HAstandardModel
        (Subst (PAnat (if b then 1 else 0)) 2
               (Subst (PAnat prf) 1
                      (Subst (PAnat prop) 0 (IsProofRepresented IsAxiom)))) varValues.
Proof.
  intros.
  pose proof (FormulaRepresents_sat
                2 _ _ (ConsNat prop (ConsNat prf NilNat))
                (fr_rep _ _ (IsProofRepresented IsAxiom))
                (fr_propprop _ _ _)
                (if b then 1 else 0) varValues) as H.
  simpl in H.
  rewrite CoordConsHeadNat, CoordTailNat, CoordConsTailNat, CoordConsHeadNat in H.
  split.
  - intros. subst b. destruct H as [H _].
    specialize (H eq_refl). exact H.
  - intro H0. destruct H as [_ H]. specialize (H H0).
    destruct (IsProof IsAxiom prop prf), b; try reflexivity; try discriminate.
Qed.
