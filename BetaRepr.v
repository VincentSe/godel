(** We prove that Gödel's beta function is represented by an arithmetic formula.

    This is a work in progress, complete proofs can be found in this library
    https://github.com/coq-community/hydra-battles *)

Require Import ZArith.
Require Import ZArith.Znumtheory.
Require Import Arith.Compare_dec.
Require Import PeanoNat.
Require Import EnumSeqNat.
Require Import Formulas.
Require Import IsFreeForSubst.
Require Import Proofs.
Require Import ProofTactics.
Require Import HeytingModel.
Require Import PeanoAxioms.
Require Import Substitutions.
Require Import HeytingRepresentation.
Require Import ChineseRemainder.

Lemma NatDivDef : forall (i j k : nat),
    IsProved IsWeakHeytingAxiom
             (Limplies
                (Land (PAle (PAmult (PAnat k) (PAnat j)) (PAnat i))
                      (PAle (PAsucc (PAnat i))
                            (PAmult (PAsucc (PAnat k)) (PAnat j))))
                (Leq (PAnat k) (PAnat (i / j)))).
Proof.
  intros i j k.
  apply PushHypothesis.
  destruct (le_lt_dec (k*j) i).
  - apply DropHypothesis.
    unfold PAle, PAmult.
    rewrite IsLproposition_rel2, IsLterm_op2, IsLterm_PAnat, IsLterm_PAnat.
    apply IsLterm_PAnat.
    destruct (le_lt_dec (S i) (S k * j)).
    + apply DropHypothesis.
      unfold PAle, PAmult, PAsucc.
      rewrite IsLproposition_rel2, IsLterm_op2, IsLterm_PAnat, IsLterm_op1.
      rewrite IsLterm_op1, IsLterm_PAnat, IsLterm_PAnat. reflexivity.
      replace (i / j)%nat with k. apply LeqRefl, IsLterm_PAnat.
      apply Nat.le_antisymm.
      apply (Nat.div_le_mono (k*j) i j) in l.
      rewrite Nat.div_mul in l. exact l.
      intro abs. rewrite abs, Nat.mul_0_r in l0. inversion l0.
      intro abs. rewrite abs, Nat.mul_0_r in l0. inversion l0.
      rewrite Nat.mul_comm in l0.
      apply (Nat.div_lt_upper_bound i j (S k)) in l0.
      apply le_S_n, l0.
      intro abs. rewrite abs, Nat.mul_0_l in l0. inversion l0.
    + pose proof (PAlt_not_le _ _ l0).
      apply (LimpliesTrans _ _ (PAle (PAsucc (PAnat i)) (PAnat (S k * j)))).
      pose proof (LeqElim_rel2 IsWeakHeytingAxiom 1
                               (PAsucc (PAnat i)) (PAsucc (PAnat i))
                               (PAmult (PAsucc (PAnat k)) (PAnat j))
                               (PAnat (S k * j))).
      apply LandElim1 in H0. exact H0.
      apply LeqRefl. unfold PAsucc. rewrite IsLterm_op1. apply IsLterm_PAnat.
      exact (PAmult_normalize (S k) j).
      apply FalseElim_impl. exact H.
      rewrite IsLproposition_eq, IsLterm_PAnat, IsLterm_PAnat. reflexivity.
  - pose proof (PAlt_not_le _ _ l).
    apply (LimpliesTrans _ _ (PAle (PAnat (k * j)) (PAnat i))).
    pose proof (LeqElim_rel2 IsWeakHeytingAxiom 1
                             (PAmult (PAnat k) (PAnat j))
                             (PAnat (k * j))
                             (PAnat i) (PAnat i)).
    apply LandElim1 in H0. exact H0.
    exact (PAmult_normalize k j).
    apply LeqRefl. apply IsLterm_PAnat.
    apply FalseElim_impl. exact H.
    unfold PAle, PAsucc, PAmult.
    reduce_islproposition.
    do 4 rewrite IsLterm_PAnat. reflexivity.
Qed.

Lemma NatDivCorrect : forall (i j : nat),
  IsProved IsWeakHeytingAxiom
           (Lor (Land (Leq (PAnat (i / j)) PAzero) (Leq (PAnat j) PAzero))
                (Land (PAle (PAmult (PAnat (i / j)) (PAnat j)) (PAnat i))
                      (PAle (PAsucc (PAnat i))
                            (PAmult (PAsucc (PAnat (i / j))) (PAnat j))))).
Proof.
  intros. destruct j.
  - apply LorIntro1. 2: apply LandIntro; apply LeqRefl, IsLterm_const.
    unfold PAle.
    rewrite IsLproposition_and, IsLproposition_rel2, IsLproposition_rel2.
    simpl. unfold PAmult, PAsucc, PAzero.
    rewrite IsLterm_PAnat, IsLterm_op2, IsLterm_op2, IsLterm_op1, IsLterm_op1.
    rewrite IsLterm_PAnat, IsLterm_const. reflexivity.
  - apply LorIntro2.
    rewrite IsLproposition_and, IsLproposition_eq, IsLproposition_eq.
    unfold PAzero.
    rewrite IsLterm_PAnat, IsLterm_PAnat, IsLterm_const. reflexivity.
    apply LandIntro.
    + pose proof (LeqElim_rel2 IsWeakHeytingAxiom 1 _ _ _ _
                               (PAmult_normalize (i/S j) (S j))
                               (LeqRefl _ (PAnat i) (IsLterm_PAnat _))) as H.
      apply LandElim2 in H.
      apply (LimpliesElim _ _ _ H). clear H.
      apply PAle_normalize.
      rewrite Nat.mul_comm. apply (Nat.mul_div_le). discriminate.
    + pose proof (LeqElim_rel2 IsWeakHeytingAxiom 1
                               _ _
                               (PAmult (PAnat (S (i / S j))) (PAnat (S j)))
                               (PAnat ((S (i / S j)) * (S j)))
                               (LeqRefl _ _ (IsLterm_PAnat (S i)))).
      apply LandElim2 in H.
      2: apply PAmult_normalize.
      apply (LimpliesElim _ _ _ H). clear H.
      apply PAle_normalize.
      rewrite Nat.mul_comm.
      apply (Nat.mul_succ_div_gt i (S j)). discriminate.
Qed.

Opaque Land Limplies.
Lemma div_repr : FunctionRepresented 2 Nat.div.
Proof.
  assert (forall i j,
             IsLterm i = true ->
             IsLterm j = true ->
             IsLproposition
(Land (PAle (Lvar 2) i)
       (Lor (Land (Leq (Lvar 2) PAzero) (Leq j PAzero))
          (Land (PAle (PAmult (Lvar 2) j) i)
             (PAle (PAsucc i) (PAmult (PAsucc (Lvar 2)) j)))))
      = true) as hypprop.
  { intros. unfold PAle, PAmult, PAsucc.
    rewrite IsLproposition_and, IsLproposition_or, IsLproposition_and.
    rewrite IsLproposition_eq, IsLproposition_eq, IsLproposition_and.
    rewrite IsLproposition_rel2, IsLproposition_rel2, IsLproposition_rel2.
    rewrite IsLterm_op2, IsLterm_op2, IsLterm_op1, IsLterm_op1, H, H0.
    unfold PAzero. rewrite IsLterm_var, IsLterm_const. reflexivity. }
  (* X2 = X0 / X1 *)
  apply (Build_FunctionRepresented 2
           _ (Land (PAle (Lvar 2) (Lvar 0))
                   (Lor (Land (Leq (Lvar 2) PAzero) (Leq (Lvar 1) PAzero))
                        (Land (PAle (PAmult (Lvar 2) (Lvar 1)) (Lvar 0))
                              (PAle (PAsucc (Lvar 0))
                              (PAmult (PAsucc (Lvar 2)) (Lvar 1))))))).
  - intro args. simpl. rewrite CoordTailNat.
    remember (CoordNat args 0) as i.
    remember (CoordNat args 1) as j.
    apply LforallIntro.
    reduce_subst; simpl.
    rewrite (SubstTerm_PAzero (PAnat i) 0). do 6 rewrite Subst_PAle.
    reduce_subst; simpl.
    reduce_subst; simpl.
    rewrite SubstTerm_PAnat. do 4 rewrite SubstTerm_PAmult.
    do 4 rewrite SubstTerm_PAsucc.
    reduce_subst; simpl. rewrite SubstTerm_PAnat.
    reduce_subst; simpl.
    apply LandIntro.
    + apply PushHypothesis, LforallBounded.
      rewrite IsLproposition_implies.
      specialize (hypprop (PAnat i) (PAnat j) (IsLterm_PAnat _) (IsLterm_PAnat _)).
      rewrite IsLproposition_and in hypprop.
      apply andb_prop in hypprop. destruct hypprop.
      rewrite SubstTerm_PAzero.
      rewrite H0.
      rewrite IsLproposition_eq, IsLterm_var, IsLterm_PAnat. reflexivity.
      intros k H.
      reduce_subst; simpl.
      rewrite Subst_PAle, Subst_PAle, (SubstTerm_PAzero (PAnat j) 1), SubstTerm_PAnat.
      rewrite SubstTerm_PAmult, SubstTerm_PAsucc, SubstTerm_PAmult.
      do 3 rewrite SubstTerm_PAnat. rewrite SubstTerm_PAsucc.
      reduce_subst; simpl.
      apply LorElim. destruct j. rewrite SubstTerm_PAzero.
      apply LandElim1_impl.
      rewrite IsLproposition_eq, IsLterm_PAnat. apply IsLterm_PAnat.
      unfold PAzero. rewrite IsLproposition_eq, IsLterm_PAnat, IsLterm_const.
      reflexivity.
      apply (LimpliesTrans _ _ (Leq (PAnat (S j)) PAzero)).
      rewrite SubstTerm_PAzero.
      apply LandElim2_impl.
      rewrite IsLproposition_eq, IsLterm_PAnat. apply IsLterm_const.
      rewrite IsLproposition_eq, IsLterm_PAnat. apply IsLterm_const.
      apply FalseElim_impl.
      pose proof IsProvedAx1 as H0.
      apply (LforallElim _ _ _ (PAnat j)) in H0.
      rewrite Subst_not, Subst_eq, SubstTerm_PAsucc, SubstTerm_var in H0.
      rewrite SubstTerm_PAzero in H0. exact H0.
      apply IsLterm_PAnat.
      apply IsFreeForSubst_PAnat.
      rewrite IsLproposition_not, IsLproposition_eq.
      unfold PAsucc, PAzero. rewrite IsLterm_op1, IsLterm_var, IsLterm_const.
      reflexivity.
      rewrite IsLproposition_eq, IsLterm_PAnat, IsLterm_PAnat. reflexivity.
      apply NatDivDef.
    + apply LeqElimSubstVarPAnat.
      rewrite SubstTerm_PAzero.
      apply hypprop.
      apply IsLterm_PAnat. apply IsLterm_PAnat.
      unfold PAle, PAmult, PAsucc.
      reduce_subst; simpl.
      rewrite SubstTerm_PAnat.
      rewrite SubstTerm_PAnat.
      apply LandIntro. apply PAle_normalize.
      destruct j. apply le_0_n.
      apply Nat.div_le_upper_bound. discriminate.
      rewrite <- (Nat.mul_1_l i) at 1.
      apply Nat.mul_le_mono_nonneg_r. apply le_0_n. apply le_n_S, le_0_n.
      rewrite (SubstTerm_PAzero (PAnat j)).
      rewrite (SubstTerm_PAzero (PAnat (i/j))).
      exact (NatDivCorrect i j).
  - apply hypprop. apply IsLterm_var. apply IsLterm_var.
  - intros. unfold PAle, PAzero, PAmult, PAsucc, Leq.
    rewrite VarOccursFreeInFormula_and, VarOccursFreeInFormula_rel2.
    rewrite VarOccursInTerm_var, VarOccursInTerm_var.
    rewrite VarOccursFreeInFormula_or, VarOccursFreeInFormula_and.
    rewrite VarOccursFreeInFormula_rel2, VarOccursFreeInFormula_rel2.
    rewrite VarOccursFreeInFormula_and, VarOccursFreeInFormula_rel2.
    rewrite VarOccursFreeInFormula_rel2, VarOccursInTerm_op1.
    rewrite VarOccursInTerm_op2, VarOccursInTerm_op2, VarOccursInTerm_op1.
    rewrite VarOccursInTerm_var, VarOccursInTerm_var, VarOccursInTerm_const.
    rewrite VarOccursInTerm_var.
    destruct v. inversion H. simpl. apply le_S_n in H.
    destruct v. inversion H. simpl. apply le_S_n in H.
    destruct v. inversion H. reflexivity.
Qed.

Lemma NatSubDef : forall (i j k : nat),
    (k <= i)%nat
    -> IsProved IsWeakHeytingAxiom
               (Limplies
       (Lor (Land (Leq (PAnat k) PAzero) (PAle (PAnat i) (PAnat j)))
          (Leq (PAplus (PAnat k) (PAnat j)) (PAnat i)))
       (Leq (PAnat k) (PAnat (i - j)))).
Proof.
  intros i j k klei.
  apply LorElim.
  - apply PushHypothesis.
    assert (IsLproposition (Limplies (PAle (PAnat i) (PAnat j))
                                     (Leq (Lvar 0) (PAnat (i - j)))) = true)
      as hypprop.
    { unfold PAle.
      rewrite IsLproposition_implies, IsLproposition_rel2, IsLproposition_eq.
      rewrite IsLterm_PAnat, IsLterm_PAnat, IsLterm_var, IsLterm_PAnat.
      reflexivity. }
    pose proof (LeqElim IsWeakHeytingAxiom
                        (Limplies (PAle (PAnat i) (PAnat j))
                                  (Leq (Lvar 0) (PAnat (i - j))))
                        PAzero (PAnat k) 0) as H.
    rewrite Subst_implies, Subst_implies, Subst_PAle, Subst_PAle in H.
    rewrite SubstTerm_PAnat, SubstTerm_PAnat, SubstTerm_PAnat, SubstTerm_PAnat in H.
    rewrite Subst_eq, SubstTerm_var, SubstTerm_PAnat in H; simpl in H.
    rewrite Subst_eq, SubstTerm_var, SubstTerm_PAnat in H; simpl in H.
    apply (LimpliesTrans _ _ (Leq PAzero (PAnat k))).
    apply LeqSym_impl. apply IsLterm_PAnat. apply IsLterm_const.
    apply (RemoveRedundantHypothesis
             _ _
             (Limplies (PAle (PAnat i) (PAnat j)) (Leq PAzero (PAnat (i - j))))
             (Limplies (PAle (PAnat i) (PAnat j)) (Leq (PAnat k) (PAnat (i - j)))))
      in H.
    apply H. exact hypprop.
    apply IsLterm_const. apply IsLterm_PAnat.
    apply (IsFreeForSubst_PAnat 0). exact hypprop.
    apply IsFreeForSubst_PAnat. exact hypprop.
    apply DropHypothesis.
    unfold PAzero. rewrite IsLproposition_eq, IsLterm_const, IsLterm_PAnat.
    reflexivity.
    destruct (le_lt_dec i j).
    apply Nat.sub_0_le in l. rewrite l.
    apply DropHypothesis, LeqRefl, IsLterm_const.
    unfold PAle. rewrite IsLproposition_rel2, IsLterm_PAnat, IsLterm_PAnat.
    reflexivity.
    apply FalseElim_impl.
    exact (PAlt_not_le _ _ l).
    unfold PAzero. rewrite IsLproposition_eq, IsLterm_const, IsLterm_PAnat.
    reflexivity.
  - (* i = k + j *)
    pose proof (Nat.add_sub_eq_l i j k).
    apply (LimpliesTrans _ _ (Leq (PAnat (k+j)) (PAnat i))).
    pose proof (LeqElim_rel2 IsWeakHeytingAxiom 0
                             (PAplus (PAnat k) (PAnat j)) (PAnat (k + j))
                             (PAnat i) (PAnat i)).
    apply LandElim1 in H0. exact H0.
    apply PAplus_normalize. apply LeqRefl. apply IsLterm_PAnat.
    destruct (Nat.eq_dec (k+j) i).
    subst i.
    apply DropHypothesis.
    rewrite IsLproposition_eq, IsLterm_PAnat. reflexivity.
    rewrite H. apply LeqRefl. apply IsLterm_PAnat.
    rewrite Nat.add_comm. reflexivity.
    apply FalseElim_impl.
    destruct (Nat.lt_trichotomy i (k+j)).
    exact (PAlt_not_eq _ _ H0). destruct H0.
    rewrite H0 in n. exfalso. apply n. reflexivity.
    pose proof (PAlt_not_eq _ _ H0).
    apply NotByContradiction.
    apply (LimpliesTrans _ _ (Leq (PAnat i) (PAnat (k + j)))).
    apply LeqSym_impl. apply IsLterm_PAnat. apply IsLterm_PAnat.
    apply FalseElim_impl. exact H1.
    rewrite IsLproposition_not, IsLproposition_eq, IsLterm_PAnat, IsLterm_PAnat.
    reflexivity.
    rewrite IsLproposition_eq, IsLterm_PAnat, IsLterm_PAnat. reflexivity.
Qed.

Lemma NatSubCorrect : forall (i j : nat),
  IsProved IsWeakHeytingAxiom
           (Lor (Land (Leq (PAnat (i - j)) PAzero) (PAle (PAnat i) (PAnat j)))
                (Leq (PAplus (PAnat (i - j)) (PAnat j)) (PAnat i))).
Proof.
  intros i j. destruct (le_lt_dec i j).
  - apply LorIntro1.
    unfold PAle, PAplus, PAsucc.
    rewrite IsLproposition_eq, IsLterm_op2.
    rewrite IsLterm_PAnat, IsLterm_PAnat, IsLterm_PAnat. reflexivity.
    apply LandIntro.
    apply Nat.sub_0_le in l. rewrite l. apply LeqRefl, IsLterm_const.
    apply PAle_normalize, l.
  - apply LorIntro2.
    unfold PAzero, PAle.
    rewrite IsLproposition_and, IsLproposition_eq, IsLproposition_rel2.
    rewrite IsLterm_PAnat, IsLterm_PAnat, IsLterm_PAnat, IsLterm_const.
    reflexivity.
    pose proof (LeqElim_rel2 IsWeakHeytingAxiom 0 _ _ _ _
                             (PAplus_normalize (i-j) j)
                             (LeqRefl _ (PAnat i) (IsLterm_PAnat _))) as H0.
    apply LandElim2 in H0.
    apply (LimpliesElim _ _ _ H0); clear H0.
    rewrite Nat.add_comm, <- (Minus.le_plus_minus j i).
    apply LeqRefl, IsLterm_PAnat.
    apply Nat.lt_le_incl, l.
Qed.

Lemma sub_repr : FunctionRepresented 2 Nat.sub.
Proof.
  assert (forall i j,
             IsLterm i = true ->
             IsLterm j = true ->
             IsLproposition
(Land (PAle (Lvar 2) i)
       (Lor (Land (Leq (Lvar 2) PAzero) (PAle i j))
        (Leq (PAplus (Lvar 2) j) i)))
      = true) as hypprop.
  { intros. unfold PAle, PAplus, PAsucc, PAzero.
    rewrite IsLproposition_and, IsLproposition_or, IsLproposition_and.
    rewrite IsLproposition_rel2, IsLproposition_eq, IsLproposition_rel2.
    rewrite IsLproposition_eq, IsLterm_op2, IsLterm_var, IsLterm_const, H, H0.
    reflexivity. }
  (* X2 = X0 - X1 *)
  apply (Build_FunctionRepresented 2
           _ (Land (PAle (Lvar 2) (Lvar 0))
                   (Lor (Land (Leq (Lvar 2) PAzero) (PAle (Lvar 0) (Lvar 1)))
                        (Leq (PAplus (Lvar 2) (Lvar 1)) (Lvar 0))))).
  - intro args. simpl. rewrite CoordTailNat.
    remember (CoordNat args 0) as i.
    remember (CoordNat args 1) as j.
    apply LforallIntro.
    rewrite Subst_and, Subst_or, Subst_and, Subst_or, Subst_and.
    rewrite Subst_and, Subst_eq, SubstTerm_PAzero.
    rewrite Subst_PAle, SubstTerm_var, SubstTerm_var; simpl.
    rewrite Subst_PAle, SubstTerm_var, SubstTerm_PAnat; simpl.
    rewrite Subst_eq, SubstTerm_var, SubstTerm_PAzero; simpl.
    rewrite Subst_PAle, Subst_eq, Subst_PAle; simpl.
    rewrite SubstTerm_var, Subst_eq, SubstTerm_var; simpl.
    rewrite SubstTerm_PAnat, SubstTerm_var, SubstTerm_PAplus; simpl.
    rewrite SubstTerm_var, SubstTerm_var; simpl.
    rewrite SubstTerm_PAplus, SubstTerm_var, SubstTerm_var; simpl.
    apply LandIntro.
    + apply PushHypothesis, LforallBounded.
      rewrite IsLproposition_implies.
      specialize (hypprop (PAnat i) (PAnat j) (IsLterm_PAnat _) (IsLterm_PAnat _)).
      rewrite IsLproposition_and in hypprop.
      apply andb_prop in hypprop. destruct hypprop. rewrite H0.
      rewrite IsLproposition_eq, IsLterm_var, IsLterm_PAnat. reflexivity.
      intros k H.
      rewrite Subst_implies, Subst_or, Subst_and, Subst_eq, Subst_eq.
      rewrite Subst_eq, SubstTerm_var, SubstTerm_PAnat, SubstTerm_PAnat; simpl.
      rewrite Subst_PAle, SubstTerm_PAzero, SubstTerm_PAnat, SubstTerm_PAnat.
      rewrite SubstTerm_PAplus, SubstTerm_var, SubstTerm_PAnat; simpl.
      apply NatSubDef, H.
    + apply LeqElimSubstVarPAnat. apply hypprop.
      apply IsLterm_PAnat. apply IsLterm_PAnat.
      rewrite Subst_and, Subst_or, Subst_and, Subst_PAle, Subst_PAle.
      rewrite Subst_eq, Subst_eq, SubstTerm_PAzero, SubstTerm_var; simpl.
      rewrite SubstTerm_PAnat, SubstTerm_PAnat, SubstTerm_PAplus, SubstTerm_var; simpl.
      rewrite SubstTerm_PAnat.
      apply LandIntro. apply PAle_normalize.
      apply Nat.le_sub_l. apply NatSubCorrect.
  - apply hypprop. apply IsLterm_var. apply IsLterm_var.
  - intros. unfold PAle, PAzero, PAplus, PAsucc, Leq.
    rewrite VarOccursFreeInFormula_and, VarOccursFreeInFormula_rel2.
    rewrite VarOccursInTerm_var, VarOccursInTerm_var.
    rewrite VarOccursFreeInFormula_or, VarOccursFreeInFormula_and.
    rewrite VarOccursFreeInFormula_rel2, VarOccursFreeInFormula_rel2.
    rewrite VarOccursFreeInFormula_rel2.
    rewrite VarOccursInTerm_var, VarOccursInTerm_var, VarOccursInTerm_const.
    rewrite VarOccursInTerm_var, VarOccursInTerm_op2, VarOccursInTerm_var.
    rewrite VarOccursInTerm_var.
    destruct v. inversion H. simpl. apply le_S_n in H.
    destruct v. inversion H. simpl. apply le_S_n in H.
    destruct v. inversion H. reflexivity.
Qed.

Lemma mod_repr : FunctionRepresented 2 Nat.modulo.
Proof.
  assert (forall i j : nat, i - (i/j)*j = i mod j)%nat as moddef.
  { intros. pose proof (Nat.div_mod_eq i j) as H.
    rewrite Nat.mul_comm in H.
    symmetry in H. exact (Nat.add_sub_eq_l i ((i/j)*j) (i mod j) H). }
  refine (FunctionRepresented_2_ext _ _ _ moddef). clear moddef.
  apply (ComposeRepr_22 Nat.sub _ sub_repr).
  exact (ComposeRepr_21 Nat.mul _ MultiplicationRepresented div_repr).
Qed.

Definition godel_beta (s t i : nat) : nat := s mod ((i+1)*t+1).

Lemma beta_repr : FunctionRepresented 3 godel_beta.
Proof.
  pose proof (IncrOutputVarRepresented _ _ mod_repr) as H; simpl in H.
  apply (ComposeRepr_31 _ (fun s t i => (i+1)*t+1) H)%nat.
  apply (Build_FunctionRepresented
           3 _ (Leq (Lvar 3) (PAsucc (PAmult (PAsucc (Lvar 2)) (Lvar 1))))).
  intro args. apply LforallIntro. simpl.
  do 3 rewrite CoordTailNat.
  remember (CoordNat args 0) as i.
  remember (CoordNat args 1) as j.
  remember (CoordNat args 2) as k.
  rewrite Subst_eq, SubstTerm_var, Subst_eq, Subst_eq. simpl.
  rewrite SubstTerm_var; simpl.
  rewrite SubstTerm_var; simpl.
  do 3 rewrite SubstTerm_PAsucc.
  do 3 rewrite SubstTerm_PAmult.
  do 3 rewrite SubstTerm_PAsucc.
  rewrite SubstTerm_var; simpl.
  rewrite SubstTerm_var; simpl.
  rewrite SubstTerm_var; simpl.
  rewrite SubstTerm_var; simpl.
  rewrite SubstTerm_var; simpl.
  rewrite SubstTerm_PAnat.
  apply (LeqElim_rel2 _ 0). apply LeqRefl. apply IsLterm_var.
  apply (LeqTrans _ _ (PAnat (HAstandardModelTerm (fun _ => O) (PAsucc (PAmult (PAsucc (PAnat k)) (PAnat j)))))).
  apply ClosedTerm_normalize.
  rewrite IsPeanoTerm_PAsucc, IsPeanoTerm_PAmult, IsPeanoTerm_PAsucc.
  rewrite IsPeanoTerm_PAnat. apply IsPeanoTerm_PAnat.
  intro v. unfold PAsucc, PAmult.
  rewrite VarOccursInTerm_op1, VarOccursInTerm_op2, VarOccursInTerm_op1.
  rewrite PAnat_closed, PAnat_closed. reflexivity.
  rewrite HAstandardModelTerm_succ, HAstandardModelTerm_mult.
  rewrite HAstandardModelTerm_succ, HAstandardModelTerm_PAnat.
  rewrite HAstandardModelTerm_PAnat.
  rewrite (Nat.add_comm k).
  rewrite <- (Nat.add_comm 1). apply LeqRefl. apply IsLterm_PAnat.
  unfold PAsucc, PAmult.
  rewrite IsLproposition_eq, IsLterm_var, IsLterm_op1, IsLterm_op2, IsLterm_op1.
  rewrite IsLterm_var, IsLterm_var. reflexivity.
  intros v H0. unfold Leq.
  rewrite VarOccursFreeInFormula_rel2, VarOccursInTerm_var.
  unfold PAsucc, PAmult.
  rewrite VarOccursInTerm_op1, VarOccursInTerm_op2, VarOccursInTerm_op1.
  rewrite VarOccursInTerm_var, VarOccursInTerm_var.
  destruct v. inversion H0. apply le_S_n in H0.
  destruct v. inversion H0. apply le_S_n in H0.
  destruct v. inversion H0. apply le_S_n in H0.
  destruct v. inversion H0. apply le_S_n in H0.
  reflexivity.
Qed.

(* We add a minimalist clause to beta_repr so that it better represents beta
   for possibly non-standard inputs, when the output is standard. *)
Definition beta_prop_min : nat :=
  let m := MaxVar beta_repr in
  (Land beta_repr
        (Lforall (S m) (Limplies (PAle (PAsucc (Lvar (S m))) (Lvar 3))
                                 (Lnot (Subst (Lvar (S m)) 3 beta_repr))))).
Lemma beta_representation_unique
  : FormulaRepresents 3 godel_beta beta_prop_min.
Proof.
  unfold beta_prop_min.
  pose (MaxVar beta_repr) as m. fold m.
  intro args. simpl.
  do 3 rewrite Subst_and.
  pose proof (fr_rep _ _ beta_repr args) as beta_rep.
  apply LforallElimIdemVar in beta_rep.
  apply LforallIntro, LandIntro. 
  - (* The new representation is syntactically stronger than beta_repr,
       so the first implication is trivial. *)
    apply LandElim1 in beta_rep.
    refine (LimpliesTrans _ _ _ _ _ beta_rep). clear beta_rep.
    apply LandElim1_impl.
    apply SubstIsLproposition. 
    apply SubstIsLproposition. 
    apply SubstIsLproposition. 
    apply fr_propprop.
    apply IsLterm_PAnat. apply IsLterm_PAnat. apply IsLterm_PAnat.
    apply SubstIsLproposition. 
    apply SubstIsLproposition. 
    apply SubstIsLproposition. 
    unfold PAle, PAsucc. reduce_islproposition.
    apply SubstIsLproposition. apply fr_propprop.
    apply IsLterm_var. apply IsLterm_PAnat.
    apply IsLterm_PAnat. apply IsLterm_PAnat.
  - (* Now the converse, we first clear the beta_repr clause. *)
    apply LandIntroHyp.
    apply LandElim2 in beta_rep. exact beta_rep.
    (* And we are left to prove than no number lower than godel_beta i j k
       satisfies beta_repr. LforallBounded_lt will pull the hypothesis in
       the meta-theory. *)
    do 3 rewrite CoordTailNat.
    simpl in beta_rep.
    do 3 rewrite CoordTailNat in beta_rep.
    remember (CoordNat args 0) as i.
    remember (CoordNat args 1) as j.
    remember (CoordNat args 2) as k.
    (* Replace Lvar 3 by godel_beta i j k *)
    apply LeqElimSubstVarPAnat. 
    apply SubstIsLproposition. 
    apply SubstIsLproposition. 
    apply SubstIsLproposition. 
    unfold PAle, PAsucc. reduce_islproposition.
    apply SubstIsLproposition. apply fr_propprop.
    apply IsLterm_var. apply IsLterm_PAnat.
    apply IsLterm_PAnat. apply IsLterm_PAnat. 
    (* Pull the bounded Lforall (S m) into the meta, as a new hypothesis
       H0 : a < godel_beta i j k *)
    assert (3 <= m)%nat.
    { destruct (le_lt_dec 3 (MaxVar beta_repr)). exact l. exfalso.
      pose proof (MaxVarDoesNotOccurFree beta_repr (fr_propprop _ _ beta_repr) 3 l).
      pose proof (fr_freevar _ _ beta_repr).
      rewrite H0 in H. discriminate H. } 
    assert (m =? 0 = false)%nat as m0.
    { apply Nat.eqb_neq. intro abs. rewrite abs in H. inversion H. }
    assert (m =? 1 = false)%nat as m1.
    { apply Nat.eqb_neq. intro abs. rewrite abs in H.
      apply le_S_n in H. inversion H. } 
    assert (m =? 2 = false)%nat as m2.
    { apply Nat.eqb_neq. intro abs. rewrite abs in H.
      apply le_S_n, le_S_n in H. inversion H. } 
    rewrite Subst_forall; simpl.
    rewrite Subst_forall; simpl; rewrite m0.
    rewrite Subst_forall; simpl; rewrite m1.
    rewrite Subst_forall; simpl; rewrite m2.
    do 4 rewrite Subst_implies.
    do 4 rewrite Subst_PAle, SubstTerm_PAsucc.
    reduce_subst; simpl. rewrite SubstTerm_var. simpl. rewrite m0.
    do 2 rewrite SubstTerm_var. simpl. rewrite m1.
    rewrite SubstTerm_var. simpl. rewrite m2.
    rewrite SubstTerm_var. simpl.
    rewrite SubstTerm_var. simpl.
    apply LforallIntro.
    apply LforallBounded_lt.
    rewrite IsLproposition_not.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply fr_propprop. apply IsLterm_var.
    apply IsLterm_PAnat. apply IsLterm_PAnat.
    apply IsLterm_PAnat. apply IsLterm_PAnat.
    intros a H0.
    (* Finish by showing that a cannot satisfy beta_repr,
       otherwise it would be equal to godel_beta i j k. *)
    rewrite Subst_not.
    rewrite (SubstSubstDiffCommutes _ 0 3).
    rewrite (SubstSubstDiffCommutes _ 1 3).
    rewrite (SubstSubstDiffCommutes _ 2 3).
    rewrite SubstSubstIdem, SubstTerm_var. simpl. rewrite m2.
    rewrite SubstSubstNested, SubstTerm_var, Nat.eqb_refl.
    + apply NotByContradiction.
      apply (LforallIntro _ _ 3) in beta_rep.
      apply (LforallElim _ _ _ (PAnat a)) in beta_rep.
      rewrite Subst_equiv, Subst_eq, SubstTerm_var in beta_rep.
      rewrite SubstTerm_PAnat in beta_rep. simpl in beta_rep.
      apply LandElim1 in beta_rep.
      apply (LimpliesTrans _ _ _ _ beta_rep). clear beta_rep.
      apply (LimpliesTrans _ _ (Leq (PAnat (godel_beta i j k)) (PAnat a))).
      apply LeqSym_impl. apply IsLterm_PAnat. apply IsLterm_PAnat.
      apply FalseElim_impl. 
      apply PAlt_not_eq, H0.
      rewrite IsLproposition_not.
      apply SubstIsLproposition.
      apply SubstIsLproposition.
      apply SubstIsLproposition.
      apply SubstIsLproposition.
      apply fr_propprop. 
      apply IsLterm_PAnat. apply IsLterm_PAnat. apply IsLterm_PAnat.
      apply IsLterm_PAnat. apply IsLterm_PAnat.
      apply IsFreeForSubst_PAnat.
      rewrite IsLproposition_equiv, SubstIsLproposition.
      rewrite IsLproposition_eq, IsLterm_var, IsLterm_PAnat. reflexivity.
      apply SubstIsLproposition.
      apply SubstIsLproposition.
      apply fr_propprop. 
      apply IsLterm_PAnat. apply IsLterm_PAnat. apply IsLterm_PAnat.
    + apply SubstIsLproposition.
      apply SubstIsLproposition.
      apply SubstIsLproposition.
      apply fr_propprop. 
      apply IsLterm_PAnat. apply IsLterm_PAnat. apply IsLterm_PAnat.
    + rewrite VarOccursFreeInFormula_SubstDiff, VarOccursFreeInFormula_SubstDiff.
      rewrite VarOccursFreeInFormula_SubstDiff.
      apply MaxVarDoesNotOccurFree. apply fr_propprop.
      apply Nat.le_refl. apply fr_propprop. discriminate.
      apply PAnat_closed.
      apply SubstIsLproposition. apply fr_propprop. apply IsLterm_PAnat.
      apply Nat.eqb_neq. exact m0.
      apply PAnat_closed.
      apply SubstIsLproposition.
      apply SubstIsLproposition.
      apply fr_propprop. apply IsLterm_PAnat. apply IsLterm_PAnat.
      apply Nat.eqb_neq. exact m1.
      apply PAnat_closed.
    + apply MaxVarFreeSubst_var.
      apply SubstIsLproposition.
      apply SubstIsLproposition.
      apply SubstIsLproposition.
      apply fr_propprop. 
      apply IsLterm_PAnat. apply IsLterm_PAnat. apply IsLterm_PAnat.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_PAnat. simpl.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_PAnat. simpl.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_PAnat. apply Nat.le_refl.
    + discriminate.
    + apply PAnat_closed.
    + rewrite VarOccursInTerm_var, Nat.eqb_sym. exact m1.
    + discriminate.
    + apply PAnat_closed.
    + rewrite VarOccursInTerm_var, Nat.eqb_sym. exact m0.
    + discriminate.
    + apply PAnat_closed.
    + apply VarOccursInTerm_var.
Qed.

Lemma beta_prop_min_IsLprop : IsLproposition beta_prop_min = true.
Proof.
  unfold beta_prop_min.
  unfold PAle, PAsucc.
  reduce_islproposition.
  rewrite fr_propprop, SubstIsLproposition.
  reflexivity. apply fr_propprop. apply IsLterm_var.
Qed.

Lemma beta_prop_min_vars :
  forall v:nat, (3 < v)%nat -> VarOccursFreeInFormula v beta_prop_min = false.
Proof.
  intros. unfold beta_prop_min.
  rewrite VarOccursFreeInFormula_and, fr_vars. 2: exact H.
  rewrite VarOccursFreeInFormula_forall.
  destruct (v =? S (MaxVar beta_repr))%nat eqn:des. reflexivity.
  simpl. unfold PAle, PAsucc.
  rewrite VarOccursFreeInFormula_implies, VarOccursFreeInFormula_rel2.
  rewrite VarOccursInTerm_op1, VarOccursInTerm_var, des, VarOccursInTerm_var.
  simpl. rewrite VarOccursFreeInFormula_not, VarOccursFreeInFormula_SubstDiff.
  rewrite fr_vars, Bool.orb_false_r.
  apply Nat.eqb_neq. intro abs. rewrite abs in H. exact (Nat.lt_irrefl _ H).
  exact H. apply fr_propprop. intro abs. rewrite abs in H. exact (Nat.lt_irrefl _ H).
  rewrite VarOccursInTerm_var. exact des.
Qed.

Lemma beta_repr_uniq :
  { repr : FunctionRepresented 3 godel_beta
    | forall n:nat, IsProved IsWeakHeytingAxiom
                        (Lforall 0 (Lforall 1 (Lforall 2
                           (Limplies (Land (Subst (PAnat n) 3 repr) repr)
                                     (Leq (PAnat n) (Lvar 3)))))) }.
Proof.
  exists (Build_FunctionRepresented
       3 _ _ beta_representation_unique
       beta_prop_min_IsLprop beta_prop_min_vars). 
  simpl.
  assert (3 <= MaxVar beta_repr)%nat as m3.
  { destruct (le_lt_dec 3%nat (MaxVar beta_repr)). exact l.
    pose proof (MaxVarDoesNotOccurFree beta_repr (fr_propprop _ _ beta_repr) 3 l).
    pose proof (fr_freevar _ _ beta_repr).
    rewrite H0 in H. discriminate H. } 
  assert (S (MaxVar beta_repr) =? 3 = false)%nat as m2.
  { apply Nat.eqb_neq. intro abs. inversion abs. rewrite H0 in m3.
    exact (Nat.lt_irrefl _ m3). } 
  intros n.
  apply LforallIntro, LforallIntro, LforallIntro.
  refine (LimpliesElim _ _ _ _ (PAnat_le_lt_total (S n) (Lvar 3) (IsLterm_var 3))).
  apply LorElim.
  - (* PAle (PAnat (S n)) (Lvar 3) *)
    apply PullHypothesis.
    apply (LimpliesTrans _ _ (Land (Subst (PAnat n) 3 beta_repr)
                                   (Lnot (Subst (PAnat n) 3 beta_repr)))).
    apply LandIntroHyp.
    apply DropFirstHypothesis.
    unfold PAle. reduce_islproposition. rewrite IsLterm_PAnat. reflexivity.
    apply DropSecondHypothesis.
    exact beta_prop_min_IsLprop.
    unfold beta_prop_min. rewrite Subst_and.
    apply LandElim1_impl.
    apply SubstIsLproposition. apply fr_propprop. apply IsLterm_PAnat. 
    pose proof beta_prop_min_IsLprop. unfold beta_prop_min in H.
    rewrite IsLproposition_and in H. apply andb_prop in H. 
    destruct H as [_ H].
    apply SubstIsLproposition. exact H. apply IsLterm_PAnat. 
    apply (LimpliesTrans _ _ (Land (PAle (PAnat (S n)) (Lvar 3)) beta_prop_min)).
    apply LandIntroHyp.
    apply DropSecondHypothesis.
    rewrite IsLproposition_and, SubstIsLproposition.
    exact beta_prop_min_IsLprop. exact beta_prop_min_IsLprop.
    apply IsLterm_PAnat.
    apply LimpliesRefl. unfold PAle.
    rewrite IsLproposition_rel2, IsLterm_PAnat. apply IsLterm_var.
    apply DropFirstHypothesis. unfold PAle.
    rewrite IsLproposition_rel2, IsLterm_PAnat. apply IsLterm_var. 
    apply LandElim2_impl.
    apply SubstIsLproposition. exact beta_prop_min_IsLprop.
    apply IsLterm_PAnat. exact beta_prop_min_IsLprop.
    unfold beta_prop_min.
    apply (LimpliesTrans _ _ (Land (PAle (PAnat (S n)) (Lvar 3))
             (Subst (PAnat n) (S (MaxVar beta_repr))
                (Limplies (PAle (PAsucc (Lvar (S (MaxVar beta_repr)))) (Lvar 3))
                   (Lnot (Subst (Lvar (S (MaxVar beta_repr))) 3 beta_repr)))))).
    apply LandIntroHyp.
    apply LandElim1_impl.
    unfold PAle. rewrite IsLproposition_rel2, IsLterm_PAnat.
    apply IsLterm_var. 
    unfold PAle, PAsucc. reduce_islproposition.
    rewrite fr_propprop. apply SubstIsLproposition. apply fr_propprop.
    apply IsLterm_var.
    apply DropFirstHypothesis.
    unfold PAle. rewrite IsLproposition_rel2, IsLterm_PAnat.
    apply IsLterm_var.
    apply DropFirstHypothesis. apply fr_propprop.
    apply LforallElim_impl.
    unfold PAle, PAsucc. reduce_islproposition.
    apply SubstIsLproposition. apply fr_propprop.
    apply IsLterm_var. apply IsLterm_PAnat.
    unfold PAle.
    rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2.
    apply IsFreeForSubst_PAnat.
    rewrite IsLproposition_not. apply SubstIsLproposition.
    apply fr_propprop. apply IsLterm_var.
    rewrite Subst_implies, Subst_PAle, SubstTerm_PAsucc, SubstTerm_var, Nat.eqb_refl.
    rewrite SubstTerm_var, Nat.eqb_sym, m2, Subst_not, SubstSubstNested. 
    rewrite SubstTerm_var, Nat.eqb_refl.
    apply CommuteHypotheses.
    apply PushHypothesis. apply LimpliesRefl.
    unfold PAle. reduce_islproposition.
    rewrite IsLterm_PAnat, SubstIsLproposition. reflexivity.
    apply fr_propprop. apply IsLterm_PAnat. apply fr_propprop.
    apply MaxVarDoesNotOccurFree. apply fr_propprop. apply Nat.le_refl.
    apply MaxVarFreeSubst_var. apply fr_propprop. apply Nat.le_refl.
    apply PushHypothesis, IsProvedPropAx, Ax5IsPropAx, Ax5IsAx5.
    apply SubstIsLproposition. apply fr_propprop. apply IsLterm_PAnat.
    rewrite IsLproposition_eq, IsLterm_PAnat. apply IsLterm_var.
  - apply (LimpliesTrans _ _ (PAle (Lvar 3) (PAnat n))).
    pose proof (PAle_decr (PAnat n) (IsLterm_PAnat n)).
    apply (LforallIntro _ _ 0) in H.
    apply (LforallElim _ _ _ (Lvar 3)) in H.
    rewrite Subst_implies, Subst_PAle, SubstTerm_PAsucc, SubstTerm_var in H.
    simpl in H. rewrite SubstTerm_PAsucc, SubstTerm_PAnat, Subst_PAle in H.
    rewrite SubstTerm_var, SubstTerm_PAnat in H. exact H.
    apply IsLterm_var.
    unfold PAle.
    rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2, IsFreeForSubst_rel2.
    reflexivity.
    apply LforallBounded.
    rewrite IsLproposition_implies, IsLproposition_and, SubstIsLproposition.
    rewrite beta_prop_min_IsLprop, IsLproposition_eq, IsLterm_PAnat.
    apply IsLterm_var. apply beta_prop_min_IsLprop. apply IsLterm_PAnat.
    intros j jlen.
    rewrite Subst_implies, Subst_and, SubstSubstIdem, SubstTerm_PAnat.
    rewrite Subst_eq, SubstTerm_PAnat, SubstTerm_var. simpl.
    destruct (Nat.lt_trichotomy j n). clear jlen. 
    apply (LimpliesTrans _ _ (Land (Subst (PAnat j) 3 beta_repr)
                                   (Lnot (Subst (PAnat j) 3 beta_repr)))).
    apply LandIntroHyp.
    apply DropFirstHypothesis.
    apply SubstIsLproposition. apply beta_prop_min_IsLprop.
    apply IsLterm_PAnat.
    unfold beta_prop_min. rewrite Subst_and.
    apply LandElim1_impl.
    apply SubstIsLproposition. apply fr_propprop. apply IsLterm_PAnat.
    pose proof beta_prop_min_IsLprop. unfold beta_prop_min in H0.
    rewrite IsLproposition_and in H0. apply andb_prop in H0. 
    destruct H0 as [_ H0].
    apply SubstIsLproposition. exact H0. apply IsLterm_PAnat.
    apply DropSecondHypothesis.
    apply SubstIsLproposition. apply beta_prop_min_IsLprop.
    apply IsLterm_PAnat.
    unfold beta_prop_min.
    rewrite Subst_and, Subst_forall.
    rewrite m2.
    rewrite Subst_implies, Subst_PAle, SubstTerm_PAsucc, SubstTerm_var.
    rewrite m2, SubstTerm_var, Subst_not, SubstSubstIdem. simpl.
    rewrite SubstTerm_var, m2.
    apply DropFirstHypothesis.
    apply SubstIsLproposition. apply fr_propprop. apply IsLterm_PAnat.
    refine (LimpliesTrans _ _ _ _ (LforallElim_impl _ _ _ (PAnat j) _ _ _) _).
    unfold PAle, PAsucc. reduce_islproposition.
    rewrite IsLterm_PAnat. apply SubstIsLproposition.
    apply fr_propprop. apply IsLterm_var. apply IsLterm_PAnat. 
    apply IsFreeForSubst_PAnat.
    unfold PAle, PAsucc. reduce_islproposition.
    rewrite IsLterm_PAnat. apply SubstIsLproposition.
    apply fr_propprop. apply IsLterm_var.
    rewrite Subst_implies, Subst_PAle, SubstTerm_PAsucc, SubstTerm_var.
    rewrite Nat.eqb_refl, SubstTerm_PAnat, Subst_not, SubstSubstNested.
    rewrite SubstTerm_var, Nat.eqb_refl.
    apply LimpliesElim_impl.
    rewrite IsLproposition_not. apply SubstIsLproposition.
    apply fr_propprop. apply IsLterm_PAnat.
    apply (PAle_normalize (S j) n H).
    apply fr_propprop.
    apply MaxVarDoesNotOccurFree. apply fr_propprop. apply Nat.le_refl.
    apply MaxVarFreeSubst_var. apply fr_propprop. apply Nat.le_refl.
    apply PushHypothesis.
    apply IsProvedPropAx, Ax5IsPropAx, Ax5IsAx5.
    apply SubstIsLproposition. apply fr_propprop. apply IsLterm_PAnat.
    rewrite IsLproposition_eq, IsLterm_PAnat. apply IsLterm_PAnat.
    destruct H.
    subst j. apply DropHypothesis.
    rewrite IsLproposition_and, SubstIsLproposition. reflexivity.
    apply beta_prop_min_IsLprop. apply IsLterm_PAnat.
    apply LeqRefl. apply IsLterm_PAnat.
    exfalso. apply (Nat.lt_irrefl n). exact (Nat.lt_le_trans _ _ _ H jlen).
Qed.

(* Show that the modulos inside the beta function are pairwise coprime. *)
Lemma BetaRelPrime : forall (i j : Z) (m : nat),
    0 < i < j
    -> j <= Z.of_nat m
    -> rel_prime (i*Z.of_nat (fact m)+1) (j*Z.of_nat (fact m)+1).
Proof.
  intros. constructor.
  exists (i*Z.of_nat (fact m)+1). rewrite Z.mul_1_r. reflexivity.
  exists (j*Z.of_nat (fact m)+1). rewrite Z.mul_1_r. reflexivity.
  intros r H1 H2.
  assert ((r | (j-i)*Z.of_nat (fact m))).
  { destruct H1, H2. exists (x0-x).
    rewrite Z.mul_sub_distr_r.
    rewrite Z.mul_sub_distr_r.
    rewrite <- H2, <- H1. ring. }
  rewrite Z.mul_comm in H3.
  apply Gauss in H3.
  - apply Zdivide_Zabs_l.
    assert (0 < j - i) as jipos by apply Z.lt_0_sub, H.
    pose proof (Zdivide_bounds _ _ H3) as rle.
    assert ((Z.abs r | Z.of_nat (fact m))).
    apply ZdivideFact.
    split. destruct r. exfalso.
    destruct H3. rewrite Z.mul_0_r in H3.
    rewrite H3 in jipos. inversion jipos.
    reflexivity. reflexivity.
    apply (Z.le_trans _ (Z.abs (j-i))). apply rle.
    intro abs. rewrite abs in jipos. inversion jipos.
    rewrite Z.abs_eq.
    apply (Z.le_trans _ j).
    apply Z.le_sub_nonneg. apply Z.lt_le_incl, H. exact H0.
    apply Z.lt_le_incl, jipos.
    apply Zdivide_Zabs_inv_l in H1.
    destruct H4, H1. rewrite H4 in H1.
    exists (x0 - i*x).
    rewrite Z.mul_sub_distr_r, <- H1. ring.
  - apply bezout_rel_prime.
    destruct H1 as [x H1].
    apply (Bezout_intro _ _ _ x (-i)).
    rewrite <- H1. ring.
Qed.

Fixpoint MaxSeq (n l : nat) {struct l} : nat :=
  match l with
  | O => O   (* neutral for Nat.max *)
  | S k => Nat.max (CoordNat n 0) (MaxSeq (TailNat n) k)
  end.

Lemma CoordLeMaxSeq : forall l i n,
    (i < l)%nat
    -> (CoordNat n i <= MaxSeq n l)%nat.
Proof.
  induction l.
  - intros. inversion H.
  - intros. simpl.
    destruct i. apply Nat.le_max_l.
    rewrite <- CoordTailNat.
    apply le_S_n in H.
    exact (Nat.le_trans _ _ _ (IHl _ _ H) (Nat.le_max_r _ _)).
Qed.

Lemma fact_le_id : forall n:nat, (n <= fact n)%nat.
Proof.
  induction n.
  - apply le_S, Nat.le_refl.
  - rewrite <- (Nat.mul_1_r (S n)) at 1.
    change (fact (S n)) with ((S n) * fact n)%nat.
    apply Nat.mul_le_mono_nonneg_l. apply le_0_n.
    apply lt_O_fact.
Qed.

(* The other encoding of sequences, by the beta function.
   Beta is simple enough to be represented by a direct arithmetic formula,
   but it is not injective so it cannot replace CoordNat. Beta is
   sufficient to prove that recursive definitions like CoordNat are represented. *)
Lemma BetaSeq : forall n:nat, exists (s:nat),
      forall i:nat, (i < LengthNat n)%nat
             -> godel_beta s (fact (MaxSeq (ConsNat (LengthNat n) n) (S (LengthNat n)))) i
               = CoordNat n i.
Proof.
  intro n.
  pose (fact (MaxSeq (ConsNat (LengthNat n) n) (S (LengthNat n)))) as t.
  pose (MapNat (fun i => (i+1)*t+1)%nat (RangeNat 0 (LengthNat n))) as modulos.
  assert (LengthNat modulos = LengthNat n) as moduloslen.
  { unfold modulos. rewrite LengthMapNat, LengthRangeNat. reflexivity. }
  destruct (ChineseRemainder modulos n) as [s H].
  - exact moduloslen.
  - intros i H. unfold modulos.
    rewrite CoordMapNat, CoordRangeNat. simpl.
    apply (Nat.le_lt_trans _ t).
    refine (Nat.le_trans _ _ _ _ (fact_le_id _)).
    rewrite <- (CoordConsTailNat i n (LengthNat n)).
    apply CoordLeMaxSeq. apply le_n_S.
    rewrite moduloslen in H. exact H.
    rewrite <- (Nat.add_comm 1). apply le_n_S.
    rewrite <- (Nat.mul_1_l t) at 1.
    apply Nat.mul_le_mono_nonneg_r. apply le_0_n.
    rewrite Nat.add_comm. apply le_n_S, le_0_n.
    rewrite <- moduloslen. exact H.
    rewrite LengthRangeNat, <- moduloslen. exact H.
  - intros i j H. unfold modulos.
    rewrite moduloslen in H.
    rewrite CoordMapNat, CoordMapNat, CoordRangeNat, CoordRangeNat.
    simpl.
    rewrite Nat2Z.inj_add, Nat2Z.inj_add. simpl.
    rewrite Nat2Z.inj_mul, Nat2Z.inj_mul.
    apply BetaRelPrime.
    split. apply (Nat2Z.inj_lt 0).
    rewrite Nat.add_comm. apply le_n_S, le_0_n.
    apply Nat2Z.inj_lt. rewrite (Nat.add_comm i), (Nat.add_comm j).
    apply le_n_S, H.
    apply Nat2Z.inj_le. simpl. rewrite CoordConsHeadNat.
    refine (Nat.le_trans _ _ _ _ (Nat.le_max_l _ _)).
    rewrite Nat.add_comm. apply H. apply H.
    exact (Nat.lt_trans _ _ _ (proj1 H) (proj2 H)).
    rewrite LengthRangeNat. apply H.
    rewrite LengthRangeNat.
    exact (Nat.lt_trans _ _ _ (proj1 H) (proj2 H)).
  - exists s. intros i H0. unfold godel_beta.
    rewrite moduloslen in H.
    specialize (H i H0). unfold modulos in H.
    rewrite CoordMapNat, CoordRangeNat in H. exact H.
    exact H0. rewrite LengthRangeNat. exact H0.
Qed.


(* This proposition asserts the existence of a finite sequence
   beta(s,t,0), ..., beta(s,t,k) such as
   beta(s,t,0) = init and ... beta(s,t,1+i) = u(i, beta(s,t,i)).
   We take s = Lvar m and t = Lvar (1+m).

   It represents function nat_rec (fun _ => nat) init u
    = (fix F (k : nat) : nat := match k with
                             | O => init
                             | S p => u p (F p)
                             end) *)
Definition betast (m : nat) : nat
  := Subst (Lvar (1+m)) 1 (Subst (Lvar m) 0 (proj1_sig beta_repr_uniq)).
Definition beta_rec_body (m uprop bound : nat) :=
  (Lforall (2+m) (Limplies (PAle (PAsucc (Lvar (2+m))) bound)
          (Lexists (3+m) (Lexists (4+m)
             (* X3+m = beta(s,t,X2+m) is the recursive computation.
                X4+m = beta(s,t,1+X2+m) is the next value. *)
             (Land (Subst (Lvar (3+m)) 3 (Subst (Lvar (2+m)) 2 (betast m)))
             (Land (Subst (Lvar (4+m)) 3 (Subst (PAsucc (Lvar (2+m))) 2 (betast m)))
                   (Subst (Lvar (4+m)) 2 (Subst (Lvar (3+m)) 1
                                                (Subst (Lvar (2+m)) 0 uprop))))))))).
Definition nat_rec_representation (uprop : nat) : nat :=
  let m := S (Nat.max (MaxVar (proj1_sig beta_repr_uniq)) (MaxVar uprop)) in
  Lexists m (Lexists (1+m)  (* the s,t that define the beta-sequence *)
    (Land (Land
       (Lexists (2+m)    (* beta(s,t,0) = X0 *)
                (Land (Leq (Lvar (2+m)) (Lvar 0))
                      (Subst (Lvar (2+m)) 3 (Subst PAzero 2 (betast m)))))
       (beta_rec_body m uprop (Lvar 1)))
       (Lexists (2+m) (Lexists (3+m)   (* beta(s,t,X1) = X2 *)
          (Land (Leq (Lvar (2+m)) (Lvar 1))
          (Land (Leq (Lvar (3+m)) (Lvar 2))
                (Subst (Lvar (3+m)) 3 (Subst (Lvar (2+m)) 2 (betast m))))))))).

Lemma betast_IsLprop : forall m, IsLproposition (betast m) = true.
Proof.
  intros.
  apply SubstIsLproposition.
  apply SubstIsLproposition.
  apply fr_propprop. apply IsLterm_var. apply IsLterm_var.
Qed.

Lemma betast_vars : forall m v,
    (0 <> m)%nat
    -> (v <= 1)%nat -> VarOccursFreeInFormula v (betast m) = false.
Proof.
  intros m v H H0. unfold betast.
  destruct v.
  - apply VarOccursFreeInFormula_SubstClosed.
    apply VarOccursFreeInFormula_SubstIdem.
    apply fr_propprop.
    rewrite VarOccursInTerm_var. apply Nat.eqb_neq, H.
    apply VarOccursInTerm_var.
  - destruct v. apply VarOccursFreeInFormula_SubstIdem.
    apply SubstIsLproposition. apply fr_propprop.
    apply IsLterm_var. 
    rewrite VarOccursInTerm_var. simpl.
    destruct m. exfalso. apply H. reflexivity. reflexivity.
    exfalso. apply le_S_n in H0. inversion H0.
Qed.

Lemma MaxVar_betast : forall m,
  (MaxVar (betast m) <= Nat.max (S m) (MaxVar (proj1_sig beta_repr_uniq)))%nat.
Proof.
  intro m.
  apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
  apply Nat.max_lub. rewrite MaxVarTerm_var. apply Nat.le_max_l.
  apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
  apply Nat.max_lub. rewrite MaxVarTerm_var.
  apply (Nat.le_trans _ (S m)). apply le_S, Nat.le_refl.
  apply Nat.le_max_l. apply Nat.le_max_r.
Qed.

Lemma betast_SubstSubst : forall m s t,
    (MaxVar (proj1_sig beta_repr_uniq) < m)%nat
    -> (2 <= m)%nat
    -> Subst (PAnat t) (S m) (Subst (PAnat s) m (betast m))
      = Subst (PAnat t) 1 (Subst (PAnat s) 0 (proj1_sig beta_repr_uniq)). 
Proof.
  intros. unfold betast. simpl.
  rewrite SubstSubstDiffCommutes.
  3: apply PAnat_closed. 3: apply PAnat_closed.
  assert (IsLproposition (Subst (Lvar m) 0 (proj1_sig beta_repr_uniq)) = true).
  { apply SubstIsLproposition. apply fr_propprop. apply IsLterm_var. }
  rewrite (SubstSubstNested _ H1), SubstTerm_var, Nat.eqb_refl. clear H1.
  rewrite SubstSubstDiffCommutes. apply f_equal.
  rewrite SubstSubstNested, SubstTerm_var, Nat.eqb_refl. reflexivity.
  apply fr_propprop.
  apply MaxVarDoesNotOccurFree. apply fr_propprop. exact H.
  apply MaxVarFreeSubst_var. apply fr_propprop. exact H.
  intro abs. rewrite abs in H0. apply le_S_n in H0. inversion H0.
  apply PAnat_closed. apply PAnat_closed.
  apply VarOccursFreeInFormula_SubstClosed.
  apply MaxVarDoesNotOccurFree. apply fr_propprop. apply le_S, H.
  rewrite VarOccursInTerm_var.
  apply Nat.eqb_neq. intro abs. apply (Nat.lt_irrefl m).
  rewrite <- abs at 2. apply Nat.le_refl.
  apply MaxVarFreeSubst_var.
  apply SubstIsLproposition.
  apply fr_propprop. apply IsLterm_var. apply le_n_S.
  apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
  apply Nat.max_lub. rewrite MaxVarTerm_var. apply Nat.le_refl.
  apply Nat.lt_le_incl, H.
  intro abs. apply (Nat.lt_irrefl m).
  rewrite <- abs at 2. apply Nat.le_refl. 
Qed.

Lemma beta_rec_body_IsLprop : forall m uprop bound,
    IsLproposition uprop = true 
    -> IsLterm bound = true 
    -> IsLproposition (beta_rec_body m uprop bound) = true.
Proof.
  intros. unfold beta_rec_body. unfold PAle, PAsucc.
  repeat (reduce_islproposition; rewrite SubstIsLproposition).
  rewrite H0. reflexivity. reflexivity. reflexivity.
  exact H. apply IsLterm_var. apply IsLterm_var.
  apply IsLterm_var. reflexivity. apply betast_IsLprop.
  rewrite IsLterm_op1. apply IsLterm_var. apply IsLterm_var.
  reflexivity. apply betast_IsLprop. apply IsLterm_var. apply IsLterm_var.
Qed.

Lemma beta_rec_body_vars : forall uprop bound v,
    let m := S (Nat.max (MaxVar (proj1_sig beta_repr_uniq)) (MaxVar uprop)) in
    (v <= 2)%nat
    -> IsLproposition uprop = true
    -> VarOccursInTerm v bound = false
    -> VarOccursFreeInFormula v (beta_rec_body m uprop bound) = false.
Proof.
  intros. unfold beta_rec_body.
  unfold PAle, PAsucc, VarOccursFreeInFormula.
  assert (2 + m =? v = false)%nat as H2.
  { apply Nat.eqb_neq. intro abs. apply (Nat.lt_irrefl (2+m)).
    rewrite abs at 1. apply le_n_S. apply (Nat.le_trans _ _ _ H).
    apply le_n_S, le_n_S, le_0_n. }
  assert (3 + m =? v = false)%nat as H3.
  { apply Nat.eqb_neq. intro abs. apply (Nat.lt_irrefl (3+m)).
    rewrite abs at 1. apply le_n_S. apply (Nat.le_trans _ _ _ H).
    apply le_n_S, le_n_S, le_0_n. }
  assert (4 + m =? v = false)%nat as H4.
  { apply Nat.eqb_neq. intro abs. apply (Nat.lt_irrefl (4+m)).
    rewrite abs at 1. apply le_n_S. apply (Nat.le_trans _ _ _ H).
    apply le_n_S, le_n_S, le_0_n. }
  reduce_subst; rewrite H2, H3, H4.
  apply Bool.negb_false_iff, Nat.eqb_eq in H1.
  rewrite H1.
  rewrite (Subst_nosubst _ _ 0), (Subst_nosubst _ _ 0), (Subst_nosubst _ _ 0).
  apply Bool.negb_false_iff, Nat.eqb_refl.
  destruct v. 2: destruct v.
  - apply VarOccursFreeInFormula_SubstClosed.
    apply VarOccursFreeInFormula_SubstClosed.
    apply VarOccursFreeInFormula_SubstIdem.
    exact H0.
    apply VarOccursInTerm_var.
    apply VarOccursInTerm_var.
    apply VarOccursInTerm_var.
  - rewrite VarOccursFreeInFormula_SubstDiff.
    apply VarOccursFreeInFormula_SubstIdem.
    apply SubstIsLproposition. exact H0. apply IsLterm_var.
    apply VarOccursInTerm_var.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    exact H0. apply IsLterm_var. apply IsLterm_var.
    discriminate. apply VarOccursInTerm_var.
  - destruct v.
    apply VarOccursFreeInFormula_SubstIdem.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    exact H0. apply IsLterm_var. apply IsLterm_var.
    apply VarOccursInTerm_var.
    exfalso. apply le_S_n, le_S_n in H. inversion H.
  - apply VarOccursFreeInFormula_SubstClosed.
    2: rewrite VarOccursInTerm_var, Nat.eqb_sym; exact H4.
    destruct v.
    apply VarOccursFreeInFormula_SubstClosed.
    apply betast_vars. discriminate. apply le_0_n.
    rewrite VarOccursInTerm_op1.
    rewrite VarOccursInTerm_var, Nat.eqb_sym. exact H2.
    destruct v.
    apply VarOccursFreeInFormula_SubstClosed.
    apply betast_vars. discriminate. apply Nat.le_refl.
    rewrite VarOccursInTerm_op1.
    rewrite VarOccursInTerm_var, Nat.eqb_sym. exact H2.
    destruct v.
    apply VarOccursFreeInFormula_SubstIdem.
    apply betast_IsLprop.
    rewrite VarOccursInTerm_op1.
    rewrite VarOccursInTerm_var, Nat.eqb_sym. exact H3.
    exfalso. apply le_S_n, le_S_n in H. inversion H.
  - apply VarOccursFreeInFormula_SubstClosed.
    2: rewrite VarOccursInTerm_var, Nat.eqb_sym; exact H3. 
    destruct v.
    apply VarOccursFreeInFormula_SubstClosed.
    apply betast_vars. discriminate. apply le_0_n.
    rewrite VarOccursInTerm_var, Nat.eqb_sym. exact H2.
    destruct v.
    apply VarOccursFreeInFormula_SubstClosed.
    apply betast_vars. discriminate. apply Nat.le_refl.
    rewrite VarOccursInTerm_var, Nat.eqb_sym. exact H2.
    destruct v.
    apply VarOccursFreeInFormula_SubstIdem.
    apply betast_IsLprop.
    rewrite VarOccursInTerm_var, Nat.eqb_sym. exact H3.
    exfalso. apply le_S_n, le_S_n in H. inversion H.
Qed.

Lemma beta_rec_body_subst_one : forall uprop k,
    let m := S (Nat.max (MaxVar (proj1_sig beta_repr_uniq)) (MaxVar uprop)) in
    IsLproposition uprop = true
    -> Subst (PAnat k) 1 (beta_rec_body m uprop (Lvar 1))
      = beta_rec_body m uprop (PAnat k).
Proof.
  intros. unfold beta_rec_body.
  unfold PAle, PAsucc.
  reduce_subst; simpl. 
  rewrite (Subst_nosubst _ _ (PAnat k)),
  (Subst_nosubst _ _ (PAnat k)), (Subst_nosubst _ _ (PAnat k)).
  reflexivity.
  rewrite VarOccursFreeInFormula_SubstDiff, VarOccursFreeInFormula_SubstIdem.
  reflexivity.
  apply SubstIsLproposition. exact H. apply IsLterm_var.
  rewrite VarOccursInTerm_var. reflexivity.
  apply SubstIsLproposition.
  apply SubstIsLproposition.
  exact H. apply IsLterm_var. apply IsLterm_var. discriminate.
  rewrite VarOccursInTerm_var. reflexivity.
  rewrite VarOccursFreeInFormula_SubstDiff, VarOccursFreeInFormula_SubstDiff.
  apply betast_vars. discriminate. apply Nat.le_refl.
  apply betast_IsLprop. discriminate.
  rewrite VarOccursInTerm_op1, VarOccursInTerm_var. reflexivity.
  apply SubstIsLproposition.
  apply betast_IsLprop. rewrite IsLterm_op1, IsLterm_var.
  reflexivity. discriminate.
  rewrite VarOccursInTerm_var. reflexivity.
  rewrite VarOccursFreeInFormula_SubstDiff, VarOccursFreeInFormula_SubstDiff.
  apply betast_vars. discriminate. apply Nat.le_refl.
  apply betast_IsLprop. discriminate.
  rewrite VarOccursInTerm_var. reflexivity.
  apply SubstIsLproposition.
  apply betast_IsLprop. rewrite IsLterm_var.
  reflexivity. discriminate.
  rewrite VarOccursInTerm_var. reflexivity. 
Qed.

Lemma nat_rec_repr_IsLprop : forall (uprop : nat),
    IsLproposition uprop = true
    -> IsLproposition (nat_rec_representation uprop) = true.
Proof.
  intros.
  pose (S (Nat.max (MaxVar beta_repr) (MaxVar uprop))) as m.
  unfold nat_rec_representation; fold m.
  rewrite IsLproposition_exists, IsLproposition_exists.
  rewrite IsLproposition_and. apply andb_true_intro. split.
  rewrite IsLproposition_and; apply andb_true_intro; split.
  - (* init *)
    rewrite IsLproposition_exists, IsLproposition_and, IsLproposition_eq.
    rewrite IsLterm_var, IsLterm_var.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply betast_IsLprop. apply IsLterm_const. apply IsLterm_var.
  - (* recursion body *)
    apply beta_rec_body_IsLprop. exact H. apply IsLterm_var.
  - (* end *)
    rewrite IsLproposition_exists, IsLproposition_exists.
    rewrite IsLproposition_and, IsLproposition_and.
    rewrite IsLproposition_eq, IsLproposition_eq.
    do 4 rewrite IsLterm_var.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply betast_IsLprop. apply IsLterm_var. apply IsLterm_var. 
Qed.

Lemma nat_rec_repr_vars : forall (uprop v : nat),
    IsLproposition uprop = true
    -> (3 <= v)%nat
    -> (forall k, 3 <= k -> VarOccursFreeInFormula k uprop = false)%nat
    -> VarOccursFreeInFormula v (nat_rec_representation uprop) = false.
Proof.
  intros uprop v upropprop H H0.
  destruct v. inversion H. apply le_S_n in H.
  destruct v. inversion H. apply le_S_n in H.
  destruct v. inversion H. apply le_S_n in H. clear H.
  pose (S (Nat.max (MaxVar (proj1_sig beta_repr_uniq)) (MaxVar uprop))) as m.
  unfold nat_rec_representation; fold m.
  rewrite VarOccursFreeInFormula_exists.
  destruct (S (S (S v)) =? m)%nat eqn:des; [reflexivity|simpl].
  rewrite VarOccursFreeInFormula_exists.
  destruct (S (S (S v)) =? S m)%nat eqn:des2; [reflexivity|simpl].
  assert (1 <= v -> VarOccursFreeInFormula (S (S (S v))) (betast m) = false)%nat.
  { intros. unfold betast.
    rewrite VarOccursFreeInFormula_SubstDiff, VarOccursFreeInFormula_SubstDiff.
    apply fr_vars. do 3 apply le_n_S. exact H.
    apply fr_propprop. discriminate.
    rewrite VarOccursInTerm_var, des. reflexivity.
    apply SubstIsLproposition. apply fr_propprop.
    apply IsLterm_var. discriminate.
    rewrite VarOccursInTerm_var. exact des2. }
  rewrite VarOccursFreeInFormula_and.
  apply Bool.orb_false_intro.
  rewrite VarOccursFreeInFormula_and; apply Bool.orb_false_intro.
  - (* init *)
    rewrite VarOccursFreeInFormula_exists.
    destruct (S (S (S v)) =? S (S m))%nat eqn:des3. reflexivity. simpl.
    unfold Leq. rewrite VarOccursFreeInFormula_and, VarOccursFreeInFormula_rel2.
    rewrite VarOccursInTerm_var, VarOccursInTerm_var, des3. simpl.
    destruct v.
    rewrite VarOccursFreeInFormula_SubstIdem. reflexivity.
    apply SubstIsLproposition.
    apply betast_IsLprop. apply IsLterm_const.
    rewrite VarOccursInTerm_var. exact des3.
    rewrite VarOccursFreeInFormula_SubstDiff, VarOccursFreeInFormula_SubstDiff.
    apply H. apply le_n_S, le_0_n.
    apply betast_IsLprop. discriminate.
    apply (PAnat_closed 0).
    apply SubstIsLproposition. apply betast_IsLprop.
    apply IsLterm_const. discriminate.
    rewrite VarOccursInTerm_var. exact des3.
  - (* recursion body *)
    unfold beta_rec_body. simpl.
    rewrite VarOccursFreeInFormula_forall.
    destruct (S (S (S v)) =? S (S m))%nat eqn:des3. reflexivity. simpl.
    rewrite VarOccursFreeInFormula_implies.
    apply Bool.orb_false_intro.
    unfold PAle, PAsucc.
    rewrite VarOccursFreeInFormula_rel2, VarOccursInTerm_op1.
    rewrite VarOccursInTerm_var, VarOccursInTerm_var, des3. reflexivity.
    rewrite VarOccursFreeInFormula_exists.
    destruct (S (S (S v)) =? S (S (S m)))%nat eqn:des4. reflexivity. simpl.
    rewrite VarOccursFreeInFormula_exists.
    destruct (S (S (S v)) =? S (S (S (S m))))%nat eqn:des5. reflexivity. simpl.
    rewrite VarOccursFreeInFormula_and. apply Bool.orb_false_intro.
    destruct v.
    rewrite VarOccursFreeInFormula_SubstIdem. reflexivity.
    apply SubstIsLproposition.
    apply betast_IsLprop. apply IsLterm_var.
    rewrite VarOccursInTerm_var. exact des4.
    rewrite VarOccursFreeInFormula_SubstDiff, VarOccursFreeInFormula_SubstDiff.
    apply H. apply le_n_S, le_0_n.
    apply betast_IsLprop. discriminate.
    rewrite VarOccursInTerm_var. exact des3.
    apply SubstIsLproposition. apply betast_IsLprop.
    apply IsLterm_var. discriminate.
    rewrite VarOccursInTerm_var. exact des4.
    rewrite VarOccursFreeInFormula_and.
    apply Bool.orb_false_intro.
    destruct v.
    rewrite VarOccursFreeInFormula_SubstIdem. reflexivity.
    apply SubstIsLproposition.
    apply betast_IsLprop. unfold PAsucc.
    rewrite IsLterm_op1. apply IsLterm_var.
    rewrite VarOccursInTerm_var. exact des4.
    rewrite VarOccursFreeInFormula_SubstDiff, VarOccursFreeInFormula_SubstDiff.
    apply H. apply le_n_S, le_0_n. apply betast_IsLprop.
    discriminate. unfold PAsucc. rewrite VarOccursInTerm_op1.
    rewrite VarOccursInTerm_var. exact des3.
    apply SubstIsLproposition. apply betast_IsLprop.
    unfold PAsucc. rewrite IsLterm_op1.
    apply IsLterm_var. discriminate.
    rewrite VarOccursInTerm_var. exact des5.
    rewrite VarOccursFreeInFormula_SubstDiff.
    rewrite VarOccursFreeInFormula_SubstDiff.
    rewrite VarOccursFreeInFormula_SubstDiff.
    apply H0. do 3 apply le_n_S. apply le_0_n.
    exact upropprop. discriminate.
    rewrite VarOccursInTerm_var. exact des3.
    apply SubstIsLproposition. exact upropprop.
    apply IsLterm_var. discriminate.
    rewrite VarOccursInTerm_var. exact des4.
    apply SubstIsLproposition.
    apply SubstIsLproposition. exact upropprop.
    apply IsLterm_var. apply IsLterm_var. discriminate.
    rewrite VarOccursInTerm_var. exact des5.
  - (* end *)
    rewrite VarOccursFreeInFormula_exists.
    destruct (S (S (S v)) =? S (S m))%nat eqn:des3. reflexivity. simpl.
    rewrite VarOccursFreeInFormula_exists.
    destruct (S (S (S v)) =? S (S (S m)))%nat eqn:des4. reflexivity. simpl.
    unfold Leq. rewrite VarOccursFreeInFormula_and, VarOccursFreeInFormula_and.
    rewrite VarOccursFreeInFormula_rel2, VarOccursFreeInFormula_rel2.
    rewrite VarOccursInTerm_var, des3.
    rewrite VarOccursInTerm_var, VarOccursInTerm_var, des4.
    rewrite VarOccursInTerm_var. simpl.
    destruct v.
    rewrite VarOccursFreeInFormula_SubstIdem. reflexivity.
    apply SubstIsLproposition.
    apply betast_IsLprop. apply IsLterm_var.
    rewrite VarOccursInTerm_var. reflexivity.
    rewrite VarOccursFreeInFormula_SubstDiff, VarOccursFreeInFormula_SubstDiff.
    apply H. apply le_n_S, le_0_n.
    apply betast_IsLprop. discriminate.
    rewrite VarOccursInTerm_var. exact des3.
    apply SubstIsLproposition. apply betast_IsLprop.
    apply IsLterm_var. discriminate.
    rewrite VarOccursInTerm_var. exact des4.
Qed.

Lemma betast_uniq : forall v j k m,
    (MaxVar (proj1_sig beta_repr_uniq) < m)%nat ->
    (S m < v)%nat ->
    IsProved IsWeakHeytingAxiom
             (Limplies
                (Land (Subst (PAnat j) 3 (Subst (PAnat k) 2 (betast m)))
                      (Subst (Lvar v) 3 (Subst (PAnat k) 2 (betast m))) )
                (Leq (Lvar v) (PAnat j))).
Proof.
  intros.
  unfold betast.
  destruct beta_repr_uniq as [prop repr]; simpl.
  simpl in H.
  assert (4 <= m)%nat as m4.
  { destruct (le_lt_dec 3%nat (MaxVar prop)).
    apply le_n_S in l. exact (Nat.le_trans _ _ _ l H).
    pose proof (MaxVarDoesNotOccurFree prop (fr_propprop _ _ prop) 3 l).
    pose proof (fr_freevar _ _ prop).
    rewrite H2 in H1. discriminate H1. } 
  specialize (repr j).
  apply LforallElimIdemVar in repr.
  apply LforallElimIdemVar in repr.
  apply LforallElimIdemVar in repr.
  apply (LforallIntro _ _ 0) in repr.
  apply (LforallElim _ _ _ (Lvar m)) in repr.
  rewrite Subst_implies, Subst_and, Subst_eq, SubstTerm_var, SubstTerm_PAnat in repr.
  simpl in repr. rewrite SubstSubstDiffCommutes in repr.
  apply (LforallIntro _ _ 1) in repr.
  apply (LforallElim _ _ _ (Lvar (S m))) in repr.
  rewrite Subst_implies, Subst_and, Subst_eq, SubstTerm_var, SubstTerm_PAnat in repr.
  simpl in repr. rewrite SubstSubstDiffCommutes in repr.
  apply (LforallIntro _ _ 2) in repr.
  apply (LforallElim _ _ _ (PAnat k)) in repr.
  rewrite Subst_implies, Subst_and, Subst_eq, SubstTerm_var, SubstTerm_PAnat in repr.
  simpl in repr. rewrite SubstSubstDiffCommutes in repr.
  apply (LforallIntro _ _ 3) in repr.
  apply (LforallElim _ _ _ (Lvar v)) in repr.
  rewrite Subst_implies, Subst_and, Subst_eq, SubstTerm_var, SubstTerm_PAnat in repr.
  simpl in repr. rewrite SubstSubstIdem, SubstTerm_PAnat in repr.
  apply (LimpliesTrans _ _ (Leq (PAnat j) (Lvar v))).
  exact repr. apply LeqSym_impl. apply IsLterm_PAnat. apply IsLterm_var.
  apply IsLterm_var. unfold Leq.
  rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2, Bool.andb_true_r.
  rewrite IsFreeForSubst_and.
  rewrite IsFreeForSubst_nosubst.
  apply MaxVarFreeSubst_var.
  apply SubstIsLproposition.
  apply SubstIsLproposition.
  apply SubstIsLproposition.
  apply fr_propprop. apply IsLterm_var. apply IsLterm_var. apply IsLterm_PAnat.
  apply (Nat.le_lt_trans _ _ _ (MaxVar_Subst _ _ _)).
  rewrite MaxVarTerm_PAnat. simpl.
  apply (Nat.le_lt_trans _ _ _ (MaxVar_Subst _ _ _)).
  apply (Nat.le_lt_trans _ (S m)). 2: exact H0.
  rewrite MaxVarTerm_var.
  apply Nat.max_lub. apply Nat.le_refl.
  apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
  rewrite MaxVarTerm_var.
  apply Nat.max_lub. apply le_S, Nat.le_refl.
  apply le_S_n. apply (Nat.le_trans _ _ _ H). apply le_S, le_S, Nat.le_refl.
  apply SubstIsLproposition.
  apply SubstIsLproposition.
  apply SubstIsLproposition.
  apply SubstIsLproposition.
  apply fr_propprop. apply IsLterm_var. apply IsLterm_var.
  apply IsLterm_PAnat. apply IsLterm_PAnat.
  apply VarOccursFreeInFormula_SubstIdem.
  apply SubstIsLproposition.
  apply SubstIsLproposition.
  apply SubstIsLproposition.
  apply fr_propprop. apply IsLterm_var. apply IsLterm_var. apply IsLterm_PAnat.
  apply PAnat_closed. discriminate.
  apply PAnat_closed. apply PAnat_closed.
  apply IsLterm_PAnat.
  unfold Leq.
  rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2, Bool.andb_true_r.
  apply IsFreeForSubst_PAnat.
  rewrite IsLproposition_and, SubstIsLproposition, SubstIsLproposition.
  reflexivity.
  apply SubstIsLproposition. apply fr_propprop. apply IsLterm_var.
  apply IsLterm_var.
  apply SubstIsLproposition. apply SubstIsLproposition.
  apply fr_propprop. apply IsLterm_var. apply IsLterm_var.
  apply IsLterm_PAnat. discriminate.
  rewrite VarOccursInTerm_var.
  apply Nat.eqb_neq. intro abs. inversion abs.
  rewrite <- H2 in m4. apply le_S_n, le_S_n in m4. inversion m4.
  apply PAnat_closed. apply IsLterm_var.
  unfold Leq.
  rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2, Bool.andb_true_r.
  apply MaxVarFreeSubst_var.
  rewrite IsLproposition_and, SubstIsLproposition, SubstIsLproposition.
  reflexivity. apply fr_propprop. apply IsLterm_var.
  apply SubstIsLproposition. apply fr_propprop. apply IsLterm_var.
  apply IsLterm_PAnat.
  apply le_n_S. rewrite MaxVar_and. apply Nat.max_lub.
  apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)). 
  rewrite MaxVarTerm_PAnat.
  apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)). 
  apply Nat.max_lub. rewrite MaxVarTerm_var. apply Nat.le_refl.
  apply (Nat.le_trans _ (S (MaxVar prop))). apply le_S, Nat.le_refl. exact H.
  apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)). 
  apply Nat.max_lub. rewrite MaxVarTerm_var. apply Nat.le_refl.
  apply (Nat.le_trans _ (S (MaxVar prop))). apply le_S, Nat.le_refl. exact H.
  discriminate. rewrite VarOccursInTerm_var.
  apply Nat.eqb_neq. intro abs. 
  rewrite <- abs in m4. apply le_S_n, le_S_n, le_S_n in m4. inversion m4.
  apply PAnat_closed. apply IsLterm_var.
  unfold Leq.
  rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2, Bool.andb_true_r.
  apply MaxVarFreeSubst_var.
  rewrite IsLproposition_and, SubstIsLproposition.
  apply fr_propprop. apply fr_propprop. apply IsLterm_PAnat.
  rewrite MaxVar_and.
  refine (Nat.le_lt_trans _ _ _ _ H).
  apply Nat.max_lub. 2: apply Nat.le_refl.
  apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)). 
  rewrite MaxVarTerm_PAnat. apply Nat.le_refl.
Qed.

Lemma SubstPANatDoesNotOccurFree : forall f v w k,
    VarOccursFreeInFormula v f = false
    -> VarOccursFreeInFormula v (Subst (PAnat k) w f) = false.
Proof.
  intros.
  apply VarOccursFreeInFormula_SubstClosed. exact H.
  apply PAnat_closed.
Qed.

(* beta init and beta_rec_body work, which means the beta-sequence they
   produce is equal to nat_rec u. *)
Lemma beta_recurse : forall (u : nat -> nat -> nat) (j k i : nat)
    (urep : FunctionRepresented 2 u),
    let m := S (Nat.max (MaxVar (proj1_sig beta_repr_uniq)) (MaxVar urep)) in
    (k <= j)%nat ->
  IsProved IsWeakHeytingAxiom
    (Limplies
       (Land (Subst (PAnat i) 3 (Subst PAzero 2 (betast m)))
             (beta_rec_body m urep (PAnat j)))
       (Subst (PAnat (nat_rec (fun _ : nat => nat) i u k)) 3 (Subst (PAnat k) 2 (betast m)))).
Proof.
  induction k.
  - intros. simpl.
    apply LandElim1_impl.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply betast_IsLprop. apply IsLterm_const. apply IsLterm_PAnat.
    apply beta_rec_body_IsLprop. apply fr_propprop. apply IsLterm_PAnat.
  - intros. simpl.
    assert (VarOccursFreeInFormula (2 + m) (betast m) = false) as betast2free.
    { apply MaxVarDoesNotOccurFree.
      apply betast_IsLprop. apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_betast _)).
      apply Nat.max_lub. apply Nat.le_refl.
      apply le_S, le_S. apply Nat.le_max_l. } 
    assert (VarOccursFreeInFormula (3 + m) (betast m) = false) as betast3free.
    { apply MaxVarDoesNotOccurFree.
      apply betast_IsLprop. apply le_n_S, le_S.
      apply (Nat.le_trans _ _ _ (MaxVar_betast _)).
      apply Nat.max_lub. apply Nat.le_refl.
      apply le_S, le_S. apply Nat.le_max_l. } 
    assert (VarOccursFreeInFormula (4 + m) (betast m) = false) as betast4free.
    { apply MaxVarDoesNotOccurFree.
      apply betast_IsLprop. apply le_n_S, le_S, le_S.
      apply (Nat.le_trans _ _ _ (MaxVar_betast _)).
      apply Nat.max_lub. apply Nat.le_refl.
      apply le_S, le_S. apply Nat.le_max_l. } 
    assert (forall a b m, a + m =? b + m = (a=? b))%nat as cancelm.
    { intros. destruct (a =? b)%nat eqn:des.
      apply Nat.eqb_eq in des. subst b. apply Nat.eqb_refl.
      apply Nat.eqb_neq. intro abs. apply Nat.eqb_neq in des.
      apply Nat.add_cancel_r in abs. contradiction. }
    assert (4 <= m)%nat as m4.
    { destruct beta_repr_uniq; simpl in m.
      destruct (le_lt_dec 3%nat (MaxVar x)).
      apply le_n_S. apply (Nat.le_trans _ _ _ l). apply Nat.le_max_l.
      pose proof (MaxVarDoesNotOccurFree x (fr_propprop _ _ x) 3 l).
      pose proof (fr_freevar _ _ x).
      rewrite H1 in H0. discriminate H0. } 
    apply (LimpliesTrans
             _ _ (Land (beta_rec_body m urep (PAnat j))
                       (Subst (PAnat (nat_rec (fun _ : nat => nat) i u k)) 3
                              (Subst (PAnat k) 2 (betast m))))).
    apply LandIntroHyp.
    apply LandElim2_impl.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply betast_IsLprop. apply IsLterm_const. apply IsLterm_PAnat.
    apply beta_rec_body_IsLprop.
    apply fr_propprop. apply IsLterm_PAnat.
    apply IHk. apply (Nat.le_trans _ (S k)).
    apply le_S, Nat.le_refl. exact H.
    clear IHk. apply PushHypothesis.
    (* Last goal to prove the increment between k and S k. *)
    pose proof (beta_rec_body_IsLprop m urep (PAnat j)
                                      (fr_propprop _ _ urep) (IsLterm_PAnat j)) as H0.
    unfold beta_rec_body in H0. rewrite IsLproposition_forall in H0.
    refine (LimpliesTrans _ _ _ _ (LforallElim_impl _ _ _ (PAnat k) _ _ _) _).
    exact H0.
    apply IsLterm_PAnat.
    apply IsFreeForSubst_PAnat.
    exact H0. clear H0.
    (* Last goal, where beta_rec_body is instantiated. *)
    reduce_subst; rewrite cancelm, cancelm; simpl.
    rewrite Subst_PAle, SubstTerm_PAsucc, SubstTerm_PAnat, SubstTerm_var, Nat.eqb_refl.
    (* Substitute k for Lvar 2+m *)
    rewrite (SubstSubstDiffCommutes _ _ _ (PAnat k)).
    rewrite (SubstSubstNested _ (betast_IsLprop m)), SubstTerm_var, Nat.eqb_refl;
    fold (betast m).
    rewrite (SubstSubstDiffCommutes _ (2+m) 3).
    rewrite (SubstSubstNested
               _ (betast_IsLprop m) (PAnat k) (PAsucc (Lvar (S (S m)))) (2+m) 2)
    ; fold (betast m).
    rewrite SubstTerm_PAsucc, SubstTerm_var, Nat.eqb_refl.
    rewrite (SubstSubstDiffCommutes _ (2+m) 2).
    rewrite (SubstSubstDiffCommutes _ (2+m) 1).
    rewrite (SubstSubstNested _ (fr_propprop _ _ urep) _ _ (2+m) 0); fold (betast m).
    rewrite SubstTerm_var, Nat.eqb_refl.
    refine (LimpliesTrans _ _ _ _
                          (LimpliesElim_impl _ _ _ _ (PAle_normalize (S k) j H)) _).
    rewrite IsLproposition_exists, IsLproposition_exists.
    rewrite IsLproposition_and, SubstIsLproposition, IsLproposition_and.
    rewrite SubstIsLproposition. apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply fr_propprop.
    apply IsLterm_PAnat. apply IsLterm_var. apply IsLterm_var.
    apply SubstIsLproposition. apply betast_IsLprop.
    apply (IsLterm_PAnat (S k)).
    apply IsLterm_var.
    apply SubstIsLproposition. apply betast_IsLprop.
    apply IsLterm_PAnat. apply IsLterm_var.
    apply LexistsElim_impl.
    rewrite VarOccursFreeInFormula_implies.
    rewrite SubstPANatDoesNotOccurFree, SubstPANatDoesNotOccurFree. reflexivity.
    apply (SubstPANatDoesNotOccurFree _ _ _ (S k)).
    exact betast3free.
    apply SubstPANatDoesNotOccurFree. exact betast3free.
    apply LforallIntro.
    apply LexistsElim_impl.
    rewrite VarOccursFreeInFormula_implies.
    rewrite SubstPANatDoesNotOccurFree, SubstPANatDoesNotOccurFree. reflexivity.
    apply (SubstPANatDoesNotOccurFree _ _ _ (S k)).
    exact betast4free. apply SubstPANatDoesNotOccurFree. exact betast4free.
    apply LforallIntro.
    apply PullHypothesis.
    apply (LimpliesTrans _ _ (Land (Leq (Lvar (3 + m)) (PAnat (nat_rec (fun _ : nat => nat) i u k)))
                                   (Land (Subst (Lvar (4 + m)) 3 (Subst (PAsucc (PAnat k)) 2 (betast m)))
                (Subst (Lvar (4 + m)) 2
                   (Subst (Lvar (3 + m)) 1 (Subst (PAnat k) 0 urep)))) )).
    apply LandIntroHyp.
    refine (LimpliesTrans
              _ _ _ _ _ ((betast_uniq (3+m) (nat_rec (fun _ : nat => nat) i u k) k m) _ _)).
    apply LandIntroHyp.
    apply LandElim2_impl.
    rewrite IsLproposition_and, IsLproposition_and, SubstIsLproposition.
    rewrite SubstIsLproposition, SubstIsLproposition. reflexivity.
    apply SubstIsLproposition.
    apply SubstIsLproposition. apply fr_propprop.
    apply IsLterm_PAnat. apply IsLterm_var. apply IsLterm_var.
    apply SubstIsLproposition. apply betast_IsLprop.
    apply (IsLterm_PAnat (S k)).
    apply IsLterm_var.
    apply SubstIsLproposition. apply betast_IsLprop.
    apply IsLterm_PAnat. apply IsLterm_var.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply betast_IsLprop. apply IsLterm_PAnat. apply IsLterm_PAnat.
    apply DropSecondHypothesis.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply betast_IsLprop. apply IsLterm_PAnat. apply IsLterm_PAnat.
    apply LandElim1_impl.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply betast_IsLprop. apply IsLterm_PAnat. apply IsLterm_var.
    rewrite IsLproposition_and, SubstIsLproposition, SubstIsLproposition.
    reflexivity. apply SubstIsLproposition. apply SubstIsLproposition.
    apply fr_propprop. apply IsLterm_PAnat. apply IsLterm_var.
    apply IsLterm_var. apply SubstIsLproposition. apply betast_IsLprop.
    apply (IsLterm_PAnat (S k)).
    apply IsLterm_var.
    apply le_n_S, Nat.le_max_l.
    apply le_n_S, le_S, Nat.le_refl.
    apply DropSecondHypothesis.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply betast_IsLprop. apply IsLterm_PAnat. apply IsLterm_PAnat.
    apply LandElim2_impl.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply betast_IsLprop. apply IsLterm_PAnat. apply IsLterm_var.
    repeat (reduce_islproposition; rewrite SubstIsLproposition).
    reflexivity. reflexivity. reflexivity. apply fr_propprop.
    apply IsLterm_PAnat. apply IsLterm_var. apply IsLterm_var.
    reflexivity. apply betast_IsLprop. apply (IsLterm_PAnat (S k)).
    apply IsLterm_var.
    apply PushHypothesis.
    apply LeqElimSubstVarPAnat.
    repeat (reduce_islproposition; rewrite SubstIsLproposition).
    reflexivity. reflexivity. apply betast_IsLprop.
    apply (IsLterm_PAnat (S k)). apply IsLterm_PAnat.
    reflexivity. reflexivity. apply fr_propprop. apply IsLterm_PAnat.
    apply IsLterm_var. apply IsLterm_var. reflexivity.
    apply betast_IsLprop. apply (IsLterm_PAnat (S k)).
    apply IsLterm_var.
    rewrite Subst_implies, Subst_and.
    rewrite Subst_nosubst.
    rewrite (SubstSubstDiffCommutes _ (3+m) 2).
    assert (IsLproposition (Subst (PAnat k) 0 urep) = true).
    { apply SubstIsLproposition. apply fr_propprop. apply IsLterm_PAnat. }
    rewrite (SubstSubstNested _ H0), SubstTerm_var, Nat.eqb_refl.
    rewrite (Subst_nosubst _ (3+m)).
    apply (LimpliesTrans
             _ _ (Land (Leq (Lvar (4+m)) (PAnat (u k (nat_rec (fun _ : nat => nat) i u k))))
                       (Subst (Lvar (4 + m)) 3 (Subst (PAsucc (PAnat k)) 2 (betast m))))).
    apply LandIntroHyp.
    apply DropFirstHypothesis.
    apply SubstIsLproposition.
    apply SubstIsLproposition. apply betast_IsLprop.
    apply (IsLterm_PAnat (S k)). apply IsLterm_var.
    pose proof (fr_rep _ _ urep (ConsNat k (ConsNat (nat_rec (fun _ : nat => nat) i u k) NilNat))).
    simpl in H1. rewrite CoordTailNat, CoordConsHeadNat, CoordConsTailNat in H1.
    rewrite CoordConsHeadNat in H1.
    apply (LforallElim _ _ _ (Lvar (4+m))) in H1.
    rewrite Subst_equiv, Subst_eq, SubstTerm_var, Nat.eqb_refl, SubstTerm_PAnat in H1.
    apply LandElim1 in H1. exact H1.
    apply IsLterm_var.
    unfold Leq. rewrite IsFreeForSubst_equiv, IsFreeForSubst_rel2, Bool.andb_true_r.
    apply MaxVarFreeSubst_var.
    apply SubstIsLproposition.
    apply SubstIsLproposition. apply fr_propprop.
    apply IsLterm_PAnat. apply IsLterm_PAnat.
    apply le_n_S.
    apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
    rewrite MaxVarTerm_PAnat.
    apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
    rewrite MaxVarTerm_PAnat. do 4 apply le_S. apply Nat.le_max_r.
    apply LandElim1_impl.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply betast_IsLprop. apply (IsLterm_PAnat (S k)).
    apply IsLterm_var.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply fr_propprop. apply IsLterm_PAnat. apply IsLterm_PAnat.
    apply IsLterm_var.
    apply PushHypothesis.
    apply LeqElimSubstVar.
    repeat (reduce_islproposition; rewrite SubstIsLproposition).
    reflexivity. reflexivity. apply betast_IsLprop.
    apply (IsLterm_PAnat (S k)). apply IsLterm_PAnat.
    reflexivity. apply betast_IsLprop. apply (IsLterm_PAnat (S k)). 
    apply IsLterm_var.
    apply IsLterm_PAnat.
    apply IsFreeForSubst_PAnat.
    repeat (reduce_islproposition; rewrite SubstIsLproposition).
    reflexivity. reflexivity. apply betast_IsLprop.
    apply (IsLterm_PAnat (S k)). apply IsLterm_PAnat.
    reflexivity. apply betast_IsLprop. apply (IsLterm_PAnat (S k)). 
    apply IsLterm_var.
    rewrite Subst_implies.
    rewrite SubstSubstNested, SubstTerm_var, Nat.eqb_refl.
    rewrite (Subst_nosubst _ (4+m)).
    apply LimpliesRefl.
    apply SubstIsLproposition.
    apply SubstIsLproposition. apply betast_IsLprop.
    apply (IsLterm_PAnat (S k)). apply IsLterm_PAnat.
    rewrite SubstPANatDoesNotOccurFree. reflexivity.
    apply (SubstPANatDoesNotOccurFree _ _ _ (S k)).
    exact betast4free.
    apply SubstIsLproposition. apply betast_IsLprop. apply (IsLterm_PAnat (S k)).
    apply (SubstPANatDoesNotOccurFree _ _ _ (S k)).
    exact betast4free. 
    apply MaxVarFreeSubst_var.
    apply SubstIsLproposition. apply betast_IsLprop.
    apply (IsLterm_PAnat (S k)). apply le_n_S.
    apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
    change (PAsucc (PAnat k)) with (PAnat (S k)).
    rewrite MaxVarTerm_PAnat.
    apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
    apply Nat.max_lub. rewrite MaxVarTerm_var.
    apply le_n_S, le_S, le_S, Nat.le_refl.
    apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
    do 3 apply le_S.
    apply Nat.max_lub. rewrite MaxVarTerm_var. apply Nat.le_refl.
    apply le_S. apply Nat.le_max_l.
    apply SubstPANatDoesNotOccurFree.
    apply (SubstPANatDoesNotOccurFree _ _ _ (S k)).
    exact betast3free. 
    apply MaxVarDoesNotOccurFree.
    apply SubstIsLproposition. apply fr_propprop. apply IsLterm_PAnat.
    apply le_n_S.
    apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
    rewrite MaxVarTerm_PAnat. do 3 apply le_S. apply Nat.le_max_r.
    apply MaxVarFreeSubst_var.
    apply SubstIsLproposition. apply fr_propprop.
    apply IsLterm_PAnat.
    apply le_n_S, le_S, le_S, le_S.
    apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
    rewrite MaxVarTerm_PAnat. apply Nat.le_max_r.
    discriminate.
    apply PAnat_closed. rewrite VarOccursInTerm_var.
    rewrite cancelm. reflexivity.
    rewrite VarOccursFreeInFormula_SubstDiff.
    apply (SubstPANatDoesNotOccurFree _ _ _ (S k)).
    exact betast3free.
    apply SubstIsLproposition. apply betast_IsLprop.
    apply (IsLterm_PAnat (S k)).
    apply Nat.eqb_neq. reflexivity.
    rewrite VarOccursInTerm_var, cancelm. reflexivity.
    apply MaxVarDoesNotOccurFree. apply fr_propprop.
    apply le_n_S, le_S, le_S. apply Nat.le_max_r.
    apply MaxVarFreeSubst_var. apply fr_propprop.
    apply le_n_S, le_S, le_S. apply Nat.le_max_r.
    discriminate. apply PAnat_closed.
    rewrite VarOccursInTerm_var.
    change (2+m =? 3 + m = false)%nat.
    rewrite cancelm. reflexivity.
    discriminate. apply PAnat_closed.
    rewrite VarOccursInTerm_var.
    change (2+m =? 4 + m = false)%nat.
    rewrite cancelm. reflexivity. 
    exact betast2free.
    apply MaxVarFreeSubst.
    apply betast_IsLprop. intros.
    unfold PAsucc in H0.
    rewrite VarOccursInTerm_op1, VarOccursInTerm_var  in H0.
    apply Nat.eqb_eq in H0. rewrite H0.
    apply le_n_S.
    apply (Nat.le_trans _ _ _ (MaxVar_betast _)).
    apply Nat.max_lub. apply Nat.le_refl.
    apply le_S, le_S. apply Nat.le_max_l.
    apply Nat.eqb_neq. simpl.
    apply le_S_n in m4.
    apply Nat.eqb_neq. intro abs. rewrite abs in m4. inversion m4.
    apply PAnat_closed.
    rewrite VarOccursInTerm_var.
    change (S (S (S (S m)))) with (4+m)%nat. rewrite cancelm. reflexivity.
    exact betast2free.
    apply MaxVarFreeSubst_var. apply betast_IsLprop.
    apply le_n_S.
    apply (Nat.le_trans _ _ _ (MaxVar_betast _)).
    apply Nat.max_lub. apply Nat.le_refl.
    apply le_S, le_S. apply Nat.le_max_l.
    apply Nat.eqb_neq. simpl.
    apply le_S_n in m4.
    apply Nat.eqb_neq. intro abs. rewrite abs in m4. inversion m4.
    apply PAnat_closed.
    rewrite VarOccursInTerm_var.
    change (2+m =? 3 + m = false)%nat.
    rewrite cancelm. reflexivity.
Qed.

Lemma LexistsIntroPAnat : forall IsAxiom (f v t:nat),
    IsLproposition f = true
    -> IsProved IsAxiom (Subst (PAnat t) v f)
    -> IsProved IsAxiom (Lexists v f).
Proof.
  intros.
  apply (LexistsIntro _ _ _ (PAnat t)).
  apply IsLterm_PAnat. exact H.
  apply IsFreeForSubst_PAnat, H. exact H0.
Qed.

Lemma nat_rec_half : forall (u : nat -> nat -> nat)
    (urep : FunctionRepresented 2 u) i j,
  let m := S (Nat.max (MaxVar (proj1_sig beta_repr_uniq)) (MaxVar urep)) in
   IsProved IsWeakHeytingAxiom
    (Lexists m
       (Lexists (S m)
             (Land
                (Land
                   (Lexists (S (S m))
                      (Land (Leq (Lvar (S (S m))) (PAnat i))
                         (Subst (Lvar (S (S m))) 3 (Subst PAzero 2 (betast m)))))
                   (beta_rec_body m urep (PAnat j)))
                (Lexists (S (S m))
                   (Lexists (S (S (S m)))
                      (Land (Leq (Lvar (S (S m))) (PAnat j))
                         (Land (Leq (Lvar (S (S (S m)))) (PAnat (nat_rec (fun _ : nat => nat) i u j)))
                            (Subst (Lvar (S (S (S m)))) 3
                               (Subst (Lvar (S (S m))) 2 (betast m)))))))))).
Proof.
  intros.
  pose proof (BetaSeq (MapNat (nat_rec (fun _ : nat => nat) i u) (RangeNat 0 (S j)))) as [s H].
  rewrite LengthMapNat, LengthRangeNat in H.
  pose (fact
           (MaxSeq
              (ConsNat (S j)
                 (MapNat (nat_rec (fun _ : nat => nat) i u) (RangeNat 0 (S j))))
              (S (S j)))) as t.
  fold t in H. 
  apply (LexistsIntroPAnat _ _ _ s).
  reduce_islproposition. rewrite IsLterm_PAnat, SubstIsLproposition.
  rewrite beta_rec_body_IsLprop, IsLterm_PAnat, IsLterm_PAnat, SubstIsLproposition.
  reflexivity. apply SubstIsLproposition. apply betast_IsLprop.
  apply IsLterm_var. apply IsLterm_var. apply fr_propprop.
  apply IsLterm_PAnat.
  apply SubstIsLproposition. apply betast_IsLprop.
  apply IsLterm_const. apply IsLterm_var.
  assert (S m =? m = false)%nat as m1.
  { apply Nat.eqb_neq. intro abs. apply (Nat.lt_irrefl m).
    rewrite <- abs at 2. apply Nat.le_refl. }
  assert (S (S m) =? m = false)%nat as m2.
  { apply Nat.eqb_neq. intro abs. apply (Nat.lt_irrefl m).
    rewrite <- abs at 2. apply le_S, Nat.le_refl. }
  assert (S (S (S m)) =? m = false)%nat as m3.
  { apply Nat.eqb_neq. intro abs. apply (Nat.lt_irrefl m).
    rewrite <- abs at 2. apply le_S, le_S, Nat.le_refl. }
  assert (S (S (S (S m))) =? m = false)%nat as m4.
  { apply Nat.eqb_neq. intro abs. apply (Nat.lt_irrefl m).
    rewrite <- abs at 2. apply le_S, le_S, le_S, Nat.le_refl. }
  assert (4 <= m)%nat as fourlem.
  { apply le_n_S. apply (Nat.le_trans _ (MaxVar (proj1_sig beta_repr_uniq))).
    2: apply Nat.le_max_l.
    destruct (le_lt_dec 3 (MaxVar (proj1_sig beta_repr_uniq))). exact l. exfalso.
    pose proof (MaxVarDoesNotOccurFree
                  _ (fr_propprop _ _ (proj1_sig beta_repr_uniq)) 3 l).
    pose proof (fr_freevar _ _ (proj1_sig beta_repr_uniq)).
    rewrite H1 in H0. discriminate H0. } 
  assert (VarOccursFreeInFormula (2 + m) (betast m) = false) as m2free.
  { apply MaxVarDoesNotOccurFree. apply betast_IsLprop.
    apply le_n_S.
    apply (Nat.le_trans _ _ _ (MaxVar_betast _)).
    apply Nat.max_lub. apply Nat.le_refl. apply le_S, le_S, Nat.le_max_l. }
  rewrite Subst_exists, m1.
  reduce_subst; rewrite m2, m3.
  do 3 rewrite SubstTerm_PAnat.
  apply (LexistsIntroPAnat _ _ _ t).
  reduce_islproposition. rewrite IsLterm_PAnat, SubstIsLproposition.
  rewrite SubstIsLproposition, IsLterm_PAnat, IsLterm_PAnat.
  apply SubstIsLproposition. apply SubstIsLproposition.
  apply SubstIsLproposition. apply betast_IsLprop.
  apply IsLterm_var. apply IsLterm_var. apply IsLterm_PAnat.
  rewrite beta_rec_body_IsLprop. reflexivity. apply fr_propprop.
  apply IsLterm_PAnat. apply IsLterm_PAnat.
  apply SubstIsLproposition. apply SubstIsLproposition.
  apply betast_IsLprop. apply IsLterm_const. apply IsLterm_var.
  apply IsLterm_PAnat.
  reduce_subst.
  change (S (S m) =? S m)%nat with (S m =? m)%nat. rewrite m1.
  change (S (S (S m)) =? S m)%nat with (S (S m) =? m)%nat. rewrite m2.
  do 3 rewrite SubstTerm_PAnat.
  apply LandIntro.
  apply LandIntro.
  - apply (LexistsIntroPAnat _ _ _ i).
    reduce_islproposition. rewrite IsLterm_PAnat, SubstIsLproposition.
    reflexivity. apply SubstIsLproposition. apply SubstIsLproposition.
    apply SubstIsLproposition. apply betast_IsLprop. apply IsLterm_const.
    apply IsLterm_var. apply IsLterm_PAnat. apply IsLterm_PAnat.
    rewrite Subst_and, Subst_eq, SubstTerm_var, Nat.eqb_refl, SubstTerm_PAnat.
    apply LandIntro. apply LeqRefl. apply IsLterm_PAnat.
    specialize (H O).
    rewrite CoordMapNat, CoordRangeNat in H. simpl in H.
    rewrite SubstSubstDiffCommutes.
    rewrite (SubstSubstDiffCommutes _ (S (S m)) m).
    assert (IsLproposition (Subst PAzero 2 (betast m)) = true).
    { apply SubstIsLproposition. apply betast_IsLprop. apply IsLterm_const. }
    rewrite (SubstSubstNested _ H0), SubstTerm_var, Nat.eqb_refl.
    rewrite (SubstSubstDiffCommutes _ m 3).
    rewrite (SubstSubstDiffCommutes _ m 2).
    rewrite (SubstSubstDiffCommutes _ (S m) 3).
    rewrite (SubstSubstDiffCommutes _ (S m) 2).
    rewrite betast_SubstSubst.
    destruct beta_repr_uniq as [repr H1]; unfold proj1_sig.
    unfold proj1_sig in m. clear H1.
    pose proof (FormulaRepresents_alt
               _ _ _ (ConsNat s (ConsNat t (ConsNat 0 NilNat))) (fr_rep _ _ repr) (fr_propprop _ _ repr) i).
    simpl in H1.
    do 3 rewrite CoordTailNat in H1.
    rewrite CoordConsHeadNat in H1.
    do 3 rewrite CoordConsTailNat in H1.
    rewrite CoordConsHeadNat in H1.
    rewrite CoordConsHeadNat in H1.
    apply H1, H. apply le_n_S, le_0_n.
    apply le_n_S, Nat.le_max_l. apply (le_trans _ 4). auto. exact fourlem.
    intro abs. apply le_n_S in fourlem. rewrite abs in fourlem.
    apply le_S_n, le_S_n in fourlem. inversion fourlem.
    apply PAnat_closed. apply (PAnat_closed O).
    intro abs. apply le_n_S in fourlem. rewrite abs in fourlem.
    do 3 apply le_S_n in fourlem. inversion fourlem.
    apply PAnat_closed. apply PAnat_closed.
    intro abs. rewrite abs in fourlem.
    apply le_S_n, le_S_n in fourlem. inversion fourlem.
    apply PAnat_closed. apply (PAnat_closed O).
    intro abs. rewrite abs in fourlem.
    do 3 apply le_S_n in fourlem. inversion fourlem.
    apply PAnat_closed. apply PAnat_closed.
    apply VarOccursFreeInFormula_SubstClosed.
    exact m2free.
    apply (PAnat_closed O).
    apply MaxVarFreeSubst_var.
    apply SubstIsLproposition. apply betast_IsLprop. apply IsLterm_const.
    apply le_n_S.
    apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
    change PAzero with (PAnat O). rewrite (MaxVarTerm_PAnat 0).
    simpl.
    apply (Nat.le_trans _ _ _ (MaxVar_betast _)).
    apply Nat.max_lub. apply Nat.le_refl. apply le_S, le_S, Nat.le_max_l.
    apply Nat.eqb_neq, m2. apply PAnat_closed. apply PAnat_closed.
    apply Nat.eqb_neq, m1. apply PAnat_closed. apply PAnat_closed.
    apply le_n_S, le_0_n. rewrite LengthRangeNat.
    apply le_n_S, le_0_n.
  - unfold beta_rec_body.
    rewrite Subst_forall.
    change (2 + m =? m)%nat with (S (S m) =? m)%nat. rewrite m2.
    rewrite Subst_forall. change (2 + m =? S m)%nat with (S m =? m)%nat.
    rewrite m1, Subst_implies, Subst_PAle, SubstTerm_PAsucc. 
    apply LforallIntro.
    rewrite SubstTerm_var.
    change (2 + m =? m)%nat with (S (S m) =? m)%nat. rewrite m2, SubstTerm_PAnat.
    rewrite Subst_implies, Subst_PAle, SubstTerm_PAsucc, SubstTerm_PAnat. 
    rewrite SubstTerm_var.
    change (2 + m =? S m)%nat with (S m =? m)%nat. rewrite m1.
    apply LforallBounded_lt.
    repeat (reduce_islproposition; rewrite SubstIsLproposition); try reflexivity.
    apply fr_propprop. apply IsLterm_var. apply IsLterm_var.
    apply IsLterm_var. apply betast_IsLprop.
    unfold PAsucc. rewrite IsLterm_op1. apply IsLterm_var.
    apply IsLterm_var. apply betast_IsLprop. apply IsLterm_var.
    apply IsLterm_var. apply IsLterm_PAnat. apply IsLterm_PAnat.
    intros k H0.
    rewrite Subst_exists; simpl (3+m)%nat; rewrite m3.
    rewrite Subst_exists.
    change (S (S (S m)) =? S m)%nat with (S (S m) =? m)%nat; rewrite m2.
    rewrite Subst_exists.
    change (S (S (S m)) =? 2 + m)%nat with (S m =? m)%nat; rewrite m1.
    rewrite Subst_exists; simpl (4+m)%nat; rewrite m4.
    rewrite Subst_exists.
    change (S (S (S (S m))) =? S m)%nat with (S (S (S m)) =? m)%nat; rewrite m3.
    rewrite Subst_exists.
    change (S (S (S (S m))) =? 2 + m)%nat with (S (S m) =? m)%nat; rewrite m2.
    reduce_subst.
    apply (LexistsIntroPAnat _ _ _ (godel_beta s t k)).
    unfold PAsucc.
    repeat (reduce_islproposition; rewrite SubstIsLproposition); try reflexivity.
    apply fr_propprop. apply IsLterm_var. apply IsLterm_var.
    apply IsLterm_var. apply IsLterm_PAnat. apply IsLterm_PAnat.
    apply IsLterm_PAnat. apply betast_IsLprop.
    rewrite IsLterm_op1. apply IsLterm_var. apply IsLterm_var.
    apply IsLterm_PAnat. apply IsLterm_PAnat. apply IsLterm_PAnat.
    apply betast_IsLprop. apply IsLterm_var. apply IsLterm_var.
    apply IsLterm_PAnat. apply IsLterm_PAnat. apply IsLterm_PAnat.
    rewrite Subst_exists.
    change (S (S (S (S m))) =? S (S (S m)))%nat with (S m =? m)%nat; rewrite m1.
    apply (LexistsIntroPAnat _ _ _ (godel_beta s t (S k))).
    unfold PAsucc.
    repeat (reduce_islproposition; rewrite SubstIsLproposition); try reflexivity.
    apply fr_propprop. apply IsLterm_var. apply IsLterm_var.
    apply IsLterm_var. apply IsLterm_PAnat. apply IsLterm_PAnat.
    apply IsLterm_PAnat. apply betast_IsLprop.
    rewrite IsLterm_op1. apply IsLterm_var. apply IsLterm_var.
    apply IsLterm_PAnat. apply IsLterm_PAnat. apply IsLterm_PAnat.
    apply betast_IsLprop. apply IsLterm_var. apply IsLterm_var.
    apply IsLterm_PAnat. apply IsLterm_PAnat. apply IsLterm_PAnat.
    apply IsLterm_PAnat.
    rewrite Subst_and, Subst_and, Subst_and, Subst_and.
    apply LandIntro. 2: apply LandIntro.
    + rewrite (SubstSubstDiffCommutes _ m 3).
      rewrite (SubstSubstDiffCommutes _ m 2).
      rewrite (SubstSubstDiffCommutes _ (S m) 3).
      rewrite (SubstSubstDiffCommutes _ (S m) 2). 
      rewrite (SubstSubstDiffCommutes _ (2+m) 3).
      assert (IsLproposition (Subst (PAnat t) (S m) (Subst (PAnat s) m (betast m))) = true) as H1.
      { apply SubstIsLproposition. apply SubstIsLproposition.
        apply betast_IsLprop. apply IsLterm_PAnat. apply IsLterm_PAnat. }
      rewrite (SubstSubstNested _ H1), SubstTerm_var, Nat.eqb_refl. clear H1.
      rewrite Subst_nosubst, SubstSubstNested, SubstTerm_var, Nat.eqb_refl.
      unfold betast.
      rewrite betast_SubstSubst. 
      destruct beta_repr_uniq as [repr H1]; unfold proj1_sig. 
      unfold proj1_sig in m.
      pose proof (FormulaRepresents_alt
                    _ _ _ (ConsNat s (ConsNat t (ConsNat k NilNat))) (fr_rep _ _ repr) (fr_propprop _ _ repr) (godel_beta s t k)) as H2.
      simpl in H2.
      do 3 rewrite CoordTailNat in H2.
      rewrite CoordConsHeadNat in H2.
      do 3 rewrite CoordConsTailNat in H2.
      rewrite CoordConsHeadNat in H2.
      rewrite CoordConsHeadNat in H2.
      apply H2. reflexivity.
      apply le_n_S, Nat.le_max_l.
      refine (Nat.le_trans _ _ _ _ fourlem). auto.
      apply SubstIsLproposition.
      apply SubstIsLproposition.
      apply SubstIsLproposition.
      apply betast_IsLprop. apply IsLterm_PAnat.
      apply IsLterm_PAnat. apply IsLterm_PAnat.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply MaxVarDoesNotOccurFree. apply betast_IsLprop.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_betast _)), le_S.
      apply Nat.max_lub. apply Nat.le_refl. apply le_S, le_S, Nat.le_max_l.
      apply PAnat_closed. apply PAnat_closed. apply PAnat_closed.
      apply MaxVarFreeSubst_var.
      apply SubstIsLproposition. apply SubstIsLproposition.
      apply SubstIsLproposition.
      apply betast_IsLprop. apply IsLterm_PAnat. apply IsLterm_PAnat.
      apply IsLterm_PAnat.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_PAnat.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_PAnat.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_PAnat. simpl.
      apply (Nat.le_trans _ _ _ (MaxVar_betast _)), le_S.
      apply Nat.max_lub. apply Nat.le_refl. apply le_S, le_S, Nat.le_max_l.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply MaxVarDoesNotOccurFree. apply betast_IsLprop.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_betast _)), le_S, le_S.
      apply Nat.max_lub. apply Nat.le_refl. apply le_S, le_S, Nat.le_max_l.
      apply PAnat_closed. apply PAnat_closed. apply PAnat_closed.
      rewrite VarOccursInTerm_var. exact m1.
      apply PAnat_closed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply MaxVarDoesNotOccurFree. apply betast_IsLprop.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_betast _)).
      apply Nat.max_lub. apply Nat.le_refl. apply le_S, le_S, Nat.le_max_l.
      apply PAnat_closed. apply PAnat_closed.
      apply MaxVarFreeSubst_var.
      apply SubstIsLproposition. apply SubstIsLproposition.
      apply betast_IsLprop. apply IsLterm_PAnat. apply IsLterm_PAnat.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_PAnat.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_PAnat. simpl.
      apply (Nat.le_trans _ _ _ (MaxVar_betast _)).
      apply Nat.max_lub. apply Nat.le_refl. apply le_S, le_S, Nat.le_max_l.
      simpl. intro abs. apply le_n_S, le_n_S in fourlem.
      rewrite abs in fourlem. do 3 apply le_S_n in fourlem. inversion fourlem.
      apply PAnat_closed.
      rewrite VarOccursInTerm_var, Nat.eqb_sym. exact m1.
      intro abs. apply le_n_S in fourlem.
      rewrite abs in fourlem. do 2 apply le_S_n in fourlem. inversion fourlem.
      apply PAnat_closed.
      rewrite VarOccursInTerm_var, Nat.eqb_sym. exact m1.
      intro abs. apply le_n_S in fourlem.
      rewrite abs in fourlem. do 3 apply le_S_n in fourlem. inversion fourlem.
      apply PAnat_closed.
      rewrite VarOccursInTerm_var, Nat.eqb_sym. exact m2.
      intro abs. 
      rewrite abs in fourlem. do 2 apply le_S_n in fourlem. inversion fourlem.
      apply PAnat_closed.
      rewrite VarOccursInTerm_var, Nat.eqb_sym. exact m2.
      intro abs. 
      rewrite abs in fourlem. do 3 apply le_S_n in fourlem. inversion fourlem.
      apply PAnat_closed.
      rewrite VarOccursInTerm_var, Nat.eqb_sym. exact m3.
    + simpl.
      rewrite (SubstSubstDiffCommutes _ m 3).
      rewrite (SubstSubstDiffCommutes _ m 2).
      rewrite (SubstSubstDiffCommutes _ (S m) 3).
      rewrite (SubstSubstDiffCommutes _ (S m) 2). 
      rewrite (SubstSubstDiffCommutes _ (S (S m)) 3).
      assert (IsLproposition (Subst (PAnat t) (S m) (Subst (PAnat s) m (betast m))) = true) as H1.
      { apply SubstIsLproposition. apply SubstIsLproposition.
        apply betast_IsLprop. apply IsLterm_PAnat. apply IsLterm_PAnat. }
      rewrite (SubstSubstNested _ H1), SubstTerm_PAsucc, SubstTerm_var, Nat.eqb_refl.
      clear H1.
      rewrite SubstSubstDiffCommutes.
      assert (IsLproposition 
             (Subst (PAsucc (PAnat k)) 2
                (Subst (PAnat t) (S m) (Subst (PAnat s) m (betast m)))) = true).
      { apply SubstIsLproposition. apply SubstIsLproposition.
        apply SubstIsLproposition. apply betast_IsLprop. apply IsLterm_PAnat.
        apply IsLterm_PAnat. unfold PAsucc. rewrite IsLterm_op1. apply IsLterm_PAnat. }
      rewrite (SubstSubstNested _ H1), SubstTerm_var, Nat.eqb_refl. clear H1.
      rewrite Subst_nosubst.
      unfold betast.
      rewrite betast_SubstSubst.
      destruct beta_repr_uniq as [repr H1]; unfold proj1_sig. 
      unfold proj1_sig in m. clear H1.
      pose proof (FormulaRepresents_alt
                    _ _ _ (ConsNat s (ConsNat t (ConsNat (S k) NilNat)))
                    (fr_rep _ _ repr) (fr_propprop _ _ repr) (godel_beta s t (S k)))
        as [H1 _].
      simpl in H1.
      do 3 rewrite CoordTailNat in H1.
      rewrite CoordConsHeadNat in H1.
      do 3 rewrite CoordConsTailNat in H1.
      do 2 rewrite CoordConsHeadNat in H1.
      apply H1. reflexivity.
      apply le_n_S, Nat.le_max_l. 
      refine (Nat.le_trans _ _ _ _ fourlem). auto.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply MaxVarDoesNotOccurFree. apply betast_IsLprop.
      apply le_n_S, le_S.
      apply (Nat.le_trans _ _ _ (MaxVar_betast _)).
      apply Nat.max_lub. apply Nat.le_refl. apply le_S, le_S, Nat.le_max_l.
      apply PAnat_closed. apply PAnat_closed.
      unfold PAsucc. rewrite VarOccursInTerm_op1.
      apply PAnat_closed. apply PAnat_closed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply MaxVarDoesNotOccurFree. apply betast_IsLprop.
      apply le_n_S, le_S, le_S.
      apply (Nat.le_trans _ _ _ (MaxVar_betast _)).
      apply Nat.max_lub. apply Nat.le_refl. apply le_S, le_S, Nat.le_max_l.
      apply PAnat_closed. apply PAnat_closed.
      unfold PAsucc. rewrite VarOccursInTerm_op1. apply PAnat_closed.
      apply MaxVarFreeSubst_var.
      apply SubstIsLproposition.
      apply SubstIsLproposition.
      apply SubstIsLproposition. apply betast_IsLprop.
      apply IsLterm_PAnat. apply IsLterm_PAnat.
      unfold PAsucc. rewrite IsLterm_op1. apply IsLterm_PAnat.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      change (PAsucc (PAnat k)) with (PAnat (S k)).
      rewrite MaxVarTerm_PAnat.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_PAnat.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_PAnat. simpl.
      apply (Nat.le_trans _ _ _ (MaxVar_betast _)), le_S, le_S.
      apply Nat.max_lub. apply Nat.le_refl. apply le_S, le_S, Nat.le_max_l.
      apply Nat.eqb_neq. exact m1. apply PAnat_closed. apply PAnat_closed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply MaxVarDoesNotOccurFree. apply betast_IsLprop.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_betast _)).
      apply Nat.max_lub. apply Nat.le_refl. apply le_S, le_S, Nat.le_max_l.
      apply PAnat_closed. apply PAnat_closed.
      apply MaxVarFreeSubst.
      apply SubstIsLproposition.
      apply SubstIsLproposition.
      apply betast_IsLprop.
      apply IsLterm_PAnat. apply IsLterm_PAnat.
      intros w H2.
      unfold PAsucc in H2. rewrite VarOccursInTerm_op1, VarOccursInTerm_var in H2.
      apply Nat.eqb_eq in H2. subst w.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_PAnat.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_PAnat. simpl.
      apply (Nat.le_trans _ _ _ (MaxVar_betast _)).
      apply Nat.max_lub. apply Nat.le_refl. apply le_S, le_S, Nat.le_max_l.
      intro abs. apply le_n_S, le_n_S in fourlem.
      rewrite abs in fourlem. do 3 apply le_S_n in fourlem. inversion fourlem.
      apply PAnat_closed.
      rewrite VarOccursInTerm_var, Nat.eqb_sym. exact m2.
      intro abs. apply le_n_S in fourlem.
      rewrite abs in fourlem. do 2 apply le_S_n in fourlem. inversion fourlem.
      apply PAnat_closed. unfold PAsucc.
      rewrite VarOccursInTerm_op1, VarOccursInTerm_var, Nat.eqb_sym. exact m1.
      intro abs. apply le_n_S in fourlem.
      rewrite abs in fourlem. do 3 apply le_S_n in fourlem. inversion fourlem.
      apply PAnat_closed.
      rewrite VarOccursInTerm_var, Nat.eqb_sym. exact m3.
      intro abs.
      rewrite abs in fourlem. do 2 apply le_S_n in fourlem. inversion fourlem.
      apply PAnat_closed. unfold PAsucc.
      rewrite VarOccursInTerm_op1, VarOccursInTerm_var, Nat.eqb_sym. exact m2.
      intro abs.
      rewrite abs in fourlem. do 3 apply le_S_n in fourlem. inversion fourlem.
      apply PAnat_closed.
      rewrite VarOccursInTerm_var, Nat.eqb_sym. exact m4.
    + rewrite (Subst_nosubst _ m (PAnat s)).
      rewrite (Subst_nosubst _ (S m)).
      rewrite (SubstSubstDiffCommutes _ (2+m) 2).
      rewrite (SubstSubstDiffCommutes _ (2+m) 1).
      rewrite (SubstSubstNested _ (fr_propprop _ _ urep)), SubstTerm_var, Nat.eqb_refl.
      rewrite SubstSubstDiffCommutes.
      assert (IsLproposition (Subst (Lvar (S (S (S m)))) 1 (Subst (PAnat k) 0 urep)) = true).
      { apply SubstIsLproposition. apply SubstIsLproposition.
        apply fr_propprop. apply IsLterm_PAnat. apply IsLterm_var. }
      rewrite (SubstSubstNested _ H1), SubstTerm_var, Nat.eqb_refl. clear H1.
      rewrite SubstSubstDiffCommutes.
      assert (IsLproposition (Subst (PAnat k) 0 urep) = true).
      { apply SubstIsLproposition. apply fr_propprop. apply IsLterm_PAnat. }
      rewrite (SubstSubstNested _ H1), SubstTerm_var, Nat.eqb_refl. clear H1.
      rewrite (H (S k) (le_n_S _ _ H0)), CoordMapNat, CoordRangeNat. simpl.
      rewrite (H k), CoordMapNat, CoordRangeNat. simpl.
      pose proof (FormulaRepresents_alt
                    _ _ _ (ConsNat k (ConsNat (nat_rec (fun _ : nat => nat) i u k) NilNat))
                    (fr_rep _ _ urep) (fr_propprop _ _ urep)
                    (u k (nat_rec (fun _ : nat => nat) i u k)) ) as H2.
      simpl in H2.
      rewrite CoordTailNat in H2.
      rewrite CoordConsHeadNat in H2.
      rewrite CoordConsTailNat in H2.
      rewrite CoordConsHeadNat in H2.
      apply H2. reflexivity. apply le_S, H0.
      rewrite LengthRangeNat. apply le_S, H0. apply le_S, H0.
      apply le_n_S, H0. rewrite LengthRangeNat. apply le_n_S, H0.
      apply VarOccursFreeInFormula_SubstClosed.
      apply MaxVarDoesNotOccurFree. apply fr_propprop.
      apply le_n_S. apply le_S, le_S, le_S, Nat.le_max_r.
      apply PAnat_closed.
      apply MaxVarFreeSubst_var.
      apply SubstIsLproposition. apply fr_propprop. apply IsLterm_PAnat.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_PAnat.
      do 3 apply le_S. apply Nat.le_max_r. discriminate.
      apply PAnat_closed. apply PAnat_closed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply MaxVarDoesNotOccurFree.
      apply SubstIsLproposition. apply fr_propprop. apply IsLterm_PAnat.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_PAnat.
      do 4 apply le_S. apply Nat.le_max_r. 
      rewrite VarOccursInTerm_var. exact m1. 
      apply MaxVarFreeSubst_var.
      apply SubstIsLproposition.
      apply SubstIsLproposition. apply fr_propprop.
      apply IsLterm_PAnat. apply IsLterm_var.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      apply Nat.max_lub. rewrite MaxVarTerm_var. apply Nat.le_refl.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_PAnat.
      do 4 apply le_S. apply Nat.le_max_r.
      apply Nat.eqb_neq. exact m1.
      apply PAnat_closed. apply PAnat_closed.
      apply MaxVarDoesNotOccurFree. apply fr_propprop.
      apply le_n_S, le_S, le_S. apply Nat.le_max_r.
      apply MaxVarFreeSubst_var. apply fr_propprop.
      apply le_n_S, le_S, le_S, Nat.le_max_r.
      discriminate. apply PAnat_closed.
      rewrite VarOccursInTerm_var. rewrite Nat.eqb_sym. exact m1.
      discriminate. apply PAnat_closed.
      rewrite VarOccursInTerm_var. rewrite Nat.eqb_sym. exact m2.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply MaxVarDoesNotOccurFree. apply fr_propprop.
      apply le_n_S, le_S. apply Nat.le_max_r.
      rewrite VarOccursInTerm_var. rewrite Nat.eqb_sym. exact m1.
      rewrite VarOccursInTerm_var. rewrite Nat.eqb_sym. exact m2.
      rewrite VarOccursInTerm_var. rewrite Nat.eqb_sym. exact m3.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply MaxVarDoesNotOccurFree. apply fr_propprop.
      apply le_n_S. apply Nat.le_max_r.
      rewrite VarOccursInTerm_var. rewrite Nat.eqb_sym. exact m2.
      rewrite VarOccursInTerm_var. rewrite Nat.eqb_sym. exact m3.
      rewrite VarOccursInTerm_var. rewrite Nat.eqb_sym. exact m4.
  - apply (LexistsIntroPAnat _ _ _ j).
    reduce_islproposition. rewrite IsLterm_PAnat, SubstIsLproposition.
    rewrite IsLterm_PAnat. reflexivity. apply SubstIsLproposition.
    apply SubstIsLproposition. apply SubstIsLproposition.
    apply betast_IsLprop. apply IsLterm_var. apply IsLterm_var.
    apply IsLterm_PAnat. apply IsLterm_PAnat.
    rewrite Subst_exists.
    change (S (S (S m)) =? S (S m))%nat with (S m =? m)%nat; rewrite m1.
    rewrite Subst_and, Subst_eq, SubstTerm_var, Nat.eqb_refl, SubstTerm_PAnat.
    apply (LexistsIntroPAnat _ _ _ (nat_rec (fun _ : nat => nat) i u j)).
    reduce_islproposition. rewrite IsLterm_PAnat, SubstIsLproposition.
    reflexivity. reduce_islproposition.
    rewrite IsLterm_PAnat, SubstIsLproposition. reflexivity.
    apply SubstIsLproposition. apply SubstIsLproposition.
    apply SubstIsLproposition. apply betast_IsLprop.
    apply IsLterm_var. apply IsLterm_var.
    apply IsLterm_PAnat. apply IsLterm_PAnat. apply IsLterm_PAnat.
    rewrite Subst_and. apply LandIntro.
    rewrite Subst_eq, SubstTerm_PAnat. apply LeqRefl, IsLterm_PAnat.
    rewrite Subst_and, Subst_and. apply LandIntro.
    rewrite Subst_eq, SubstTerm_var.
    change (S (S (S m)) =? S (S m))%nat with (S m =? m)%nat; rewrite m1.
    rewrite SubstTerm_PAnat, Subst_eq, SubstTerm_PAnat, SubstTerm_var, Nat.eqb_refl.
    apply LeqRefl, IsLterm_PAnat.
    specialize (H j (Nat.le_refl _)).
    rewrite CoordMapNat, CoordRangeNat in H. simpl in H.
    2: apply Nat.le_refl. 2: rewrite LengthRangeNat; apply Nat.le_refl. 
    rewrite (SubstSubstDiffCommutes _ m 3).
    rewrite (SubstSubstDiffCommutes _ m 2).
    rewrite (SubstSubstDiffCommutes _ (S m) 3).
    rewrite (SubstSubstDiffCommutes _ (S m) 2).
    rewrite (SubstSubstDiffCommutes _ (S (S m)) 3).
    assert (IsLproposition (Subst (PAnat t) (S m) (Subst (PAnat s) m (betast m))) = true).
    { apply SubstIsLproposition. apply SubstIsLproposition.
      apply betast_IsLprop. apply IsLterm_PAnat. apply IsLterm_PAnat. }
    rewrite (SubstSubstNested _ H0), SubstTerm_var, Nat.eqb_refl. 
    rewrite SubstSubstNested, SubstTerm_var, Nat.eqb_refl. 
    rewrite betast_SubstSubst.
    destruct beta_repr_uniq as [repr H1]; unfold proj1_sig.
    unfold proj1_sig in m.
    pose proof (FormulaRepresents_alt
               _ _ _ (ConsNat s (ConsNat t (ConsNat j NilNat))) (fr_rep _ _ repr) (fr_propprop _ _ repr) (nat_rec (fun _ : nat => nat) i u j)).
    simpl in H2.
    do 3 rewrite CoordTailNat in H2.
    rewrite CoordConsHeadNat in H2.
    do 3 rewrite CoordConsTailNat in H2.
    rewrite CoordConsHeadNat in H2.
    rewrite CoordConsHeadNat in H2. 
    apply H2, H.
    apply le_n_S, Nat.le_max_l.
    apply (Nat.le_trans _ 4). auto. exact fourlem.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply SubstIsLproposition. apply betast_IsLprop.
    apply IsLterm_PAnat. apply IsLterm_PAnat. apply IsLterm_PAnat.
    apply VarOccursFreeInFormula_SubstClosed.
    apply VarOccursFreeInFormula_SubstClosed.
    apply VarOccursFreeInFormula_SubstClosed.
    apply MaxVarDoesNotOccurFree. apply betast_IsLprop.
    apply le_n_S.
    apply (Nat.le_trans _ _ _ (MaxVar_betast _)).
    apply le_S. apply Nat.max_lub. apply Nat.le_refl.
    apply le_S, le_S, Nat.le_max_l.
    apply PAnat_closed. apply PAnat_closed. apply PAnat_closed.
    apply MaxVarFreeSubst_var.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply SubstIsLproposition. apply betast_IsLprop.
    apply IsLterm_PAnat. apply IsLterm_PAnat. apply IsLterm_PAnat.
    apply le_n_S.
    apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
    rewrite MaxVarTerm_PAnat.
    apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
    rewrite MaxVarTerm_PAnat.
    apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
    rewrite MaxVarTerm_PAnat. simpl.
    apply (Nat.le_trans _ _ _ (MaxVar_betast _)).
    apply le_S. apply Nat.max_lub. apply Nat.le_refl.
    apply le_S, le_S, Nat.le_max_l. 
    apply VarOccursFreeInFormula_SubstClosed.
    apply VarOccursFreeInFormula_SubstClosed.
    exact m2free.
    apply PAnat_closed. apply PAnat_closed. 
    apply MaxVarFreeSubst_var.
    apply SubstIsLproposition.
    apply SubstIsLproposition.
    apply betast_IsLprop.
    apply IsLterm_PAnat. apply IsLterm_PAnat.
    apply le_n_S.
    apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
    rewrite MaxVarTerm_PAnat.
    apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
    rewrite MaxVarTerm_PAnat. simpl.
    apply (Nat.le_trans _ _ _ (MaxVar_betast _)).
    apply Nat.max_lub. apply Nat.le_refl.
    apply le_S, le_S, Nat.le_max_l. 
    intro abs. apply le_n_S, le_n_S in fourlem. rewrite abs in fourlem.
    apply le_S_n, le_S_n, le_S_n in fourlem. inversion fourlem.
    apply PAnat_closed. rewrite VarOccursInTerm_var, Nat.eqb_sym. exact m1.
    intro abs. apply le_n_S in fourlem. rewrite abs in fourlem.
    apply le_S_n, le_S_n in fourlem. inversion fourlem.
    apply PAnat_closed. rewrite VarOccursInTerm_var, Nat.eqb_sym. exact m1.
    intro abs. apply le_n_S in fourlem. rewrite abs in fourlem.
    apply le_S_n, le_S_n, le_S_n in fourlem. inversion fourlem.
    apply PAnat_closed. rewrite VarOccursInTerm_var, Nat.eqb_sym. exact m2.
    intro abs. apply le_n_S in fourlem. rewrite abs in fourlem.
    apply le_S_n, le_S_n, le_S_n in fourlem. inversion fourlem.
    apply PAnat_closed. rewrite VarOccursInTerm_var, Nat.eqb_sym. exact m2.
    intro abs. apply le_n_S in fourlem. rewrite abs in fourlem.
    do 4 apply le_S_n in fourlem. inversion fourlem.
    apply PAnat_closed. rewrite VarOccursInTerm_var, Nat.eqb_sym. exact m3. 
Qed.

Lemma nat_rec_repr : forall (u : nat -> nat -> nat),
    FunctionRepresented 2 u
    -> FunctionRepresented 2 (fun init => nat_rec (fun _ => nat) init u).
Proof.
  intros u urep.
  apply (Build_FunctionRepresented 2 _ (nat_rec_representation urep)).
  2: apply nat_rec_repr_IsLprop, fr_propprop.
  - intro args. apply LforallIntro. simpl.
    rewrite CoordTailNat.
    remember (CoordNat args 0) as i.
    remember (CoordNat args 1) as j.
    clear Heqj Heqi args.
    pose (S (Nat.max (MaxVar (proj1_sig beta_repr_uniq)) (MaxVar urep))) as m.
    assert (4 <= m)%nat.
    { apply le_n_S. apply (Nat.le_trans _ (MaxVar (proj1_sig beta_repr_uniq))).
      2: apply Nat.le_max_l.
      destruct (le_lt_dec 3 (MaxVar (proj1_sig beta_repr_uniq))). exact l. exfalso.
      pose proof (MaxVarDoesNotOccurFree
                    _ (fr_propprop _ _ (proj1_sig beta_repr_uniq)) 3 l).
      pose proof (fr_freevar _ _ (proj1_sig beta_repr_uniq)).
      rewrite H0 in H. discriminate H. }
    assert (m =? 0 = false)%nat as m0.
    { reflexivity. }
    assert (m =? 1 = false)%nat as m1.
    { apply Nat.eqb_neq. intro abs. rewrite abs in H.
      apply le_S_n in H. inversion H. }
    assert (m =? 2 = false)%nat as m2.
    { apply Nat.eqb_neq. intro abs. rewrite abs in H.
      apply le_S_n, le_S_n in H. inversion H. }
    assert (m =? 3 = false)%nat as m3.
    { apply Nat.eqb_neq. intro abs. rewrite abs in H.
      apply le_S_n, le_S_n, le_S_n in H. inversion H. }
    assert (S m =? 1 = false)%nat as m11.
    { apply Nat.eqb_neq. intro abs. inversion abs. }
    assert (VarOccursFreeInFormula (S (S m)) (betast m) = false) as m2free.
    { apply MaxVarDoesNotOccurFree.
      apply betast_IsLprop.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_betast _)).
      apply Nat.max_lub. apply Nat.le_refl. apply le_S, le_S, Nat.le_max_l. }
    unfold nat_rec_representation; fold m. simpl.
    reduce_subst; rewrite m0, m1; simpl.
    reduce_subst; rewrite m11; simpl.
    rewrite SubstTerm_PAnat.
    rewrite (Subst_nosubst (beta_rec_body m urep (Lvar 1)) 0).
    2: apply (beta_rec_body_vars _ _ 0 (le_0_n _)).
    2: apply fr_propprop.
    2: apply VarOccursInTerm_var.
    rewrite (beta_rec_body_subst_one urep); fold m.
    2: apply fr_propprop.
    rewrite (Subst_nosubst _ 0).
    rewrite (Subst_nosubst _ 0).
    rewrite (Subst_nosubst _ 1).
    rewrite (Subst_nosubst _ 1).
    apply LandIntro.
    + (* Remove the first 2 existentials *)
      apply LexistsElim_impl.
      unfold Leq. rewrite VarOccursFreeInFormula_rel2.
      rewrite VarOccursInTerm_var, m2, PAnat_closed. reflexivity.
      apply LforallIntro.
      apply LexistsElim_impl.
      unfold Leq. rewrite VarOccursFreeInFormula_rel2.
      rewrite VarOccursInTerm_var, PAnat_closed. 
      change (S m =? 2)%nat with (m =? 1)%nat. rewrite m1. reflexivity.
      apply LforallIntro.
      apply PushHypothesis, PushHypothesis.
      (* Replace the third existential by PAnat i *)
      apply (LimpliesTrans
               _ _ (Subst (PAnat i) 3 (Subst PAzero 2 (betast m)))).
      apply LexistsElim_impl.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      exact m2free.
      apply (PAnat_closed 0). apply PAnat_closed.
      apply LforallIntro.
      apply PushHypothesis.
      apply LeqElimSubstVarPAnat.
      rewrite IsLproposition_implies, SubstIsLproposition, SubstIsLproposition.
      reflexivity. apply SubstIsLproposition. apply betast_IsLprop.
      apply IsLterm_const. apply IsLterm_PAnat.
      apply SubstIsLproposition. apply betast_IsLprop.
      apply IsLterm_const. apply IsLterm_var.
      reduce_subst.
      rewrite SubstSubstNested, SubstTerm_var, Nat.eqb_refl.
      rewrite (Subst_nosubst _ (S (S m))).
      apply LimpliesRefl.
      apply SubstIsLproposition.
      apply SubstIsLproposition. apply betast_IsLprop.
      apply IsLterm_const. apply IsLterm_PAnat.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      exact m2free.
      apply (PAnat_closed 0). apply PAnat_closed.
      apply SubstIsLproposition. apply betast_IsLprop.
      apply IsLterm_const.
      apply VarOccursFreeInFormula_SubstClosed.
      exact m2free.
      apply (PAnat_closed 0). 
      apply MaxVarFreeSubst_var.
      apply SubstIsLproposition. apply betast_IsLprop.
      apply IsLterm_const.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      apply Nat.max_lub. change PAzero with (PAnat 0).
      rewrite MaxVarTerm_PAnat.
      apply le_0_n.
      apply (Nat.le_trans _ _ _ (MaxVar_betast _)).
      apply Nat.max_lub. apply Nat.le_refl. apply le_S, le_S, Nat.le_max_l.
      (* Now we have the hypothesis beta(s,t,0) = i.
         Use beta_recurse to deduce beta(s,t,j). *)
      apply PullHypothesis.
      apply (LimpliesTrans _ _ _ _ (beta_recurse u j j i urep (Nat.le_refl j)));
      fold m.
      (* Finish by removing Lvar 2. *)
      (* Remove first two existentials. *)
      apply PullHypothesis, CommuteHypotheses, PushHypothesis.
      apply LexistsElim_impl.
      unfold Leq.
      rewrite VarOccursFreeInFormula_implies, VarOccursFreeInFormula_rel2.
      rewrite VarOccursInTerm_var, PAnat_closed. simpl.
      rewrite Bool.orb_false_r.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      exact m2free. apply PAnat_closed. apply PAnat_closed.
      apply LforallIntro.
      apply LexistsElim_impl.
      unfold Leq.
      rewrite VarOccursFreeInFormula_implies, VarOccursFreeInFormula_rel2.
      rewrite VarOccursInTerm_var, PAnat_closed. simpl.
      rewrite Bool.orb_false_r.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      apply MaxVarDoesNotOccurFree.
      apply betast_IsLprop.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_betast _)).
      apply Nat.max_lub. apply le_S, Nat.le_refl.
      apply le_S, le_S, le_S, Nat.le_max_l.
      apply PAnat_closed. apply PAnat_closed.
      apply LforallIntro.
      (* Replace Lvar (S (S m)) by PAnat j *)
      apply PushHypothesis, LeqElimSubstVarPAnat.
      repeat (reduce_islproposition; rewrite SubstIsLproposition).
      rewrite IsLterm_PAnat. reflexivity. reflexivity.
      apply betast_IsLprop. apply IsLterm_PAnat. apply IsLterm_PAnat.
      reflexivity. apply betast_IsLprop. apply IsLterm_var. apply IsLterm_var.
      reduce_subst.
      replace (S (S (S m)) =? S (S m))%nat with false. simpl.
      rewrite SubstTerm_PAnat.
      rewrite SubstSubstDiffCommutes.
      rewrite (SubstSubstNested _ (betast_IsLprop _)).
      rewrite SubstTerm_var, Nat.eqb_refl.
      rewrite (Subst_nosubst _ (S (S m))).
      apply PushHypothesis.
      apply (LimpliesTrans _ _ (Leq (Lvar 2) (Lvar (S (S (S m)))))).
      apply LeqSym_impl. apply IsLterm_var. apply IsLterm_var.
      apply LeqElimSubstVar.
      repeat (reduce_islproposition; rewrite SubstIsLproposition).
      rewrite IsLterm_PAnat. reflexivity. reflexivity.
      apply betast_IsLprop. apply IsLterm_PAnat. apply IsLterm_PAnat.
      reflexivity.
      apply betast_IsLprop. 
      apply IsLterm_PAnat. apply IsLterm_var. apply IsLterm_var. 
      rewrite IsFreeForSubst_implies. apply andb_true_intro. split.
      apply IsFreeForSubst_nosubst.
      apply SubstIsLproposition.
      apply SubstIsLproposition.
      apply betast_IsLprop. apply IsLterm_PAnat. apply IsLterm_var.
      rewrite VarOccursFreeInFormula_SubstDiff, VarOccursFreeInFormula_SubstIdem.
      reflexivity. apply betast_IsLprop. apply PAnat_closed.
      apply SubstIsLproposition.
      apply betast_IsLprop. apply IsLterm_PAnat. discriminate.
      apply VarOccursInTerm_var.
      unfold Leq.
      rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2, Bool.andb_true_r.
      apply IsFreeForSubst_nosubst.
      apply SubstIsLproposition.
      apply SubstIsLproposition.
      apply betast_IsLprop. apply IsLterm_PAnat. apply IsLterm_PAnat.
      rewrite VarOccursFreeInFormula_SubstDiff, VarOccursFreeInFormula_SubstIdem.
      reflexivity. apply betast_IsLprop. apply PAnat_closed.
      apply SubstIsLproposition.
      apply betast_IsLprop. apply IsLterm_PAnat. discriminate.
      apply PAnat_closed.
      reduce_subst; simpl.
      rewrite SubstTerm_PAnat.
      rewrite Subst_nosubst.
      rewrite (Subst_nosubst _ 2 (Lvar (S (S (S m))))).
      unfold betast. destruct beta_repr_uniq as [repr i0]; simpl; simpl in m.
      apply PullHypothesis, CommuteHypotheses.
      specialize (i0 (nat_rec (fun _ : nat => nat) i u j)).
      apply LforallElimIdemVar, LforallElimIdemVar, LforallElimIdemVar in i0.
      apply (LforallIntro _ _ 0) in i0.
      apply (LforallElim _ _ _ (Lvar m)) in i0.
      rewrite Subst_implies, Subst_and, Subst_eq, SubstTerm_PAnat in i0.
      rewrite SubstTerm_var in i0. simpl in i0.
      rewrite SubstSubstDiffCommutes in i0.
      apply (LforallIntro _ _ 1) in i0.
      apply (LforallElim _ _ _ (Lvar (S m))) in i0.
      rewrite Subst_implies, Subst_and, Subst_eq, SubstTerm_PAnat in i0.
      rewrite SubstTerm_var in i0. simpl in i0.
      rewrite SubstSubstDiffCommutes in i0. 
      apply (LforallIntro _ _ 2) in i0.
      apply (LforallElim _ _ _ (PAnat j)) in i0.
      rewrite Subst_implies, Subst_and, Subst_eq, SubstTerm_PAnat in i0.
      rewrite SubstTerm_var in i0. simpl in i0.
      rewrite SubstSubstDiffCommutes in i0. 
      apply (LforallIntro _ _ 3) in i0.
      apply (LforallElim _ _ _ (Lvar (S (S (S m))))) in i0.
      rewrite Subst_implies, Subst_and, Subst_eq, SubstTerm_PAnat in i0.
      rewrite SubstTerm_var in i0. simpl in i0.
      rewrite Subst_nosubst in i0. 
      apply (LimpliesTrans _ _ _ _ i0).
      apply LeqSym_impl. apply IsLterm_PAnat. apply IsLterm_var.
      apply VarOccursFreeInFormula_SubstIdem.
      apply SubstIsLproposition.
      apply SubstIsLproposition.
      apply SubstIsLproposition. apply fr_propprop.
      apply IsLterm_var. apply IsLterm_var. apply IsLterm_PAnat.
      apply PAnat_closed.
      apply IsLterm_var.
      unfold Leq.
      rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2, Bool.andb_true_r.
      rewrite IsFreeForSubst_and. apply andb_true_intro. split.
      apply MaxVarFreeSubst_var.
      repeat (reduce_islproposition; rewrite SubstIsLproposition).
      reflexivity. reflexivity. reflexivity. reflexivity.
      apply fr_propprop. apply IsLterm_var. apply IsLterm_var.
      apply IsLterm_PAnat. apply IsLterm_PAnat.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_PAnat.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_PAnat.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_var. apply Nat.max_lub.
      apply le_S, Nat.le_refl.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_var. apply Nat.max_lub.
      apply le_S, le_S, Nat.le_refl.
      do 3 apply le_S. apply Nat.le_max_l. 
      apply MaxVarFreeSubst_var.
      repeat (reduce_islproposition; rewrite SubstIsLproposition).
      reflexivity. reflexivity. reflexivity.
      apply fr_propprop. apply IsLterm_var. apply IsLterm_var.
      apply IsLterm_PAnat.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_PAnat.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_var. apply Nat.max_lub.
      apply le_S, Nat.le_refl.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_var. apply Nat.max_lub.
      apply le_S, le_S, Nat.le_refl.
      do 3 apply le_S. apply Nat.le_max_l. 
      discriminate. apply PAnat_closed. apply PAnat_closed.
      apply IsLterm_PAnat. apply IsFreeForSubst_PAnat.
      repeat (reduce_islproposition; rewrite SubstIsLproposition).
      rewrite IsLterm_PAnat. reflexivity. reflexivity.
      apply fr_propprop. apply IsLterm_var. apply IsLterm_var.
      reflexivity. reflexivity. apply fr_propprop.
      apply IsLterm_var. apply IsLterm_var. apply IsLterm_PAnat.
      discriminate. rewrite VarOccursInTerm_var, Nat.eqb_sym. exact m2.
      apply PAnat_closed. apply IsLterm_var.
      unfold Leq.
      rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2, Bool.andb_true_r.
      rewrite IsFreeForSubst_and.
      apply andb_true_intro. split.
      apply MaxVarFreeSubst_var.
      apply SubstIsLproposition.
      apply SubstIsLproposition.
      apply fr_propprop. apply IsLterm_var.
      apply IsLterm_PAnat. apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_PAnat. 
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_var. apply Nat.max_lub. apply Nat.le_refl.
      apply le_S, Nat.le_max_l.
      apply MaxVarFreeSubst_var.
      apply SubstIsLproposition.
      apply fr_propprop. apply IsLterm_var.
      apply le_n_S. 
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_var. apply Nat.max_lub. apply Nat.le_refl.
      apply le_S, Nat.le_max_l.
      discriminate. rewrite VarOccursInTerm_var, Nat.eqb_sym. exact m3.
      apply PAnat_closed. apply IsLterm_var.
      unfold Leq.
      rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2, Bool.andb_true_r.
      rewrite IsFreeForSubst_and.
      apply andb_true_intro. split.
      apply MaxVarFreeSubst_var.
      apply SubstIsLproposition. apply fr_propprop.
      apply IsLterm_PAnat. apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      rewrite MaxVarTerm_PAnat. apply Nat.le_max_l.
      apply MaxVarFreeSubst_var.
      apply fr_propprop. apply le_n_S. apply Nat.le_max_l. 
      apply VarOccursFreeInFormula_SubstClosed.
      rewrite VarOccursFreeInFormula_SubstIdem. reflexivity.
      apply betast_IsLprop. apply PAnat_closed. apply PAnat_closed. 
      apply VarOccursFreeInFormula_SubstClosed.
      rewrite VarOccursFreeInFormula_SubstIdem. reflexivity.
      apply betast_IsLprop. apply PAnat_closed.
      apply VarOccursInTerm_var.
      apply VarOccursFreeInFormula_SubstClosed.
      apply VarOccursFreeInFormula_SubstClosed.
      exact m2free.
      apply PAnat_closed. apply PAnat_closed.
      exact m2free.
      apply MaxVarFreeSubst_var. apply betast_IsLprop.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_betast _)).
      apply Nat.max_lub. apply Nat.le_refl.
      apply le_S, le_S, Nat.le_max_l. 
      apply Nat.eqb_neq, m1.
      apply PAnat_closed.
      rewrite VarOccursInTerm_var. apply Nat.eqb_neq.
      intro abs. apply (Nat.lt_irrefl (S (S m))).
      rewrite abs at 2. apply Nat.le_refl.
      symmetry. apply Nat.eqb_neq. intro abs.
      apply (Nat.lt_irrefl (S (S m))).
      rewrite <- abs at 2. apply Nat.le_refl.
    + apply LeqElimSubstVarPAnat.
      repeat (reduce_islproposition; rewrite SubstIsLproposition).
      rewrite IsLterm_PAnat, IsLterm_PAnat.
      rewrite beta_rec_body_IsLprop. reflexivity.
      apply fr_propprop. apply IsLterm_PAnat. reflexivity.
      apply betast_IsLprop. apply IsLterm_var. apply IsLterm_var.
      reflexivity. apply betast_IsLprop. apply IsLterm_const.
      apply IsLterm_var.
      rewrite Subst_exists, m2.
      rewrite Subst_exists; change (S m =? 2)%nat with (m =? 1)%nat; rewrite m1.
      rewrite Subst_and, Subst_and, Subst_exists; simpl.
      rewrite Subst_and, Subst_eq, SubstTerm_var; simpl.
      rewrite SubstTerm_PAnat.
      rewrite (Subst_nosubst (beta_rec_body m urep (PAnat j))).
      2: exact (beta_rec_body_vars _ _ 2 (Nat.le_refl 2)
                                   (fr_propprop _ _ urep) (PAnat_closed _ _)).
      rewrite Subst_exists; simpl.
      rewrite Subst_exists; simpl.
      rewrite Subst_and, Subst_eq, SubstTerm_var; simpl.
      rewrite SubstTerm_PAnat, Subst_and, Subst_eq, SubstTerm_var; simpl.
      rewrite SubstTerm_var; simpl.
      rewrite SubstSubstDiffCommutes.
      2: discriminate. 2: apply PAnat_closed. 2: apply VarOccursInTerm_var.
      rewrite SubstSubstIdem.
      change PAzero with (PAnat 0). rewrite SubstTerm_PAnat.
      rewrite (SubstSubstDiffCommutes _ 2 3).
      rewrite SubstSubstIdem.
      rewrite SubstTerm_var; simpl. 
      apply nat_rec_half.
      discriminate. apply PAnat_closed.
      apply VarOccursInTerm_var.
    + rewrite VarOccursFreeInFormula_SubstDiff, VarOccursFreeInFormula_SubstDiff.
      apply betast_vars. apply Nat.eqb_neq.
      rewrite Nat.eqb_sym. exact m0. apply Nat.le_refl.
      apply betast_IsLprop. discriminate.
      rewrite VarOccursInTerm_var. reflexivity.
      apply SubstIsLproposition. apply betast_IsLprop. apply IsLterm_var.
      discriminate. rewrite VarOccursInTerm_var. reflexivity.
    + rewrite VarOccursFreeInFormula_SubstDiff, VarOccursFreeInFormula_SubstDiff.
      apply betast_vars. apply Nat.eqb_neq.
      rewrite Nat.eqb_sym. exact m0. apply Nat.le_refl.
      apply betast_IsLprop. discriminate.
      apply (PAnat_closed 0).
      apply SubstIsLproposition. apply betast_IsLprop. apply IsLterm_const.
      discriminate. rewrite VarOccursInTerm_var. reflexivity.
    + rewrite VarOccursFreeInFormula_SubstDiff, VarOccursFreeInFormula_SubstDiff.
      apply betast_vars. apply Nat.eqb_neq.
      rewrite Nat.eqb_sym. exact m0. apply le_0_n.
      apply betast_IsLprop. discriminate.
      rewrite VarOccursInTerm_var. reflexivity.
      apply SubstIsLproposition. apply betast_IsLprop. apply IsLterm_var.
      discriminate. unfold PAsucc. 
      rewrite VarOccursInTerm_var. reflexivity.
    + rewrite VarOccursFreeInFormula_SubstDiff, VarOccursFreeInFormula_SubstDiff.
      apply betast_vars. apply Nat.eqb_neq.
      rewrite Nat.eqb_sym. exact m0. apply le_0_n.
      apply betast_IsLprop. discriminate.
      apply (PAnat_closed 0).
      apply SubstIsLproposition. apply betast_IsLprop. apply IsLterm_const.
      discriminate.
      rewrite VarOccursInTerm_var. reflexivity.
  - intros. apply nat_rec_repr_vars. apply fr_propprop.
    exact H. intros. apply fr_vars. exact H0.
Qed.

