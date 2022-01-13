Require Import PeanoNat.
Require Import Numbers.NaryFunctions.
Require Import Arith.Wf_nat.
Require Import EnumSeqNat.
Require Import Formulas.
Require Import Substitutions.
Require Import IsFreeForSubst.
Require Import Proofs.
Require Import PeanoAxioms.
Require Import HeytingModel.
Require Import HeytingRepresentation.
Require Import BoolRepresented.
Require Import BetaRepr.
Require Import EnumSeqNat_repr.

Lemma Lnot_repr : FunctionRepresented 1 Lnot.
Proof.
  unfold Lnot.
  apply ComposeRepr_21.
  exact ConsNat_repr.
  apply (ConstantRepresented 1).
  apply ComposeRepr_21.
  exact ConsNat_repr.
  apply (proj_represented 1 0); auto.
  apply (ConstantRepresented 0).
Qed.

Lemma Land_repr : FunctionRepresented 2 Land.
Proof.
  unfold Land.
  apply ComposeRepr_22.
  exact ConsNat_repr.
  apply (ConstantRepresented LandHead).
  apply ComposeRepr_22.
  exact ConsNat_repr.
  apply (proj_represented 2 0); auto.
  apply ComposeRepr_22.
  exact ConsNat_repr.
  apply (proj_represented 2 1); auto.
  apply (ConstantRepresented 0).
Qed.

Lemma Lor_repr : FunctionRepresented 2 Lor.
Proof.
  unfold Lor.
  apply ComposeRepr_22.
  exact ConsNat_repr.
  apply (ConstantRepresented LorHead).
  apply ComposeRepr_22.
  exact ConsNat_repr.
  apply (proj_represented 2 0); auto.
  apply ComposeRepr_22.
  exact ConsNat_repr.
  apply (proj_represented 2 1); auto.
  apply (ConstantRepresented 0).
Qed.

Lemma Limplies_repr : FunctionRepresented 2 Limplies.
Proof.
  unfold Limplies.
  apply ComposeRepr_22.
  exact ConsNat_repr.
  apply (ConstantRepresented LimpliesHead).
  apply ComposeRepr_22.
  exact ConsNat_repr.
  apply (proj_represented 2 0); auto.
  apply ComposeRepr_22.
  exact ConsNat_repr.
  apply (proj_represented 2 1); auto.
  apply (ConstantRepresented 0).
Qed.

Lemma Lop_repr : FunctionRepresented 2 Lop.
Proof.
  unfold Lop.
  apply ComposeRepr_22.
  exact ConsNat_repr.
  apply (ConstantRepresented LopHead).
  exact ConsNat_repr.
Qed.

Lemma Lop1_repr : FunctionRepresented 2 Lop1.
Proof.
  unfold Lop1.
  apply ComposeRepr_22. exact Lop_repr.
  apply (proj_represented 2 0); auto.
  apply ComposeRepr_22. exact ConsNat_repr.
  apply (proj_represented 2 1); auto.
  apply (ConstantRepresented 0).
Qed.

Lemma Lop2_repr : FunctionRepresented 3 Lop2.
Proof.
  unfold Lop2.
  apply ComposeRepr_23. exact Lop_repr.
  apply (proj_represented 3 0); auto.
  apply ComposeRepr_23. exact ConsNat_repr.
  apply (proj_represented 3 1); auto.
  apply ComposeRepr_23. exact ConsNat_repr.
  apply (proj_represented 3 2); auto.
  apply (ConstantRepresented 0).
Qed.

Lemma Lrel_repr : FunctionRepresented 2 Lrel.
Proof.
  unfold Lrel.
  apply ComposeRepr_22.
  exact ConsNat_repr.
  apply (ConstantRepresented LrelHead).
  exact ConsNat_repr.
Qed.

Lemma Lrel2_repr : FunctionRepresented 3 Lrel2.
Proof.
  unfold Lrel2.
  apply ComposeRepr_23. exact Lrel_repr.
  apply (proj_represented 3 0); auto.
  apply ComposeRepr_23. exact ConsNat_repr.
  apply (proj_represented 3 1); auto.
  apply ComposeRepr_23. exact ConsNat_repr.
  apply (proj_represented 3 2); auto.
  apply (ConstantRepresented 0).
Qed. 

Lemma Leq_repr : FunctionRepresented 2 Leq.
Proof.
  unfold Leq.
  apply ComposeRepr_32. exact Lrel2_repr.
  apply (ConstantRepresented 0).
  apply (proj_represented 2 0); auto.
  apply (proj_represented 2 1); auto.
Qed.

Lemma Lvar_repr : FunctionRepresented 1 Lvar.
Proof.
  unfold Lvar.
  apply ComposeRepr_21.
  exact ConsNat_repr.
  apply (ConstantRepresented LvarHead).
  apply ComposeRepr_21.
  exact ConsNat_repr.
  apply (proj_represented 1 0); auto.
  apply (ConstantRepresented 0).
Qed.

Lemma Lexists_repr : FunctionRepresented 2 Lexists.
Proof.
  unfold Lexists.
  apply ComposeRepr_22.
  exact ConsNat_repr.
  apply (ConstantRepresented LexistsHead).
  apply ComposeRepr_22.
  exact ConsNat_repr.
  apply (proj_represented 2 0); auto.
  apply ComposeRepr_22.
  exact ConsNat_repr.
  apply (proj_represented 2 1); auto.
  apply (ConstantRepresented 0).
Qed. 

Lemma Lforall_repr : FunctionRepresented 2 Lforall.
Proof.
  unfold Lforall.
  apply ComposeRepr_22.
  exact ConsNat_repr.
  apply (ConstantRepresented LforallHead).
  apply ComposeRepr_22.
  exact ConsNat_repr.
  apply (proj_represented 2 0); auto.
  apply ComposeRepr_22.
  exact ConsNat_repr.
  apply (proj_represented 2 1); auto.
  apply (ConstantRepresented 0).
Qed. 

Lemma IsLvar_repr : FunctionRepresentedBool 1 IsLvar.
Proof.
  unfold IsLvar.
  apply (EqbRepresented 1).
  apply (proj_represented 1 0); auto.
  apply ComposeRepr_11.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ConstantRepresented LvarHead).
  apply (proj_represented 1 0); auto.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply ComposeRepr_21. exact CoordNat_repr.
  apply (proj_represented 1 0); auto.
  apply (ConstantRepresented 1).
  apply (ConstantRepresented 0).
Qed.

Lemma IsLnot_repr : FunctionRepresentedBool 1 IsLnot.
Proof.
  apply (EqbRepresented 1).
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply ComposeRepr_11.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ConstantRepresented 1).
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply ComposeRepr_21. exact CoordNat_repr.
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply (ConstantRepresented 1).
  apply (ConstantRepresented 0).
Qed.

Lemma IsLimplies_repr : FunctionRepresentedBool 1 IsLimplies.
Proof.
  apply (EqbRepresented 1).
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply ComposeRepr_11.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ConstantRepresented 2).
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply ComposeRepr_21. exact CoordNat_repr.
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply (ConstantRepresented 1).
  apply ComposeRepr_21. exact ConsNat_repr.
  apply ComposeRepr_21. exact CoordNat_repr.
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply (ConstantRepresented 2).
  apply (ConstantRepresented 0).
Qed.

Lemma IsLor_repr : FunctionRepresentedBool 1 IsLor.
Proof.
  apply (EqbRepresented 1).
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply ComposeRepr_11.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ConstantRepresented LorHead).
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply ComposeRepr_21. exact CoordNat_repr.
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply (ConstantRepresented 1).
  apply ComposeRepr_21. exact ConsNat_repr.
  apply ComposeRepr_21. exact CoordNat_repr.
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply (ConstantRepresented 2).
  apply (ConstantRepresented 0).
Qed.

Lemma IsLand_repr : FunctionRepresentedBool 1 IsLand.
Proof.
  apply (EqbRepresented 1).
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply ComposeRepr_11.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ConstantRepresented LandHead).
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply ComposeRepr_21. exact CoordNat_repr.
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply (ConstantRepresented 1).
  apply ComposeRepr_21. exact ConsNat_repr.
  apply ComposeRepr_21. exact CoordNat_repr.
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply (ConstantRepresented 2).
  apply (ConstantRepresented 0).
Qed.

Lemma IsLforall_repr : FunctionRepresentedBool 1 IsLforall.
Proof.
  apply (EqbRepresented 1).
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply ComposeRepr_11.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ConstantRepresented LforallHead).
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply ComposeRepr_21. exact CoordNat_repr.
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply (ConstantRepresented 1).
  apply ComposeRepr_21. exact ConsNat_repr.
  apply ComposeRepr_21. exact CoordNat_repr.
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply (ConstantRepresented 2).
  apply (ConstantRepresented 0).
Qed.

Lemma IsLexists_repr : FunctionRepresentedBool 1 IsLexists.
Proof.
  apply (EqbRepresented 1).
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply ComposeRepr_11.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ConstantRepresented LexistsHead).
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply ComposeRepr_21. exact CoordNat_repr.
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply (ConstantRepresented 1).
  apply ComposeRepr_21. exact ConsNat_repr.
  apply ComposeRepr_21. exact CoordNat_repr.
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply (ConstantRepresented 2).
  apply (ConstantRepresented 0).
Qed.

Lemma IsLrel_repr : FunctionRepresentedBool 1 IsLrel.
Proof.
  apply (EqbRepresented 1).
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply ComposeRepr_11.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ConstantRepresented LrelHead).
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply ComposeRepr_21. exact CoordNat_repr.
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply (ConstantRepresented 1).
  apply ComposeRepr_11; exact TailNat_repr.
Qed.

Lemma IsLopTerm_repr : FunctionRepresentedBool 2
    (fun term previousValues : nat =>
     IsLopTerm term (LengthNat term)
       (fun i : nat => CoordNat previousValues i =? 1)).
Proof.
  apply (FunctionRepresentedBool_ext
           2 (fun term previousValues =>
                Nat.leb 2 (LengthNat term)
                && AndNat (NthTailNat previousValues 2) (LengthNat term - 2))%bool).
  - apply (AndRepresented 2 (fun term _ => Nat.leb 2 (LengthNat term))
                          (fun term p => AndNat (NthTailNat p 2) (LengthNat term - 2))).
    apply (LebRepresented 2 (fun _ _ => 2) (fun t _ => LengthNat t)).
    apply (ConstantRepresented 2).
    apply ComposeRepr_12. exact LengthNat_repr.
    apply (proj_represented 2 0); auto.
    apply (ComposeRepr_22 (fun t p => if AndNat t p then 1 else 0)).
    exact AndNat_repr.
    apply ComposeRepr_12. exact TailNat_repr.
    apply ComposeRepr_12. exact TailNat_repr.
    apply (proj_represented 2 1); auto.
    apply ComposeRepr_22. exact SubtractionRepresented.
    apply ComposeRepr_12. exact LengthNat_repr.
    apply (proj_represented 2 0); auto.
    apply (ConstantRepresented 2).
  - intros [term [previousValues n0]].
    unfold nuncurry. clear n0.
    destruct (Nat.leb 2 (LengthNat term)) eqn:des.
    + apply Nat.leb_le in des. simpl.
      assert (forall i j : bool, ((i = true) <-> (j = true)) -> i = j).
      { intros. destruct i,j; try reflexivity.
        destruct H. symmetry. apply H. reflexivity.
        apply H. reflexivity. }
      apply H. clear H. rewrite AndNat_spec.
      rewrite IsLopTerm_spec.
      split.
      intros H. split. exact des. split. exact des.
      intros j H0. apply Nat.eqb_eq. specialize (H (j-2)).
      destruct H0. destruct j. exfalso; inversion H0.
      destruct j. exfalso. apply le_S_n in H0. inversion H0.
      simpl in H. rewrite Nat.sub_0_r in H.
      rewrite CoordTailNat, CoordTailNat in H. apply H.
      destruct (LengthNat term). inversion H1.
      destruct n. apply le_S_n in H1. inversion H1.
      simpl. rewrite Nat.sub_0_r. apply le_S_n, le_S_n in H1. exact H1.
      intros [_ [_ H]] k H0.
      rewrite CoordTailNat, CoordTailNat.
      apply Nat.eqb_eq, H. split.
      apply le_n_S, le_n_S, le_0_n.
      destruct (LengthNat term). inversion H0.
      destruct n. simpl in H0. inversion H0.
      simpl in H0. rewrite Nat.sub_0_r in H0.
      apply le_n_S, le_n_S. exact H0.
    + simpl. destruct (LengthNat term). reflexivity.
      destruct n. reflexivity.
      exfalso. discriminate des.
Qed.

Lemma IsLterm_repr : FunctionRepresentedBool 1 IsLterm.
Proof.
  apply TreeFoldNatBool_repr.
  unfold IsLtermRec.
  apply (FunctionRepresentedBool_ext
           2 (fun n previousValues : nat =>
                if CoordNat n 0 =? LopHead then
                  (IsLopTerm n (LengthNat n)
            (fun i : nat => CoordNat previousValues i =? 1) &&
          (NthTailNat n (LengthNat n) =? 0))%bool
                else if CoordNat n 0 =? LvarHead then
                       IsLvar n
                     else false)).
  apply (IfRepresentedBool 2 (fun i j => CoordNat i 0 =? LopHead)).
  apply (EqbRepresented 2).
  apply ComposeRepr_22. exact CoordNat_repr.
  apply (proj_represented 2 0); auto.
  apply (ConstantRepresented 0).
  apply (ConstantRepresented 8).
  apply (IfRepresentedBool 2
(fun currentStep previousValues : nat =>
      IsLopTerm currentStep (LengthNat currentStep)
                (fun i : nat => CoordNat previousValues i =? 1))
        (fun currentStep previousValues => NthTailNat currentStep (LengthNat currentStep) =? 0)).
  exact IsLopTerm_repr.
  apply (EqbRepresented 2 (fun currentStep _ : nat => NthTailNat currentStep (LengthNat currentStep))).
  apply ComposeRepr_22. exact NthTailNat_repr.
  apply (proj_represented 2 0); auto.
  apply ComposeRepr_12. exact LengthNat_repr.
  apply (proj_represented 2 0); auto.
  apply (ConstantRepresented 0).
  apply (ConstantRepresented 0).
  apply (IfRepresentedBool 2 (fun currentStep _ : nat => CoordNat currentStep 0 =? 9)
                           (fun currentStep _ => IsLvar currentStep)).
  apply (EqbRepresented 2).
  apply ComposeRepr_22. exact CoordNat_repr.
  apply (proj_represented 2 0); auto.
  apply (ConstantRepresented 0).
  apply (ConstantRepresented 9).
  unfold FunctionRepresentedBool. simpl.
  apply (ComposeRepr_12 (fun a => if IsLvar a then 1 else 0)).
  exact IsLvar_repr.
  apply (proj_represented 2 0); auto.
  apply (ConstantRepresented 0).
  intros. destruct x, n0. simpl.
  destruct (CoordNat n 0). reflexivity. clear n1.
  destruct n2. reflexivity.
  destruct n2. reflexivity.
  destruct n2. reflexivity.
  destruct n2. reflexivity.
  destruct n2. reflexivity.
  destruct n2. reflexivity.
  destruct n2. reflexivity.
  destruct n2. reflexivity.
  destruct n2. reflexivity.
  reflexivity.
  intros i r s H. unfold IsLtermRec.
  destruct (CoordNat i 0). reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n.
  2: destruct n; reflexivity.
  destruct (NthTailNat i (LengthNat i) =? 0).
  2: rewrite Bool.andb_false_r, Bool.andb_false_r; reflexivity.
  rewrite Bool.andb_true_r, Bool.andb_true_r.
  pose proof (IsLopTerm_spec (LengthNat i) i r).
  pose proof (IsLopTerm_spec (LengthNat i) i s).
  destruct (IsLopTerm i (LengthNat i) r).
  symmetry. apply H1.
  destruct H0 as [H0 _]. specialize (H0 eq_refl) as [H0 H2].
  split. exact H0. split. exact H0.
  intros j H3. rewrite <- H. apply H2, H3.  apply H3.
  destruct (IsLopTerm i (LengthNat i) s). 2: reflexivity.
  apply H0.
  destruct H1 as [H1 _]. specialize (H1 eq_refl) as [H1 H2].
  split. exact H1. split. exact H1.
  intros j H3. rewrite H. apply H2, H3. apply H3.
Qed.

Lemma IsLproposition_repr : FunctionRepresentedBool 1 IsLproposition.
Proof.
  apply TreeFoldNatBool_repr.
  - unfold IsLpropositionRec.
    apply (FunctionRepresentedBool_ext
           2 (fun n p : nat =>
                if CoordNat n 0 =? LnotHead then
                  IsLnot n && (CoordNat p 1 =? 1)
                else if CoordNat n 0 =? LimpliesHead then
                       IsLimplies n && (CoordNat p 1 =? 1)
                       && (CoordNat p 2 =? 1)
                else if CoordNat n 0 =? LorHead then
                       IsLor n && (CoordNat p 1 =? 1)
                       && (CoordNat p 2 =? 1)
                else if CoordNat n 0 =? LandHead then
                       IsLand n && (CoordNat p 1 =? 1)
                       && (CoordNat p 2 =? 1)
                else if CoordNat n 0 =? LforallHead then
                       IsLforall n && (CoordNat p 2 =? 1)
                else if CoordNat n 0 =? LexistsHead then
                       IsLexists n && (CoordNat p 2 =? 1)
                else if CoordNat n 0 =? LrelHead then
                       IsLrel n && IsLterm (Lop 0 (TailNat (TailNat n)))
                else
                  false)%bool).
    + apply (IfRepresentedBool 2 (fun n _ => CoordNat n 0 =? 1)
                               (fun n p => IsLnot n && (CoordNat p 1 =? 1)))%bool.
      apply (EqbRepresented 2).
      apply ComposeRepr_22. exact CoordNat_repr.
      apply (proj_represented 2 0); auto.
      apply (ConstantRepresented 0).
      apply (ConstantRepresented 1).
      apply (AndRepresented 2 (fun n _ => IsLnot n) (fun _ p => CoordNat p 1 =? 1)).
      apply (ComposeRepr_12 (fun n => if IsLnot n then 1 else 0)).
      exact IsLnot_repr.
      apply (proj_represented 2 0); auto.
      apply (EqbRepresented 2).
      apply ComposeRepr_22. exact CoordNat_repr.
      apply (proj_represented 2 1); auto.
      apply (ConstantRepresented 1).
      apply (ConstantRepresented 1).
      apply (IfRepresentedBool 2 (fun n _ => CoordNat n 0 =? 2)
                               (fun n p => (IsLimplies n && (CoordNat p 1 =? 1) && (CoordNat p 2 =? 1))))%bool.
      apply (EqbRepresented 2).
      apply ComposeRepr_22. exact CoordNat_repr.
      apply (proj_represented 2 0); auto.
      apply (ConstantRepresented 0).
      apply (ConstantRepresented 2).
      apply (AndRepresented 2 (fun n p => IsLimplies n && (CoordNat p 1 =? 1))
                            (fun n p => CoordNat p 2 =? 1))%bool.
      apply (AndRepresented 2 (fun n p => IsLimplies n)
                            (fun n p => CoordNat p 1 =? 1)).
      apply (ComposeRepr_12 (fun n => if IsLimplies n then 1 else 0)).
      exact IsLimplies_repr.
      apply (proj_represented 2 0); auto.
      apply (EqbRepresented 2).
      apply ComposeRepr_22. exact CoordNat_repr.
      apply (proj_represented 2 1); auto.
      apply (ConstantRepresented 1).
      apply (ConstantRepresented 1).
      apply (EqbRepresented 2).
      apply ComposeRepr_22. exact CoordNat_repr.
      apply (proj_represented 2 1); auto.
      apply (ConstantRepresented 2).
      apply (ConstantRepresented 1).
      apply (IfRepresentedBool 2 (fun n _ => CoordNat n 0 =? LorHead)
                               (fun n p => (IsLor n && (CoordNat p 1 =? 1) && (CoordNat p 2 =? 1))))%bool.
      apply (EqbRepresented 2).
      apply ComposeRepr_22. exact CoordNat_repr.
      apply (proj_represented 2 0); auto.
      apply (ConstantRepresented 0).
      apply (ConstantRepresented LorHead).
      apply (AndRepresented 2 (fun n p => IsLor n && (CoordNat p 1 =? 1))
                            (fun n p => CoordNat p 2 =? 1))%bool.
      apply (AndRepresented 2 (fun n p => IsLor n)
                            (fun n p => CoordNat p 1 =? 1)).
      apply (ComposeRepr_12 (fun n => if IsLor n then 1 else 0)).
      exact IsLor_repr.
      apply (proj_represented 2 0); auto.
      apply (EqbRepresented 2).
      apply ComposeRepr_22. exact CoordNat_repr.
      apply (proj_represented 2 1); auto.
      apply (ConstantRepresented 1).
      apply (ConstantRepresented 1).
      apply (EqbRepresented 2).
      apply ComposeRepr_22. exact CoordNat_repr.
      apply (proj_represented 2 1); auto.
      apply (ConstantRepresented 2).
      apply (ConstantRepresented 1).
      apply (IfRepresentedBool 2 (fun n _ => CoordNat n 0 =? LandHead)
                               (fun n p => (IsLand n && (CoordNat p 1 =? 1) && (CoordNat p 2 =? 1))))%bool.
      apply (EqbRepresented 2).
      apply ComposeRepr_22. exact CoordNat_repr.
      apply (proj_represented 2 0); auto.
      apply (ConstantRepresented 0).
      apply (ConstantRepresented LandHead).
      apply (AndRepresented 2 (fun n p => IsLand n && (CoordNat p 1 =? 1))
                            (fun n p => CoordNat p 2 =? 1))%bool.
      apply (AndRepresented 2 (fun n p => IsLand n)
                            (fun n p => CoordNat p 1 =? 1)).
      apply (ComposeRepr_12 (fun n => if IsLand n then 1 else 0)).
      exact IsLand_repr.
      apply (proj_represented 2 0); auto.
      apply (EqbRepresented 2).
      apply ComposeRepr_22. exact CoordNat_repr.
      apply (proj_represented 2 1); auto.
      apply (ConstantRepresented 1).
      apply (ConstantRepresented 1).
      apply (EqbRepresented 2).
      apply ComposeRepr_22. exact CoordNat_repr.
      apply (proj_represented 2 1); auto.
      apply (ConstantRepresented 2).
      apply (ConstantRepresented 1).
      apply (IfRepresentedBool 2 (fun n _ => CoordNat n 0 =? LforallHead)
                               (fun n p => (IsLforall n && (CoordNat p 2 =? 1))))%bool.
      apply (EqbRepresented 2).
      apply ComposeRepr_22. exact CoordNat_repr.
      apply (proj_represented 2 0); auto.
      apply (ConstantRepresented 0).
      apply (ConstantRepresented LforallHead).
      apply (AndRepresented 2 (fun n p => IsLforall n)
                            (fun n p => CoordNat p 2 =? 1))%bool.
      apply (ComposeRepr_12 (fun n => if IsLforall n then 1 else 0)).
      exact IsLforall_repr.
      apply (proj_represented 2 0); auto.
      apply (EqbRepresented 2).
      apply ComposeRepr_22. exact CoordNat_repr.
      apply (proj_represented 2 1); auto.
      apply (ConstantRepresented 2).
      apply (ConstantRepresented 1).
      apply (IfRepresentedBool 2 (fun n _ => CoordNat n 0 =? LexistsHead)
                               (fun n p => (IsLexists n && (CoordNat p 2 =? 1))))%bool.
      apply (EqbRepresented 2).
      apply ComposeRepr_22. exact CoordNat_repr.
      apply (proj_represented 2 0); auto.
      apply (ConstantRepresented 0).
      apply (ConstantRepresented LexistsHead).
      apply (AndRepresented 2 (fun n p => IsLexists n)
                            (fun n p => CoordNat p 2 =? 1))%bool.
      apply (ComposeRepr_12 (fun n => if IsLexists n then 1 else 0)).
      exact IsLexists_repr.
      apply (proj_represented 2 0); auto.
      apply (EqbRepresented 2).
      apply ComposeRepr_22. exact CoordNat_repr.
      apply (proj_represented 2 1); auto.
      apply (ConstantRepresented 2).
      apply (ConstantRepresented 1).
      apply (IfRepresentedBool 2 (fun n _ => CoordNat n 0 =? LrelHead)
                               (fun n p => (IsLrel n && IsLterm (Lop 0 (TailNat (TailNat n))))))%bool.
      apply (EqbRepresented 2).
      apply ComposeRepr_22. exact CoordNat_repr.
      apply (proj_represented 2 0); auto.
      apply (ConstantRepresented 0).
      apply (ConstantRepresented LrelHead).
      apply (AndRepresented 2 (fun n p => IsLrel n)
                            (fun n p => IsLterm (Lop 0 (TailNat (TailNat n)))))%bool.
      apply (ComposeRepr_12 (fun n => if IsLrel n then 1 else 0)).
      exact IsLrel_repr.
      apply (proj_represented 2 0); auto.
      apply (ComposeRepr_12 (fun n => if IsLterm n then 1 else 0)).
      exact IsLterm_repr.
      apply ComposeRepr_22.
      exact Lop_repr.
      apply (ConstantRepresented 0).
      apply ComposeRepr_12. exact TailNat_repr.
      apply ComposeRepr_12. exact TailNat_repr.
      apply (proj_represented 2 0); auto.
      apply (ConstantRepresented 0).
    + intros [n [p n0]]. simpl. clear n0.
      destruct (CoordNat n 0) eqn:des. reflexivity.
      destruct n0. reflexivity.
      destruct n0. reflexivity.
      destruct n0. reflexivity.
      destruct n0. reflexivity.
      destruct n0. reflexivity.
      destruct n0. reflexivity.
      destruct n0; reflexivity.
  - intros. unfold IsLpropositionRec.
    destruct (CoordNat n 0) eqn:des. reflexivity.
    destruct n0.
    destruct (IsLnot n) eqn:isnot. 2: reflexivity.
    rewrite H. reflexivity.
    apply Nat.eqb_eq in isnot.
    rewrite isnot, LengthLnot. apply Nat.le_refl.
    destruct n0.
    destruct (IsLimplies n) eqn:isimplies. 2: reflexivity.
    apply Nat.eqb_eq in isimplies.
    rewrite H, H. reflexivity.
    rewrite isimplies, LengthLimplies. apply Nat.le_refl.
    rewrite isimplies, LengthLimplies. auto.
    destruct n0.
    destruct (IsLor n) eqn:isimplies. 2: reflexivity.
    apply Nat.eqb_eq in isimplies.
    rewrite H, H. reflexivity.
    rewrite isimplies, LengthLor. apply Nat.le_refl.
    rewrite isimplies, LengthLor. auto.
    destruct n0.
    destruct (IsLand n) eqn:isimplies. 2: reflexivity.
    apply Nat.eqb_eq in isimplies.
    rewrite H, H. reflexivity.
    rewrite isimplies, LengthLand. apply Nat.le_refl.
    rewrite isimplies, LengthLand. auto.
    destruct n0.
    destruct (IsLforall n) eqn:isimplies. 2: reflexivity.
    apply Nat.eqb_eq in isimplies.
    rewrite H. reflexivity.
    rewrite isimplies, LengthLforall. apply Nat.le_refl.
    destruct n0.
    destruct (IsLexists n) eqn:isimplies. 2: reflexivity.
    apply Nat.eqb_eq in isimplies.
    rewrite H. reflexivity.
    rewrite isimplies, LengthLexists. apply Nat.le_refl.
    destruct n0; reflexivity.
Qed.

Lemma RangeNat_repr : FunctionRepresented 2 RangeNat.
Proof.
  pose (fun start currentStep val
        => ConcatNat val (ConsNat (currentStep+start) NilNat)) as f.
  apply (FunctionRepresented_2_ext (fun start => nat_rec (fun _ => nat) NilNat (f start))).
  - apply (ComposeRepr_32 (fun param init => nat_rec (fun _ => nat) init (f param))).
    apply nat_rec_param_repr.
    unfold f.
    apply ComposeRepr_23. exact ConcatNat_repr.
    apply (proj_represented 3 2); auto.
    apply ComposeRepr_23. exact ConsNat_repr.
    apply ComposeRepr_23. exact AdditionRepresented.
    apply (proj_represented 3 1); auto.
    apply (proj_represented 3 0); auto.
    apply (ConstantRepresented 0).
    apply (proj_represented 2 0); auto.
    apply (ConstantRepresented 0).
    apply (proj_represented 2 1); auto.
  - intro start. induction k. reflexivity.
    simpl. rewrite IHk. clear IHk.
    unfold f.
    apply TruncatedEqNat.
    rewrite LengthConcatNat, LengthRangeNat, LengthConsNat, LengthConsNat.
    rewrite LengthRangeNat, Nat.add_comm. reflexivity.
    rewrite LengthConcatNat, NthTailConcatNat.
    rewrite LengthConsNat, LengthConsNat, LengthRangeNat.
    change (LengthNat NilNat) with 0.
    simpl. rewrite TailConsNat, TailConsNat.
    rewrite RangeNatTruncated. reflexivity.
    intros i H.
    rewrite LengthConcatNat, LengthRangeNat, LengthConsNat in H.
    rewrite Nat.add_comm in H.
    change (LengthNat NilNat) with 0 in H. simpl in H.
    change (ConsNat start (RangeNat (S start) k)) with (RangeNat start (S k)).
    apply Nat.le_succ_r in H. destruct H.
    rewrite CoordConcatNatFirst. 
    rewrite CoordRangeNat, CoordRangeNat. reflexivity.
    apply le_n_S. apply (Nat.le_trans _ (S i)).
    apply le_S, Nat.le_refl. exact H. exact H.
    rewrite LengthRangeNat. exact H.
    inversion H. subst k.
    replace i with (0+LengthNat (RangeNat start i)) at 3.
    rewrite CoordConcatNatSecond.
    rewrite CoordConsHeadNat, CoordRangeNat, Nat.add_comm. reflexivity.
    apply Nat.le_refl. rewrite LengthRangeNat. reflexivity.
Qed.
 
Lemma SubstLopTerm_repr : FunctionRepresented 2
    (fun n previousValues : nat =>
     Lop (CoordNat n 1)
         (MapNat (CoordNat previousValues) (RangeNat 2 (LengthNat n - 2)))).
Proof.
  apply ComposeRepr_22. exact Lop_repr.
  apply ComposeRepr_22. exact CoordNat_repr.
  apply (proj_represented 2 0); auto.
  apply (ConstantRepresented 1).
  apply (ComposeRepr_22 (fun n => MapNat (CoordNat n))
                       (fun u v => v)
                            (fun u v => RangeNat 2 (LengthNat u - 2))).
  apply MapNat_repr. exact CoordNat_repr.
  apply (proj_represented 2 1). auto.
  apply ComposeRepr_22. exact RangeNat_repr.
  apply (ConstantRepresented 2).
  apply ComposeRepr_22. exact SubtractionRepresented.
  apply ComposeRepr_12. exact LengthNat_repr.
  apply (proj_represented 2 0). auto.
  apply (ConstantRepresented 2).
Qed.

Lemma SubstTerm_repr : FunctionRepresented 3 SubstTerm.
Proof.
  apply (FunctionRepresented_3_ext
           (@ncompose 2 3
                      (fun param => TreeFoldNat (SubstTermRec (diagX param) (diagY param)) O)
                      (fun k => match k with
                             | O => fun u v f => diagMerge u v
                             | _ => fun u v f => f
                             end))).
  - apply ComposeRepr_n.
    apply TreeFoldNat_repr_2.
    + unfold SubstTermRec.
      apply (FunctionRepresented_3_ext
               (fun param n previousValues =>
                  if CoordNat n 0 =? LopHead then
                    Lop (CoordNat n 1)
                        (MapNat (CoordNat previousValues) (RangeNat 2 (LengthNat n - 2)))
                  else if CoordNat n 0 =? LvarHead then
                         if CoordNat n 1 =? diagY param then diagX param else n
                       else 0)).
      apply (IfRepresented 3 (fun param n previousValues => CoordNat n 0 =? LopHead)
                           (fun _ n previousValues => Lop (CoordNat n 1)
                        (MapNat (CoordNat previousValues) (RangeNat 2 (LengthNat n - 2))))).
      apply (EqbRepresented 3).
      apply ComposeRepr_23. exact CoordNat_repr.
      apply (proj_represented 3 1); auto.
      apply (ConstantRepresented 0).
      apply (ConstantRepresented LopHead).
      apply (ComposeRepr_23
               (fun n previousValues : nat =>
Lop (CoordNat n 1)
       (MapNat (CoordNat previousValues) (RangeNat 2 (LengthNat n - 2))))).
      exact SubstLopTerm_repr.
      apply (proj_represented 3 1); auto.
      apply (proj_represented 3 2); auto.
      apply (IfRepresented 3 (fun param n _ => CoordNat n 0 =? LvarHead)).
      apply (EqbRepresented 3).
      apply ComposeRepr_23. exact CoordNat_repr.
      apply (proj_represented 3 1); auto.
      apply (ConstantRepresented 0).
      apply (ConstantRepresented LvarHead).
      apply (IfRepresented 3 (fun param n _ => CoordNat n 1 =? diagY param)).
      apply (EqbRepresented 3).
      apply ComposeRepr_23. exact CoordNat_repr.
      apply (proj_represented 3 1); auto.
      apply (ConstantRepresented 1).
      apply ComposeRepr_13. exact diagY_repr.
      apply (proj_represented 3 0); auto.
      apply ComposeRepr_13. exact diagX_repr.
      apply (proj_represented 3 0); auto.
      apply (proj_represented 3 1); auto.
      apply (ConstantRepresented 0).
      intros i j k. simpl.
      destruct (CoordNat j 0). reflexivity.
      destruct n. reflexivity.
      destruct n. reflexivity.
      destruct n. reflexivity.
      destruct n. reflexivity.
      destruct n. reflexivity.
      destruct n. reflexivity.
      destruct n. reflexivity.
      destruct n. reflexivity.
      destruct n. reflexivity.
      reflexivity.
    + intros. unfold SubstTermRec.
      destruct (CoordNat n 0). reflexivity.
      destruct n0. reflexivity.
      destruct n0. reflexivity.
      destruct n0. reflexivity.
      destruct n0. reflexivity.
      destruct n0. reflexivity.
      destruct n0. reflexivity.
      destruct n0. reflexivity.
      destruct n0. 2: reflexivity.
      apply f_equal.
      apply MapNatExt. intros. rewrite LengthRangeNat in H0.
      rewrite H. reflexivity.
      rewrite CoordRangeNat. 2: exact H0.
      destruct (LengthNat n). simpl in H0. inversion H0.
      destruct n0. simpl in H0. inversion H0.
      simpl. simpl in H0. rewrite Nat.sub_0_r in H0.
      apply le_n_S, le_n_S. exact H0.
    + intros [|k].
      apply ComposeRepr_23. exact diagMerge_repr.
      apply (proj_represented 3 0); auto.
      apply (proj_represented 3 1); auto.
      apply (proj_represented 3 2); auto.
  - intros u v t. simpl. rewrite diagYMergeId, diagXMergeId. reflexivity.
Qed.

Lemma strangeDiag_repr : forall v : nat,
    FunctionRepresented 3
    (fun i j k : nat => diagY (CoordNat k (diagMerge i (CoordNat j v)))).
Proof.
  intro v.
  apply ComposeRepr_13. exact diagY_repr.
  apply ComposeRepr_23. exact CoordNat_repr.
  apply (proj_represented 3 2); auto.
  apply ComposeRepr_23. exact diagMerge_repr.
  apply (proj_represented 3 0); auto.
  apply ComposeRepr_23. exact CoordNat_repr.
  apply (proj_represented 3 1); auto.
  apply (ConstantRepresented v).
Qed.

Lemma SubstTerms_repr : FunctionRepresented 3 (fun i j k => MapNat (SubstTerm i j) k).
Proof.
  apply (FunctionRepresented_3_ext
           (@ncompose 2 3
                      (fun i_j k => MapNat (SubstTerm (diagX i_j) (diagY i_j)) k)
                      (fun k => match k with
                             | O => fun i j k => diagMerge i j
                             | _ => fun i j k => k
                             end))).
  - apply ComposeRepr_n.
    apply MapNat_repr.
    apply ComposeRepr_32. exact SubstTerm_repr.
    apply ComposeRepr_12. exact diagX_repr.
    apply (proj_represented 2 0); auto.
    apply ComposeRepr_12. exact diagY_repr.
    apply (proj_represented 2 0); auto.
    apply (proj_represented 2 1); auto.
    intros [|k].
    apply ComposeRepr_23. exact diagMerge_repr.
    apply (proj_represented 3 0); auto.
    apply (proj_represented 3 1); auto.
    apply (proj_represented 3 2); auto. 
  - intros. simpl. rewrite diagXMergeId, diagYMergeId. reflexivity.
Qed.
  
Lemma Subst_repr : FunctionRepresented 3 Subst.
Proof.
  apply (FunctionRepresented_3_ext
           (@ncompose 2 3
                      (fun param => TreeFoldNat (SubstRec (diagX param) (diagY param)) O)
                      (fun k => match k with
                             | O => fun u v f => diagMerge u v
                             | _ => fun u v f => f
                             end))).
  2: intros u v t; simpl; rewrite diagYMergeId, diagXMergeId; reflexivity.
  apply ComposeRepr_n.
  apply TreeFoldNat_repr_2_ill_formed.
  - unfold SubstRec.
    apply (FunctionRepresented_3_ext
             (fun param n k =>
                if CoordNat n 0 =? LnotHead then
                  Lnot (diagY (CoordNat k (diagMerge param (CoordNat n 1))))
                else if CoordNat n 0 =? LimpliesHead then
                  Limplies (diagY (CoordNat k (diagMerge param (CoordNat n 1))))
                           (diagY (CoordNat k (diagMerge param (CoordNat n 2))))
                else if CoordNat n 0 =? LorHead then
                  Lor (diagY (CoordNat k (diagMerge param (CoordNat n 1))))
                      (diagY (CoordNat k (diagMerge param (CoordNat n 2))))
                else if CoordNat n 0 =? LandHead then
                  Land (diagY (CoordNat k (diagMerge param (CoordNat n 1))))
                       (diagY (CoordNat k (diagMerge param (CoordNat n 2))))
                else if CoordNat n 0 =? LforallHead then
                  Lforall (CoordNat n 1)
                          (if CoordNat n 1 =? diagY param
                           then CoordNat n 2
                           else diagY (CoordNat k (diagMerge param (CoordNat n 2))))
                else if CoordNat n 0 =? LexistsHead then
                  Lexists (CoordNat n 1)
                          (if CoordNat n 1 =? diagY param
                           then CoordNat n 2
                           else diagY (CoordNat k (diagMerge param (CoordNat n 2))))
                else if CoordNat n 0 =? LrelHead then
                  Lrel (CoordNat n 1)
                       (MapNat (SubstTerm (diagX param) (diagY param)) (TailNat (TailNat n)))
                else 0)).
    apply (IfRepresented 3 (fun p n pr => CoordNat n 0 =? LnotHead)).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 1).
    apply ComposeRepr_23. exact ConsNat_repr.
    apply (ConstantRepresented 1).
    apply ComposeRepr_23. exact ConsNat_repr.
    apply strangeDiag_repr.
    apply (ConstantRepresented 0).
    apply (IfRepresented 3 (fun p n pr => CoordNat n 0 =? LimpliesHead)).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 2).
    apply ComposeRepr_23. exact ConsNat_repr.
    apply (ConstantRepresented 2).
    apply ComposeRepr_23. exact ConsNat_repr.
    apply strangeDiag_repr.
    apply ComposeRepr_23. exact ConsNat_repr.
    apply strangeDiag_repr.
    apply (ConstantRepresented 0).
    apply (IfRepresented 3 (fun p n pr => CoordNat n 0 =? LorHead)).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 3).
    apply ComposeRepr_23. exact ConsNat_repr.
    apply (ConstantRepresented 3).
    apply ComposeRepr_23. exact ConsNat_repr.
    apply strangeDiag_repr.
    apply ComposeRepr_23. exact ConsNat_repr.
    apply strangeDiag_repr.
    apply (ConstantRepresented 0).
    apply (IfRepresented 3 (fun p n pr => CoordNat n 0 =? LandHead)).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 4).
    apply ComposeRepr_23. exact ConsNat_repr.
    apply (ConstantRepresented 4).
    apply ComposeRepr_23. exact ConsNat_repr.
    apply strangeDiag_repr.
    apply ComposeRepr_23. exact ConsNat_repr.
    apply strangeDiag_repr.
    apply (ConstantRepresented 0). 
    apply (IfRepresented 3 (fun p n pr => CoordNat n 0 =? LforallHead)).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 5).
    apply ComposeRepr_23. exact ConsNat_repr.
    apply (ConstantRepresented 5).
    apply ComposeRepr_23. exact ConsNat_repr.
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1). 
    apply ComposeRepr_23. exact ConsNat_repr.
    apply (IfRepresented 3 (fun i j k => CoordNat j 1 =? diagY i)).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1). 
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 0); auto.
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 2). 
    apply strangeDiag_repr.
    apply (ConstantRepresented 0). 
    apply (IfRepresented 3 (fun p n pr => CoordNat n 0 =? LexistsHead)).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 6).
    apply ComposeRepr_23. exact ConsNat_repr.
    apply (ConstantRepresented 6).
    apply ComposeRepr_23. exact ConsNat_repr.
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1). 
    apply ComposeRepr_23. exact ConsNat_repr.
    apply (IfRepresented 3 (fun i j k => CoordNat j 1 =? diagY i)).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1). 
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 0); auto.
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 2). 
    apply strangeDiag_repr.
    apply (ConstantRepresented 0). 
    apply (IfRepresented 3 (fun p n pr => CoordNat n 0 =? LrelHead)).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 7).
    apply ComposeRepr_23. exact ConsNat_repr.
    apply (ConstantRepresented 7).
    apply ComposeRepr_23. exact ConsNat_repr.
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1).
    apply (ComposeRepr_33 _ _ _ _ SubstTerms_repr).
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 0); auto.
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 0); auto.
    apply ComposeRepr_13. exact TailNat_repr.
    apply ComposeRepr_13. exact TailNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0). 
    intros i j k. unfold SubstRec.
    destruct (CoordNat j 0). reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    reflexivity.
  - intros. unfold SubstRec.
    destruct (CoordNat n 0). reflexivity.
    destruct n0. rewrite H. reflexivity.
    destruct n0. rewrite H, H. reflexivity.
    destruct n0. rewrite H, H. reflexivity.
    destruct n0. rewrite H, H. reflexivity.
    destruct n0. rewrite H. reflexivity.
    destruct n0. rewrite H. reflexivity.
    destruct n0; reflexivity.
  - intros [|k].
    apply ComposeRepr_23. exact diagMerge_repr.
    apply (proj_represented 3 0); auto.
    apply (proj_represented 3 1); auto.
    apply (proj_represented 3 2); auto. 
Qed. 
Opaque Subst.

Lemma VarOccursInTerm_repr
  : FunctionRepresentedBool 2 VarOccursInTerm.
Proof.
  unfold FunctionRepresentedBool, VarOccursInTerm.
  simpl.
  apply (IfRepresented 2 (fun i j => negb (SubstTerm 0 i j =? j))).
  apply (NegRepresented 2).
  apply (EqbRepresented 2).
  apply ComposeRepr_32. exact SubstTerm_repr.
  apply (ConstantRepresented 0).
  apply (proj_represented 2 0); auto.
  apply (proj_represented 2 1); auto.
  apply (proj_represented 2 1); auto.
  apply (ConstantRepresented 1).
  apply (ConstantRepresented 0).
Qed. 

Lemma VarOccursFreeInFormula_repr
  : FunctionRepresentedBool 2 VarOccursFreeInFormula.
Proof.
  unfold FunctionRepresentedBool, VarOccursFreeInFormula.
  simpl.
  apply (IfRepresented 2 (fun i j => negb (Subst 0 i j =? j))).
  apply (NegRepresented 2).
  apply (EqbRepresented 2).
  apply ComposeRepr_32. exact Subst_repr.
  apply (ConstantRepresented 0).
  apply (proj_represented 2 0); auto.
  apply (proj_represented 2 1); auto.
  apply (proj_represented 2 1); auto.
  apply (ConstantRepresented 1).
  apply (ConstantRepresented 0).
Qed. 

Definition IsFreeForSubstRecNat (u v f : nat) (rec : nat -> nat) : nat :=
  match CoordNat f 0 with
  | LnotHead => rec 1
  | LimpliesHead
  | LorHead
  | LandHead => if rec 1 =? 1 then rec 2 else 0
  | LforallHead
  | LexistsHead => if negb (VarOccursFreeInFormula v f)  (* no substitutions *)
                  then 1 else (if negb (VarOccursInTerm (CoordNat f 1) u)
                               then rec 2 else 0)
  | LrelHead
  | LopHead
  | LvarHead => 1
  | _ => 0
  end.
Definition IsFreeForSubstNat (u v : nat) : nat -> nat
  := TreeFoldNat (IsFreeForSubstRecNat u v) O.

Lemma IsFreeForSubstNat_step : forall u v f,
    TreeFoldNat (IsFreeForSubstRecNat u v) O f
    = TreeFoldNatRec (IsFreeForSubstRecNat u v) O f (fun k _ => IsFreeForSubstNat u v k).
Proof.
  intros.
  unfold IsFreeForSubstNat, TreeFoldNat. rewrite Fix_eq.
  reflexivity.
  intros. unfold IsFreeForSubstRecNat, TreeFoldNatRec.
  destruct (Compare_dec.le_lt_dec (LengthNat x) 0). reflexivity.
  destruct (CoordNat x 0). reflexivity.
  destruct n. rewrite H. reflexivity.
  destruct n. rewrite H, H. reflexivity.
  destruct n. rewrite H, H. reflexivity.
  destruct n. rewrite H, H. reflexivity.
  destruct n. rewrite H. reflexivity.
  destruct n. rewrite H. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n; reflexivity.
Qed.

Lemma IsFreeForSubst_repr : FunctionRepresentedBool 3 IsFreeForSubst.
Proof.
  apply (FunctionRepresented_3_ext
           (@ncompose 2 3
                      (fun param => TreeFoldNat (IsFreeForSubstRecNat (diagX param) (diagY param)) O)
                      (fun k => match k with
                             | O => fun u v f => diagMerge u v
                             | _ => fun u v f => f
                             end))).
  - apply ComposeRepr_n.
    apply TreeFoldNat_repr_2_ill_formed. 
    unfold IsFreeForSubstRecNat.
    apply (FunctionRepresented_3_ext
             (fun param n k =>
                if CoordNat n 0 =? LnotHead then
                  diagY (CoordNat k (diagMerge param (CoordNat n 1)))
                else if CoordNat n 0 =? LimpliesHead then
                       (if diagY (CoordNat k (diagMerge param (CoordNat n 1))) =? 1
                        then diagY (CoordNat k (diagMerge param (CoordNat n 2))) else 0)
                else if CoordNat n 0 =? LorHead then
                       (if diagY (CoordNat k (diagMerge param (CoordNat n 1))) =? 1
                        then diagY (CoordNat k (diagMerge param (CoordNat n 2))) else 0)
                else if CoordNat n 0 =? LandHead then
                       (if diagY (CoordNat k (diagMerge param (CoordNat n 1))) =? 1
                        then diagY (CoordNat k (diagMerge param (CoordNat n 2))) else 0)
                else if CoordNat n 0 =? LforallHead then
                       (if negb (VarOccursFreeInFormula (diagY param) n)
                        then 1
                        else
                          if negb (VarOccursInTerm (CoordNat n 1) (diagX param))
                          then diagY (CoordNat k (diagMerge param (CoordNat n 2)))
                          else 0) 
                else if CoordNat n 0 =? LexistsHead then
                       (if negb (VarOccursFreeInFormula (diagY param) n)
                        then 1
                        else
                          if negb (VarOccursInTerm (CoordNat n 1) (diagX param))
                          then diagY (CoordNat k (diagMerge param (CoordNat n 2)))
                          else 0)
                     else if (CoordNat n 0 =? LrelHead) || (CoordNat n 0 =? LopHead)
                             || (CoordNat n 0 =? LvarHead) then
                       1
                else 0)%bool).
    assert (forall v, FunctionRepresented 3 (fun param n k => diagY (CoordNat k (diagMerge param (CoordNat n v))))).
    { intro v. apply ComposeRepr_13. exact diagY_repr.
      apply ComposeRepr_23. exact CoordNat_repr.
      apply (proj_represented 3 2); auto.
      apply ComposeRepr_23. exact diagMerge_repr.
      apply (proj_represented 3 0); auto.
      apply ComposeRepr_23. exact CoordNat_repr.
      apply (proj_represented 3 1); auto.
      apply (ConstantRepresented v). } 
    apply (IfRepresented 3).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 1).
    apply H.
    apply (IfRepresented 3).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 2).
    apply (IfRepresented 3).
    apply (EqbRepresented 3).
    apply H.
    apply (ConstantRepresented 1).
    apply H.
    apply (ConstantRepresented 0).
    apply (IfRepresented 3).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 3).
    apply (IfRepresented 3).
    apply (EqbRepresented 3).
    apply H.
    apply (ConstantRepresented 1).
    apply H.
    apply (ConstantRepresented 0).
    apply (IfRepresented 3).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 4).
    apply (IfRepresented 3).
    apply (EqbRepresented 3).
    apply H.
    apply (ConstantRepresented 1).
    apply H.
    apply (ConstantRepresented 0).
    apply (IfRepresented 3).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 5).
    apply (IfRepresented 3).
    apply (NegRepresented 3).
    apply (ComposeRepr_23 _ _ _ VarOccursFreeInFormula_repr).
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 0); auto.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1).
    apply (IfRepresented 3).
    apply (NegRepresented 3).
    apply (ComposeRepr_23 _ _ _ VarOccursInTerm_repr).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1).
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 0); auto.
    apply H.
    apply (ConstantRepresented 0).
    apply (IfRepresented 3).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 6).
    apply (IfRepresented 3).
    apply (NegRepresented 3).
    apply (ComposeRepr_23 _ _ _ VarOccursFreeInFormula_repr).
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 0); auto.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1).
    apply (IfRepresented 3).
    apply (NegRepresented 3).
    apply (ComposeRepr_23 _ _ _ VarOccursInTerm_repr).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1).
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 0); auto.
    apply H.
    apply (ConstantRepresented 0).
    apply (OrRepresented 3).
    apply (OrRepresented 3).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 7).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 8).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 9).
    intros i j k.
    destruct (CoordNat j 0). reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n; reflexivity.
    intros. unfold IsFreeForSubstRecNat.
    destruct (CoordNat n 0). reflexivity.
    destruct n0. rewrite H. reflexivity.
    destruct n0. rewrite H,H. reflexivity.
    destruct n0. rewrite H,H. reflexivity.
    destruct n0. rewrite H,H. reflexivity.
    destruct n0. rewrite H. reflexivity.
    destruct n0. rewrite H. reflexivity.
    destruct n0. reflexivity.
    destruct n0. reflexivity.
    destruct n0; reflexivity.
    intros [|k].
    apply ComposeRepr_23. exact diagMerge_repr.
    apply (proj_represented 3 0); auto.
    apply (proj_represented 3 1); auto.
    apply (proj_represented 3 2); auto.
  - simpl. intros i j.
    rewrite diagYMergeId, diagXMergeId.
    apply (Fix lt_wf).
    intros prop IHprop. 
    rewrite IsFreeForSubst_step.
    rewrite IsFreeForSubstNat_step.
    unfold TreeFoldNatRec.
    destruct (Compare_dec.le_lt_dec (LengthNat prop) 0). reflexivity.
    unfold IsFreeForSubstRecNat, IsFreeForSubstRec.
    destruct (CoordNat prop 0) eqn:des. reflexivity.
    destruct n. unfold IsFreeForSubstNat. apply IHprop.
    exact (CoordLower _ _ (LengthPositive _ l)).
    destruct n. unfold IsFreeForSubstNat.
    rewrite IHprop, IHprop.
    destruct (IsFreeForSubst i j (CoordNat prop 1)); reflexivity.
    exact (CoordLower _ _ (LengthPositive _ l)).
    exact (CoordLower _ _ (LengthPositive _ l)).
    destruct n. unfold IsFreeForSubstNat.
    rewrite IHprop, IHprop.
    destruct (IsFreeForSubst i j (CoordNat prop 1)); reflexivity.
    exact (CoordLower _ _ (LengthPositive _ l)).
    exact (CoordLower _ _ (LengthPositive _ l)).
    destruct n. unfold IsFreeForSubstNat.
    rewrite IHprop, IHprop.
    destruct (IsFreeForSubst i j (CoordNat prop 1)); reflexivity.
    exact (CoordLower _ _ (LengthPositive _ l)).
    exact (CoordLower _ _ (LengthPositive _ l)).
    destruct n. unfold IsFreeForSubstNat.
    rewrite IHprop.
    destruct (negb (VarOccursFreeInFormula j prop)). reflexivity.
    destruct (VarOccursInTerm (CoordNat prop 1) i), (IsFreeForSubst i j (CoordNat prop 2)); reflexivity.
    exact (CoordLower _ _ (LengthPositive _ l)).
    destruct n. unfold IsFreeForSubstNat.
    rewrite IHprop.
    destruct (negb (VarOccursFreeInFormula j prop)). reflexivity.
    destruct (VarOccursInTerm (CoordNat prop 1) i), (IsFreeForSubst i j (CoordNat prop 2)); reflexivity.
    exact (CoordLower _ _ (LengthPositive _ l)).
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n; reflexivity.
Qed.

Lemma FindSubstTermTermLoop_repr
  : FunctionRepresented 4 (fun v tu i previousValues
                           => FindSubstTermTermLoop v tu i 
        (fun (y : nat) (_ : y < tu) =>
         diagY (CoordNat previousValues (diagMerge v y)))).
Proof.
  pose (fun v tu previousValues currentStep val =>
          if currentStep <=? 1 then 0
          else 
            if LengthNat (diagY tu) <=? 0 then 0
            else if VarOccursInTerm v (CoordNat (diagX tu) currentStep)
                 then
                   diagY (CoordNat previousValues (diagMerge v (diagMerge (CoordNat (diagX tu) currentStep) (CoordNat (diagY tu) currentStep))))
                 else val) as f.
  apply (FunctionRepresented_4_ext
          (@ncompose 4 4 (fun v tu previousValues : nat =>
                            nat_rec (fun _ => nat) 0 (f v tu previousValues))
                     (fun k => match k with
                            | 0 => fun v tu i prev => v
                            | 1 => fun v tu i prev => tu
                            | 2 => fun v tu i prev => prev
                            | _ => fun v tu i prev => i end))).
  - apply ComposeRepr_n.
    apply (ComposeRepr_54 (fun v tu previousValues init : nat =>
                           nat_rec (fun _ => nat) init (f v tu previousValues))).
    apply nat_rec_param_3_repr.
    unfold f. 
    apply (IfRepresented 5).
    apply (LebRepresented 5).
    apply (proj_represented 5 3); auto.
    apply (ConstantRepresented 1).
    apply (ConstantRepresented 0).
    apply (IfRepresented 5).
    apply (LebRepresented 5).
    apply ComposeRepr_15. exact LengthNat_repr.
    apply ComposeRepr_15. exact diagY_repr.
    apply (proj_represented 5 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 0).
    apply (IfRepresented 5 (fun v tu _ currentStep _ => VarOccursInTerm v (CoordNat (diagX tu) currentStep))).
    apply (ComposeRepr_25 _ _ _ VarOccursInTerm_repr).
    apply (proj_represented 5 0); apply le_n_S, le_0_n.
    apply ComposeRepr_25. exact CoordNat_repr.
    apply ComposeRepr_15. exact diagX_repr.
    apply (proj_represented 5 1); auto.
    apply (proj_represented 5 3); auto.
    apply ComposeRepr_15. exact diagY_repr.
    apply ComposeRepr_25. exact CoordNat_repr.
    apply (proj_represented 5 2); auto.
    apply ComposeRepr_25. exact diagMerge_repr.
    apply (proj_represented 5 0); apply le_n_S, le_0_n.
    apply ComposeRepr_25. exact diagMerge_repr.
    apply ComposeRepr_25. exact CoordNat_repr.
    apply ComposeRepr_15. exact diagX_repr.
    apply (proj_represented 5 1); auto.
    apply (proj_represented 5 3); auto.
    apply ComposeRepr_25. exact CoordNat_repr.
    apply ComposeRepr_15. exact diagY_repr.
    apply (proj_represented 5 1); auto.
    apply (proj_represented 5 3); auto.
    apply (proj_represented 5 4); auto.
    apply (proj_represented 4 0); auto.
    apply (proj_represented 4 1); auto.
    apply (proj_represented 4 2); auto.
    apply (ConstantRepresented 0).
    apply (proj_represented 4 3); auto.
    intros [|k]. apply (proj_represented 4 0); auto.
    destruct k. apply (proj_represented 4 1); auto.
    destruct k. apply (proj_represented 4 3); auto.
    apply (proj_represented 4 2); auto.
  - simpl. intros v tu i previousValues.
    revert i. induction i. reflexivity.
    simpl. destruct i. reflexivity.
    destruct i. reflexivity.
    rewrite IHi. clear IHi.
    unfold f.
    destruct (Compare_dec.le_lt_dec (LengthNat (diagY tu)) 0).
    apply Nat.leb_le in l. rewrite l. reflexivity.
    replace (LengthNat (diagY tu) <=? 0) with false.
    reflexivity.
    destruct (LengthNat (diagY tu) <=? 0) eqn:des. 2: reflexivity.
    exfalso. apply (Nat.lt_irrefl 0).
    apply Nat.leb_le in des.
    exact (Nat.lt_le_trans _ _ _ l des).
Qed.

Lemma FindSubstTermTerm_repr : FunctionRepresented 3 FindSubstTermTerm.
Proof.
  apply (ComposeRepr_23 (fun v : nat =>
                           Fix lt_wf (fun _ : nat => nat) (FindSubstTermTermRec v))).
  apply Fix_param_repr.
  - unfold FindSubstTermTermRec.
    apply (FunctionRepresented_3_ext
             (fun param currentStep previousValues : nat =>
     if CoordNat (diagX currentStep) 0 =? LopHead then
         (if
          ((CoordNat (diagY currentStep) 0 =? 8) &&
           (CoordNat (diagX currentStep) 1 =? CoordNat (diagY currentStep) 1) &&
           (LengthNat (diagX currentStep) =? LengthNat (diagY currentStep)))%bool
         then
          FindSubstTermTermLoop param currentStep (LengthNat (diagX currentStep))
            (fun (y : nat) (_ : y < currentStep) =>
             diagY (CoordNat previousValues (diagMerge param y)))
         else 0)
     else if CoordNat (diagX currentStep) 0 =? LvarHead then
          (if CoordNat (diagX currentStep) 1 =? param then diagY currentStep else 0)
     else 0)).
    apply (IfRepresented 3).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented LopHead).
    apply (IfRepresented 3).
    apply (AndRepresented 3).
    apply (AndRepresented 3).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented LopHead). 
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1).
    apply (EqbRepresented 3).
    apply ComposeRepr_13. exact LengthNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply ComposeRepr_13. exact LengthNat_repr.
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 1); auto.
    apply (ComposeRepr_43 _ _ _ _ _ FindSubstTermTermLoop_repr).
    apply (proj_represented 3 0); auto.
    apply (proj_represented 3 1); auto.
    apply ComposeRepr_13. exact LengthNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply (proj_represented 3 2); auto.
    apply (ConstantRepresented 0).
    apply (IfRepresented 3).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented LvarHead). 
    apply (IfRepresented 3).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1).
    apply (proj_represented 3 0); auto.
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 0).
    intros i j k. destruct (CoordNat (diagX j) 0). reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n; reflexivity.
  - intros. unfold FindSubstTermTermRec.
    replace (FindSubstTermTermLoop param i (LengthNat (diagX i)) p)
      with (FindSubstTermTermLoop param i (LengthNat (diagX i)) q).
    reflexivity.
    generalize (LengthNat (diagX i)) as n.
    induction n. reflexivity.
    simpl. destruct n. reflexivity.
    destruct n. reflexivity.
    destruct (Compare_dec.le_lt_dec (LengthNat (diagY i)) 0). reflexivity.
    destruct (VarOccursInTerm param (CoordNat (diagX i) (S (S n)))).
    symmetry. apply H.
    rewrite IHn. reflexivity.
  - apply (proj_represented 3 0); auto.
  - apply ComposeRepr_23. exact diagMerge_repr.
    apply (proj_represented 3 1); auto.
    apply (proj_represented 3 2); auto. 
Qed. 

Lemma FindSubstTermLoop_repr : FunctionRepresented 4 FindSubstTermLoop.
Proof.
  pose (fun v f g currentStep val
        => if VarOccursInTerm v (CoordNat f currentStep)
          then FindSubstTermTerm v (CoordNat f currentStep) (CoordNat g currentStep)
          else val) as stepF.
  apply (FunctionRepresented_4_ext
           (fun v f g => nat_rec (fun _ => nat) 0 (stepF v f g))).
  - apply (ComposeRepr_54 (fun v f g init : nat =>
                           nat_rec (fun _ => nat) init (stepF v f g))). 
    apply nat_rec_param_3_repr.
    unfold stepF.
    apply (IfRepresented 5 (fun v f _ currentStep _ => VarOccursInTerm v (CoordNat f currentStep))
                         (fun v f g currentStep val : nat =>
                          FindSubstTermTerm v (CoordNat f currentStep) (CoordNat g currentStep))).
    apply (ComposeRepr_25 _ _ _ VarOccursInTerm_repr).
    apply (proj_represented 5 0); apply le_n_S, le_0_n.
    apply ComposeRepr_25. exact CoordNat_repr.
    apply (proj_represented 5 1); auto.
    apply (proj_represented 5 3); auto.
    apply ComposeRepr_35. exact FindSubstTermTerm_repr.
    apply (proj_represented 5 0); apply le_n_S, le_0_n.
    apply ComposeRepr_25. exact CoordNat_repr.
    apply (proj_represented 5 1); auto.
    apply (proj_represented 5 3); auto.
    apply ComposeRepr_25. exact CoordNat_repr.
    apply (proj_represented 5 2); auto.
    apply (proj_represented 5 3); auto.
    apply (proj_represented 5 4); auto.
    apply (proj_represented 4 0); auto.
    apply (proj_represented 4 1); auto.
    apply (proj_represented 4 2); auto.
    apply (ConstantRepresented 0).
    apply (proj_represented 4 3); auto.
  - intros v f g. induction l. reflexivity.
    simpl. rewrite IHl. reflexivity.
Qed.

Lemma FindSubstTerm_repr : FunctionRepresented 3 FindSubstTerm.
Proof.
  unfold FindSubstTerm.
  apply (ComposeRepr_23 (fun v : nat =>
                           Fix lt_wf (fun _ : nat => nat) (FindSubstTermRec v))).
  apply Fix_param_repr.
  apply (FunctionRepresented_3_ext
           (fun v fg previousValues : nat =>
     if LengthNat (diagY fg) <=? 0
     then 0
     else
      if CoordNat (diagX fg) 0 =? CoordNat (diagY fg) 0
      then
       if CoordNat (diagX fg) 0 =? 1 then
           diagY
             (CoordNat previousValues
                (diagMerge v
                   (diagMerge (CoordNat (diagX fg) 1)
                      (CoordNat (diagY fg) 1))))
       else if (CoordNat (diagX fg) 0 =? 5) || (CoordNat (diagX fg) 0 =? 6) then
           (if
             ((CoordNat (diagX fg) 1 =? CoordNat (diagY fg) 1) &&
             negb (CoordNat (diagX fg) 1 =? v))%bool
           then
            diagY
              (CoordNat previousValues
                 (diagMerge v
                    (diagMerge (CoordNat (diagX fg) 2)
                       (CoordNat (diagY fg) 2))))
           else 0)
       else if CoordNat (diagX fg) 0 =? 7 then
           (if
             ((CoordNat (diagX fg) 1 =? CoordNat (diagY fg) 1) &&
             (LengthNat (diagX fg) =? LengthNat (diagY fg)))%bool
           then
            FindSubstTermLoop v (TailNat (TailNat (diagX fg)))
              (TailNat (TailNat (diagY fg)))
              (LengthNat (diagX fg) - 2)
           else 0)
       else if (CoordNat (diagX fg) 0 =? LimpliesHead)
               || (CoordNat (diagX fg) 0 =? LorHead)
               || (CoordNat (diagX fg) 0 =? LandHead) then
           (if VarOccursFreeInFormula v (CoordNat (diagX fg) 1)
           then
            diagY
              (CoordNat previousValues
                 (diagMerge v
                    (diagMerge (CoordNat (diagX fg) 1)
                       (CoordNat (diagY fg) 1))))
           else
            diagY
              (CoordNat previousValues
                 (diagMerge v
                    (diagMerge (CoordNat (diagX fg) 2)
                               (CoordNat (diagY fg) 2)))))
       else 0 else 0))%bool.
  - apply (IfRepresented 3).
    apply (LebRepresented 3).
    apply ComposeRepr_13. exact LengthNat_repr.
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 0).
    apply (IfRepresented 3). 3: apply (ConstantRepresented 0).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (IfRepresented 3).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 1).
    apply ComposeRepr_13. exact diagY_repr.
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 2); auto.
    apply ComposeRepr_23. exact diagMerge_repr.
    apply (proj_represented 3 0); auto.
    apply ComposeRepr_23. exact diagMerge_repr.
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1).
    apply (IfRepresented 3).
    apply (OrRepresented 3); apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 5).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 6).
    apply (IfRepresented 3).
    apply (AndRepresented 3).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1).
    apply (NegRepresented 3).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1).
    apply (proj_represented 3 0); auto.
    apply ComposeRepr_13. exact diagY_repr.
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 2); auto.
    apply ComposeRepr_23. exact diagMerge_repr.
    apply (proj_represented 3 0); auto.
    apply ComposeRepr_23. exact diagMerge_repr.
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 2).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 2).
    apply (ConstantRepresented 0).
    apply (IfRepresented 3).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 7).
    apply (IfRepresented 3).
    apply (AndRepresented 3); apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1).
    apply ComposeRepr_13. exact LengthNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply ComposeRepr_13. exact LengthNat_repr.
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 1); auto.
    apply ComposeRepr_43. exact FindSubstTermLoop_repr.
    apply (proj_represented 3 0); auto.
    apply ComposeRepr_13. exact TailNat_repr.
    apply ComposeRepr_13. exact TailNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply ComposeRepr_13. exact TailNat_repr.
    apply ComposeRepr_13. exact TailNat_repr.
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 1); auto.
    apply ComposeRepr_23. exact SubtractionRepresented.
    apply ComposeRepr_13. exact LengthNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 2).
    apply (ConstantRepresented 0). 
    apply (IfRepresented 3).
    apply (OrRepresented 3).
    apply (OrRepresented 3).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 2).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 3).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 4).
    apply (IfRepresented 3).
    apply (ComposeRepr_23 _ _ _ VarOccursFreeInFormula_repr).
    apply (proj_represented 3 0); auto.
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1).
    apply ComposeRepr_13. exact diagY_repr.
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 2); auto.
    apply ComposeRepr_23. exact diagMerge_repr.
    apply (proj_represented 3 0); auto.
    apply ComposeRepr_23. exact diagMerge_repr.
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1).
    apply ComposeRepr_13. exact diagY_repr.
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 2); auto.
    apply ComposeRepr_23. exact diagMerge_repr.
    apply (proj_represented 3 0); auto.
    apply ComposeRepr_23. exact diagMerge_repr.
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 2).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 2).
    apply (ConstantRepresented 0).
  - intros v j previousValues.
    unfold FindSubstTermRec.
    destruct (Compare_dec.le_lt_dec (LengthNat (diagY j)) 0).
    apply Nat.leb_le in l. rewrite l; reflexivity.
    replace (LengthNat (diagY j) <=? 0) with false. simpl.
    destruct (CoordNat (diagX j) 0 =? CoordNat (diagY j) 0). 2: reflexivity.
    destruct (CoordNat (diagX j) 0). reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n; reflexivity.
    destruct (LengthNat (diagY j) <=? 0) eqn:des. 2: reflexivity.
    apply Nat.leb_le in des.
    exfalso. apply (Nat.lt_irrefl 0).
    exact (Nat.lt_le_trans _ _ _ l des). 
  - intros. unfold FindSubstTermRec.
    destruct (Compare_dec.le_lt_dec (LengthNat (diagY i)) 0). reflexivity.
    destruct (CoordNat (diagX i) 0 =? CoordNat (diagY i) 0). 2: reflexivity.
    destruct (CoordNat (diagX i) 0). reflexivity.
    destruct n. rewrite H. reflexivity.
    destruct n. rewrite H, H. reflexivity.
    destruct n. rewrite H, H. reflexivity.
    destruct n. rewrite H, H. reflexivity.
    destruct n. rewrite H. reflexivity.
    destruct n. rewrite H. reflexivity.
    destruct n; reflexivity.
  - apply (proj_represented 3 0); auto. 
  - apply ComposeRepr_23. exact diagMerge_repr.
    apply (proj_represented 3 1); auto. 
    apply (proj_represented 3 2); auto. 
Qed.

Lemma IsExistsElim_repr : FunctionRepresentedBool 1 IsExistsElim.
Proof.
  apply (AndRepresented 1 _ (fun f : nat =>
     negb (VarOccursFreeInFormula (CoordNat (CoordNat (CoordNat f 2) 1) 1)
       (CoordNat (CoordNat f 2) 2)))).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1 IsLproposition). exact IsLproposition_repr.
  apply (EqbRepresented 1).
  apply (proj_represented 1 0); auto.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ConstantRepresented 2).
  apply ComposeRepr_21. exact ConsNat_repr.
  apply CoordNat_fst_repr.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply CoordNat_fst_repr.
  apply (ConstantRepresented 0).
  apply (EqbRepresented 1).
  apply CoordNat_fst_repr.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ConstantRepresented 6).
  apply ComposeRepr_21. exact ConsNat_repr.
  apply ComposeRepr_21. exact CoordNat_repr.
  apply CoordNat_fst_repr.
  apply (ConstantRepresented 1).
  apply ComposeRepr_21. exact ConsNat_repr.
  apply ComposeRepr_21. exact CoordNat_repr.
  apply CoordNat_fst_repr.
  apply (ConstantRepresented 2).
  apply (ConstantRepresented 0).
  apply (EqbRepresented 1).
  apply CoordNat_fst_repr.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ConstantRepresented 2).
  apply ComposeRepr_21. exact ConsNat_repr.
  apply ComposeRepr_21. exact CoordNat_repr.
  apply CoordNat_fst_repr. 
  apply (ConstantRepresented 1).
  apply ComposeRepr_21. exact ConsNat_repr.
  apply ComposeRepr_21. exact CoordNat_repr.
  apply CoordNat_fst_repr. 
  apply (ConstantRepresented 2).
  apply (ConstantRepresented 0).
  apply (EqbRepresented 1).
  apply ComposeRepr_21. exact CoordNat_repr.
  apply CoordNat_fst_repr. 
  apply (ConstantRepresented 1).
  apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr. 
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply (ConstantRepresented 0). 
  apply (EqbRepresented 1).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ConstantRepresented 2). 
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply (ConstantRepresented 0). 
  apply (EqbRepresented 1). 
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply (EqbRepresented 1). 
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply (EqbRepresented 1). 
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply (NegRepresented 1).
  apply (ComposeRepr_21 _ _ _ VarOccursFreeInFormula_repr).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr. 
Qed.

Lemma IsIndependenceOfPremise_repr :
  FunctionRepresentedBool 1 IsIndependenceOfPremise.
Proof.
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1 IsLproposition).
  exact IsLproposition_repr.
  apply (EqbRepresented 1).
  apply (proj_represented 1 0); auto.
  apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
  apply ComposeRepr_21. exact ConsNat_repr.
  apply CoordNat_fst_repr.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply CoordNat_fst_repr.
  apply (ConstantRepresented 0).
  apply (EqbRepresented 1).
  apply CoordNat_fst_repr.
  apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply (ConstantRepresented 0).
  apply (EqbRepresented 1).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply (ConstantRepresented 0).
  apply (EqbRepresented 1).
  apply CoordNat_fst_repr.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ConstantRepresented 2).
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply (ConstantRepresented 0).
  apply (EqbRepresented 1).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ConstantRepresented 5).
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply (ConstantRepresented 0).
  apply (EqbRepresented 1).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply (EqbRepresented 1).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply (EqbRepresented 1).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply (NegRepresented 1).
  apply (ComposeRepr_21 _ _ _ VarOccursFreeInFormula_repr).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
Qed.

Lemma FindNat_repr : FunctionRepresentedBool 3 FindNat.
Proof.
  pose (fun n_k l val : nat
        => if diagY n_k =? CoordNat (diagX n_k) l
          then 1 else val)%bool as f.
  apply (FunctionRepresented_3_ext
           (@ncompose 3 3 (fun param init : nat => nat_rec (fun _ : nat => nat) init (f param))
                      (fun k => match k with
                             | 0 => fun n k l => diagMerge n k
                             | 1 => fun n k l => 0
                             | _ => fun n k l => l end))).
  - apply ComposeRepr_n.
    apply (nat_rec_param_repr f).
    unfold f.
    apply (IfRepresented 3).
    apply (EqbRepresented 3).
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 0); auto.
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 0); auto.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1). 
    apply (proj_represented 3 2); auto.
    intros [|k].
    apply ComposeRepr_23. exact diagMerge_repr.
    apply (proj_represented 3 0); auto.
    apply (proj_represented 3 1); auto. 
    destruct k.
    apply (ConstantRepresented 0). 
    apply (proj_represented 3 2); auto.
  - simpl. intros i j. induction k.
    reflexivity. simpl. rewrite IHk. unfold f.
    rewrite diagXMergeId, diagYMergeId.
    destruct (j =? CoordNat i k); reflexivity.
Qed.

Lemma IsGeneralization_repr : FunctionRepresentedBool 2 IsGeneralization.
Proof.
  unfold IsGeneralization.
  apply (AndRepresented 2).
  apply (EqbRepresented 2).
  apply (proj_represented 2 0); auto.
  apply ComposeRepr_22. exact ConsNat_repr.
  apply (ConstantRepresented 5).
  apply ComposeRepr_22. exact ConsNat_repr.
  apply ComposeRepr_22. exact CoordNat_repr.
  apply (proj_represented 2 0); auto.
  apply (ConstantRepresented 1).
  apply ComposeRepr_22. exact ConsNat_repr.
  apply ComposeRepr_22. exact CoordNat_repr.
  apply (proj_represented 2 0); auto.
  apply (ConstantRepresented 2).
  apply (ConstantRepresented 0).
  apply (ComposeRepr_32 _ _ _ _ FindNat_repr).
  apply (proj_represented 2 1); auto.
  apply ComposeRepr_22. exact CoordNat_repr.
  apply (proj_represented 2 0); auto.
  apply (ConstantRepresented 2).
  apply ComposeRepr_12. exact LengthNat_repr.
  apply (proj_represented 2 1); auto.
Qed.

Lemma IsSpecialization_repr :
  FunctionRepresentedBool 1 IsSpecialization.
Proof.
  unfold IsSpecialization.
  apply (AndRepresented 1).
  apply (AndRepresented 1 IsLproposition _ IsLproposition_repr).
  apply (EqbRepresented 1).
  apply (proj_represented 1 0); auto.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ConstantRepresented 2).
  apply ComposeRepr_21. exact ConsNat_repr.
  apply CoordNat_fst_repr.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply CoordNat_fst_repr.
  apply (ConstantRepresented 0).
  apply (OrRepresented 1).
  - apply (AndRepresented 1).
    apply (EqbRepresented 1).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
    apply (AndRepresented 1 (fun prop => IsFreeForSubst
        (FindSubstTerm (CoordNat (CoordNat prop 1) 1) (CoordNat (CoordNat prop 1) 2)
           (CoordNat prop 2)) (CoordNat (CoordNat prop 1) 1) (CoordNat (CoordNat prop 1) 2))).
    apply (ComposeRepr_31 _ _ _ _ (IsFreeForSubst_repr)).
    apply ComposeRepr_31. exact FindSubstTerm_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (EqbRepresented 1).
    apply CoordNat_fst_repr.
    apply ComposeRepr_31. exact Subst_repr.
    apply ComposeRepr_31. exact FindSubstTerm_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
  - apply (AndRepresented 1 (fun prop => IsLexists (CoordNat prop 2))).
    apply (ComposeRepr_11 _ _ IsLexists_repr).
    apply CoordNat_fst_repr.
    apply (AndRepresented 1 (fun prop => IsFreeForSubst
        (FindSubstTerm (CoordNat (CoordNat prop 2) 1) (CoordNat (CoordNat prop 2) 2)
           (CoordNat prop 1)) (CoordNat (CoordNat prop 2) 1)
        (CoordNat (CoordNat prop 2) 2))).
    apply (ComposeRepr_31 _ _ _ _ (IsFreeForSubst_repr)).
    apply ComposeRepr_31. exact FindSubstTerm_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (EqbRepresented 1).
    apply CoordNat_fst_repr.
    apply ComposeRepr_31. exact Subst_repr.
    apply ComposeRepr_31. exact FindSubstTerm_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr. 
Qed.

Lemma IsQuantifierAxiom_repr : FunctionRepresentedBool 2 IsQuantifierAxiom.
Proof.
  unfold IsQuantifierAxiom.
  apply (OrRepresented 2).
  2: apply (ComposeRepr_12 _ _ IsExistsElim_repr), (proj_represented 2 0); auto.
  apply (OrRepresented 2).
  2: apply (ComposeRepr_12 _ _ IsIndependenceOfPremise_repr), (proj_represented 2 0); auto.
  apply (OrRepresented 2 _ _ IsGeneralization_repr).
  apply (ComposeRepr_12 _ _ IsSpecialization_repr).
  apply (proj_represented 2 0); auto.
Qed.

Lemma IsModusPonens_repr : FunctionRepresentedBool 2 IsModusPonens.
Proof.
  pose (fun prop_proof k val : nat
        => if IsLimplies (CoordNat (diagY prop_proof) k)
             && Nat.eqb (diagX prop_proof) (CoordNat (CoordNat (diagY prop_proof) k) 2)
             && FindNat (diagY prop_proof) (CoordNat (CoordNat (diagY prop_proof) k) 1) (LengthNat (diagY prop_proof))
          then 1 else val)%bool as f.
  unfold IsModusPonens.
  apply (FunctionRepresented_2_ext
           (@ncompose 3 2 (fun param init : nat => nat_rec (fun _ : nat => nat) init (f param))
                      (fun k => match k with
                             | 0 => fun prop proof => diagMerge prop proof
                             | 1 => fun prop proof => 0
                             | _ => fun prop proof => LengthNat proof end))).
  - apply ComposeRepr_n.
    apply (nat_rec_param_repr f).
    unfold f. apply (IfRepresented 3).
    apply (AndRepresented 3).
    apply (AndRepresented 3).
    apply (EqbRepresented 3).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 0); auto.
    apply (proj_represented 3 1); auto.
    apply ComposeRepr_23. exact ConsNat_repr.
    apply (ConstantRepresented 2).
    apply ComposeRepr_23. exact ConsNat_repr.
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 0); auto.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1).
    apply ComposeRepr_23. exact ConsNat_repr.
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 0); auto.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 2).
    apply (ConstantRepresented 0).
    apply (EqbRepresented 3).
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 0); auto.
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 0); auto.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 2).
    apply (ComposeRepr_33 _ _ _ _ FindNat_repr).
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 0); auto.
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_23. exact CoordNat_repr.
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 0); auto.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 1).
    apply ComposeRepr_13. exact LengthNat_repr.
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 0); auto.
    apply (ConstantRepresented 1).
    apply (proj_represented 3 2); auto.
    intros [|k].
    apply ComposeRepr_22. exact diagMerge_repr.
    apply (proj_represented 2 0); auto.
    apply (proj_represented 2 1); auto.
    destruct k.
    apply (ConstantRepresented 0).
    apply ComposeRepr_12. exact LengthNat_repr.
    apply (proj_represented 2 1); auto.
  - simpl. intros n k.
    generalize (LengthNat k) as p. induction p.
    reflexivity. simpl.
    rewrite IHp. clear IHp. unfold f.
    rewrite diagYMergeId, diagXMergeId.
    destruct (IsLimplies (CoordNat k p) && (n =? CoordNat (CoordNat k p) 2) &&
              FindNat k (CoordNat (CoordNat k p) 1) (LengthNat k))%bool.
    reflexivity. reflexivity.
Qed.

Definition ZipNat (n p l : nat) : nat :=
  MapNat (fun i => diagMerge (CoordNat n i) (CoordNat p i))
         (RangeNat 0 l).

Lemma ZipNat_repr : FunctionRepresented 3 ZipNat.
Proof.
  unfold ZipNat.
  pose (fun np i => diagMerge (CoordNat (diagX np) i) (CoordNat (diagY np) i)) as f.
  apply (FunctionRepresented_3_ext
           (@ncompose 2 3 (fun np : nat => MapNat (f np))
                      (fun k => match k with
                             | 0 => fun n p l => diagMerge n p
                             | _ => fun n p l => RangeNat 0 l end))).
  - apply ComposeRepr_n.
    apply MapNat_repr. unfold f.
    apply ComposeRepr_22. exact diagMerge_repr.
    apply ComposeRepr_22. exact CoordNat_repr.
    apply ComposeRepr_12. exact diagX_repr.
    apply (proj_represented 2 0); auto.
    apply (proj_represented 2 1); auto.
    apply ComposeRepr_22. exact CoordNat_repr.
    apply ComposeRepr_12. exact diagY_repr.
    apply (proj_represented 2 0); auto.
    apply (proj_represented 2 1); auto.
    intros [|k].
    apply ComposeRepr_23. exact diagMerge_repr.
    apply (proj_represented 3 0); auto.
    apply (proj_represented 3 1); auto.
    apply ComposeRepr_23. exact RangeNat_repr.
    apply (ConstantRepresented 0).
    apply (proj_represented 3 2); auto.
  - intros n k l. simpl.
    apply MapNatExt. intros i H.
    unfold f. rewrite diagXMergeId, diagYMergeId. reflexivity.
Qed.

Definition LandNat (n init : nat) : nat -> nat :=
  nat_rec (fun _ => nat) init (fun currentStep val => Land val (CoordNat n currentStep)).

Lemma LandNat_succ : forall n init l,
    LandNat n init (S l) = Land (LandNat n init l) (CoordNat n l).
Proof.
  reflexivity.
Qed.

Lemma LandNat_ext : forall l n p init,
    (forall k, k < l -> CoordNat n k = CoordNat p k)
    -> LandNat n init l = LandNat p init l. 
Proof.
  induction l. reflexivity.
  intros. simpl. rewrite (IHl n p). 
  rewrite H. reflexivity. apply Nat.le_refl.
  intros. apply H. apply (Nat.lt_trans _ _ _ H0). apply Nat.le_refl.
Qed.

Lemma LandNat_repr : FunctionRepresented 3 LandNat.
Proof.
  unfold LandNat.
  apply nat_rec_param_repr.
  apply ComposeRepr_23. exact Land_repr.
  apply (proj_represented 3 2); auto.
  apply ComposeRepr_23. exact CoordNat_repr.
  apply (proj_represented 3 0); auto.
  apply (proj_represented 3 1); auto.
Qed.

Lemma EqTerms_repr : FunctionRepresented 3 EqTerms.
Proof.
  pose (@ncompose 1 3 (MapNat (fun x => Leq (diagX x) (diagY x)))
                  (fun _ terms1 terms2 l : nat => ZipNat terms1 terms2 (S l))) as mapeq.
  apply (FunctionRepresented_3_ext
           (@ncompose 1 3 (fun l => LandNat (TailNat l) (HeadNat l) (LengthNat l-1))
                      (fun _ => mapeq))).
  - apply ComposeRepr_n.
    apply ComposeRepr_31. exact LandNat_repr.
    exact TailNat_repr. exact HeadNat_repr.
    apply ComposeRepr_21. exact SubtractionRepresented.
    exact LengthNat_repr.
    apply (ConstantRepresented 1).
    intros _. 
    apply ComposeRepr_n.
    apply (FunctionRepresented_1_ext
             (@ncompose 2 1 (fun n => MapNat (fun x : nat => Leq (diagX x) (diagY x)))
                        (fun k => match k with
                               | 0 => fun x => 0
                               | _ => fun x => x end))).
    2: reflexivity.
    apply ComposeRepr_n.
    apply (MapNat_repr (fun _ x => Leq (diagX x) (diagY x))).
    apply ComposeRepr_22. exact Leq_repr.
    apply ComposeRepr_12. exact diagX_repr.
    apply (proj_represented 2 1); auto.
    apply ComposeRepr_12. exact diagY_repr.
    apply (proj_represented 2 1); auto.
    intros [|k].
    apply (ConstantRepresented 0).
    apply (proj_represented 1 0); auto.
    intros _.
    apply ComposeRepr_33. exact ZipNat_repr.
    apply (proj_represented 3 0); auto.
    apply (proj_represented 3 1); auto.
    apply ComposeRepr_13. exact SuccessorRepresented.
    apply (proj_represented 3 2); auto.
  - simpl. intros terms1 terms2 l.
    revert l terms1 terms2. 
    induction l.
    + intros. simpl. unfold mapeq. simpl.
      unfold ZipNat. rewrite MapMapNat.
      rewrite LengthMapNat, LengthRangeNat. simpl.
      rewrite MapConsNat, HeadConsNat.
      rewrite diagXMergeId, diagYMergeId. reflexivity.
    + intros. unfold mapeq. unfold mapeq in IHl.
      simpl in IHl. simpl.
      unfold ZipNat. rewrite MapMapNat, LengthMapNat.
      rewrite LengthRangeNat.
      unfold ZipNat in IHl.
      rewrite TailMapNat.
      change (RangeNat 0 (S (S l))) with (ConsNat 0 (RangeNat 1 (S l))).
      rewrite TailConsNat, MapConsNat, HeadConsNat.
      simpl (S (S l) - 1). rewrite LandNat_succ, CoordMapNat.
      2: rewrite LengthRangeNat; apply Nat.le_refl.
      rewrite diagXMergeId, diagXMergeId, diagYMergeId, diagYMergeId.
      rewrite CoordRangeNat.
      apply f_equal2. 2: reflexivity. 2: apply Nat.le_refl.
      rewrite <- IHl. clear IHl.
      rewrite MapMapNat.
      rewrite LengthMapNat.
      rewrite TailMapNat.
      simpl (RangeNat 0 (S l)). rewrite TailConsNat.
      rewrite MapConsNat, HeadConsNat.
      rewrite LengthConsNat, LengthRangeNat.
      rewrite diagXMergeId, diagYMergeId.
      simpl (S l - 1). rewrite Nat.sub_0_r.
      apply LandNat_ext. intros k H.
      rewrite CoordMapNat, CoordMapNat.
      rewrite diagXMergeId, diagXMergeId, diagYMergeId, diagYMergeId.
      rewrite CoordRangeNat, CoordRangeNat. reflexivity.
      exact H. apply (Nat.lt_trans _ _ _ H).
      apply Nat.le_refl.
      rewrite LengthRangeNat. exact H.
      rewrite LengthRangeNat.
      apply (Nat.lt_trans _ _ _ H). apply Nat.le_refl.
Qed.

Lemma EvenVars_repr : FunctionRepresented 2 EvenVars.
Proof.
  unfold EvenVars.
  pose (fun start n : nat => Lvar (start + 2 * n)) as f.
  apply (ComposeRepr_22 (fun start : nat => MapNat (f start))
                        (fun start l => start)
                        (fun start l => RangeNat 0 l)).
  apply MapNat_repr.
  unfold f.
  apply ComposeRepr_12. exact Lvar_repr.
  apply ComposeRepr_22. exact AdditionRepresented.
  apply (proj_represented 2 0); auto.
  apply ComposeRepr_22. exact MultiplicationRepresented.
  apply (ConstantRepresented 2).
  apply (proj_represented 2 1); auto.
  apply (proj_represented 2 0); auto.
  apply ComposeRepr_22. exact RangeNat_repr.
  apply (ConstantRepresented 0).
  apply (proj_represented 2 1); auto.
Qed.

Lemma IsEqualityRelationAxiom_repr
  : FunctionRepresentedBool 1 IsEqualityRelationAxiom.
Proof.
  assert (FunctionRepresented 1 (fun f => LengthNat (CoordNat (CoordNat (CoordNat f 2) 1) 1) - 2)) as arity_repr.
  { apply ComposeRepr_21. exact SubtractionRepresented.
    apply ComposeRepr_11. exact LengthNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr. apply (ConstantRepresented 2). }
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1 _ (fun f => 1 <=? LengthNat (CoordNat (CoordNat (CoordNat f 2) 1) 1) - 2)).
  apply (EqbRepresented 1).
  apply (proj_represented 1 0); auto.
  apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
  apply ComposeRepr_21. exact ConsNat_repr.
  apply CoordNat_fst_repr.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply CoordNat_fst_repr.
  apply (ConstantRepresented 0).
  apply (LebRepresented 1 (fun _ => 1)).
  apply (ConstantRepresented 1).
  exact arity_repr.
  apply (EqbRepresented 1).
  apply CoordNat_fst_repr.
  apply ComposeRepr_31. exact EqTerms_repr.
  apply ComposeRepr_21. exact EvenVars_repr.
  apply (ConstantRepresented 0).
  exact arity_repr.
  apply ComposeRepr_21. exact EvenVars_repr.
  apply (ConstantRepresented 1).
  exact arity_repr.
  apply ComposeRepr_11. exact PredRepresented.
  exact arity_repr.
  apply (EqbRepresented 1).
  apply CoordNat_fst_repr.
  apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
  apply ComposeRepr_21. exact ConsNat_repr. 
  apply ComposeRepr_21. exact Limplies_repr.
  apply ComposeRepr_21. exact Lrel_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply ComposeRepr_21. exact EvenVars_repr.
  apply (ConstantRepresented 0).
  exact arity_repr.
  apply ComposeRepr_21. exact Lrel_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply ComposeRepr_21. exact EvenVars_repr.
  apply (ConstantRepresented 1).
  exact arity_repr.
  apply ComposeRepr_21. exact ConsNat_repr. 
  apply ComposeRepr_21. exact Limplies_repr.
  apply ComposeRepr_21. exact Lrel_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply ComposeRepr_21. exact EvenVars_repr.
  apply (ConstantRepresented 1).
  exact arity_repr. 
  apply ComposeRepr_21. exact Lrel_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply ComposeRepr_21. exact EvenVars_repr.
  apply (ConstantRepresented 0).
  exact arity_repr. 
  apply (ConstantRepresented 0). 
Qed.

Lemma IsEqualityAxiom_repr : FunctionRepresentedBool 1 IsEqualityAxiom.
Proof.
  unfold IsEqualityAxiom.
  assert (FunctionRepresented 1 (fun f => LengthNat (CoordNat (CoordNat f 2) 2) - 2))
    as arity_repr.
  { apply ComposeRepr_21. exact SubtractionRepresented.
    apply ComposeRepr_11. exact LengthNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 2). }
  apply (OrRepresented 1).
  apply (OrRepresented 1).
  apply (OrRepresented 1).
  apply (OrRepresented 1).
  apply (EqbRepresented 1).
  apply (proj_represented 1 0); auto.
  apply (ConstantRepresented (
     ConsNat 7 (ConsNat 0 (ConsNat (Lvar 0) (ConsNat (Lvar 0) NilNat))))).
  apply (EqbRepresented 1).
  apply (proj_represented 1 0); auto.
  apply (ConstantRepresented (
     ConsNat 2
       (ConsNat (Leq (Lvar 0) (Lvar 1)) (ConsNat (Leq (Lvar 1) (Lvar 0)) NilNat)))).
  apply (EqbRepresented 1).
  apply (proj_represented 1 0); auto.
  exact (ConstantRepresented (
     ConsNat 2
       (ConsNat (Land (Leq (Lvar 0) (Lvar 1)) (Leq (Lvar 1) (Lvar 2)))
          (ConsNat (Leq (Lvar 0) (Lvar 2)) NilNat))) 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1 _ (fun f => 1 <=? LengthNat (CoordNat (CoordNat f 2) 2) - 2)).
  apply (EqbRepresented 1).
  apply (proj_represented 1 0); auto.
  apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
  apply ComposeRepr_21. exact ConsNat_repr.
  apply CoordNat_fst_repr.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply CoordNat_fst_repr.
  apply (ConstantRepresented 0).
  refine (LebRepresented 1 (fun _ => 1) _ _ arity_repr).
  apply (ConstantRepresented 1).
  apply (EqbRepresented 1).
  apply ComposeRepr_21. exact CoordNat_repr.
  apply (proj_represented 1 0); auto.
  apply (ConstantRepresented 1).
  apply ComposeRepr_31. exact EqTerms_repr.
  apply ComposeRepr_21. exact EvenVars_repr.
  apply (ConstantRepresented 0).
  exact arity_repr.
  apply ComposeRepr_21. exact EvenVars_repr.
  apply (ConstantRepresented 1).
  exact arity_repr.
  apply ComposeRepr_11.
  exact PredRepresented.
  apply ComposeRepr_21. exact SubtractionRepresented.
  apply ComposeRepr_11. exact LengthNat_repr.
  apply ComposeRepr_21. exact CoordNat_repr.
  apply ComposeRepr_21. exact CoordNat_repr.
  apply (proj_represented 1 0); auto.
  apply (ConstantRepresented 2).
  apply (ConstantRepresented 2).
  apply (ConstantRepresented 2).
  apply (EqbRepresented 1).
  apply ComposeRepr_21. exact CoordNat_repr.
  apply (proj_represented 1 0); auto.
  apply (ConstantRepresented 2).
  apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
  apply ComposeRepr_21. exact ConsNat_repr.
  apply ComposeRepr_21. exact Lop_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr. 
  apply ComposeRepr_21. exact EvenVars_repr.
  apply (ConstantRepresented 0). exact arity_repr.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply ComposeRepr_21. exact Lop_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr. 
  apply ComposeRepr_21. exact EvenVars_repr.
  apply (ConstantRepresented 1). exact arity_repr.
  apply (ConstantRepresented 0).
  apply IsEqualityRelationAxiom_repr.
Qed.

Lemma IsPropAx1_repr : FunctionRepresentedBool 1 IsPropAx1.
Proof.
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1 _ _ IsLproposition_repr).
  apply (EqbRepresented 1).
  apply (proj_represented 1 0); auto.
  apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
  apply ComposeRepr_21. exact ConsNat_repr.
  apply CoordNat_fst_repr.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply CoordNat_fst_repr.
  apply (ConstantRepresented 0).
  apply (EqbRepresented 1).
  apply CoordNat_fst_repr.
  apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
  apply (ConstantRepresented 0).
  apply (EqbRepresented 1).
  apply CoordNat_fst_repr.
  apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
  apply CoordNat_fst_repr.
Qed. 

Lemma IsPropAx2_repr : FunctionRepresentedBool 1 IsPropAx2.
Proof.
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1 _ _ IsLproposition_repr).
  - apply (EqbRepresented 1).
    apply (proj_represented 1 0); auto.
    apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 2).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 2).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
Qed.

Lemma IsPropAx3_repr : FunctionRepresentedBool 1 IsPropAx3.
Proof.
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1 _ _ IsLproposition_repr).
  - apply (EqbRepresented 1).
    apply (proj_represented 1 0); auto.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 2).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (proj_represented 1 0); auto.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 2).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 2).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 2).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 1).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 1).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
Qed.

Lemma IsPropAx4_repr : FunctionRepresentedBool 1 IsPropAx4.
Proof.
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1 _ _ IsLproposition_repr).
  - apply (EqbRepresented 1).
    apply (proj_represented 1 0); auto.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 2).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 1).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 1).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply CoordNat_fst_repr.
Qed.

Lemma IsPropAx5_repr : FunctionRepresentedBool 1 IsPropAx5.
Proof.
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1 _ _ IsLproposition_repr).
  - apply (EqbRepresented 1).
    apply (proj_represented 1 0); auto.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 2).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 2).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 1).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
Qed.

Lemma IsPropAx6_repr : FunctionRepresentedBool 1 IsPropAx6.
Proof.
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1 _ _ IsLproposition_repr).
  - apply (EqbRepresented 1).
    apply (proj_represented 1 0); auto.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 2).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 2).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 4).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
Qed.

Lemma IsPropAx7_repr : FunctionRepresentedBool 1 IsPropAx7.
Proof.
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1 _ _ IsLproposition_repr).
  - apply (EqbRepresented 1).
    apply (proj_represented 1 0); auto.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 2).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 4).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply CoordNat_fst_repr.
Qed.

Lemma IsPropAx8_repr : FunctionRepresentedBool 1 IsPropAx8.
Proof.
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1 _ _ IsLproposition_repr).
  - apply (EqbRepresented 1).
    apply (proj_represented 1 0); auto.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 2).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 4).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply CoordNat_fst_repr.
Qed.

Lemma IsPropAx9_repr : FunctionRepresentedBool 1 IsPropAx9.
Proof.
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1 _ _ IsLproposition_repr).
  - apply (EqbRepresented 1).
    apply (proj_represented 1 0); auto.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 2).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 3).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
Qed.

Lemma IsPropAx10_repr : FunctionRepresentedBool 1 IsPropAx10.
Proof.
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1 _ _ IsLproposition_repr).
  - apply (EqbRepresented 1).
    apply (proj_represented 1 0); auto.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 2).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 3).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
Qed.

Lemma IsPropAx11_repr : FunctionRepresentedBool 1 IsPropAx11.
Proof.
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1).
  apply (AndRepresented 1 _ _ IsLproposition_repr).
  - apply (EqbRepresented 1).
    apply (proj_represented 1 0); auto.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 2).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 2).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 2).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 2).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 2).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ConstantRepresented 3).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply ComposeRepr_21. exact ConsNat_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
  - apply (EqbRepresented 1).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (CoordNat_fst_repr _)).
    apply CoordNat_fst_repr.
Qed.

Lemma IsPropositionalAxiom_repr : FunctionRepresentedBool 1 IsPropositionalAxiom.
Proof.
  apply (OrRepresented 1).
  apply (OrRepresented 1).
  apply (OrRepresented 1).
  apply (OrRepresented 1).
  apply (OrRepresented 1).
  apply (OrRepresented 1).
  apply (OrRepresented 1).
  apply (OrRepresented 1).
  apply (OrRepresented 1).
  exact IsPropAx1_repr.
  exact IsPropAx2_repr.
  exact IsPropAx3_repr.
  exact IsPropAx5_repr.
  exact IsPropAx6_repr.
  exact IsPropAx7_repr.
  exact IsPropAx8_repr.
  exact IsPropAx9_repr.
  exact IsPropAx10_repr.
  exact IsPropAx11_repr.
Qed.

Lemma IsProofStep_repr : forall IsAxiom,
    FunctionRepresentedBool 1 IsAxiom ->
    FunctionRepresentedBool 2 (IsProofStep IsAxiom).
Proof.
  intros IsAxiom IsAxiomRep.
  unfold IsProofStep.
  refine (OrRepresented 2 (fun prop proof => (IsAxiom prop && IsLproposition prop || IsPropositionalAxiom prop
      || IsEqualityAxiom prop || IsModusPonens prop proof))%bool
                        _ _ IsQuantifierAxiom_repr).
  refine (OrRepresented 2 (fun prop proof => (IsAxiom prop && IsLproposition prop || IsPropositionalAxiom prop
      || IsEqualityAxiom prop))%bool
                       _ _ IsModusPonens_repr).
  apply (OrRepresented 2 (fun prop proof => (IsAxiom prop && IsLproposition prop || IsPropositionalAxiom prop))
                       (fun prop proof => IsEqualityAxiom prop))%bool.
  apply (OrRepresented 2 (fun prop proof => (IsAxiom prop && IsLproposition prop))%bool
                       (fun prop proof => IsPropositionalAxiom prop)).
  apply (AndRepresented 2 _ (fun prop proof => IsLproposition prop)).
  apply (ComposeRepr_12 _ _ IsAxiomRep).
  apply (proj_represented 2 0); auto.
  apply (ComposeRepr_12 _ _ IsLproposition_repr).
  apply (proj_represented 2 0); auto.
  apply (ComposeRepr_12 _ _ IsPropositionalAxiom_repr).
  apply (proj_represented 2 0); auto.
  apply (ComposeRepr_12 _ _ IsEqualityAxiom_repr).
  apply (proj_represented 2 0); auto.
Qed.

Lemma IsProofLoopRepresented : forall (IsAxiom : nat -> bool),
    FunctionRepresentedBool 1 IsAxiom ->
    FunctionRepresentedBool 2 (IsProofLoop IsAxiom).
Proof.
  intros IsAxiom IsAxiomRep.
  pose (fun proof currentStep val : nat
        => if IsProofStep IsAxiom (CoordNat proof currentStep)
                         (NthTailNat proof (S currentStep))
          then val else 0) as stepF.
  apply (FunctionRepresented_2_ext
           (@ncompose 3 2 (fun param init : nat => nat_rec (fun _ : nat => nat) init (stepF param))
                      (fun k => match k with
                             | 0 => fun proof k => proof
                             | 1 => fun proof k => 1
                             | _ => fun proof k => k
                             end))).
  - apply ComposeRepr_n.
    apply nat_rec_param_repr.
    unfold stepF.
    apply (IfRepresented 3 (fun proof currentStep val
                            => IsProofStep IsAxiom (CoordNat proof currentStep)
                                          (NthTailNat proof (S currentStep)))).
    apply (ComposeRepr_23 _ _ _ (IsProofStep_repr IsAxiom IsAxiomRep)).
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 0); auto.
    apply (proj_represented 3 1); auto.
    apply ComposeRepr_23. exact NthTailNat_repr.
    apply (proj_represented 3 0); auto.
    apply ComposeRepr_13. exact SuccessorRepresented.
    apply (proj_represented 3 1); auto.
    apply (proj_represented 3 2); auto.
    apply (ConstantRepresented 0).
    intros [|k].
    apply (proj_represented 2 0); auto.
    destruct k.
    apply (ConstantRepresented 1).
    apply (proj_represented 2 1); auto.
  - simpl.
    assert (forall k proof, nat_rec (fun _ : nat => nat) 1 (stepF proof) k = 0
                       \/ nat_rec (fun _ : nat => nat) 1 (stepF proof) k = 1)
      as binary.
    { induction k. intros. right. reflexivity.
      intros. simpl. unfold stepF. simpl.
      destruct (IsProofStep IsAxiom (CoordNat proof k) (NthTailNat (TailNat proof) k)).
      2: left; reflexivity. apply IHk. }
    assert (forall k proof, nat_rec (fun _ : nat => nat) 1 (stepF proof) k = 1
                       <-> (forall i : nat,
       i < k ->
       IsProofStep IsAxiom (CoordNat proof i) (NthTailNat proof (S i)) = true)) as H.
    induction k.
    + intros. simpl. split. intros. inversion H0.
      intros. reflexivity.
    + intros. simpl. split.
      intros. unfold stepF in H.
      destruct (IsProofStep IsAxiom (CoordNat proof k) (NthTailNat proof (S k)))
               eqn:des.
      2: discriminate H.
      apply Nat.le_succ_r in H0. destruct H0.
      2: inversion H0; exact des.
      apply IHk. exact H. exact H0.
      intro H. unfold stepF.
      destruct (IsProofStep IsAxiom (CoordNat proof k) (NthTailNat proof (S k)))
               eqn:des.
      apply IHk. intros i H0. apply H.
      apply (Nat.lt_trans _ _ _ H0). apply Nat.le_refl.
      exfalso.
      specialize (H k (Nat.le_refl _)).
      simpl in des. rewrite des in H. discriminate H.
    + intros proof k.
      pose proof (IsProofLoop_spec IsAxiom k proof).
      destruct (IsProofLoop IsAxiom proof k).
      apply H, H0. reflexivity.
      specialize (H k proof).
      specialize (binary k proof).
      destruct (nat_rec (fun _ : nat => nat) 1 (stepF proof) k). reflexivity.
      exfalso. destruct binary. discriminate H1.
      destruct H as [H _]. specialize (H H1).
      destruct H0 as [_ H0]. specialize (H0 H). discriminate H0.
Qed.

Lemma IsProofRepresented : forall (IsAxiom : nat -> bool),
    FunctionRepresentedBool 1 IsAxiom ->
    FunctionRepresentedBool 2 (IsProof IsAxiom).
Proof.
  intros IsAxiom IsAxiomRep.
  unfold IsProof.
  apply (AndRepresented 2
                        (fun prop proof =>
                           ((prop =? CoordNat proof 0) && (1 <=? LengthNat proof))%bool)
                        (fun _ proof => IsProofLoop IsAxiom proof (LengthNat proof))).
  apply (AndRepresented 2 (fun prop proof => ((prop =? CoordNat proof 0)))
                        (fun prop proof => ((1 <=? LengthNat proof)))).
  apply (EqbRepresented 2).
  apply (proj_represented 2 0); auto.
  apply (ComposeRepr_22 _ _ _ CoordNat_repr).
  apply (proj_represented 2 1); auto.
  apply (ConstantRepresented 0).
  apply (LebRepresented 2 (fun _ _ => 1) (fun _ proof => LengthNat proof)).
  apply (ConstantRepresented 1).
  apply ComposeRepr_12.
  exact LengthNat_repr.
  apply (proj_represented 2 1); auto.
  apply (ComposeRepr_22 _ _ _ (IsProofLoopRepresented IsAxiom IsAxiomRep)).
  apply (proj_represented 2 1); auto.
  apply ComposeRepr_12.
  exact LengthNat_repr.
  apply (proj_represented 2 1); auto.
Qed.

Lemma SubstSelfZeroRepresented :
  FunctionRepresented 1 (fun prop : nat => Subst (PAnat prop) 0 prop).
Proof.
  apply ComposeRepr_31.
  exact Subst_repr.
  exact PAnatRepresented.
  apply (ConstantRepresented 0).
  apply (proj_represented 1 0); apply Nat.le_refl.
Qed.

Lemma IsProofRepresented_alt : forall IsAxiom (prop prf : nat) (b : bool)
                                 (IsAxiomRep : FunctionRepresentedBool 1 IsAxiom),
    IsProof IsAxiom prop prf = b
    <-> IsProved IsWeakHeytingAxiom
               (Subst (PAnat (if b then 1 else 0)) 2
                      (Subst (PAnat prf) 1
                             (Subst (PAnat prop) 0 (IsProofRepresented IsAxiom IsAxiomRep)))).
Proof.
  intros.
  pose proof (FormulaRepresents_alt
                2
                _ _ (ConsNat prop (ConsNat prf NilNat))
                (fr_rep _ _ (IsProofRepresented IsAxiom IsAxiomRep))
                (fr_propprop _ _ _)
                (if b then 1 else 0)) as H.
  simpl in H.
  rewrite CoordTailNat, CoordConsHeadNat, CoordConsTailNat, CoordConsHeadNat in H.
  simpl in H.
  rewrite (SubstSubstDiffCommutes _ 0 1) in H.
  split.
  - intros. subst b. destruct H as [H _].
    specialize (H eq_refl).
    exact H.
  - intro H0. destruct H as [_ H]. specialize (H H0).
    destruct (IsProof IsAxiom prop prf), b; try reflexivity; try discriminate.
  - discriminate.
  - apply PAnat_closed.
  - apply PAnat_closed.
Qed.

Lemma IsProofRepresented_sat : forall IsAxiom (prop prf : nat) (b : bool) varValues
                                 (IsAxiomRep : FunctionRepresentedBool 1 IsAxiom),
    IsProof IsAxiom prop prf = b
    <-> HAstandardModel
        (Subst (PAnat (if b then 1 else 0)) 2
               (Subst (PAnat prf) 1
                      (Subst (PAnat prop) 0 (IsProofRepresented IsAxiom IsAxiomRep)))) varValues.
Proof.
  intros.
  pose proof (FormulaRepresents_sat
                2 _ _ (ConsNat prop (ConsNat prf NilNat))
                (fr_rep _ _ (IsProofRepresented IsAxiom IsAxiomRep))
                (fr_propprop _ _ _)
                (if b then 1 else 0) varValues) as H.
  simpl in H.
  rewrite CoordConsHeadNat, CoordTailNat, CoordConsTailNat, CoordConsHeadNat in H.
  rewrite (SubstSubstDiffCommutes _ 0 1) in H.
  split.
  - intros. subst b. destruct H as [H _].
    specialize (H eq_refl). exact H.
  - intro H0. destruct H as [_ H]. specialize (H H0).
    destruct (IsProof IsAxiom prop prf), b; try reflexivity; try discriminate.
  - discriminate.
  - apply PAnat_closed.
  - apply PAnat_closed.
Qed.
