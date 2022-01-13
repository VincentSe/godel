(** Functions to substitute terms for variables, and checks of variable captures. *)

Require Import PeanoNat.
Require Import Arith.Wf_nat.
Require Import Arith.Compare_dec.
Require Import EnumSeqNat.
Require Import Formulas.

(* Substitute term u for variable Xv in term t.
   SubstTerm truncates t, as does Subst below. *)
Definition SubstTermRec (u v t : nat) (rec : nat -> nat) : nat :=
  match CoordNat t 0 with
  | LvarHead => if Nat.eqb (CoordNat t 1) v then u else t
  | LopHead => Lop (CoordNat t 1) (MapNat rec (RangeNat 2 (LengthNat t - 2)))
  | _ => 0
  end.
Definition SubstTerm (u v : nat) : nat -> nat := TreeFoldNat (SubstTermRec u v) O.

Lemma SubstTerm_step : forall u v t,
    SubstTerm u v t = TreeFoldNatRec (SubstTermRec u v) O t (fun k _ => SubstTerm u v k).
Proof.
  intros.
  unfold SubstTerm, TreeFoldNat. rewrite Fix_eq.
  reflexivity.
  intros. unfold TreeFoldNatRec, SubstTermRec.
  destruct (le_lt_dec (LengthNat x) 0). reflexivity.
  destruct (CoordNat x 0). reflexivity.
  repeat (destruct n; [reflexivity|]).
  destruct n. 2: destruct n; reflexivity.
  apply f_equal.
  apply MapNatExt. intros.
  rewrite H. reflexivity. 
Qed.

Lemma SubstTerm_zero : forall u v, SubstTerm u v 0 = 0.
Proof.
  intros. rewrite SubstTerm_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat 0) 0). reflexivity.
  inversion l.
Qed.

Lemma SubstTerm_varHead : forall u v t,
    CoordNat t 0 = LvarHead
    -> SubstTerm u v t = (if Nat.eqb (CoordNat t 1) v then u else t).
Proof.
  intros. rewrite SubstTerm_step.
  unfold SubstTermRec, TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat t) 0).
  exfalso.
  rewrite CoordNatAboveLength in H. discriminate. exact l.
  rewrite H. reflexivity.
Qed.

Lemma SubstTerm_var : forall u v t,
    SubstTerm u v (Lvar t) = (if Nat.eqb t v then u else Lvar t).
Proof.
  intros. rewrite SubstTerm_varHead.
  unfold Lvar.
  rewrite CoordConsTailNat, CoordConsHeadNat.
  reflexivity.
  unfold Lvar.
  rewrite CoordConsHeadNat. reflexivity.
Qed.

Lemma SubstTerm_opHead : forall u v t,
    CoordNat t 0 = LopHead
    -> SubstTerm u v t 
      = Lop (CoordNat t 1)
            (MapNat (fun i : nat => SubstTerm u v (CoordNat t i)) (RangeNat 2 (LengthNat t - 2))).
Proof.
  intros.
  rewrite SubstTerm_step.
  unfold SubstTermRec, TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat t) 0).
  exfalso. rewrite CoordNatAboveLength in H. discriminate. exact l.
  rewrite H. reflexivity.
Qed.

Lemma SubstTerm_op : forall u v o args,
    SubstTerm u v (Lop o args)
    = Lop o (MapNat (SubstTerm u v) args).
Proof.
  intros. rewrite SubstTerm_opHead.
  unfold Lop at 2. rewrite CoordConsTailNat, CoordConsHeadNat.
  rewrite LengthLop.
  replace (2 + LengthNat args - 2) with (LengthNat args).
  apply f_equal.
  apply TruncatedEqNat.
  rewrite LengthMapNat, LengthRangeNat, LengthMapNat. reflexivity.
  rewrite LengthMapNat, MapNatTruncated.
  rewrite LengthMapNat, MapNatTruncated. reflexivity.
  intros k H. rewrite LengthMapNat in H.
  rewrite CoordMapNat. 2: exact H.
  rewrite LengthRangeNat in H.
  rewrite CoordMapNat, CoordRangeNat, (CoordNat_op _ _ k). reflexivity.
  exact H. exact H.
  rewrite Nat.add_comm. rewrite Nat.add_sub. reflexivity.
  unfold Lop. rewrite CoordConsHeadNat. reflexivity.
Qed.

Lemma SubstTerm_const : forall u v c,
    SubstTerm u v (Lconst c) = Lconst c.
Proof.
  intros. unfold Lconst.
  rewrite SubstTerm_op.
  reflexivity.
Qed.

Lemma SubstTerm_op1 : forall u v o a,
    SubstTerm u v (Lop1 o a) = Lop1 o (SubstTerm u v a).
Proof.
  intros. unfold Lop1.
  rewrite SubstTerm_op, MapConsNat, MapNilNat. reflexivity.
Qed.

Lemma SubstTerm_op2 : forall u v o a b,
    SubstTerm u v (Lop2 o a b) = Lop2 o (SubstTerm u v a) (SubstTerm u v b).
Proof.
  intros. unfold Lop2.
  rewrite SubstTerm_op, MapConsNat, MapConsNat, MapNilNat. reflexivity.
Qed.

Lemma SubstTerm_op3 : forall u v o a b c,
    SubstTerm u v (Lop3 o a b c)
    = Lop3 o (SubstTerm u v a) (SubstTerm u v b) (SubstTerm u v c).
Proof.
  intros. unfold Lop3.
  rewrite SubstTerm_op, MapConsNat, MapConsNat, MapConsNat, MapNilNat. reflexivity.
Qed.

Lemma SubstTerm_not : forall u v f, SubstTerm u v (Lnot f) = 0.
Proof.
  intros.
  rewrite SubstTerm_step.
  unfold SubstTermRec, TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lnot f)) 0).
  reflexivity.
  unfold Lnot.
  rewrite CoordConsHeadNat. reflexivity.
Qed.

Lemma IsSubstTermLterm : forall u v t : nat,
    IsLterm t = true ->
    IsLterm u = true ->
    IsLterm (SubstTerm u v t) = true.
Proof.
  intros u v.
  apply (Lterm_rect (fun term => IsLterm u = true ->
                              IsLterm (SubstTerm u v term) = true)).
  - (* Lvar *)
    intros. 
    rewrite SubstTerm_var. destruct (v0 =? v).
    exact H. apply IsLterm_var.
  - (* Lop *)
    intros. 
    rewrite SubstTerm_op.
    apply LopIsTerm.
    intros i H0. rewrite LengthMapNat in H0.
    rewrite CoordMapNat.
    apply IHterms. exact H0. exact H. exact H0.
    rewrite LengthMapNat. apply MapNatTruncated.
Qed.
 
(* Substitute term u for all free occurrences of variable Xv in formula f.
   This accepts variable captures, which will be handled by IsFreeForSubst below. *)
Definition SubstRec (u v f : nat) (rec : nat -> nat) : nat :=
  match CoordNat f 0 with
  | LnotHead => Lnot (rec 1) (* this truncates ill-formed propositions *)
  | LimpliesHead => Limplies (rec 1) (rec 2)
  | LorHead => Lor (rec 1) (rec 2)
  | LandHead => Land (rec 1) (rec 2)
  | LforallHead => Lforall (CoordNat f 1)
                          (if Nat.eqb (CoordNat f 1) v
                           then CoordNat f 2 (* do not substitute u for bound Xv *)
                           else rec 2)
  | LexistsHead => Lexists (CoordNat f 1)
                          (if Nat.eqb (CoordNat f 1) v
                           then CoordNat f 2 (* do not substitute u for bound Xv *)
                           else rec 2)
  | LrelHead => Lrel (CoordNat f 1) (MapNat (SubstTerm u v) (TailNat (TailNat f)))
  | _ => 0
  end.

Definition Subst (u v : nat) : nat -> nat := TreeFoldNat (SubstRec u v) O.

Lemma Subst_step : forall u v f,
    Subst u v f = TreeFoldNatRec (SubstRec u v) O f (fun k _ => Subst u v k).
Proof.
  intros.
  unfold Subst, TreeFoldNat. rewrite Fix_eq.
  reflexivity.
  intros x g h H. unfold TreeFoldNatRec, SubstRec.
  destruct (le_lt_dec (LengthNat x) 0). reflexivity.
  destruct (CoordNat x 0). reflexivity.
  destruct n. rewrite H. reflexivity.
  destruct n. rewrite H, H. reflexivity.
  destruct n. rewrite H, H. reflexivity.
  destruct n. rewrite H, H. reflexivity.
  destruct n. rewrite H. reflexivity.
  destruct n. rewrite H. reflexivity.
  destruct n. reflexivity. reflexivity.
Qed.

Lemma Subst_not : forall u v f, Subst u v (Lnot f) = Lnot (Subst u v f).
Proof.
  intros. rewrite Subst_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lnot f)) 0).
  rewrite LengthLnot in l. inversion l.
  unfold SubstRec, Lnot.
  rewrite CoordConsHeadNat.
  rewrite CoordConsTailNat, CoordConsHeadNat.
  reflexivity.
Qed.

Lemma Subst_implies : forall u v f g,
    Subst u v (Limplies f g) = Limplies (Subst u v f) (Subst u v g).
Proof.
  intros. rewrite Subst_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Limplies f g)) 0).
  rewrite LengthLimplies in l. inversion l.
  unfold SubstRec, Limplies.
  rewrite CoordConsHeadNat.
  do 3 rewrite CoordConsTailNat.
  do 2 rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma Subst_or : forall u v f g,
    Subst u v (Lor f g) = Lor (Subst u v f) (Subst u v g).
Proof.
  intros. rewrite Subst_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lor f g)) 0).
  rewrite LengthLor in l. inversion l.
  unfold SubstRec, Lor.
  rewrite CoordConsHeadNat.
  do 3 rewrite CoordConsTailNat.
  do 2 rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma Subst_and : forall u v f g,
    Subst u v (Land f g) = Land (Subst u v f) (Subst u v g).
Proof.
  intros. rewrite Subst_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Land f g)) 0).
  rewrite LengthLand in l. inversion l.
  unfold SubstRec, Land.
  rewrite CoordConsHeadNat.
  do 3 rewrite CoordConsTailNat.
  do 2 rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma Subst_equiv : forall u v f g,
    Subst u v (Lequiv f g) = Lequiv (Subst u v f) (Subst u v g).
Proof.
  intros. rewrite Subst_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lequiv f g)) 0).
  unfold Lequiv in l. rewrite LengthLand in l. inversion l.
  unfold SubstRec, Lequiv, Land.
  rewrite CoordConsHeadNat.
  do 3 rewrite CoordConsTailNat.
  do 2 rewrite CoordConsHeadNat.
  rewrite Subst_implies.
  rewrite Subst_implies.
  reflexivity.
Qed.

Lemma Subst_forallHead : forall u v f,
    CoordNat f 0 = LforallHead
    -> Subst u v f
      = Lforall (CoordNat f 1) (if CoordNat f 1 =? v then CoordNat f 2
                                else (Subst u v (CoordNat f 2))).
Proof.
  intros. rewrite Subst_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat f) 0).
  exfalso. rewrite CoordNatAboveLength in H. discriminate. exact l.
  unfold SubstRec, Lforall.
  rewrite H.
  reflexivity.
Qed.

Lemma Subst_forall : forall u v i f,
    Subst u v (Lforall i f)
    = Lforall i (if Nat.eqb i v then f else Subst u v f).
Proof.
  intros. rewrite (Subst_forallHead _ _ (Lforall i f)).
  rewrite CoordNat_forall_1, CoordNat_forall_2.
  reflexivity.
  unfold Lforall.
  rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma Subst_existsHead : forall u v f,
    CoordNat f 0 = LexistsHead
    -> Subst u v f
      = Lexists (CoordNat f 1) (if CoordNat f 1 =? v then CoordNat f 2
                                else (Subst u v (CoordNat f 2))).
Proof.
  intros. rewrite Subst_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat f) 0).
  exfalso. rewrite CoordNatAboveLength in H. discriminate. exact l.
  unfold SubstRec, Lexists.
  rewrite H.
  reflexivity.
Qed.

Lemma Subst_exists : forall u v i f,
    Subst u v (Lexists i f)
    = Lexists i (if Nat.eqb i v then f else Subst u v f).
Proof.
  intros. rewrite Subst_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lexists i f)) 0).
  rewrite LengthLexists in l. inversion l.
  unfold SubstRec, Lexists; rewrite CoordConsHeadNat.
  rewrite CoordConsTailNat, CoordConsHeadNat.
  rewrite CoordConsTailNat, CoordConsTailNat.
  rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma Subst_rel : forall u v r args,
    Subst u v (Lrel r args) = Lrel r (MapNat (SubstTerm u v) args).
Proof.
  intros. rewrite Subst_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lrel r args)) 0).
  rewrite LengthLrel in l. inversion l.
  unfold SubstRec, Lrel; rewrite CoordConsHeadNat.
  rewrite TailConsNat, TailConsNat.
  rewrite CoordConsTailNat, CoordConsHeadNat.
  reflexivity.
Qed.

Lemma Subst_rel1 : forall u v r a,
    Subst u v (Lrel1 r a) = Lrel1 r (SubstTerm u v a).
Proof.
  intros.
  unfold Lrel1. rewrite Subst_rel, MapConsNat, MapNilNat. 
  reflexivity.
Qed.

Lemma Subst_rel2 : forall u v r a b,
    Subst u v (Lrel2 r a b)
    = Lrel2 r (SubstTerm u v a) (SubstTerm u v b).
Proof.
  intros.
  unfold Lrel2. rewrite Subst_rel.
  rewrite MapConsNat, MapConsNat, MapNilNat. reflexivity.
Qed.

Lemma Subst_eq : forall u v a b,
    Subst u v (Leq a b)
    = Leq (SubstTerm u v a) (SubstTerm u v b).
Proof.
  intros. unfold Leq.
  rewrite Subst_rel2. reflexivity.
Qed.

Lemma SubstIsLproposition : forall f,
    IsLproposition f = true
    -> forall u v, IsLterm u = true
    -> IsLproposition (Subst u v f) = true.
Proof.
  apply (Lproposition_rect
           (fun prop => forall u v, IsLterm u = true
                            -> IsLproposition (Subst u v prop) = true)).
  - (* Lrel *)
    intros. rewrite Subst_rel, IsLproposition_rel.
    split. rewrite LengthMapNat.
    apply MapNatTruncated.
    intros n H0. rewrite LengthMapNat in H0.
    rewrite CoordMapNat.
    apply IsSubstTermLterm.
    apply elemterms, H0. exact H. exact H0.
  - (* Lnot *)
    intros. rewrite Subst_not, IsLproposition_not.
    apply IHprop, H.
  - (* Limplies *)
    intros. rewrite Subst_implies, IsLproposition_implies.
    rewrite IHg, IHh. reflexivity. exact H. exact H.
  - (* Lor *)
    intros. rewrite Subst_or, IsLproposition_or.
    rewrite IHg, IHh. reflexivity. exact H. exact H.
  - (* Land *)
    intros. rewrite Subst_and, IsLproposition_and.
    rewrite IHg, IHh. reflexivity. exact H. exact H.
  - (* Lforall *)
    intros. rewrite Subst_forall, IsLproposition_forall.
    destruct (v =? v0). exact propprop. apply IHprop, H.
  - (* Lexists *)
    intros. rewrite Subst_exists, IsLproposition_exists.
    destruct (v =? v0). exact propprop. apply IHprop, H.
Qed.

(* We reuse SubstTerm instead of redefining a new fold,
   to extract less code in OCaml. *)
Definition VarOccursInTerm (v t : nat) : bool := negb (Nat.eqb (SubstTerm 0 v t) t).

Lemma VarOccursInTerm_opHead : forall v t,
    CoordNat t 0 = LopHead
    -> 2 <= LengthNat t
    -> NthTailNat t (LengthNat t) = 0
    -> (VarOccursInTerm v t = true    (* i.e. SubstTerm 0 v t <> t *)
       <-> exists j, j < pred (pred (LengthNat t))
              /\ VarOccursInTerm v (CoordNat t (S (S j))) = true).
Proof.
  intros v t top tlen ttrunc.
  unfold VarOccursInTerm.
  rewrite Bool.negb_true_iff. split.
  - intro H0.
    apply Nat.eqb_neq in H0.
    rewrite SubstTerm_step in H0.
    unfold TreeFoldNatRec in H0.
    destruct (le_lt_dec (LengthNat t) 0).
    rewrite (CoordNatAboveLength _ _ l) in top.
    discriminate.
    unfold SubstTermRec in H0.
    rewrite top in H0.
    destruct (TruncatedDiffNat (Lop (CoordNat t 1)
         (MapNat (fun i : nat => SubstTerm 0 v (CoordNat t i))
            (RangeNat 2 (LengthNat t - 2)))) t) as [k H].
    rewrite LengthLop, LengthMapNat, LengthRangeNat.
    rewrite Nat.add_comm, Nat.sub_add. reflexivity.
    exact tlen. rewrite LengthLop.
    rewrite LengthMapNat, LengthRangeNat, ttrunc.
    unfold Lop. simpl. rewrite TailConsNat, TailConsNat.
    rewrite <- (LengthRangeNat (LengthNat t - 2) 2) at 2.
    apply MapNatTruncated. exact H0.
    destruct H.
    rewrite LengthLop, LengthMapNat, LengthRangeNat in H.
    rewrite Nat.add_comm, Nat.sub_add in H. 2: exact tlen.
    destruct k. exfalso.
    unfold Lop in H1. rewrite CoordConsHeadNat in H1.
    contradict H1. symmetry. exact top.
    destruct k. 
    unfold Lop in H1. rewrite CoordConsTailNat, CoordConsHeadNat in H1.
    contradict H1. reflexivity.
    assert (k < LengthNat t - 2) as H2.
    { apply le_S_n, le_S_n.
      change (S (S (LengthNat t - 2))) with (2+(LengthNat t -2)).
      rewrite Nat.add_comm, Nat.sub_add. exact H. exact tlen. }
    exists k. split.
    rewrite Minus.pred_of_minus_stt.
    rewrite Minus.pred_of_minus_stt. 
    rewrite <- Nat.sub_add_distr. exact H2.
    rewrite CoordNat_op, CoordMapNat, CoordRangeNat in H1.
    apply Nat.eqb_neq in H1. change (2+k) with (S (S k)) in H1.
    rewrite H1. reflexivity.
    exact H2. rewrite LengthRangeNat. exact H2.
  - intros [j [H0 H1]].
    apply Bool.negb_true_iff, Nat.eqb_neq in H1.
    destruct (SubstTerm 0 v t =? t) eqn:des. 2: reflexivity.
    exfalso. apply Nat.eqb_eq in des.
    rewrite SubstTerm_step in des.
    unfold TreeFoldNatRec in des.
    destruct (le_lt_dec (LengthNat t) 0).
    inversion l. rewrite (CoordNatAboveLength _ _ l) in top.
    discriminate top.
    rewrite Minus.pred_of_minus_stt in H0.
    rewrite Minus.pred_of_minus_stt in H0.
    rewrite <- Nat.sub_add_distr in H0. 
    unfold SubstTermRec in des. rewrite top in des.
    apply (f_equal (fun n => CoordNat n (S (S j)))) in des.
    rewrite CoordNat_op, CoordMapNat, CoordRangeNat in des.
    contradict H1. exact des. exact H0.
    rewrite LengthRangeNat. exact H0.
Qed.

Lemma VarOccursInTerm_const : forall v c,
    VarOccursInTerm v (Lconst c) = false.
Proof.
  intros. unfold Lconst.
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite SubstTerm_op. change (LengthNat NilNat) with 0. simpl.
  rewrite MapNilNat. reflexivity.
Qed.

Lemma VarOccursInTerm_op1 : forall v o a,
    VarOccursInTerm v (Lop1 o a) = VarOccursInTerm v a.
Proof.
  intros. unfold VarOccursInTerm. apply f_equal.
  unfold Lop1.
  rewrite SubstTerm_op, MapConsNat, MapNilNat. 
  destruct (SubstTerm 0 v a =? a) eqn:des.
  - apply Nat.eqb_eq in des. rewrite des. apply Nat.eqb_refl.
  - apply Nat.eqb_neq. intro abs.
    apply (f_equal (fun n => CoordNat n 2)) in abs.
    rewrite CoordNat_op, CoordNat_op in abs.
    rewrite CoordConsHeadNat, CoordConsHeadNat in abs.
    apply Nat.eqb_neq in des. contradiction.
Qed.

Lemma VarOccursInTerm_op2 : forall v o a b,
    VarOccursInTerm v (Lop2 o a b)
    = (VarOccursInTerm v a || VarOccursInTerm v b)%bool.
Proof.
  intros. unfold VarOccursInTerm. 
  unfold Lop2. rewrite SubstTerm_op.
  rewrite MapConsNat, MapConsNat, MapNilNat.
  destruct (SubstTerm 0 v a =? a) eqn:des.
  - simpl. apply f_equal. apply Nat.eqb_eq in des. rewrite des. clear des.
    destruct (SubstTerm 0 v b =? b) eqn:des.
    + apply Nat.eqb_eq in des. rewrite des. apply Nat.eqb_refl.
    + apply Nat.eqb_neq. intro abs.
      apply (f_equal (fun n => CoordNat n 3)) in abs.
      rewrite CoordNat_op, CoordNat_op in abs.
      rewrite CoordConsTailNat, CoordConsHeadNat in abs.
      rewrite CoordConsTailNat, CoordConsHeadNat in abs.
      apply Nat.eqb_neq in des. contradiction.
  - apply Bool.negb_true_iff. apply Nat.eqb_neq. intro abs.
    apply (f_equal (fun n => CoordNat n 2)) in abs.
    rewrite CoordNat_op, CoordNat_op in abs.
    rewrite CoordConsHeadNat, CoordConsHeadNat in abs.
    apply Nat.eqb_neq in des. contradiction.
Qed.

Lemma VarOccursInTerm_var : forall v t,
    VarOccursInTerm v (Lvar t) = Nat.eqb v t.
Proof.
  intros. unfold VarOccursInTerm.
  rewrite SubstTerm_var, (Nat.eqb_sym t v).
  destruct (v =? t).
  2: rewrite Nat.eqb_refl; reflexivity.
  apply Bool.negb_true_iff.
  pose proof (LengthPositive (Lvar t)).
  rewrite LengthLvar in H.
  destruct (Lvar t). 2: reflexivity.
  exfalso. apply (Nat.lt_irrefl 0), H.
  apply le_n_S, le_S, Nat.le_refl.
Qed.

(* Ill-formed propositions are truncated by Subst, so all variables seem
   to occur free in them. *)
Definition VarOccursFreeInFormula (v f : nat) : bool := negb (Nat.eqb (Subst 0 v f) f).

(* This Prop is actually a decidable bool *)
Definition IsClosedFormula (f : nat) : Prop :=
  forall v:nat, VarOccursFreeInFormula v f = false.

Lemma VarOccursFreeInFormula_not : forall v f,
    VarOccursFreeInFormula v (Lnot f) = VarOccursFreeInFormula v f.
Proof.
  intros.
  unfold VarOccursFreeInFormula.
  rewrite Subst_not. apply f_equal.
  destruct (Subst 0 v f =? f) eqn:des.
  apply Nat.eqb_eq in des. rewrite des, Nat.eqb_refl. reflexivity.
  apply Nat.eqb_neq. intro abs.
  assert (CoordNat (Lnot (Subst 0 v f)) 1 = CoordNat (Lnot f) 1).
  rewrite abs. reflexivity.
  rewrite CoordNat_not_1, CoordNat_not_1 in H.
  rewrite H, Nat.eqb_refl in des. discriminate.
Qed.

Lemma VarOccursFreeInFormula_implies : forall v f g,
    VarOccursFreeInFormula v (Limplies f g)
    = (VarOccursFreeInFormula v f || VarOccursFreeInFormula v g)%bool.
Proof.
  intros.
  unfold VarOccursFreeInFormula.
  rewrite Subst_implies.
  destruct (Subst 0 v f =? f) eqn:desf.
  apply Nat.eqb_eq in desf. rewrite desf.
  destruct (Subst 0 v g =? g) eqn:desg.
  apply Nat.eqb_eq in desg. rewrite desg.
  rewrite Nat.eqb_refl. reflexivity.
  apply Bool.negb_true_iff, Nat.eqb_neq. intro abs.
  assert (CoordNat (Limplies f (Subst 0 v g)) 2 = CoordNat (Limplies f g) 2).
  rewrite abs. reflexivity.
  rewrite CoordNat_implies_2, CoordNat_implies_2 in H.
  rewrite H, Nat.eqb_refl in desg. discriminate.
  apply Bool.negb_true_iff, Nat.eqb_neq. intro abs.
  assert (CoordNat (Limplies (Subst 0 v f) (Subst 0 v g)) 1 = CoordNat (Limplies f g) 1).
  rewrite abs. reflexivity.
  rewrite CoordNat_implies_1, CoordNat_implies_1 in H.
  rewrite H, Nat.eqb_refl in desf. discriminate.
Qed.

Lemma VarOccursFreeInFormula_or : forall v f g,
    VarOccursFreeInFormula v (Lor f g)
    = (VarOccursFreeInFormula v f || VarOccursFreeInFormula v g)%bool.
Proof.
  intros.
  unfold VarOccursFreeInFormula.
  rewrite Subst_or.
  destruct (Subst 0 v f =? f) eqn:desf.
  apply Nat.eqb_eq in desf. rewrite desf.
  destruct (Subst 0 v g =? g) eqn:desg.
  apply Nat.eqb_eq in desg. rewrite desg.
  rewrite Nat.eqb_refl. reflexivity.
  apply Bool.negb_true_iff, Nat.eqb_neq. intro abs.
  assert (CoordNat (Lor f (Subst 0 v g)) 2 = CoordNat (Lor f g) 2).
  rewrite abs. reflexivity.
  rewrite CoordNat_or_2, CoordNat_or_2 in H.
  rewrite H, Nat.eqb_refl in desg. discriminate.
  apply Bool.negb_true_iff, Nat.eqb_neq. intro abs.
  assert (CoordNat (Lor (Subst 0 v f) (Subst 0 v g)) 1 = CoordNat (Lor f g) 1).
  rewrite abs. reflexivity.
  rewrite CoordNat_or_1, CoordNat_or_1 in H.
  rewrite H, Nat.eqb_refl in desf. discriminate.
Qed.

Lemma VarOccursFreeInFormula_and : forall v f g,
    VarOccursFreeInFormula v (Land f g)
    = (VarOccursFreeInFormula v f || VarOccursFreeInFormula v g)%bool.
Proof.
  intros.
  unfold VarOccursFreeInFormula.
  rewrite Subst_and.
  destruct (Subst 0 v f =? f) eqn:desf.
  apply Nat.eqb_eq in desf. rewrite desf.
  destruct (Subst 0 v g =? g) eqn:desg.
  apply Nat.eqb_eq in desg. rewrite desg.
  rewrite Nat.eqb_refl. reflexivity.
  apply Bool.negb_true_iff, Nat.eqb_neq. intro abs.
  assert (CoordNat (Land f (Subst 0 v g)) 2 = CoordNat (Land f g) 2).
  rewrite abs. reflexivity.
  rewrite CoordNat_and_2, CoordNat_and_2 in H.
  rewrite H, Nat.eqb_refl in desg. discriminate.
  apply Bool.negb_true_iff, Nat.eqb_neq. intro abs.
  assert (CoordNat (Land (Subst 0 v f) (Subst 0 v g)) 1 = CoordNat (Land f g) 1).
  rewrite abs. reflexivity.
  rewrite CoordNat_and_1, CoordNat_and_1 in H.
  rewrite H, Nat.eqb_refl in desf. discriminate.
Qed.

Lemma VarOccursFreeInFormula_equiv : forall v f g,
    VarOccursFreeInFormula v (Lequiv f g)
    = (VarOccursFreeInFormula v f || VarOccursFreeInFormula v g)%bool.
Proof.
  intros. unfold Lequiv.
  rewrite VarOccursFreeInFormula_and, VarOccursFreeInFormula_implies.
  rewrite VarOccursFreeInFormula_implies.
  destruct (VarOccursFreeInFormula v f), (VarOccursFreeInFormula v g); reflexivity.
Qed. 

Lemma VarOccursFreeInFormula_forallHead : forall v f,
    CoordNat f 0 = LforallHead
    -> VarOccursFreeInFormula v f
      = negb (Lforall (CoordNat f 1) (if CoordNat f 1 =? v then CoordNat f 2
                                      else (Subst 0 v (CoordNat f 2)))
              =? f).
Proof.
  intros.
  unfold VarOccursFreeInFormula.
  rewrite (Subst_forallHead _ _ f H).
  reflexivity.
Qed.

Lemma VarOccursFreeInFormula_forall : forall v k f,
    VarOccursFreeInFormula v (Lforall k f)
    = (negb (Nat.eqb v k) && VarOccursFreeInFormula v f)%bool.
Proof.
  intros.
  unfold VarOccursFreeInFormula.
  rewrite Subst_forall.
  rewrite (Nat.eqb_sym k v). destruct (v =? k).
  rewrite Nat.eqb_refl. reflexivity.
  simpl.
  destruct (Subst 0 v f =? f) eqn:des.
  apply Nat.eqb_eq in des. rewrite des, Nat.eqb_refl. reflexivity.
  apply f_equal, Nat.eqb_neq. intro abs.
  assert (CoordNat (Lforall k (Subst 0 v f)) 2 = CoordNat (Lforall k f) 2).
  rewrite abs. reflexivity.
  rewrite CoordNat_forall_2, CoordNat_forall_2 in H.
  rewrite H, Nat.eqb_refl in des. discriminate.
Qed.

Lemma VarOccursFreeInFormula_existsHead : forall v f,
    CoordNat f 0 = LexistsHead
    -> VarOccursFreeInFormula v f
      = negb (Lexists (CoordNat f 1) (if CoordNat f 1 =? v then CoordNat f 2
                                      else (Subst 0 v (CoordNat f 2)))
              =? f).
Proof.
  intros.
  unfold VarOccursFreeInFormula.
  rewrite (Subst_existsHead _ _ f H).
  reflexivity.
Qed.

Lemma VarOccursFreeInFormula_exists : forall v k f,
    VarOccursFreeInFormula v (Lexists k f)
    = (negb (Nat.eqb v k) && VarOccursFreeInFormula v f)%bool.
Proof.
  intros.
  unfold VarOccursFreeInFormula.
  rewrite Subst_exists.
  rewrite (Nat.eqb_sym k v). destruct (v =? k).
  rewrite Nat.eqb_refl. reflexivity.
  simpl.
  destruct (Subst 0 v f =? f) eqn:des.
  apply Nat.eqb_eq in des. rewrite des, Nat.eqb_refl. reflexivity.
  apply f_equal, Nat.eqb_neq. intro abs.
  assert (CoordNat (Lexists k (Subst 0 v f)) 2 = CoordNat (Lexists k f) 2).
  rewrite abs. reflexivity.
  rewrite CoordNat_exists_2, CoordNat_exists_2 in H.
  rewrite H, Nat.eqb_refl in des. discriminate.
Qed.

Lemma VarOccursFreeInFormula_rel : forall v r args,
    NthTailNat args (LengthNat args) = 0 ->
    (VarOccursFreeInFormula v (Lrel r args) = true
     <-> (exists j, j < LengthNat args /\ VarOccursInTerm v (CoordNat args j) = true)).
Proof.
  intros v r args argstrunc.
  split.
  - intro H. unfold VarOccursFreeInFormula in H.
    apply Bool.negb_true_iff, Nat.eqb_neq in H.
    rewrite Subst_rel in H.
    assert (MapNat (SubstTerm 0 v) args <> args).
    { intro abs. rewrite abs in H. apply H. reflexivity. } clear H.
    apply MapNatDiff in H0.
    destruct H0. exists x. destruct a.
    split. exact H.
    apply Bool.negb_true_iff, Nat.eqb_neq, H0. exact argstrunc.
  - intros [j [H H0]]. unfold VarOccursFreeInFormula.
    apply Bool.negb_true_iff, Nat.eqb_neq.
    intro abs. rewrite Subst_rel in abs.
    unfold VarOccursInTerm in H0.
    apply Bool.negb_true_iff, Nat.eqb_neq in H0.
    contradict H0.
    assert (CoordNat (Lrel r (MapNat (SubstTerm 0 v) args)) (2+j)
            = CoordNat (Lrel r args) (2+j))
      by (rewrite abs; reflexivity).
    rewrite (CoordNat_rel _ _ j), (CoordNat_rel _ _ j) in H0.
    rewrite CoordMapNat in H0.
    exact H0. exact H. 
Qed.

Lemma VarOccursFreeInFormula_rel2 : forall v r a b,
    VarOccursFreeInFormula v (Lrel2 r a b)
    = (VarOccursInTerm v a || VarOccursInTerm v b)%bool.
Proof.
  intros. unfold Lrel2.
  unfold VarOccursFreeInFormula.
  rewrite Subst_rel, MapConsNat, MapConsNat, MapNilNat.
  unfold VarOccursInTerm.
  destruct (SubstTerm 0 v a =? a) eqn:des.
  - simpl. apply f_equal.
    apply Nat.eqb_eq in des. rewrite des. clear des.
    destruct (SubstTerm 0 v b =? b) eqn:des.
    + apply Nat.eqb_eq in des. rewrite des. apply Nat.eqb_refl.
    + apply Nat.eqb_neq. intro abs.
      apply (f_equal (fun n => CoordNat n 3)) in abs.
      rewrite CoordNat_rel, CoordNat_rel in abs.
      rewrite CoordConsTailNat, CoordConsTailNat in abs.
      rewrite CoordConsHeadNat, CoordConsHeadNat in abs.
      apply Nat.eqb_neq in des. contradiction.
  - apply Bool.negb_true_iff, Nat.eqb_neq. intro abs.
    apply (f_equal (fun n => CoordNat n 2)) in abs.
    rewrite CoordNat_rel, CoordNat_rel in abs.
    rewrite CoordConsHeadNat, CoordConsHeadNat in abs.
    apply Nat.eqb_neq in des. contradiction.
Qed.

Lemma SubstTerm_nosubst : forall v t u,
    VarOccursInTerm v t = false    (* i.e. SubstTerm 0 v t = t *)
    -> SubstTerm u v t = t.
Proof.
  intros v.
  apply (Fix lt_wf (fun t => forall u,
    VarOccursInTerm v t = false
    -> SubstTerm u v t = t)).
  intros t IHt u nosubst.
  rewrite SubstTerm_step.
  unfold TreeFoldNatRec.
  apply Bool.negb_false_iff, Nat.eqb_eq in nosubst.
  rewrite SubstTerm_step in nosubst.
  unfold TreeFoldNatRec in nosubst.
  destruct (le_lt_dec (LengthNat t) 0). exact nosubst.
  unfold SubstTermRec.
  unfold SubstTermRec in nosubst.
  destruct (CoordNat t 0) eqn:headT. exact nosubst.
  do 7 (destruct n; [exact nosubst|]).
  destruct n.
  - (* Lop *)
    rewrite <- nosubst at 3. apply f_equal.
    apply MapNatExt. intros k H.
    rewrite LengthRangeNat in H.
    rewrite CoordRangeNat. 2: exact H.
    apply (f_equal (fun a => CoordNat a (S (S k)))) in nosubst.
    rewrite CoordNat_op, CoordMapNat, CoordRangeNat in nosubst.
    rewrite nosubst. apply IHt.
    exact (CoordLower _ _ (LengthPositive _ l)).
    unfold VarOccursInTerm. change (S (S k)) with (2+k).
    rewrite nosubst, Nat.eqb_refl. reflexivity.
    exact H.
    rewrite LengthRangeNat. exact H.
  - (* Lvariable *)
    destruct n. 2: exact nosubst.
    destruct (CoordNat t 1 =? v). 2: reflexivity.
    exfalso. rewrite <- nosubst in headT. inversion headT.
Qed.

Lemma Subst_nosubst : forall f v u,
    VarOccursFreeInFormula v f = false
    -> Subst u v f = f.
Proof.
  apply (Fix lt_wf (fun f => forall v u,
                        VarOccursFreeInFormula v f = false -> Subst u v f = f)).
  intros f IHf v u nosubst.
  rewrite Subst_step.
  unfold TreeFoldNatRec.
  apply Bool.negb_false_iff, Nat.eqb_eq in nosubst.
  rewrite Subst_step in nosubst.
  unfold TreeFoldNatRec in nosubst.
  destruct (le_lt_dec (LengthNat f) 0). exact nosubst.
  unfold SubstRec. unfold SubstRec in nosubst.
  destruct (CoordNat f 0) eqn:headF. exact nosubst.
  destruct n.
  (* Lnot *)
  rewrite IHf.
  rewrite IHf in nosubst. exact nosubst.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nosubst at 2.
  rewrite CoordNat_not_1. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nosubst at 2.
  rewrite CoordNat_not_1. reflexivity.
  destruct n.
  (* Limplies *)
  rewrite IHf, IHf. rewrite IHf, IHf in nosubst. exact nosubst.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nosubst at 2.
  rewrite CoordNat_implies_2. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nosubst at 2.
  rewrite CoordNat_implies_1. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nosubst at 2.
  rewrite CoordNat_implies_2. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nosubst at 2.
  rewrite CoordNat_implies_1. reflexivity.
  destruct n.
  (* Lor *)
  rewrite IHf, IHf. rewrite IHf, IHf in nosubst. exact nosubst.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nosubst at 2.
  rewrite CoordNat_or_2. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nosubst at 2.
  rewrite CoordNat_or_1. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nosubst at 2.
  rewrite CoordNat_or_2. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nosubst at 2.
  rewrite CoordNat_or_1. reflexivity.
  destruct n.
  (* Land *)
  rewrite IHf, IHf. rewrite IHf, IHf in nosubst. exact nosubst.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nosubst at 2.
  rewrite CoordNat_and_2. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nosubst at 2.
  rewrite CoordNat_and_1. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nosubst at 2.
  rewrite CoordNat_and_2. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nosubst at 2.
  rewrite CoordNat_and_1. reflexivity.
  destruct n.
  (* Lforall *)
  destruct (CoordNat f 1 =? v) eqn:des. exact nosubst.
  rewrite IHf.
  rewrite IHf in nosubst. exact nosubst.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nosubst at 2.
  rewrite CoordNat_forall_2. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nosubst at 2.
  rewrite CoordNat_forall_2. reflexivity.
  destruct n.
  (* Lexists *)
  destruct (CoordNat f 1 =? v) eqn:des. exact nosubst.
  rewrite IHf.
  rewrite IHf in nosubst. exact nosubst.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nosubst at 2.
  rewrite CoordNat_exists_2. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nosubst at 2.
  rewrite CoordNat_exists_2. reflexivity.
  destruct n.
  (* Lrel *)
  2: exact nosubst.
  clear IHf.
  rewrite <- nosubst at 3.
  apply f_equal.
  assert (MapNat (SubstTerm 0 v) (TailNat (TailNat f)) = TailNat (TailNat f)) as H.
  { apply (f_equal (fun n => TailNat (TailNat n))) in nosubst.
    unfold Lrel in nosubst.
    rewrite TailConsNat, TailConsNat in nosubst. exact nosubst. }
  rewrite H.
  apply TruncatedEqNat.
  rewrite LengthMapNat. reflexivity.
  rewrite LengthMapNat, MapNatTruncated.
  rewrite <- H at 1. rewrite MapNatTruncated. reflexivity.
  intros j H0. rewrite LengthMapNat in H0.
  rewrite CoordMapNat. 2: exact H0.
  rewrite CoordTailNat, CoordTailNat.
  rewrite SubstTerm_nosubst. reflexivity.
  apply Bool.negb_false_iff, Nat.eqb_eq.
  apply (f_equal (fun n => CoordNat n (S (S j)))) in nosubst.
  rewrite CoordNat_rel, CoordMapNat in nosubst. exact nosubst. exact H0.
Qed.

Lemma SubstSubstTermNested : forall term,
    IsLterm term = true
    -> forall t u v w, VarOccursInTerm v term = false
    -> SubstTerm t v (SubstTerm u w term) = SubstTerm (SubstTerm t v u) w term.
Proof.
  apply (Lterm_rect (fun term => forall t u v w, VarOccursInTerm v term = false
    -> SubstTerm t v (SubstTerm u w term) = SubstTerm (SubstTerm t v u) w term)).
  - (* Lvar *)
    intros. rewrite SubstTerm_var, SubstTerm_var.
    destruct (v =? w). reflexivity.
    rewrite VarOccursInTerm_var in H.
    rewrite SubstTerm_var, Nat.eqb_sym, H. reflexivity.
  - (* Lop *)
    intros. rewrite SubstTerm_op, SubstTerm_op, SubstTerm_op.
    apply f_equal. rewrite MapMapNat.
    apply MapNatExt.
    intros n H0. apply IHterms. exact H0.
    apply Bool.negb_false_iff, Nat.eqb_eq in H.
    apply Bool.negb_false_iff, Nat.eqb_eq.
    rewrite SubstTerm_op in H.
    apply (f_equal (fun a => CoordNat a (S (S n)))) in H.
    rewrite CoordNat_op, CoordNat_op, CoordMapNat in H. exact H. exact H0.
Qed.

Lemma SubstTermsNested : forall (r terms t u v w : nat),
    (forall i : nat, i < LengthNat terms -> IsLterm (CoordNat terms i) = true)
    -> VarOccursFreeInFormula v (Lrel r terms) = false
    -> MapNat (SubstTerm t v) (MapNat (SubstTerm u w) terms)
      = MapNat (SubstTerm (SubstTerm t v u) w) terms.
Proof.
  intros. rewrite MapMapNat.
  apply MapNatExt. intros j H1.
  rewrite SubstSubstTermNested. reflexivity.
  apply H. exact H1.
  apply Bool.negb_false_iff, Nat.eqb_eq in H0.
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite Subst_rel in H0.
  apply (f_equal (fun a => CoordNat a (S (S j)))) in H0.
  rewrite CoordNat_rel, CoordNat_rel, CoordMapNat in H0. exact H0. exact H1.
Qed.

Lemma VarOccursInTermVarChange : forall term,
    IsLterm term = true
    -> forall v w, VarOccursInTerm v term = false
    -> VarOccursInTerm v (SubstTerm (Lvar v) w term) = VarOccursInTerm w term.
Proof.
  apply (Lterm_rect (fun term => forall v w, VarOccursInTerm v term = false
    -> VarOccursInTerm v (SubstTerm (Lvar v) w term) = VarOccursInTerm w term)).
  - (* Lvar *)
    intros. rewrite SubstTerm_var, VarOccursInTerm_var.
    destruct (v =? w) eqn:des.
    apply Nat.eqb_eq in des. subst w.
    rewrite VarOccursInTerm_var, Nat.eqb_refl, Nat.eqb_refl. reflexivity.
    rewrite H, Nat.eqb_sym, des. reflexivity.
  - (* Lop *)
    intros.
    assert (forall a b : bool, ((a = true) <-> (b = true)) -> a = b).
    { intros. destruct H0. destruct a. symmetry. apply H0. reflexivity.
      destruct b. 2: reflexivity. apply H1. reflexivity. }
    apply H0. clear H0.
    rewrite VarOccursInTerm_opHead, VarOccursInTerm_opHead.
    rewrite SubstTerm_op, LengthLop, LengthMapNat, LengthLop.
    split; intros [j [H0 H1]]; exists j; split.
    + exact H0.
    + simpl in H0.
      rewrite CoordNat_op, CoordMapNat in H1.
      2: exact H0.
      rewrite CoordNat_op.
      specialize (IHterms j H0) as [_ IHterms].
      rewrite IHterms in H1.
      exact H1.
      apply Bool.negb_false_iff, Nat.eqb_eq in H.
      apply (f_equal (fun a => CoordNat a (S (S j)))) in H.
      apply Bool.negb_false_iff, Nat.eqb_eq.
      rewrite CoordNat_op, SubstTerm_op, CoordNat_op in H.
      rewrite CoordMapNat in H.
      exact H. exact H0. 
    + exact H0.
    + simpl in H0.
      rewrite CoordNat_op, CoordMapNat. 2: exact H0.
      rewrite CoordNat_op in H1.
      specialize (IHterms j H0) as [_ IHterms]. rewrite IHterms.
      exact H1.
      apply Bool.negb_false_iff, Nat.eqb_eq in H.
      apply (f_equal (fun a => CoordNat a (S (S j)))) in H.
      apply Bool.negb_false_iff, Nat.eqb_eq.
      rewrite CoordNat_op, SubstTerm_op, CoordNat_op in H.
      rewrite CoordMapNat in H.
      exact H. exact H0. 
    + unfold Lop. rewrite CoordConsHeadNat. reflexivity. 
    + change 2 with (2+0). rewrite LengthLop.
      apply Nat.add_le_mono_l, le_0_n.
    + rewrite LengthLop. unfold Lop.
      simpl. rewrite TailConsNat, TailConsNat. exact termsTrunc.
    + rewrite SubstTerm_op. unfold Lop.
      rewrite CoordConsHeadNat. reflexivity.
    + change 2 with (2+0). rewrite SubstTerm_op, LengthLop.
      apply Nat.add_le_mono_l, le_0_n.
    + rewrite SubstTerm_op, LengthLop, LengthMapNat.
      simpl. unfold Lop at 1; rewrite TailConsNat, TailConsNat.
      apply MapNatTruncated.
Qed. 

Fixpoint MaxVarLopTerm (t i : nat) (rec : nat -> nat) {struct i} : nat :=
  match i with
  | O => 0
  | 1 => 0
  | 2 => 0
  | S j => Nat.max (MaxVarLopTerm t j rec) (rec j)
  end.

Definition MaxVarTermRec (t : nat) (rec : nat -> nat) : nat :=
  match CoordNat t 0 with
  | LvarHead => CoordNat t 1
  | LopHead => MaxVarLopTerm t (LengthNat t) rec
  | _ => 0
  end.
Definition MaxVarTerm : nat -> nat := TreeFoldNat MaxVarTermRec O.

Lemma MaxVarLopTerm_spec : forall i t rec v,
    MaxVarLopTerm t i rec <= v
    <-> forall j, j < pred (pred i) -> rec (S (S j)) <= v.
Proof.
  induction i.
  - split. intros. inversion H0. intros. apply le_0_n.
  - intros t rec v. specialize (IHi t rec v). split.
    + intros. simpl in H. destruct i. inversion H0.
      destruct i. inversion H0.
      simpl in H0.
      apply Nat.le_succ_r in H0. destruct H0.
      * destruct IHi as [IHi _]. apply IHi.
        refine (Nat.le_trans _ _ _ _ H).
        apply Nat.le_max_l. assumption.
      * inversion H0. subst j.
        refine (Nat.le_trans _ _ _ _ H).
        apply Nat.le_max_r.
    + intro H. destruct IHi as [_ IHi]. simpl.
      destruct i. apply le_0_n. destruct i. apply le_0_n.
      apply Nat.max_lub. apply IHi.
      intros. apply H. simpl. simpl in H0.
      apply le_S, H0.
      apply H. apply Nat.le_refl.
Qed.

Lemma MaxVarTerm_step : forall t,
    MaxVarTerm t = TreeFoldNatRec MaxVarTermRec O t (fun k _ => MaxVarTerm k).
Proof.
  intros. unfold MaxVarTerm, TreeFoldNat.
  rewrite Fix_eq. reflexivity.
  intros. unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat x) 0). reflexivity.
  unfold MaxVarTermRec. destruct (CoordNat x 0). reflexivity.
  repeat (destruct n; [reflexivity|]).
  destruct n. 2: destruct n; reflexivity.
  generalize (LengthNat x). induction n.
  reflexivity.
  simpl. rewrite IHn, H. reflexivity.
Qed.

Lemma MaxVarTerm_var : forall v,
    MaxVarTerm (Lvar v) = v.
Proof.
  intros. rewrite MaxVarTerm_step.
  unfold TreeFoldNatRec. rewrite LengthLvar. simpl.
  unfold MaxVarTermRec, Lvar.
  rewrite CoordConsHeadNat, CoordConsTailNat, CoordConsHeadNat.
  reflexivity.
Qed.

Lemma MaxVarTerm_opHead : forall term,
    CoordNat term 0 = LopHead
    -> MaxVarTerm term
      = MaxVarLopTerm term (LengthNat term)
                      (fun i : nat => MaxVarTerm (CoordNat term i)).
Proof.
  intros. rewrite MaxVarTerm_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat term) 0).
  rewrite CoordNatAboveLength in H. discriminate. exact l.
  unfold MaxVarTermRec. rewrite H. reflexivity.
Qed.

Lemma MaxVarTerm_op : forall o terms,
    MaxVarTerm (Lop o terms)
    = MaxVarLopTerm (Lop o terms) (S (S (LengthNat terms)))
                    (fun i : nat => MaxVarTerm (CoordNat (Lop o terms) i)).
Proof.
  intros. rewrite MaxVarTerm_step.
  unfold TreeFoldNatRec. rewrite LengthLop.
  simpl.
  unfold MaxVarTermRec, Lop.
  rewrite CoordConsHeadNat.
  rewrite LengthConsNat, LengthConsNat.
  reflexivity.
Qed.

Lemma MaxVarTermDoesNotOccur : forall v t,
    MaxVarTerm t < v
    -> IsLterm t = true
    -> VarOccursInTerm v t = false.
Proof.
  intros. revert t H0 v H.
  apply (Lterm_rect (fun t => forall v : nat,
                         MaxVarTerm t < v -> VarOccursInTerm v t = false)).
  - (* Lvar *)
    intros.
    rewrite VarOccursInTerm_var. rewrite MaxVarTerm_var in H.
    apply Nat.eqb_neq. intro abs. rewrite <- abs in H.
    exact (Nat.lt_irrefl v0 H).
  - (* Lop *)
    intros. rewrite MaxVarTerm_op in H.
    destruct (VarOccursInTerm v (Lop o terms)) eqn:des. 2: reflexivity.
    apply VarOccursInTerm_opHead in des.
    destruct des as [j [H1 H2]].
    rewrite LengthLop in H1. simpl in H1.
    destruct v. inversion H. apply le_S_n in H.
    pose proof (MaxVarLopTerm_spec
                  (S (S (LengthNat terms))) (Lop o terms)
                  (fun i : nat => MaxVarTerm (CoordNat (Lop o terms) i)) v) as [H0 _].
    specialize (H0 H j H1). 
    specialize (IHterms j H1) as [_ IHterms].
    rewrite <- (IHterms (S v)).
    rewrite CoordNat_op in H2.
    symmetry. exact H2.
    rewrite CoordNat_op in H0. apply le_n_S. exact H0.
    unfold Lop. rewrite CoordConsHeadNat. reflexivity.
    change 2 with (2+0). rewrite LengthLop.
    apply Nat.add_le_mono_l, le_0_n.
    rewrite LengthLop. unfold Lop. simpl.
    rewrite TailConsNat, TailConsNat. exact termsTrunc. 
Qed.

Lemma SubstAboveMaxVarTerm : forall u v t,
    MaxVarTerm t < v
    -> IsLterm t = true
    -> SubstTerm u v t = t.
Proof.
  intros. apply SubstTerm_nosubst.
  apply MaxVarTermDoesNotOccur; assumption.
Qed.

Definition MaxVarRec (f : nat) (rec : nat -> nat) : nat :=
  match CoordNat f 0 with
  | LnotHead => rec 1
  | LimpliesHead
  | LorHead
  | LandHead => Nat.max (rec 1) (rec 2)
  | LforallHead
  | LexistsHead => Nat.max (CoordNat f 1) (rec 2)
  | LrelHead => MaxVarTerm (Lop 0 (TailNat (TailNat f)))
  | _ => 0
  end.

Definition MaxVar : nat -> nat := TreeFoldNat MaxVarRec O.

Lemma MaxVar_step : forall prop,
    MaxVar prop = TreeFoldNatRec MaxVarRec O prop (fun k _ => MaxVar k).
Proof.
  intros. 
  unfold MaxVar, TreeFoldNat. rewrite Fix_eq.
  reflexivity.
  intros x f g H. unfold TreeFoldNatRec, MaxVarRec.
  destruct (le_lt_dec (LengthNat x) 0). reflexivity.
  destruct (CoordNat x 0). reflexivity.
  destruct n. rewrite H. reflexivity.
  destruct n. rewrite H, H. reflexivity.
  destruct n. rewrite H, H. reflexivity.
  destruct n. rewrite H, H. reflexivity.
  destruct n. rewrite H. reflexivity.
  destruct n. rewrite H. reflexivity.
  destruct n. reflexivity. reflexivity.
Qed.

Lemma MaxVar_not : forall f, MaxVar (Lnot f) = MaxVar f.
Proof.
  intros. rewrite MaxVar_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lnot f)) 0).
  rewrite LengthLnot in l. inversion l.
  unfold MaxVarRec, Lnot.
  rewrite CoordConsHeadNat.
  rewrite CoordConsTailNat, CoordConsHeadNat.
  reflexivity.
Qed.

Lemma MaxVar_implies : forall f g,
    MaxVar (Limplies f g) = Nat.max (MaxVar f) (MaxVar g).
Proof.
  intros. rewrite MaxVar_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Limplies f g)) 0).
  rewrite LengthLimplies in l. inversion l.
  unfold MaxVarRec. unfold Limplies at 1.
  rewrite CoordConsHeadNat.
  rewrite CoordNat_implies_2, CoordNat_implies_1.
  reflexivity.
Qed.

Lemma MaxVar_or : forall f g,
    MaxVar (Lor f g) = Nat.max (MaxVar f) (MaxVar g).
Proof.
  intros. rewrite MaxVar_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lor f g)) 0).
  rewrite LengthLor in l. inversion l.
  unfold MaxVarRec. unfold Lor at 1.
  rewrite CoordConsHeadNat.
  rewrite CoordNat_or_2, CoordNat_or_1.
  reflexivity.
Qed.

Lemma MaxVar_and : forall f g,
    MaxVar (Land f g) = Nat.max (MaxVar f) (MaxVar g).
Proof.
  intros. rewrite MaxVar_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Land f g)) 0).
  rewrite LengthLand in l. inversion l.
  unfold MaxVarRec. unfold Land at 1.
  rewrite CoordConsHeadNat.
  rewrite CoordNat_and_2, CoordNat_and_1.
  reflexivity.
Qed.

Lemma MaxVar_equiv : forall f g,
    MaxVar (Lequiv f g) = Nat.max (MaxVar f) (MaxVar g).
Proof.
  intros. unfold Lequiv.
  rewrite MaxVar_and, MaxVar_implies, MaxVar_implies.
  rewrite (Nat.max_comm (MaxVar f)), Nat.max_id. reflexivity.
Qed. 

Lemma MaxVar_forall : forall v f, MaxVar (Lforall v f) = Nat.max v (MaxVar f).
Proof.
  intros. rewrite MaxVar_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lforall v f)) 0).
  rewrite LengthLforall in l. inversion l.
  unfold MaxVarRec. unfold Lforall at 1.
  rewrite CoordConsHeadNat.
  rewrite CoordNat_forall_1, CoordNat_forall_2.
  reflexivity.
Qed.

Lemma MaxVar_exists : forall v f, MaxVar (Lexists v f) = Nat.max v (MaxVar f).
Proof.
  intros. rewrite MaxVar_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lexists v f)) 0).
  rewrite LengthLexists in l. inversion l.
  unfold MaxVarRec. unfold Lexists at 1.
  rewrite CoordConsHeadNat.
  rewrite CoordNat_exists_1, CoordNat_exists_2.
  reflexivity.
Qed.

Lemma MaxVar_rel : forall r terms,
    MaxVar (Lrel r terms) = MaxVarTerm (Lop 0 terms).
Proof.
  intros. rewrite MaxVar_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lrel r terms)) 0).
  rewrite LengthLrel in l. inversion l.
  unfold MaxVarRec. unfold Lrel at 1.
  rewrite CoordConsHeadNat.
  unfold Lrel; rewrite TailConsNat, TailConsNat.
  reflexivity.
Qed.

Lemma MaxVar_rel2 : forall r f g,
    MaxVar (Lrel2 r f g) = Nat.max (MaxVarTerm f) (MaxVarTerm g).
Proof.
  intros. unfold Lrel2. rewrite MaxVar_rel.
  rewrite MaxVarTerm_op. rewrite LengthConsNat, LengthConsNat.
  change (LengthNat NilNat) with 0.
  simpl.
  rewrite CoordNat_op, CoordNat_op. 
  rewrite CoordConsHeadNat, CoordConsTailNat, CoordConsHeadNat.
  reflexivity.
Qed.

Lemma MaxVar_rel_lower : forall r terms i,
    i < LengthNat terms
    -> MaxVarTerm (CoordNat terms i) <= MaxVar (Lrel r terms).
Proof.
  intros.
  rewrite MaxVar_rel, MaxVarTerm_op.
  pose proof (MaxVarLopTerm_spec
                (S (S (LengthNat terms))) (Lop 0 terms)
                (fun i0 : nat => MaxVarTerm (CoordNat (Lop 0 terms) i0))
                (MaxVarLopTerm (Lop 0 terms) (S (S (LengthNat terms)))
                               (fun i0 : nat => MaxVarTerm (CoordNat (Lop 0 terms) i0))))
    as [H0 _].
  specialize (H0 (Nat.le_refl _) i H).
  unfold Lop in H0 at 1.
  rewrite CoordConsTailNat, CoordConsTailNat in H0.
  exact H0.
Qed.

(* This does not extend to ill-formed formulas, because
   (LnotHead a b c) is truncated by Subst to (LnotHead a), which is
   a modification. *)
Lemma MaxVarDoesNotOccurFree : forall f,
    IsLproposition f = true
    -> forall v, MaxVar f < v
    -> VarOccursFreeInFormula v f = false.
Proof.
  apply (Lproposition_rect
             (fun f => forall v, MaxVar f < v
                    -> VarOccursFreeInFormula v f = false)). 
  - (* Lrel *)
    intros. 
    destruct (VarOccursFreeInFormula v (Lrel r terms)) eqn:des. 2: reflexivity.
    apply VarOccursFreeInFormula_rel in des.
    destruct des as [j [des occur]].
    pose proof (MaxVarTermDoesNotOccur v (CoordNat terms j)) as H1.
    rewrite occur in H1. apply H1.
    refine (Nat.le_lt_trans _ _ _ _ H).
    apply MaxVar_rel_lower, des.
    apply elemterms, des. exact termsTrunc.
  - (* Lnot *)
    intros.
    rewrite VarOccursFreeInFormula_not.
    apply IHprop. rewrite MaxVar_not in H. exact H.
  - (* Limplies *)
    intros.
    rewrite VarOccursFreeInFormula_implies.
    rewrite MaxVar_implies in H.
    rewrite IHg, IHh. reflexivity.
    exact (Nat.le_lt_trans _ _ _ (Nat.le_max_r _ _) H).
    exact (Nat.le_lt_trans _ _ _ (Nat.le_max_l _ _) H).
  - (* Lor *)
    intros.
    rewrite VarOccursFreeInFormula_or.
    rewrite MaxVar_or in H.
    rewrite IHg, IHh. reflexivity.
    exact (Nat.le_lt_trans _ _ _ (Nat.le_max_r _ _) H).
    exact (Nat.le_lt_trans _ _ _ (Nat.le_max_l _ _) H).
  - (* Land *)
    intros.
    rewrite VarOccursFreeInFormula_and.
    rewrite MaxVar_and in H.
    rewrite IHg, IHh. reflexivity.
    exact (Nat.le_lt_trans _ _ _ (Nat.le_max_r _ _) H).
    exact (Nat.le_lt_trans _ _ _ (Nat.le_max_l _ _) H).
  - (* Lforall *)
    intros. rewrite VarOccursFreeInFormula_forall.
    rewrite MaxVar_forall in H.
    destruct (v0 =? v) eqn:des. reflexivity. simpl.
    apply IHprop.
    exact (Nat.le_lt_trans _ _ _ (Nat.le_max_r _ _) H).
  - (* Lexists *)
    intros. rewrite VarOccursFreeInFormula_exists.
    rewrite MaxVar_exists in H.
    destruct (v0 =? v) eqn:des. reflexivity. simpl.
    apply IHprop.
    exact (Nat.le_lt_trans _ _ _ (Nat.le_max_r _ _) H).
Qed.

Lemma MaxVarTerm_Subst : forall term u v,
    MaxVarTerm (SubstTerm u v term) <= Nat.max (MaxVarTerm u) (MaxVarTerm term).
Proof.
  apply (Fix lt_wf (fun term => forall u v,
    MaxVarTerm (SubstTerm u v term) <= Nat.max (MaxVarTerm u) (MaxVarTerm term))).
  intros term IHterm u v.
  rewrite SubstTerm_step, (MaxVarTerm_step term).
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat term) 0). apply le_0_n.
  unfold SubstTermRec, MaxVarTermRec.
  destruct (CoordNat term 0) eqn:headTerm. apply le_0_n.
  do 7 (destruct n; [apply le_0_n|]).
  destruct n.
  - (* Lop *)
    rewrite MaxVarTerm_opHead, LengthLop, LengthMapNat, LengthRangeNat.
    2: unfold Lop; rewrite CoordConsHeadNat; reflexivity.
    apply MaxVarLopTerm_spec. intros j H.
    simpl in H.
    destruct (LengthNat term) eqn:lenTerm. inversion H.
    destruct n. inversion H. 
    rewrite CoordNat_op, CoordMapNat.
    2: rewrite LengthRangeNat; exact H.
    rewrite CoordRangeNat. 2: exact H.
    apply (Nat.le_trans _ (Nat.max (MaxVarTerm u) (MaxVarTerm (CoordNat term (S (S j)))))).
    apply IHterm.
    rewrite <- lenTerm in l.
    exact (CoordLower _ _ (LengthPositive _ l)).
    apply Nat.max_lub. apply Nat.le_max_l.
    refine (Nat.le_trans _ _ _ _ (Nat.le_max_r _ _)).
    destruct (le_lt_dec (MaxVarTerm (CoordNat term (S (S j))))
                        (MaxVarLopTerm term (S (S n)) (fun i : nat => MaxVarTerm (CoordNat term i)))).
    exact l0. exfalso.
    destruct (MaxVarTerm (CoordNat term (S (S j)))) eqn:des. inversion l0.
    apply le_S_n in l0. rewrite MaxVarLopTerm_spec in l0.
    simpl in H. rewrite Nat.sub_0_r in H.
    specialize (l0 j H). rewrite des in l0.
    exact (Nat.lt_irrefl _ l0).
  - (* Lvar *)
    destruct n.
    2: apply le_0_n.
    destruct (CoordNat term 1 =? v). apply Nat.le_max_l.
    rewrite MaxVarTerm_step.
    unfold TreeFoldNatRec.
    destruct (le_lt_dec (LengthNat term) 0). apply le_0_n.
    unfold MaxVarTermRec. rewrite headTerm. apply Nat.le_max_r.
Qed.

(* If u is closed and v is the greatest variable of f, the inequality is strict. *)
Lemma MaxVar_Subst : forall prop u v,
    MaxVar (Subst u v prop) <= Nat.max (MaxVarTerm u) (MaxVar prop).
Proof.
  apply (Fix lt_wf (fun prop => forall u v,
    MaxVar (Subst u v prop) <= Nat.max (MaxVarTerm u) (MaxVar prop))).
  intros prop IHprop u v.
  rewrite Subst_step, (MaxVar_step prop).
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat prop) 0). apply le_0_n.
  unfold SubstRec, MaxVarRec.
  destruct (CoordNat prop 0) eqn:headProp. apply le_0_n.
  destruct n.
  (* Lnot *)
  rewrite MaxVar_not. apply IHprop.
  exact (CoordLower _ _ (LengthPositive _ l)). destruct n.
  (* Limplies *)
  rewrite MaxVar_implies.
  apply Nat.max_lub.
  apply (Nat.le_trans _ (Nat.max (MaxVarTerm u) (MaxVar (CoordNat prop 1)))).
  apply IHprop.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Nat.max_lub. apply Nat.le_max_l.
  rewrite Nat.max_comm, <- Nat.max_assoc. apply Nat.le_max_l.
  apply (Nat.le_trans _ (Nat.max (MaxVarTerm u) (MaxVar (CoordNat prop 2)))).
  apply IHprop.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Nat.max_lub. apply Nat.le_max_l.
  rewrite Nat.max_comm, (Nat.max_comm (MaxVar (CoordNat prop 1))).
  rewrite <- Nat.max_assoc. apply Nat.le_max_l. destruct n.
  (* Lor *)
  rewrite MaxVar_or.
  apply Nat.max_lub.
  apply (Nat.le_trans _ (Nat.max (MaxVarTerm u) (MaxVar (CoordNat prop 1)))).
  apply IHprop.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Nat.max_lub. apply Nat.le_max_l.
  rewrite Nat.max_comm, <- Nat.max_assoc. apply Nat.le_max_l.
  apply (Nat.le_trans _ (Nat.max (MaxVarTerm u) (MaxVar (CoordNat prop 2)))).
  apply IHprop.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Nat.max_lub. apply Nat.le_max_l.
  rewrite Nat.max_comm, (Nat.max_comm (MaxVar (CoordNat prop 1))).
  rewrite <- Nat.max_assoc. apply Nat.le_max_l. destruct n.
  (* Land *)
  rewrite MaxVar_and.
  apply Nat.max_lub.
  apply (Nat.le_trans _ (Nat.max (MaxVarTerm u) (MaxVar (CoordNat prop 1)))).
  apply IHprop.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Nat.max_lub. apply Nat.le_max_l.
  rewrite Nat.max_comm, <- Nat.max_assoc. apply Nat.le_max_l.
  apply (Nat.le_trans _ (Nat.max (MaxVarTerm u) (MaxVar (CoordNat prop 2)))).
  apply IHprop.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Nat.max_lub. apply Nat.le_max_l.
  rewrite Nat.max_comm, (Nat.max_comm (MaxVar (CoordNat prop 1))).
  rewrite <- Nat.max_assoc. apply Nat.le_max_l. destruct n.
  (* Lforall *)
  rewrite MaxVar_forall. apply Nat.max_lub.
  rewrite Nat.max_comm, <- Nat.max_assoc. apply Nat.le_max_l.
  destruct (CoordNat prop 1 =? v) eqn:des.
  rewrite Nat.max_comm, (Nat.max_comm (CoordNat prop 1)).
  rewrite <- Nat.max_assoc. apply Nat.le_max_l.
  apply (Nat.le_trans _ (Nat.max (MaxVarTerm u) (MaxVar (CoordNat prop 2)))).
  apply IHprop.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Nat.max_lub. apply Nat.le_max_l.
  rewrite Nat.max_comm, (Nat.max_comm (CoordNat prop 1)).
  rewrite <- Nat.max_assoc. apply Nat.le_max_l. destruct n.
  (* Lexists *)
  rewrite MaxVar_exists. apply Nat.max_lub.
  rewrite Nat.max_comm, <- Nat.max_assoc. apply Nat.le_max_l.
  destruct (CoordNat prop 1 =? v) eqn:des.
  rewrite Nat.max_comm, (Nat.max_comm (CoordNat prop 1)).
  rewrite <- Nat.max_assoc. apply Nat.le_max_l.
  apply (Nat.le_trans _ (Nat.max (MaxVarTerm u) (MaxVar (CoordNat prop 2)))).
  apply IHprop.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Nat.max_lub. apply Nat.le_max_l.
  rewrite Nat.max_comm, (Nat.max_comm (CoordNat prop 1)).
  rewrite <- Nat.max_assoc. apply Nat.le_max_l. destruct n.
  (* Lrel *)
  2: apply le_0_n. clear IHprop.
  rewrite <- (MaxVar_rel (CoordNat prop 1)).
  rewrite MaxVar_rel, MaxVarTerm_op.
  apply MaxVarLopTerm_spec. intros j H.
  simpl in H. rewrite LengthMapNat in H.
  rewrite CoordNat_op, CoordMapNat. 2: exact H.
  apply (Nat.le_trans _ _ _ (MaxVarTerm_Subst _ _ _)).
  apply Nat.max_lub. apply Nat.le_max_l. 
  refine (Nat.le_trans _ _ _ _ (Nat.le_max_r _ _)). clear u.
  apply MaxVar_rel_lower, H.
Qed.

Lemma SubstSubstTermDiffCommutes : forall f v w t u,
    v <> w
    -> VarOccursInTerm w t = false
    -> VarOccursInTerm v u = false
    -> SubstTerm t v (SubstTerm u w f) = SubstTerm u w (SubstTerm t v f).
Proof.
  apply (Fix lt_wf (fun f => forall v w t u : nat,
  v <> w ->
  VarOccursInTerm w t = false ->
  VarOccursInTerm v u = false ->
  SubstTerm t v (SubstTerm u w f) = SubstTerm u w (SubstTerm t v f))).
  intros f IHf v w t u H H0 H1. intros.
  rewrite (SubstTerm_step _ _ f).
  rewrite (SubstTerm_step _ _ f).
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat f) 0). reflexivity.
  unfold SubstTermRec.
  destruct (CoordNat f 0) eqn:headF. reflexivity.
  do 7 (destruct n; [reflexivity|]).
  destruct n.
  - (* Lop *)
    rewrite SubstTerm_step, SubstTerm_step.
    unfold TreeFoldNatRec.
    rewrite LengthLop, LengthMapNat, LengthRangeNat.
    rewrite LengthLop, LengthMapNat, LengthRangeNat.
    simpl.
    unfold SubstTermRec; unfold Lop at 1; rewrite CoordConsHeadNat.
    unfold Lop at 5; rewrite CoordConsHeadNat.
    rewrite LengthLop, LengthLop, LengthMapNat, LengthMapNat.
    rewrite LengthRangeNat. simpl. rewrite Nat.sub_0_r.
    apply f_equal2. unfold Lop.
    rewrite CoordConsTailNat, CoordConsTailNat.
    rewrite CoordConsHeadNat, CoordConsHeadNat. reflexivity.
    apply MapNatExt.
    intros n Hn. rewrite LengthRangeNat in Hn.
    rewrite CoordRangeNat. 2: exact Hn.
    rewrite (CoordNat_op _ _ n), (CoordNat_op _ _ n).
    rewrite CoordMapNat, CoordMapNat.
    rewrite CoordRangeNat. apply IHf.
    exact (CoordLower _ _ (LengthPositive _ l)).
    exact H. exact H0. exact H1. exact Hn.
    rewrite LengthRangeNat. exact Hn.
    rewrite LengthRangeNat. exact Hn.
  - (* Lvar *)
    destruct n. 2: reflexivity.
    destruct (CoordNat f 1 =? w) eqn:des1.
    destruct (CoordNat f 1 =? v) eqn:des2.
    exfalso. apply Nat.eqb_eq in des2. rewrite des2 in des1.
    apply Nat.eqb_eq in des1. contradiction.
    rewrite (SubstTerm_varHead _ _ f headF), des1.
    apply SubstTerm_nosubst, H1.
    destruct (CoordNat f 1 =? v) eqn:des2.
    rewrite (SubstTerm_varHead _ _ f headF), des2.
    symmetry. apply SubstTerm_nosubst, H0.
    rewrite (SubstTerm_varHead _ _ f headF), des2.
    rewrite (SubstTerm_varHead _ _ f headF), des1.
    reflexivity.
Qed.

Lemma SubstSubstTermsDiffCommutes : forall f v w t u,
    v <> w
    -> VarOccursInTerm w t = false
    -> VarOccursInTerm v u = false
    -> MapNat (SubstTerm t v) (MapNat (SubstTerm u w) f)
      = MapNat (SubstTerm u w) (MapNat (SubstTerm t v) f).
Proof.
  intros.
  rewrite MapMapNat, MapMapNat. apply MapNatExt. intros k H2.
  rewrite (SubstSubstTermDiffCommutes _ _ _ _ _ H H0 H1). reflexivity.
Qed.

Lemma SubstSubstDiffCommutes : forall (f v w t u : nat),
    v <> w
    -> VarOccursInTerm w t = false
    -> VarOccursInTerm v u = false
    -> Subst t v (Subst u w f) = Subst u w (Subst t v f).
Proof.
  apply (Fix lt_wf (fun f => forall v w t u : nat,
  v <> w ->
  VarOccursInTerm w t = false ->
  VarOccursInTerm v u = false ->
  Subst t v (Subst u w f) = Subst u w (Subst t v f))).
  intros f IHf v w t u H. intros.
  rewrite (Subst_step _ _ f).
  rewrite (Subst_step t v f).
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat f) 0).
  unfold Subst. rewrite TreeFoldNat_nil, TreeFoldNat_nil.
  reflexivity.
  unfold SubstRec.
  destruct (CoordNat f 0).
  unfold Subst. rewrite TreeFoldNat_nil, TreeFoldNat_nil.
  reflexivity.
  destruct n.
  (* Lnot *)
  rewrite Subst_not, Subst_not, IHf. reflexivity.
  apply (CoordLower _ _ (LengthPositive _ l)).
  exact H.
  exact H0. exact H1. destruct n.
  (* Limplies *)
  rewrite Subst_implies, Subst_implies, IHf.
  rewrite (IHf (CoordNat f 2)). reflexivity.
  apply (CoordLower _ _ (LengthPositive _ l)).
  exact H. exact H0. exact H1.
  apply (CoordLower _ _ (LengthPositive _ l)).
  exact H.
  exact H0. exact H1. destruct n.
  (* Lor *)
  rewrite Subst_or, Subst_or, IHf.
  rewrite (IHf (CoordNat f 2)). reflexivity.
  apply (CoordLower _ _ (LengthPositive _ l)).
  exact H. exact H0. exact H1.
  apply (CoordLower _ _ (LengthPositive _ l)).
  exact H.
  exact H0. exact H1. destruct n.
  (* Land *)
  rewrite Subst_and, Subst_and, IHf.
  rewrite (IHf (CoordNat f 2)). reflexivity.
  apply (CoordLower _ _ (LengthPositive _ l)).
  exact H. exact H0. exact H1.
  apply (CoordLower _ _ (LengthPositive _ l)).
  exact H.
  exact H0. exact H1. destruct n.
  (* Lforall *)
  destruct (PeanoNat.Nat.eqb (CoordNat f 1) w) eqn:des1.
  destruct (PeanoNat.Nat.eqb (CoordNat f 1) v) eqn:des2.
  exfalso.
  apply Nat.eqb_eq in des1.
  apply Nat.eqb_eq in des2. rewrite des1 in des2.
  rewrite des2 in H. apply H. reflexivity.
  rewrite (Subst_forall u), des1.
  rewrite Subst_forall, des2. reflexivity.
  destruct (PeanoNat.Nat.eqb (CoordNat f 1) v) eqn:des2.
  rewrite Subst_forall, des2.
  rewrite Subst_forall, des1. reflexivity.
  rewrite Subst_forall, Subst_forall, des1, des2.
  rewrite IHf, IHf. reflexivity.
  apply (CoordLower _ _ (LengthPositive _ l)).
  intro abs. rewrite abs in H. apply H. reflexivity.
  exact H1. exact H0.
  apply (CoordLower _ _ (LengthPositive _ l)).
  exact H. exact H0. exact H1. destruct n.
  (* Lexists *)
  destruct (PeanoNat.Nat.eqb (CoordNat f 1) w) eqn:des1.
  destruct (PeanoNat.Nat.eqb (CoordNat f 1) v) eqn:des2.
  exfalso.
  apply Nat.eqb_eq in des1.
  apply Nat.eqb_eq in des2. rewrite des1 in des2.
  rewrite des2 in H. apply H. reflexivity.
  rewrite (Subst_exists u), des1.
  rewrite Subst_exists, des2. reflexivity.
  destruct (PeanoNat.Nat.eqb (CoordNat f 1) v) eqn:des2.
  rewrite Subst_exists, des2.
  rewrite Subst_exists, des1. reflexivity.
  rewrite Subst_exists, Subst_exists, des1, des2.
  rewrite IHf, IHf. reflexivity.
  apply (CoordLower _ _ (LengthPositive _ l)).
  intro abs. rewrite abs in H. apply H. reflexivity.
  exact H1. exact H0.
  apply (CoordLower _ _ (LengthPositive _ l)).
  exact H. exact H0. exact H1. destruct n.
  (* Lrel *)
  pose proof Subst_rel as H2.
  rewrite H2, H2. apply f_equal. clear H2.
  apply SubstSubstTermsDiffCommutes.
  exact H. exact H0. exact H1.
  unfold Subst. rewrite TreeFoldNat_nil, TreeFoldNat_nil. reflexivity.
Qed.

Lemma SubstSubstTermIdem : forall (u t w : nat) (* terms *) (v:nat) (* variable *),
    SubstTerm w v (SubstTerm t v u) = SubstTerm (SubstTerm w v t) v u.
Proof.
  apply (Fix lt_wf (fun u => forall t w v,
      SubstTerm w v (SubstTerm t v u) = SubstTerm (SubstTerm w v t) v u)).
  intros u IHu t v w.
  rewrite (SubstTerm_step _ _ u), (SubstTerm_step _ _ u).
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat u) 0). reflexivity.
  unfold SubstTermRec.
  destruct (CoordNat u 0) eqn:headU. reflexivity.
  do 7 (destruct n; [reflexivity|]). destruct n.
  - (* Lop *)
    rewrite SubstTerm_opHead.
    2: unfold Lop; rewrite CoordConsHeadNat; reflexivity.
    apply f_equal2.
    unfold Lop. rewrite CoordConsTailNat, CoordConsHeadNat. reflexivity. 
    rewrite LengthLop, LengthMapNat, LengthRangeNat. simpl.
    rewrite Nat.sub_0_r.
    apply MapNatExt.
    intros n H. rewrite LengthRangeNat in H.
    rewrite CoordRangeNat, (CoordNat_op _ _ n). 2: exact H.
    rewrite CoordMapNat, CoordRangeNat.
    apply IHu.
    exact (CoordLower _ _ (LengthPositive _ l)). exact H.
    rewrite LengthRangeNat. exact H.
  - (* Lvar *)
    destruct n. 2: reflexivity.
    destruct (CoordNat u 1 =? w) eqn:des2. reflexivity.
    rewrite SubstTerm_step. unfold TreeFoldNatRec.
    destruct (le_lt_dec (LengthNat u) 0). exfalso.
    apply (Nat.lt_irrefl 0). exact (Nat.lt_le_trans _ _ _ l l0).
    unfold SubstTermRec. rewrite headU, des2. reflexivity.
Qed.

Lemma SubstSubstTermsIdem : forall (terms t u v : nat),
    MapNat (SubstTerm u v) (MapNat (SubstTerm t v) terms)
    = MapNat (SubstTerm (SubstTerm u v t) v) terms.
Proof.
  intros. 
  rewrite MapMapNat. apply MapNatExt. intros k H0.
  apply SubstSubstTermIdem.
Qed.

Lemma SubstSubstIdem : forall (prop t u v : nat),
    Subst u v (Subst t v prop) = Subst (SubstTerm u v t) v prop.
Proof.
  apply (Fix lt_wf (fun prop => forall t u v,
                        Subst u v (Subst t v prop) = Subst (SubstTerm u v t) v prop)).
  intros prop IHprop t u v.
  rewrite (Subst_step _ _ prop). rewrite (Subst_step (SubstTerm u v t) v prop).
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat prop) 0).
  reflexivity. unfold SubstRec.
  destruct (CoordNat prop 0) eqn:headProp. reflexivity.
  destruct n.
  (* Lnot *)
  rewrite Subst_not, IHprop. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)). 
  destruct n.
  (* Limplies *)
  rewrite Subst_implies, IHprop, IHprop. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)). 
  exact (CoordLower _ _ (LengthPositive _ l)). 
  destruct n.
  (* Lor *)
  rewrite Subst_or, IHprop, IHprop. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)). 
  exact (CoordLower _ _ (LengthPositive _ l)). 
  destruct n.
  (* Land *)
  rewrite Subst_and, IHprop, IHprop. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)). 
  exact (CoordLower _ _ (LengthPositive _ l)). 
  destruct n.
  (* Lforall *)
  rewrite Subst_forall.
  destruct (CoordNat prop 1 =? v). reflexivity.
  rewrite IHprop. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)). 
  destruct n.
  (* Lexists *)
  rewrite Subst_exists.
  destruct (CoordNat prop 1 =? v). reflexivity.
  rewrite IHprop. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)). 
  destruct n.
  (* Lrel *)
  rewrite Subst_rel, SubstSubstTermsIdem. reflexivity. reflexivity.
Qed.

Lemma VarOccursFreeInFormula_SubstIdem : forall prop t v,
    IsLproposition prop = true
    -> VarOccursInTerm v t = false
    -> VarOccursFreeInFormula v (Subst t v prop) = false.
Proof.
  intros.
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite SubstSubstIdem.
  apply Bool.negb_false_iff, Nat.eqb_eq in H0.
  rewrite H0. reflexivity.
Qed.

Lemma VarOccursInTerm_SubstDiff : forall term,
    IsLterm term = true
    -> forall t v w, v <> w
    -> VarOccursInTerm v term = true
    -> VarOccursInTerm v (SubstTerm t w term) = true.
Proof.
  apply (Lterm_rect (fun term => forall t v w, v <> w
    -> VarOccursInTerm v term = true
    -> VarOccursInTerm v (SubstTerm t w term) = true)).
  - intros. rewrite SubstTerm_var.
    destruct (v =? w) eqn:des. 2: exact H0. exfalso.
    rewrite VarOccursInTerm_var in H0.
    apply Nat.eqb_eq in H0. subst v0.
    apply Nat.eqb_eq in des. subst w.
    apply H. reflexivity.
  - intros. apply VarOccursInTerm_opHead in H0.
    rewrite SubstTerm_op. apply VarOccursInTerm_opHead.
    unfold Lop. rewrite CoordConsHeadNat. reflexivity.
    change 2 with (2+0). rewrite LengthLop, LengthMapNat.
    apply Nat.add_le_mono_l, le_0_n.
    rewrite LengthLop, LengthMapNat. unfold Lop.
    simpl. rewrite TailConsNat, TailConsNat.
    apply MapNatTruncated.
    destruct H0 as [j [H0 H1]]. rewrite LengthLop in H0.
    exists j. split. rewrite LengthLop, LengthMapNat. exact H0.
    rewrite CoordNat_op, CoordMapNat.
    rewrite CoordNat_op in H1.
    apply IHterms. exact H0. exact H.
    exact H1. exact H0.
    unfold Lop. rewrite CoordConsHeadNat. reflexivity. 
    change 2 with (2+0). rewrite LengthLop.
    apply Nat.add_le_mono_l, le_0_n.
    rewrite LengthLop. simpl. unfold Lop.
    rewrite TailConsNat, TailConsNat. exact termsTrunc.
Qed.

Lemma VarOccursFreeInFormula_SubstDiff : forall prop t v w,
    IsLproposition prop = true
    -> v <> w
    -> VarOccursInTerm v t = false
    -> VarOccursFreeInFormula v (Subst t w prop) = VarOccursFreeInFormula v prop.
Proof.
  intros.
  destruct (VarOccursFreeInFormula v prop) eqn:des.
  clear H1. revert prop H t v w H0 des.
  apply (Lproposition_rect (fun prop => forall t v w : nat,
  v <> w ->
  VarOccursFreeInFormula v prop = true ->
  VarOccursFreeInFormula v (Subst t w prop) = true)).
  - intros. rewrite Subst_rel, VarOccursFreeInFormula_rel, LengthMapNat.
    apply VarOccursFreeInFormula_rel in H0.
    destruct H0 as [j [H1 H2]]. exists j. split. exact H1.
    rewrite CoordMapNat. 2: exact H1. 
    apply VarOccursInTerm_SubstDiff. apply elemterms. exact H1.
    exact H. exact H2. exact termsTrunc.
    rewrite LengthMapNat. apply MapNatTruncated.
  - intros. rewrite Subst_not, VarOccursFreeInFormula_not.
    apply IHprop. exact H.
    rewrite VarOccursFreeInFormula_not in H0. exact H0.
  - intros. rewrite Subst_implies, VarOccursFreeInFormula_implies.
    rewrite VarOccursFreeInFormula_implies in H0.
    apply Bool.orb_prop in H0. destruct H0.
    rewrite IHg. reflexivity. exact H. exact H0.
    rewrite IHh. rewrite Bool.orb_true_r. reflexivity. exact H. exact H0.
  - intros. rewrite Subst_or, VarOccursFreeInFormula_or.
    rewrite VarOccursFreeInFormula_or in H0.
    apply Bool.orb_prop in H0. destruct H0.
    rewrite IHg. reflexivity. exact H. exact H0.
    rewrite IHh. rewrite Bool.orb_true_r. reflexivity. exact H. exact H0.
  - intros. rewrite Subst_and, VarOccursFreeInFormula_and.
    rewrite VarOccursFreeInFormula_and in H0.
    apply Bool.orb_prop in H0. destruct H0.
    rewrite IHg. reflexivity. exact H. exact H0.
    rewrite IHh. rewrite Bool.orb_true_r. reflexivity. exact H. exact H0.
  - intros. rewrite Subst_forall, VarOccursFreeInFormula_forall.
    rewrite VarOccursFreeInFormula_forall in H0.
    destruct (v0 =? v) eqn:desv. discriminate H0. simpl. simpl in H0.
    destruct (v =? w) eqn:desw. exact H0. apply IHprop. exact H. exact H0.
  - intros. rewrite Subst_exists, VarOccursFreeInFormula_exists.
    rewrite VarOccursFreeInFormula_exists in H0.
    destruct (v0 =? v) eqn:desv. discriminate H0. simpl. simpl in H0.
    destruct (v =? w) eqn:desw. exact H0. apply IHprop. exact H. exact H0.
  - unfold VarOccursFreeInFormula.
    rewrite SubstSubstDiffCommutes.
    2: exact H0. 2: reflexivity.
    apply Bool.negb_false_iff in des.
    apply Nat.eqb_eq in des. rewrite des, Nat.eqb_refl. reflexivity. exact H1.
Qed.

Lemma VarOccursInTerm_SubstClosed : forall u v w t,
    VarOccursInTerm v u = false
    -> VarOccursInTerm v t = false
    -> VarOccursInTerm v (SubstTerm t w u) = false.
Proof.
  apply (Fix lt_wf (fun u => forall v w t,
    VarOccursInTerm v u = false
    -> VarOccursInTerm v t = false
    -> VarOccursInTerm v (SubstTerm t w u) = false)).
  intros u IHu. intros.
  apply Bool.negb_false_iff in H. rewrite SubstTerm_step in H.
  unfold TreeFoldNatRec in H.
  rewrite SubstTerm_step. unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat u) 0). reflexivity.
  unfold SubstTermRec. unfold SubstTermRec in H.
  destruct (CoordNat u 0) eqn:headU. reflexivity.
  do 7 (destruct n; [reflexivity|]). destruct n.
  - (* Lop *)
    apply Nat.eqb_eq in H.
    apply Bool.negb_false_iff, Nat.eqb_eq.
    rewrite SubstTerm_op. apply f_equal.
    rewrite MapMapNat.
    apply MapNatExt. intros k H1.
    rewrite LengthRangeNat in H1.
    rewrite CoordRangeNat. 2: exact H1.
    apply (f_equal (fun a => CoordNat a (S (S k)))) in H.
    rewrite CoordNat_op in H.
    rewrite CoordMapNat, CoordRangeNat in H.
    apply Nat.eqb_eq, Bool.negb_false_iff. apply IHu.
    exact (CoordLower _ _ (LengthPositive _ l)).
    apply Bool.negb_false_iff, Nat.eqb_eq. exact H. exact H0.
    exact H1. rewrite LengthRangeNat. exact H1.
  - (* Lvar *)
    clear IHu. destruct n. 2: reflexivity.
    destruct (CoordNat u 1 =? w). exact H0. clear w.
    destruct (CoordNat u 1 =? v) eqn:des.
    apply Nat.eqb_eq in H. rewrite <- H. reflexivity. clear H.
    apply Bool.negb_false_iff.
    rewrite SubstTerm_step.
    unfold TreeFoldNatRec.
    destruct (le_lt_dec (LengthNat u) 0). exfalso.
    inversion l0. rewrite H1 in l. inversion l.
    unfold SubstTermRec. rewrite headU, des. apply Nat.eqb_refl.
Qed.

Lemma VarOccursFreeInFormula_SubstClosed : forall f v w t,
    VarOccursFreeInFormula v f = false
    -> VarOccursInTerm v t = false
    -> VarOccursFreeInFormula v (Subst t w f) = false.
Proof.
  apply (Fix lt_wf (fun f => forall v w t,
    VarOccursFreeInFormula v f = false
    -> VarOccursInTerm v t = false
    -> VarOccursFreeInFormula v (Subst t w f) = false)).
  intros f IHf. intros.
  apply Bool.negb_false_iff in H. rewrite Subst_step in H.
  unfold TreeFoldNatRec in H.
  rewrite Subst_step. unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat f) 0). reflexivity.
  unfold SubstRec. unfold SubstRec in H.
  destruct (CoordNat f 0) eqn:headF. reflexivity. destruct n.
  (* Lnot *)
  rewrite VarOccursFreeInFormula_not.
  apply IHf.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff.
  apply Nat.eqb_eq in H.
  rewrite <- H at 2. rewrite CoordNat_not_1. apply Nat.eqb_refl.
  exact H0. destruct n.
  (* Limplies *)
  rewrite VarOccursFreeInFormula_implies.
  apply Nat.eqb_eq in H.
  rewrite IHf, IHf. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff.
  rewrite <- H at 2. rewrite CoordNat_implies_2. apply Nat.eqb_refl.
  exact H0.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff.
  rewrite <- H at 2. rewrite CoordNat_implies_1. apply Nat.eqb_refl.
  exact H0. destruct n.
  (* Lor *)
  rewrite VarOccursFreeInFormula_or.
  apply Nat.eqb_eq in H.
  rewrite IHf, IHf. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff.
  rewrite <- H at 2. rewrite CoordNat_or_2. apply Nat.eqb_refl.
  exact H0.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff.
  rewrite <- H at 2. rewrite CoordNat_or_1. apply Nat.eqb_refl.
  exact H0. destruct n.
  (* Land *)
  rewrite VarOccursFreeInFormula_and.
  apply Nat.eqb_eq in H.
  rewrite IHf, IHf. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff.
  rewrite <- H at 2. rewrite CoordNat_and_2. apply Nat.eqb_refl.
  exact H0.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff.
  rewrite <- H at 2. rewrite CoordNat_and_1. apply Nat.eqb_refl.
  exact H0. destruct n.
  (* Lforall *)
  apply Nat.eqb_eq in H.
  rewrite VarOccursFreeInFormula_forall.
  destruct (v =? CoordNat f 1) eqn:des. reflexivity. simpl.
  rewrite Nat.eqb_sym in des. rewrite des in H. 
  destruct (CoordNat f 1 =? w) eqn:des2.
  clear des2 w.
  apply Bool.negb_false_iff.
  rewrite <- H at 2. rewrite CoordNat_forall_2. apply Nat.eqb_refl.
  apply IHf.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff.
  rewrite <- H at 2. rewrite CoordNat_forall_2. apply Nat.eqb_refl.
  exact H0. destruct n.
  (* Lexists *)
  apply Nat.eqb_eq in H.
  rewrite VarOccursFreeInFormula_exists.
  destruct (v =? CoordNat f 1) eqn:des. reflexivity. simpl.
  rewrite Nat.eqb_sym in des. rewrite des in H. 
  destruct (CoordNat f 1 =? w) eqn:des2.
  clear des2 w.
  apply Bool.negb_false_iff.
  rewrite <- H at 2. rewrite CoordNat_exists_2. apply Nat.eqb_refl.
  apply IHf.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff.
  rewrite <- H at 2. rewrite CoordNat_exists_2. apply Nat.eqb_refl.
  exact H0. destruct n.
  (* Lrel *)
  2: reflexivity. clear IHf.
  apply Nat.eqb_eq in H.
  pose proof (VarOccursFreeInFormula_rel
                v (CoordNat f 1) (MapNat (SubstTerm t w) (TailNat (TailNat f)))).
  destruct (VarOccursFreeInFormula v
    (Lrel (CoordNat f 1) (MapNat (SubstTerm t w) (TailNat (TailNat f))))).
  2: reflexivity. exfalso.
  destruct H1 as [H1 _]. rewrite LengthMapNat. apply MapNatTruncated.
  specialize (H1 eq_refl).
  destruct H1 as [j [H1 H2]].
  rewrite LengthMapNat in H1.
  rewrite CoordMapNat, CoordTailNat, CoordTailNat in H2. 2: exact H1.
  assert (VarOccursInTerm v (CoordNat f (S (S j))) = false).
  { apply Bool.negb_false_iff.
    rewrite <- H at 2. rewrite CoordNat_rel, CoordMapNat.
    rewrite CoordTailNat, CoordTailNat. apply Nat.eqb_refl.
    exact H1. }
  rewrite (VarOccursInTerm_SubstClosed (CoordNat f (S (S j))) v w t H3 H0) in H2.
  discriminate H2.
Qed. 

Lemma SubstTermIdemVar : forall t,
    IsLterm t = true
    -> forall v, SubstTerm (Lvar v) v t = t.
Proof.
  apply (Lterm_rect (fun t => forall v, SubstTerm (Lvar v) v t = t)).
  - intros. rewrite SubstTerm_var.
    destruct (v =? v0) eqn:des. apply Nat.eqb_eq in des.
    subst v0. reflexivity. reflexivity.
  - intros. rewrite SubstTerm_op. 
    apply f_equal. 
    apply TruncatedEqNat.
    rewrite LengthMapNat. reflexivity.
    rewrite LengthMapNat, MapNatTruncated. 
    symmetry. exact termsTrunc.
    intros k H. rewrite LengthMapNat in H.
    rewrite CoordMapNat.
    apply IHterms, H. exact H.
Qed.

Lemma SubstTermsIdemVar : forall (terms v : nat),
    NthTailNat terms (LengthNat terms) = 0
    -> (forall i : nat, i < LengthNat terms -> IsLterm (CoordNat terms i) = true)
    -> MapNat (SubstTerm (Lvar v) v) terms = terms.
Proof.
  intros. apply TruncatedEqNat.
  rewrite LengthMapNat. reflexivity.
  rewrite LengthMapNat, MapNatTruncated.
  symmetry. exact H.
  intros k H1. rewrite LengthMapNat in H1.
  rewrite CoordMapNat. apply SubstTermIdemVar.
  apply H0. exact H1. exact H1.
Qed.

Lemma SubstIdemVar : forall prop,
    IsLproposition prop = true
    -> forall v, Subst (Lvar v) v prop = prop.
Proof.
  apply (Lproposition_rect (fun prop => forall v, Subst (Lvar v) v prop = prop)).
  - intros. rewrite Subst_rel.
    apply f_equal, SubstTermsIdemVar. exact termsTrunc. exact elemterms.
  - intros. rewrite Subst_not, IHprop. reflexivity.
  - intros. rewrite Subst_implies, IHg, IHh. reflexivity.
  - intros. rewrite Subst_or, IHg, IHh. reflexivity.
  - intros. rewrite Subst_and, IHg, IHh. reflexivity.
  - intros. rewrite Subst_forall.
    destruct (v =? v0). reflexivity.
    rewrite IHprop. reflexivity.
  - intros. rewrite Subst_exists.
    destruct (v =? v0). reflexivity.
    rewrite IHprop. reflexivity.
Qed.


(* Accelerate the type checker and simpl tactics *)
Global Opaque SubstTerm.
Global Opaque Subst.

Global Ltac reduce_subst := repeat (rewrite Subst_exists
                                    || rewrite Subst_forall
                                    || rewrite Subst_not
                                    || rewrite Subst_and
                                    || rewrite Subst_or
                                    || rewrite Subst_implies
                                    || rewrite Subst_eq
                                    || rewrite Subst_rel2
                                    || rewrite SubstTerm_op1
                                    || rewrite SubstTerm_op2
                                    || rewrite SubstTerm_var).

