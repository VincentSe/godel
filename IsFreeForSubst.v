(** This is how we avoid captures of variables in substitutions.
    Instead of automatically renaming all quantifiers for each substitution,
    we simply check whether a substitution captures variables, and refuse it
    when it does. *)

Require Import PeanoNat.
Require Import Arith.Compare_dec.
Require Import EnumSeqNat.
Require Import Formulas.
Require Import Substitutions.


(* Check that the substitution of term u for all free occurrences of variable Xv
   in formula f does not capture any variables of u. *)
Definition IsFreeForSubstRec (u v f : nat) (rec : nat -> bool) : bool :=
  match CoordNat f 0 with
  | LnotHead => rec 1
  | LimpliesHead
  | LorHead
  | LandHead => rec 1 && rec 2
  | LforallHead
  | LexistsHead => negb (VarOccursFreeInFormula v f)  (* no substitutions *)
                  || (rec 2 && negb (VarOccursInTerm (CoordNat f 1) u))
  | LrelHead => true
  | LopHead => true
  | LvarHead => true
  | _ => false
  end.

Definition IsFreeForSubst (u v : nat) : nat -> bool
  := TreeFoldNat (IsFreeForSubstRec u v) false.

Lemma IsFreeForSubst_step : forall u v f,
    IsFreeForSubst u v f
    = TreeFoldNatRec (IsFreeForSubstRec u v) false f (fun k _ => IsFreeForSubst u v k).
Proof.
  intros.
  unfold IsFreeForSubst, TreeFoldNat. rewrite Fix_eq.
  reflexivity.
  intros. unfold IsFreeForSubstRec, TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat x) 0). reflexivity.
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

Lemma IsFreeForSubst_not : forall u v f,
    IsFreeForSubst u v (Lnot f) = IsFreeForSubst u v f.
Proof.
  intros.
  rewrite IsFreeForSubst_step.
  unfold TreeFoldNatRec.
  rewrite LengthLnot. simpl.
  unfold IsFreeForSubstRec.
  unfold Lnot.
  rewrite CoordConsHeadNat, CoordConsTailNat.
  rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma IsFreeForSubst_implies : forall u v f g,
    IsFreeForSubst u v (Limplies f g)
    = (IsFreeForSubst u v f && IsFreeForSubst u v g)%bool.
Proof.
  intros.
  rewrite IsFreeForSubst_step.
  unfold TreeFoldNatRec.
  rewrite LengthLimplies. simpl.
  unfold IsFreeForSubstRec.
  unfold Limplies.
  rewrite CoordConsHeadNat, CoordConsTailNat.
  rewrite CoordConsHeadNat.
  rewrite CoordConsTailNat, CoordConsTailNat.
  rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma IsFreeForSubst_or : forall u v f g,
    IsFreeForSubst u v (Lor f g)
    = (IsFreeForSubst u v f && IsFreeForSubst u v g)%bool.
Proof.
  intros.
  rewrite IsFreeForSubst_step.
  unfold TreeFoldNatRec.
  rewrite LengthLor. simpl.
  unfold IsFreeForSubstRec.
  unfold Lor.
  rewrite CoordConsHeadNat, CoordConsTailNat.
  rewrite CoordConsHeadNat.
  rewrite CoordConsTailNat, CoordConsTailNat.
  rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma IsFreeForSubst_and : forall u v f g,
    IsFreeForSubst u v (Land f g)
    = (IsFreeForSubst u v f && IsFreeForSubst u v g)%bool.
Proof.
  intros.
  rewrite IsFreeForSubst_step.
  unfold TreeFoldNatRec.
  rewrite LengthLand. simpl.
  unfold IsFreeForSubstRec.
  unfold Land.
  rewrite CoordConsHeadNat, CoordConsTailNat.
  rewrite CoordConsHeadNat.
  rewrite CoordConsTailNat, CoordConsTailNat.
  rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma IsFreeForSubst_equiv : forall u v f g,
    IsFreeForSubst u v (Lequiv f g)
    = (IsFreeForSubst u v f && IsFreeForSubst u v g)%bool.
Proof.
  intros.
  unfold Lequiv.
  rewrite IsFreeForSubst_and, IsFreeForSubst_implies, IsFreeForSubst_implies.
  destruct (IsFreeForSubst u v f), (IsFreeForSubst u v g); reflexivity.
Qed.

Lemma IsFreeForSubst_forall : forall u v n f,
    IsFreeForSubst u v (Lforall n f)
    = (Nat.eqb v n
       || negb (VarOccursFreeInFormula v f)  (* no substitutions *)
       || (IsFreeForSubst u v f && negb (VarOccursInTerm n u)))%bool.
Proof.
  intros. rewrite IsFreeForSubst_step.
  unfold TreeFoldNatRec.
  rewrite LengthLforall. simpl.
  unfold IsFreeForSubstRec.
  rewrite CoordNat_forall_2.
  rewrite CoordNat_forall_1.
  rewrite VarOccursFreeInFormula_forall.
  unfold Lforall; rewrite CoordConsHeadNat.
  rewrite Bool.negb_andb, Bool.negb_involutive.
  reflexivity.
Qed.

Lemma IsFreeForSubst_exists : forall u v n f,
    IsFreeForSubst u v (Lexists n f)
    = (Nat.eqb v n
       || negb (VarOccursFreeInFormula v f)  (* no substitutions *)
       || (IsFreeForSubst u v f && negb (VarOccursInTerm n u)))%bool.
Proof.
  intros. rewrite IsFreeForSubst_step.
  unfold TreeFoldNatRec.
  rewrite LengthLexists. simpl.
  unfold IsFreeForSubstRec.
  rewrite CoordNat_exists_2.
  rewrite CoordNat_exists_1.
  rewrite VarOccursFreeInFormula_exists.
  unfold Lexists; rewrite CoordConsHeadNat.
  rewrite Bool.negb_andb, Bool.negb_involutive.
  reflexivity.
Qed.

Lemma IsFreeForSubst_rel : forall u v f,
    CoordNat f 0 = LrelHead
    -> IsFreeForSubst u v f = true.
Proof.
  intros. rewrite IsFreeForSubst_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat f) 0). 
  rewrite CoordNatAboveLength in H. discriminate. exact l.
  unfold IsFreeForSubstRec. rewrite H. reflexivity.
Qed.

Lemma IsFreeForSubst_rel2 : forall u v r a b,
    IsFreeForSubst u v (Lrel2 r a b) = true.
Proof.
  intros. rewrite IsFreeForSubst_step.
  unfold TreeFoldNatRec.
  rewrite LengthLrel2. simpl.
  unfold IsFreeForSubstRec.
  unfold Lrel2, Lrel; rewrite CoordConsHeadNat.
  reflexivity.
Qed.

(* An example of bad specialization that is avoided by IsFreeForSubst,
   exists X1, X1 <> X0. *)
Lemma IsFreeForSubstExample :
  IsFreeForSubst (Lvar 1) 0 (Lexists 1 (Lnot (Leq (Lvar 0) (Lvar 1))))
  = false.
Proof.
  rewrite IsFreeForSubst_exists.
  rewrite VarOccursFreeInFormula_not.
  rewrite IsFreeForSubst_not.
  unfold Leq. rewrite IsFreeForSubst_rel2.
  rewrite VarOccursInTerm_var.
  rewrite VarOccursFreeInFormula_rel2.
  rewrite VarOccursInTerm_var.
  rewrite VarOccursInTerm_var.
  reflexivity.
Qed.

Lemma IsFreeForSubst_nosubst : forall f,
    IsLproposition f = true
    -> forall v u, VarOccursFreeInFormula v f = false
    -> IsFreeForSubst u v f = true.
Proof.
  apply (Lproposition_rect (fun f => forall v u,
    VarOccursFreeInFormula v f = false
    -> IsFreeForSubst u v f = true)).
  - (* Lrel *)
    intros. rewrite IsFreeForSubst_rel. reflexivity.
    unfold Lrel. rewrite CoordConsHeadNat. reflexivity.
  - (* Lnot *)
    intros. rewrite IsFreeForSubst_not. apply IHprop.
    rewrite VarOccursFreeInFormula_not in H.
    exact H.
  - (* Limplies *)
    intros. 
    rewrite VarOccursFreeInFormula_implies in H.
    apply Bool.orb_false_elim in H. destruct H.
    rewrite IsFreeForSubst_implies, IHg, IHh. reflexivity.
    exact H0. exact H.
  - (* Lor *)
    intros. 
    rewrite VarOccursFreeInFormula_or in H.
    apply Bool.orb_false_elim in H. destruct H.
    rewrite IsFreeForSubst_or, IHg, IHh. reflexivity.
    exact H0. exact H.
  - (* Land *)
    intros. 
    rewrite VarOccursFreeInFormula_and in H.
    apply Bool.orb_false_elim in H. destruct H.
    rewrite IsFreeForSubst_and, IHg, IHh. reflexivity.
    exact H0. exact H.
  - (* Lforall *)
    intros. rewrite VarOccursFreeInFormula_forall in H.
    rewrite IsFreeForSubst_forall.
    destruct (Nat.eqb v0 v) eqn:des. reflexivity. simpl in H.
    simpl. rewrite H. reflexivity.
  - (* Lexists *)
    intros. rewrite VarOccursFreeInFormula_exists in H.
    rewrite IsFreeForSubst_exists.
    destruct (Nat.eqb v0 v) eqn:des. reflexivity. simpl in H.
    simpl. rewrite H. reflexivity.
Qed.

Lemma IsFreeForSubst_closed : forall f,
    IsLproposition f = true
    -> forall u v, (forall w, w <> v -> VarOccursInTerm w u = false)
    -> IsFreeForSubst u v f = true.
Proof.
  apply (Lproposition_rect (fun f => forall u v : nat,
  (forall w : nat, w <> v -> VarOccursInTerm w u = false) ->
  IsFreeForSubst u v f = true)).
  - (* Lrel *)
    intros. rewrite IsFreeForSubst_rel. reflexivity.
    unfold Lrel. rewrite CoordConsHeadNat. reflexivity.
  - (* Lnot *)
    intros. rewrite IsFreeForSubst_not.
    apply IHprop. exact H.
  - (* Limplies *)
    intros. rewrite IsFreeForSubst_implies.
    apply andb_true_intro; split.
    apply IHg. exact H.
    apply IHh. exact H.
  - (* Lor *)
    intros. rewrite IsFreeForSubst_or.
    apply andb_true_intro; split.
    apply IHg. exact H.
    apply IHh. exact H.
  - (* Land *)
    intros. rewrite IsFreeForSubst_and.
    apply andb_true_intro; split.
    apply IHg. exact H.
    apply IHh. exact H.
  - (* Lforall *)
    intros. rewrite IsFreeForSubst_forall.
    destruct (Nat.eqb v0 v) eqn:des. reflexivity. simpl.
    destruct (VarOccursFreeInFormula v0 prop) eqn:v0occur.
    2: reflexivity. simpl.
    apply andb_true_intro; split.
    apply IHprop. exact H.
    apply Bool.negb_true_iff, H.
    apply Nat.eqb_neq in des.
    intro abs. rewrite abs in des. contradict des. reflexivity.
  - (* Lexists *)
    intros. rewrite IsFreeForSubst_exists.
    destruct (v0 =? v) eqn:des. reflexivity. simpl.
    destruct (VarOccursFreeInFormula v0 prop) eqn:v0occur.
    2: reflexivity. simpl.
    apply andb_true_intro; split.
    apply IHprop. exact H.
    apply Bool.negb_true_iff, H.
    apply Nat.eqb_neq in des.
    intro abs. rewrite abs in des. contradict des. reflexivity.
Qed.

(* IsFreeForSubst u w prop is needed, because all substitutions are free in
   SubstTerm t v u. *)
Lemma SubstSubstNested : forall prop,
    IsLproposition prop = true 
    -> forall t u v w, VarOccursFreeInFormula v prop = false
    -> IsFreeForSubst u w prop = true
    -> Subst t v (Subst u w prop) = Subst (SubstTerm t v u) w prop.
Proof.
  apply (Lproposition_rect (fun prop =>
                               forall t u v w : nat,
  VarOccursFreeInFormula v prop = false ->
    IsFreeForSubst u w prop = true ->
  Subst t v (Subst u w prop) = Subst (SubstTerm t v u) w prop )).
  - (* Lrel *)
    intros. rewrite Subst_rel, Subst_rel, Subst_rel.
    apply f_equal. apply (SubstTermsNested r).
    exact elemterms. exact H. 
  - (* Lnot *)
    intros.
    rewrite Subst_not, Subst_not, IHprop, Subst_not. reflexivity.
    rewrite VarOccursFreeInFormula_not in H. exact H.
    rewrite IsFreeForSubst_not in H0. exact H0.
  - (* Limplies *)
    intros.
    rewrite VarOccursFreeInFormula_implies in H.
    apply Bool.orb_false_elim in H.
    rewrite IsFreeForSubst_implies in H0.
    apply andb_prop in H0.
    rewrite Subst_implies, Subst_implies, Subst_implies, IHg, IHh.
    reflexivity. apply H. apply H0. apply H. apply H0.
  - (* Lor *)
    intros.
    rewrite VarOccursFreeInFormula_or in H.
    apply Bool.orb_false_elim in H.
    rewrite IsFreeForSubst_or in H0.
    apply andb_prop in H0.
    rewrite Subst_or, Subst_or, Subst_or, IHg, IHh.
    reflexivity. apply H. apply H0. apply H. apply H0.
  - (* Land *)
    intros.
    rewrite VarOccursFreeInFormula_and in H.
    apply Bool.orb_false_elim in H.
    rewrite IsFreeForSubst_and in H0.
    apply andb_prop in H0.
    rewrite Subst_and, Subst_and, Subst_and, IHg, IHh.
    reflexivity. apply H. apply H0. apply H. apply H0.
  - (* Lforall *)
    intros.
    rewrite Subst_forall, Subst_forall, Subst_forall.
    destruct (v =? w) eqn:desw, (v =? v0) eqn:desv.
    + apply Nat.eqb_eq in desw. subst w. reflexivity.
    + rewrite VarOccursFreeInFormula_forall, Nat.eqb_sym, desv in H.
      simpl in H.
      rewrite Subst_nosubst. reflexivity. exact H.
    + apply Nat.eqb_eq in desv. subst v0. clear H. apply f_equal.
      rewrite IsFreeForSubst_forall, Nat.eqb_sym, desw in H0.
      simpl in H0. destruct (VarOccursFreeInFormula w prop) eqn:occur.
      simpl in H0.
      apply andb_prop in H0. destruct H0 as [_ occvar].
      rewrite SubstTerm_nosubst. reflexivity.
      apply Bool.negb_true_iff in occvar. exact occvar.
      rewrite Subst_nosubst, Subst_nosubst. reflexivity. 
      exact occur. exact occur.
    + apply f_equal.
      rewrite VarOccursFreeInFormula_forall, Nat.eqb_sym, desv in H; simpl in H.
      destruct (VarOccursFreeInFormula w prop) eqn:occur.
      rewrite IHprop.
      reflexivity.
      exact H.
      rewrite IsFreeForSubst_forall, Nat.eqb_sym, desw in H0.
      simpl in H0. rewrite occur in H0.
      apply andb_prop in H0. apply H0.
      rewrite (Subst_nosubst _ w), (Subst_nosubst _ w), Subst_nosubst.
      reflexivity. exact H. exact occur. exact occur.
  - (* Lexists *)
    intros.
    rewrite Subst_exists, Subst_exists, Subst_exists.
    destruct (v =? w) eqn:desw, (v =? v0) eqn:desv.
    + apply Nat.eqb_eq in desw. subst w. reflexivity.
    + rewrite VarOccursFreeInFormula_exists, Nat.eqb_sym, desv in H.
      simpl in H.
      rewrite Subst_nosubst. reflexivity. exact H.
    + apply Nat.eqb_eq in desv. subst v0. clear H. apply f_equal.
      rewrite IsFreeForSubst_exists, Nat.eqb_sym, desw in H0.
      simpl in H0. destruct (VarOccursFreeInFormula w prop) eqn:occur.
      simpl in H0.
      apply andb_prop in H0. destruct H0 as [_ occvar].
      rewrite SubstTerm_nosubst. reflexivity.
      apply Bool.negb_true_iff in occvar. exact occvar.
      rewrite Subst_nosubst, Subst_nosubst. reflexivity. 
      exact occur. exact occur.
    + apply f_equal.
      rewrite VarOccursFreeInFormula_exists, Nat.eqb_sym, desv in H; simpl in H.
      destruct (VarOccursFreeInFormula w prop) eqn:occur.
      rewrite IHprop.
      reflexivity.
      exact H.
      rewrite IsFreeForSubst_exists, Nat.eqb_sym, desw in H0.
      simpl in H0. rewrite occur in H0.
      apply andb_prop in H0. apply H0.
      rewrite (Subst_nosubst _ w), (Subst_nosubst _ w), Subst_nosubst.
      reflexivity. exact H. exact occur. exact occur.
Qed.

Lemma VarOccursFreeInFormulaVarChange : forall prop v w,
    IsLproposition prop = true
    -> VarOccursFreeInFormula v prop = false
    -> IsFreeForSubst (Lvar v) w prop = true
    -> VarOccursFreeInFormula v (Subst (Lvar v) w prop)
      = VarOccursFreeInFormula w prop.
Proof.
  intros.
  destruct (VarOccursFreeInFormula w prop) eqn:woccur.
  revert prop H v w H0 H1 woccur.
  apply (Lproposition_rect (fun prop => forall v w,
  VarOccursFreeInFormula v prop = false ->
  IsFreeForSubst (Lvar v) w prop = true ->
  VarOccursFreeInFormula w prop = true ->
  VarOccursFreeInFormula v (Subst (Lvar v) w prop) = true)).
  - (* Lrel *)
    intros.
    rewrite Subst_rel.
    apply VarOccursFreeInFormula_rel.
    apply VarOccursFreeInFormula_rel in H1.
    destruct H1 as [j [H1 H2]]. exists j.
    split. rewrite SubstTermsLength. exact H1.
    rewrite SubstTermsCoord. 2: exact H1.
    rewrite VarOccursInTermVarChange. exact H2.
    apply elemterms, H1.
    destruct (VarOccursInTerm v (CoordNat terms j)) eqn:des.
    2: reflexivity.
    pose proof (VarOccursFreeInFormula_rel v r terms) as [_ H3].
    rewrite H in H3. symmetry. apply H3.
    exists j. split. exact H1. exact des.
  - (* Lnot *)
    intros. rewrite Subst_not, VarOccursFreeInFormula_not. apply IHprop.
    rewrite VarOccursFreeInFormula_not in H. exact H.
    rewrite IsFreeForSubst_not in H0. exact H0.
    rewrite VarOccursFreeInFormula_not in H1. exact H1.
  - (* Limplies *)
    intros.
    rewrite VarOccursFreeInFormula_implies in H.
    apply Bool.orb_false_elim in H.
    rewrite IsFreeForSubst_implies in H0. apply andb_prop in H0.
    rewrite VarOccursFreeInFormula_implies in H1.
    rewrite Subst_implies, VarOccursFreeInFormula_implies.
    apply Bool.orb_prop in H1. destruct H1.
    rewrite IHg. reflexivity. apply H. apply H0. exact H1.
    rewrite IHh. rewrite Bool.orb_true_r. reflexivity. apply H. apply H0. exact H1.
  - (* Lor *)
    intros.
    rewrite VarOccursFreeInFormula_or in H.
    apply Bool.orb_false_elim in H.
    rewrite IsFreeForSubst_or in H0. apply andb_prop in H0.
    rewrite VarOccursFreeInFormula_or in H1.
    rewrite Subst_or, VarOccursFreeInFormula_or.
    apply Bool.orb_prop in H1. destruct H1.
    rewrite IHg. reflexivity. apply H. apply H0. exact H1.
    rewrite IHh. rewrite Bool.orb_true_r. reflexivity. apply H. apply H0. exact H1.
  - (* Land *)
    intros.
    rewrite VarOccursFreeInFormula_and in H.
    apply Bool.orb_false_elim in H.
    rewrite IsFreeForSubst_and in H0. apply andb_prop in H0.
    rewrite VarOccursFreeInFormula_and in H1.
    rewrite Subst_and, VarOccursFreeInFormula_and.
    apply Bool.orb_prop in H1. destruct H1.
    rewrite IHg. reflexivity. apply H. apply H0. exact H1.
    rewrite IHh. rewrite Bool.orb_true_r. reflexivity. apply H. apply H0. exact H1.
  - (* Lforall *)
    intros.
    rewrite VarOccursFreeInFormula_forall in H.
    rewrite VarOccursFreeInFormula_forall in H1.
    rewrite IsFreeForSubst_forall in H0.
    apply andb_prop in H1.
    rewrite Subst_forall.
    destruct (v =? w) eqn:desw.
    apply Nat.eqb_eq in desw. subst w.
    exfalso.
    destruct H1. rewrite Nat.eqb_refl in H1. discriminate H1.
    destruct H1 as [_ H1].
    rewrite Nat.eqb_sym, desw in H0. simpl in H0.
    rewrite VarOccursFreeInFormula_forall.
    destruct (v0 =? v) eqn:desv. exfalso. clear H.
    apply Nat.eqb_eq in desv. subst v.
    rewrite H1 in H0. simpl in H0.
    apply andb_prop in H0. destruct H0.
    rewrite VarOccursInTerm_var, Nat.eqb_refl in H0. discriminate H0.
    simpl.
    apply IHprop.
    apply H. simpl in H0.
    rewrite H1 in H0. 
    apply andb_prop in H0. apply H0. exact H1.
  - (* Lexists *)
    intros.
    rewrite VarOccursFreeInFormula_exists in H.
    rewrite VarOccursFreeInFormula_exists in H1.
    rewrite IsFreeForSubst_exists in H0.
    apply andb_prop in H1.
    rewrite Subst_exists.
    destruct (v =? w) eqn:desw.
    apply Nat.eqb_eq in desw. subst w.
    exfalso.
    destruct H1. rewrite Nat.eqb_refl in H1. discriminate H1.
    destruct H1 as [_ H1].
    rewrite Nat.eqb_sym, desw in H0. simpl in H0.
    rewrite VarOccursFreeInFormula_exists.
    destruct (v0 =? v) eqn:desv. exfalso. clear H.
    apply Nat.eqb_eq in desv. subst v.
    rewrite H1 in H0. simpl in H0.
    apply andb_prop in H0. destruct H0.
    rewrite VarOccursInTerm_var, Nat.eqb_refl in H0. discriminate H0.
    simpl.
    apply IHprop.
    apply H. simpl in H0.
    rewrite H1 in H0. 
    apply andb_prop in H0. apply H0. exact H1.
  - unfold VarOccursFreeInFormula.
    rewrite SubstSubstNested, SubstTerm_var, Nat.eqb_refl.
    2: exact H. 2: exact H0. 2: exact H1.
    rewrite Subst_nosubst, Subst_nosubst, Nat.eqb_refl. reflexivity.
    exact woccur. exact woccur.
Qed.

Lemma IsFreeForSubstVarChange : forall prop,
    IsLproposition prop = true
    -> forall u v w, IsLterm u = true
    -> VarOccursFreeInFormula v prop = false
    -> IsFreeForSubst (Lvar v) w prop = true
    -> IsFreeForSubst u v (Subst (Lvar v) w prop)
      = IsFreeForSubst u w prop.
Proof.
  apply (Lproposition_rect (fun prop => forall u v w,
    IsLterm u = true
    -> VarOccursFreeInFormula v prop = false
    -> IsFreeForSubst (Lvar v) w prop = true
    -> IsFreeForSubst u v (Subst (Lvar v) w prop)
      = IsFreeForSubst u w prop)).
  - (* Lrel *)
    intros. rewrite Subst_rel, IsFreeForSubst_rel. 
    symmetry. apply IsFreeForSubst_rel.
    unfold Lrel. rewrite CoordConsHeadNat. reflexivity.
    unfold Lrel. rewrite CoordConsHeadNat. reflexivity.
  - (* Lnot *)
    intros.
    rewrite IsFreeForSubst_not, Subst_not, IsFreeForSubst_not.
    apply IHprop.
    exact H.
    rewrite VarOccursFreeInFormula_not in H0. exact H0.
    rewrite IsFreeForSubst_not in H1. exact H1.
  - (* Limplies *)
    intros.
    rewrite VarOccursFreeInFormula_implies in H0.
    apply Bool.orb_false_elim in H0.
    rewrite IsFreeForSubst_implies in H1.
    apply andb_prop in H1.
    rewrite Subst_implies, IsFreeForSubst_implies, IsFreeForSubst_implies, IHg, IHh.
    reflexivity.
    exact H. apply H0. apply H1.
    exact H. apply H0. apply H1.
  - (* Lor *)
    intros.
    rewrite VarOccursFreeInFormula_or in H0.
    apply Bool.orb_false_elim in H0.
    rewrite IsFreeForSubst_or in H1.
    apply andb_prop in H1.
    rewrite Subst_or, IsFreeForSubst_or, IsFreeForSubst_or, IHg, IHh.
    reflexivity.
    exact H. apply H0. apply H1.
    exact H. apply H0. apply H1.
  - (* Land *)
    intros.
    rewrite VarOccursFreeInFormula_and in H0.
    apply Bool.orb_false_elim in H0.
    rewrite IsFreeForSubst_and in H1.
    apply andb_prop in H1.
    rewrite Subst_and, IsFreeForSubst_and, IsFreeForSubst_and, IHg, IHh.
    reflexivity.
    exact H. apply H0. apply H1.
    exact H. apply H0. apply H1.
  - (* Lforall *)
    intros v prop propprop IHprop u v0 w uterm vnoccur vfreesubst.
    rewrite VarOccursFreeInFormula_forall in vnoccur.
    rewrite Subst_forall, IsFreeForSubst_forall.
    destruct (v =? w) eqn:des.
    apply Nat.eqb_eq in des. subst w.
    rewrite IsFreeForSubst_forall, Nat.eqb_refl. simpl.
    destruct (v0 =? v) eqn:desv. reflexivity.
    simpl.
    destruct (VarOccursFreeInFormula v0 prop) eqn:occur.
    2: reflexivity. discriminate vnoccur.
    rewrite IsFreeForSubst_forall in vfreesubst.
    rewrite Nat.eqb_sym in des. rewrite des in vfreesubst.
    simpl in vfreesubst.
    rewrite IsFreeForSubst_forall.
    destruct (v0 =? v) eqn:desv. clear vnoccur.
    apply Nat.eqb_eq in desv. subst v. simpl.
    rewrite des.
    destruct (VarOccursFreeInFormula w prop) eqn:woccur. 2: reflexivity.
    exfalso. simpl in vfreesubst.
    apply andb_prop in vfreesubst. destruct vfreesubst.
    rewrite VarOccursInTerm_var, Nat.eqb_refl in H0. discriminate H0.
    simpl. simpl in vnoccur. 
    apply Bool.orb_prop in vfreesubst.
    destruct vfreesubst as [vfreesubst | vfreesubst].
    apply Bool.negb_true_iff in vfreesubst.
    rewrite des, vfreesubst. simpl.
    rewrite Subst_nosubst, vnoccur. reflexivity. exact vfreesubst.
    apply andb_prop in vfreesubst. destruct vfreesubst as [vfreesubst _].
    rewrite IHprop.
    f_equal. 
    rewrite VarOccursFreeInFormulaVarChange.
    rewrite des. reflexivity.
    exact propprop. exact vnoccur. exact vfreesubst.
    exact uterm. exact vnoccur. exact vfreesubst.
  - (* Lexists *)
    intros v prop propprop IHprop u v0 w uterm vnoccur vfreesubst.
    rewrite VarOccursFreeInFormula_exists in vnoccur.
    rewrite Subst_exists, IsFreeForSubst_exists.
    destruct (v =? w) eqn:des.
    apply Nat.eqb_eq in des. subst w.
    rewrite IsFreeForSubst_exists, Nat.eqb_refl. simpl.
    destruct (v0 =? v) eqn:desv. reflexivity.
    simpl.
    destruct (VarOccursFreeInFormula v0 prop) eqn:occur.
    2: reflexivity. discriminate vnoccur.
    rewrite IsFreeForSubst_exists in vfreesubst.
    rewrite Nat.eqb_sym in des. rewrite des in vfreesubst.
    simpl in vfreesubst.
    rewrite IsFreeForSubst_exists.
    destruct (v0 =? v) eqn:desv. clear vnoccur.
    apply Nat.eqb_eq in desv. subst v. simpl.
    rewrite des.
    destruct (VarOccursFreeInFormula w prop) eqn:woccur. 2: reflexivity.
    exfalso. simpl in vfreesubst.
    apply andb_prop in vfreesubst. destruct vfreesubst.
    rewrite VarOccursInTerm_var, Nat.eqb_refl in H0. discriminate H0.
    simpl. simpl in vnoccur. 
    apply Bool.orb_prop in vfreesubst.
    destruct vfreesubst as [vfreesubst | vfreesubst].
    apply Bool.negb_true_iff in vfreesubst.
    rewrite des, vfreesubst. simpl.
    rewrite Subst_nosubst, vnoccur. reflexivity. exact vfreesubst.
    apply andb_prop in vfreesubst. destruct vfreesubst as [vfreesubst _].
    rewrite IHprop.
    f_equal. 
    rewrite VarOccursFreeInFormulaVarChange.
    rewrite des. reflexivity.
    exact propprop. exact vnoccur. exact vfreesubst.
    exact uterm. exact vnoccur. exact vfreesubst.
Qed.

(* This does not extend to ill-formed propositions, because we chose
   IsFreeForSubst = false on them. *)
Lemma MaxVarFreeSubst : forall prop,
    IsLproposition prop = true
    -> forall v t,
      (forall w, VarOccursInTerm w t = true -> MaxVar prop < w)
      -> IsFreeForSubst t v prop = true.
Proof.
  apply (Lproposition_rect (fun prop => forall v t,
      (forall w, VarOccursInTerm w t = true -> MaxVar prop < w)
      -> IsFreeForSubst t v prop = true)).
  - (* Lrel *)
    intros. apply IsFreeForSubst_rel.
    unfold Lrel. rewrite CoordConsHeadNat. reflexivity.
  - intros.
    rewrite IsFreeForSubst_not.
    rewrite MaxVar_not in H. apply IHprop, H.
  - intros.
    rewrite IsFreeForSubst_implies.
    rewrite MaxVar_implies in H. 
    rewrite IHg, IHh. reflexivity.
    intros w H0. specialize (H w H0).
    exact (Nat.le_lt_trans _ _ _ (Nat.le_max_r _ _) H).
    intros w H0. specialize (H w H0).
    exact (Nat.le_lt_trans _ _ _ (Nat.le_max_l _ _) H).
  - intros.
    rewrite IsFreeForSubst_or.
    rewrite MaxVar_or in H. 
    rewrite IHg, IHh. reflexivity.
    intros w H0. specialize (H w H0).
    exact (Nat.le_lt_trans _ _ _ (Nat.le_max_r _ _) H).
    intros w H0. specialize (H w H0).
    exact (Nat.le_lt_trans _ _ _ (Nat.le_max_l _ _) H).
  - intros.
    rewrite IsFreeForSubst_and.
    rewrite MaxVar_and in H. 
    rewrite IHg, IHh. reflexivity.
    intros w H0. specialize (H w H0).
    exact (Nat.le_lt_trans _ _ _ (Nat.le_max_r _ _) H).
    intros w H0. specialize (H w H0).
    exact (Nat.le_lt_trans _ _ _ (Nat.le_max_l _ _) H).
  - intros.
    rewrite IsFreeForSubst_forall.
    rewrite MaxVar_forall in H.
    rewrite IHprop. simpl. clear IHprop.
    destruct (v0 =? v) eqn:des. reflexivity. simpl.
    destruct (VarOccursInTerm v t) eqn:vt.
    2: simpl; apply Bool.orb_true_r. exfalso.
    specialize (H v vt).
    apply (Nat.lt_irrefl v).
    refine (Nat.le_lt_trans _ _ _ _ H).
    apply Nat.le_max_l.
    intros w H0. specialize (H w H0).
    exact (Nat.le_lt_trans _ _ _ (Nat.le_max_r _ _) H).
  - intros.
    rewrite IsFreeForSubst_exists.
    rewrite MaxVar_exists in H.
    rewrite IHprop. simpl. clear IHprop.
    destruct (v0 =? v) eqn:des. reflexivity. simpl.
    destruct (VarOccursInTerm v t) eqn:vt.
    2: simpl; apply Bool.orb_true_r. exfalso.
    specialize (H v vt).
    apply (Nat.lt_irrefl v).
    refine (Nat.le_lt_trans _ _ _ _ H).
    apply Nat.le_max_l.
    intros w H0. specialize (H w H0).
    exact (Nat.le_lt_trans _ _ _ (Nat.le_max_r _ _) H).
Qed.

Lemma MaxVarFreeSubst_var : forall prop,
    IsLproposition prop = true
    -> forall v w, MaxVar prop < v
    -> IsFreeForSubst (Lvar v) w prop = true.
Proof.
  intros. apply MaxVarFreeSubst.
  exact H. intros. rewrite VarOccursInTerm_var in H1.
  apply Nat.eqb_eq in H1. subst w0. exact H0.
Qed.

Lemma IsFreeForSubstIdemVar : forall prop v,
    IsLproposition prop = true
    -> IsFreeForSubst (Lvar v) v prop = true.
Proof.
  intros. apply IsFreeForSubst_closed.
  exact H. intros. rewrite VarOccursInTerm_var.
  apply Nat.eqb_neq, H0.
Qed.

