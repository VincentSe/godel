(** Prop-valued model of IsProof IsWeakPeanoAxiom, to show its consistency.

    This both shows that IsProof is correctly implemented, and pushes the
    incompleteness of Heyting arithmetic one step further : there exists a
    Peano proposition that is neither provable, nor refutable.

    This model looks like HAstandardModel, but uses double negations before
    disjunctions and existentials, to make them classical. *)


Require Import Arith.Wf_nat.
Require Import PeanoNat.
Require Import Arith.Compare_dec.
Require Import EnumSeqNat.
Require Import Formulas.
Require Import Substitutions.
Require Import IsFreeForSubst.
Require Import PeanoAxioms.
Require Import Proofs.
Require Import HeytingModel.


(** Interpretation of Peano propositions as Prop *)

(* We use the Gödel-Gentzen double-negation translation, to model classical logic.
   The atomic propositions x = y and x <= y do not need double negations, because
   they are recursive.
   We interpret all undefined relations by False, so that we will establish
   that nothing can be proved about them. *)
Definition PAstandardModelRec (f : nat) (rec : nat -> (nat -> nat) -> Prop) (varValues : nat -> nat)
  : Prop :=
  match CoordNat f 0 with
  | LnotHead => not (rec 1 varValues)
  | LimpliesHead => rec 1 varValues -> rec 2 varValues
  | LorHead => ~~(rec 1 varValues \/ rec 2 varValues)
  | LandHead => rec 1 varValues /\ rec 2 varValues
  | LforallHead => forall n:nat, rec 2 (setValue (CoordNat f 1) n varValues)
  | LexistsHead => ~~exists n:nat, rec 2 (setValue (CoordNat f 1) n varValues)
  | LrelHead => if Nat.eqb (LengthNat f) 4 then
                 match CoordNat f 1 with
                 | 0 => HAstandardModelTerm varValues (CoordNat f 2)
                       = HAstandardModelTerm varValues (CoordNat f 3)
                 | 1 => HAstandardModelTerm varValues (CoordNat f 2)
                       <= HAstandardModelTerm varValues (CoordNat f 3)
                 | _ => False
                 end
               else False
  | _ => False
  end.

Definition PAstandardModel : nat -> (nat -> nat) -> Prop
  := TreeFoldNat PAstandardModelRec (fun _ => False).

(* Satisfaction of an arithmetical formula in the standard model.
   For a closed proposition f, varValues does not matter and be replaced by
   fun _ => 0. *)
Definition PAstandardModelSat (f : nat) : Prop :=
  forall varValues, PAstandardModel f varValues.

Lemma PAstandardModel_step : forall f,
    PAstandardModel f
    = TreeFoldNatRec PAstandardModelRec (fun _ => False) f
                     (fun k _ => PAstandardModel k).
Proof.
  intros.
  unfold PAstandardModel, TreeFoldNat. rewrite Fix_eq.
  reflexivity.
  intros. unfold PAstandardModelRec, TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat x) 0). reflexivity.
  destruct (CoordNat x 0). reflexivity.
  destruct n. rewrite H. reflexivity.
  destruct n. rewrite H,H. reflexivity.
  destruct n. rewrite H,H. reflexivity.
  destruct n. rewrite H,H. reflexivity.
  destruct n. rewrite H. reflexivity.
  destruct n. rewrite H. reflexivity.
  destruct n. reflexivity. reflexivity.
Qed.

Lemma FactorNotNotExists : forall P Q : nat -> Prop,
    (forall n, P n <-> Q n) -> (~~(exists n, P n) <-> ~~(exists n, Q n)).
Proof.
  split.
  - intros. intro abs. contradict H0; intro H0. contradict abs.
    destruct H0. exists x. rewrite <- H. apply H0.
  - intros. intro abs. contradict H0; intro H0. contradict abs.
    destruct H0. exists x. rewrite H. apply H0.
Qed.

(* TODO merge with VarIndep, by requiring equality on the free variables only. *)
Lemma PAstandardModel_ext : forall f val1 val2,
    (forall n:nat, val1 n = val2 n)
    -> (PAstandardModel f val1 <-> PAstandardModel f val2).
Proof.
  apply (Fix lt_wf (fun f => forall val1 val2,
    (forall n:nat, val1 n = val2 n)
    -> (PAstandardModel f val1 <-> PAstandardModel f val2))).
  intro f. intros.
  rewrite PAstandardModel_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat f) 0). reflexivity.
  unfold PAstandardModelRec.
  destruct (CoordNat f 0). reflexivity.
  destruct n.
  (* Lnot *)
  rewrite H. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)). exact H0.
  destruct n.
  (* Limplies *)
  rewrite (H _ (CoordLower _ _ (LengthPositive _ l)) val1 val2).
  rewrite (H _ (CoordLower _ _ (LengthPositive _ l)) val1 val2).
  reflexivity. exact H0. exact H0.
  destruct n.
  (* Lor *)
  rewrite (H _ (CoordLower _ _ (LengthPositive _ l)) val1 val2).
  rewrite (H _ (CoordLower _ _ (LengthPositive _ l)) val1 val2).
  reflexivity. exact H0. exact H0.
  destruct n.
  (* Land *)
  rewrite (H _ (CoordLower _ _ (LengthPositive _ l)) val1 val2).
  rewrite (H _ (CoordLower _ _ (LengthPositive _ l)) val1 val2).
  reflexivity. exact H0. exact H0.
  destruct n.
  (* Lforall *)
  apply FactorForall. intro n.
  rewrite (H _ (CoordLower _ _ (LengthPositive _ l))
             _ (setValue (CoordNat f 1) n val2)).
  reflexivity.
  intro k. unfold setValue. destruct (Nat.eqb k (CoordNat f 1)).
  reflexivity. apply H0.
  destruct n.
  (* Lexists *)
  apply FactorNotNotExists. intro n.
  rewrite (H _ (CoordLower _ _ (LengthPositive _ l))
             _ (setValue (CoordNat f 1) n val2)).
  reflexivity.
  intro k. unfold setValue. destruct (Nat.eqb k (CoordNat f 1)).
  reflexivity. apply H0.
  (* Lop *)
  destruct n.
  rewrite (HAstandardModelTerm_ext _ val1 val2).
  rewrite (HAstandardModelTerm_ext _ val1 val2). reflexivity.
  exact H0. exact H0. reflexivity.
Qed.

Lemma PAstandardModel_not : forall varValues f,
    PAstandardModel (Lnot f) varValues
    = ~(PAstandardModel f varValues).
Proof.
  intros. rewrite PAstandardModel_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lnot f)) 0).
  exfalso. rewrite LengthLnot in l. inversion l.
  unfold PAstandardModelRec, Lnot; rewrite CoordConsHeadNat.
  rewrite CoordConsTailNat.
  rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma PAstandardModel_or : forall varValues f g,
    PAstandardModel (Lor f g) varValues
    = ~~(PAstandardModel f varValues \/ PAstandardModel g varValues).
Proof.
  intros. rewrite PAstandardModel_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lor f g)) 0).
  exfalso. rewrite LengthLor in l. inversion l.
  unfold PAstandardModelRec, Lor; rewrite CoordConsHeadNat.
  do 3 rewrite CoordConsTailNat.
  do 2 rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma PAstandardModel_and : forall varValues f g,
    PAstandardModel (Land f g) varValues
    = (PAstandardModel f varValues /\ PAstandardModel g varValues).
Proof.
  intros. rewrite PAstandardModel_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Land f g)) 0).
  exfalso. rewrite LengthLand in l. inversion l.
  unfold PAstandardModelRec, Land; rewrite CoordConsHeadNat.
  do 3 rewrite CoordConsTailNat.
  do 2 rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma PAstandardModel_implies : forall varValues f g,
    PAstandardModel (Limplies f g) varValues
    = (PAstandardModel f varValues -> PAstandardModel g varValues).
Proof.
  intros. rewrite PAstandardModel_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Limplies f g)) 0).
  exfalso. rewrite LengthLimplies in l. inversion l.
  unfold PAstandardModelRec, Limplies; rewrite CoordConsHeadNat.
  do 3 rewrite CoordConsTailNat.
  do 2 rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma PAstandardModel_equiv : forall varValues f g,
    PAstandardModel (Lequiv f g) varValues
    <-> (PAstandardModel f varValues <-> PAstandardModel g varValues).
Proof.
  intros. unfold Lequiv.
  rewrite PAstandardModel_and, PAstandardModel_implies, PAstandardModel_implies.
  reflexivity.
Qed.

Lemma PAstandardModel_eq : forall varValues a b,
    PAstandardModel (Leq a b) varValues
    = (HAstandardModelTerm varValues a = HAstandardModelTerm varValues b).
Proof.
  intros. rewrite PAstandardModel_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Leq a b)) 0).
  unfold Leq in l. rewrite LengthLrel2 in l. inversion l.
  unfold PAstandardModelRec, Leq, Lrel2, Lrel; rewrite CoordConsHeadNat.
  do 4 rewrite LengthConsNat. simpl.
  do 6 rewrite CoordConsTailNat.
  do 3 rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma PAstandardModel_le : forall varValues a b,
    PAstandardModel (PAle a b) varValues
    = (HAstandardModelTerm varValues a <= HAstandardModelTerm varValues b).
Proof.
  intros. rewrite PAstandardModel_step.
  unfold TreeFoldNatRec, PAle.
  destruct (le_lt_dec (LengthNat (Lrel2 1 a b)) 0).
  rewrite LengthLrel2 in l. inversion l.
  unfold PAstandardModelRec, PAle, Lrel2, Lrel; rewrite CoordConsHeadNat.
  do 4 rewrite LengthConsNat. simpl.
  do 6 rewrite CoordConsTailNat.
  do 3 rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma PAstandardModel_rel : forall varValues r args,
    PAstandardModel (Lrel r args) varValues
    =  (if LengthNat args =? 2
   then
    match r with
    | 0 =>
        HAstandardModelTerm varValues (CoordNat args 0) =
        HAstandardModelTerm varValues (CoordNat args 1)
    | 1 =>
        HAstandardModelTerm varValues (CoordNat args 0) <=
        HAstandardModelTerm varValues (CoordNat args 1)
    | S (S _) => False
    end
   else False).
Proof.
  intros. rewrite PAstandardModel_step.
  unfold TreeFoldNatRec. rewrite LengthLrel. simpl.
  unfold PAstandardModelRec.
  unfold Lrel. rewrite CoordConsHeadNat.
  rewrite LengthConsNat, LengthConsNat. simpl.
  do 5 rewrite CoordConsTailNat.
  rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma PAstandardModel_forallHead : forall varValues f,
    CoordNat f 0 = LforallHead
    -> PAstandardModel f varValues
      = (forall n:nat, PAstandardModel (CoordNat f 2) (setValue (CoordNat f 1) n varValues)).
Proof.
  intros. rewrite PAstandardModel_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat f) 0).
  exfalso. rewrite CoordNatAboveLength in H.
  discriminate. exact l.
  unfold PAstandardModelRec; rewrite H.
  reflexivity.
Qed.

Lemma PAstandardModel_forall : forall varValues v f,
    PAstandardModel (Lforall v f) varValues
    = (forall n:nat, PAstandardModel f (setValue v n varValues)).
Proof.
  intros.
  rewrite PAstandardModel_forallHead.
  rewrite CoordNat_forall_1, CoordNat_forall_2.
  reflexivity.
  unfold Lforall.
  rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma PAstandardModel_exists : forall varValues v f,
    PAstandardModel (Lexists v f) varValues
    = ~~(exists n:nat, PAstandardModel f (setValue v n varValues)).
Proof.
  intros. rewrite PAstandardModel_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lexists v f)) 0).
  exfalso. rewrite LengthLexists in l. inversion l.
  unfold PAstandardModelRec, Lexists; rewrite CoordConsHeadNat.
  do 3 rewrite CoordConsTailNat.
  do 2 rewrite CoordConsHeadNat.
  reflexivity.
Qed.


(** Evaluations of substitutions by PAstandardModel *)

Lemma VarIndepTerm : forall t v (varValues : nat -> nat) y,
    VarOccursInTerm v t = false
    -> (HAstandardModelTerm (setValue v y varValues) t
       = HAstandardModelTerm varValues t).
Proof.
  apply (Fix lt_wf (fun t => forall v (varValues : nat -> nat) y,
                        VarOccursInTerm v t = false
    -> (HAstandardModelTerm (setValue v y varValues) t
       = HAstandardModelTerm varValues t))).
  intros t IHt v varValues y H.
  rewrite HAstandardModelTerm_step, HAstandardModelTerm_step.
  unfold TreeFoldNatRec.
  assert (VarOccursInTerm v t = false) by (exact H).
  unfold VarOccursInTerm in H0.
  apply Bool.negb_false_iff in H0.
  rewrite SubstTerm_step in H0.
  unfold TreeFoldNatRec in H0.
  destruct (le_lt_dec (LengthNat t) 0).
  reflexivity.
  unfold HAstandardModelTermRec.
  unfold SubstTermRec in H0.
  apply Nat.eqb_eq in H0.
  destruct (CoordNat t 0) eqn:headT. reflexivity.
  do 7 (destruct n; [reflexivity|]).
  destruct n.
  (* Lop, go through each PAmodel's operation according to the length of t. *)
  destruct (LengthNat t) eqn:lenT. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n.
  (* Successor *)
  rewrite IHt. reflexivity.
  rewrite <- lenT in l.
  exact (CoordLower _ _ (LengthPositive _ l)).
  destruct (VarOccursInTerm v (CoordNat t 2)) eqn:des. 2: reflexivity.
  pose proof (VarOccursInTerm_opHead v t headT) as [_ H1].
  rewrite H in H1. symmetry. apply H1.
  exists 0. split. rewrite lenT. auto. exact des.
  destruct n.
  (* Addition and multiplication *)
  2: reflexivity.
  rewrite IHt, IHt. reflexivity.
  rewrite <- lenT in l.
  exact (CoordLower _ _ (LengthPositive _ l)).
  destruct (VarOccursInTerm v (CoordNat t 3)) eqn:des. 2: reflexivity.
  pose proof (VarOccursInTerm_opHead v t headT) as [_ H1].
  rewrite H in H1. symmetry. apply H1.
  exists 1. split. 
  rewrite lenT. apply Nat.le_refl. exact des.
  rewrite <- lenT in l.
  exact (CoordLower _ _ (LengthPositive _ l)).
  destruct (VarOccursInTerm v (CoordNat t 2)) eqn:des. 2: reflexivity.
  pose proof (VarOccursInTerm_opHead v t headT) as [_ H1].
  rewrite H in H1. symmetry. apply H1.
  exists 0. split. rewrite lenT. apply le_n_S, le_0_n. exact des.
  (* Lvar *)
  destruct n. 2: reflexivity.
  unfold setValue.
  destruct (CoordNat t 1 =? v).
  rewrite <- H0 in l. inversion l. reflexivity.
Qed.

Lemma VarIndep : forall f v (varValues : nat -> nat) y,
    VarOccursFreeInFormula v f = false
    -> (PAstandardModel f (setValue v y varValues)
       <-> PAstandardModel f varValues).
Proof.
  apply (Fix lt_wf (fun f => forall (v : nat) (varValues : nat -> nat) (y : nat),
  VarOccursFreeInFormula v f = false ->
  PAstandardModel f (setValue v y varValues) <-> PAstandardModel f varValues)).
  intros f IHf v varValues y nooccur.
  apply Bool.negb_false_iff, Nat.eqb_eq in nooccur.
  rewrite PAstandardModel_step. unfold TreeFoldNatRec.
  rewrite Subst_step in nooccur. unfold TreeFoldNatRec in nooccur.
  destruct (le_lt_dec (LengthNat f) 0).
  reflexivity.
  unfold SubstRec in nooccur.
  unfold PAstandardModelRec.
  destruct (CoordNat f 0) eqn:headF.
  (* Lnot *)
  reflexivity. destruct n. rewrite IHf. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nooccur at 2.
  rewrite CoordNat_not_1. reflexivity.
  destruct n.
  (* Limplies *)
  rewrite IHf,IHf. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nooccur at 2.
  rewrite CoordNat_implies_2. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nooccur at 2.
  rewrite CoordNat_implies_1. reflexivity.
  destruct n.
  (* Lor *)
  rewrite IHf,IHf. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nooccur at 2.
  rewrite CoordNat_or_2. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nooccur at 2.
  rewrite CoordNat_or_1. reflexivity.
  destruct n.
  (* Land *)
  rewrite IHf,IHf. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nooccur at 2.
  rewrite CoordNat_and_2. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nooccur at 2.
  rewrite CoordNat_and_1. reflexivity.
  destruct n.
  (* Lforall *)
  apply FactorForall; intro n.
  destruct (CoordNat f 1 =? v) eqn:des.
  apply Nat.eqb_eq in des.
  rewrite des.
  rewrite (PAstandardModel_ext
             _ _ _ (SetSetValueIdem varValues v _ _)).
  reflexivity.
  apply EqNat.beq_nat_false in des.
  rewrite (PAstandardModel_ext
             _ _ _ (SetSetValueCommute varValues _ _ _ _ des)).
  rewrite IHf. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nooccur at 2.
  rewrite CoordNat_forall_2. reflexivity.
  destruct n.
  (* Lexists *)
  apply FactorNotNotExists; intro n.
  destruct (CoordNat f 1 =? v) eqn:des.
  apply Nat.eqb_eq in des.
  rewrite des.
  rewrite (PAstandardModel_ext
             _ _ _ (SetSetValueIdem varValues v _ _)).
  reflexivity.
  apply EqNat.beq_nat_false in des.
  rewrite (PAstandardModel_ext
             _ _ _ (SetSetValueCommute varValues _ _ _ _ des)).
  rewrite IHf. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nooccur at 2.
  rewrite CoordNat_exists_2. reflexivity.
  destruct n.
  (* Lrel, 2 cases Leq and PAle *)
  2: reflexivity.
  destruct (LengthNat f) eqn:lenF. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. 2: reflexivity. simpl.
  assert (LengthNat (TailNat (TailNat f)) = 2) as H.
  { rewrite LengthTailNat, LengthTailNat, lenF. reflexivity. }
  unfold SubstTerms, MapNat in nooccur.
  rewrite LengthTailNat, LengthTailNat, lenF in nooccur.
  simpl in nooccur. 
  rewrite VarIndepTerm, VarIndepTerm. reflexivity.
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nooccur at 2.
  rewrite CoordNat_rel.
  rewrite CoordConsTailNat, CoordConsHeadNat.
  reflexivity.
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nooccur at 2.
  rewrite CoordNat_rel.
  rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma PAstandardModel_SubstTerm : forall t u v varValues,
    HAstandardModelTerm varValues (SubstTerm u v t)
    = HAstandardModelTerm (setValue v (HAstandardModelTerm varValues u) varValues) t.
Proof.
  apply (Fix lt_wf (fun t => forall u v varValues,
    HAstandardModelTerm varValues (SubstTerm u v t)
    = HAstandardModelTerm (setValue v (HAstandardModelTerm varValues u) varValues) t)).
  intros t IHt u v varValues.
  rewrite SubstTerm_step.
  rewrite (HAstandardModelTerm_step _ t).
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat t) 0).
  - reflexivity.
  - pose proof (LengthPositive t l) as tpos.
    unfold SubstTermRec. unfold HAstandardModelTermRec.
    destruct (CoordNat t 0) eqn:headT.
    reflexivity.
    do 7 (destruct n; [reflexivity|]).
    destruct n. 
    + (* case Lop, i.e. PAzero, PAsucc, PAplus or PAmult *)
      destruct (LengthNat t) eqn:lent.
      exfalso; inversion l. clear l.
      destruct n.
      exact (HAstandardModelTerm_length1 _ _ headT lent).
      destruct n.
      (* case PAzero *)
      exact (HAstandardModelTerm_length2 _ _ headT lent).
      destruct n.
      (* case PAsucc *)
      rewrite <- (IHt (CoordNat t 2) (CoordLower t 2 tpos)).
      simpl.
      do 3 rewrite LengthTailNat.
      rewrite lent. simpl.
      rewrite headT.
      rewrite HAstandardModelTerm_length3.
      do 2 rewrite CoordConsTailNat.
      rewrite CoordConsHeadNat.
      reflexivity.
      apply CoordConsHeadNat.
      do 3 rewrite LengthConsNat.
      do 3 rewrite LengthTailNat. rewrite lent. reflexivity.
      destruct n.
      (* case PAsucc or PAmult *)
      simpl.
      do 9 rewrite LengthTailNat.
      rewrite lent. simpl.
      do 3 rewrite LengthConsNat. simpl.
      do 3 rewrite LengthTailNat. rewrite lent. simpl.
      rewrite HAstandardModelTerm_length4.
      do 6 rewrite CoordConsTailNat.
      do 3 rewrite CoordConsHeadNat.
      do 4 rewrite CoordTailNat.
      do 3 rewrite CoordConsTailNat.
      do 2 rewrite CoordConsHeadNat.
      rewrite IHt, IHt. reflexivity.
      exact (CoordLower t 3 tpos).
      exact (CoordLower t 2 tpos).
      do 2 rewrite CoordConsHeadNat. exact headT.
      do 4 rewrite LengthConsNat.
      do 4 rewrite LengthTailNat.
      do 3 rewrite LengthConsNat.
      simpl.
      do 3 rewrite LengthTailNat. rewrite lent. reflexivity.
      (* case length too high *)
      apply HAstandardModelTerm_length5.
      rewrite <- headT.
      apply SubstLopTermHead.
      rewrite SubstLopTermLength.
      rewrite lent.
      do 5 apply le_n_S. apply le_0_n.
    + (* case Lvar *)
      destruct n. 2: reflexivity. clear IHt.
      unfold setValue.
      destruct (CoordNat t 1 =? v) eqn:des.
      reflexivity.
      rewrite HAstandardModelTerm_step.
      unfold TreeFoldNatRec.
      destruct (le_lt_dec (LengthNat t) 0).
      exfalso. inversion l0. rewrite H0 in l.
      exact (Nat.lt_irrefl 0 l).
      unfold HAstandardModelTermRec. rewrite headT. reflexivity. 
Qed.

Lemma PAstandardModel_Subst : forall prop u v (varValues : nat -> nat),
    IsFreeForSubst u v prop = true
    -> (PAstandardModel (Subst u v prop) varValues
       <-> PAstandardModel prop (setValue v (HAstandardModelTerm varValues u) varValues)).
Proof.
  apply (Fix lt_wf (fun prop => forall u v (varValues : nat -> nat),
    IsFreeForSubst u v prop = true
    -> (PAstandardModel (Subst u v prop) varValues
       <-> PAstandardModel prop (setValue v (HAstandardModelTerm varValues u) varValues)))).
  intros prop IHprop u v varValues free.
  rewrite Subst_step.
  unfold TreeFoldNatRec.
  rewrite (PAstandardModel_step prop).
  unfold TreeFoldNatRec.
  rewrite IsFreeForSubst_step in free.
  unfold TreeFoldNatRec in free.
  destruct (le_lt_dec (LengthNat prop) 0). discriminate.
  unfold IsFreeForSubstRec in free.
  unfold PAstandardModelRec.
  unfold SubstRec.
  destruct (CoordNat prop 0) eqn:headProp. discriminate.
  destruct n.
  (* Lnot *)
  rewrite PAstandardModel_not, IHprop. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  exact free.
  destruct n.
  (* Limplies *)
  apply andb_prop in free.
  rewrite PAstandardModel_implies.
  rewrite IHprop, IHprop. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply free.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply free.
  destruct n.
  (* Lor *)
  apply andb_prop in free.
  rewrite PAstandardModel_or.
  rewrite IHprop, IHprop. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply free.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply free.
  destruct n.
  (* Land *)
  apply andb_prop in free.
  rewrite PAstandardModel_and.
  rewrite IHprop, IHprop. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply free.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply free.
  destruct n.
  (* Lforall : 3 cases, same var, no subst and recurse.
     The first 2 cases could be merged. *)
  apply Bool.orb_prop in free.
  rewrite PAstandardModel_forall.
  apply FactorForall. intro n.
  destruct (CoordNat prop 1 =? v) eqn:eqvar.
  apply Nat.eqb_eq in eqvar. subst v.
  symmetry.
  rewrite (PAstandardModel_ext _ _ (setValue (CoordNat prop 1) n varValues)).
  reflexivity.
  intro k. apply SetSetValueIdem.
  destruct free as [nosubst | free].
  clear IHprop.
  apply Bool.negb_true_iff in nosubst.
  rewrite VarOccursFreeInFormula_forallHead in nosubst.
  2: exact headProp.
  apply Bool.negb_false_iff, Nat.eqb_eq in nosubst.
  rewrite eqvar in nosubst.
  assert (VarOccursFreeInFormula v (CoordNat prop 2) = false) as nosubst2.
  { apply Bool.negb_false_iff.
    rewrite <- nosubst at 2. rewrite CoordNat_forall_2.
    apply Nat.eqb_refl. } 
  symmetry.
  rewrite (PAstandardModel_ext _ _ (setValue v (HAstandardModelTerm varValues u) (setValue (CoordNat prop 1) n varValues))).
  2: apply SetSetValueCommute.
  rewrite VarIndep.
  rewrite Subst_nosubst. reflexivity.
  exact nosubst2. exact nosubst2.
  intro abs. rewrite abs, Nat.eqb_refl in eqvar. discriminate.
  apply andb_prop in free.
  rewrite IHprop.
  rewrite (PAstandardModel_ext _ _ (setValue (CoordNat prop 1) n
                                             (setValue v (HAstandardModelTerm varValues u) varValues))).
  reflexivity. intro k.
  rewrite VarIndepTerm. apply SetSetValueCommute.
  intro abs. rewrite <- abs, Nat.eqb_refl in eqvar. discriminate.
  destruct free.
  apply Bool.negb_true_iff in H0. exact H0.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply free.
  destruct n.
  (* Lexists : 3 cases, same var, no subst and recurse.
     The first 2 cases could be merged. *)
  apply Bool.orb_prop in free.
  rewrite PAstandardModel_exists.
  apply FactorNotNotExists. intro n.
  destruct (CoordNat prop 1 =? v) eqn:eqvar.
  apply Nat.eqb_eq in eqvar. subst v.
  symmetry.
  rewrite (PAstandardModel_ext _ _ (setValue (CoordNat prop 1) n varValues)).
  reflexivity.
  intro k. apply SetSetValueIdem.
  destruct free as [nosubst | free].
  clear IHprop.
  apply Bool.negb_true_iff in nosubst.
  rewrite VarOccursFreeInFormula_existsHead in nosubst.
  2: exact headProp.
  apply Bool.negb_false_iff, Nat.eqb_eq in nosubst.
  rewrite eqvar in nosubst.
  assert (VarOccursFreeInFormula v (CoordNat prop 2) = false) as nosubst2.
  { apply Bool.negb_false_iff.
    rewrite <- nosubst at 2. rewrite CoordNat_exists_2.
    apply Nat.eqb_refl. } 
  symmetry.
  rewrite (PAstandardModel_ext _ _ (setValue v (HAstandardModelTerm varValues u) (setValue (CoordNat prop 1) n varValues))).
  2: apply SetSetValueCommute.
  rewrite VarIndep. rewrite Subst_nosubst. reflexivity.
  exact nosubst2. exact nosubst2.
  intro abs. rewrite abs, Nat.eqb_refl in eqvar. discriminate.
  apply andb_prop in free.
  rewrite IHprop.
  rewrite (PAstandardModel_ext _ _ (setValue (CoordNat prop 1) n
                                             (setValue v (HAstandardModelTerm varValues u) varValues))).
  reflexivity. intro k.
  rewrite VarIndepTerm. apply SetSetValueCommute.
  intro abs. rewrite <- abs, Nat.eqb_refl in eqvar. discriminate.
  destruct free.
  apply Bool.negb_true_iff in H0. exact H0.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply free.
  destruct n. 
  (* Lrel *)
  2: reflexivity.
  rewrite PAstandardModel_rel, SubstTermsLength.
  rewrite LengthTailNat, LengthTailNat.
  destruct (LengthNat prop) eqn:lenProp. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. 2: reflexivity. simpl (pred (pred 4)).
  rewrite Nat.eqb_refl, Nat.eqb_refl.
  rewrite SubstTermsCoord, SubstTermsCoord.
  rewrite PAstandardModel_SubstTerm, PAstandardModel_SubstTerm.
  rewrite CoordTailNat, CoordTailNat.
  rewrite CoordTailNat, CoordTailNat.
  reflexivity.
  rewrite LengthTailNat, LengthTailNat, lenProp.
  apply Nat.le_refl. auto.
  rewrite LengthTailNat, LengthTailNat, lenProp. simpl. auto.
Qed.


(** Satisfaction of propositional logic in the standard model. *)

(* This is both an internal and external property of the standard model.
   Internally the model satisfies ~~A->A, and externally it suffices to prove
   ~~PAstandardmodel prop varValues to prove PAstandardmodel prop varValues. *)
Lemma PAstandardModelNotNot : forall (prop : nat) (varValues : nat -> nat),
    ~~PAstandardModel prop varValues
    -> PAstandardModel prop varValues.
Proof.
  apply (Fix lt_wf (fun prop =>  forall (varValues : nat -> nat),
  ~ ~ PAstandardModel prop varValues -> PAstandardModel prop varValues)).
  intros prop IHprop varValues.
  rewrite PAstandardModel_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat prop) 0).
  intro abs. contradict abs. intro abs. contradiction.
  unfold PAstandardModelRec.
  destruct (CoordNat prop 0).
  intro abs. contradict abs. intro abs. contradiction.
  destruct n.
  (* Lnot *)
  intros notnotprop H. contradict notnotprop; intro notnotprop. contradiction.
  destruct n.
  (* Limplies *)
  intros notnotprop H.
  apply IHprop.
  exact (CoordLower _ _ (LengthPositive _ l)).
  intro abs. contradict notnotprop; intro notnotprop.
  contradict abs. apply notnotprop, H.
  destruct n.
  (* Lor *)
  intros notnotprop abs.
  contradict notnotprop; intro notnotprop.
  contradict notnotprop; intro notnotprop.
  contradict abs. exact notnotprop.
  destruct n.
  (* Land *)
  intro notnotprop. split. apply IHprop.
  exact (CoordLower _ _ (LengthPositive _ l)).
  intro abs. contradict notnotprop; intro notnotprop.
  contradict abs. apply notnotprop.
  apply IHprop.
  exact (CoordLower _ _ (LengthPositive _ l)).
  intro abs. contradict notnotprop; intro notnotprop.
  contradict abs. apply notnotprop.
  destruct n.
  (* Lforall *)
  intros notnotprop n.
  apply IHprop.
  exact (CoordLower _ _ (LengthPositive _ l)).
  intro abs. contradict notnotprop; intro notnotprop.
  contradict abs. apply notnotprop.
  destruct n.
  (* Lexists *)
  intros notnotprop abs.
  contradict notnotprop; intro notnotprop.
  revert abs. exact notnotprop.
  destruct n.
  (* Lrel *)
  clear IHprop. intro notnotprop.
  destruct (LengthNat prop =? 4).
  destruct (CoordNat prop 1).
  destruct (Nat.eq_dec (HAstandardModelTerm varValues (CoordNat prop 2))
                       (HAstandardModelTerm varValues (CoordNat prop 3))).
  exact e. contradiction.
  destruct n.
  destruct (le_dec (HAstandardModelTerm varValues (CoordNat prop 2))
                   (HAstandardModelTerm varValues (CoordNat prop 3))).
  exact l0. contradiction.
  contradict notnotprop. intro abs. contradiction.
  contradict notnotprop; intro notnotprop. contradiction.
  intro abs. contradict abs. intro abs. contradiction.
Qed.

(* ~~X1 -> X1, the only classical axiom *)
Lemma Ax4Satisfied : forall (prop : nat),
  IsPropAx4 prop = true -> PAstandardModelSat prop.
Proof.
  intros prop H varValues. 
  do 4 (apply andb_prop in H; destruct H).
  apply Nat.eqb_eq in H3. rewrite H3, PAstandardModel_implies.
  apply Nat.eqb_eq in H2. rewrite H2, PAstandardModel_not.
  apply Nat.eqb_eq in H1. rewrite H1, PAstandardModel_not.
  apply Nat.eqb_eq in H0. rewrite H0.
  apply PAstandardModelNotNot. 
Qed.

(* This internal property of the model does not extend to a constructive
   external excluded middle 
   PAstandardModel prop varValues \/ ~PAstandardModel prop varValues *)
Lemma ExcludedMiddleSatisfied : forall prop,
    PAstandardModelSat (Lor prop (Lnot prop)).
Proof.
  intros prop varValues. rewrite PAstandardModel_or.
  intro abs. assert (~~PAstandardModel prop varValues).
  intro H. contradict abs. right. rewrite PAstandardModel_not. exact H.
  contradict H; intro H. contradict abs. left. exact H.
Qed.

(* (X1 -> (X2 -> X3)) -> ((X1 -> X2) -> (X1 -> X3)) *)
Lemma Ax2Satisfied : forall (prop : nat),
  IsPropAx2 prop = true -> PAstandardModelSat prop.
Proof.
  intros prop H varValues. 
  do 10 (apply andb_prop in H; destruct H).
  apply Nat.eqb_eq in H9.
  rewrite H9, PAstandardModel_implies. intro X1X2X3.
  apply Nat.eqb_eq in H6.
  rewrite H6, PAstandardModel_implies. intro X1X2.
  apply Nat.eqb_eq in H4.
  rewrite H4, PAstandardModel_implies. intro X1.
  apply Nat.eqb_eq in H5.
  rewrite H5, PAstandardModel_implies in X1X2.
  apply Nat.eqb_eq in H2.
  rewrite <- H2 in X1.
  apply Nat.eqb_eq in H3.
  rewrite <- H3 in X1X2.
  specialize (X1X2 X1).
  apply Nat.eqb_eq in H8.
  rewrite H8, PAstandardModel_implies in X1X2X3.
  specialize (X1X2X3 X1).
  apply Nat.eqb_eq in H7.
  rewrite H7, PAstandardModel_implies in X1X2X3.
  apply Nat.eqb_eq in H1.
  rewrite H1 in X1X2X3.
  specialize (X1X2X3 X1X2).
  apply Nat.eqb_eq in H0.
  rewrite <- H0. exact X1X2X3.
Qed.

(* X1 -> (~X1 -> X2) *)
Lemma Ax5Satisfied : forall (prop : nat),
  IsPropAx5 prop = true -> PAstandardModelSat prop.
Proof.
  intros prop H varValues. 
  do 4 (apply andb_prop in H; destruct H).
  apply Nat.eqb_eq in H3.
  apply Nat.eqb_eq in H2.
  apply Nat.eqb_eq in H0.
  apply Nat.eqb_eq in H1.
  rewrite H3, PAstandardModel_implies.
  intro X1.
  rewrite H2, PAstandardModel_implies.
  intro notX1.
  rewrite H1, PAstandardModel_not, <- H0 in notX1.
  contradiction.
Qed.

(* X1 -> (X2 -> (X1 /\ X2)) *)
Lemma Ax6Satisfied : forall (prop : nat),
  IsPropAx6 prop = true -> PAstandardModelSat prop.
Proof.
  intros prop H varValues.
  do 5 (apply andb_prop in H; destruct H).
  apply Nat.eqb_eq in H0.
  apply Nat.eqb_eq in H1.
  apply Nat.eqb_eq in H2.
  apply Nat.eqb_eq in H3.
  apply Nat.eqb_eq in H4.
  rewrite H4, PAstandardModel_implies.
  intro X1.
  rewrite H3, PAstandardModel_implies.
  intro X2.
  rewrite H2, PAstandardModel_and.
  split.
  rewrite <- H1. exact X1.
  rewrite <- H0. exact X2.
Qed.

(* (X1 -> X3) -> ((X2 -> X3) -> ((X1 \/ X2) -> X3)) *)
Lemma Ax11Satisfied : forall (prop : nat),
  IsPropAx11 prop = true -> PAstandardModelSat prop.
Proof.
  intros prop H varValues.
  do 10 (apply andb_prop in H; destruct H).
  apply Nat.eqb_eq in H9.
  apply Nat.eqb_eq in H8.
  apply Nat.eqb_eq in H7.
  apply Nat.eqb_eq in H6.
  apply Nat.eqb_eq in H5.
  apply Nat.eqb_eq in H4.
  apply Nat.eqb_eq in H3.
  apply Nat.eqb_eq in H2.
  apply Nat.eqb_eq in H1.
  apply Nat.eqb_eq in H0.
  rewrite H9, PAstandardModel_implies. intro X1implX3.
  rewrite H7, PAstandardModel_implies. intro X2implX3.
  rewrite H5, PAstandardModel_implies. intro X1orX2.
  rewrite H4, PAstandardModel_or in X1orX2.
  apply PAstandardModelNotNot.
  intro abs; contradict X1orX2; intro X1orX2; contradict abs.
  rewrite <- H0.
  destruct X1orX2 as [X1 | X2].
  rewrite H8, PAstandardModel_implies in X1implX3.
  apply X1implX3. rewrite <- H3 in X1. exact X1.
  rewrite H6, PAstandardModel_implies, <- H1 in X2implX3.
  apply X2implX3. rewrite <- H2 in X2. exact X2.
Qed.

Lemma PropositionalAxiomsSatisfied : forall prop,
    IsPropositionalAxiom prop = true
    -> PAstandardModelSat prop.
Proof.
  intros prop H varValues.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  - (* X1 -> (X2 -> X1) *)
    do 3 (apply andb_prop in H; destruct H).
    apply Nat.eqb_eq in H2.
    rewrite H2, PAstandardModel_implies. intro X1.
    apply Nat.eqb_eq in H1.
    rewrite H1, PAstandardModel_implies.
    intro J.
    apply Nat.eqb_eq in H0.
    rewrite H0 in X1. exact X1.
  - apply Ax2Satisfied, H.
  - (* (X1 -> X2) -> ((X1 -> ~X2) -> ~X1) *)
    do 9 (apply andb_prop in H; destruct H).
    apply Nat.eqb_eq in H8.
    apply Nat.eqb_eq in H7.
    apply Nat.eqb_eq in H6.
    apply Nat.eqb_eq in H5.
    apply Nat.eqb_eq in H4.
    apply Nat.eqb_eq in H3.
    apply Nat.eqb_eq in H1.
    apply Nat.eqb_eq in H2.
    apply Nat.eqb_eq in H0.
    rewrite H8, PAstandardModel_implies; intro X1implX2.
    rewrite H6, PAstandardModel_implies; intro X1implnotX2.
    rewrite H4, PAstandardModel_not; intro X1.
    rewrite H5, PAstandardModel_implies in X1implnotX2.
    rewrite H7, PAstandardModel_implies in X1implX2.
    rewrite <- H1 in X1. specialize (X1implX2 X1).
    rewrite <- H2 in X1implnotX2. specialize (X1implnotX2 X1).
    rewrite H3, PAstandardModel_not, <- H0 in X1implnotX2.
    contradiction.
  - apply Ax5Satisfied, H.
  - apply Ax6Satisfied, H.
  - (* (X1 /\ X2) -> X1 *)
    do 3 (apply andb_prop in H; destruct H).
    apply Nat.eqb_eq in H2.
    rewrite H2, PAstandardModel_implies.
    intro X1andX2.
    apply Nat.eqb_eq in H1.
    rewrite H1, PAstandardModel_and in X1andX2.
    apply Nat.eqb_eq in H0.
    rewrite <- H0. apply X1andX2.
  - (* (X1 /\ X2) -> X2 *)
    do 3 (apply andb_prop in H; destruct H).
    apply Nat.eqb_eq in H2.
    rewrite H2, PAstandardModel_implies.
    intro X1andX2.
    apply Nat.eqb_eq in H1.
    rewrite H1, PAstandardModel_and in X1andX2.
    apply Nat.eqb_eq in H0.
    rewrite <- H0. apply X1andX2.
  - (* X1 -> (X1 \/ X2) *)
    do 3 (apply andb_prop in H; destruct H).
    apply Nat.eqb_eq in H2.
    rewrite H2, PAstandardModel_implies.
    intro X1.
    apply Nat.eqb_eq in H1.
    rewrite H1, PAstandardModel_or.
    intro abs; contradict abs.
    left.
    apply Nat.eqb_eq in H0.
    rewrite <- H0. exact X1.
  - (* X2 -> (X1 \/ X2) *)
    do 3 (apply andb_prop in H; destruct H).
    apply Nat.eqb_eq in H2.
    rewrite H2, PAstandardModel_implies.
    intro X2.
    apply Nat.eqb_eq in H1.
    rewrite H1, PAstandardModel_or.
    intro abs; contradict abs.
    right.
    apply Nat.eqb_eq in H0.
    rewrite <- H0. exact X2.
  - apply Ax11Satisfied, H.
Qed.


(** Satisfaction of the Peano axioms in the standard model. *)

Lemma PAaxiomsSatisfied : forall prop,
    IsWeakPeanoAxiom prop = true -> PAstandardModelSat prop.
Proof.
  intros prop H varValues. 
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  - apply Nat.eqb_eq in H. subst prop.
    unfold PAax1. rewrite PAstandardModel_forall.
    intro n. rewrite PAstandardModel_not, PAstandardModel_eq.
    rewrite HAstandardModelTerm_succ.
    rewrite HAstandardModelTerm_zero.
    discriminate.
  - apply Nat.eqb_eq in H. subst prop.
    unfold PAax2. rewrite PAstandardModel_forall.
    intro n. rewrite PAstandardModel_or, PAstandardModel_eq.
    intro abs; contradict abs.
    rewrite PAstandardModel_exists.
    rewrite HAstandardModelTerm_var.
    unfold setValue at 1; simpl.
    rewrite HAstandardModelTerm_zero.
    destruct n. left. reflexivity.
    right. intro abs; contradict abs. exists n.
    rewrite PAstandardModel_eq, HAstandardModelTerm_var.
    rewrite HAstandardModelTerm_succ, HAstandardModelTerm_var.
    reflexivity.
  - apply Nat.eqb_eq in H. subst prop.
    unfold PAax3. rewrite PAstandardModel_forall.
    intro n. rewrite PAstandardModel_forall. intro p.
    rewrite PAstandardModel_implies. intro succEq.
    rewrite PAstandardModel_eq in succEq.
    rewrite PAstandardModel_eq.
    rewrite HAstandardModelTerm_succ, HAstandardModelTerm_succ in succEq.
    assert (forall x y : nat, S x = S y -> x = y) as H.
    intros. inversion H. reflexivity.
    apply H, succEq.
  - apply Nat.eqb_eq in H. subst prop.
    unfold PAax4. rewrite PAstandardModel_forall.
    intro n. rewrite PAstandardModel_eq.
    rewrite HAstandardModelTerm_plus.
    rewrite HAstandardModelTerm_zero.
    rewrite Nat.add_0_r. reflexivity.
  - apply Nat.eqb_eq in H. subst prop.
    unfold PAax5.
    rewrite PAstandardModel_forall. intro n.
    rewrite PAstandardModel_forall. intro p.
    rewrite PAstandardModel_eq.
    rewrite HAstandardModelTerm_plus.
    rewrite HAstandardModelTerm_succ.
    rewrite HAstandardModelTerm_succ.
    rewrite HAstandardModelTerm_plus.
    rewrite Nat.add_succ_r. reflexivity.
  - apply Nat.eqb_eq in H. subst prop.
    unfold PAax6.
    rewrite PAstandardModel_forall. intro n.
    rewrite PAstandardModel_eq.
    rewrite HAstandardModelTerm_mult.
    rewrite HAstandardModelTerm_zero.
    apply Nat.mul_0_r.
  - apply Nat.eqb_eq in H. subst prop.
    unfold PAax7.
    rewrite PAstandardModel_forall. intro n.
    rewrite PAstandardModel_forall. intro p.
    rewrite PAstandardModel_eq.
    rewrite HAstandardModelTerm_mult.
    rewrite HAstandardModelTerm_plus.
    rewrite HAstandardModelTerm_mult.
    rewrite HAstandardModelTerm_succ.
    apply Nat.mul_succ_r.
  - apply Nat.eqb_eq in H. subst prop.
    unfold PAorder.
    rewrite PAstandardModel_forall. intro n.
    rewrite PAstandardModel_forall. intro p.
    rewrite PAstandardModel_equiv, PAstandardModel_le.
    rewrite PAstandardModel_exists.
    rewrite HAstandardModelTerm_var, HAstandardModelTerm_var.
    change (setValue 1 p (setValue 0 n varValues) 0 <= setValue 1 p (setValue 0 n varValues) 1)
      with (n <= p).
    split.
    + intro le. apply Nat.le_exists_sub in le.
      intro abs; contradict abs.
      destruct le, H. exists x. subst p.
      rewrite PAstandardModel_eq.
      rewrite HAstandardModelTerm_var.
      rewrite HAstandardModelTerm_plus.
      rewrite HAstandardModelTerm_var, HAstandardModelTerm_var.
      reflexivity.
    + intro H.
      destruct (le_lt_dec n p). exact l.
      exfalso. contradict H; intros [k H].
      rewrite PAstandardModel_eq in H.
      rewrite HAstandardModelTerm_plus, HAstandardModelTerm_var in H.
      rewrite HAstandardModelTerm_var, HAstandardModelTerm_var in H.
      unfold setValue in H; simpl in H. subst p.
      rewrite <- (Nat.add_0_l n) in l at 2.
      apply (Nat.add_lt_mono_r k 0 n) in l. inversion l.
  - apply Ax4Satisfied, H.
Qed.


Lemma IndependenceOfPremiseSatisfied : forall prop,
    IsIndependenceOfPremise prop = true
    -> PAstandardModelSat prop.
Proof.
  intros prop H varValues.
  do 9 (apply andb_prop in H; destruct H).
  apply Bool.negb_true_iff in H0.
  apply Nat.eqb_eq in H8.
  remember (CoordNat prop 1) as ForallXfg.
  remember (CoordNat prop 2) as fForallXg.
  rewrite H8, PAstandardModel_implies.
  rewrite H8, IsLproposition_implies in H.
  clear H8 HeqfForallXg HeqForallXfg prop.
  intro ForallXfg_proof.
  apply Nat.eqb_eq in H5.
  rewrite H5, PAstandardModel_implies.
  rewrite H5, IsLproposition_implies in H.
  remember (CoordNat fForallXg 1) as f.
  remember (CoordNat fForallXg 2) as ForallXg.
  clear H5 HeqForallXg Heqf fForallXg.
  apply Nat.eqb_eq in H1.
  intro f_proof.
  apply Nat.eqb_eq in H4.
  rewrite H4, PAstandardModel_forall.
  intro valX.
  apply Nat.eqb_eq in H7.
  rewrite H7, PAstandardModel_forall in ForallXfg_proof.
  specialize (ForallXfg_proof valX).
  apply Nat.eqb_eq in H6.
  apply Nat.eqb_eq in H3.
  apply Nat.eqb_eq in H2.
  rewrite H6, PAstandardModel_implies, H2, H1 in ForallXfg_proof.
  apply ForallXfg_proof.
  rewrite VarIndep, H3. exact f_proof.
  rewrite H3. apply andb_prop in H. destruct H.
  rewrite <- H1. exact H0.
Qed.

Lemma SpecializationSatisfied : forall prop,
    IsSpecialization prop = true
    -> PAstandardModelSat prop.
Proof.
  intros prop special varValues.
  apply andb_prop in special; destruct special.
  apply andb_prop in H; destruct H as [lprop isimp].
  apply Nat.eqb_eq in isimp.
  apply Bool.orb_prop in H0. destruct H0 as [isforall | isexists].
  - apply andb_prop in isforall.
    destruct isforall as [isforall H0].
    simpl in H0.
    apply andb_prop in H0; destruct H0.
    apply Nat.eqb_eq in H0.
    rewrite isimp, H0.
    apply Nat.eqb_eq in isforall.
    rewrite isforall.
    rewrite CoordNat_forall_1.
    rewrite CoordNat_forall_2.
    rewrite PAstandardModel_implies.
    intro forall_proof.
    rewrite PAstandardModel_forall in forall_proof.
    rewrite PAstandardModel_Subst.
    apply forall_proof.
    exact H.
  - apply andb_prop in isexists.
    destruct isexists as [isexists H0].
    simpl in H0.
    apply andb_prop in H0; destruct H0.
    apply Nat.eqb_eq in H0.
    rewrite isimp, H0.
    apply Nat.eqb_eq in isexists.
    rewrite isexists.
    rewrite CoordNat_exists_1, CoordNat_exists_2.
    rewrite PAstandardModel_implies.
    intro exist_proof.
    rewrite PAstandardModel_exists.
    intro abs; contradict abs.
    rewrite PAstandardModel_Subst in exist_proof.
    exists (HAstandardModelTerm varValues
                        (FindSubstTerm (CoordNat (CoordNat prop 2) 1)
                           (CoordNat (CoordNat prop 2) 2) 
                           (CoordNat prop 1))).
    exact exist_proof. exact H.
Qed.

Lemma ExistsElimSatisfied : forall prop,
    IsExistsElim prop = true
    -> PAstandardModelSat prop.
Proof.
  intros prop H varValues.
  do 9 (apply andb_prop in H; destruct H).
  apply Bool.negb_true_iff in H0.
  apply Nat.eqb_eq in H8. rewrite H8, PAstandardModel_implies.
  intro exproof.
  apply Nat.eqb_eq in H6. rewrite H6, PAstandardModel_implies.
  intro forallproof.
  apply Nat.eqb_eq in H7. rewrite H7, PAstandardModel_exists in exproof.
  apply PAstandardModelNotNot.
  intro abs; contradict exproof; intros [n exproof]; contradict abs.
  apply Nat.eqb_eq in H5. rewrite H5, PAstandardModel_forall in forallproof.
  specialize (forallproof n).
  apply Nat.eqb_eq in H4. rewrite H4, PAstandardModel_implies in forallproof.
  apply Nat.eqb_eq in H2. rewrite H2 in forallproof.
  rewrite (VarIndep (CoordNat (CoordNat prop 2) 2)) in forallproof.
  2: exact H0.
  apply forallproof.
  apply Nat.eqb_eq in H3. rewrite H3.
  apply Nat.eqb_eq in H1. rewrite H1.
  exact exproof.
Qed.

(* This works around an infinite loop at Qed *)
Lemma PAstandardModel_EqVars : forall varValues,
    PAstandardModel (EqTerms (EvenVars 0 2) (EvenVars 1 2) 1) varValues
    = (HAstandardModelTerm varValues (Lvar 0) = HAstandardModelTerm varValues (Lvar 1)
       /\ HAstandardModelTerm varValues (Lvar 2) = HAstandardModelTerm varValues (Lvar 3)).
Proof.
  intros varValues. simpl.
  rewrite PAstandardModel_and.
  rewrite PAstandardModel_eq.
  rewrite PAstandardModel_eq.
  rewrite CoordEvenVarsNat, CoordEvenVarsNat.
  rewrite CoordEvenVarsNat, CoordEvenVarsNat.
  rewrite Nat.mul_0_r, Nat.mul_1_r, Nat.add_0_r, Nat.add_0_r.
  reflexivity. apply Nat.le_refl. apply Nat.le_refl. auto. auto.
Qed.

Lemma EqualityRelationAxiomSatisfied : forall l r varValues,
    PAstandardModel (EqTerms (EvenVars 0 (l-2)) (EvenVars 1 (l-2)) (pred (l-2))) varValues
    -> (PAstandardModel
         (Lrel r (EvenVars 0 (l-2))) varValues <->
       PAstandardModel
         (Lrel r (EvenVars 1 (l-2))) varValues).
Proof.
  intros l r varValues equalities.
  rewrite PAstandardModel_rel, PAstandardModel_rel.
  rewrite LengthEvenVarsNat, LengthEvenVarsNat.
  destruct (l-2 =? 2) eqn:des.
  apply Nat.eqb_eq in des.
  rewrite des. rewrite des in equalities.
  simpl (2-1) in equalities.
  rewrite PAstandardModel_EqVars in equalities. destruct equalities.
  rewrite CoordEvenVarsNat, CoordEvenVarsNat.
  rewrite CoordEvenVarsNat, CoordEvenVarsNat.
  simpl.
  rewrite H, H0.
  reflexivity. apply Nat.le_refl.
  apply le_n_S, le_0_n.
  apply Nat.le_refl.
  apply le_n_S, le_0_n.
  reflexivity.
Qed.

Lemma EqualityAxiomsSatisfied : forall f,
    IsEqualityAxiom f = true -> PAstandardModelSat f.
Proof.
  intros f H varValues.
  apply Bool.orb_prop in H. destruct H.
  apply Bool.orb_prop in H. destruct H.
  apply Bool.orb_prop in H. destruct H.
  apply Bool.orb_prop in H. destruct H.
  - apply Nat.eqb_eq in H. rewrite H, PAstandardModel_eq. reflexivity.
  - apply Nat.eqb_eq in H.
    rewrite H, PAstandardModel_implies, PAstandardModel_eq, PAstandardModel_eq.
    intro H0. symmetry. exact H0.
  - apply Nat.eqb_eq in H.
    rewrite H, PAstandardModel_implies, PAstandardModel_and.
    rewrite PAstandardModel_eq, PAstandardModel_eq, PAstandardModel_eq.
    intros [H0 H1].
    rewrite H0. exact H1.
  - apply andb_prop in H. destruct H.
    apply andb_prop in H. destruct H.
    apply andb_prop in H. destruct H.
    apply Nat.eqb_eq in H.
    apply Nat.eqb_eq in H0.
    apply Nat.eqb_eq in H1.
    apply Nat.leb_le in H2.
    rewrite H, PAstandardModel_implies, H0, H1.
    rewrite PAstandardModel_eq.
    destruct ((LengthNat (CoordNat (CoordNat f 2) 2))) eqn:len.
    inversion H2.
    destruct n. inversion H2.
    destruct n. inversion H2. simpl.
    clear H2.
    simpl in H1. simpl in H0. 
    destruct n.
    (* PAsucc *)
    simpl in H1. simpl in H0. simpl.
    rewrite HAstandardModelTerm_length3.
    2: apply CoordConsHeadNat.
    rewrite (HAstandardModelTerm_length3
               varValues (Lop (CoordNat (CoordNat (CoordNat f 2) 2) 1) (EvenVars 1 1))).
    2: apply CoordConsHeadNat.
    rewrite PAstandardModel_eq.
    rewrite CoordNat_op, CoordNat_op.
    intro H2. rewrite H2. reflexivity.
    rewrite LengthLop, LengthEvenVarsNat. reflexivity.
    rewrite LengthLop, LengthEvenVarsNat. reflexivity.
    destruct n.
    (* PAplus and PAmult *)
    simpl in H1. simpl in H0. simpl.
    intro H2.
    rewrite HAstandardModelTerm_length4.
    rewrite (HAstandardModelTerm_length4
               varValues (Lop (CoordNat (CoordNat (CoordNat f 2) 2) 1)
                              (EvenVars 1 2))).
    rewrite PAstandardModel_and, PAstandardModel_eq, PAstandardModel_eq in H2.
    destruct H2.
    do 4 rewrite CoordNat_op.
    rewrite H2, H3. 
    unfold Lop.
    rewrite CoordConsTailNat, CoordConsTailNat.
    rewrite CoordConsHeadNat, CoordConsHeadNat. reflexivity.
    apply CoordConsHeadNat.
    rewrite LengthLop, LengthEvenVarsNat. reflexivity.
    apply CoordConsHeadNat.
    rewrite LengthLop, LengthEvenVarsNat. reflexivity.
    intro H2.
    rewrite HAstandardModelTerm_length5, HAstandardModelTerm_length5.
    reflexivity.
    apply CoordConsHeadNat.
    rewrite LengthLop, LengthEvenVarsNat.
    do 5 apply le_n_S. apply le_0_n.
    apply CoordConsHeadNat.
    rewrite LengthLop, LengthEvenVarsNat.
    do 5 apply le_n_S. apply le_0_n.
  - intros.
    apply andb_prop in H. destruct H.
    apply andb_prop in H. destruct H.
    apply andb_prop in H. destruct H.
    apply Nat.eqb_eq in H.
    apply Nat.eqb_eq in H0.
    apply Nat.eqb_eq in H1.
    apply Nat.leb_le in H2.
    rewrite H, PAstandardModel_implies, H0, H1.
    rewrite PAstandardModel_equiv.
    apply EqualityRelationAxiomSatisfied.
Qed.

Lemma PAloopCorrection : forall l IsAxiom (proof:nat),
    l = LengthNat proof
    -> (forall n:nat, IsAxiom n = true -> PAstandardModelSat n)
    -> IsProofLoop IsAxiom proof (LengthNat proof) = true
    -> forall i:nat, i < LengthNat proof
    -> PAstandardModelSat (CoordNat proof i).
Proof.
  induction l.
  - intros. exfalso.
    rewrite <- H in H2. inversion H2.
  - intros IsAxiom proof lenproof IsAxiomSat proofloop i H varValues.
    rewrite <- lenproof in H.
    assert (l = LengthNat (TailNat proof)) as lentail.
    { rewrite LengthTailNat. destruct (LengthNat proof).
      discriminate. simpl. inversion lenproof. reflexivity. }
    subst l.
    rewrite <- lenproof in proofloop.
    simpl in proofloop.
    apply andb_prop in proofloop.
    destruct proofloop as [proofstep proofloop].
    specialize (IHl IsAxiom (TailNat proof) eq_refl IsAxiomSat proofloop).
    destruct i.
    + clear H.
      apply Bool.orb_prop in proofstep.
      destruct proofstep as [H0 | quantifier].
      apply Bool.orb_prop in H0. destruct H0 as [H0 | modus].
      apply Bool.orb_prop in H0. destruct H0 as [H0 | eqax].
      apply Bool.orb_prop in H0. destruct H0.
      apply andb_prop in H.
      apply IsAxiomSat, H.
      apply PropositionalAxiomsSatisfied, H.
      apply EqualityAxiomsSatisfied, eqax.
      (* modus ponens, use induction hypothesis on the implication formula *)
      apply IsModusPonens_true in modus.
      destruct modus as [imp [lenimp [isimp [H modus]]]].
      apply FindNat_true in modus.
      destruct modus as [hyp [H4 modus]].
      apply Nat.eqb_eq in isimp.
      pose proof (IHl imp lenimp varValues).
      rewrite H.
      rewrite isimp, PAstandardModel_implies in H0.
      specialize (IHl hyp H4 varValues).
      apply H0. clear H0.
      rewrite modus.
      apply IHl.
      (* Quantifier axioms *)
      apply Bool.orb_prop in quantifier. destruct quantifier as [H0 | exelim].
      apply Bool.orb_prop in H0. destruct H0 as [H0 | premise].
      apply Bool.orb_prop in H0. destruct H0 as [gen | special].
      (* generalization *)
      apply andb_prop in gen. destruct gen as [all gen].
      apply FindNat_true in gen. destruct gen as [p gen].
      destruct gen.
      specialize (IHl p H).
      apply Nat.eqb_eq in all. rewrite all, PAstandardModel_forall, H0.
      intro n.
      apply (IHl (setValue (CoordNat (CoordNat proof 0) 1) n varValues)).
      (* specialization *)
      apply SpecializationSatisfied, special.
      apply IndependenceOfPremiseSatisfied, premise.
      apply ExistsElimSatisfied, exelim.
    + (* use induction hypothesis *)
      specialize (IHl i).
      rewrite CoordTailNat in IHl. apply IHl.
      rewrite LengthTailNat.
      destruct (LengthNat proof). discriminate.
      inversion lenproof. subst n.
      simpl. apply le_S_n. exact H.
Qed.

Lemma PAstandardModel_correction : forall IsAxiom (prop : nat),
    (forall n:nat, IsAxiom n = true -> PAstandardModelSat n)
    -> IsProved IsAxiom prop
    -> PAstandardModelSat prop.
Proof.
  intros IsAxiom prop IsAxiomSat [proof isproof] varValues.
  apply andb_prop in isproof. destruct isproof.
  apply andb_prop in H. destruct H.
  apply Nat.eqb_eq in H. subst prop.
  apply Nat.leb_le in H1.
  exact (PAloopCorrection (LengthNat proof) IsAxiom proof
                          eq_refl IsAxiomSat H0 0 H1 varValues).
Qed.

Lemma PAundefinedRelations : forall r args n:nat,
    LengthNat args <> 2
    -> IsProof IsWeakPeanoAxiom (Lrel r args) n = false.
Proof.
  intros. 
  destruct (IsProof IsWeakPeanoAxiom (Lrel r args) n) eqn:des. 2: reflexivity.
  exfalso.
  assert (IsProved IsWeakPeanoAxiom (Lrel r args)).
  { exists n. exact des. }
  pose proof (PAstandardModel_correction IsWeakPeanoAxiom _ PAaxiomsSatisfied
                                         H0 (fun _ => 0)).
  rewrite PAstandardModel_rel in H1.
  apply Nat.eqb_neq in H. rewrite H in H1.
  contradiction.
Qed. 

Lemma PAconsistent : IsConsistent IsWeakPeanoAxiom.
Proof.
  intro incons. unfold IsInconsistent in incons.
  apply PAstandardModel_correction in incons.
  2: exact PAaxiomsSatisfied.
  specialize (incons (fun _ => 0)).
  rewrite PAstandardModel_not in incons. contradict incons.
  rewrite PAstandardModel_eq. reflexivity.
Qed.
