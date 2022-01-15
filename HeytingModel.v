(** Prop-valued model of IsProof IsWeakHeytingAxiom, to show its consistency.

    This both shows that IsProof is correctly implemented, and pushes the
    incompleteness of Heyting Arithmetic one step further :
    HA neither proves nor refutes its Gödel proposition.

    A model of HA lifts proofs by HA into the meta-theory (Coq). If there was
    a proof HA |-- Leq PAzero (PAsucc PAzero), the model would lift it as
    a proof of 0 = 1 in Coq's type nat. Since Coq refutes the latter, Coq
    also refutes HA |-- Leq PAzero (PAsucc PAzero), which means Coq proves
    the consistency of HA. Of course, there still is the risk that Coq
    itself is inconsistent. *)

Require Import Arith.Wf_nat.
Require Import PeanoNat.
Require Import Arith.Compare_dec.
Require Import EnumSeqNat.
Require Import Formulas.
Require Import Substitutions.
Require Import IsFreeForSubst.
Require Import PeanoAxioms.
Require Import Proofs.
Require Import ProofTactics.


(** Interpretation of Peano terms as natural numbers. *)

Definition HAstandardModelTermRec (varValues : nat -> nat) (t : nat) (rec : nat -> nat) : nat :=
  match CoordNat t 0 with
  | LopHead => match LengthNat t with
              | 2 => 0 (* PAzero *)
              | 3 => S (rec 2)
              | 4 => match CoordNat t 1 with
                    | 0 => rec 2 + rec 3
                    | 1 => rec 2 * rec 3
                    | _ => 0
                    end
              | _ => 0
              end
  | LvarHead => varValues (CoordNat t 1)
  | _ => 0
  end.
Definition HAstandardModelTerm (varValues : nat -> nat) : nat -> nat
  := TreeFoldNat (HAstandardModelTermRec varValues) 0.

Lemma HAstandardModelTerm_step : forall varValues f,
    HAstandardModelTerm varValues f
    = TreeFoldNatRec (HAstandardModelTermRec varValues) 0 f
                     (fun k _ => HAstandardModelTerm varValues k).
Proof.
  intros.
  unfold HAstandardModelTerm, TreeFoldNat. rewrite Fix_eq.
  reflexivity.
  intros. unfold HAstandardModelTermRec, TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat x) 0). reflexivity.
  destruct (CoordNat x 0). reflexivity.
  repeat (destruct n; [reflexivity|]).
  destruct n.
  generalize (LengthNat x). intro n.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. rewrite H. reflexivity.
  destruct n. destruct (CoordNat x 1).
  rewrite H,H. reflexivity.
  destruct n. rewrite H,H. reflexivity.
  reflexivity. reflexivity.
  destruct n. reflexivity. reflexivity.
Qed.

(* TODO merge with VarIndep, by requiring equality on the free variables only. *)
Lemma HAstandardModelTerm_ext : forall t val1 val2,
    (forall n:nat, val1 n = val2 n)
    -> (HAstandardModelTerm val1 t = HAstandardModelTerm val2 t).
Proof.
  apply (Fix lt_wf (fun t => forall val1 val2,
    (forall n:nat, val1 n = val2 n)
    -> (HAstandardModelTerm val1 t = HAstandardModelTerm val2 t))).
  intro t. intros.
  rewrite HAstandardModelTerm_step, HAstandardModelTerm_step.
  unfold TreeFoldNatRec. destruct (le_lt_dec (LengthNat t) 0).
  reflexivity.
  unfold HAstandardModelTermRec.
  destruct (CoordNat t 0). reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n.
  destruct (LengthNat t) eqn:lenT. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n.
  rewrite <- lenT in l.
  rewrite (H _ (CoordLower _ _ (LengthPositive _ l)) val1 val2).
  reflexivity. exact H0.
  destruct n. 2: reflexivity.
  destruct (CoordNat t 1).
  rewrite <- lenT in l.
  rewrite (H _ (CoordLower _ _ (LengthPositive _ l)) val1 val2).
  rewrite (H _ (CoordLower _ _ (LengthPositive _ l)) val1 val2).
  reflexivity. exact H0. exact H0.
  destruct n. 2: reflexivity.
  rewrite <- lenT in l.
  rewrite (H _ (CoordLower _ _ (LengthPositive _ l)) val1 val2).
  rewrite (H _ (CoordLower _ _ (LengthPositive _ l)) val1 val2).
  reflexivity. exact H0. exact H0.
  destruct n.
  apply H0. reflexivity.
Qed.

Lemma HAstandardModelTerm_nil : forall varValues,
    HAstandardModelTerm varValues 0 = 0.
Proof.
  intros. rewrite HAstandardModelTerm_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat 0) 0). reflexivity.
  inversion l.
Qed.

Lemma HAstandardModelTerm_var : forall varValues v,
    HAstandardModelTerm varValues (Lvar v) = varValues v.
Proof.
  intros. rewrite HAstandardModelTerm_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lvar v)) 0).
  rewrite LengthLvar in l. inversion l.
  unfold HAstandardModelTermRec.
  unfold Lvar.
  do 5 rewrite CoordConsTailNat.
  do 2 rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma HAstandardModelTerm_zero : forall varValues,
    HAstandardModelTerm varValues PAzero = 0.
Proof.
  intros. rewrite HAstandardModelTerm_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat PAzero) 0). reflexivity.
  unfold HAstandardModelTermRec.
  unfold PAzero, Lconst, Lop. rewrite CoordConsHeadNat.
  rewrite LengthConsNat, LengthConsNat.
  reflexivity.
Qed.

Lemma HAstandardModelTerm_succ : forall varValues t,
    HAstandardModelTerm varValues (PAsucc t) = S (HAstandardModelTerm varValues t).
Proof.
  intros. rewrite HAstandardModelTerm_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (PAsucc t)) 0).
  unfold PAsucc in l.
  rewrite LengthLop1 in l. inversion l.
  unfold HAstandardModelTermRec.
  unfold PAsucc, Lop1.
  do 2 rewrite CoordNat_op.
  unfold Lop.
  do 2 rewrite CoordConsTailNat.
  do 3 rewrite CoordConsHeadNat.
  do 3 rewrite LengthConsNat. reflexivity.
Qed.

Lemma HAstandardModelTerm_PAnat : forall varValues n,
    HAstandardModelTerm varValues (PAnat n) = n.
Proof.
  induction n.
  - apply HAstandardModelTerm_zero.
  - simpl. rewrite HAstandardModelTerm_succ, IHn. reflexivity.
Qed.

Lemma HAstandardModelTerm_plus : forall varValues t u,
    HAstandardModelTerm varValues (PAplus t u)
    = HAstandardModelTerm varValues t + HAstandardModelTerm varValues u.
Proof.
  intros.
  rewrite HAstandardModelTerm_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (PAplus t u)) 0).
  exfalso. unfold PAplus in l.
  rewrite LengthLop2 in l. inversion l.
  unfold HAstandardModelTermRec.
  unfold PAplus, Lop2.
  do 2 rewrite CoordNat_op.
  unfold Lop.
  do 2 rewrite CoordConsTailNat.
  do 4 rewrite CoordConsHeadNat.
  do 4 rewrite LengthConsNat. reflexivity.
Qed.

Lemma HAstandardModelTerm_mult : forall varValues t u,
    HAstandardModelTerm varValues (PAmult t u)
    = HAstandardModelTerm varValues t * HAstandardModelTerm varValues u.
Proof.
  intros.
  rewrite HAstandardModelTerm_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (PAmult t u)) 0).
  exfalso. unfold PAmult in l.
  rewrite LengthLop2 in l. inversion l.
  unfold HAstandardModelTermRec.
  unfold PAmult, Lop2.
  do 2 rewrite CoordNat_op.
  unfold Lop.
  do 2 rewrite CoordConsTailNat.
  do 4 rewrite CoordConsHeadNat.
  do 4 rewrite LengthConsNat. reflexivity.
Qed.

Lemma HAstandardModelTerm_length1 : forall varValues t,
    CoordNat t 0 = LopHead
    -> LengthNat t = 1
    -> HAstandardModelTerm varValues t = 0.
Proof.
  intros. rewrite HAstandardModelTerm_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat t) 0).
  reflexivity.
  unfold HAstandardModelTermRec.
  rewrite H, H0. reflexivity.
Qed.

Lemma HAstandardModelTerm_length2 : forall varValues t,
    CoordNat t 0 = LopHead
    -> LengthNat t = 2
    -> HAstandardModelTerm varValues t = 0.
Proof.
  intros. rewrite HAstandardModelTerm_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat t) 0).
  reflexivity.
  unfold HAstandardModelTermRec.
  rewrite H, H0. reflexivity.
Qed.

Lemma HAstandardModelTerm_length3 : forall varValues t,
    CoordNat t 0 = LopHead
    -> LengthNat t = 3
    -> HAstandardModelTerm varValues t
      = S (HAstandardModelTerm varValues (CoordNat t 2)).
Proof.
  intros. rewrite HAstandardModelTerm_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat t) 0).
  exfalso. inversion l. rewrite H2 in H0. discriminate.
  unfold HAstandardModelTermRec.
  rewrite H, H0. reflexivity.
Qed.

Lemma HAstandardModelTerm_length4 : forall varValues t,
    CoordNat t 0 = LopHead
    -> LengthNat t = 4
    -> HAstandardModelTerm varValues t
      = match CoordNat t 1 with
        | 0 =>
          HAstandardModelTerm varValues (CoordNat t 2) +
          HAstandardModelTerm varValues (CoordNat t 3)
        | 1 =>
          HAstandardModelTerm varValues (CoordNat t 2) *
          HAstandardModelTerm varValues (CoordNat t 3)
        | S (S _) => 0
        end.
Proof.
  intros. rewrite HAstandardModelTerm_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat t) 0).
  exfalso. inversion l. rewrite H2 in H0. discriminate.
  unfold HAstandardModelTermRec.
  rewrite H, H0. reflexivity.
Qed.

Lemma HAstandardModelTerm_length5 : forall varValues t,
    CoordNat t 0 = LopHead
    -> 5 <= LengthNat t
    -> HAstandardModelTerm varValues t = 0.
Proof.
  intros. rewrite HAstandardModelTerm_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat t) 0).
  exfalso. inversion l. rewrite H2 in H0. inversion H0.
  unfold HAstandardModelTermRec.
  rewrite H.
  destruct (LengthNat t). reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. do 3 apply le_S_n in H0. inversion H0.
  destruct n. do 4 apply le_S_n in H0. inversion H0.
  reflexivity.
Qed.


(** Interpretation of Peano propositions as Prop *)

Definition setValue (i newVal : nat) (values : nat -> nat) (n : nat) : nat :=
  if Nat.eqb n i then newVal else values n.

Lemma SetSetValueIdem : forall (varValues : nat -> nat) v y z n,
    setValue v y (setValue v z varValues) n
    = setValue v y varValues n.
Proof.
  intros.
  unfold setValue.
  destruct (n =? v); reflexivity.
Qed.

Lemma SetSetValueCommute : forall (varValues : nat -> nat) u v y z,
    u <> v
    -> forall n, setValue u y (setValue v z varValues) n
      = setValue v z (setValue u y varValues) n.
Proof.
  intros. unfold setValue.
  destruct (n =? u) eqn:des1, (n =? v) eqn:des2.
  2: reflexivity. 2: reflexivity. 2: reflexivity.
  apply Nat.eqb_eq in des1.
  apply Nat.eqb_eq in des2. subst n. contradiction.
Qed.

(* We use the Gödel-Gentzen double-negation translation, to model classical logic.
   The atomic propositions x = y and x <= y do not need double negations, because
   they are recursive.
   We interpret all undefined relations by False, so that we will establish
   that nothing can be proved about them. *)
Definition HAstandardModelRec (f : nat) (rec : nat -> (nat -> nat) -> Prop) (varValues : nat -> nat)
  : Prop :=
  match CoordNat f 0 with
  | LnotHead => not (rec 1 varValues)
  | LimpliesHead => rec 1 varValues -> rec 2 varValues
  | LorHead => rec 1 varValues \/ rec 2 varValues
  | LandHead => rec 1 varValues /\ rec 2 varValues
  | LforallHead => forall n:nat, rec 2 (setValue (CoordNat f 1) n varValues)
  | LexistsHead => exists n:nat, rec 2 (setValue (CoordNat f 1) n varValues)
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

Definition HAstandardModel : nat -> (nat -> nat) -> Prop
  := TreeFoldNat HAstandardModelRec (fun _ => False).

(* Satisfaction of an arithmetical formula in the standard model.
   For a closed proposition f, varValues does not matter and be replaced by
   fun _ => 0. *)
Definition HAstandardModelSat (f : nat) : Prop :=
  forall varValues, HAstandardModel f varValues.

Lemma HAstandardModel_step : forall f,
    HAstandardModel f
    = TreeFoldNatRec HAstandardModelRec (fun _ => False) f
                     (fun k _ => HAstandardModel k).
Proof.
  intros.
  unfold HAstandardModel, TreeFoldNat. rewrite Fix_eq.
  reflexivity.
  intros. unfold HAstandardModelRec, TreeFoldNatRec.
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

Lemma FactorForall : forall P Q : nat -> Prop,
    (forall n, P n <-> Q n) -> ((forall n, P n) <-> (forall n, Q n)).
Proof.
  split.
  - intros. rewrite <- H. apply H0.
  - intros. rewrite H. apply H0.
Qed.

Lemma FactorExists : forall P Q : nat -> Prop,
    (forall n, P n <-> Q n) -> ((exists n, P n) <-> (exists n, Q n)).
Proof.
  split.
  - intros. destruct H0. exists x. rewrite <- H. apply H0.
  - intros. destruct H0. exists x. rewrite H. apply H0.
Qed.

Lemma HAstandardModel_ext : forall f val1 val2,
    (forall n:nat, val1 n = val2 n)
    -> (HAstandardModel f val1 <-> HAstandardModel f val2).
Proof.
  apply (Fix lt_wf (fun f => forall val1 val2,
    (forall n:nat, val1 n = val2 n)
    -> (HAstandardModel f val1 <-> HAstandardModel f val2))).
  intro f. intros.
  rewrite HAstandardModel_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat f) 0). reflexivity.
  unfold HAstandardModelRec.
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
  apply FactorExists. intro n.
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

Lemma HAstandardModel_not : forall varValues f,
    HAstandardModel (Lnot f) varValues
    = ~(HAstandardModel f varValues).
Proof.
  intros. rewrite HAstandardModel_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lnot f)) 0).
  exfalso. rewrite LengthLnot in l. inversion l.
  unfold HAstandardModelRec, Lnot; rewrite CoordConsHeadNat.
  rewrite CoordConsTailNat.
  rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma HAstandardModel_or : forall varValues f g,
    HAstandardModel (Lor f g) varValues
    = (HAstandardModel f varValues \/ HAstandardModel g varValues).
Proof.
  intros. rewrite HAstandardModel_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lor f g)) 0).
  exfalso. rewrite LengthLor in l. inversion l.
  unfold HAstandardModelRec, Lor; rewrite CoordConsHeadNat.
  do 3 rewrite CoordConsTailNat.
  do 2 rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma HAstandardModel_and : forall varValues f g,
    HAstandardModel (Land f g) varValues
    = (HAstandardModel f varValues /\ HAstandardModel g varValues).
Proof.
  intros. rewrite HAstandardModel_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Land f g)) 0).
  exfalso. rewrite LengthLand in l. inversion l.
  unfold HAstandardModelRec, Land; rewrite CoordConsHeadNat.
  do 3 rewrite CoordConsTailNat.
  do 2 rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma HAstandardModel_implies : forall varValues f g,
    HAstandardModel (Limplies f g) varValues
    = (HAstandardModel f varValues -> HAstandardModel g varValues).
Proof.
  intros. rewrite HAstandardModel_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Limplies f g)) 0).
  exfalso. rewrite LengthLimplies in l. inversion l.
  unfold HAstandardModelRec, Limplies; rewrite CoordConsHeadNat.
  do 3 rewrite CoordConsTailNat.
  do 2 rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma HAstandardModel_equiv : forall varValues f g,
    HAstandardModel (Lequiv f g) varValues
    <-> (HAstandardModel f varValues <-> HAstandardModel g varValues).
Proof.
  intros. unfold Lequiv.
  rewrite HAstandardModel_and, HAstandardModel_implies, HAstandardModel_implies.
  reflexivity.
Qed.

Lemma HAstandardModel_eq : forall varValues a b,
    HAstandardModel (Leq a b) varValues
    = (HAstandardModelTerm varValues a = HAstandardModelTerm varValues b).
Proof.
  intros. rewrite HAstandardModel_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Leq a b)) 0).
  unfold Leq in l. rewrite LengthLrel2 in l. inversion l.
  unfold HAstandardModelRec, Leq, Lrel2, Lrel; rewrite CoordConsHeadNat.
  do 4 rewrite LengthConsNat. simpl.
  do 6 rewrite CoordConsTailNat.
  do 3 rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma HAstandardModel_le : forall varValues a b,
    HAstandardModel (PAle a b) varValues
    = (HAstandardModelTerm varValues a <= HAstandardModelTerm varValues b).
Proof.
  intros. rewrite HAstandardModel_step.
  unfold TreeFoldNatRec, PAle.
  destruct (le_lt_dec (LengthNat (Lrel2 1 a b)) 0).
  rewrite LengthLrel2 in l. inversion l.
  unfold HAstandardModelRec, PAle, Lrel2, Lrel; rewrite CoordConsHeadNat.
  do 4 rewrite LengthConsNat. simpl.
  do 6 rewrite CoordConsTailNat.
  do 3 rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma HAstandardModel_rel : forall varValues r args,
    HAstandardModel (Lrel r args) varValues
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
  intros. rewrite HAstandardModel_step.
  unfold TreeFoldNatRec. rewrite LengthLrel. simpl.
  unfold HAstandardModelRec.
  unfold Lrel. rewrite CoordConsHeadNat.
  rewrite LengthConsNat, LengthConsNat. simpl.
  do 5 rewrite CoordConsTailNat.
  rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma HAstandardModel_forallHead : forall varValues f,
    CoordNat f 0 = LforallHead
    -> HAstandardModel f varValues
      = (forall n:nat, HAstandardModel (CoordNat f 2) (setValue (CoordNat f 1) n varValues)).
Proof.
  intros. rewrite HAstandardModel_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat f) 0).
  exfalso. rewrite CoordNatAboveLength in H.
  discriminate. exact l.
  unfold HAstandardModelRec; rewrite H.
  reflexivity.
Qed.

Lemma HAstandardModel_forall : forall varValues v f,
    HAstandardModel (Lforall v f) varValues
    = (forall n:nat, HAstandardModel f (setValue v n varValues)).
Proof.
  intros.
  rewrite HAstandardModel_forallHead.
  rewrite CoordNat_forall_1, CoordNat_forall_2.
  reflexivity.
  unfold Lforall.
  rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma HAstandardModel_exists : forall varValues v f,
    HAstandardModel (Lexists v f) varValues
    = exists n:nat, HAstandardModel f (setValue v n varValues).
Proof.
  intros. rewrite HAstandardModel_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lexists v f)) 0).
  exfalso. rewrite LengthLexists in l. inversion l.
  unfold HAstandardModelRec, Lexists; rewrite CoordConsHeadNat.
  do 3 rewrite CoordConsTailNat.
  do 2 rewrite CoordConsHeadNat.
  reflexivity.
Qed.


(** Evaluations of substitutions by HAstandardModel *)

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
  apply Bool.negb_false_iff, Nat.eqb_eq.
  apply Bool.negb_false_iff, Nat.eqb_eq in H.
  rewrite SubstTerm_opHead in H. 2: exact headT.
  apply (f_equal (fun a => CoordNat a 2)) in H.
  rewrite CoordNat_op, CoordMapNat, CoordRangeNat in H. exact H.
  rewrite lenT. apply Nat.le_refl.
  rewrite LengthRangeNat. rewrite lenT. apply Nat.le_refl.
  destruct n.
  (* Addition and multiplication *)
  2: reflexivity.
  rewrite IHt, IHt. reflexivity.
  rewrite <- lenT in l.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  apply Bool.negb_false_iff, Nat.eqb_eq in H.
  rewrite SubstTerm_opHead in H. 2: exact headT.
  apply (f_equal (fun a => CoordNat a 3)) in H.
  rewrite CoordNat_op, CoordMapNat, CoordRangeNat in H. exact H.
  rewrite lenT. apply Nat.le_refl.
  rewrite LengthRangeNat. rewrite lenT. apply Nat.le_refl.
  apply CoordLower, LengthPositive. rewrite lenT. auto.
  apply Bool.negb_false_iff, Nat.eqb_eq.
  apply Bool.negb_false_iff, Nat.eqb_eq in H.
  rewrite SubstTerm_opHead in H. 2: exact headT.
  apply (f_equal (fun a => CoordNat a 2)) in H.
  rewrite CoordNat_op, CoordMapNat, CoordRangeNat in H. exact H.
  rewrite lenT. apply le_n_S, le_0_n.
  rewrite LengthRangeNat. rewrite lenT. apply le_n_S, le_0_n.
  (* Lvar *)
  destruct n. 2: reflexivity.
  unfold setValue.
  destruct (CoordNat t 1 =? v).
  rewrite <- H0 in l. inversion l. reflexivity.
Qed.

Lemma VarIndep : forall f v (varValues : nat -> nat) y,
    VarOccursFreeInFormula v f = false
    -> (HAstandardModel f (setValue v y varValues)
       <-> HAstandardModel f varValues).
Proof.
  apply (Fix lt_wf (fun f => forall (v : nat) (varValues : nat -> nat) (y : nat),
  VarOccursFreeInFormula v f = false ->
  HAstandardModel f (setValue v y varValues) <-> HAstandardModel f varValues)).
  intros f IHf v varValues y nooccur.
  apply Bool.negb_false_iff, Nat.eqb_eq in nooccur.
  rewrite HAstandardModel_step. unfold TreeFoldNatRec.
  rewrite Subst_step in nooccur. unfold TreeFoldNatRec in nooccur.
  destruct (le_lt_dec (LengthNat f) 0).
  reflexivity.
  unfold SubstRec in nooccur.
  unfold HAstandardModelRec.
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
  rewrite (HAstandardModel_ext
             _ _ _ (SetSetValueIdem varValues v _ _)).
  reflexivity.
  apply Nat.eqb_neq in des.
  rewrite (HAstandardModel_ext
             _ _ _ (SetSetValueCommute varValues _ _ _ _ des)).
  rewrite IHf. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply Bool.negb_false_iff, Nat.eqb_eq.
  rewrite <- nooccur at 2.
  rewrite CoordNat_forall_2. reflexivity.
  destruct n.
  (* Lexists *)
  apply FactorExists; intro n.
  destruct (CoordNat f 1 =? v) eqn:des.
  apply Nat.eqb_eq in des.
  rewrite des.
  rewrite (HAstandardModel_ext
             _ _ _ (SetSetValueIdem varValues v _ _)).
  reflexivity.
  apply Nat.eqb_neq in des.
  rewrite (HAstandardModel_ext
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
  rewrite VarIndepTerm, VarIndepTerm. reflexivity.
  apply Bool.negb_false_iff, Nat.eqb_eq.
  apply (f_equal (fun n => CoordNat n 3)) in nooccur.
  rewrite CoordNat_rel, CoordMapNat, CoordTailNat, CoordTailNat in nooccur.
  exact nooccur. rewrite LengthTailNat, LengthTailNat, lenF. auto.
  apply Bool.negb_false_iff, Nat.eqb_eq.
  apply (f_equal (fun n => CoordNat n 2)) in nooccur.
  rewrite CoordNat_rel, CoordMapNat, CoordTailNat, CoordTailNat in nooccur.
  exact nooccur. rewrite LengthTailNat, LengthTailNat, lenF.
  apply le_n_S, le_0_n.
Qed.

Lemma HAstandardModel_SubstTerm : forall t u v varValues,
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
      destruct n. simpl. rewrite MapNilNat.
      apply HAstandardModelTerm_length2.
      unfold Lop. rewrite CoordConsHeadNat. reflexivity.
      rewrite LengthLop. reflexivity.
      destruct n.
      (* case PAzero *)
      simpl. rewrite MapNilNat.
      apply HAstandardModelTerm_length2.
      unfold Lop. rewrite CoordConsHeadNat. reflexivity.
      rewrite LengthLop. reflexivity.
      destruct n.
      (* case PAsucc *)
      rewrite <- (IHt (CoordNat t 2) (CoordLower t 2 tpos)).
      simpl. rewrite MapConsNat, MapNilNat.
      rewrite HAstandardModelTerm_length3.
      3: rewrite LengthLop, LengthConsNat; reflexivity.
      2: unfold Lop; rewrite CoordConsHeadNat; reflexivity.
      rewrite CoordNat_op, CoordConsHeadNat. reflexivity.
      destruct n.
      (* case PAplus or PAmult *)
      simpl.
      rewrite MapConsNat, MapConsNat, MapNilNat.
      rewrite HAstandardModelTerm_length4.
      rewrite CoordNat_op, CoordNat_op.
      unfold Lop at 1. rewrite CoordConsTailNat, CoordConsHeadNat.
      rewrite CoordConsHeadNat.
      rewrite CoordConsTailNat, CoordConsHeadNat.
      rewrite IHt, IHt. reflexivity.
      exact (CoordLower t 3 tpos).
      exact (CoordLower t 2 tpos).
      unfold Lop. rewrite CoordConsHeadNat. reflexivity.
      rewrite LengthLop, LengthConsNat, LengthConsNat. reflexivity.
      (* case length too high *)
      apply HAstandardModelTerm_length5.
      rewrite <- headT.
      unfold Lop. rewrite CoordConsHeadNat.
      symmetry. exact headT.
      rewrite LengthLop, LengthMapNat, LengthRangeNat.
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

Lemma HAstandardModel_Subst : forall prop u v (varValues : nat -> nat),
    IsFreeForSubst u v prop = true
    -> (HAstandardModel (Subst u v prop) varValues
       <-> HAstandardModel prop (setValue v (HAstandardModelTerm varValues u) varValues)).
Proof.
  apply (Fix lt_wf (fun prop => forall u v (varValues : nat -> nat),
    IsFreeForSubst u v prop = true
    -> (HAstandardModel (Subst u v prop) varValues
       <-> HAstandardModel prop (setValue v (HAstandardModelTerm varValues u) varValues)))).
  intros prop IHprop u v varValues free.
  rewrite Subst_step.
  unfold TreeFoldNatRec.
  rewrite (HAstandardModel_step prop).
  unfold TreeFoldNatRec.
  rewrite IsFreeForSubst_step in free.
  unfold TreeFoldNatRec in free.
  destruct (le_lt_dec (LengthNat prop) 0). discriminate.
  unfold IsFreeForSubstRec in free.
  unfold HAstandardModelRec.
  unfold SubstRec.
  destruct (CoordNat prop 0) eqn:headProp. discriminate.
  destruct n.
  (* Lnot *)
  rewrite HAstandardModel_not, IHprop. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  exact free.
  destruct n.
  (* Limplies *)
  apply andb_prop in free.
  rewrite HAstandardModel_implies.
  rewrite IHprop, IHprop. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply free.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply free.
  destruct n.
  (* Lor *)
  apply andb_prop in free.
  rewrite HAstandardModel_or.
  rewrite IHprop, IHprop. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply free.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply free.
  destruct n.
  (* Land *)
  apply andb_prop in free.
  rewrite HAstandardModel_and.
  rewrite IHprop, IHprop. reflexivity.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply free.
  exact (CoordLower _ _ (LengthPositive _ l)).
  apply free.
  destruct n.
  (* Lforall : 3 cases, same var, no subst and recurse.
     The first 2 cases could be merged. *)
  apply Bool.orb_prop in free.
  rewrite HAstandardModel_forall.
  apply FactorForall. intro n.
  destruct (CoordNat prop 1 =? v) eqn:eqvar.
  apply Nat.eqb_eq in eqvar. subst v.
  symmetry.
  rewrite (HAstandardModel_ext _ _ (setValue (CoordNat prop 1) n varValues)).
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
  rewrite (HAstandardModel_ext _ _ (setValue v (HAstandardModelTerm varValues u) (setValue (CoordNat prop 1) n varValues))).
  2: apply SetSetValueCommute.
  rewrite VarIndep.
  rewrite Subst_nosubst. reflexivity.
  exact nosubst2. exact nosubst2.
  intro abs. rewrite abs, Nat.eqb_refl in eqvar. discriminate.
  apply andb_prop in free.
  rewrite IHprop.
  rewrite (HAstandardModel_ext _ _ (setValue (CoordNat prop 1) n
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
  rewrite HAstandardModel_exists.
  apply FactorExists. intro n.
  destruct (CoordNat prop 1 =? v) eqn:eqvar.
  apply Nat.eqb_eq in eqvar. subst v.
  symmetry.
  rewrite (HAstandardModel_ext _ _ (setValue (CoordNat prop 1) n varValues)).
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
  rewrite (HAstandardModel_ext _ _ (setValue v (HAstandardModelTerm varValues u) (setValue (CoordNat prop 1) n varValues))).
  2: apply SetSetValueCommute.
  rewrite VarIndep. rewrite Subst_nosubst. reflexivity.
  exact nosubst2. exact nosubst2.
  intro abs. rewrite abs, Nat.eqb_refl in eqvar. discriminate.
  apply andb_prop in free.
  rewrite IHprop.
  rewrite (HAstandardModel_ext _ _ (setValue (CoordNat prop 1) n
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
  rewrite HAstandardModel_rel, LengthMapNat.
  rewrite LengthTailNat, LengthTailNat.
  destruct (LengthNat prop) eqn:lenProp. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. 2: reflexivity. simpl (pred (pred 4)).
  rewrite Nat.eqb_refl, Nat.eqb_refl.
  rewrite CoordMapNat, CoordMapNat.
  rewrite HAstandardModel_SubstTerm, HAstandardModel_SubstTerm.
  rewrite CoordTailNat, CoordTailNat.
  rewrite CoordTailNat, CoordTailNat.
  reflexivity.
  rewrite LengthTailNat, LengthTailNat, lenProp.
  apply Nat.le_refl. auto.
  rewrite LengthTailNat, LengthTailNat, lenProp. simpl. auto.
Qed.


(** Satisfaction of propositional logic in the standard model. *)

(* (X1 -> (X2 -> X3)) -> ((X1 -> X2) -> (X1 -> X3)) *)
Lemma Ax2Satisfied : forall (prop : nat),
  IsPropAx2 prop = true -> HAstandardModelSat prop.
Proof.
  intros prop H varValues.
  do 10 (apply andb_prop in H; destruct H).
  apply Nat.eqb_eq in H9.
  rewrite H9, HAstandardModel_implies. intro X1X2X3.
  apply Nat.eqb_eq in H6.
  rewrite H6, HAstandardModel_implies. intro X1X2.
  apply Nat.eqb_eq in H4.
  rewrite H4, HAstandardModel_implies. intro X1.
  apply Nat.eqb_eq in H5.
  rewrite H5, HAstandardModel_implies in X1X2.
  apply Nat.eqb_eq in H2.
  rewrite <- H2 in X1.
  apply Nat.eqb_eq in H3.
  rewrite <- H3 in X1X2.
  specialize (X1X2 X1).
  apply Nat.eqb_eq in H8.
  rewrite H8, HAstandardModel_implies in X1X2X3.
  specialize (X1X2X3 X1).
  apply Nat.eqb_eq in H7.
  rewrite H7, HAstandardModel_implies in X1X2X3.
  apply Nat.eqb_eq in H1.
  rewrite H1 in X1X2X3.
  specialize (X1X2X3 X1X2).
  apply Nat.eqb_eq in H0.
  rewrite <- H0. exact X1X2X3.
Qed.

(* X1 -> (~X1 -> X2) *)
Lemma Ax5Satisfied : forall (prop : nat),
  IsPropAx5 prop = true -> HAstandardModelSat prop.
Proof.
  intros prop H varValues.
  do 4 (apply andb_prop in H; destruct H).
  apply Nat.eqb_eq in H3.
  apply Nat.eqb_eq in H2.
  apply Nat.eqb_eq in H0.
  apply Nat.eqb_eq in H1.
  rewrite H3, HAstandardModel_implies.
  intro X1.
  rewrite H2, HAstandardModel_implies.
  intro notX1.
  rewrite H1, HAstandardModel_not, <- H0 in notX1.
  contradiction.
Qed.

(* X1 -> (X2 -> (X1 /\ X2)) *)
Lemma Ax6Satisfied : forall (prop : nat),
  IsPropAx6 prop = true -> HAstandardModelSat prop.
Proof.
  intros prop H varValues.
  do 5 (apply andb_prop in H; destruct H).
  apply Nat.eqb_eq in H0.
  apply Nat.eqb_eq in H1.
  apply Nat.eqb_eq in H2.
  apply Nat.eqb_eq in H3.
  apply Nat.eqb_eq in H4.
  rewrite H4, HAstandardModel_implies.
  intro X1.
  rewrite H3, HAstandardModel_implies.
  intro X2.
  rewrite H2, HAstandardModel_and.
  split.
  rewrite <- H1. exact X1.
  rewrite <- H0. exact X2.
Qed.

(* (X1 -> X3) -> ((X2 -> X3) -> ((X1 \/ X2) -> X3)) *)
Lemma Ax11Satisfied : forall (prop : nat),
  IsPropAx11 prop = true -> HAstandardModelSat prop.
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
  rewrite H9, HAstandardModel_implies. intro X1implX3.
  rewrite H7, HAstandardModel_implies. intro X2implX3.
  rewrite H5, HAstandardModel_implies. intro X1orX2.
  rewrite H4, HAstandardModel_or in X1orX2.
  rewrite <- H0.
  destruct X1orX2 as [X1 | X2].
  rewrite H8, HAstandardModel_implies in X1implX3.
  apply X1implX3. rewrite <- H3 in X1. exact X1.
  rewrite H6, HAstandardModel_implies, <- H1 in X2implX3.
  apply X2implX3. rewrite <- H2 in X2. exact X2.
Qed.

Lemma PropositionalAxiomsSatisfied : forall prop,
    IsPropositionalAxiom prop = true
    -> HAstandardModelSat prop.
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
    rewrite H2, HAstandardModel_implies. intro X1.
    apply Nat.eqb_eq in H1.
    rewrite H1, HAstandardModel_implies.
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
    rewrite H8, HAstandardModel_implies; intro X1implX2.
    rewrite H6, HAstandardModel_implies; intro X1implnotX2.
    rewrite H4, HAstandardModel_not; intro X1.
    rewrite H5, HAstandardModel_implies in X1implnotX2.
    rewrite H7, HAstandardModel_implies in X1implX2.
    rewrite <- H1 in X1. specialize (X1implX2 X1).
    rewrite <- H2 in X1implnotX2. specialize (X1implnotX2 X1).
    rewrite H3, HAstandardModel_not, <- H0 in X1implnotX2.
    contradiction.
  - apply Ax5Satisfied, H.
  - apply Ax6Satisfied, H.
  - (* (X1 /\ X2) -> X1 *)
    do 3 (apply andb_prop in H; destruct H).
    apply Nat.eqb_eq in H2.
    rewrite H2, HAstandardModel_implies.
    intro X1andX2.
    apply Nat.eqb_eq in H1.
    rewrite H1, HAstandardModel_and in X1andX2.
    apply Nat.eqb_eq in H0.
    rewrite <- H0. apply X1andX2.
  - (* (X1 /\ X2) -> X2 *)
    do 3 (apply andb_prop in H; destruct H).
    apply Nat.eqb_eq in H2.
    rewrite H2, HAstandardModel_implies.
    intro X1andX2.
    apply Nat.eqb_eq in H1.
    rewrite H1, HAstandardModel_and in X1andX2.
    apply Nat.eqb_eq in H0.
    rewrite <- H0. apply X1andX2.
  - (* X1 -> (X1 \/ X2) *)
    do 3 (apply andb_prop in H; destruct H).
    apply Nat.eqb_eq in H2.
    rewrite H2, HAstandardModel_implies.
    intro X1.
    apply Nat.eqb_eq in H1.
    rewrite H1, HAstandardModel_or.
    left.
    apply Nat.eqb_eq in H0.
    rewrite <- H0. exact X1.
  - (* X2 -> (X1 \/ X2) *)
    do 3 (apply andb_prop in H; destruct H).
    apply Nat.eqb_eq in H2.
    rewrite H2, HAstandardModel_implies.
    intro X2.
    apply Nat.eqb_eq in H1.
    rewrite H1, HAstandardModel_or.
    right.
    apply Nat.eqb_eq in H0.
    rewrite <- H0. exact X2.
  - apply Ax11Satisfied, H.
Qed.


(** Satisfaction of the Peano axioms in the standard model. *)

Lemma HAaxiomsSatisfied : forall prop,
    IsWeakHeytingAxiom prop = true -> HAstandardModelSat prop.
Proof.
  intros prop H varValues.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  - apply Nat.eqb_eq in H. subst prop.
    unfold PAax1. rewrite HAstandardModel_forall.
    intro n. rewrite HAstandardModel_not, HAstandardModel_eq.
    rewrite HAstandardModelTerm_succ.
    rewrite HAstandardModelTerm_zero.
    discriminate.
  - apply Nat.eqb_eq in H. subst prop.
    unfold PAax2. rewrite HAstandardModel_forall.
    intro n. rewrite HAstandardModel_or, HAstandardModel_eq.
    rewrite HAstandardModel_exists.
    rewrite HAstandardModelTerm_var.
    unfold setValue at 1; simpl.
    rewrite HAstandardModelTerm_zero.
    destruct n. left. reflexivity.
    right. exists n.
    rewrite HAstandardModel_eq, HAstandardModelTerm_var.
    rewrite HAstandardModelTerm_succ, HAstandardModelTerm_var.
    reflexivity.
  - apply Nat.eqb_eq in H. subst prop.
    unfold PAax3. rewrite HAstandardModel_forall.
    intro n. rewrite HAstandardModel_forall. intro p.
    rewrite HAstandardModel_implies. intro succEq.
    rewrite HAstandardModel_eq in succEq.
    rewrite HAstandardModel_eq.
    rewrite HAstandardModelTerm_succ, HAstandardModelTerm_succ in succEq.
    assert (forall x y : nat, S x = S y -> x = y) as H.
    intros. inversion H. reflexivity.
    apply H, succEq.
  - apply Nat.eqb_eq in H. subst prop.
    unfold PAax4. rewrite HAstandardModel_forall.
    intro n. rewrite HAstandardModel_eq.
    rewrite HAstandardModelTerm_plus.
    rewrite HAstandardModelTerm_zero.
    rewrite Nat.add_0_r. reflexivity.
  - apply Nat.eqb_eq in H. subst prop.
    unfold PAax5.
    rewrite HAstandardModel_forall. intro n.
    rewrite HAstandardModel_forall. intro p.
    rewrite HAstandardModel_eq.
    rewrite HAstandardModelTerm_plus.
    rewrite HAstandardModelTerm_succ.
    rewrite HAstandardModelTerm_succ.
    rewrite HAstandardModelTerm_plus.
    rewrite Nat.add_succ_r. reflexivity.
  - apply Nat.eqb_eq in H. subst prop.
    unfold PAax6.
    rewrite HAstandardModel_forall. intro n.
    rewrite HAstandardModel_eq.
    rewrite HAstandardModelTerm_mult.
    rewrite HAstandardModelTerm_zero.
    apply Nat.mul_0_r.
  - apply Nat.eqb_eq in H. subst prop.
    unfold PAax7.
    rewrite HAstandardModel_forall. intro n.
    rewrite HAstandardModel_forall. intro p.
    rewrite HAstandardModel_eq.
    rewrite HAstandardModelTerm_mult.
    rewrite HAstandardModelTerm_plus.
    rewrite HAstandardModelTerm_mult.
    rewrite HAstandardModelTerm_succ.
    apply Nat.mul_succ_r.
  - apply Nat.eqb_eq in H. subst prop.
    unfold PAorder.
    rewrite HAstandardModel_forall. intro n.
    rewrite HAstandardModel_forall. intro p.
    rewrite HAstandardModel_equiv, HAstandardModel_le.
    rewrite HAstandardModel_exists.
    rewrite HAstandardModelTerm_var, HAstandardModelTerm_var.
    change (setValue 1 p (setValue 0 n varValues) 0 <= setValue 1 p (setValue 0 n varValues) 1)
      with (n <= p).
    split.
    + intro le. apply Nat.le_exists_sub in le.
      destruct le, H. exists x. subst p.
      rewrite HAstandardModel_eq.
      rewrite HAstandardModelTerm_var.
      rewrite HAstandardModelTerm_plus.
      rewrite HAstandardModelTerm_var, HAstandardModelTerm_var.
      reflexivity.
    + intro H.
      destruct (le_lt_dec n p). exact l.
      exfalso. contradict H; intros [k H].
      rewrite HAstandardModel_eq in H.
      rewrite HAstandardModelTerm_plus, HAstandardModelTerm_var in H.
      rewrite HAstandardModelTerm_var, HAstandardModelTerm_var in H.
      unfold setValue in H; simpl in H. subst p.
      rewrite <- (Nat.add_0_l n) in l at 2.
      apply (Nat.add_lt_mono_r k 0 n) in l. inversion l.
Qed.


Lemma IndependenceOfPremiseSatisfied : forall prop,
    IsIndependenceOfPremise prop = true
    -> HAstandardModelSat prop.
Proof.
  intros prop H varValues.
  do 9 (apply andb_prop in H; destruct H).
  apply Bool.negb_true_iff in H0.
  apply Nat.eqb_eq in H8.
  remember (CoordNat prop 1) as ForallXfg.
  remember (CoordNat prop 2) as fForallXg.
  rewrite H8, HAstandardModel_implies.
  rewrite H8, IsLproposition_implies in H.
  clear H8 HeqfForallXg HeqForallXfg prop.
  intro ForallXfg_proof.
  apply Nat.eqb_eq in H5.
  rewrite H5, HAstandardModel_implies.
  rewrite H5, IsLproposition_implies in H.
  remember (CoordNat fForallXg 1) as f.
  remember (CoordNat fForallXg 2) as ForallXg.
  clear H5 HeqForallXg Heqf fForallXg.
  apply Nat.eqb_eq in H1.
  intro f_proof.
  apply Nat.eqb_eq in H4.
  rewrite H4, HAstandardModel_forall.
  intro valX.
  apply Nat.eqb_eq in H7.
  rewrite H7, HAstandardModel_forall in ForallXfg_proof.
  specialize (ForallXfg_proof valX).
  apply Nat.eqb_eq in H6.
  apply Nat.eqb_eq in H3.
  apply Nat.eqb_eq in H2.
  rewrite H6, HAstandardModel_implies, H2, H1 in ForallXfg_proof.
  apply ForallXfg_proof.
  rewrite VarIndep, H3. exact f_proof.
  rewrite H3. apply andb_prop in H. destruct H.
  rewrite <- H1. exact H0.
Qed.

Lemma SpecializationSatisfied : forall prop,
    IsSpecialization prop = true
    -> HAstandardModelSat prop.
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
    rewrite HAstandardModel_implies.
    intro forall_proof.
    rewrite HAstandardModel_forall in forall_proof.
    rewrite HAstandardModel_Subst.
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
    rewrite HAstandardModel_implies.
    intro exist_proof.
    rewrite HAstandardModel_exists.
    rewrite HAstandardModel_Subst in exist_proof.
    exists (HAstandardModelTerm varValues
                        (FindSubstTerm (CoordNat (CoordNat prop 2) 1)
                           (CoordNat (CoordNat prop 2) 2)
                           (CoordNat prop 1))).
    exact exist_proof. exact H.
Qed.

Lemma ExistsElimSatisfied : forall prop,
    IsExistsElim prop = true
    -> HAstandardModelSat prop.
Proof.
  intros prop H varValues.
  do 9 (apply andb_prop in H; destruct H).
  apply Bool.negb_true_iff in H0.
  apply Nat.eqb_eq in H8. rewrite H8, HAstandardModel_implies.
  intro exproof.
  apply Nat.eqb_eq in H6. rewrite H6, HAstandardModel_implies.
  intro forallproof.
  apply Nat.eqb_eq in H7. rewrite H7, HAstandardModel_exists in exproof.
  apply Nat.eqb_eq in H5. rewrite H5, HAstandardModel_forall in forallproof.
  destruct exproof as [n exproof].
  specialize (forallproof n).
  apply Nat.eqb_eq in H4. rewrite H4, HAstandardModel_implies in forallproof.
  apply Nat.eqb_eq in H2. rewrite H2 in forallproof.
  rewrite (VarIndep (CoordNat (CoordNat prop 2) 2)) in forallproof.
  2: exact H0.
  apply forallproof.
  apply Nat.eqb_eq in H3. rewrite H3.
  apply Nat.eqb_eq in H1. rewrite H1.
  exact exproof.
Qed.

(* This works around an infinite loop at Qed *)
Lemma HAstandardModel_EqVars : forall varValues,
    HAstandardModel (EqTerms (EvenVars 0 2) (EvenVars 1 2) 1) varValues
    = (HAstandardModelTerm varValues (Lvar 0) = HAstandardModelTerm varValues (Lvar 1)
       /\ HAstandardModelTerm varValues (Lvar 2) = HAstandardModelTerm varValues (Lvar 3)).
Proof.
  intros varValues. simpl.
  rewrite HAstandardModel_and.
  rewrite HAstandardModel_eq.
  rewrite HAstandardModel_eq.
  rewrite CoordEvenVarsNat, CoordEvenVarsNat.
  rewrite CoordEvenVarsNat, CoordEvenVarsNat.
  rewrite Nat.mul_0_r, Nat.mul_1_r, Nat.add_0_r, Nat.add_0_r.
  reflexivity. apply Nat.le_refl. apply Nat.le_refl. auto. auto.
Qed.

Lemma EqualityRelationAxiomSatisfied : forall l r varValues,
    HAstandardModel (EqTerms (EvenVars 0 (l-2)) (EvenVars 1 (l-2)) (pred (l-2))) varValues
    -> (HAstandardModel
         (Lrel r (EvenVars 0 (l-2))) varValues <->
       HAstandardModel
         (Lrel r (EvenVars 1 (l-2))) varValues).
Proof.
  intros l r varValues equalities.
  rewrite HAstandardModel_rel, HAstandardModel_rel.
  rewrite LengthEvenVarsNat, LengthEvenVarsNat.
  destruct (l-2 =? 2) eqn:des.
  apply Nat.eqb_eq in des.
  rewrite des. rewrite des in equalities.
  simpl (2-1) in equalities.
  rewrite HAstandardModel_EqVars in equalities. destruct equalities.
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
    IsEqualityAxiom f = true -> HAstandardModelSat f.
Proof.
  intros f H varValues.
  apply Bool.orb_prop in H. destruct H.
  apply Bool.orb_prop in H. destruct H.
  apply Bool.orb_prop in H. destruct H.
  apply Bool.orb_prop in H. destruct H.
  - apply Nat.eqb_eq in H. rewrite H, HAstandardModel_eq. reflexivity.
  - apply Nat.eqb_eq in H.
    rewrite H, HAstandardModel_implies, HAstandardModel_eq, HAstandardModel_eq.
    intro H0. symmetry. exact H0.
  - apply Nat.eqb_eq in H.
    rewrite H, HAstandardModel_implies, HAstandardModel_and.
    rewrite HAstandardModel_eq, HAstandardModel_eq, HAstandardModel_eq.
    intros [H0 H1].
    rewrite H0. exact H1.
  - apply andb_prop in H. destruct H.
    apply andb_prop in H. destruct H.
    apply andb_prop in H. destruct H.
    apply Nat.eqb_eq in H.
    apply Nat.eqb_eq in H0.
    apply Nat.eqb_eq in H1.
    apply Nat.leb_le in H2.
    rewrite H, HAstandardModel_implies, H0, H1.
    rewrite HAstandardModel_eq.
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
    rewrite HAstandardModel_eq.
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
    rewrite HAstandardModel_and, HAstandardModel_eq, HAstandardModel_eq in H2.
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
    rewrite H, HAstandardModel_implies, H0, H1.
    rewrite HAstandardModel_equiv.
    apply EqualityRelationAxiomSatisfied.
Qed.

Lemma PAloopCorrection : forall l IsAxiom (proof:nat),
    l = LengthNat proof
    -> (forall n:nat, IsAxiom n = true -> HAstandardModelSat n)
    -> IsProofLoop IsAxiom proof (LengthNat proof) = true
    -> forall i:nat, i < LengthNat proof
    -> HAstandardModelSat (CoordNat proof i).
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
      rewrite isimp, HAstandardModel_implies in H0.
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
      apply Nat.eqb_eq in all. rewrite all, HAstandardModel_forall, H0.
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

Lemma HAstandardModel_correction : forall IsAxiom (prop : nat),
    (forall n:nat, IsAxiom n = true -> HAstandardModelSat n)
    -> IsProved IsAxiom prop
    -> HAstandardModelSat prop.
Proof.
  intros IsAxiom prop IsAxiomSat [proof isproof] varValues.
  apply andb_prop in isproof. destruct isproof.
  apply andb_prop in H. destruct H.
  apply Nat.eqb_eq in H. subst prop.
  apply Nat.leb_le in H1.
  exact (PAloopCorrection (LengthNat proof) IsAxiom proof
                          eq_refl IsAxiomSat H0 0 H1 varValues).
Qed.

Lemma HAundefinedRelations : forall r args n:nat,
    LengthNat args <> 2
    -> IsProof IsWeakHeytingAxiom (Lrel r args) n = false.
Proof.
  intros.
  destruct (IsProof IsWeakHeytingAxiom (Lrel r args) n) eqn:des. 2: reflexivity.
  exfalso.
  assert (IsProved IsWeakHeytingAxiom (Lrel r args)).
  { exists n. exact des. }
  pose proof (HAstandardModel_correction IsWeakHeytingAxiom _ HAaxiomsSatisfied
                                         H0 (fun _ => 0)).
  rewrite HAstandardModel_rel in H1.
  apply Nat.eqb_neq in H. rewrite H in H1.
  contradiction.
Qed.

Lemma HAconsistent : IsConsistent IsWeakHeytingAxiom.
Proof.
  intro incons. unfold IsInconsistent in incons.
  apply HAstandardModel_correction in incons.
  2: exact HAaxiomsSatisfied.
  specialize (incons (fun _ => 0)).
  rewrite HAstandardModel_not in incons. contradict incons.
  rewrite HAstandardModel_eq. reflexivity.
Qed.

Definition NoQuantifiersRec (f : nat) (rec : nat -> bool) : bool :=
  match CoordNat f 0 with
  | LnotHead => rec 1
  | LimpliesHead
  | LorHead
  | LandHead => rec 1 && rec 2
  | LforallHead
  | LexistsHead => false
  | LrelHead => true
  | _ => false
  end.

Definition NoQuantifiers : nat -> bool := TreeFoldNat NoQuantifiersRec false.

Lemma NoQuantifiers_step : forall f,
    NoQuantifiers f
    = TreeFoldNatRec NoQuantifiersRec false f (fun k _ => NoQuantifiers k).
Proof.
  intros.
  unfold NoQuantifiers, TreeFoldNat. rewrite Fix_eq.
  reflexivity.
  intros. unfold NoQuantifiers, TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat x) 0). reflexivity.
  unfold NoQuantifiersRec.
  destruct (CoordNat x 0). reflexivity.
  destruct n. rewrite H. reflexivity.
  destruct n. rewrite H, H. reflexivity.
  destruct n. rewrite H, H. reflexivity.
  destruct n. rewrite H, H. reflexivity.
  reflexivity.
Qed.

Lemma NoQuantifiers_not : forall f,
    NoQuantifiers (Lnot f) = NoQuantifiers f.
Proof.
  intros. rewrite NoQuantifiers_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lnot f)) 0).
  exfalso. rewrite LengthLnot in l. inversion l.
  unfold NoQuantifiersRec, Lnot; rewrite CoordConsHeadNat.
  rewrite CoordConsTailNat.
  rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma NoQuantifiers_implies : forall f g,
    NoQuantifiers (Limplies f g) = (NoQuantifiers f && NoQuantifiers g)%bool.
Proof.
  intros. rewrite NoQuantifiers_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Limplies f g)) 0).
  exfalso. rewrite LengthLimplies in l. inversion l.
  unfold NoQuantifiersRec.
  rewrite CoordNat_implies_1, CoordNat_implies_2.
  unfold Limplies.
  rewrite CoordConsHeadNat. reflexivity.
Qed.

Lemma NoQuantifiers_or : forall f g,
    NoQuantifiers (Lor f g) = (NoQuantifiers f && NoQuantifiers g)%bool.
Proof.
  intros. rewrite NoQuantifiers_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lor f g)) 0).
  exfalso. rewrite LengthLor in l. inversion l.
  unfold NoQuantifiersRec.
  rewrite CoordNat_or_1, CoordNat_or_2.
  unfold Lor.
  rewrite CoordConsHeadNat. reflexivity.
Qed.

Lemma NoQuantifiers_and : forall f g,
    NoQuantifiers (Land f g) = (NoQuantifiers f && NoQuantifiers g)%bool.
Proof.
  intros. rewrite NoQuantifiers_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Land f g)) 0).
  exfalso. rewrite LengthLand in l. inversion l.
  unfold NoQuantifiersRec.
  rewrite CoordNat_and_1, CoordNat_and_2.
  unfold Land.
  rewrite CoordConsHeadNat. reflexivity.
Qed.

Lemma NoQuantifiers_forall : forall v f,
    NoQuantifiers (Lforall v f) = false.
Proof.
  intros. rewrite NoQuantifiers_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lforall v f)) 0).
  exfalso. rewrite LengthLforall in l. inversion l.
  unfold NoQuantifiersRec.
  unfold Lforall at 1. rewrite CoordConsHeadNat. reflexivity.
Qed.

Lemma NoQuantifiers_exists : forall v f,
    NoQuantifiers (Lexists v f) = false.
Proof.
  intros. rewrite NoQuantifiers_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lexists v f)) 0).
  exfalso. rewrite LengthLexists in l. inversion l.
  unfold NoQuantifiersRec.
  unfold Lexists at 1. rewrite CoordConsHeadNat. reflexivity.
Qed.

Lemma ClosedTerm_normalize :
  forall t,
    IsPeanoTerm t = true
    -> (forall v, VarOccursInTerm v t = false)
    -> IsProved IsWeakHeytingAxiom (Leq t (PAnat (HAstandardModelTerm (fun _ => 0) t))).
Proof.
  apply (Fix lt_wf (fun t => IsPeanoTerm t = true ->
  (forall v : nat, VarOccursInTerm v t = false) ->
  IsProved IsWeakHeytingAxiom
           (Leq t (PAnat (HAstandardModelTerm (fun _ : nat => 0) t))))).
  intros t IHt tterm tclosed.
  rewrite IsPeanoTerm_step in tterm.
  rewrite HAstandardModelTerm_step.
  unfold TreeFoldNatRec in tterm.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat t) 0). discriminate tterm.
  unfold IsPeanoTermRec in tterm.
  unfold HAstandardModelTermRec.
  destruct (CoordNat t 0) eqn:headT. discriminate tterm.
  do 7 (destruct n; [discriminate tterm|]).
  destruct n.
  (* Lop *)
  destruct (CoordNat t 1) eqn:opT.
  apply andb_prop in tterm. destruct tterm.
  apply andb_prop in H. destruct H.
  apply Bool.orb_prop in H. destruct H.
  apply Bool.orb_prop in H. destruct H.
  - (* PAzero *)
    apply Nat.eqb_eq in H. rewrite H.
    rewrite (HeadTailDecompNat t).
    2: rewrite H; auto. rewrite headT.
    rewrite (HeadTailDecompNat (TailNat t)).
    rewrite CoordTailNat, opT.
    rewrite H in H0. simpl in H0.
    apply Nat.eqb_eq in H0. rewrite H0.
    apply LeqRefl. apply IsLterm_PAnat.
    rewrite LengthTailNat, H. apply Nat.le_refl.
  - (* PAsucc *)
    apply andb_prop in H. destruct H.
    apply Nat.eqb_eq in H. rewrite H.
    assert (t = PAsucc (CoordNat t 2)).
    { rewrite (HeadTailDecompNat t) at 1.
      2: rewrite H; auto. rewrite headT.
      unfold PAsucc, Lop1, Lop. apply f_equal.
      rewrite (HeadTailDecompNat (TailNat t)).
      rewrite CoordTailNat, opT. apply f_equal.
      rewrite (HeadTailDecompNat (TailNat (TailNat t))).
      apply Nat.eqb_eq in H0. rewrite H in H0. simpl in H0.
      rewrite H0.
      rewrite CoordTailNat, CoordTailNat. reflexivity.
      rewrite LengthTailNat, LengthTailNat, H. apply Nat.le_refl.
      rewrite LengthTailNat, H. simpl. auto. }
    rewrite H3 at 1. simpl.
    apply (LeqElim_op1 IsWeakHeytingAxiom 0).
    apply IHt.
    exact (CoordLower _ _ (LengthPositive _ l)). exact H2.
    intro v. specialize (tclosed v).
    rewrite H3 in tclosed. unfold PAsucc in tclosed.
    rewrite VarOccursInTerm_op1 in tclosed. exact tclosed.
  - (* PAplus *)
    apply andb_prop in H. destruct H.
    apply andb_prop in H. destruct H.
    apply Nat.eqb_eq in H. rewrite H.
    assert (t = PAplus (CoordNat t 2) (CoordNat t 3)).
    { rewrite (HeadTailDecompNat t) at 1.
      2: rewrite H; auto. rewrite headT.
      unfold PAplus, Lop2, Lop. apply f_equal.
      rewrite (HeadTailDecompNat (TailNat t)).
      rewrite CoordTailNat, opT. apply f_equal.
      rewrite (HeadTailDecompNat (TailNat (TailNat t))).
      apply Nat.eqb_eq in H0. rewrite H in H0. simpl in H0.
      rewrite (HeadTailDecompNat (TailNat (TailNat (TailNat t)))), H0.
      do 5 rewrite CoordTailNat.
      reflexivity.
      rewrite LengthTailNat, LengthTailNat, LengthTailNat, H. apply Nat.le_refl.
      rewrite LengthTailNat, LengthTailNat, H. simpl. auto.
      rewrite LengthTailNat, H. simpl. auto. }
    rewrite H4 at 1.
    apply (LeqTrans _ _ (PAplus (PAnat
          (HAstandardModelTerm (fun _ : nat => 0) (CoordNat t 2)))
           (PAnat (HAstandardModelTerm (fun _ : nat => 0) (CoordNat t 3))))).
    apply (LeqElim_op2 IsWeakHeytingAxiom 0).
    apply IHt.
    exact (CoordLower _ _ (LengthPositive _ l)). exact H3.
    intro v. specialize (tclosed v).
    rewrite H4 in tclosed. unfold PAplus in tclosed.
    rewrite VarOccursInTerm_op2 in tclosed.
    apply Bool.orb_false_elim in tclosed. apply tclosed.
    apply IHt.
    exact (CoordLower _ _ (LengthPositive _ l)). exact H2.
    intro v. specialize (tclosed v).
    rewrite H4 in tclosed. unfold PAplus in tclosed.
    rewrite VarOccursInTerm_op2 in tclosed.
    apply Bool.orb_false_elim in tclosed. apply tclosed.
    apply PAplus_normalize.
  - (* PAmult *)
    destruct n. 2: discriminate tterm.
    apply andb_prop in tterm. destruct tterm.
    apply andb_prop in H. destruct H.
    apply andb_prop in H. destruct H.
    apply andb_prop in H. destruct H.
    apply Nat.eqb_eq in H. rewrite H.
    assert (t = PAmult (CoordNat t 2) (CoordNat t 3)).
    { rewrite (HeadTailDecompNat t) at 1.
      2: rewrite H; auto. rewrite headT.
      unfold PAmult, Lop2, Lop. apply f_equal.
      rewrite (HeadTailDecompNat (TailNat t)).
      rewrite CoordTailNat, opT. apply f_equal.
      rewrite (HeadTailDecompNat (TailNat (TailNat t))).
      apply Nat.eqb_eq in H0. rewrite H in H0. simpl in H0.
      rewrite (HeadTailDecompNat (TailNat (TailNat (TailNat t)))), H0.
      do 5 rewrite CoordTailNat.
      reflexivity.
      rewrite LengthTailNat, LengthTailNat, LengthTailNat, H. apply Nat.le_refl.
      rewrite LengthTailNat, LengthTailNat, H. simpl. auto.
      rewrite LengthTailNat, H. simpl. auto. }
    rewrite H4 at 1.
    apply (LeqTrans _ _ (PAmult (PAnat
          (HAstandardModelTerm (fun _ : nat => 0) (CoordNat t 2)))
           (PAnat (HAstandardModelTerm (fun _ : nat => 0) (CoordNat t 3))))).
    apply (LeqElim_op2 IsWeakHeytingAxiom 1).
    apply IHt.
    exact (CoordLower _ _ (LengthPositive _ l)). exact H3.
    intro v. specialize (tclosed v).
    rewrite H4 in tclosed. unfold PAmult in tclosed.
    rewrite VarOccursInTerm_op2 in tclosed.
    apply Bool.orb_false_elim in tclosed. apply tclosed.
    apply IHt.
    exact (CoordLower _ _ (LengthPositive _ l)). exact H2.
    intro v. specialize (tclosed v).
    rewrite H4 in tclosed. unfold PAmult in tclosed.
    rewrite VarOccursInTerm_op2 in tclosed.
    apply Bool.orb_false_elim in tclosed. apply tclosed.
    apply PAmult_normalize.
  - (* Lvar *)
    destruct n.
    apply Nat.eqb_eq in tterm. rewrite tterm in tclosed.
    specialize (tclosed (CoordNat t 1)).
    rewrite VarOccursInTerm_var, Nat.eqb_refl in tclosed.
    discriminate tclosed. discriminate tterm.
Qed.

Lemma Heyting_le_dec : forall t u,
    IsPeanoTerm t = true
    -> IsPeanoTerm u = true
    -> (forall v, VarOccursInTerm v t = false)
    -> (forall v, VarOccursInTerm v u = false)
    -> { IsProved IsWeakHeytingAxiom (PAle t u) }
      + { IsProved IsWeakHeytingAxiom (Lnot (PAle t u)) }.
Proof.
  intros.
  pose proof (ClosedTerm_normalize _ H H1) as normt.
  pose proof (ClosedTerm_normalize _ H0 H2) as normu.
  destruct (le_lt_dec (HAstandardModelTerm (fun _ => 0) t)
                      (HAstandardModelTerm (fun _ => 0) u)).
  - left.
    pose proof (LeqElim_rel2 IsWeakHeytingAxiom 1
                             _ _ _ _ normt normu).
    apply LandElim2 in H3.
    apply (LimpliesElim _ _ _ H3); clear H3.
    apply PAle_normalize, l.
  - right.
    apply PAlt_not_le in l.
    apply NotByContradiction.
    apply (LimpliesTrans _ _ (PAle (PAnat (HAstandardModelTerm (fun _ : nat => 0) t))
                                   (PAnat (HAstandardModelTerm (fun _ : nat => 0) u)))).
    pose proof (LeqElim_rel2 IsWeakHeytingAxiom 1
                             _ _ _ _ normt normu).
    apply LandElim1 in H3. apply H3.
    apply FalseElim_impl. exact l.
    unfold PAle. rewrite IsLproposition_not, IsLproposition_rel2.
    rewrite PeanoTermIsLterm, PeanoTermIsLterm. reflexivity.
    exact H0. exact H.
Qed.

Lemma Heyting_eq_dec : forall t u,
    IsPeanoTerm t = true
    -> IsPeanoTerm u = true
    -> (forall v, VarOccursInTerm v t = false)
    -> (forall v, VarOccursInTerm v u = false)
    -> { IsProved IsWeakHeytingAxiom (Leq t u) }
      + { IsProved IsWeakHeytingAxiom (Lnot (Leq t u)) }.
Proof.
  intros.
  pose proof (ClosedTerm_normalize _ H H1) as normt.
  pose proof (ClosedTerm_normalize _ H0 H2) as normu.
  destruct (Nat.eq_dec (HAstandardModelTerm (fun _ => 0) t)
                       (HAstandardModelTerm (fun _ => 0) u)).
  - left.
    apply (LeqTrans _ _ (PAnat (HAstandardModelTerm (fun _ => 0) t))).
    exact normt. rewrite e. apply LeqSym. exact normu.
  - right.
    destruct (le_lt_dec (HAstandardModelTerm (fun _ => 0) u)
                        (HAstandardModelTerm (fun _ => 0) t)).
    + destruct (Nat.lt_trichotomy (HAstandardModelTerm (fun _ => 0) t)
                                  (HAstandardModelTerm (fun _ => 0) u)).
      exfalso. apply (Nat.lt_irrefl (HAstandardModelTerm (fun _ => 0) t)).
      exact (Nat.lt_le_trans _ _ _ H3 l). destruct H3. contradiction.
      clear l n.
      apply PAlt_not_eq in H3.
      apply NotByContradiction.
      apply (LimpliesTrans _ _ (Leq (PAnat (HAstandardModelTerm (fun _ : nat => 0) t))
                                    (PAnat (HAstandardModelTerm (fun _ : nat => 0) u)))).
      pose proof (LeqElim_rel2 IsWeakHeytingAxiom 0
                               _ _ _ _ normt normu).
      apply LandElim1 in H4. apply H4.
      apply FalseElim_impl. exact H3.
      rewrite IsLproposition_not, IsLproposition_eq.
      rewrite PeanoTermIsLterm, PeanoTermIsLterm. reflexivity.
      exact H0. exact H.
    + apply PAlt_not_eq in l.
      apply NotByContradiction.
      apply (LimpliesTrans _ _ (Leq (PAnat (HAstandardModelTerm (fun _ : nat => 0) u))
                                    (PAnat (HAstandardModelTerm (fun _ : nat => 0) t)))).
      apply (LimpliesTrans _ _ (Leq u t)).
      apply LeqSym_impl. apply PeanoTermIsLterm, H.
      apply PeanoTermIsLterm, H0.
      pose proof (LeqElim_rel2 IsWeakHeytingAxiom 0
                               _ _ _ _ normu normt).
      apply LandElim1 in H3. apply H3.
      apply FalseElim_impl. exact l.
      rewrite IsLproposition_not, IsLproposition_eq.
      rewrite PeanoTermIsLterm, PeanoTermIsLterm. reflexivity.
      exact H0. exact H.
Qed.

Lemma NoQuantifiers_dec : forall prop,
    IsPeanoProposition prop = true
    -> NoQuantifiers prop = true
    -> (forall v, VarOccursFreeInFormula v prop = false)
    -> { IsProved IsWeakHeytingAxiom prop }
      + { IsProved IsWeakHeytingAxiom (Lnot prop) }.
Proof.
  apply (PeanoProposition_rect (fun prop =>
  NoQuantifiers prop = true ->
  (forall v : nat, VarOccursFreeInFormula v prop = false) ->
  {IsProved IsWeakHeytingAxiom prop} + {IsProved IsWeakHeytingAxiom (Lnot prop)})).
  - (* Leq *)
    intros. apply Heyting_eq_dec.
    exact tterm. exact uterm.
    intro v. specialize (H0 v).
    unfold Leq in H0. rewrite VarOccursFreeInFormula_rel2 in H0.
    apply Bool.orb_false_elim in H0. apply H0.
    intro v. specialize (H0 v).
    unfold Leq in H0. rewrite VarOccursFreeInFormula_rel2 in H0.
    apply Bool.orb_false_elim in H0. apply H0.
  - (* PAle *)
    intros. apply Heyting_le_dec.
    exact tterm. exact uterm.
    intro v. specialize (H0 v).
    unfold PAle in H0. rewrite VarOccursFreeInFormula_rel2 in H0.
    apply Bool.orb_false_elim in H0. apply H0.
    intro v. specialize (H0 v).
    unfold PAle in H0. rewrite VarOccursFreeInFormula_rel2 in H0.
    apply Bool.orb_false_elim in H0. apply H0.
  - (* Lnot *)
    intros.
    destruct IHprop. rewrite NoQuantifiers_not in H. exact H.
    intro v. specialize (H0 v).
    rewrite VarOccursFreeInFormula_not in H0. exact H0.
    right. apply LnotLnotIntro, i.
    left. exact i.
  - (* Limplies *)
    intros. rewrite NoQuantifiers_implies in H.
    apply andb_prop in H.
    assert (IsLproposition (Limplies g h) = true).
    { rewrite IsLproposition_implies, PeanoPropositionIsLproposition, PeanoPropositionIsLproposition.
      reflexivity. exact hprop. exact gprop. }
    destruct IHg. apply H.
    intro v. specialize (H0 v).
    rewrite VarOccursFreeInFormula_implies in H0.
    apply Bool.orb_false_elim in H0. apply H0.
    destruct IHh. apply H.
    intro v. specialize (H0 v).
    rewrite VarOccursFreeInFormula_implies in H0.
    apply Bool.orb_false_elim in H0. apply H0.
    left. apply DropHypothesis.
    apply PeanoPropositionIsLproposition, gprop. exact i0.
    right.
    apply (LimpliesElim _ (Limplies (Limplies g h) (Lnot h))).
    apply (LimpliesElim _ (Limplies (Limplies g h) h)).
    apply IsProvedPropAx, Ax3IsPropAx, Ax3IsAx3.
    exact H1.
    apply PeanoPropositionIsLproposition, hprop.
    apply (LimpliesElim _ g). 2: exact i.
    apply PullHypothesis.
    apply (LimpliesTrans _ _ (Land (Limplies g h) g)).
    apply LandIntroHyp.
    apply LandElim2_impl.
    apply PeanoPropositionIsLproposition, gprop. exact H1.
    apply LandElim1_impl.
    apply PeanoPropositionIsLproposition, gprop. exact H1.
    apply PushHypothesis. apply LimpliesRefl.
    exact H1.
    apply DropHypothesis. exact H1. exact i0.
    left.
    apply FalseElim_impl. exact i.
    apply PeanoPropositionIsLproposition, hprop.
  - (* Lor *)
    intros. rewrite NoQuantifiers_or in H.
    apply andb_prop in H.
    destruct IHg. apply H.
    intro v. specialize (H0 v).
    rewrite VarOccursFreeInFormula_or in H0.
    apply Bool.orb_false_elim in H0. apply H0.
    left. apply LorIntro1.
    apply PeanoPropositionIsLproposition, hprop. exact i.
    destruct IHh. apply H.
    intro v. specialize (H0 v).
    rewrite VarOccursFreeInFormula_or in H0.
    apply Bool.orb_false_elim in H0. apply H0.
    left. apply LorIntro2.
    apply PeanoPropositionIsLproposition, gprop. exact i0.
    right.
    apply NotByContradiction.
    apply LorElim.
    apply FalseElim_impl. exact i.
    rewrite IsLproposition_not, IsLproposition_or.
    rewrite PeanoPropositionIsLproposition, PeanoPropositionIsLproposition.
    reflexivity. exact hprop. exact gprop.
    apply FalseElim_impl. exact i0.
    rewrite IsLproposition_not, IsLproposition_or.
    rewrite PeanoPropositionIsLproposition, PeanoPropositionIsLproposition.
    reflexivity. exact hprop. exact gprop.
  - (* Land *)
    intros. rewrite NoQuantifiers_and in H.
    apply andb_prop in H.
    destruct IHg. apply H.
    intro v. specialize (H0 v).
    rewrite VarOccursFreeInFormula_and in H0.
    apply Bool.orb_false_elim in H0. apply H0.
    destruct IHh. apply H.
    intro v. specialize (H0 v).
    rewrite VarOccursFreeInFormula_and in H0.
    apply Bool.orb_false_elim in H0. apply H0.
    left. apply LandIntro; assumption.
    right.
    apply NotByContradiction.
    apply (LimpliesTrans _ _ h). apply LandElim2_impl.
    apply PeanoPropositionIsLproposition, gprop.
    apply PeanoPropositionIsLproposition, hprop.
    apply FalseElim_impl. exact i0.
    rewrite IsLproposition_not, IsLproposition_and.
    rewrite PeanoPropositionIsLproposition, PeanoPropositionIsLproposition.
    reflexivity. exact hprop. exact gprop.
    right.
    apply NotByContradiction.
    apply (LimpliesTrans _ _ g). apply LandElim1_impl.
    apply PeanoPropositionIsLproposition, gprop.
    apply PeanoPropositionIsLproposition, hprop.
    apply FalseElim_impl. exact i.
    rewrite IsLproposition_not, IsLproposition_and.
    rewrite PeanoPropositionIsLproposition, PeanoPropositionIsLproposition.
    reflexivity. exact hprop. exact gprop.
  - (* Lforall *)
    intros. exfalso. rewrite NoQuantifiers_forall in H. discriminate H.
  - (* Lexists *)
    intros. exfalso. rewrite NoQuantifiers_exists in H. discriminate H.
Qed.

(* This could be lifted to Delta_0 formulas *)
Lemma NoQuantifiers_sat : forall prop varValues,
    IsPeanoProposition prop = true
    -> NoQuantifiers prop = true
    -> (forall v, VarOccursFreeInFormula v prop = false)
    -> HAstandardModel prop varValues
    -> IsProved IsWeakHeytingAxiom prop.
Proof.
  intros.
  destruct (NoQuantifiers_dec prop H H0 H1). exact i.
  exfalso.
  apply HAstandardModel_correction in i.
  specialize (i varValues).
  rewrite HAstandardModel_not in i. contradiction.
  exact HAaxiomsSatisfied.
Qed.
