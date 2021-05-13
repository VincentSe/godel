(** The Peano axioms as a computable characteristic function nat -> bool,
    which tells whether a natural number represents such an axiom. *)

Require Import PeanoNat.
Require Import Arith.Wf_nat.
Require Import Arith.Compare_dec.
Require Import EnumSeqNat.
Require Import Formulas.
Require Import Substitutions.
Require Import IsFreeForSubst.
Require Import Proofs.
Require Import ProofTactics.

(* We give more readable names to the symbols used by the Peano axioms. *)
Definition PAzero : nat := Lconst 0.
Definition PAsucc : nat -> nat := Lop1 0.
Definition PAplus : nat -> nat -> nat := Lop2 0.
Definition PAmult : nat -> nat -> nat := Lop2 1.
Definition PAle : nat -> nat -> nat := Lrel2 1. (* Lrel2 0 is Leq by convention *)

Definition PAax1 : nat := Lforall 0 (Lnot (Leq (PAsucc (Lvar 0)) PAzero)).
Definition PAax2 : nat := Lforall 0 (Lor (Leq (Lvar 0) PAzero)
                                       (Lexists 1 (Leq (Lvar 0) (PAsucc (Lvar 1))))).
Definition PAax3 : nat :=
  Lforall 0 (Lforall 1 (Limplies (Leq (PAsucc (Lvar 0)) (PAsucc (Lvar 1)))
                                 (Leq (Lvar 0) (Lvar 1)))).
Definition PAax4 : nat := Lforall 0 (Leq (PAplus (Lvar 0) PAzero) (Lvar 0)).
Definition PAax5 : nat :=
  Lforall 0 (Lforall 1 (Leq (PAplus (Lvar 0) (PAsucc (Lvar 1)))
                            (PAsucc (PAplus (Lvar 0) (Lvar 1))))).
Definition PAax6 : nat := Lforall 0 (Leq (PAmult (Lvar 0) PAzero) PAzero).
Definition PAax7 : nat :=
  Lforall 0 (Lforall 1 (Leq (PAmult (Lvar 0) (PAsucc (Lvar 1)))
                            (PAplus (PAmult (Lvar 0) (Lvar 1)) (Lvar 0)))).

Definition PAorder : nat :=
  Lforall 0 (Lforall 1 (Lequiv (PAle (Lvar 0) (Lvar 1))
                               (Lexists 2 (Leq (PAplus (Lvar 2) (Lvar 0)) (Lvar 1))))).

(* We add the Peano induction schema for the sake of completeness,
   but won't use it in the rest of this repository. *)
Definition PAinduction (f : nat) : bool :=
  IsLproposition f
  && IsLimplies f
  && IsLand (CoordNat f 1)
  && IsLforall (CoordNat (CoordNat f 1) 2)
  && IsLimplies (CoordNat (CoordNat (CoordNat f 1) 2) 2)
  && IsLforall (CoordNat f 2)
  && Nat.eqb (CoordNat (CoordNat (CoordNat f 1) 2) 1)
             (CoordNat (CoordNat f 2) 1) (* same variable quantified *)
  && Nat.eqb (CoordNat (CoordNat (CoordNat (CoordNat f 1) 2) 2) 1)
             (CoordNat (CoordNat f 2) 2)
  && Nat.eqb (CoordNat (CoordNat f 1) 1)
             (Subst PAzero (CoordNat (CoordNat f 2) 1) (CoordNat (CoordNat f 2) 2))
  && Nat.eqb (CoordNat (CoordNat (CoordNat (CoordNat f 1) 2) 2) 2)
             (Subst (PAsucc (Lvar (CoordNat (CoordNat f 2) 1)))
                    (CoordNat (CoordNat f 2) 1)
                    (CoordNat (CoordNat f 2) 2)).

Definition IsWeakHeytingAxiom (prop : nat) : bool :=
  Nat.eqb prop PAax1
  || Nat.eqb prop PAax2
  || Nat.eqb prop PAax3
  || Nat.eqb prop PAax4
  || Nat.eqb prop PAax5
  || Nat.eqb prop PAax6
  || Nat.eqb prop PAax7
  || Nat.eqb prop PAorder.

(* Propositional axiom schema ~~X1 -> X1 *)
Definition IsPropAx4 (f : nat) : bool :=
  IsLproposition f
  && IsLimplies f
  && IsLnot (CoordNat f 1)
  && IsLnot (CoordNat (CoordNat f 1) 1)
  && Nat.eqb (CoordNat (CoordNat (CoordNat f 1) 1) 1) (CoordNat f 2).

(* Peano arithmetic extends Heyting arithmetic by adding the excluded middle
   axiom schema. PA is therefore one of the applications of the incompleteness
   theorem. *)
Definition IsWeakPeanoAxiom (prop : nat) : bool :=
  IsWeakHeytingAxiom prop || IsPropAx4 prop.

Lemma PAaxiomIsLproposition :
  forall k : nat, IsWeakPeanoAxiom k = true -> IsLproposition k = true.
Proof.
  intros.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  - apply Nat.eqb_eq in H. subst k.
    unfold PAax1. rewrite IsLproposition_forall, IsLproposition_not.
    unfold Leq. rewrite IsLproposition_rel2.
    unfold PAsucc, PAzero.
    rewrite IsLterm_op1, IsLterm_var, IsLterm_const.
    reflexivity.
  - apply Nat.eqb_eq in H. subst k.
    unfold PAax2. rewrite IsLproposition_forall.
    unfold Leq. rewrite IsLproposition_or.
    rewrite IsLproposition_rel2, IsLproposition_exists.
    rewrite IsLproposition_rel2.
    unfold PAsucc, PAzero.
    rewrite IsLterm_op1, IsLterm_var, IsLterm_const.
    rewrite IsLterm_var.
    reflexivity.
  - apply Nat.eqb_eq in H. subst k.
    unfold PAax3. rewrite IsLproposition_forall, IsLproposition_forall.
    rewrite IsLproposition_implies. apply andb_true_intro.
    split. unfold Leq.
    rewrite IsLproposition_rel2.
    apply andb_true_intro. split.
    unfold PAsucc. rewrite IsLterm_op1, IsLterm_var. reflexivity.
    unfold PAsucc. rewrite IsLterm_op1, IsLterm_var. reflexivity.
    unfold Leq.
    rewrite IsLproposition_rel2.
    apply andb_true_intro. split.
    unfold PAsucc. rewrite IsLterm_var. reflexivity.
    unfold PAsucc. rewrite IsLterm_var. reflexivity.
  - apply Nat.eqb_eq in H. subst k.
    unfold PAax4. rewrite IsLproposition_forall.
    unfold Leq.
    rewrite IsLproposition_rel2.
    apply andb_true_intro. split.
    unfold PAplus. rewrite IsLterm_op2.
    apply andb_true_intro. split.
    rewrite IsLterm_var. reflexivity.
    unfold PAzero.
    rewrite IsLterm_const. reflexivity.
    rewrite IsLterm_var. reflexivity.
  - apply Nat.eqb_eq in H. subst k.
    unfold PAax5.
    rewrite IsLproposition_forall, IsLproposition_forall.
    unfold Leq. rewrite IsLproposition_rel2.
    apply andb_true_intro. split.
    unfold PAplus. rewrite IsLterm_op2.
    apply andb_true_intro. split.
    rewrite IsLterm_var. reflexivity.
    unfold PAsucc. rewrite IsLterm_op1, IsLterm_var. reflexivity.
    unfold PAsucc. rewrite IsLterm_op1.
    unfold PAplus. rewrite IsLterm_op2.
    apply andb_true_intro. split.
    rewrite IsLterm_var. reflexivity.
    rewrite IsLterm_var. reflexivity.
  - apply Nat.eqb_eq in H. subst k.
    unfold PAax6, Leq.
    rewrite IsLproposition_forall, IsLproposition_rel2.
    apply andb_true_intro; split.
    unfold PAmult. rewrite IsLterm_op2.
    apply andb_true_intro; split.
    apply IsLterm_var.
    unfold PAzero.
    rewrite IsLterm_const. reflexivity.
    unfold PAzero.
    rewrite IsLterm_const. reflexivity.
  - apply Nat.eqb_eq in H. subst k.
    unfold PAax7, Leq.
    rewrite IsLproposition_forall, IsLproposition_forall.
    rewrite IsLproposition_rel2.
    apply andb_true_intro; split.
    unfold PAmult. rewrite IsLterm_op2.
    apply andb_true_intro; split.
    apply IsLterm_var.
    unfold PAsucc. rewrite IsLterm_op1. apply IsLterm_var.
    unfold PAplus. rewrite IsLterm_op2.
    apply andb_true_intro; split.
    2: apply IsLterm_var.
    unfold PAmult. rewrite IsLterm_op2.
    apply andb_true_intro; split; apply IsLterm_var.
  - apply Nat.eqb_eq in H. subst k.
    unfold PAorder, PAle.
    rewrite IsLproposition_forall, IsLproposition_forall.
    rewrite IsLproposition_equiv.
    apply andb_true_intro; split.
    rewrite IsLproposition_rel2.
    apply andb_true_intro; split.
    apply IsLterm_var.
    apply IsLterm_var.
    rewrite IsLproposition_exists.
    unfold Leq. rewrite IsLproposition_rel2.
    apply andb_true_intro; split.
    2: apply IsLterm_var.
    unfold PAplus. rewrite IsLterm_op2.
    apply andb_true_intro; split; apply IsLterm_var.
  - do 4 (apply andb_prop in H; destruct H).
    exact H.
Qed.


(** Test functions that formulas only use the Peano symbols. *)

Definition IsPeanoTermRec (t : nat) (rec : nat -> bool) : bool :=
  match CoordNat t 0 with
  | LvarHead => IsLvar t
  | LopHead => match CoordNat t 1 with
              | 0 => (* PAzero or PAsucc or PAplus *)
                Nat.eqb (LengthNat t) 2
                || Nat.eqb (LengthNat t) 3 && rec 2
                || Nat.eqb (LengthNat t) 4 && rec 2 && rec 3
              | 1 => (* PAmult *)
                Nat.eqb (LengthNat t) 4 && rec 2 && rec 3
              | _ => false
              end
              && Nat.leb 2 (LengthNat t)
              && Nat.eqb (NthTailNat t (LengthNat t)) 0
  | _ => false
  end.
Definition IsPeanoTerm : nat -> bool := TreeFoldNat IsPeanoTermRec false.

Lemma IsPeanoTerm_step : forall t,
    IsPeanoTerm t = TreeFoldNatRec IsPeanoTermRec false t (fun k _ => IsPeanoTerm k).
Proof.
  intros.
  unfold IsPeanoTerm, TreeFoldNat. rewrite Fix_eq.
  reflexivity.
  intros. unfold TreeFoldNatRec, IsPeanoTermRec.
  destruct (le_lt_dec (LengthNat x) 0). reflexivity.
  destruct (CoordNat x 0). reflexivity.
  repeat (destruct n; [reflexivity|]).
  destruct n. rewrite H, H. reflexivity.
  destruct n; reflexivity.
Qed.

Lemma IsPeanoTerm_PAzero : IsPeanoTerm PAzero = true.
Proof.
  intros. rewrite IsPeanoTerm_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat PAzero) 0).
  unfold PAzero in l. rewrite LengthLconst in l. inversion l.
  unfold IsPeanoTermRec.
  unfold PAzero, Lconst, Lop.
  rewrite CoordConsHeadNat.
  rewrite CoordConsTailNat, CoordConsHeadNat.
  rewrite LengthConsNat, LengthConsNat. simpl.
  do 2 rewrite TailConsNat. reflexivity.
Qed.

Lemma IsPeanoTerm_PAsucc : forall n,
    IsPeanoTerm (PAsucc n) = IsPeanoTerm n.
Proof.
  intros. rewrite IsPeanoTerm_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (PAsucc n)) 0).
  unfold PAsucc,Lop1 in l. rewrite LengthLop in l. inversion l.
  unfold IsPeanoTermRec.
  unfold PAsucc, Lop1, Lop.
  rewrite CoordConsHeadNat.
  rewrite CoordConsTailNat, CoordConsHeadNat.
  rewrite LengthConsNat, LengthConsNat, LengthConsNat. simpl.
  do 2 rewrite CoordConsTailNat.
  rewrite CoordConsHeadNat.
  do 3 rewrite TailConsNat. simpl.
  destruct (IsPeanoTerm n); reflexivity.
Qed.

Lemma IsPeanoTerm_PAmult : forall n m,
    IsPeanoTerm (PAmult n m) = (IsPeanoTerm n && IsPeanoTerm m)%bool.
Proof.
  intros. rewrite IsPeanoTerm_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (PAmult n m)) 0).
  unfold PAmult, Lop2 in l. rewrite LengthLop in l. inversion l.
  unfold IsPeanoTermRec.
  unfold PAmult, Lop2, Lop.
  rewrite CoordConsHeadNat.
  rewrite CoordConsTailNat, CoordConsHeadNat.
  do 4 rewrite LengthConsNat. simpl.
  do 5 rewrite CoordConsTailNat.
  rewrite CoordConsHeadNat.
  rewrite CoordConsHeadNat.
  do 4 rewrite TailConsNat. simpl.
  destruct (IsPeanoTerm n), (IsPeanoTerm m); reflexivity.
Qed.

Lemma PeanoTermIsLterm : forall t,
    IsPeanoTerm t = true -> IsLterm t = true.
Proof.
  apply (Fix lt_wf (fun t => IsPeanoTerm t = true -> IsLterm t = true)).
  intros t IHt tpeano.
  rewrite IsPeanoTerm_step in tpeano.
  unfold TreeFoldNatRec in tpeano.
  rewrite IsLterm_step. unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat t) 0). discriminate tpeano.
  unfold IsLtermRec.
  unfold IsPeanoTermRec in tpeano.
  destruct (CoordNat t 0) eqn:headT. discriminate tpeano.
  repeat (destruct n; [discriminate tpeano|]).
  destruct n.
  - (* Lop *)
    apply andb_prop in tpeano. destruct tpeano.
    apply andb_prop in H. destruct H.
    apply andb_true_intro. split. 2: exact H0.
    apply IsLopTerm_spec. apply Nat.leb_le in H1.
    split. exact H1. split. exact H1.
    intros j H2. apply IHt.
    exact (CoordLower _ _ (LengthPositive _ l)).
    destruct H2. destruct j. inversion H2.
    destruct j. apply le_S_n in H2. inversion H2. clear H2.
    destruct (CoordNat t 1) eqn:op.
    + apply Bool.orb_prop in H. destruct H.
      apply Bool.orb_prop in H. destruct H.
      apply Nat.eqb_eq in H. rewrite H in H3.
      exfalso. apply le_S_n, le_S_n in H3. inversion H3.
      apply andb_prop in H. destruct H.
      apply Nat.eqb_eq in H. rewrite H in H3.
      destruct j. exact H2.
      apply le_S_n, le_S_n, le_S_n in H3. inversion H3.
      apply andb_prop in H. destruct H.
      apply andb_prop in H. destruct H.
      apply Nat.eqb_eq in H. rewrite H in H3.
      destruct j. exact H4.
      destruct j. exact H2. do 4 apply le_S_n in H3. inversion H3.
    + destruct n. 2: discriminate H.
      apply andb_prop in H. destruct H.
      apply andb_prop in H. destruct H.
      apply Nat.eqb_eq in H. rewrite H in H3.
      destruct j. exact H4.
      destruct j. exact H2. do 4 apply le_S_n in H3. inversion H3.
  - (* Lvar *) exact tpeano.
Qed.

Definition IsPeanoPropositionRec (f : nat) (rec : nat -> bool) : bool :=
  match CoordNat f 0 with
  | LnotHead => IsLnot f && rec 1
  | LimpliesHead => IsLimplies f && rec 1 && rec 2
  | LorHead => IsLor f && rec 1 && rec 2
  | LandHead => IsLand f && rec 1 && rec 2
  | LforallHead => IsLforall f && rec 2
  | LexistsHead => IsLexists f && rec 2
  | LrelHead => Nat.eqb (LengthNat f) 4
               && (Nat.eqb (CoordNat f 1) 0 || Nat.eqb (CoordNat f 1) 1)
               && IsPeanoTerm (CoordNat f 2)
               && IsPeanoTerm (CoordNat f 3)
               && Nat.eqb (NthTailNat f (LengthNat f)) 0
  | _ => false
  end.

Definition IsPeanoProposition : nat -> bool := TreeFoldNat IsPeanoPropositionRec false.

Lemma IsPeanoProposition_step : forall p,
    IsPeanoProposition p = TreeFoldNatRec IsPeanoPropositionRec false p
                                          (fun k _ => IsPeanoProposition k).
Proof.
  intros.
  unfold IsPeanoProposition, TreeFoldNat. rewrite Fix_eq.
  reflexivity.
  intros. unfold IsPeanoPropositionRec, TreeFoldNatRec.
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

Lemma PeanoProposition_rect : forall (A : nat -> Type),
    (forall (t u:nat)
       (tterm : IsPeanoTerm t = true)
       (uterm : IsPeanoTerm u = true),
        A (Leq t u))
    -> (forall (t u:nat)
         (tterm : IsPeanoTerm t = true)
         (uterm : IsPeanoTerm u = true),
          A (PAle t u))
    -> (forall (prop:nat) (propprop : IsPeanoProposition prop = true)
         (IHprop : A prop), A (Lnot prop))
    -> (forall (g h:nat)
         (gprop : IsPeanoProposition g = true)
         (hprop : IsPeanoProposition h = true)
         (IHg : A g) (IHh : A h), A (Limplies g h))
    -> (forall (g h:nat)
         (gprop : IsPeanoProposition g = true)
         (hprop : IsPeanoProposition h = true)
         (IHg : A g) (IHh : A h), A (Lor g h))
    -> (forall (g h:nat)
         (gprop : IsPeanoProposition g = true)
         (hprop : IsPeanoProposition h = true)
         (IHg : A g) (IHh : A h), A (Land g h))
    -> (forall (v prop:nat) (propprop : IsPeanoProposition prop = true)
         (IHprop : A prop), A (Lforall v prop))
    -> (forall (v prop:nat) (propprop : IsPeanoProposition prop = true)
         (IHprop : A prop), A (Lexists v prop))
    -> forall prop, IsPeanoProposition prop = true -> A prop.
Proof.
  intros A eqcase lecase notcase impliescase orcase andcase forallcase existscase.
  apply (Fix lt_wf (fun prop => IsPeanoProposition prop = true -> A prop)).
  intros prop IHprop propprop.
  rewrite IsPeanoProposition_step in propprop.
  unfold TreeFoldNatRec in propprop.
  destruct (le_lt_dec (LengthNat prop) 0). discriminate propprop.
  unfold IsPeanoPropositionRec in propprop.
  destruct (CoordNat prop 0) eqn:headProp. discriminate propprop.
  destruct n.
  (* Lnot *)
  apply andb_prop in propprop. destruct propprop.
  apply Nat.eqb_eq in H. rewrite H. apply notcase, IHprop.
  exact H0.
  exact (CoordLower _ _ (LengthPositive _ l)). exact H0.
  destruct n.
  (* Limplies *)
  apply andb_prop in propprop. destruct propprop.
  apply andb_prop in H. destruct H.
  apply Nat.eqb_eq in H. rewrite H. apply impliescase, IHprop.
  exact H1. exact H0. apply IHprop.
  exact (CoordLower _ _ (LengthPositive _ l)). exact H1.
  exact (CoordLower _ _ (LengthPositive _ l)). exact H0.
  destruct n.
  (* Lor *)
  apply andb_prop in propprop. destruct propprop.
  apply andb_prop in H. destruct H.
  apply Nat.eqb_eq in H. rewrite H. apply orcase, IHprop.
  exact H1. exact H0. apply IHprop.
  exact (CoordLower _ _ (LengthPositive _ l)). exact H1.
  exact (CoordLower _ _ (LengthPositive _ l)). exact H0.
  destruct n.
  (* Land *)
  apply andb_prop in propprop. destruct propprop.
  apply andb_prop in H. destruct H.
  apply Nat.eqb_eq in H. rewrite H. apply andcase, IHprop.
  exact H1. exact H0. apply IHprop.
  exact (CoordLower _ _ (LengthPositive _ l)). exact H1.
  exact (CoordLower _ _ (LengthPositive _ l)). exact H0.
  destruct n.
  (* Lforall *)
  apply andb_prop in propprop. destruct propprop.
  apply Nat.eqb_eq in H. rewrite H.
  apply forallcase, IHprop. exact H0.
  exact (CoordLower _ _ (LengthPositive _ l)). exact H0.
  destruct n.
  (* Lexists *)
  apply andb_prop in propprop. destruct propprop.
  apply Nat.eqb_eq in H. rewrite H.
  apply existscase, IHprop. exact H0.
  exact (CoordLower _ _ (LengthPositive _ l)). exact H0.
  destruct n.
  (* Leq and PAle, base cases withtout IHprop *)
  2: discriminate propprop. clear IHprop.
  apply andb_prop in propprop. destruct propprop as [propprop proptrunc].
  apply andb_prop in propprop. destruct propprop as [propprop H].
  apply andb_prop in propprop. destruct propprop as [propprop H0].
  apply andb_prop in propprop. destruct propprop as [lenprop eqle].
  apply Nat.eqb_eq in lenprop.
  rewrite HeadTailDecompNat. 2: rewrite lenprop; apply le_n_S, le_0_n.
  rewrite (HeadTailDecompNat (TailNat prop)), CoordTailNat.
  rewrite (HeadTailDecompNat (TailNat (TailNat prop))), CoordTailNat, CoordTailNat.
  rewrite (HeadTailDecompNat (TailNat (TailNat (TailNat prop)))).
  rewrite CoordTailNat, CoordTailNat, CoordTailNat.
  apply Nat.eqb_eq in proptrunc. rewrite lenprop in proptrunc.
  simpl in proptrunc. rewrite proptrunc. clear proptrunc.
  rewrite headProp.
  destruct (CoordNat prop 1 =? 0) eqn:iseq. clear eqle.
  apply Nat.eqb_eq in iseq. rewrite iseq.
  apply eqcase; assumption. clear iseq. simpl in eqle.
  apply Nat.eqb_eq in eqle. rewrite eqle.
  apply lecase; assumption.
  rewrite LengthTailNat, LengthTailNat, LengthTailNat, lenprop.
  apply Nat.le_refl.
  rewrite LengthTailNat, LengthTailNat, lenprop.
  apply le_S, Nat.le_refl.
  rewrite LengthTailNat, lenprop.
  apply le_S, le_S, Nat.le_refl.
Qed.

Lemma PeanoPropositionIsLproposition : forall prop,
    IsPeanoProposition prop = true -> IsLproposition prop = true.
Proof.
  apply PeanoProposition_rect.
  - intros. rewrite IsLproposition_eq, PeanoTermIsLterm, PeanoTermIsLterm.
    reflexivity. exact uterm. exact tterm.
  - intros. unfold PAle.
    rewrite IsLproposition_rel2, PeanoTermIsLterm, PeanoTermIsLterm.
    reflexivity. exact uterm. exact tterm.
  - intros. rewrite IsLproposition_not. exact IHprop.
  - intros. rewrite IsLproposition_implies, IHg, IHh. reflexivity.
  - intros. rewrite IsLproposition_or, IHg, IHh. reflexivity.
  - intros. rewrite IsLproposition_and, IHg, IHh. reflexivity.
  - intros. rewrite IsLproposition_forall. exact IHprop.
  - intros. rewrite IsLproposition_exists. exact IHprop.
Qed.


(** PAnat, the injection of the meta-theoretic type nat as syntactical terms
    of Peano arithmetic. *)

Fixpoint PAnat (n : nat) : nat :=
  match n with
  | O => PAzero
  | S p => PAsucc (PAnat p)
  end.

Lemma IsLterm_PAnat : forall n, IsLterm (PAnat n) = true.
Proof.
  induction n.
  - simpl. apply IsLterm_const.
  - simpl. unfold PAsucc. rewrite IsLterm_op1. apply IHn.
Qed.

Lemma IsPeanoTerm_PAnat : forall n,
    IsPeanoTerm (PAnat n) = true.
Proof.
  induction n.
  - simpl. apply IsPeanoTerm_PAzero.
  - simpl. rewrite IsPeanoTerm_PAsucc. exact IHn.
Qed.

Lemma PAnat_closed : forall i v, VarOccursInTerm v (PAnat i) = false.
Proof.
  induction i.
  - intros. simpl. unfold PAzero. rewrite VarOccursInTerm_const. reflexivity.
  - intros. simpl. unfold PAsucc. rewrite VarOccursInTerm_op1. apply IHi.
Qed.

Lemma IsFreeForSubst_PAnat : forall n v f,
    IsLproposition f = true
    -> IsFreeForSubst (PAnat n) v f = true.
Proof.
  intros. apply IsFreeForSubst_closed.
  exact H. intros. apply PAnat_closed.
Qed.

Lemma MaxVarTerm_PAnat : forall n, MaxVarTerm (PAnat n) = 0.
Proof.
  induction n. simpl.
  unfold PAzero, Lconst.
  rewrite MaxVarTerm_op. simpl; rewrite LengthNilNat. reflexivity. 
  simpl. unfold PAsucc, Lop1.
  rewrite MaxVarTerm_op. simpl.
  rewrite LengthConsNat, LengthNilNat. simpl.
  unfold Lop. rewrite CoordConsTailNat, CoordConsTailNat.
  rewrite CoordConsHeadNat. exact IHn.
Qed.


Lemma PAinductionIsInduction : forall f : nat,
    IsLproposition f = true
    -> PAinduction (Limplies (Land (Subst PAzero 0 f)
                                  (Lforall 0 (Limplies f (Subst (PAsucc (Lvar 0)) 0 f))))
                            (Lforall 0 f)) = true.
Proof.
  intros f H.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  - rewrite IsLproposition_implies.
    apply andb_true_intro; split.
    rewrite IsLproposition_and.
    apply andb_true_intro; split.
    apply SubstIsLproposition. exact H.
    unfold PAzero. apply IsLterm_const.
    rewrite IsLproposition_forall.
    rewrite IsLproposition_implies.
    apply andb_true_intro; split. exact H.
    apply SubstIsLproposition. exact H.
    unfold PAsucc. rewrite IsLterm_op1. apply IsLterm_var.
    rewrite IsLproposition_forall. exact H.
  - apply LimpliesIsImplies.
  - rewrite CoordNat_implies_1. apply LandIsAnd.
  - rewrite CoordNat_implies_1, CoordNat_and_2.
    apply LforallIsForall.
  - rewrite CoordNat_implies_1, CoordNat_and_2.
    rewrite CoordNat_forall_2. apply LimpliesIsImplies.
  - rewrite CoordNat_implies_2. apply LforallIsForall.
  - rewrite CoordNat_implies_2, CoordNat_implies_1.
    rewrite CoordNat_and_2, CoordNat_forall_1, CoordNat_forall_1.
    reflexivity.
  - rewrite CoordNat_implies_2, CoordNat_implies_1.
    rewrite CoordNat_and_2, CoordNat_forall_2.
    rewrite CoordNat_implies_1, CoordNat_forall_2.
    apply PeanoNat.Nat.eqb_refl.
  - rewrite CoordNat_implies_2, CoordNat_implies_1.
    rewrite CoordNat_and_1, CoordNat_forall_1, CoordNat_forall_2.
    apply PeanoNat.Nat.eqb_refl.
  - rewrite CoordNat_implies_2, CoordNat_implies_1.
    rewrite CoordNat_and_2, CoordNat_forall_2.
    rewrite CoordNat_implies_2.
    rewrite CoordNat_forall_1, CoordNat_forall_2.
    apply PeanoNat.Nat.eqb_refl.
Qed.

Lemma Subst_PAle : forall t v n k,
    Subst t v (PAle n k) = PAle (SubstTerm t v n) (SubstTerm t v k).
Proof.
  intros. unfold PAle. rewrite Subst_rel2. reflexivity.
Qed.

Lemma SubstTerm_PAzero : forall t v, SubstTerm t v PAzero = PAzero.
Proof.
  intros. unfold PAzero. rewrite SubstTerm_const. reflexivity.
Qed.

Lemma SubstTerm_PAsucc : forall u v t,
    SubstTerm u v (PAsucc t) = PAsucc (SubstTerm u v t).
Proof.
  intros. apply SubstTerm_op1.
Qed.

Lemma SubstTerm_PAnat : forall i u v,
    SubstTerm u v (PAnat i) = PAnat i.
Proof.
  induction i.
  - intros. simpl. unfold PAzero. apply SubstTerm_const.
  - intros. simpl. rewrite SubstTerm_PAsucc, IHi. reflexivity.
Qed.

Lemma SubstTerm_PAplus : forall u v t w,
    SubstTerm u v (PAplus t w) = PAplus (SubstTerm u v t) (SubstTerm u v w).
Proof.
  intros. apply SubstTerm_op2.
Qed.

Lemma SubstTerm_PAmult : forall u v t w,
    SubstTerm u v (PAmult t w) = PAmult (SubstTerm u v t) (SubstTerm u v w).
Proof.
  intros. apply SubstTerm_op2.
Qed.

Lemma PAplus_zero : forall t,
    IsLterm t = true
    -> IsProved IsWeakHeytingAxiom (Leq (PAplus t PAzero) t).
Proof.
  intros.
  pose proof (LforallElim IsWeakHeytingAxiom
                          (Leq (PAplus (Lvar 0) PAzero) (Lvar 0))
                          0 t) as felim.
  rewrite Subst_eq, SubstTerm_PAplus in felim.
  rewrite SubstTerm_var in felim. simpl in felim.
  unfold PAzero in felim at 3. rewrite SubstTerm_const in felim.
  apply felim. 2: exact H.
  apply AxiomIsProved.
  apply Bool.orb_true_intro; left.
  apply Bool.orb_true_intro; left.
  apply Bool.orb_true_intro; left.
  apply Bool.orb_true_intro; left.
  apply Bool.orb_true_intro; right.
  unfold PAax4. apply Nat.eqb_refl.
  rewrite IsLproposition_forall. unfold Leq. rewrite IsLproposition_rel2.
  unfold PAplus, PAzero.
  rewrite IsLterm_op2, IsLterm_var, IsLterm_const. reflexivity.
  unfold Leq.
  rewrite IsFreeForSubst_rel2. reflexivity.
Qed.

Lemma PAmult_zero : forall t,
    IsLterm t = true
    -> IsProved IsWeakHeytingAxiom (Leq (PAmult t PAzero) PAzero).
Proof.
  intros.
  pose proof (LforallElim IsWeakHeytingAxiom
                          (Leq (PAmult (Lvar 0) PAzero) PAzero)
                          0 t) as felim.
  rewrite Subst_eq, SubstTerm_PAmult in felim.
  rewrite SubstTerm_var in felim. simpl in felim.
  rewrite SubstTerm_PAzero in felim.
  apply felim. 2: exact H.
  apply AxiomIsProved.
  apply Bool.orb_true_intro; left.
  apply Bool.orb_true_intro; left.
  apply Bool.orb_true_intro; right.
  unfold PAax6. apply Nat.eqb_refl.
  rewrite IsLproposition_forall, IsLproposition_eq.
  unfold PAmult, PAzero.
  rewrite IsLterm_op2, IsLterm_var, IsLterm_const. reflexivity.
  unfold Leq.
  rewrite IsFreeForSubst_rel2. reflexivity.
Qed.

Lemma IsProvedAx1
  : IsProved IsWeakHeytingAxiom
             (Lforall 0 (Lnot (Leq (PAsucc (Lvar 0)) PAzero))).
Proof.
  apply AxiomIsProved.
  do 7 (apply Bool.orb_true_intro; left).
  unfold PAax1. apply Nat.eqb_refl.
  rewrite IsLproposition_forall, IsLproposition_not, IsLproposition_eq.
  unfold PAzero, PAsucc. rewrite IsLterm_const.
  rewrite IsLterm_op1, IsLterm_var. reflexivity.
Qed.

Lemma IsProvedAx2 : forall t,
    IsLterm t = true
    -> VarOccursInTerm 1 t = false
    -> IsProved IsWeakHeytingAxiom
               (Lor (Leq t PAzero) (Lexists 1 (Leq t (PAsucc (Lvar 1))))).
Proof.
  assert (IsProved IsWeakHeytingAxiom (Lforall 0 (Lor (Leq (Lvar 0) PAzero)
                         (Lexists 1 (Leq (Lvar 0) (PAsucc (Lvar 1))))))).
  apply AxiomIsProved.
  do 6 (apply Bool.orb_true_intro; left).
  apply Bool.orb_true_intro; right.
  unfold PAax2. apply Nat.eqb_refl.
  rewrite IsLproposition_forall, IsLproposition_or, IsLproposition_eq.
  rewrite IsLproposition_exists, IsLproposition_eq, IsLterm_var.
  unfold PAsucc. rewrite IsLterm_op1, IsLterm_var.
  simpl. unfold PAzero. rewrite IsLterm_const.
  reflexivity.
  intros.
  apply (LforallElim _ _ 0 t) in H.
  rewrite Subst_or, Subst_eq, Subst_exists in H. simpl in H.
  rewrite Subst_eq, SubstTerm_var in H. simpl in H.
  rewrite SubstTerm_PAzero, SubstTerm_PAsucc, SubstTerm_var in H. simpl in H.
  exact H. exact H0. unfold Leq.
  rewrite IsFreeForSubst_or, IsFreeForSubst_rel2, IsFreeForSubst_exists.
  rewrite IsFreeForSubst_rel2, H1. simpl.
  rewrite Bool.orb_true_intro. reflexivity.
  right. reflexivity.
Qed.

Lemma IsProvedAx3 :
  IsProved IsWeakHeytingAxiom
           (Lforall 0 (Lforall 1 (Limplies (Leq (PAsucc (Lvar 0)) (PAsucc (Lvar 1)))
                                 (Leq (Lvar 0) (Lvar 1))))).
Proof.
  apply AxiomIsProved.
  apply Bool.orb_true_intro; left.
  apply Bool.orb_true_intro; left.
  apply Bool.orb_true_intro; left.
  apply Bool.orb_true_intro; left.
  apply Bool.orb_true_intro; left.
  apply Bool.orb_true_intro; right.
  unfold PAax3. apply Nat.eqb_refl.
  rewrite IsLproposition_forall, IsLproposition_forall.
  rewrite IsLproposition_implies, IsLproposition_eq.
  unfold PAsucc. rewrite IsLterm_op1, IsLterm_op1, IsLproposition_eq.
  rewrite IsLterm_var, IsLterm_var. reflexivity.
Qed.

Lemma IsProvedAx4 :
  IsProved IsWeakHeytingAxiom
           (Lforall 0 (Leq (PAplus (Lvar 0) PAzero) (Lvar 0))).
Proof.
  apply AxiomIsProved.
  apply Bool.orb_true_intro; left.
  apply Bool.orb_true_intro; left.
  apply Bool.orb_true_intro; left.
  apply Bool.orb_true_intro; left.
  apply Bool.orb_true_intro; right.
  unfold PAax4. apply Nat.eqb_refl.
  rewrite IsLproposition_forall, IsLproposition_eq.
  unfold PAplus, PAzero.
  rewrite IsLterm_op2, IsLterm_var, IsLterm_const.
  reflexivity.
Qed.

Lemma IsProvedAx5
  : IsProved IsWeakHeytingAxiom
             (Lforall 0 (Lforall 1 (Leq (PAplus (Lvar 0) (PAsucc (Lvar 1)))
                                        (PAsucc (PAplus (Lvar 0) (Lvar 1)))))).
Proof.
  apply AxiomIsProved.
  apply Bool.orb_true_intro; left.
  apply Bool.orb_true_intro; left.
  apply Bool.orb_true_intro; left.
  apply Bool.orb_true_intro; right.
  unfold PAax5. apply Nat.eqb_refl.
  rewrite IsLproposition_forall, IsLproposition_forall.
  unfold Leq.
  rewrite IsLproposition_rel2.
  unfold PAplus, PAsucc. rewrite IsLterm_op2, IsLterm_op1, IsLterm_op1.
  rewrite IsLterm_op2, IsLterm_var, IsLterm_var. reflexivity.
Qed.

Lemma IsProvedAx7 : IsProved IsWeakHeytingAxiom
  (Lforall 0 (Lforall 1 (Leq (PAmult (Lvar 0) (PAsucc (Lvar 1)))
                            (PAplus (PAmult (Lvar 0) (Lvar 1)) (Lvar 0))))).
Proof.
  apply AxiomIsProved.
  apply Bool.orb_true_intro; left.
  apply Bool.orb_true_intro; right.
  unfold PAax7. apply Nat.eqb_refl.
  rewrite IsLproposition_forall, IsLproposition_forall, IsLproposition_eq.
  unfold PAplus, PAsucc, PAmult. rewrite IsLterm_op2, IsLterm_op2, IsLterm_op1.
  rewrite IsLterm_op2, IsLterm_var, IsLterm_var. reflexivity.
Qed.

(* Specialization of PAle on arbitrary terms t and u. *)
Lemma IsProvedLe : forall t u,
    IsLterm t = true
    -> IsLterm u = true
    -> VarOccursInTerm 2 t = false
    -> VarOccursInTerm 2 u = false
    -> IsProved IsWeakHeytingAxiom
               (Lequiv (PAle t u)
                       (Lexists 2 (Leq (PAplus (Lvar 2) t) u))).
Proof.
  assert (IsProved IsWeakHeytingAxiom
  (Lforall 0 (Lforall 1 (Lequiv (PAle (Lvar 0) (Lvar 1))
                               (Lexists 2 (Leq (PAplus (Lvar 2) (Lvar 0)) (Lvar 1))))))).
  apply AxiomIsProved.
  apply Bool.orb_true_intro; right.
  unfold PAorder. apply Nat.eqb_refl.
  rewrite IsLproposition_forall, IsLproposition_forall.
  rewrite IsLproposition_equiv, IsLproposition_exists, IsLproposition_eq.
  unfold PAplus, PAsucc, PAmult, PAle.
  rewrite IsLterm_op2, IsLterm_var, IsLterm_var, IsLproposition_rel2.
  rewrite IsLterm_var, IsLterm_var.
  reflexivity.
  intros t u. intros.
  pose (S (S (S (Nat.max (MaxVarTerm u) (MaxVarTerm t))))) as m.
  assert (S m =? m = false).
  { apply Nat.eqb_neq. intro abs. apply (Nat.lt_irrefl m).
    rewrite <- abs at 2. apply Nat.le_refl. }
  apply (LforallElim _ _ 0 (Lvar m)) in H.
  rewrite Subst_forall in H. simpl in H.
  apply (LforallElim _ _ 1 (Lvar (S m))) in H.
  rewrite Subst_equiv, Subst_equiv, Subst_PAle, Subst_PAle in H.
  rewrite Subst_exists, Subst_exists in H. simpl in H.
  rewrite SubstTerm_var, SubstTerm_var in H. simpl in H.
  rewrite SubstTerm_var, Subst_eq, Subst_eq in H. simpl in H.
  rewrite SubstTerm_PAplus, SubstTerm_var, SubstTerm_var in H. simpl in H.
  rewrite SubstTerm_var, SubstTerm_var in H. simpl in H.
  rewrite SubstTerm_PAplus, SubstTerm_var, SubstTerm_var in H. simpl in H.
  rewrite SubstTerm_var in H. simpl in H.
  apply (LforallIntro _ _ m) in H.
  apply (LforallElim _ _ m t) in H.
  rewrite Subst_equiv, Subst_PAle, Subst_exists in H. simpl in H.
  rewrite SubstTerm_var, SubstTerm_var, Nat.eqb_refl, H4 in H.
  rewrite Subst_eq, SubstTerm_var, H4 in H.
  rewrite SubstTerm_PAplus, SubstTerm_var in H. simpl in H.
  rewrite SubstTerm_var, Nat.eqb_refl in H. simpl in H.
  apply (LforallIntro _ _ (S m)) in H.
  apply (LforallElim _ _ (S m) u) in H.
  rewrite Subst_equiv, Subst_PAle, Subst_exists in H. simpl in H.
  rewrite SubstTerm_var, Nat.eqb_refl in H.
  rewrite Subst_eq, SubstTerm_var, Nat.eqb_refl in H.
  rewrite SubstTerm_PAplus, SubstTerm_var in H. simpl in H.
  rewrite SubstTerm_nosubst in H. exact H.
  apply MaxVarTermDoesNotOccur.
  apply le_n_S, le_S, le_S, le_S, Nat.le_max_r.
  exact H0. exact H1. unfold PAle, Leq.
  rewrite IsFreeForSubst_equiv, IsFreeForSubst_rel2, IsFreeForSubst_exists.
  rewrite IsFreeForSubst_rel2, H3.
  simpl (true && negb false)%bool. rewrite Bool.orb_true_r. reflexivity.
  exact H0. unfold PAle, Leq.
  rewrite IsFreeForSubst_equiv, IsFreeForSubst_rel2, IsFreeForSubst_exists.
  rewrite IsFreeForSubst_rel2, H2.
  simpl (true && negb false)%bool. rewrite Bool.orb_true_r. reflexivity.
  apply IsLterm_var.
  rewrite Subst_equiv, IsFreeForSubst_equiv, Subst_PAle, Subst_exists.
  simpl. unfold PAle.
  rewrite IsFreeForSubst_rel2, IsFreeForSubst_exists, Subst_eq.
  unfold Leq. rewrite IsFreeForSubst_rel2, VarOccursInTerm_var.
  simpl. rewrite Bool.orb_true_r. reflexivity.
  apply IsLterm_var.
  rewrite IsFreeForSubst_forall.
  apply Bool.orb_true_intro. right.
  rewrite IsFreeForSubst_equiv.
  unfold PAle. rewrite IsFreeForSubst_rel2, IsFreeForSubst_exists.
  unfold Leq. rewrite IsFreeForSubst_rel2. simpl.
  rewrite VarOccursInTerm_var, VarOccursInTerm_var.
  simpl (negb (2 =? m)). rewrite Bool.orb_true_r. reflexivity.
Qed.

Lemma LeqElimSubstVarPAnat : forall IsAxiom v k prop,
    IsLproposition prop = true
    -> IsProved IsAxiom (Subst (PAnat k) v prop)
    -> IsProved IsAxiom (Limplies (Leq (Lvar v) (PAnat k)) prop).
Proof.
  intros.
  apply LeqElimSubstVar. exact H.
  apply IsLterm_PAnat. apply IsFreeForSubst_PAnat.
  exact H. exact H0.
Qed.

(* Closed terms are proved equal to closed terms with the successor symbol only. *)
Lemma PAplus_normalize : forall i j,
    IsProved IsWeakHeytingAxiom (Leq (PAplus (PAnat i) (PAnat j)) (PAnat (i + j))).
Proof.
  induction j.
  rewrite Nat.add_0_r. apply PAplus_zero.
  apply IsLterm_PAnat.
  simpl. rewrite Nat.add_succ_r. simpl.
  apply (LeqTrans _ _ (PAsucc (PAplus (PAnat i) (PAnat j)))).
  2: apply LeqElim_op1, IHj.
  pose proof (LforallElim IsWeakHeytingAxiom
                          (Leq (PAplus (PAnat i) (PAsucc (Lvar 1)))
                               (PAsucc (PAplus (PAnat i) (Lvar 1))))
                          1 (PAnat j)) as felim.
  rewrite Subst_eq, SubstTerm_PAsucc, SubstTerm_PAplus in felim.
  rewrite SubstTerm_PAplus, SubstTerm_PAnat in felim.
  rewrite SubstTerm_PAsucc, SubstTerm_var in felim.
  simpl in felim. apply felim; clear felim.
  2: apply IsLterm_PAnat.
  2: apply IsFreeForSubst_rel2.
  clear IHj j.
  pose proof (LforallElim IsWeakHeytingAxiom
                          (Lforall 1 (Leq (PAplus (Lvar 0) (PAsucc (Lvar 1)))
                                          (PAsucc (PAplus (Lvar 0) (Lvar 1)))))
                          0 (PAnat i) IsProvedAx5
                          (IsLterm_PAnat _)) as felim.
  rewrite Subst_forall, Subst_eq in felim; simpl in felim.
  rewrite SubstTerm_PAsucc, SubstTerm_PAplus in felim.
  rewrite SubstTerm_PAsucc, SubstTerm_var, SubstTerm_var in felim.
  simpl in felim.
  rewrite SubstTerm_PAplus, SubstTerm_var, SubstTerm_var in felim.
  simpl in felim.
  apply felim.
  rewrite IsFreeForSubst_forall.
  unfold Leq.
  rewrite IsFreeForSubst_rel2.
  rewrite VarOccursFreeInFormula_rel2.
  unfold PAplus, PAsucc.
  rewrite VarOccursInTerm_op2, VarOccursInTerm_op1.
  rewrite VarOccursInTerm_op1, VarOccursInTerm_op2.
  rewrite VarOccursInTerm_var, VarOccursInTerm_var.
  rewrite PAnat_closed. reflexivity.
Qed.

(* Closed terms are proved equal to closed terms with the successor symbol only. *)
Lemma PAmult_normalize : forall i j,
    IsProved IsWeakHeytingAxiom (Leq (PAmult (PAnat i) (PAnat j)) (PAnat (i * j))).
Proof.
  induction j.
  rewrite Nat.mul_0_r. apply PAmult_zero.
  apply IsLterm_PAnat.
  apply (LeqTrans _ _ (PAplus (PAmult (PAnat i) (PAnat j)) (PAnat i))).
  pose proof (LforallElim IsWeakHeytingAxiom
                          (Lforall 1 (Leq (PAmult (Lvar 0) (PAsucc (Lvar 1)))
                            (PAplus (PAmult (Lvar 0) (Lvar 1)) (Lvar 0))))
                          0 (PAnat i)) as felim.
  rewrite Subst_forall in felim. simpl in felim.
  apply (LforallElim IsWeakHeytingAxiom _ 1 (PAnat j)) in felim.
  rewrite Subst_eq, Subst_eq in felim.
  rewrite SubstTerm_PAmult, SubstTerm_PAplus in felim.
  rewrite SubstTerm_PAmult, SubstTerm_var in felim. simpl in felim.
  rewrite SubstTerm_PAmult, SubstTerm_var in felim. simpl in felim.
  rewrite SubstTerm_PAplus, SubstTerm_var in felim. simpl in felim.
  rewrite SubstTerm_PAsucc, SubstTerm_var in felim. simpl in felim.
  rewrite SubstTerm_PAsucc, SubstTerm_var in felim. simpl in felim.
  rewrite SubstTerm_PAmult, SubstTerm_var in felim. simpl in felim.
  rewrite SubstTerm_PAnat in felim. exact felim. clear felim.
  exact IsProvedAx7.
  apply IsLterm_PAnat.
  apply IsFreeForSubst_PAnat.
  rewrite IsLproposition_forall, IsLproposition_eq.
  unfold PAmult, PAplus, PAsucc.
  rewrite IsLterm_op2, IsLterm_op2, IsLterm_op2, IsLterm_op1.
  rewrite IsLterm_var, IsLterm_var. reflexivity.
  apply IsLterm_PAnat.
  apply IsFreeForSubst_PAnat.
  apply SubstIsLproposition.
  rewrite IsLproposition_eq.
  unfold PAmult, PAplus, PAsucc.
  rewrite IsLterm_op2, IsLterm_op2, IsLterm_op2, IsLterm_op1.
  rewrite IsLterm_var, IsLterm_var. reflexivity.
  apply IsLterm_PAnat.
  apply (LeqTrans _ _ (PAplus (PAnat (i*j)) (PAnat i))).
  2: rewrite Nat.mul_succ_r; apply PAplus_normalize.
  apply LeqElim_op2.
  exact IHj. apply LeqRefl, IsLterm_PAnat.
Qed.

Lemma PAle_normalize : forall i j,
    i <= j -> IsProved IsWeakHeytingAxiom (PAle (PAnat i) (PAnat j)).
Proof.
  intros i j ilej.
  pose proof (IsProvedLe (PAnat i) (PAnat j)) as H.
  apply LandElim2 in H.
  apply (LimpliesElim _ _ _ H). clear H.
  apply (LexistsIntro _ _ _ (PAnat (j-i))).
  apply IsLterm_PAnat.
  unfold PAplus. rewrite IsLproposition_eq, IsLterm_op2, IsLterm_var.
  rewrite IsLterm_PAnat, IsLterm_PAnat. reflexivity.
  apply IsFreeForSubst_PAnat.
  unfold PAplus.
  rewrite IsLproposition_eq, IsLterm_op2, IsLterm_var, IsLterm_PAnat, IsLterm_PAnat.
  reflexivity.
  rewrite Subst_eq, SubstTerm_PAplus.
  rewrite SubstTerm_var, SubstTerm_PAnat, SubstTerm_PAnat. simpl.
  apply (LeqTrans _ _ (PAnat ((j-i) + i))).
  apply PAplus_normalize.
  rewrite Nat.add_comm, <- Minus.le_plus_minus. apply LeqRefl.
  apply IsLterm_PAnat. exact ilej.
  apply IsLterm_PAnat. apply IsLterm_PAnat.
  apply PAnat_closed. apply PAnat_closed.
Qed.

Lemma PAle_zero : forall t,
    IsLterm t = true
    -> IsProved IsWeakHeytingAxiom
               (Limplies (PAle t PAzero) (Leq t PAzero)).
Proof.
  assert (IsProved IsWeakHeytingAxiom
           (Limplies (PAle (Lvar 3) PAzero) (Leq (Lvar 3) PAzero))).
  pose proof (IsProvedLe (Lvar 3) PAzero (IsLterm_var 3) (IsLterm_PAnat 0)) as H.
  apply LandElim1 in H.
  apply (LimpliesTrans _ _ _ _ H). clear H.
  apply LexistsElim_impl.
  unfold Leq. rewrite VarOccursFreeInFormula_rel2.
  rewrite VarOccursInTerm_var. apply (PAnat_closed 0).
  apply LforallIntro.
  apply (LimpliesElim _ (Lor (Leq (Lvar 3) PAzero) (Lexists 1 (Leq (Lvar 3) (PAsucc (Lvar 1)))))).
  2: apply (IsProvedAx2 (Lvar 3) (IsLterm_var 3)).
  apply LorElim.
  apply PullHypothesis. apply LandElim1_impl.
  rewrite IsLproposition_eq, IsLterm_var.
  apply IsLterm_const.
  unfold PAplus.
  rewrite IsLproposition_eq, IsLterm_op2, IsLterm_var, IsLterm_var. 
  apply IsLterm_const.
  apply LexistsElim_impl.
  unfold Leq, PAplus, PAzero.
  rewrite VarOccursFreeInFormula_implies, VarOccursFreeInFormula_rel2.
  rewrite VarOccursInTerm_op2, VarOccursInTerm_var, VarOccursInTerm_var.
  rewrite VarOccursInTerm_const, VarOccursFreeInFormula_rel2.
  rewrite VarOccursInTerm_var. apply VarOccursInTerm_const.
  apply LforallIntro.
  apply LeqElimSubstVar.
  rewrite IsLproposition_implies, IsLproposition_eq, IsLproposition_eq.
  unfold PAplus, PAzero. rewrite IsLterm_op2, IsLterm_var, IsLterm_var.
  rewrite IsLterm_const. reflexivity.
  unfold PAsucc. rewrite IsLterm_op1. apply IsLterm_var.
  unfold Leq.
  rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2.
  apply IsFreeForSubst_rel2.
  rewrite Subst_implies, Subst_eq, SubstTerm_PAplus.
  rewrite SubstTerm_var, SubstTerm_var. simpl.
  rewrite SubstTerm_PAzero.
  pose proof IsProvedAx5 as asr.
  apply (LforallElim _ _ 0 (Lvar 2)) in asr.
  2: apply IsLterm_var. rewrite Subst_forall in asr; simpl in asr.
  apply LforallElimIdemVar in asr.
  rewrite Subst_eq, SubstTerm_PAplus in asr.
  rewrite SubstTerm_var, SubstTerm_PAsucc in asr. simpl in asr.
  rewrite SubstTerm_var, SubstTerm_PAsucc, SubstTerm_PAplus in asr. simpl in asr.
  rewrite SubstTerm_var, SubstTerm_var in asr. simpl in asr.
  apply (LimpliesTrans _ _ (Leq (PAsucc (PAplus (Lvar 2) (Lvar 1))) PAzero)).
  pose proof (LeqElim_rel2 IsWeakHeytingAxiom 0 _ _
                           PAzero PAzero asr (LeqRefl _ _ (IsLterm_const _))).
  apply LandElim1 in H.
  exact H. clear asr.
  pose proof IsProvedAx1 as H0.
  apply (LforallElim _ _ 0 (PAplus (Lvar 2) (Lvar 1))) in H0.
  rewrite Subst_not, Subst_eq, SubstTerm_PAsucc in H0.
  rewrite SubstTerm_PAzero, SubstTerm_var in H0. simpl in H0.
  pose proof FalseElim_impl.
  apply (FalseElim_impl _ _ _ H0).
  apply SubstIsLproposition.
  unfold PAzero. rewrite IsLproposition_eq, IsLterm_var, IsLterm_const.
  reflexivity. unfold PAplus.
  unfold PAsucc. rewrite IsLterm_op1. apply IsLterm_var.
  unfold PAplus.
  rewrite IsLterm_op2, IsLterm_var, IsLterm_var. reflexivity.
  unfold Leq. rewrite IsFreeForSubst_not, IsFreeForSubst_rel2. reflexivity.
  rewrite IsFreeForSubst_forall. apply Bool.orb_true_intro. right.
  unfold Leq. rewrite IsFreeForSubst_rel2, VarOccursInTerm_var.
  reflexivity. apply VarOccursInTerm_var.
  apply VarOccursInTerm_var. apply (PAnat_closed 0).
  intros t H0.
  apply (LforallIntro _ _ 3) in H.
  apply (LforallElim _ _ _ t) in H.
  rewrite Subst_implies, Subst_PAle, SubstTerm_var in H. simpl in H.
  rewrite Subst_eq, SubstTerm_PAzero, SubstTerm_var in H. simpl in H.
  exact H. exact H0.
  unfold Leq, PAle.
  rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2, IsFreeForSubst_rel2.
  reflexivity.
Qed.

Lemma PAle_0_t : forall t,
    IsLterm t = true
    -> IsProved IsWeakHeytingAxiom (PAle PAzero t).
Proof.
  assert (IsProved IsWeakHeytingAxiom (PAle PAzero (Lvar 3))).
  pose proof (IsProvedLe PAzero (Lvar 3) (IsLterm_PAnat 0) (IsLterm_var _))
    as leeq.
  apply LandElim2 in leeq.
  apply (LimpliesElim _ _ _ leeq). clear leeq.
  apply (LexistsIntro _ _ _ (Lvar 3)).
  apply IsLterm_var.
  unfold PAplus, PAzero.
  rewrite IsLproposition_eq, IsLterm_op2, IsLterm_var, IsLterm_const.
  apply IsLterm_var.
  apply IsFreeForSubst_rel2.
  rewrite Subst_eq, SubstTerm_PAplus, SubstTerm_PAzero.
  rewrite SubstTerm_var, SubstTerm_var. simpl.
  pose proof IsProvedAx4.
  apply (LforallElim _ _ _ (Lvar 3)) in H.
  rewrite Subst_eq, SubstTerm_PAplus, SubstTerm_var in H; simpl in H.
  rewrite SubstTerm_PAzero in H. exact H.
  apply IsLterm_var. apply IsFreeForSubst_rel2.
  apply (PAnat_closed 0). apply VarOccursInTerm_var.
  intros t H0.
  apply (eq_ind (Subst t 3 (PAle PAzero (Lvar 3)))).
  apply LforallElim. apply LforallIntro. exact H. exact H0.
  apply IsFreeForSubst_rel2.
  rewrite Subst_PAle, SubstTerm_PAzero, SubstTerm_var. reflexivity.
Qed.

Lemma PAle_incr : forall t,
    IsLterm t = true ->
    IsProved IsWeakHeytingAxiom
             (Limplies (PAle (Lvar 0) t)
                       (PAle (PAsucc (Lvar 0)) (PAsucc t))).
Proof.
  assert (IsProved IsWeakHeytingAxiom
             (Limplies (PAle (Lvar 0) (Lvar 1))
                       (PAle (PAsucc (Lvar 0)) (PAsucc (Lvar 1))))).
  intros.
  pose proof (IsProvedLe (Lvar 0) (Lvar 1) (IsLterm_var 0) (IsLterm_var 1)).
  apply LandElim1 in H.
  2: apply VarOccursInTerm_var.
  2: apply VarOccursInTerm_var.
  apply (LimpliesTrans _ _ _ _ H). clear H.
  apply LexistsElim_impl.
  unfold PAle, PAsucc.
  rewrite VarOccursFreeInFormula_rel2, VarOccursInTerm_op1, VarOccursInTerm_var.
  rewrite VarOccursInTerm_op1, VarOccursInTerm_var. reflexivity.
  apply LforallIntro.
  apply (LimpliesTrans _ _ (Leq (Lvar 1) (PAplus (Lvar 2) (Lvar 0)))).
  apply LeqSym_impl.
  unfold PAplus. rewrite IsLterm_op2, IsLterm_var, IsLterm_var. reflexivity.
  apply IsLterm_var.
  apply LeqElimSubstVar.
  unfold PAle. rewrite IsLproposition_rel2.
  unfold PAsucc. rewrite IsLterm_op1, IsLterm_op1, IsLterm_var, IsLterm_var.
  reflexivity.
  unfold PAplus. rewrite IsLterm_op2, IsLterm_var, IsLterm_var.
  reflexivity.
  apply IsFreeForSubst_rel2.
  rewrite Subst_PAle, SubstTerm_PAsucc, SubstTerm_PAsucc.
  rewrite SubstTerm_var, SubstTerm_var. simpl.
  apply (eq_ind (Subst (Lvar 2) 3 (PAle (PAsucc (Lvar 0)) (PAsucc (PAplus (Lvar 3) (Lvar 0)))))).
  apply LforallElim. apply LforallIntro.
  pose proof (IsProvedLe (PAsucc (Lvar 0)) (PAsucc (PAplus (Lvar 3) (Lvar 0)))).
  apply LandElim2 in H.
  apply (LimpliesElim _ _ _ H). clear H.
  apply (LexistsIntro _ _ _ (Lvar 3)).
  apply IsLterm_var.
  rewrite IsLproposition_eq.
  unfold PAplus, PAsucc.
  reduce_islproposition. reflexivity.
  apply IsFreeForSubst_rel2.
  rewrite Subst_eq.
  rewrite SubstTerm_PAsucc, SubstTerm_PAplus, SubstTerm_var. simpl.
  rewrite SubstTerm_PAsucc, SubstTerm_var, SubstTerm_PAplus. simpl.
  rewrite SubstTerm_var, SubstTerm_var. simpl.
  pose proof (IsProvedAx5).
  apply (LforallElim _ _ _ (Lvar 3)) in H.
  rewrite Subst_forall in H; simpl in H.
  apply (LforallElim _ _ _ (Lvar 0)) in H.
  rewrite Subst_eq, Subst_eq, SubstTerm_PAplus, SubstTerm_PAplus in H.
  rewrite SubstTerm_var in H. simpl in H.
  rewrite SubstTerm_var in H. simpl in H.
  rewrite SubstTerm_PAsucc, SubstTerm_PAsucc in H.
  rewrite SubstTerm_var in H. simpl in H.
  rewrite SubstTerm_var in H. simpl in H.
  rewrite SubstTerm_PAsucc, SubstTerm_PAsucc, SubstTerm_PAplus, SubstTerm_PAplus in H.
  rewrite SubstTerm_var in H. simpl in H.
  rewrite SubstTerm_var in H. simpl in H.
  rewrite SubstTerm_var in H. simpl in H.
  rewrite SubstTerm_var in H. simpl in H.
  exact H. apply IsLterm_var.
  rewrite Subst_eq. apply IsFreeForSubst_rel2.
  apply IsLterm_var. unfold Leq, PAplus, PAsucc.
  rewrite IsFreeForSubst_forall, IsFreeForSubst_rel2. simpl.
  rewrite VarOccursFreeInFormula_rel2, VarOccursInTerm_op2.
  rewrite VarOccursInTerm_op1, VarOccursInTerm_op1, VarOccursInTerm_op2.
  rewrite VarOccursInTerm_var, VarOccursInTerm_var, VarOccursInTerm_var.
  reflexivity.
  unfold PAsucc. rewrite IsLterm_op1. apply IsLterm_var.
  unfold PAsucc, PAplus. rewrite IsLterm_op1, IsLterm_op2.
  rewrite IsLterm_var, IsLterm_var. reflexivity.
  unfold PAsucc. rewrite VarOccursInTerm_op1. apply VarOccursInTerm_var.
  unfold PAsucc. rewrite VarOccursInTerm_op1.
  unfold PAplus. rewrite VarOccursInTerm_op2.
  rewrite VarOccursInTerm_var, VarOccursInTerm_var. reflexivity.
  apply IsLterm_var. apply IsFreeForSubst_rel2.
  unfold PAle, PAsucc, PAplus.
  reduce_subst. reflexivity.
  intros t H0. apply (LforallIntro _ _ 1) in H.
  apply (LforallElim _ _ _ t) in H.
  rewrite Subst_implies, Subst_PAle, SubstTerm_var, SubstTerm_var in H.
  simpl in H. rewrite Subst_PAle, SubstTerm_PAsucc, SubstTerm_PAsucc in H.
  rewrite SubstTerm_var, SubstTerm_var in H. simpl in H.
  exact H. exact H0. unfold PAle.
  rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2, IsFreeForSubst_rel2.
  reflexivity.
Qed.

Lemma PAle_decr : forall t,
    IsLterm t = true ->
    IsProved IsWeakHeytingAxiom
             (Limplies (PAle (PAsucc (Lvar 0)) (PAsucc t))
                       (PAle (Lvar 0) t)).
Proof.
  assert (IsProved IsWeakHeytingAxiom
                   (Limplies (PAle (PAsucc (Lvar 0)) (PAsucc (Lvar 1)))
                             (PAle (Lvar 0) (Lvar 1)))).
  intros.
  pose proof (IsProvedLe (PAsucc (Lvar 0)) (PAsucc (Lvar 1))).
  apply LandElim1 in H.
  apply (LimpliesTrans _ _ _ _ H). clear H.
  apply LexistsElim_impl.
  unfold PAle, PAsucc.
  rewrite VarOccursFreeInFormula_rel2, VarOccursInTerm_var, VarOccursInTerm_var.
  reflexivity.
  apply LforallIntro.
  apply (LimpliesTrans _ _ (Leq (PAsucc (PAplus (Lvar 2) (Lvar 0))) (PAsucc (Lvar 1)))).
  pose proof IsProvedAx5 as H.
  apply (LforallElim _ _ _ (Lvar 2)) in H.
  rewrite Subst_forall in H; simpl in H.
  apply (LforallElim _ _ _ (Lvar 0)) in H.
  rewrite Subst_eq, SubstTerm_PAplus, SubstTerm_var in H. simpl in H.
  rewrite SubstTerm_PAsucc, SubstTerm_var in H. simpl in H.
  rewrite SubstTerm_PAsucc, SubstTerm_PAplus in H.
  rewrite SubstTerm_var, SubstTerm_var in H. simpl in H.
  rewrite Subst_eq, SubstTerm_PAplus, SubstTerm_var in H. simpl in H.
  rewrite SubstTerm_PAsucc, SubstTerm_var in H. simpl in H.
  rewrite SubstTerm_PAsucc, SubstTerm_PAplus in H.
  rewrite SubstTerm_var, SubstTerm_var in H. simpl in H.
  assert (IsLterm (PAsucc (Lvar 1)) = true).
  unfold PAsucc. rewrite IsLterm_op1. apply IsLterm_var.
  pose proof (LeqElim_rel2 IsWeakHeytingAxiom 0 _ _ _ _ H (LeqRefl _ _ H0)).
  apply LandElim1 in H1. exact H1.
  apply IsLterm_var.
  rewrite Subst_eq. apply IsFreeForSubst_rel2.
  apply IsLterm_var. unfold Leq.
  rewrite IsFreeForSubst_forall, IsFreeForSubst_rel2. simpl.
  rewrite VarOccursInTerm_var. simpl. apply Bool.orb_true_r.
  apply (LimpliesTrans _ _ (Leq (PAplus (Lvar 2) (Lvar 0)) (Lvar 1))).
  pose proof IsProvedAx3.
  apply (LforallElim _ _ _ (PAplus (Lvar 2) (Lvar 0))) in H.
  rewrite Subst_forall in H. simpl in H.
  apply LforallElimIdemVar in H.
  rewrite Subst_implies, Subst_eq, SubstTerm_PAsucc, SubstTerm_var in H.
  simpl in H. rewrite SubstTerm_PAsucc, SubstTerm_var in H. simpl in H.
  rewrite Subst_eq, SubstTerm_var, SubstTerm_var in H. simpl in H.
  exact H.
  unfold PAplus. rewrite IsLterm_op2, IsLterm_var, IsLterm_var. reflexivity.
  rewrite IsFreeForSubst_forall. simpl. unfold Leq.
  rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2, IsFreeForSubst_rel2. simpl.
  unfold PAplus. rewrite VarOccursInTerm_op2, VarOccursInTerm_var, VarOccursInTerm_var.
  simpl. apply Bool.orb_true_r.
  pose proof (IsProvedLe (Lvar 0) (Lvar 1) (IsLterm_var 0) (IsLterm_var 1)).
  apply LandElim2 in H.
  refine (LimpliesTrans _ _ _ _ _ H). clear H.
  assert (IsLproposition (Leq (PAplus (Lvar 2) (Lvar 0)) (Lvar 1)) = true).
  { unfold Leq, PAplus. reduce_islproposition. reflexivity. }
  rewrite <- (SubstIdemVar _ H 2) at 1.
  apply LexistsIntro_impl. apply IsLterm_var. exact H.
  apply IsFreeForSubstIdemVar. exact H.
  apply VarOccursInTerm_var.
  apply VarOccursInTerm_var.
  unfold PAsucc. rewrite IsLterm_op1. apply IsLterm_var.
  unfold PAsucc. rewrite IsLterm_op1. apply IsLterm_var.
  unfold PAsucc. rewrite VarOccursInTerm_op1. apply VarOccursInTerm_var.
  unfold PAsucc. rewrite VarOccursInTerm_op1. apply VarOccursInTerm_var.
  intros t H0. apply (LforallIntro _ _ 1) in H.
  apply (LforallElim _ _ _ t) in H.
  rewrite Subst_implies, Subst_PAle, SubstTerm_PAsucc in H.
  rewrite Subst_PAle, SubstTerm_var, SubstTerm_var in H. simpl in H.
  rewrite SubstTerm_PAsucc, SubstTerm_var in H. simpl in H.
  exact H. exact H0. unfold PAle.
  rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2, IsFreeForSubst_rel2.
  reflexivity.
Qed.

Lemma PAnat_le_lt_total : forall i t,
    IsLterm t = true
    -> IsProved IsWeakHeytingAxiom
               (Lor (PAle (PAnat i) t) (PAle (PAsucc t) (PAnat i))).
Proof.
  assert (forall i, IsProved IsWeakHeytingAxiom
                        (Lor (PAle (PAnat i) (Lvar 3))
                             (PAle (PAsucc (Lvar 3)) (PAnat i)))).
  induction i.
  - apply LorIntro1.
    unfold PAle, PAsucc. rewrite IsLproposition_rel2, IsLterm_op1, IsLterm_var.
    apply IsLterm_const.
    apply PAle_0_t. apply IsLterm_var.
  - (* If X3 = 0 then it is lower, otherwise apply IHi on its predecessor *)
    apply (LimpliesElim _ (Lor (Leq (Lvar 3) PAzero)
                               (Lexists 1 (Leq (Lvar 3) (PAsucc (Lvar 1)))))).
    2: apply (IsProvedAx2 (Lvar 3) (IsLterm_var 3)).
    2: apply VarOccursInTerm_var.
    apply LorElim.
    + clear IHi.
      apply (LeqElimSubstVarPAnat _ _ 0).
      unfold PAle, PAsucc.
      rewrite IsLproposition_or, IsLproposition_rel2, IsLproposition_rel2.
      rewrite IsLterm_PAnat, IsLterm_var, IsLterm_op1, IsLterm_var. reflexivity.
      rewrite Subst_or, Subst_PAle, Subst_PAle, SubstTerm_PAnat.
      rewrite SubstTerm_var, SubstTerm_PAsucc, SubstTerm_var. simpl.
      apply LorIntro2.
      unfold PAle, PAsucc.
      rewrite IsLproposition_rel2, IsLterm_op1, IsLterm_PAnat.
      apply IsLterm_const.
      pose proof (PAle_incr (PAnat i) (IsLterm_PAnat i)) as H.
      apply (LforallIntro _ _ 0) in H.
      apply (LforallElim _ _ _ PAzero) in H.
      rewrite Subst_implies, Subst_PAle, SubstTerm_var, SubstTerm_PAnat in H.
      simpl in H. rewrite Subst_PAle, SubstTerm_PAsucc in H.
      rewrite SubstTerm_var, SubstTerm_PAsucc, SubstTerm_PAnat in H. simpl in H.
      apply (LimpliesElim _ _ _ H). clear H.
      apply PAle_0_t. apply IsLterm_PAnat.
      apply IsLterm_const. unfold PAle.
      rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2, IsFreeForSubst_rel2.
      reflexivity.
    + apply LexistsElim_impl. unfold PAle.
      rewrite VarOccursFreeInFormula_or, VarOccursFreeInFormula_rel2.
      rewrite VarOccursFreeInFormula_rel2, PAnat_closed, VarOccursInTerm_var.
      unfold PAsucc. rewrite VarOccursInTerm_op1, VarOccursInTerm_var.
      reflexivity.
      apply LforallIntro.
      apply LeqElimSubstVar.
      unfold PAle, PAsucc. reduce_islproposition.
      rewrite IsLterm_PAnat. reflexivity.
      unfold PAsucc. rewrite IsLterm_op1. apply IsLterm_var.
      unfold PAle.
      rewrite IsFreeForSubst_or, IsFreeForSubst_rel2, IsFreeForSubst_rel2.
      reflexivity.
      rewrite Subst_or, Subst_PAle, Subst_PAle, SubstTerm_PAnat.
      rewrite SubstTerm_var, SubstTerm_PAsucc, SubstTerm_var. simpl.
      apply (LforallIntro _ _ 3) in IHi.
      apply (LforallElim _ _ _ (Lvar 1)) in IHi.
      rewrite Subst_or, Subst_PAle, Subst_PAle, SubstTerm_PAnat in IHi.
      rewrite SubstTerm_var, SubstTerm_PAsucc, SubstTerm_var in IHi. simpl in IHi.
      apply (LimpliesElim _ (Lor (PAle (PAnat i) (Lvar 1))
                                 (PAle (PAsucc (Lvar 1)) (PAnat i)))).
      2: exact IHi. clear IHi.
      apply LorElim.
      * apply (LimpliesTrans _ _ (PAle (PAsucc (PAnat i)) (PAsucc (Lvar 1)))).
        pose proof (PAle_incr (Lvar 1) (IsLterm_var 1)).
        apply (LforallIntro _ _ 0) in H.
        apply (LforallElim _ _ _ (PAnat i)) in H.
        rewrite Subst_implies, Subst_PAle, SubstTerm_var, SubstTerm_var in H.
        rewrite Subst_PAle, SubstTerm_PAsucc, SubstTerm_var in H.
        simpl in H. rewrite SubstTerm_PAsucc, SubstTerm_var in H.
        simpl in H. exact H.
        apply IsLterm_PAnat.
        apply IsFreeForSubst_PAnat.
        unfold PAle, PAsucc.
        reduce_islproposition. reflexivity.
        apply LorIntro1_impl.
        unfold PAle, PAsucc.
        reduce_islproposition. rewrite IsLterm_PAnat. reflexivity.
        unfold PAle, PAsucc.
        reduce_islproposition. rewrite IsLterm_PAnat. reflexivity.
      * apply (LimpliesTrans _ _ (PAle (PAsucc (PAsucc (Lvar 1))) (PAsucc (PAnat i)))).
        pose proof (PAle_incr (PAnat i) (IsLterm_PAnat i)).
        apply (LforallIntro _ _ 0) in H.
        apply (LforallElim _ _ _ (PAsucc (Lvar 1))) in H.
        rewrite Subst_implies, Subst_PAle, SubstTerm_var in H. simpl in H.
        rewrite Subst_PAle, SubstTerm_PAsucc, SubstTerm_var in H.
        simpl in H. rewrite SubstTerm_PAnat, SubstTerm_PAsucc in H.
        rewrite SubstTerm_PAnat in H. exact H.
        unfold PAsucc. rewrite IsLterm_op1. apply IsLterm_var.
        unfold PAle.
        rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2, IsFreeForSubst_rel2.
        reflexivity.
        apply LorIntro2_impl.
        unfold PAle, PAsucc.
        reduce_islproposition. rewrite IsLterm_PAnat. reflexivity.
        unfold PAle, PAsucc.
        reduce_islproposition. rewrite IsLterm_PAnat. reflexivity.
      * apply IsLterm_var.
      * unfold PAle.
        rewrite IsFreeForSubst_or, IsFreeForSubst_rel2, IsFreeForSubst_rel2.
        reflexivity.
  - intros i t tterm.
    apply (eq_ind (Subst t 3 (Lor (PAle (PAnat i) (Lvar 3))
                                  (PAle (PAsucc (Lvar 3)) (PAnat i))))).
    apply LforallElim.
    apply LforallIntro. exact (H i). exact tterm.
    unfold PAle.
    rewrite IsFreeForSubst_or, IsFreeForSubst_rel2, IsFreeForSubst_rel2.
    reflexivity.
    unfold PAle, PAsucc. reduce_subst.
    rewrite Nat.eqb_refl, SubstTerm_PAnat. reflexivity.
Qed.

(* Piece of the trichotomy *)
Lemma PAle_succ_r_aux : forall i,
    IsProved IsWeakHeytingAxiom
             (Limplies (PAle (Lvar 0) (PAnat i))
                       (Lor (PAle (Lvar 0) (PAnat (pred i)))
                            (Leq (Lvar 0) (PAnat i)))).
Proof.
  induction i.
  - simpl.
    apply (LimpliesTrans _ _ _ _ (PAle_zero (Lvar 0) (IsLterm_var _))).
    apply LorIntro2_impl. unfold PAle.
    rewrite IsLproposition_rel2, IsLterm_var. apply IsLterm_const.
    rewrite IsLproposition_eq, IsLterm_var. apply IsLterm_const.
  - simpl.
    apply (LimpliesElim _ (Lor (Leq (Lvar 0) PAzero)
                               (Lexists 1 (Leq (Lvar 0) (PAsucc (Lvar 1)))))).
    2: apply (IsProvedAx2 (Lvar 0) (IsLterm_var 0)).
    2: apply VarOccursInTerm_var.
    apply LorElim.
    + clear IHi. apply LeqElimSubstVar.
      unfold PAle, PAsucc. reduce_islproposition.
      rewrite IsLterm_PAnat. reflexivity.
      apply IsLterm_const.
      unfold PAle, Leq.
      rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2, IsFreeForSubst_or.
      rewrite IsFreeForSubst_rel2, IsFreeForSubst_rel2. reflexivity.
      rewrite Subst_implies. apply DropHypothesis.
      apply SubstIsLproposition.
      unfold PAle, PAsucc.
      reduce_islproposition. rewrite IsLterm_PAnat. reflexivity.
      apply IsLterm_const.
      rewrite Subst_or, Subst_PAle, SubstTerm_var. simpl.
      apply LorIntro1.
      apply SubstIsLproposition.
      unfold PAle, PAsucc.
      reduce_islproposition. rewrite IsLterm_PAnat. reflexivity.
      apply IsLterm_const.
      apply PAle_0_t.
      rewrite SubstTerm_PAnat. apply IsLterm_PAnat.
    + apply LexistsElim_impl. unfold PAle, PAsucc, Leq.
      rewrite VarOccursFreeInFormula_implies, VarOccursFreeInFormula_rel2.
      rewrite VarOccursInTerm_var, VarOccursInTerm_op1, PAnat_closed.
      rewrite VarOccursFreeInFormula_or, VarOccursFreeInFormula_rel2.
      rewrite VarOccursInTerm_var, PAnat_closed, VarOccursFreeInFormula_rel2.
      rewrite VarOccursInTerm_var, VarOccursInTerm_op1, PAnat_closed.
      reflexivity.
      apply LforallIntro.
      apply LeqElimSubstVar.
      unfold PAle, PAsucc.
      reduce_islproposition; rewrite IsLterm_PAnat; reflexivity.
      unfold PAsucc. rewrite IsLterm_op1. apply IsLterm_var.
      unfold PAle, Leq.
      rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2, IsFreeForSubst_or.
      rewrite IsFreeForSubst_rel2, IsFreeForSubst_rel2. reflexivity.
      rewrite Subst_implies, Subst_PAle, SubstTerm_PAsucc.
      rewrite SubstTerm_var, SubstTerm_PAnat, Subst_or, Subst_PAle. simpl.
      rewrite SubstTerm_var, SubstTerm_PAnat, Subst_eq. simpl.
      rewrite SubstTerm_PAsucc, SubstTerm_PAnat, SubstTerm_var. simpl.
      apply (LimpliesTrans _ _ (PAle (Lvar 1) (PAnat i))).
      pose proof (PAle_decr (PAnat i) (IsLterm_PAnat i)) as H.
      apply (LforallIntro _ _ 0) in H.
      apply (LforallElim _ _ _ (Lvar 1)) in H.
      rewrite Subst_implies, Subst_PAle, SubstTerm_PAsucc in H.
      rewrite SubstTerm_var, SubstTerm_PAsucc in H. simpl in H.
      rewrite SubstTerm_PAnat, Subst_PAle, SubstTerm_var in H. simpl in H.
      rewrite SubstTerm_PAnat in H. exact H. apply IsLterm_var.
      unfold PAle.
      rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2, IsFreeForSubst_rel2.
      reflexivity.
      (* fails *)
      apply (LforallIntro _ _ 0) in IHi.
      apply (LforallElim _ _ _ (Lvar 1)) in IHi.
      rewrite Subst_implies, Subst_or, Subst_PAle, SubstTerm_PAnat in IHi.
      rewrite SubstTerm_var, Subst_PAle, SubstTerm_var in IHi. simpl in IHi.
      rewrite SubstTerm_PAnat, Subst_eq, SubstTerm_var in IHi. simpl in IHi.
      rewrite SubstTerm_PAnat in IHi.
      apply (LimpliesTrans _ _ _ _ IHi). clear IHi.
      apply LorElim.
      destruct i. simpl.
      apply (LimpliesTrans _ _ (Leq (PAsucc (Lvar 1)) (PAsucc PAzero))).
      apply (LimpliesTrans _ _ _ _ (PAle_zero (Lvar 1) (IsLterm_var 1))).
      apply (LeqElimSubstVarPAnat _ _ 0).
      unfold PAle, PAsucc. reduce_islproposition. apply IsLterm_const.
      rewrite Subst_eq, SubstTerm_PAsucc, SubstTerm_var. simpl.
      rewrite SubstTerm_PAsucc, SubstTerm_PAzero. apply LeqRefl.
      unfold PAsucc. rewrite IsLterm_op1. apply IsLterm_const.
      apply LorIntro2_impl.
      unfold PAle, PAsucc. reduce_islproposition. apply IsLterm_const.
      unfold PAle, PAsucc. reduce_islproposition. apply IsLterm_const.
      simpl.
      apply (LimpliesTrans _ _ (PAle (PAsucc (Lvar 1)) (PAsucc (PAnat i)))).
      pose proof (PAle_incr (PAnat i) (IsLterm_PAnat i)) as H.
      apply (LforallIntro _ _ 0) in H.
      apply (LforallElim _ _ _ (Lvar 1)) in H.
      rewrite Subst_implies, Subst_PAle, SubstTerm_var, SubstTerm_PAnat in H.
      simpl in H. rewrite Subst_PAle, SubstTerm_PAsucc, SubstTerm_var in H.
      simpl in H. rewrite SubstTerm_PAsucc, SubstTerm_PAnat in H.
      exact H. apply IsLterm_var.
      unfold PAle.
      rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2, IsFreeForSubst_rel2.
      reflexivity.
      apply LorIntro1_impl.
      unfold PAle, PAsucc. reduce_islproposition. apply IsLterm_PAnat.
      unfold PAle, PAsucc. reduce_islproposition. apply IsLterm_PAnat.
      apply LeqElimSubstVarPAnat.
      unfold PAle, PAsucc. reduce_islproposition. rewrite IsLterm_PAnat. reflexivity.
      rewrite Subst_or.
      apply LorIntro2.
      apply SubstIsLproposition.
      unfold PAle, PAsucc. reduce_islproposition. rewrite IsLterm_PAnat. reflexivity.
      apply IsLterm_PAnat.
      rewrite Subst_eq, SubstTerm_PAsucc, SubstTerm_var. simpl.
      rewrite SubstTerm_PAsucc, SubstTerm_PAnat.
      apply LeqRefl. unfold PAsucc.
      rewrite IsLterm_op1. apply IsLterm_PAnat.
      apply IsLterm_var.
      unfold PAle, Leq.
      rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2, IsFreeForSubst_or.
      rewrite IsFreeForSubst_rel2, IsFreeForSubst_rel2. reflexivity.
Qed.

Lemma PAle_succ_r : forall i v,
    IsProved IsWeakHeytingAxiom
             (Limplies (PAle (Lvar v) (PAnat i))
                       (Lor (PAle (Lvar v) (PAnat (pred i)))
                            (Leq (Lvar v) (PAnat i)))).
Proof.
  intros.
  apply (eq_ind (Subst (Lvar v) 0 (Limplies (PAle (Lvar 0) (PAnat i))
       (Lor (PAle (Lvar 0) (PAnat (Init.Nat.pred i))) (Leq (Lvar 0) (PAnat i)))))).
  apply LforallElim. apply LforallIntro. apply PAle_succ_r_aux.
  apply IsLterm_var.
  unfold PAle, Leq.
  rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2, IsFreeForSubst_or.
  rewrite IsFreeForSubst_rel2, IsFreeForSubst_rel2. reflexivity.
  unfold PAle. reduce_subst. simpl.
  rewrite SubstTerm_PAnat, SubstTerm_PAnat. reflexivity.
Qed.


(* Semantic proofs of Delta_0 arithmetic formulas.
   An Lforall v bounded by PAnat i is equivalent to a finite conjunction
   of propositions where closed terms are substituted for Lvar v.
   When all quantifiers are bounded, all variables are removed and we are
   left to prove a closed proposition without quantifiers. The latter
   can be solved by satisfaction in the standard model of arithmetic. *)
Lemma LforallBounded : forall (i prop v : nat),
    IsLproposition prop = true
    -> (forall j : nat, j <= i -> IsProved IsWeakHeytingAxiom (Subst (PAnat j) v prop))
    -> IsProved IsWeakHeytingAxiom
               (Limplies (PAle (Lvar v) (PAnat i)) prop).
Proof.
  induction i.
  - intros prop v propprop conjunct.
    specialize (conjunct 0 (Nat.le_refl 0)).
    apply (LimpliesTrans _ _ _ _ (PAle_zero (Lvar v) (IsLterm_var v))).
    apply (LeqElimSubstVarPAnat _ _ 0).
    exact propprop. exact conjunct.
  - intros.
    apply (LimpliesTrans _ _ _ _ (PAle_succ_r (S i) v)). simpl.
    apply LorElim.
    + specialize (IHi prop v H).
      assert (IsLproposition (Limplies (PAle (Lvar v) (PAnat i)) prop) = true)
        as hypprop.
      { unfold PAle. rewrite IsLproposition_implies, IsLproposition_rel2.
        rewrite IsLterm_var, IsLterm_PAnat, H. reflexivity. }
      apply IHi.
      intros. apply H0. apply (Nat.le_trans _ _ _ H1).
      apply le_S, Nat.le_refl.
    + clear IHi.
      apply (LeqElimSubstVarPAnat _ _ (S i)). exact H.
      apply H0, Nat.le_refl.
Qed.

Lemma LforallBounded_lt : forall (i prop v : nat),
    IsLproposition prop = true
    -> (forall j : nat, j < i -> IsProved IsWeakHeytingAxiom (Subst (PAnat j) v prop))
    -> IsProved IsWeakHeytingAxiom
               (Limplies (PAle (PAsucc (Lvar v)) (PAnat i)) prop).
Proof.
  intros. destruct i.
  - apply (LimpliesTrans _ _ (Leq (PAsucc (Lvar v)) (PAnat 0))).
    apply PAle_zero.
    unfold PAsucc. rewrite IsLterm_op1. apply IsLterm_var.
    apply FalseElim_impl. 2: exact H.
    pose proof IsProvedAx1.
    apply (LforallElim _ _ _ (Lvar v)) in H1.
    rewrite Subst_not, Subst_eq, SubstTerm_PAsucc, SubstTerm_var in H1.
    simpl in H1. rewrite SubstTerm_PAzero in H1. exact H1.
    apply IsLterm_var.
    rewrite IsFreeForSubst_not. apply IsFreeForSubst_rel2.
  - apply (LimpliesTrans _ _ (PAle (Lvar v) (PAnat i))).
    pose proof (PAle_decr (PAnat i) (IsLterm_PAnat i)).
    apply (LforallIntro _ _ 0) in H1.
    apply (LforallElim _ _ _ (Lvar v)) in H1.
    rewrite Subst_implies, Subst_PAle, SubstTerm_PAsucc, SubstTerm_var in H1.
    simpl in H1. rewrite SubstTerm_PAsucc, SubstTerm_PAnat, Subst_PAle in H1.
    rewrite SubstTerm_var, SubstTerm_PAnat in H1. simpl in H1. exact H1.
    apply IsLterm_var. unfold PAle.
    rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2, IsFreeForSubst_rel2.
    reflexivity. apply LforallBounded.
    exact H. intros.
    apply H0. apply le_n_S, H1.
Qed.

Lemma PAlt_not_eq : forall i j,
    i < j
    -> IsProved IsWeakHeytingAxiom (Lnot (Leq (PAnat j) (PAnat i))).
Proof.
  induction i.
  - intros. destruct j. inversion H. clear H.
    pose proof (IsProvedAx1).
    apply (LforallElim _ _ _ (PAnat j)) in H.
    rewrite Subst_not, Subst_eq, SubstTerm_PAsucc, SubstTerm_PAzero in H.
    rewrite SubstTerm_var in H. exact H.
    apply IsLterm_PAnat.
    unfold Leq. rewrite IsFreeForSubst_not, IsFreeForSubst_rel2. reflexivity.
  - intros. destruct j. inversion H.
    apply NotByContradiction.
    apply (LimpliesTrans _ _ (Leq (PAnat j) (PAnat i))).
    pose proof IsProvedAx3 as H0.
    apply (LforallElim _ _ 0 (PAnat j)) in H0.
    rewrite Subst_forall in H0; simpl in H0.
    apply (LforallElim _ _ 1 (PAnat i)) in H0.
    rewrite Subst_implies, Subst_implies, Subst_eq, Subst_eq, Subst_eq in H0.
    rewrite SubstTerm_PAsucc, SubstTerm_PAsucc, SubstTerm_var in H0. simpl in H0.
    rewrite SubstTerm_var, SubstTerm_PAsucc in H0. simpl in H0.
    rewrite SubstTerm_PAnat, SubstTerm_PAsucc, SubstTerm_var in H0; simpl in H0.
    rewrite SubstTerm_var in H0. simpl in H0.
    rewrite Subst_eq, SubstTerm_PAnat, SubstTerm_var in H0. simpl in H0.
    exact H0. apply IsLterm_PAnat.
    apply IsFreeForSubst_PAnat, SubstIsLproposition.
    rewrite IsLproposition_implies, IsLproposition_eq, IsLproposition_eq.
    unfold PAsucc. rewrite IsLterm_op1, IsLterm_op1, IsLterm_var, IsLterm_var.
    reflexivity. apply IsLterm_PAnat. apply IsLterm_PAnat.
    apply IsFreeForSubst_PAnat.
    rewrite IsLproposition_forall, IsLproposition_implies.
    rewrite IsLproposition_eq, IsLproposition_eq.
    unfold PAsucc. rewrite IsLterm_op1, IsLterm_op1, IsLterm_var, IsLterm_var.
    reflexivity.
    apply FalseElim_impl. apply IHi. apply le_S_n, H.
    rewrite IsLproposition_not, IsLproposition_eq.
    rewrite IsLterm_PAnat, IsLterm_PAnat. reflexivity.
Qed.

Lemma PAlt_not_le : forall i j,
    i < j
    -> IsProved IsWeakHeytingAxiom (Lnot (PAle (PAnat j) (PAnat i))).
Proof.
  induction i.
  - intros j jpos. destruct j. inversion jpos. clear jpos.
    apply NotByContradiction.
    apply (LimpliesTrans _ _ _ _ (PAle_zero (PAnat (S j)) (IsLterm_PAnat _))).
    apply FalseElim_impl.
    pose proof (IsProvedAx1).
    apply (LforallElim _ _ _ (PAnat j)) in H.
    rewrite Subst_not, Subst_eq, SubstTerm_PAsucc, SubstTerm_PAzero in H.
    rewrite SubstTerm_var in H. exact H.
    apply IsLterm_PAnat.
    apply IsFreeForSubst_PAnat.
    rewrite IsLproposition_not, IsLproposition_eq.
    unfold PAzero, PAsucc. rewrite IsLterm_op1, IsLterm_const, IsLterm_var.
    reflexivity. unfold PAle.
    rewrite IsLproposition_not, IsLproposition_rel2, IsLterm_PAnat, IsLterm_PAnat.
    reflexivity.
  - intros j H. destruct j. inversion H.
    apply le_S_n in H.
    specialize (IHi j H).
    apply NotByContradiction.
    pose proof (PAle_decr (PAnat i) (IsLterm_PAnat _)) as H0.
    apply (LforallIntro _ _ 0) in H0.
    apply (LforallElim _ _ _ (PAnat j)) in H0.
    rewrite Subst_implies, Subst_PAle, SubstTerm_PAsucc in H0.
    rewrite SubstTerm_var, SubstTerm_PAsucc in H0. simpl in H0.
    rewrite SubstTerm_PAnat, Subst_PAle, SubstTerm_var in H0. simpl in H0.
    rewrite SubstTerm_PAnat in H0.
    apply (LimpliesTrans _ _ _ _ H0). clear H0.
    apply (FalseElim_impl _ _ _ IHi).
    unfold PAle. rewrite IsLproposition_not, IsLproposition_rel2.
    rewrite IsLterm_PAnat, IsLterm_PAnat. reflexivity.
    apply IsLterm_PAnat.
    apply IsFreeForSubst_PAnat.
    unfold PAle, PAsucc.
    reduce_islproposition.
    rewrite IsLterm_PAnat. reflexivity.
Qed.
