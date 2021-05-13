(** Encoding of logical formulas by natural numbers.

    These are the formulas of first-order predicate calculus, with a countably
    infinite signature. The relation and operation symbols are therefore
    identified by naturals numbers, up to infinity (relation symbol 0,
    relation symbol 1, ... and likewise for operation symbols).

    The head of a formula's list is a number that gives the type of the formula,
    1: not
    2: implies
    3: or
    4: and
    5: forall
    6: exists
    7: relation symbol
    8: operation symbol
    9: variable

    The next coordinates of the list are the operands, for example an implication
    formula is of type 2, and of length 3.

    Type 7, relation symbol, is also called atomic proposition. The head 7
    is followed by the number of the relation, and its operands (which are terms).
    By convention, relation number 0 is equality. *)

Require Import PeanoNat.
Require Import Arith.Wf_nat.
Require Import Arith.Compare_dec.
Require Import EnumSeqNat.

(* To read formulas more easily, we give their usual names
   to the logical connectives. *)
Notation LnotHead := 1.
Notation LimpliesHead := 2.
Notation LorHead := 3.
Notation LandHead := 4.
Notation LforallHead := 5.
Notation LexistsHead := 6.
Notation LrelHead := 7.
Notation LopHead := 8.
Notation LvarHead := 9.

Definition Lnot (f : nat) : nat := ConsNat LnotHead (ConsNat f NilNat).
Definition Limplies (f g : nat) : nat
  := ConsNat LimpliesHead (ConsNat f (ConsNat g NilNat)).
Definition Lor (f g : nat) : nat := ConsNat LorHead (ConsNat f (ConsNat g NilNat)).
Definition Land (f g : nat) : nat := ConsNat LandHead (ConsNat f (ConsNat g NilNat)).
Definition Lequiv (f g : nat) : nat
  := Land (Limplies f g) (Limplies g f).
Definition Lforall (var f : nat) : nat
  := ConsNat LforallHead (ConsNat var (ConsNat f NilNat)).
Definition Lexists (var f : nat) : nat
  := ConsNat LexistsHead (ConsNat var (ConsNat f NilNat)).
Definition Lrel (r args : nat) : nat := ConsNat LrelHead (ConsNat r args).
Definition Lrel1 (r f : nat) : nat := Lrel r (ConsNat f NilNat).
Definition Lrel2 (r f g : nat) : nat := Lrel r (ConsNat f (ConsNat g NilNat)).
Definition Lrel3 (r f g h : nat) : nat :=
  Lrel r (ConsNat f (ConsNat g (ConsNat h NilNat))).
Definition Leq (t u : nat) : nat := Lrel2 0 t u.
Definition Lop (o args : nat) : nat := ConsNat LopHead (ConsNat o args).
Definition Lconst (c : nat) : nat := Lop c NilNat. (* same as Lop0 *)
Definition Lop1 (o f : nat) : nat := Lop o (ConsNat f NilNat).
Definition Lop2 (o f g : nat) : nat := Lop o (ConsNat f (ConsNat g NilNat)).
Definition Lop3 (o f g h : nat) : nat :=
  Lop o (ConsNat f (ConsNat g (ConsNat h NilNat))).
Definition Lvar (v : nat) : nat := ConsNat LvarHead (ConsNat v NilNat).


(** Algorithms that compute whether a formula is a well-formed variable,
    term or proposition. *)

Definition IsLnot (f : nat) : bool := Nat.eqb f (Lnot (CoordNat f 1)).
Definition IsLimplies (f : nat) : bool :=
  Nat.eqb f (Limplies (CoordNat f 1) (CoordNat f 2)).
Definition IsLor (f : nat) : bool :=
  Nat.eqb f (Lor (CoordNat f 1) (CoordNat f 2)).
Definition IsLand (f : nat) : bool :=
  Nat.eqb f (Land (CoordNat f 1) (CoordNat f 2)).
Definition IsLforall (f : nat) : bool :=
  Nat.eqb f (Lforall (CoordNat f 1) (CoordNat f 2)).
Definition IsLexists (f : nat) : bool :=
  Nat.eqb f (Lexists (CoordNat f 1) (CoordNat f 2)).
Definition IsLrel (f : nat) : bool :=
  Nat.eqb f (Lrel (CoordNat f 1) (TailNat (TailNat f))).
Definition IsLop (f : nat) : bool :=
  Nat.eqb f (Lop (CoordNat f 1) (TailNat (TailNat f))).
Definition IsLop1 (f : nat) : bool :=
  Nat.eqb f (Lop1 (CoordNat f 1) (CoordNat f 2)).
Definition IsLconst (f : nat) : bool := Nat.eqb f (Lconst (CoordNat f 1)).
Definition IsLvar (f : nat) : bool := Nat.eqb f (Lvar (CoordNat f 1)).
Definition IsLeq (f : nat) : bool := Nat.eqb f (Leq (CoordNat f 2) (CoordNat f 3)).

Lemma LnotIsNot : forall f,
    IsLnot (Lnot f) = true.
Proof.
  intros. unfold IsLnot, Lnot.
  rewrite CoordConsTailNat.
  rewrite CoordConsHeadNat.
  apply Nat.eqb_refl.
Qed.

Lemma LimpliesIsImplies : forall f g,
    IsLimplies (Limplies f g) = true.
Proof.
  intros. unfold IsLimplies, Limplies.
  do 3 rewrite CoordConsTailNat.
  do 2 rewrite CoordConsHeadNat.
  apply Nat.eqb_refl.
Qed.

Lemma LorIsOr : forall f g,
    IsLor (Lor f g) = true.
Proof.
  intros. unfold IsLor, Lor.
  do 3 rewrite CoordConsTailNat.
  do 2 rewrite CoordConsHeadNat.
  apply Nat.eqb_refl.
Qed.

Lemma LandIsAnd : forall f g,
    IsLand (Land f g) = true.
Proof.
  intros. unfold IsLand, Land.
  do 3 rewrite CoordConsTailNat.
  do 2 rewrite CoordConsHeadNat.
  apply Nat.eqb_refl.
Qed.

Lemma LforallIsForall : forall v f,
    IsLforall (Lforall v f) = true.
Proof.
  intros. unfold IsLforall, Lforall.
  do 3 rewrite CoordConsTailNat.
  do 2 rewrite CoordConsHeadNat.
  apply Nat.eqb_refl.
Qed.

Lemma LexistsIsExists : forall v f,
    IsLexists (Lexists v f) = true.
Proof.
  intros. unfold IsLexists, Lexists.
  do 3 rewrite CoordConsTailNat.
  do 2 rewrite CoordConsHeadNat.
  apply Nat.eqb_refl.
Qed.

Lemma LrelIsRel : forall r args,
    IsLrel (Lrel r args) = true.
Proof.
  intros. unfold IsLrel, Lrel.
  rewrite CoordConsTailNat.
  rewrite CoordConsHeadNat.
  do 2 rewrite TailConsNat.
  apply Nat.eqb_refl.
Qed.


(* Length of nodes *)
Lemma LengthLnot : forall f, LengthNat (Lnot f) = 2.
Proof.
  intros. unfold Lnot.
  rewrite LengthConsNat, LengthConsNat.
  reflexivity.
Qed.

Lemma LengthLimplies : forall f g, LengthNat (Limplies f g) = 3.
Proof.
  intros. unfold Limplies.
  rewrite LengthConsNat, LengthConsNat, LengthConsNat.
  reflexivity.
Qed.

Lemma LengthLor : forall f g, LengthNat (Lor f g) = 3.
Proof.
  intros. unfold Lor.
  rewrite LengthConsNat, LengthConsNat, LengthConsNat.
  reflexivity.
Qed.

Lemma LengthLand : forall f g, LengthNat (Land f g) = 3.
Proof.
  intros. unfold Land.
  rewrite LengthConsNat, LengthConsNat, LengthConsNat.
  reflexivity.
Qed.

Lemma LengthLforall : forall v f, LengthNat (Lforall v f) = 3.
Proof.
  intros. unfold Lforall.
  rewrite LengthConsNat, LengthConsNat, LengthConsNat.
  reflexivity.
Qed.

Lemma LengthLexists : forall v f, LengthNat (Lexists v f) = 3.
Proof.
  intros. unfold Lexists.
  rewrite LengthConsNat, LengthConsNat, LengthConsNat.
  reflexivity.
Qed.

Lemma LengthLop : forall o args : nat, LengthNat (Lop o args) = 2 + LengthNat args.
Proof.
  intros. unfold Lop.
  rewrite LengthConsNat, LengthConsNat.
  reflexivity.
Qed.

Lemma LengthLconst : forall c, LengthNat (Lconst c) = 2.
Proof.
  intros. unfold Lconst.
  rewrite LengthLop.
  reflexivity.
Qed.

Lemma LengthLop1 : forall o f, LengthNat (Lop1 o f) = 3.
Proof.
  intros. unfold Lop1.
  rewrite LengthLop, LengthConsNat.
  reflexivity.
Qed.

Lemma LengthLop2 : forall o f g, LengthNat (Lop2 o f g) = 4.
Proof.
  intros. unfold Lop2.
  rewrite LengthLop, LengthConsNat, LengthConsNat.
  reflexivity.
Qed.

Lemma LengthLop3 : forall o f g h, LengthNat (Lop3 o f g h) = 5.
Proof.
  intros. unfold Lop3.
  rewrite LengthLop.
  rewrite LengthConsNat, LengthConsNat, LengthConsNat.
  reflexivity.
Qed.

Lemma LengthLrel : forall r args : nat, LengthNat (Lrel r args) = 2 + LengthNat args.
Proof.
  intros. unfold Lrel.
  rewrite LengthConsNat, LengthConsNat.
  reflexivity.
Qed.

Lemma LengthLrel1 : forall r f, LengthNat (Lrel1 r f) = 3.
Proof.
  intros. unfold Lrel1.
  rewrite LengthLrel.
  rewrite LengthConsNat.
  reflexivity.
Qed.

Lemma LengthLrel2 : forall r f g, LengthNat (Lrel2 r f g) = 4.
Proof.
  intros. unfold Lrel2.
  rewrite LengthLrel.
  rewrite LengthConsNat, LengthConsNat.
  reflexivity.
Qed.

Lemma LengthLrel3 : forall r f g h, LengthNat (Lrel3 r f g h) = 5.
Proof.
  intros. unfold Lrel3.
  rewrite LengthLrel.
  rewrite LengthConsNat, LengthConsNat, LengthConsNat.
  reflexivity.
Qed.

Lemma LengthLvar : forall v, LengthNat (Lvar v) = 2.
Proof.
  intro v. unfold Lvar.
  rewrite LengthConsNat, LengthConsNat.
  reflexivity.
Qed.


(* Nodes destructors *)
Lemma CoordNat_not_1 : forall f, CoordNat (Lnot f) 1 = f.
Proof.
  intros. unfold Lnot.
  rewrite CoordConsTailNat, CoordConsHeadNat.
  reflexivity.
Qed.

Lemma CoordNat_implies_0 : forall f g, CoordNat (Limplies f g) 0 = LimpliesHead.
Proof.
  intros. unfold Limplies.
  rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma CoordNat_implies_1 : forall f g, CoordNat (Limplies f g) 1 = f.
Proof.
  intros. unfold Limplies.
  rewrite CoordConsTailNat.
  rewrite CoordConsHeadNat. reflexivity.
Qed.

Lemma CoordNat_implies_2 : forall f g, CoordNat (Limplies f g) 2 = g.
Proof.
  intros. unfold Limplies.
  rewrite CoordConsTailNat, CoordConsTailNat.
  rewrite CoordConsHeadNat. reflexivity.
Qed.

Lemma CoordNat_or_1 : forall f g, CoordNat (Lor f g) 1 = f.
Proof.
  intros. unfold Lor.
  rewrite CoordConsTailNat.
  rewrite CoordConsHeadNat. reflexivity.
Qed.

Lemma CoordNat_or_2 : forall f g, CoordNat (Lor f g) 2 = g.
Proof.
  intros. unfold Lor.
  rewrite CoordConsTailNat, CoordConsTailNat.
  rewrite CoordConsHeadNat. reflexivity.
Qed.

Lemma CoordNat_and_1 : forall f g, CoordNat (Land f g) 1 = f.
Proof.
  intros. unfold Land.
  rewrite CoordConsTailNat.
  rewrite CoordConsHeadNat. reflexivity.
Qed.

Lemma CoordNat_and_2 : forall f g, CoordNat (Land f g) 2 = g.
Proof.
  intros. unfold Land.
  rewrite CoordConsTailNat, CoordConsTailNat.
  rewrite CoordConsHeadNat. reflexivity.
Qed.

Lemma CoordNat_equiv_1 : forall f g, CoordNat (Lequiv f g) 1 = Limplies f g.
Proof.
  intros. apply CoordNat_and_1.
Qed.

Lemma CoordNat_equiv_2 : forall f g, CoordNat (Lequiv f g) 2 = Limplies g f.
Proof.
  intros. apply CoordNat_and_2.
Qed.

Lemma CoordNat_forall_1 : forall v f, CoordNat (Lforall v f) 1 = v.
Proof.
  intros. unfold Lforall.
  rewrite CoordConsTailNat.
  rewrite CoordConsHeadNat. reflexivity.
Qed.

Lemma CoordNat_forall_2 : forall v f, CoordNat (Lforall v f) 2 = f.
Proof.
  intros. unfold Lforall.
  rewrite CoordConsTailNat, CoordConsTailNat.
  rewrite CoordConsHeadNat. reflexivity.
Qed.

Lemma CoordNat_exists_1 : forall v f, CoordNat (Lexists v f) 1 = v.
Proof.
  intros. unfold Lexists.
  rewrite CoordConsTailNat.
  rewrite CoordConsHeadNat. reflexivity.
Qed.

Lemma CoordNat_exists_2 : forall v f, CoordNat (Lexists v f) 2 = f.
Proof.
  intros. unfold Lexists.
  rewrite CoordConsTailNat, CoordConsTailNat.
  rewrite CoordConsHeadNat. reflexivity.
Qed.

Lemma CoordNat_rel : forall r args i,
    CoordNat (Lrel r args) (S (S i)) = CoordNat args i.
Proof.
  intros. unfold Lrel.
  rewrite CoordConsTailNat, CoordConsTailNat.
  reflexivity.
Qed.

Lemma CoordNat_rel_1 : forall r args,
    CoordNat (Lrel r args) 1 = r.
Proof.
  intros. unfold Lrel.
  rewrite CoordConsTailNat, CoordConsHeadNat.
  reflexivity.
Qed.

Lemma CoordNat_op : forall o args i,
    CoordNat (Lop o args) (S (S i)) = CoordNat args i.
Proof.
  intros. unfold Lop.
  rewrite CoordConsTailNat, CoordConsTailNat.
  reflexivity.
Qed.

Lemma TailTailNat_op : forall o args,
    TailNat (TailNat (Lop o args)) = args.
Proof.
  intros. unfold Lop.
  rewrite TailConsNat, TailConsNat.
  reflexivity.
Qed.


(* Test that a number represents a well-formed term.
   It interprets the number as a tree of symbols, and checks depth-first
   that all nodes are Lops, until leaves are reached which must be variables
   or constants. *)
Fixpoint IsLopTerm (t i : nat) (rec : nat -> bool) {struct i} : bool :=
  match i with
  | O => false
  | 1 => false
  | 2 => Nat.leb 2 (LengthNat t)
  | S j => andb (rec j) (IsLopTerm t j rec)
  end.
Definition IsLtermRec (n : nat) (rec : nat -> bool) : bool :=
  match CoordNat n 0 with
  | LvarHead => IsLvar n
  | LopHead => IsLopTerm n (LengthNat n) rec (* cannot use TailNat n,
                                               because the indices of rec are those of n. *)
              && Nat.eqb (NthTailNat n (LengthNat n)) 0
  | _ => false
  end.
Definition IsLterm : nat -> bool := TreeFoldNat IsLtermRec false.

Lemma IsLopTerm_spec : forall i t rec,
    IsLopTerm t i rec = true
    <-> (2 <= i /\ 2 <= LengthNat t /\ forall j, 2 <= j < i -> rec j = true).
Proof.
  split. induction i. 3: induction i.
  - intros. discriminate.
  - intros. simpl in H.
    destruct i. discriminate. destruct i.
    destruct (LengthNat t). discriminate.
    destruct n. discriminate. split. apply Nat.le_refl.
    split. apply le_n_S, le_n_S, le_0_n.
    intros. exfalso. apply (Nat.lt_irrefl 2).
    apply (Nat.le_lt_trans _ j); apply H0.
    apply andb_prop in H. destruct H. specialize (IHi H0). destruct IHi.
    split. apply le_n_S, le_n_S, le_0_n.
    split. apply H2. intros. destruct H3.
    apply Nat.le_succ_r in H4. destruct H4.
    apply H2. split. apply H3. apply H4.
    inversion H4. exact H.
  - intros [H [H0 H1]]. inversion H.
  - intros [H [H0 H1]].
    simpl. destruct i. apply le_S_n in H. inversion H.
    destruct i. destruct (LengthNat t). inversion H0.
    destruct n. apply le_S_n in H0. inversion H0. reflexivity.
    apply andb_true_intro. split.
    apply H1. split. apply le_n_S, le_n_S, le_0_n.
    apply Nat.le_refl. apply IHi. split.
    apply le_n_S, le_n_S, le_0_n. split. exact H0.
    intros. apply H1. split. apply H2.
    apply le_S, H2.
Qed.

Lemma IsLterm_step : forall t,
    IsLterm t = TreeFoldNatRec IsLtermRec false t (fun k _ => IsLterm k).
Proof.
  intros.
  unfold IsLterm, TreeFoldNat. rewrite Fix_eq.
  reflexivity.
  intros. unfold IsLtermRec, TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat x) 0). reflexivity.
  destruct (CoordNat x 0). reflexivity.
  repeat (destruct n; [reflexivity|]).
  destruct n.
  apply f_equal2. 2: reflexivity. 
  generalize (LengthNat x).
  induction n.
  - reflexivity.
  - simpl. destruct n. reflexivity.
    destruct n. reflexivity.
    rewrite IHn, H. reflexivity.
  - destruct n. reflexivity. reflexivity.
Qed.

Lemma Lterm_rect : forall (A : nat -> Type),
    (forall v:nat, A (Lvar v))
    -> (forall (o terms:nat)
         (termsTrunc : NthTailNat terms (LengthNat terms) = 0)
         (IHterms : forall i, i < LengthNat terms
                         -> prod (IsLterm (CoordNat terms i) = true)
                                (A (CoordNat terms i))),
          A (Lop o terms))
    -> forall term, IsLterm term = true -> A term.
Proof.
  intros A varcase opcase.
  apply (Fix lt_wf (fun term => IsLterm term = true -> A term)).
  intros term IHterm termterm.
  rewrite IsLterm_step in termterm.
  unfold TreeFoldNatRec in termterm.
  destruct (le_lt_dec (LengthNat term) 0). discriminate termterm.
  unfold IsLtermRec in termterm.
  destruct (CoordNat term 0) eqn:headTerm.
  discriminate termterm.
  do 7 (destruct n; [discriminate termterm|]).
  destruct n.
  - (* Lop *)
    apply andb_prop in termterm. destruct termterm as [termterm termtrunc].
    apply IsLopTerm_spec in termterm.
    destruct termterm as [_ [H termterm]].
    destruct (LengthNat term) eqn:lenTerm.
    exfalso; inversion l. destruct n.
    apply le_S_n in H. exfalso; inversion H.
    replace term with (Lop (CoordNat term 1) (TailNat (TailNat term))).
    apply opcase.
    apply Nat.eqb_eq in termtrunc.
    rewrite LengthTailNat, LengthTailNat, lenTerm. simpl. exact termtrunc.
    intros i H0.
    rewrite LengthTailNat, LengthTailNat in H0.
    rewrite CoordTailNat, CoordTailNat.
    rewrite lenTerm in H0. simpl in H0.
    split.
    apply termterm.
    split. apply le_n_S, le_n_S, le_0_n.
    apply le_n_S, le_n_S, H0.
    apply IHterm.
    rewrite <- lenTerm in l.
    exact (CoordLower _ _ (LengthPositive _ l)).
    apply termterm.
    split. apply le_n_S, le_n_S, le_0_n.
    apply le_n_S, le_n_S, H0.
    rewrite <- lenTerm in l.
    rewrite (HeadTailDecompNat term l) at 3.
    unfold Lop. rewrite headTerm. apply f_equal.
    rewrite (HeadTailDecompNat (TailNat term)) at 2.
    rewrite CoordTailNat. reflexivity.
    rewrite LengthTailNat, lenTerm.
    apply le_n_S, le_0_n.
  - (* Lvar *)
    destruct n. 2: discriminate. apply Nat.eqb_eq in termterm.
    rewrite termterm. apply varcase.
Qed.

Lemma IsLterm_var : forall v:nat, IsLterm (Lvar v) = true.
Proof.
  intro c.
  rewrite IsLterm_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lvar c)) 0).
  rewrite LengthLvar in l. inversion l.
  unfold IsLtermRec. unfold Lvar at 1. rewrite CoordConsHeadNat.
  apply Nat.eqb_eq.
  unfold Lvar at 3.
  rewrite CoordConsTailNat, CoordConsHeadNat.
  reflexivity.
Qed.

Lemma LopHeadIsTerm : forall t,
    (forall i:nat, i < pred (pred (LengthNat t))
            -> IsLterm (CoordNat t (S (S i))) = true)
    -> CoordNat t 0 = LopHead
    -> 2 <= LengthNat t
    -> NthTailNat t (LengthNat t) = 0
    -> IsLterm t = true.
Proof.
  intros.
  rewrite IsLterm_step.
  unfold IsLtermRec, TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat t) 0).
  exfalso. apply (Nat.le_trans _ _ _ H1) in l. inversion l.
  rewrite H0, H2, Nat.eqb_refl, Bool.andb_true_r.
  apply IsLopTerm_spec.
  split. exact H1. split. exact H1.
  intros.
  destruct H3.
  destruct j. inversion H3. destruct j. apply le_S_n in H3. inversion H3.
  specialize (H j).
  apply H.
  destruct (LengthNat t). inversion H4.
  destruct n. simpl. apply le_S_n in H4. inversion H4.
  simpl. apply le_S_n, le_S_n, H4.
Qed.

Lemma LopIsTerm : forall (o args:nat),
    (forall i:nat, i < LengthNat args -> IsLterm (CoordNat args i) = true)
    -> NthTailNat args (LengthNat args) = 0
    -> IsLterm (Lop o args) = true. (* Is is an equivalence actually *)
Proof.
  intros o args H argstrunc.
  apply LopHeadIsTerm.
  intros i H0. rewrite CoordNat_op.
  rewrite LengthLop in H0.
  apply H, H0.
  unfold Lop. rewrite CoordConsHeadNat. reflexivity.
  rewrite LengthLop.
  apply le_n_S, le_n_S, le_0_n.
  rewrite LengthLop. unfold Lop.
  change (2 + LengthNat args) with (S (S (LengthNat args))).
  rewrite NthTailConsNat, NthTailConsNat. exact argstrunc.
Qed.

(* The full specification of IsLterm, which is the intuitive definition of IsTerm.
   We leave it only to prove the correctness of TreeFoldNat, IsLterm_rect should be
   enough to prove all subsequent lemmas. *)
Lemma IsLterm_spec : forall (t:nat),
    IsLterm t = true
    <-> (t = Lvar (CoordNat t 1)
       \/ (CoordNat t 0 = LopHead
          /\ 2 <= LengthNat t
          /\ NthTailNat t (LengthNat t) = 0
          /\ forall k:nat, 2 <= k < LengthNat t -> IsLterm (CoordNat t k) = true)).
Proof.
  intro t. split.
  - revert t. apply Lterm_rect.
    + (* Lvar *)
      intros. left. unfold Lvar.
      rewrite CoordConsTailNat, CoordConsHeadNat. reflexivity.
    + (* Lop *)
      intros. right. split.
      unfold Lop. rewrite CoordConsHeadNat. reflexivity. split.
      rewrite LengthLop. apply le_n_S, le_n_S, le_0_n.
      split. rewrite LengthLop.
      change (2 + LengthNat terms) with (S (S (LengthNat terms))).
      unfold Lop. rewrite NthTailConsNat, NthTailConsNat. exact termsTrunc.
      intros k H. destruct H. destruct k. inversion H.
      destruct k. apply le_S_n in H. inversion H.
      unfold Lop. rewrite CoordConsTailNat, CoordConsTailNat.
      apply IHterms. rewrite LengthLop in H0.
      apply le_S_n, le_S_n in H0. exact H0.
  - intros [H | [tlop H]].
    rewrite H. apply IsLterm_var.
    destruct H.
    replace t with (Lop (CoordNat t 1) (TailNat (TailNat t))).
    apply LopIsTerm. intros i H2.
    rewrite CoordTailNat, CoordTailNat. apply H0.
    split. apply le_n_S, le_n_S, le_0_n.
    rewrite LengthTailNat, LengthTailNat in H2.
    apply le_n_S, le_n_S in H2. unfold lt.
    destruct (LengthNat t). inversion H.
    simpl in H2. destruct n. apply le_S_n in H. inversion H.
    apply H2.
    destruct H0 as [ttrunc H0].
    rewrite LengthTailNat, LengthTailNat.
    destruct (LengthNat t). inversion H. destruct n.
    apply le_S_n in H. inversion H. simpl. exact ttrunc.
    transitivity (ConsNat (CoordNat t 0) (TailNat t)).
    unfold Lop.
    rewrite tlop.
    rewrite <- (CoordTailNat t 0).
    rewrite <- (HeadTailDecompNat (TailNat t)). reflexivity.
    rewrite LengthTailNat.
    destruct (LengthNat t).
    inversion H. simpl. destruct n. apply le_S_n in H. inversion H.
    apply le_n_S, le_0_n.
    symmetry. apply HeadTailDecompNat. destruct (LengthNat t).
    inversion H. apply le_n_S, le_0_n.
Qed.

Lemma IsLterm_const : forall c:nat, IsLterm (Lconst c) = true.
Proof.
  intro c. apply LopIsTerm. intros. inversion H. reflexivity.
Qed.

Lemma IsLterm_op1 : forall (o n:nat), IsLterm (Lop1 o n) = IsLterm n.
Proof.
  intros o n.
  rewrite IsLterm_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lop1 o n)) 0).
  rewrite LengthLop1 in l. inversion l.
  unfold IsLtermRec. unfold Lop1, Lop.
  rewrite CoordConsHeadNat.
  do 3 rewrite LengthConsNat.
  do 3 rewrite NthTailConsNat.
  change (LengthNat NilNat) with O.
  simpl.
  do 2 rewrite LengthConsNat.
  do 2 rewrite CoordConsTailNat.
  rewrite CoordConsHeadNat, Bool.andb_true_r.
  destruct (IsLterm n). 2: reflexivity. reflexivity.
Qed.

Lemma IsLterm_op2 : forall (o n p:nat), IsLterm (Lop2 o n p) = (IsLterm n && IsLterm p)%bool.
Proof.
  intros o n p.
  rewrite IsLterm_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lop2 o n p)) 0).
  exfalso. rewrite LengthLop2 in l. inversion l.
  unfold IsLtermRec. unfold Lop2, Lop.
  rewrite CoordConsHeadNat.
  do 4 rewrite LengthConsNat. 
  do 4 rewrite NthTailConsNat.
  change (LengthNat NilNat) with O.
  simpl.
  do 2 rewrite LengthConsNat.
  do 5 rewrite CoordConsTailNat.
  do 2 rewrite CoordConsHeadNat.
  destruct (IsLterm p), (IsLterm n); reflexivity.
Qed.


(* Test that a number represents a well-formed proposition. *)
Definition IsLpropositionRec (f : nat) (rec : nat -> bool) : bool :=
  match CoordNat f 0 with
  | LnotHead => IsLnot f && rec 1
  | LimpliesHead => IsLimplies f && rec 1 && rec 2
  | LorHead => IsLor f && rec 1 && rec 2
  | LandHead => IsLand f && rec 1 && rec 2
  | LforallHead => IsLforall f && rec 2
  | LexistsHead => IsLexists f && rec 2
  | LrelHead => IsLrel f && IsLterm (Lop 0 (TailNat (TailNat f)))
  | _ => false
  end.
Definition IsLproposition : nat -> bool := TreeFoldNat IsLpropositionRec false.

Lemma IsLproposition_step : forall p,
    IsLproposition p = TreeFoldNatRec IsLpropositionRec false p
                                      (fun k _ => IsLproposition k).
Proof.
  intros.
  unfold IsLproposition, TreeFoldNat. rewrite Fix_eq.
  reflexivity.
  intros. unfold IsLpropositionRec, TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat x) 0). reflexivity.
  destruct (CoordNat x 0). reflexivity.
  destruct n. rewrite H. reflexivity.
  destruct n. rewrite H, H. reflexivity.
  destruct n. rewrite H, H. reflexivity.
  destruct n. rewrite H, H. reflexivity.
  destruct n. rewrite H. reflexivity.
  destruct n. rewrite H. reflexivity.
  destruct n.
  generalize (LengthNat x).
  intro n. destruct n.
  - reflexivity.
  - simpl. destruct n. reflexivity.
    destruct n. reflexivity. reflexivity.
  - destruct n. reflexivity. reflexivity.
Qed.

Lemma Lproposition_rect : forall (A : nat -> Type),
    (forall (r terms:nat)
       (termsTrunc : NthTailNat terms (LengthNat terms) = 0)
       (elemterms : forall i, i < LengthNat terms -> IsLterm (CoordNat terms i) = true),
        A (Lrel r terms))
    -> (forall (prop:nat) (propprop : IsLproposition prop = true)
       (IHprop : A prop), A (Lnot prop))
    -> (forall (g h:nat)
         (gprop : IsLproposition g = true)
         (hprop : IsLproposition h = true)
         (IHg : A g) (IHh : A h), A (Limplies g h))
    -> (forall (g h:nat)
         (gprop : IsLproposition g = true)
         (hprop : IsLproposition h = true)
         (IHg : A g) (IHh : A h), A (Lor g h))
    -> (forall (g h:nat)
         (gprop : IsLproposition g = true)
         (hprop : IsLproposition h = true)
         (IHg : A g) (IHh : A h), A (Land g h))
    -> (forall (v prop:nat) (propprop : IsLproposition prop = true)
         (IHprop : A prop), A (Lforall v prop))
    -> (forall (v prop:nat) (propprop : IsLproposition prop = true)
         (IHprop : A prop), A (Lexists v prop))
    -> forall prop, IsLproposition prop = true -> A prop.
Proof.
  intros A relcase notcase impliescase orcase andcase forallcase existscase.
  apply (Fix lt_wf (fun prop => IsLproposition prop = true -> A prop)).
  intros prop IHprop propprop.
  rewrite IsLproposition_step in propprop.
  unfold TreeFoldNatRec in propprop.
  destruct (le_lt_dec (LengthNat prop) 0). discriminate propprop.
  unfold IsLpropositionRec in propprop.
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
  (* Lrel, base case withtout IHprop *)
  2: discriminate. clear IHprop.
  apply andb_prop in propprop. destruct propprop as [proprel proptrunc].
  apply Nat.eqb_eq in proprel. rewrite proprel.
  rewrite IsLterm_step in proptrunc.
  unfold TreeFoldNatRec in proptrunc.
  rewrite LengthLop in proptrunc. simpl in proptrunc.
  unfold IsLtermRec in proptrunc.
  unfold Lop in proptrunc at 1.
  rewrite CoordConsHeadNat in proptrunc.
  apply andb_prop in proptrunc. destruct proptrunc.
  apply Nat.eqb_eq in H0.
  apply relcase. rewrite LengthLop in H0. simpl in H0.
  unfold Lop in H0. rewrite TailConsNat, TailConsNat in H0.
  exact H0.
  intros i H1.
  apply IsLopTerm_spec in H. destruct H, H2.
  specialize (H3 (S (S i))). rewrite LengthLop in H3.
  unfold Lop in H3. rewrite CoordConsTailNat, CoordConsTailNat in H3.
  apply H3. split. apply le_n_S, le_n_S, le_0_n.
  apply le_n_S, le_n_S. exact H1.
Qed.

Lemma IsLproposition_not : forall f,
    IsLproposition (Lnot f) = IsLproposition f.
Proof.
  intros. rewrite IsLproposition_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lnot f)) 0).
  rewrite LengthLnot in l. inversion l.
  unfold IsLpropositionRec.
  rewrite LnotIsNot.
  unfold Lnot.
  do 3 rewrite CoordConsTailNat.
  do 2 rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma IsLproposition_implies : forall f g,
    IsLproposition (Limplies f g)
    = (IsLproposition f && IsLproposition g)%bool.
Proof.
  intros. rewrite IsLproposition_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Limplies f g)) 0).
  rewrite LengthLimplies in l. inversion l.
  unfold IsLpropositionRec.
  rewrite CoordNat_implies_0, CoordNat_implies_2.
  rewrite LimpliesIsImplies.
  unfold Limplies.
  rewrite CoordConsTailNat, CoordConsHeadNat.
  reflexivity.
Qed.

Lemma IsLproposition_or : forall f g,
    IsLproposition (Lor f g)
    = (IsLproposition f && IsLproposition g)%bool.
Proof.
  intros. rewrite IsLproposition_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lor f g)) 0).
  rewrite LengthLor in l. inversion l.
  unfold IsLpropositionRec.
  unfold Lor at 1. rewrite CoordConsHeadNat.
  rewrite LorIsOr.
  unfold Lor.
  do 3 rewrite CoordConsTailNat.
  do 2 rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma IsLproposition_and : forall f g,
    IsLproposition (Land f g)
    = (IsLproposition f && IsLproposition g)%bool.
Proof.
  intros. rewrite IsLproposition_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Land f g)) 0).
  rewrite LengthLand in l. inversion l.
  unfold IsLpropositionRec.
  unfold Land at 1. rewrite CoordConsHeadNat.
  rewrite LandIsAnd. unfold Land.
  do 3 rewrite CoordConsTailNat.
  do 2 rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma IsLproposition_equiv : forall f g,
    IsLproposition (Lequiv f g)
    = (IsLproposition f && IsLproposition g)%bool.
Proof.
  intros. unfold Lequiv.
  rewrite IsLproposition_and.
  rewrite IsLproposition_implies, IsLproposition_implies.
  destruct (IsLproposition f), (IsLproposition g); reflexivity.
Qed.

Lemma IsLproposition_forall : forall v f,
    IsLproposition (Lforall v f) = IsLproposition f.
Proof.
  intros. rewrite IsLproposition_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lforall v f)) 0).
  rewrite LengthLforall in l. inversion l.
  unfold IsLpropositionRec.
  unfold Lforall at 1. rewrite CoordConsHeadNat.
  rewrite LforallIsForall.
  unfold Lforall.
  do 2 rewrite CoordConsTailNat.
  rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma IsLproposition_exists : forall v f,
    IsLproposition (Lexists v f) = IsLproposition f.
Proof.
  intros. rewrite IsLproposition_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat (Lexists v f)) 0).
  rewrite LengthLexists in l. inversion l.
  unfold IsLpropositionRec.
  unfold Lexists at 1. rewrite CoordConsHeadNat.
  rewrite LexistsIsExists.
  unfold Lexists.
  do 2 rewrite CoordConsTailNat.
  rewrite CoordConsHeadNat.
  reflexivity.
Qed.

Lemma IsLproposition_rel : forall r args,
    IsLproposition (Lrel r args) = true
    <-> (NthTailNat args (LengthNat args) = 0
       /\ forall n, n < LengthNat args -> IsLterm (CoordNat args n) = true).
Proof.
  intros. rewrite IsLproposition_step.
  unfold TreeFoldNatRec. rewrite LengthLrel. simpl.
  unfold IsLpropositionRec.
  unfold Lrel at 1. rewrite CoordConsHeadNat.
  split.
  - intros H. apply andb_prop in H. destruct H as [H H0].
    rewrite IsLterm_step in H0.
    unfold TreeFoldNatRec in H0.
    rewrite LengthLop in H0. simpl in H0.
    unfold IsLtermRec in H0.
    unfold Lop in H0 at 1.
    rewrite CoordConsHeadNat in H0.
    apply andb_prop in H0. destruct H0.
    split.
    apply Nat.eqb_eq in H1. rewrite LengthLop in H1.
    unfold Lop in H1. 
    simpl in H1.
    rewrite LengthTailNat, LengthTailNat, LengthLrel in H1.
    rewrite TailConsNat, TailConsNat in H1. 
    unfold Lrel in H1. rewrite TailConsNat, TailConsNat in H1.
    exact H1. clear H1.
    intros n H1.
    apply IsLopTerm_spec in H0. destruct H0, H2. clear H2.
    specialize (H3 (S (S n))).
    unfold Lrel in H3.
    rewrite CoordNat_op, TailConsNat, TailConsNat in H3.
    apply H3. split. apply le_n_S, le_n_S, le_0_n.
    rewrite LengthLop.
    apply le_n_S, le_n_S. exact H1.
  - intro H. apply andb_true_intro; split.
    apply LrelIsRel.
    rewrite IsLterm_step.
    unfold TreeFoldNatRec.
    rewrite LengthLop. simpl.
    unfold IsLtermRec.
    unfold Lop at 1.
    rewrite CoordConsHeadNat.
    apply andb_true_intro. destruct H. split.
    apply IsLopTerm_spec. split.
    rewrite LengthLop, LengthTailNat, LengthTailNat, LengthLrel.
    apply le_n_S, le_n_S, le_0_n. split.
    rewrite LengthLop, LengthTailNat, LengthTailNat, LengthLrel.
    apply le_n_S, le_n_S, le_0_n. 
    intros j H1. rewrite LengthLop in H1. destruct H1.
    destruct j. inversion H1. destruct j. apply le_S_n in H1. inversion H1.
    rewrite CoordNat_op, CoordTailNat, CoordTailNat, CoordNat_rel.
    apply H0. rewrite LengthTailNat, LengthTailNat, LengthLrel in H2.
    apply le_S_n, le_S_n in H2. exact H2.
    apply Nat.eqb_eq.
    rewrite LengthLop, LengthTailNat, LengthTailNat. simpl.
    rewrite LengthLrel. simpl. unfold Lop.
    rewrite TailConsNat, TailConsNat. unfold Lrel.
    rewrite TailConsNat, TailConsNat. exact H.
Qed.

Lemma IsLproposition_rel2 : forall r f g,
    IsLproposition (Lrel2 r f g) = (IsLterm f && IsLterm g)%bool.
Proof.
  intros. 
  rewrite IsLproposition_step.
  unfold TreeFoldNatRec.
  rewrite LengthLrel2. simpl.
  unfold IsLpropositionRec.
  unfold Lrel2 at 1, Lrel; rewrite CoordConsHeadNat.
  unfold Lrel2.
  rewrite LrelIsRel. simpl.
  unfold Lrel. rewrite TailConsNat, TailConsNat.
  exact (IsLterm_op2 0 f g).
Qed.

Lemma IsLproposition_eq : forall f g,
    IsLproposition (Leq f g) = (IsLterm f && IsLterm g)%bool.
Proof.
  intros. apply IsLproposition_rel2.
Qed.

Global Ltac reduce_islproposition
  := repeat (rewrite IsLproposition_exists
             || rewrite IsLproposition_forall
             || rewrite IsLproposition_not
             || rewrite IsLproposition_and
             || rewrite IsLproposition_or
             || rewrite IsLproposition_implies
             || rewrite IsLproposition_eq
             || rewrite IsLproposition_rel2
             || rewrite IsLterm_op1
             || rewrite IsLterm_op2
             || rewrite IsLterm_var).

