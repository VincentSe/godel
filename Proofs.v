(** Encoding of proofs by natural numbers.
    The proofs are formalized in the style of Hilbert, as a list of formulas
    that imply one another.

    The axioms are represented by a characteristic function IsAxiom : nat -> bool,
    which incites to consider computable sets of axioms. We believe those are
    the only reasonable sets of axioms, so that mathematical proofs can be
    mechanically checked. If one wants non-computable sets of axioms, one therefore
    has to pose extra meta-axioms in Coq. For example, Henkin's proof of Gödel's
    completeness theorem considers saturated sets of axioms, and it is known that
    Henkin's proof requires Markov's principle.

    Function IsProof will only assume constructive logic, because the excluded
    middle axiom schema can be added via IsAxiom, as is done in the file
    PeanoAxioms.v, to pass from Heyting arithmetic to Peano arithmetic. *)

Require Import ConstructiveEpsilon.
Require Import PeanoNat.
Require Import Arith.Wf_nat.
Require Import Arith.Compare_dec.
Require Import EnumSeqNat.
Require Import Formulas.
Require Import Substitutions.
Require Import IsFreeForSubst.


(* This rule is maybe redundant, because there are also the 4 quantifier rules
   Lforall/Lexists intro/elim. *)
Definition IsIndependenceOfPremise (prop : nat) : bool :=
  IsLproposition prop
  && IsLimplies prop
  && IsLforall (CoordNat prop 1)
  && IsLimplies (CoordNat (CoordNat prop 1) 2)
  && IsLimplies (CoordNat prop 2)
  && IsLforall (CoordNat (CoordNat prop 2) 2)
  && Nat.eqb (CoordNat (CoordNat (CoordNat prop 1) 2) 1)
             (CoordNat (CoordNat prop 2) 1)
  && Nat.eqb (CoordNat (CoordNat (CoordNat prop 1) 2) 2)
             (CoordNat (CoordNat (CoordNat prop 2) 2) 2)
  && Nat.eqb (CoordNat (CoordNat prop 1) 1)
             (CoordNat (CoordNat (CoordNat prop 2) 2) 1)
  && negb (VarOccursFreeInFormula (CoordNat (CoordNat prop 1) 1)
                                  (CoordNat (CoordNat prop 2) 1)).

(* This is the Lforall introduction rule. It is weaker than taking
   Limplies prop (Lforall n prop)
   as axioms, because it only applies to previously proved props
   (as usual for inference rules). The Limplies above is not satisfied
   in the standard model of arithmetic. *)
Definition IsGeneralization (prop proof : nat) : bool :=
  IsLforall prop
  && FindNat proof (CoordNat prop 2) (LengthNat proof).

(* Search proof for an implication ending in prop, and then search proof again
   for the hypothesis of that implication. Tail recursive. *)
Fixpoint IsModusPonensLoop (prop proof last : nat) : bool :=
  match last with
  | 0 => false
  | S k => (IsLimplies (CoordNat proof k)
           && Nat.eqb prop (CoordNat (CoordNat proof k) 2)
           && FindNat proof (CoordNat (CoordNat proof k) 1) (LengthNat proof))
          || IsModusPonensLoop prop proof k
  end.

Definition IsModusPonens (prop proof : nat) : bool :=
  IsModusPonensLoop prop proof (LengthNat proof).

Lemma IsModusPonens_true : forall prop proof last,
    prod (IsModusPonensLoop prop proof last = true
          -> { n : nat | n < last
                      /\ IsLimplies (CoordNat proof n) = true
                      /\ prop = CoordNat (CoordNat proof n) 2
                      /\ FindNat proof (CoordNat (CoordNat proof n) 1) (LengthNat proof)
                        = true })
         ({ n : nat | n < last
                    /\ IsLimplies (CoordNat proof n) = true
                    /\ prop = CoordNat (CoordNat proof n) 2
                    /\ FindNat proof (CoordNat (CoordNat proof n) 1) (LengthNat proof)
                      = true }
          -> IsModusPonensLoop prop proof last = true).
Proof.
  split.
  - induction last.
    intros H. discriminate.
    intros H. simpl in H.
    destruct (IsModusPonensLoop prop proof last).
    + specialize (IHlast eq_refl) as [n [H0 H1]].
      exists n. split. apply le_S, H0. exact H1.
    + clear IHlast. rewrite Bool.orb_false_r in H.
      exists last. split. apply Nat.le_refl.
      apply andb_prop in H. destruct H.
      apply andb_prop in H. destruct H.
      split. exact H. split.
      apply Nat.eqb_eq in H1. exact H1. exact H0.
  - induction last.
    intros [n [H _]]. inversion H.
    intros [n [H H0]]. simpl.
    apply Nat.le_succ_r in H. destruct H.
    + rewrite IHlast. rewrite Bool.orb_true_r. reflexivity.
      exists n. split. exact H. exact H0.
    + clear IHlast. inversion H. subst n.
      apply Bool.orb_true_intro. left.
      apply andb_true_intro. split.
      apply andb_true_intro. split.
      apply H0. apply Nat.eqb_eq, H0. apply H0.
Qed.

Lemma DoubleParamDecr : forall fg i j,
    0 < LengthNat (diagY fg)
    -> diagMerge (CoordNat (diagX fg) i) (CoordNat (diagY fg) j) < fg.
Proof.
  intros.
  rewrite <- (diagSplitMergeId fg) at 3.
  apply diagMergeIncrLt. apply CoordLe.
  apply CoordLower. apply LengthPositive, H.
Qed. 

(* Precondition: there exists a term t such as g = Subst t v f.
   Compute that term t. *)
Fixpoint FindSubstTermTermLoop (v tu i : nat)
         (rec : forall y : nat, y < tu -> nat) : nat :=
  match i with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | S k => let t := diagX tu in
          let u := diagY tu in
          match le_lt_dec (LengthNat u) 0 with
          | left _ => 0
          | right l =>
          if VarOccursInTerm v (CoordNat t k)
          then rec (diagMerge (CoordNat t k) (CoordNat u k))
                   (DoubleParamDecr tu _ _ l)
          else FindSubstTermTermLoop v tu k rec
          end
  end.
Definition FindSubstTermTermRec (v tu : nat) (rec : forall y : nat, y < tu -> nat) : nat :=
  let t := diagX tu in
  let u := diagY tu in
  match CoordNat t 0 with
  | LvarHead => if Nat.eqb (CoordNat t 1) v then u else 0
  | LopHead => if (Nat.eqb (CoordNat u 0) LopHead
                  && Nat.eqb (CoordNat t 1) (CoordNat u 1)
                  && Nat.eqb (LengthNat t) (LengthNat u))%bool then
                FindSubstTermTermLoop v tu (LengthNat t) rec
              else 0
  | _ => 0
  end.
Definition FindSubstTermTerm (v t u : nat) : nat
  := Fix lt_wf (fun _ => nat) (FindSubstTermTermRec v) (diagMerge t u).

Lemma FindSubstTermTerm_step : forall v t u,
    FindSubstTermTerm v t u
    = FindSubstTermTermRec v (diagMerge t u)
                           (fun (y : nat) (_ : y < diagMerge t u) =>
                              Fix lt_wf (fun _ => nat) (FindSubstTermTermRec v) y).
Proof.
  intros.
  unfold FindSubstTermTerm.
  rewrite Fix_eq. reflexivity.
  intros. unfold FindSubstTermTermRec.
  replace (FindSubstTermTermLoop v x (LengthNat (diagX x)) f)
    with (FindSubstTermTermLoop v x (LengthNat (diagX x)) g).
  reflexivity.
  generalize (LengthNat (diagX x)) as n.
  induction n. reflexivity.
  simpl. destruct n. reflexivity.
  destruct n. reflexivity.
  destruct (le_lt_dec (LengthNat (diagY x)) 0). reflexivity.
  destruct (VarOccursInTerm v (CoordNat (diagX x) (S (S n)))).
  rewrite H. reflexivity. rewrite IHn. reflexivity.
Qed.

Lemma FindSubstTermTerm_var : forall v k u,
    FindSubstTermTerm v (Lvar k) u = if Nat.eqb k v then u else 0.
Proof.
  intros.
  rewrite FindSubstTermTerm_step.
  unfold FindSubstTermTermRec; rewrite diagXMergeId, diagYMergeId.
  unfold Lvar at 1. rewrite CoordConsHeadNat.
  unfold Lvar.
  rewrite CoordConsTailNat, CoordConsHeadNat. reflexivity.
Qed.

Lemma FindSubstTermTerm_zero : forall v t, FindSubstTermTerm v t 0 = 0.
Proof.
  intros v t.
  rewrite FindSubstTermTerm_step.
  unfold FindSubstTermTermRec.
  rewrite diagXMergeId, diagYMergeId.
  destruct (CoordNat t 0). reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. 2: reflexivity.
  destruct (CoordNat t 1 =? v); reflexivity.
Qed.

Lemma FindSubstTermTermLoop_true : forall i j v t u,
    j < pred (pred i)
    -> VarOccursInTerm v (CoordNat t (S (S j))) = true
    -> { k:nat | k < pred (pred i)
              /\ VarOccursInTerm v (CoordNat t (S (S k))) = true
              /\ FindSubstTermTermLoop
                  v (diagMerge t u) i
                  (fun (y : nat) (_ : y < diagMerge t u) =>
                     Fix lt_wf (fun _ => nat) (FindSubstTermTermRec v) y)
                = FindSubstTermTerm v (CoordNat t (S (S k))) (CoordNat u (S (S k))) }.
Proof.
  induction i.
  - intros. exfalso. inversion H.
  - intros. simpl.
    destruct i. exfalso. inversion H.
    destruct i. exfalso. inversion H.
    destruct (VarOccursInTerm v (CoordNat t (S (S i)))) eqn:des.
    + exists i. split.
      apply Nat.le_refl.
      split. exact des.
      rewrite diagXMergeId, diagYMergeId.
      rewrite des.
      destruct (le_lt_dec (LengthNat u) 0).
      2: reflexivity.
      rewrite (CoordNatAboveLength _ u).
      symmetry. apply FindSubstTermTerm_zero.
      inversion l. rewrite H2. apply le_0_n.
    + simpl in H.
      destruct (IHi j v t u) as [x [a b]]. simpl.
      apply Nat.le_succ_r in H.
      destruct H. exact H. exfalso. inversion H.
      rewrite H2 in H0.
      rewrite H0 in des. discriminate des. exact H0.
      exists x. split. apply le_S, a.
      split. apply b. 
      rewrite diagXMergeId, diagYMergeId.
      destruct (le_lt_dec (LengthNat u) 0).
      rewrite (CoordNatAboveLength _ u).
      symmetry. apply FindSubstTermTerm_zero.
      inversion l. rewrite H2. apply le_0_n.
      destruct (VarOccursInTerm v (CoordNat t (S (S i)))).
      discriminate des. apply b.
Qed.

Lemma FindSubstTermTerm_op : forall v o args u,
    FindSubstTermTerm v (Lop o args) u
    = if (Nat.eqb (CoordNat u 0) LopHead
                  && Nat.eqb o (CoordNat u 1)
                  && Nat.eqb (2 + LengthNat args) (LengthNat u))%bool then
        FindSubstTermTermLoop v (diagMerge (Lop o args) u)
                              (2 + LengthNat args)
                              (fun (y : nat) (_ : y < diagMerge _ u) =>
                     Fix lt_wf (fun _ => nat) (FindSubstTermTermRec v) y) 
      else 0.
Proof.
  intros. rewrite FindSubstTermTerm_step.
  unfold FindSubstTermTermRec; rewrite diagXMergeId, diagYMergeId.
  unfold Lop at 1; rewrite CoordConsHeadNat.
  unfold Lop at 1; rewrite CoordConsTailNat, CoordConsHeadNat.
  rewrite LengthLop. reflexivity.
Qed.

(*
Lemma FindSubstTermTerm_varoccur : forall v t u,
    match FindSubstTermTerm v t u with
    | 0 => True
    | S _ => VarOccursInTerm v t = true
    end.
Proof.
  intro v.
  apply (Fix lt_wf (fun t => forall u : nat,
  match FindSubstTermTerm v t u with
  | 0 => True
  | S _ => VarOccursInTerm v t = true
  end)).
  intros t IHt u.
  rewrite FindSubstTermTerm_step. unfold FindSubstTermTermRec.
  rewrite diagXMergeId, diagYMergeId.
  destruct (CoordNat t 0) eqn:headT. trivial.
  destruct n. trivial.
  destruct n. trivial.
  destruct n. trivial.
  destruct n. trivial.
  destruct n. trivial.
  destruct n. trivial.
  destruct n. trivial.
  destruct n.
  rewrite headT.
  shelve.
  destruct n. 2: trivial.
  destruct (CoordNat t 1 =? v) eqn:des. 2: trivial.
  destruct u. trivial.
  unfold VarOccursInTerm.
  rewrite SubstTerm_step.
  unfold TreeFoldNatRec.
  destruct (le_lt_dec (LengthNat t) 0).
  exfalso. rewrite CoordNatAboveLength in headT.
  discriminate headT. exact l.
  unfold SubstTermRec. rewrite headT.
  rewrite des. simpl.
  destruct t. 
  exfalso. discriminate headT.
  reflexivity.
Qed.
*)

Fixpoint FindSubstTermLoop (v f g l : nat) : nat :=
  match l with
  | 0 => 0
  | S k => if VarOccursInTerm v (CoordNat f k)
          then FindSubstTermTerm v (CoordNat f k) (CoordNat g k)
          else FindSubstTermLoop v f g k
  end.

Definition FindSubstTermRec (v fg : nat) (rec : forall y : nat, y < fg -> nat) : nat :=
  let f := diagX fg in
  let g := diagY fg in
  match le_lt_dec (LengthNat g) 0 with
  | left _ => 0
  | right l =>
  if Nat.eqb (CoordNat f 0) (CoordNat g 0) then
  match CoordNat f 0 with
  | LnotHead => rec (diagMerge (CoordNat f 1) (CoordNat g 1))
                   (DoubleParamDecr fg 1 1 l)
  | LimpliesHead
  | LorHead
  | LandHead => if VarOccursFreeInFormula v (CoordNat f 1)
               then rec (diagMerge (CoordNat f 1) (CoordNat g 1))
                        (DoubleParamDecr fg 1 1 l) 
               else rec (diagMerge (CoordNat f 2) (CoordNat g 2))
                        (DoubleParamDecr fg _ _ l)
  | LforallHead
  | LexistsHead => if (Nat.eqb (CoordNat f 1) (CoordNat g 1)
                      && negb (Nat.eqb (CoordNat f 1) v))%bool then
                    (* If Xv is quantified, there will be no substitutions for it *)
                    rec (diagMerge (CoordNat f 2) (CoordNat g 2))
                        (DoubleParamDecr fg _ _ l) 
                  else 0
  | LrelHead => if (Nat.eqb (CoordNat f 1) (CoordNat g 1)
                   && Nat.eqb (LengthNat f) (LengthNat g))%bool then
                 FindSubstTermLoop v (TailNat (TailNat f))
                                   (TailNat (TailNat g)) (LengthNat f - 2)
               else 0
  | _ => 0
  end
  else 0
  end.
Definition FindSubstTerm (v f g : nat) : nat
  := Fix lt_wf (fun _ => nat) (FindSubstTermRec v) (diagMerge f g).

Lemma FindSubstTerm_step : forall v f g,
    FindSubstTerm v f g
    = FindSubstTermRec v (diagMerge f g)
                       (fun (y : nat) (_ : y < diagMerge f g) =>
                          Fix lt_wf (fun _ => nat) (FindSubstTermRec v) y).
Proof.
  intros.
  unfold FindSubstTerm.
  rewrite Fix_eq. reflexivity.
  intros. unfold FindSubstTermRec.
  destruct (le_lt_dec (LengthNat (diagY x)) 0). reflexivity.
  unfold FindSubstTermRec.
  simpl. rewrite H, H. reflexivity.
Qed.

Lemma FindSubstTermLoop_true : forall (l j v f g : nat),
    j < l
    -> VarOccursInTerm v (CoordNat f j) = true
    -> { k:nat | k < l
              /\ VarOccursInTerm v (CoordNat f k) = true
              /\ (FindSubstTermLoop v f g l
                 = FindSubstTermTerm v (CoordNat f k) (CoordNat g k)) }.
Proof.
  induction l.
  - intros. exfalso. inversion H.
  - intros. simpl.
    destruct (VarOccursInTerm v (CoordNat f l)) eqn:des.
    + exists l. split. apply Nat.le_refl.
      split. exact des. reflexivity.
    + assert (j < l).
      { apply Nat.le_succ_r in H. destruct H. exact H. exfalso.
        inversion H.
        rewrite H2 in H0. rewrite H0 in des. discriminate des. }
      destruct (IHl _ v f g H1 H0) as [k IHk].
      exists k. split. apply le_S, IHk.
      split. apply IHk. apply IHk.
Qed.

Lemma FindSubstTermTerm_true : forall t v u,
    IsLterm u = true
    -> VarOccursInTerm v u = true
    -> FindSubstTermTerm v u (SubstTerm t v u) = t.
Proof.
  intros t v.
  apply (Lterm_rect (fun u =>
    VarOccursInTerm v u = true
    -> FindSubstTermTerm v u (SubstTerm t v u) = t)).
  - (* Lvar *)
    intros. rewrite SubstTerm_var.
    rewrite VarOccursInTerm_var in H.
    rewrite Nat.eqb_sym, H.
    rewrite FindSubstTermTerm_var, Nat.eqb_sym, H. reflexivity.
  - (* Lop *)
    intros.
    apply VarOccursInTerm_opHead in H.
    destruct H as [j occur].
    rewrite SubstTerm_op.
    rewrite FindSubstTermTerm_op.
    rewrite LengthLop, SubstTermsLength, Nat.eqb_refl, Bool.andb_true_r.
    unfold Lop at 1.
    rewrite CoordConsHeadNat, Nat.eqb_refl, Bool.andb_true_l.
    unfold Lop at 1.
    rewrite CoordConsTailNat, CoordConsHeadNat.
    rewrite Nat.eqb_refl.
    destruct (FindSubstTermTermLoop_true
                (LengthNat (Lop o terms)) j v (Lop o terms)
                (Lop o (SubstTerms t v terms)))
      as [k [H0 [H1 H2]]].
    apply occur. apply occur.
    rewrite LengthLop in H2.
    rewrite H2. clear H2.
    rewrite LengthLop in H0. 
    rewrite CoordNat_op, CoordNat_op, SubstTermsCoord.
    apply IHterms. 
    exact H0.
    rewrite CoordNat_op in H1. exact H1. exact H0.
    unfold Lop. rewrite CoordConsHeadNat. reflexivity.
Qed.

Lemma FindSubstTerm_not : forall v f g,
    FindSubstTerm v (Lnot f) (Lnot g) = FindSubstTerm v f g.
Proof.
  intros. 
  rewrite FindSubstTerm_step.
  unfold FindSubstTermRec at 1; rewrite diagXMergeId, diagYMergeId.
  destruct (le_lt_dec (LengthNat (Lnot g)) 0).
  exfalso. rewrite LengthLnot in l. inversion l.
  unfold Lnot at 1 2 3.
  rewrite CoordConsHeadNat, CoordConsHeadNat. simpl.
  unfold Lnot.
  rewrite CoordConsTailNat, CoordConsHeadNat.
  rewrite CoordConsTailNat, CoordConsHeadNat. reflexivity.
Qed.

Lemma FindSubstTerm_implies : forall v f g h k,
    FindSubstTerm v (Limplies f g) (Limplies h k)
    = (if VarOccursFreeInFormula v f
       then FindSubstTerm v f h else FindSubstTerm v g k).
Proof.
  intros. 
  rewrite FindSubstTerm_step.
  unfold FindSubstTermRec at 1; rewrite diagXMergeId, diagYMergeId.
  destruct (le_lt_dec (LengthNat (Limplies h k)) 0).
  exfalso. rewrite LengthLimplies in l. inversion l.
  unfold Limplies at 1 2 3.
  rewrite CoordConsHeadNat, CoordConsHeadNat. simpl.
  unfold Limplies.
  rewrite CoordConsTailNat, CoordConsHeadNat.
  rewrite CoordConsTailNat, CoordConsHeadNat. 
  rewrite CoordConsTailNat, CoordConsTailNat, CoordConsHeadNat. 
  rewrite CoordConsTailNat, CoordConsTailNat, CoordConsHeadNat. 
  reflexivity.
Qed.

Lemma FindSubstTerm_or : forall v f g h k,
    FindSubstTerm v (Lor f g) (Lor h k)
    = (if VarOccursFreeInFormula v f
       then FindSubstTerm v f h else FindSubstTerm v g k).
Proof.
  intros. 
  rewrite FindSubstTerm_step.
  unfold FindSubstTermRec at 1; rewrite diagXMergeId, diagYMergeId.
  destruct (le_lt_dec (LengthNat (Lor h k)) 0).
  exfalso. rewrite LengthLor in l. inversion l.
  unfold Lor at 1 2 3.
  rewrite CoordConsHeadNat, CoordConsHeadNat. simpl.
  unfold Lor.
  rewrite CoordConsTailNat, CoordConsHeadNat.
  rewrite CoordConsTailNat, CoordConsHeadNat. 
  rewrite CoordConsTailNat, CoordConsTailNat, CoordConsHeadNat. 
  rewrite CoordConsTailNat, CoordConsTailNat, CoordConsHeadNat. 
  reflexivity.
Qed.

Lemma FindSubstTerm_and : forall v f g h k,
    FindSubstTerm v (Land f g) (Land h k)
    = (if VarOccursFreeInFormula v f
       then FindSubstTerm v f h else FindSubstTerm v g k).
Proof.
  intros. 
  rewrite FindSubstTerm_step.
  unfold FindSubstTermRec at 1; rewrite diagXMergeId, diagYMergeId.
  destruct (le_lt_dec (LengthNat (Land h k)) 0).
  exfalso. rewrite LengthLand in l. inversion l.
  unfold Land at 1 2 3.
  rewrite CoordConsHeadNat, CoordConsHeadNat. simpl.
  unfold Land.
  rewrite CoordConsTailNat, CoordConsHeadNat.
  rewrite CoordConsTailNat, CoordConsHeadNat. 
  rewrite CoordConsTailNat, CoordConsTailNat, CoordConsHeadNat. 
  rewrite CoordConsTailNat, CoordConsTailNat, CoordConsHeadNat. 
  reflexivity.
Qed.

Lemma FindSubstTerm_forall : forall v w f g,
    FindSubstTerm v (Lforall w f) (Lforall w g)
    = (if w =? v then 0 else FindSubstTerm v f g).
Proof.
  intros. 
  rewrite FindSubstTerm_step.
  unfold FindSubstTermRec at 1; rewrite diagXMergeId, diagYMergeId.
  destruct (le_lt_dec (LengthNat (Lforall w g)) 0).
  exfalso. rewrite LengthLforall in l. inversion l.
  unfold Lforall at 1 2 3.
  rewrite CoordConsHeadNat, CoordConsHeadNat. simpl.
  unfold Lforall.
  rewrite CoordConsTailNat, CoordConsHeadNat.
  rewrite CoordConsTailNat, CoordConsHeadNat. 
  rewrite CoordConsTailNat, CoordConsTailNat, CoordConsHeadNat. 
  rewrite CoordConsTailNat, CoordConsTailNat, CoordConsHeadNat. 
  rewrite Nat.eqb_refl. simpl.
  destruct (w =? v); reflexivity.
Qed.

Lemma FindSubstTerm_exists : forall v w f g,
    FindSubstTerm v (Lexists w f) (Lexists w g)
    = (if w =? v then 0 else FindSubstTerm v f g).
Proof.
  intros. 
  rewrite FindSubstTerm_step.
  unfold FindSubstTermRec at 1; rewrite diagXMergeId, diagYMergeId.
  destruct (le_lt_dec (LengthNat (Lexists w g)) 0).
  exfalso. rewrite LengthLexists in l. inversion l.
  unfold Lexists at 1 2 3.
  rewrite CoordConsHeadNat, CoordConsHeadNat. simpl.
  unfold Lexists.
  rewrite CoordConsTailNat, CoordConsHeadNat.
  rewrite CoordConsTailNat, CoordConsHeadNat. 
  rewrite CoordConsTailNat, CoordConsTailNat, CoordConsHeadNat. 
  rewrite CoordConsTailNat, CoordConsTailNat, CoordConsHeadNat. 
  rewrite Nat.eqb_refl. simpl.
  destruct (w =? v); reflexivity.
Qed.

Lemma FindSubstTerm_rel : forall v r terms r2 terms2,
    FindSubstTerm v (Lrel r terms) (Lrel r2 terms2)
    = (if ((r =? r2) && (LengthNat terms =? LengthNat terms2))%bool
       then FindSubstTermLoop v terms terms2 (LengthNat terms)
       else 0).
Proof.
  intros. 
  rewrite FindSubstTerm_step.
  unfold FindSubstTermRec at 1; rewrite diagXMergeId, diagYMergeId.
  destruct (le_lt_dec (LengthNat (Lrel r2 terms2)) 0).
  exfalso. rewrite LengthLrel in l. inversion l.
  unfold Lrel at 1 2 3.
  rewrite CoordConsHeadNat, CoordConsHeadNat. simpl.
  unfold Lrel.
  rewrite CoordConsTailNat, CoordConsHeadNat.
  rewrite CoordConsTailNat, CoordConsHeadNat. 
  rewrite TailConsNat, TailConsNat.
  rewrite TailConsNat, TailConsNat.
  rewrite LengthConsNat, LengthConsNat.
  rewrite LengthConsNat, LengthConsNat.
  simpl.
  rewrite Nat.sub_0_r. reflexivity.
Qed.

Lemma FindSubstTerm_true : forall prop,
    IsLproposition prop = true
    -> forall t v, VarOccursFreeInFormula v prop = true
    -> FindSubstTerm v prop (Subst t v prop) = t.
Proof.
  apply (Lproposition_rect (fun prop => forall t v,
                                VarOccursFreeInFormula v prop = true
                                -> FindSubstTerm v prop (Subst t v prop) = t)).
  - (* Lrel *)
    intros. 
    rewrite Subst_rel, FindSubstTerm_rel, Nat.eqb_refl.
    rewrite SubstTermsLength, Nat.eqb_refl. simpl.
    apply VarOccursFreeInFormula_rel in H.
    destruct H as [j [H H0]].
    pose proof (FindSubstTermLoop_true
                  (LengthNat terms) j v terms
                  (SubstTerms t v terms)
                  H H0) as [k H3].
    destruct H3, H2.
    rewrite H3, SubstTermsCoord. 2: exact H1. 
    apply FindSubstTermTerm_true. apply elemterms, H1. exact H2.
  - (* Lnot *)
    intros.
    rewrite VarOccursFreeInFormula_not in H.
    rewrite Subst_not, FindSubstTerm_not. apply IHprop, H.
  - (* Limplies *)
    intros.
    rewrite Subst_implies, FindSubstTerm_implies.
    rewrite VarOccursFreeInFormula_implies in H.
    destruct (VarOccursFreeInFormula v g) eqn:des.
    apply IHg. exact des.
    apply IHh. exact H.
  - (* Lor *)
    intros.
    rewrite Subst_or, FindSubstTerm_or.
    rewrite VarOccursFreeInFormula_or in H.
    destruct (VarOccursFreeInFormula v g) eqn:des.
    apply IHg. exact des.
    apply IHh. exact H.
  - (* Land *)
    intros.
    rewrite Subst_and, FindSubstTerm_and.
    rewrite VarOccursFreeInFormula_and in H.
    destruct (VarOccursFreeInFormula v g) eqn:des.
    apply IHg. exact des.
    apply IHh. exact H.
  - (* Lforall *)
    intros.
    rewrite VarOccursFreeInFormula_forall in H.
    apply andb_prop in H. destruct H.
    rewrite Subst_forall, FindSubstTerm_forall.
    rewrite Nat.eqb_sym. destruct (v0 =? v). discriminate H.
    apply IHprop, H0.
  - (* Lexists *)
    intros.
    rewrite VarOccursFreeInFormula_exists in H.
    apply andb_prop in H. destruct H.
    rewrite Subst_exists, FindSubstTerm_exists.
    rewrite Nat.eqb_sym. destruct (v0 =? v). discriminate H.
    apply IHprop, H0.
Qed.

(* In the specialization rule, we choose to forbid the capture of variables,
   so that the theorem (forall x, exists y, not(x = y)) does not specialize
   into the absurdity (exists y, not(y = y)).
   This gathers the Lforall elimination and Lexists introduction rules. *)
Definition IsSpecialization (prop : nat) : bool :=
  IsLproposition prop (* This prevents the substitution of t := FindSubstTerm = 0
                         for a free variable. When there is no substitution,
                         it is simply the erasure of the forall quantifier,
                         which is the same as substituting the variable for itself. *) 
  && IsLimplies prop
  && ((IsLforall (CoordNat prop 1)
       && let t := FindSubstTerm (CoordNat (CoordNat prop 1) 1)
                                 (CoordNat (CoordNat prop 1) 2)
                                 (CoordNat prop 2) in
          IsFreeForSubst t (CoordNat (CoordNat prop 1) 1)
                         (CoordNat (CoordNat prop 1) 2)
          && Nat.eqb (CoordNat prop 2)
                     (Subst t (CoordNat (CoordNat prop 1) 1)
                            (CoordNat (CoordNat prop 1) 2)))
      || (IsLexists (CoordNat prop 2)
         && let t := FindSubstTerm (CoordNat (CoordNat prop 2) 1)
                                   (CoordNat (CoordNat prop 2) 2)
                                   (CoordNat prop 1) in
            IsFreeForSubst t (CoordNat (CoordNat prop 2) 1)
                           (CoordNat (CoordNat prop 2) 2)
            && Nat.eqb (CoordNat prop 1)
                       (Subst t (CoordNat (CoordNat prop 2) 1)
                              (CoordNat (CoordNat prop 2) 2)))).

(* Propositional axiom schema of weakening
   X1 -> (X2 -> X1) *)
Definition IsPropAx1 (f : nat) : bool :=
  IsLproposition f
  && IsLimplies f
  && IsLimplies (CoordNat f 2)
  && Nat.eqb (CoordNat f 1) (CoordNat (CoordNat f 2) 2).

(* Propositional axiom schema of modus ponens with a hypothesis X1
   (X1 -> (X2 -> X3)) -> ((X1 -> X2) -> (X1 -> X3)). *)
Definition IsPropAx2 (f : nat) : bool :=
  IsLproposition f
  && IsLimplies f
  && IsLimplies (CoordNat f 1)
  && IsLimplies (CoordNat (CoordNat f 1) 2)
  && IsLimplies (CoordNat f 2)
  && IsLimplies (CoordNat (CoordNat f 2) 1)
  && IsLimplies (CoordNat (CoordNat f 2) 2)
  && Nat.eqb (CoordNat (CoordNat f 1) 1)
             (CoordNat (CoordNat (CoordNat f 2) 1) 1)
  && Nat.eqb (CoordNat (CoordNat f 1) 1)
             (CoordNat (CoordNat (CoordNat f 2) 2) 1)
  && Nat.eqb (CoordNat (CoordNat (CoordNat f 1) 2) 1)
             (CoordNat (CoordNat (CoordNat f 2) 1) 2)
  && Nat.eqb (CoordNat (CoordNat (CoordNat f 1) 2) 2)
             (CoordNat (CoordNat (CoordNat f 2) 2) 2).

(* Propositional axiom schema LnotIntro
   (X1 -> X2) -> ((X1 -> ~X2) -> ~X1) *)
Definition IsPropAx3 (f : nat) : bool :=
  IsLproposition f
  && IsLimplies f
  && IsLimplies (CoordNat f 1)
  && IsLimplies (CoordNat f 2)
  && IsLimplies (CoordNat (CoordNat f 2) 1)
  && IsLnot (CoordNat (CoordNat f 2) 2)
  && IsLnot (CoordNat (CoordNat (CoordNat f 2) 1) 2)
  && Nat.eqb (CoordNat (CoordNat f 1) 1)    (* X1 *)
             (CoordNat (CoordNat (CoordNat f 2) 1) 1)
  && Nat.eqb (CoordNat (CoordNat f 1) 1)    (* X1 *)
             (CoordNat (CoordNat (CoordNat f 2) 2) 1)
  && Nat.eqb (CoordNat (CoordNat f 1) 2)    (* X2 *)
             (CoordNat (CoordNat (CoordNat (CoordNat f 2) 1) 2) 1).

(* IsPropAx4 is the classical logic axiom : ~~X -> X.
   We postpone it to remain constructive here. *)

(* Propositional axiom schema ex falso quodlibet, or LnotElim
   X1 -> (~X1 -> X2) *)
Definition IsPropAx5 (f : nat) : bool :=
  IsLproposition f
  && IsLimplies f
  && IsLimplies (CoordNat f 2)
  && IsLnot (CoordNat (CoordNat f 2) 1)
  && Nat.eqb (CoordNat f 1)
             (CoordNat (CoordNat (CoordNat f 2) 1) 1).

(* Propositional axiom schema LandIntro
   X1 -> (X2 -> (X1 /\ X2)) *)
Definition IsPropAx6 (f : nat) : bool :=
  IsLproposition f
  && IsLimplies f
  && IsLimplies (CoordNat f 2)
  && IsLand (CoordNat (CoordNat f 2) 2)
  && Nat.eqb (CoordNat f 1)
             (CoordNat (CoordNat (CoordNat f 2) 2) 1)
  && Nat.eqb (CoordNat (CoordNat f 2) 1)
             (CoordNat (CoordNat (CoordNat f 2) 2) 2).

(* Propositional axiom schema LandElim1
   (X1 /\ X2) -> X1 *)
Definition IsPropAx7 (f : nat) : bool :=
  IsLproposition f
  && IsLimplies f
  && IsLand (CoordNat f 1)
  && Nat.eqb (CoordNat (CoordNat f 1) 1) (CoordNat f 2).

(* Propositional axiom schema LandElim2
   (X1 /\ X2) -> X2 *)
Definition IsPropAx8 (f : nat) : bool :=
  IsLproposition f
  && IsLimplies f
  && IsLand (CoordNat f 1)
  && Nat.eqb (CoordNat (CoordNat f 1) 2) (CoordNat f 2).

(* Propositional axiom schema LorIntro1
   X1 -> (X1 \/ X2) *)
Definition IsPropAx9 (f : nat) : bool :=
  IsLproposition f
  && IsLimplies f
  && IsLor (CoordNat f 2)
  && Nat.eqb (CoordNat f 1) (CoordNat (CoordNat f 2) 1).

(* Propositional axiom schema LorIntro2
   X2 -> (X1 \/ X2) *)
Definition IsPropAx10 (f : nat) : bool :=
  IsLproposition f
  && IsLimplies f
  && IsLor (CoordNat f 2)
  && Nat.eqb (CoordNat f 1) (CoordNat (CoordNat f 2) 2).

(* Propositional axiom schema LorElim
   (X1 -> X3) -> ((X2 -> X3) -> ((X1 \/ X2) -> X3)) *)
Definition IsPropAx11 (f : nat) : bool :=
  IsLproposition f
  && IsLimplies f
  && IsLimplies (CoordNat f 1)
  && IsLimplies (CoordNat f 2)
  && IsLimplies (CoordNat (CoordNat f 2) 1)
  && IsLimplies (CoordNat (CoordNat f 2) 2)
  && IsLor (CoordNat (CoordNat (CoordNat f 2) 2) 1)
  && Nat.eqb (CoordNat (CoordNat f 1) 1)  (* X1 *)
             (CoordNat (CoordNat (CoordNat (CoordNat f 2) 2) 1) 1)
  && Nat.eqb (CoordNat (CoordNat (CoordNat f 2) 1) 1)  (* X2 *)
             (CoordNat (CoordNat (CoordNat (CoordNat f 2) 2) 1) 2)
  && Nat.eqb (CoordNat (CoordNat f 1) 2)  (* X3 *)
             (CoordNat (CoordNat (CoordNat f 2) 1) 2)
  && Nat.eqb (CoordNat (CoordNat f 1) 2)  (* X3 *)
             (CoordNat (CoordNat (CoordNat f 2) 2) 2).


Definition IsPropositionalAxiom (f : nat) : bool :=
  IsPropAx1 f
  || IsPropAx2 f
  || IsPropAx3 f
  || IsPropAx5 f
  || IsPropAx6 f
  || IsPropAx7 f
  || IsPropAx8 f
  || IsPropAx9 f
  || IsPropAx10 f
  || IsPropAx11 f.

Lemma Ax1IsPropAx : forall f, IsPropAx1 f = true -> IsPropositionalAxiom f = true.
Proof.
  intros. unfold IsPropositionalAxiom.
  do 9 (apply Bool.orb_true_intro; left).
  exact H.
Qed.

Lemma Ax1IsAx1 : forall f g,
    IsLproposition f = true
    -> IsLproposition g = true
    -> IsPropAx1 (Limplies f (Limplies g f)) = true.
Proof.
  intros.
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  rewrite IsLproposition_implies.
  apply andb_true_intro. split. exact H.
  rewrite IsLproposition_implies.
  apply andb_true_intro. split. exact H0. exact H.
  apply LimpliesIsImplies.
  rewrite CoordNat_implies_2.
  apply LimpliesIsImplies.
  rewrite CoordNat_implies_1.
  rewrite CoordNat_implies_2, CoordNat_implies_2.
  apply Nat.eqb_refl.
Qed.

Lemma Ax2IsPropAx : forall f, IsPropAx2 f = true -> IsPropositionalAxiom f = true.
Proof.
  intros. unfold IsPropositionalAxiom.
  do 8 (apply Bool.orb_true_intro; left).
  apply Bool.orb_true_intro; right.
  exact H.
Qed.

Lemma Ax2IsAx2 : forall f g h,
    IsLproposition f = true
    -> IsLproposition g = true
    -> IsLproposition h = true
    -> IsPropAx2 (Limplies (Limplies f (Limplies g h))
                          (Limplies (Limplies f g) (Limplies f h))) = true.
Proof.
  intros.
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  rewrite IsLproposition_implies.
  apply andb_true_intro. split.
  rewrite IsLproposition_implies.
  apply andb_true_intro. split. exact H.
  rewrite IsLproposition_implies.
  apply andb_true_intro. split. exact H0. exact H1.
  rewrite IsLproposition_implies.
  apply andb_true_intro. split.
  rewrite IsLproposition_implies.
  apply andb_true_intro. split. exact H. exact H0.
  rewrite IsLproposition_implies.
  apply andb_true_intro. split. exact H. exact H1.
  apply LimpliesIsImplies.
  rewrite CoordNat_implies_1.
  apply LimpliesIsImplies.
  rewrite CoordNat_implies_1, CoordNat_implies_2.
  apply LimpliesIsImplies.
  rewrite CoordNat_implies_2.
  apply LimpliesIsImplies.
  rewrite CoordNat_implies_2, CoordNat_implies_1.
  apply LimpliesIsImplies.
  rewrite CoordNat_implies_2, CoordNat_implies_2.
  apply LimpliesIsImplies.
  rewrite CoordNat_implies_1, CoordNat_implies_1.
  rewrite CoordNat_implies_2, CoordNat_implies_1, CoordNat_implies_1.
  apply Nat.eqb_refl.
  rewrite CoordNat_implies_1, CoordNat_implies_1.
  rewrite CoordNat_implies_2, CoordNat_implies_2, CoordNat_implies_1.
  apply Nat.eqb_refl.
  rewrite CoordNat_implies_1, CoordNat_implies_2.
  rewrite CoordNat_implies_1, CoordNat_implies_2, CoordNat_implies_1.
  rewrite CoordNat_implies_2.
  apply Nat.eqb_refl.
  rewrite CoordNat_implies_1, CoordNat_implies_2.
  rewrite CoordNat_implies_2, CoordNat_implies_2.
  rewrite CoordNat_implies_2, CoordNat_implies_2.
  apply Nat.eqb_refl.
Qed.

Lemma Ax3IsPropAx : forall f, IsPropAx3 f = true -> IsPropositionalAxiom f = true.
Proof.
  intros. unfold IsPropositionalAxiom.
  do 7 (apply Bool.orb_true_intro; left).
  apply Bool.orb_true_intro; right.
  exact H.
Qed.

Lemma Ax3IsAx3 : forall f g,
    IsLproposition f = true
    -> IsLproposition g = true
    -> IsPropAx3 (Limplies (Limplies f g)
                          (Limplies (Limplies f (Lnot g)) (Lnot f))) = true.
Proof.
  intros.
  unfold IsPropAx3; rewrite CoordNat_implies_2, CoordNat_implies_1.
  rewrite CoordNat_implies_2, CoordNat_implies_1.
  rewrite CoordNat_implies_2, CoordNat_implies_1.
  rewrite CoordNat_implies_2, CoordNat_implies_1.
  rewrite CoordNat_not_1, CoordNat_not_1.
  rewrite Nat.eqb_refl, Nat.eqb_refl.
  do 4 rewrite LimpliesIsImplies.
  rewrite LnotIsNot, LnotIsNot.
  do 4 rewrite IsLproposition_implies.
  rewrite IsLproposition_not, IsLproposition_not, H, H0.
  reflexivity.
Qed.

Lemma Ax5IsPropAx : forall f, IsPropAx5 f = true -> IsPropositionalAxiom f = true.
Proof.
  intros. unfold IsPropositionalAxiom.
  do 6 (apply Bool.orb_true_intro; left).
  apply Bool.orb_true_intro. right.
  exact H.
Qed.

Lemma Ax5IsAx5 : forall f g : nat,
    IsLproposition f = true
    -> IsLproposition g = true
    -> IsPropAx5 (Limplies f (Limplies (Lnot f) g)) = true.
Proof.
  intros. unfold IsPropAx5.
  rewrite CoordNat_implies_1, CoordNat_implies_2, CoordNat_implies_1.
  rewrite CoordNat_not_1.
  rewrite LimpliesIsImplies, LimpliesIsImplies, LnotIsNot, Nat.eqb_refl.
  rewrite IsLproposition_implies, IsLproposition_implies, IsLproposition_not.
  rewrite H, H0. reflexivity.
Qed.

Lemma Ax6IsPropAx : forall f, IsPropAx6 f = true -> IsPropositionalAxiom f = true.
Proof.
  intros. unfold IsPropositionalAxiom.
  do 5 (apply Bool.orb_true_intro; left).
  apply Bool.orb_true_intro. right.
  exact H.
Qed.

Lemma Ax6IsAx6 : forall f g : nat,
    IsLproposition f = true
    -> IsLproposition g = true
    -> IsPropAx6 (Limplies f (Limplies g (Land f g))) = true.
Proof.
  intros.
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  rewrite IsLproposition_implies.
  apply andb_true_intro. split. exact H.
  rewrite IsLproposition_implies.
  apply andb_true_intro. split. exact H0.
  rewrite IsLproposition_and.
  apply andb_true_intro. split. exact H. exact H0.
  apply LimpliesIsImplies.
  rewrite CoordNat_implies_2. apply LimpliesIsImplies.
  rewrite CoordNat_implies_2, CoordNat_implies_2. apply LandIsAnd.
  rewrite CoordNat_implies_1, CoordNat_implies_2.
  rewrite CoordNat_implies_2, CoordNat_and_1.
  apply Nat.eqb_refl.
  rewrite CoordNat_implies_2, CoordNat_implies_2.
  rewrite CoordNat_implies_1, CoordNat_and_2.
  apply Nat.eqb_refl.
Qed.

Lemma Ax7IsPropAx : forall f, IsPropAx7 f = true -> IsPropositionalAxiom f = true.
Proof.
  intros. unfold IsPropositionalAxiom.
  do 4 (apply Bool.orb_true_intro; left).
  apply Bool.orb_true_intro. right.
  exact H.
Qed.

Lemma Ax7IsAx7 : forall f g : nat,
    IsLproposition f = true
    -> IsLproposition g = true
    -> IsPropAx7 (Limplies (Land f g) f) = true.
Proof.
  intros. unfold IsPropAx7.
  rewrite CoordNat_implies_2, CoordNat_implies_1.
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  rewrite IsLproposition_implies.
  apply andb_true_intro. split.
  rewrite IsLproposition_and.
  apply andb_true_intro. split.
  exact H. exact H0. exact H.
  apply LimpliesIsImplies.
  apply LandIsAnd.
  apply Nat.eqb_eq.
  unfold Land.
  rewrite CoordConsTailNat.
  rewrite CoordConsHeadNat. reflexivity.
Qed.

Lemma Ax8IsPropAx : forall f, IsPropAx8 f = true -> IsPropositionalAxiom f = true.
Proof.
  intros. unfold IsPropositionalAxiom.
  do 3 (apply Bool.orb_true_intro; left).
  apply Bool.orb_true_intro. right.
  exact H.
Qed.

Lemma Ax8IsAx8 : forall f g : nat,
    IsLproposition f = true
    -> IsLproposition g = true
    -> IsPropAx8 (Limplies (Land f g) g) = true.
Proof.
  intros.
  unfold IsPropAx8.
  rewrite CoordNat_implies_2, CoordNat_implies_1.
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  rewrite IsLproposition_implies.
  apply andb_true_intro. split.
  rewrite IsLproposition_and.
  apply andb_true_intro. split.
  exact H. exact H0. exact H0.
  apply LimpliesIsImplies.
  apply LandIsAnd.
  rewrite CoordNat_and_2.
  apply Nat.eqb_refl.
Qed.

Lemma Ax9IsPropAx : forall f, IsPropAx9 f = true -> IsPropositionalAxiom f = true.
Proof.
  intros. unfold IsPropositionalAxiom.
  do 2 (apply Bool.orb_true_intro; left).
  apply Bool.orb_true_intro. right.
  exact H.
Qed.

Lemma Ax9IsAx9 : forall f g : nat,
    IsLproposition f = true
    -> IsLproposition g = true
    -> IsPropAx9 (Limplies f (Lor f g)) = true.
Proof.
  intros.
  unfold IsPropAx9.
  rewrite CoordNat_implies_2, CoordNat_implies_1, CoordNat_or_1.
  rewrite IsLproposition_implies, LimpliesIsImplies, IsLproposition_or, H, H0.
  rewrite LorIsOr, Nat.eqb_refl.
  reflexivity.
Qed.

Lemma Ax10IsPropAx : forall f, IsPropAx10 f = true -> IsPropositionalAxiom f = true.
Proof.
  intros. unfold IsPropositionalAxiom.
  apply Bool.orb_true_intro; left.
  apply Bool.orb_true_intro. right.
  exact H.
Qed.

Lemma Ax10IsAx10 : forall f g : nat,
    IsLproposition f = true
    -> IsLproposition g = true
    -> IsPropAx10 (Limplies g (Lor f g)) = true.
Proof.
  intros.
  unfold IsPropAx10.
  rewrite CoordNat_implies_2, CoordNat_implies_1, CoordNat_or_2.
  rewrite IsLproposition_implies, LimpliesIsImplies, IsLproposition_or, H, H0.
  rewrite LorIsOr, Nat.eqb_refl.
  reflexivity.
Qed.

Lemma Ax11IsPropAx : forall f, IsPropAx11 f = true -> IsPropositionalAxiom f = true.
Proof.
  intros. unfold IsPropositionalAxiom.
  apply Bool.orb_true_intro. right. exact H.
Qed.

Lemma Ax11IsAx11 : forall f g h : nat,
    IsLproposition f = true
    -> IsLproposition g = true
    -> IsLproposition h = true
    -> IsPropAx11 (Limplies (Limplies f h)
                           (Limplies (Limplies g h) (Limplies (Lor f g) h))) = true.
Proof.
  intros. unfold IsPropAx11.
  rewrite CoordNat_implies_2, CoordNat_implies_2.
  rewrite CoordNat_implies_1, CoordNat_implies_1.
  rewrite CoordNat_implies_1, CoordNat_implies_1.
  rewrite CoordNat_implies_2, CoordNat_implies_2.
  rewrite CoordNat_implies_1, CoordNat_implies_2.
  rewrite CoordNat_or_1, CoordNat_or_2.
  do 3 rewrite Nat.eqb_refl.
  do 5 rewrite IsLproposition_implies.
  rewrite IsLproposition_or, H, H0, H1.
  do 5 rewrite LimpliesIsImplies.
  rewrite LorIsOr.
  reflexivity.
Qed.

(* terms1_0=terms2_0 /\ ... /\ terms1_l=terms2_l *)
Fixpoint EqTerms (terms1 terms2 l : nat) { struct l } : nat :=
  match l with
  | O => Leq (CoordNat terms1 0) (CoordNat terms2 0)
  | S k => Land (EqTerms terms1 terms2 k)
               (Leq (CoordNat terms1 l) (CoordNat terms2 l))
  end.

(* X0 :: X2 :: ... :: X(2l-2) *)
Definition EvenVars (start l : nat) : nat :=
  MapNat (fun n => Lvar (start + 2*n)) (RangeNat 0 l).

(* VarEqual -> (r(X0,...,X2n) <-> r(X1,...X2n+1)) *)
Definition IsEqualityRelationAxiom (f : nat) : bool :=
  let arity := LengthNat (CoordNat (CoordNat (CoordNat f 2) 1) 1) - 2 in
  IsLimplies f
  && Nat.leb 1 arity
  && Nat.eqb (CoordNat f 1)
             (EqTerms (EvenVars 0 arity) (EvenVars 1 arity) (pred arity))
  && Nat.eqb (CoordNat f 2)
             (Lequiv (Lrel (CoordNat (CoordNat (CoordNat (CoordNat f 2) 1) 1) 1)
                           (EvenVars 0 arity))
                     (Lrel (CoordNat (CoordNat (CoordNat (CoordNat f 2) 1) 1) 1)
                           (EvenVars 1 arity))).

(* We could have taken LeqElim as axiom instead, but it is more difficult
   to get convinced of its truth, and it must avoid variable captures. *)
Definition IsEqualityAxiom (f : nat) : bool :=
  Nat.eqb f (Leq (Lvar 0) (Lvar 0))
  || Nat.eqb f (Limplies (Leq (Lvar 0) (Lvar 1)) (Leq (Lvar 1) (Lvar 0)))
  || Nat.eqb f (Limplies (Land (Leq (Lvar 0) (Lvar 1)) (Leq (Lvar 1) (Lvar 2)))
                        (Leq (Lvar 0) (Lvar 2)))
  || (let arity := LengthNat (CoordNat (CoordNat f 2) 2) - 2 in
    IsLimplies f
     && Nat.leb 1 arity
     && Nat.eqb (CoordNat f 1)
                (EqTerms (EvenVars 0 arity) (EvenVars 1 arity) (pred arity))
     && Nat.eqb (CoordNat f 2)
                (Leq (Lop (CoordNat (CoordNat (CoordNat f 2) 2) 1)
                          (EvenVars 0 arity))
                     (Lop (CoordNat (CoordNat (CoordNat f 2) 2) 1)
                          (EvenVars 1 arity))))
  || IsEqualityRelationAxiom f.

Definition IsExistsElim (f : nat) : bool :=
  IsLproposition f
  && IsLimplies f
  && IsLexists (CoordNat f 1)
  && IsLimplies (CoordNat f 2)
  && IsLforall (CoordNat (CoordNat f 2) 1)
  && IsLimplies (CoordNat (CoordNat (CoordNat f 2) 1) 2)
  && Nat.eqb (CoordNat (CoordNat (CoordNat (CoordNat f 2) 1) 2) 1)
             (CoordNat (CoordNat f 1) 2)
  && Nat.eqb (CoordNat (CoordNat (CoordNat (CoordNat f 2) 1) 2) 2)
             (CoordNat (CoordNat f 2) 2)
  && Nat.eqb (CoordNat (CoordNat (CoordNat f 2) 1) 1)
             (CoordNat (CoordNat f 1) 1)
  && negb (VarOccursFreeInFormula (CoordNat (CoordNat (CoordNat f 2) 1) 1)
                                  (CoordNat (CoordNat f 2) 2)).

(* The 4 quantifier rules Lforall/Lexists intro/elim, and the independence
   of premise. *)
Definition IsQuantifierAxiom (prop proof : nat) : bool :=
  IsGeneralization prop proof
  || IsSpecialization prop
  || IsIndependenceOfPremise prop
  || IsExistsElim prop.

(* Compute whether prop is a consequence of the axioms and of proof,
   considered as a list of additional axioms. *)
Definition IsProofStep (IsAxiom : nat -> bool) (prop proof : nat) : bool :=
  (IsAxiom prop && IsLproposition prop)
  || IsPropositionalAxiom prop
  || IsEqualityAxiom prop
  || IsModusPonens prop proof
  || IsQuantifierAxiom prop proof.

(* Precondition: i = LengthNat proof.
   Compute whether proof is correct. *)
Fixpoint IsProofLoop (IsAxiom : nat -> bool) (proof i : nat) : bool :=
  match i with
  | O => true
  | S j => IsProofStep IsAxiom (CoordNat proof 0) (TailNat proof)
          && IsProofLoop IsAxiom (TailNat proof) j
  end.

Definition IsProof (IsAxiom : nat -> bool) (prop proof : nat) : bool :=
   Nat.eqb prop (CoordNat proof 0)
   && Nat.leb 1 (LengthNat proof)
   && IsProofLoop IsAxiom proof (LengthNat proof).

(* Sigma_1 arithmetic formula expressing provability.
   - When proved by Heyting arithmetic it is faithful, because true in
     all models of arithmetic, in particular in Coq's standard model of arithmetic.
     Then Coq's normalization computes the underlying proof of prop.
   - When proved by Peano arithmetic it is slightly less faithful, because
     the doubly negated model of arithmetic and Markov's principle must be used
     to compute the underlying proof of prop, for example by brute force search
     on all natural numbers.
   - When true in ZFC's standard model of arithmetic (the first limit ordinal),
     it is up to the reader to judge whether it constitutes of a proof of
     termination for the brute force search. *)
Definition IsProved (IsAxiom : nat -> bool) (prop : nat) : Prop :=
  exists proof : nat, IsProof IsAxiom prop proof = true.

Lemma IsProvedT : forall IsAxiom prop,
    IsProved IsAxiom prop -> { proof : nat | IsProof IsAxiom prop proof = true }.
Proof.
  intros IsAxiom prop proofF.
  apply constructive_indefinite_ground_description_nat in proofF.
  exact proofF. intro n.
  destruct (IsProof IsAxiom prop n). left. reflexivity. right. discriminate.
Qed.

(* Inconsistency is a positive statement meaning that IsAxiom is broken.
   When it happens, IsAxiom proves all propositions by FalseElim. *)
Definition IsInconsistent (IsAxiom : nat -> bool) : Prop :=
  IsProved IsAxiom (Lnot (Leq (Lvar 0) (Lvar 0))).

Definition IsConsistent (IsAxiom : nat -> bool) : Prop := ~IsInconsistent IsAxiom.

Lemma IsProofLoop_spec : forall IsAxiom k proof,
    IsProofLoop IsAxiom proof k = true
    <-> (forall i, i < k -> IsProofStep IsAxiom (CoordNat proof i)
                                (NthTailNat proof (S i)) = true).
Proof.
  intros IsAxiom. induction k.
  - simpl. split. intros. inversion H0.
    intros. reflexivity.
  - split.
    + intros. simpl.
      simpl in H.
      specialize (IHk (TailNat proof)) as [IHk _].
      apply andb_prop in H. destruct H.
      destruct i. exact H.
      specialize (IHk H1 i). 
      rewrite CoordTailNat in IHk. apply IHk.
      apply le_S_n, H0.
    + intro H. simpl. apply andb_true_intro. split.
      apply H. apply le_n_S, le_0_n.
      apply (IHk (TailNat proof)).
      intros i H0. apply (H (S i)). apply le_n_S, H0.
Qed. 

Lemma IsProofLoop_cons : forall IsAxiom prop proof,
    IsProofLoop IsAxiom (ConsNat prop proof) (S (LengthNat proof))
    = (IsProofStep IsAxiom prop proof
       && IsProofLoop IsAxiom proof (LengthNat proof))%bool.
Proof.
  intros. simpl.
  rewrite CoordConsHeadNat, TailConsNat.
  reflexivity.
Qed.

Lemma IsProofLoop_propax : forall IsAxiom prop proof,
    IsPropositionalAxiom prop = true
    -> IsProofLoop IsAxiom (ConsNat prop proof) (LengthNat (ConsNat prop proof))
      = IsProofLoop IsAxiom proof (LengthNat proof).
Proof.
  intros. rewrite LengthConsNat. simpl.
  unfold IsProofStep.
  rewrite Bool.orb_true_intro.
  rewrite TailConsNat. reflexivity.
  left.
  rewrite CoordConsHeadNat.
  rewrite H. rewrite Bool.orb_true_r. reflexivity.
Qed.

Lemma IsProofLoop_eqax : forall IsAxiom prop proof,
    IsEqualityAxiom prop = true
    -> IsProofLoop IsAxiom (ConsNat prop proof) (LengthNat (ConsNat prop proof))
      = IsProofLoop IsAxiom proof (LengthNat proof).
Proof.
  intros. rewrite LengthConsNat. simpl.
  unfold IsProofStep.
  rewrite Bool.orb_true_intro.
  rewrite TailConsNat. reflexivity.
  left.
  rewrite Bool.orb_true_intro.
  reflexivity.
  left.
  rewrite Bool.orb_true_intro.
  reflexivity.
  right.
  rewrite CoordConsHeadNat.
  exact H.
Qed.

Lemma IsProofLoop_mp : forall IsAxiom prop proof,
    IsModusPonens prop proof = true
    -> IsProofLoop IsAxiom (ConsNat prop proof) (LengthNat (ConsNat prop proof))
      = IsProofLoop IsAxiom proof (LengthNat proof).
Proof.
  intros. rewrite LengthConsNat. simpl.
  unfold IsProofStep.
  rewrite Bool.orb_true_intro.
  rewrite TailConsNat. reflexivity.
  left.
  rewrite Bool.orb_true_intro.
  reflexivity.
  right.
  rewrite TailConsNat, CoordConsHeadNat.
  exact H.
Qed.

Lemma IsProofLoop_specialization : forall IsAxiom prop proof,
    IsSpecialization prop = true
    -> IsProofLoop IsAxiom (ConsNat prop proof) (LengthNat (ConsNat prop proof))
      = IsProofLoop IsAxiom proof (LengthNat proof).
Proof.
  intros. rewrite LengthConsNat. simpl.
  unfold IsProofStep.
  rewrite Bool.orb_true_intro.
  rewrite TailConsNat. reflexivity.
  right.
  apply Bool.orb_true_intro.
  left.
  rewrite Bool.orb_true_intro.
  reflexivity.
  left.
  rewrite Bool.orb_true_intro.
  reflexivity.
  right.
  rewrite CoordConsHeadNat.
  exact H.
Qed.

Lemma IsProofLoop_generalization : forall IsAxiom prop proof,
    IsGeneralization prop proof = true
    -> IsProofLoop IsAxiom (ConsNat prop proof) (LengthNat (ConsNat prop proof))
      = IsProofLoop IsAxiom proof (LengthNat proof).
Proof.
  intros. rewrite LengthConsNat. simpl.
  unfold IsProofStep.
  rewrite Bool.orb_true_intro.
  rewrite TailConsNat. reflexivity.
  right.
  apply Bool.orb_true_intro.
  left.
  rewrite Bool.orb_true_intro.
  reflexivity.
  left.
  rewrite Bool.orb_true_intro.
  reflexivity.
  left.
  rewrite CoordConsHeadNat, TailConsNat.
  exact H.
Qed.

Lemma PropAxIsLproposition : forall (prop:nat),
    IsPropositionalAxiom prop = true
    -> IsLproposition prop = true.
Proof.
  intros prop H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  apply Bool.orb_prop in H; destruct H.
  - do 3 (apply andb_prop in H; destruct H).
    exact H.
  - do 10 (apply andb_prop in H; destruct H).
    exact H.
  - do 9 (apply andb_prop in H; destruct H).
    exact H.
  - do 4 (apply andb_prop in H; destruct H).
    exact H.
  - do 5 (apply andb_prop in H; destruct H).
    exact H.
  - do 3 (apply andb_prop in H; destruct H).
    exact H.
  - do 3 (apply andb_prop in H; destruct H).
    exact H.
  - do 3 (apply andb_prop in H; destruct H).
    exact H.
  - do 3 (apply andb_prop in H; destruct H).
    exact H.
  - do 10 (apply andb_prop in H; destruct H).
    exact H.
Qed.

Lemma EqTermsIsLproposition : forall l terms1 terms2:nat,
    (forall n, n<=l -> IsLterm (CoordNat terms1 n) = true
                /\ IsLterm (CoordNat terms2 n) = true)
    -> IsLproposition (EqTerms terms1 terms2 l) = true.
Proof.
  induction l.
  - intros. simpl. unfold Leq. rewrite IsLproposition_rel2.
    apply andb_true_intro; split; apply (H 0 (Nat.le_refl 0)).
  - intros. simpl. rewrite IsLproposition_and.
    apply andb_true_intro; split. apply IHl.
    intros. apply H. apply (Nat.le_trans _ l _ H0).
    apply le_S, Nat.le_refl.
    unfold Leq. rewrite IsLproposition_rel2.
    apply andb_true_intro; split; apply H, Nat.le_refl.
Qed.

Lemma CoordEvenVarsNat : forall l start k : nat,
    k < l
    -> CoordNat (EvenVars start l) k = Lvar (start + 2*k).
Proof.
  intros.
  unfold EvenVars. rewrite CoordMapNat, CoordRangeNat. reflexivity.
  exact H. rewrite LengthRangeNat. exact H.
Qed.

Lemma LengthEvenVarsNat : forall l start : nat, LengthNat (EvenVars start l) = l.
Proof.
  intros. unfold EvenVars. rewrite LengthMapNat, LengthRangeNat. reflexivity.
Qed.

Lemma EvenVarsTruncated : forall l start,
    NthTailNat (EvenVars start l) l = 0.
Proof. 
  intros. 
  rewrite <- (LengthRangeNat l 0) at 2.
  unfold EvenVars.
  rewrite MapNatTruncated. rewrite LengthRangeNat.
  generalize 0 at 1.
  induction l. reflexivity. simpl. intro k.
  rewrite TailConsNat. apply IHl.
Qed.

Lemma EqualityAxiomIsLproposition : forall f,
    IsEqualityAxiom f = true
    -> IsLproposition f = true.
Proof.
  intros.
  apply Bool.orb_prop in H. destruct H.
  apply Bool.orb_prop in H. destruct H.
  apply Bool.orb_prop in H. destruct H.
  apply Bool.orb_prop in H. destruct H.
  - apply Nat.eqb_eq in H. rewrite H.
    unfold Leq. rewrite IsLproposition_rel2.
    apply andb_true_intro. split.
    apply IsLterm_var. apply IsLterm_var.
  - apply Nat.eqb_eq in H. rewrite H.
    rewrite IsLproposition_implies.
    apply andb_true_intro. split.
    unfold Leq. rewrite IsLproposition_rel2.
    apply andb_true_intro. split.
    apply IsLterm_var. apply IsLterm_var.
    unfold Leq. rewrite IsLproposition_rel2.
    apply andb_true_intro. split.
    apply IsLterm_var. apply IsLterm_var.
  - apply Nat.eqb_eq in H. rewrite H.
    rewrite IsLproposition_implies.
    apply andb_true_intro. split.
    rewrite IsLproposition_and.
    apply andb_true_intro. split.
    unfold Leq. rewrite IsLproposition_rel2.
    apply andb_true_intro. split.
    apply IsLterm_var. apply IsLterm_var.
    unfold Leq. rewrite IsLproposition_rel2.
    apply andb_true_intro. split.
    apply IsLterm_var. apply IsLterm_var.
    unfold Leq. rewrite IsLproposition_rel2.
    apply andb_true_intro. split.
    apply IsLterm_var. apply IsLterm_var.
  - (* Lop equality *)
    apply andb_prop in H. destruct H.
    apply andb_prop in H. destruct H.
    apply andb_prop in H. destruct H.
    apply Nat.eqb_eq in H.
    apply Nat.eqb_eq in H0.
    apply Nat.eqb_eq in H1.
    apply Nat.leb_le in H2.
    rewrite H, IsLproposition_implies.
    apply andb_true_intro. split.
    rewrite H1. apply EqTermsIsLproposition.
    intros n H3.
    rewrite CoordEvenVarsNat, CoordEvenVarsNat.
    rewrite IsLterm_var, IsLterm_var. split; reflexivity.
    destruct (LengthNat (CoordNat (CoordNat f 2) 2) - 2). inversion H2.
    apply le_n_S, H3.
    destruct (LengthNat (CoordNat (CoordNat f 2) 2) - 2). inversion H2.
    apply le_n_S, H3.
    rewrite H0. unfold Leq. rewrite IsLproposition_rel2.
    apply andb_true_intro; split.
    apply LopIsTerm. intros k H3.
    rewrite LengthEvenVarsNat in H3.
    rewrite CoordEvenVarsNat.
    apply IsLterm_var. exact H3.
    rewrite LengthEvenVarsNat. apply EvenVarsTruncated.
    apply LopIsTerm. intros k H3.
    rewrite LengthEvenVarsNat in H3.
    rewrite CoordEvenVarsNat.
    apply IsLterm_var. exact H3.
    rewrite LengthEvenVarsNat. apply EvenVarsTruncated.
  - (* Lrel equivalence *)
    apply andb_prop in H. destruct H.
    apply andb_prop in H. destruct H.
    apply andb_prop in H. destruct H.
    apply Nat.eqb_eq in H.
    apply Nat.eqb_eq in H0.
    apply Nat.eqb_eq in H1.
    apply Nat.leb_le in H2.
    rewrite H, IsLproposition_implies.
    apply andb_true_intro. split.
    rewrite H1. apply EqTermsIsLproposition.
    intros n H3.
    rewrite CoordEvenVarsNat, CoordEvenVarsNat.
    rewrite IsLterm_var, IsLterm_var. split; reflexivity.
    destruct (LengthNat (CoordNat (CoordNat (CoordNat f 2) 1) 1) - 2). inversion H2.
    apply le_n_S, H3.
    destruct (LengthNat (CoordNat (CoordNat (CoordNat f 2) 1) 1) - 2). inversion H2.
    apply le_n_S, H3.
    rewrite H0. rewrite IsLproposition_equiv.
    apply andb_true_intro; split.
    apply IsLproposition_rel.
    split.
    rewrite LengthEvenVarsNat. apply EvenVarsTruncated.
    intros.
    rewrite CoordEvenVarsNat.
    apply IsLterm_var. rewrite LengthEvenVarsNat in H3. exact H3.
    apply IsLproposition_rel.
    split.
    rewrite LengthEvenVarsNat. apply EvenVarsTruncated.
    intros.
    rewrite CoordEvenVarsNat.
    apply IsLterm_var. rewrite LengthEvenVarsNat in H3. exact H3.
Qed.

Lemma ProofLoopIsLproposition : forall IsAxiom l (proof:nat),
    l = LengthNat proof
    -> IsProofLoop IsAxiom proof l = true
    -> forall i:nat, i < LengthNat proof
    -> IsLproposition (CoordNat proof i) = true.
Proof.
  intro IsAxiom.
  induction l.
  - intros. exfalso.
    rewrite <- H in H1. inversion H1.
  - intros proof lenproof proofloop i H.
    rewrite <- lenproof in H.
    assert (l = LengthNat (TailNat proof)) as lentail.
    { rewrite LengthTailNat. destruct (LengthNat proof).
      discriminate. simpl. inversion lenproof. reflexivity. }
    subst l.
    simpl in proofloop.
    apply andb_prop in proofloop.
    destruct proofloop as [proofstep proofloop].
    specialize (IHl (TailNat proof) eq_refl proofloop).
    destruct i.
    + clear H.
      apply Bool.orb_prop in proofstep.
      destruct proofstep as [H | quantifier].
      apply Bool.orb_prop in H. destruct H as [H | modus].
      apply Bool.orb_prop in H. destruct H as [H | eqax].
      apply Bool.orb_prop in H. destruct H.
      apply andb_prop in H. apply H.
      apply PropAxIsLproposition, H.
      apply EqualityAxiomIsLproposition, eqax.
      (* modus ponens, use induction hypothesis on the implication formula *)
      apply IsModusPonens_true in modus.
      destruct modus as [imp [lenimp [isimp [H modus]]]].
      apply FindNat_true in modus.
      destruct modus as [hyp [H4 modus]].
      specialize (IHl imp lenimp).
      apply Nat.eqb_eq in isimp.
      rewrite isimp, IsLproposition_implies in IHl.
      apply andb_prop in IHl.
      rewrite H.
      apply IHl.
      (* Quantifier axioms *)
      apply Bool.orb_prop in quantifier. destruct quantifier as [H | exelim].
      apply Bool.orb_prop in H. destruct H as [H | premise].
      apply Bool.orb_prop in H. destruct H as [gen | special].
      apply andb_prop in gen. destruct gen as [all gen].
      apply FindNat_true in gen. destruct gen as [p gen].
      apply Nat.eqb_eq in all. rewrite all, IsLproposition_forall.
      destruct gen. rewrite H0. apply IHl. exact H.
      do 2 (apply andb_prop in special; destruct special as [special _]).
      exact special.
      do 9 (apply andb_prop in premise; destruct premise as [premise _]).
      exact premise.
      do 9 (apply andb_prop in exelim; destruct exelim as [exelim _]).
      exact exelim.
    + (* use induction hypothesis *)
      specialize (IHl i).
      rewrite CoordTailNat in IHl. apply IHl.
      rewrite LengthTailNat.
      destruct (LengthNat proof). discriminate.
      inversion lenproof. subst n.
      simpl. apply le_S_n. exact H.
Qed.

Lemma IsProvedIsLproposition : forall IsAxiom (prop:nat),
    IsProved IsAxiom prop
    -> IsLproposition prop = true.
Proof.
  intros.
  destruct H as [proof H0].
  apply andb_prop in H0. destruct H0 as [H0 proofloop].
  apply andb_prop in H0. destruct H0 as [H0 lenproof].
  apply Nat.eqb_eq in H0. subst prop.
  apply Nat.leb_le in lenproof.
  apply (ProofLoopIsLproposition IsAxiom (LengthNat proof) proof
                                 eq_refl proofloop 0).
  exact lenproof.
Qed.
