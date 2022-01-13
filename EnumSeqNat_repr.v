Require Import Arith.Wf_nat.
Require Import PeanoNat.
Require Import Numbers.NaryFunctions.
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
Require Import BoolRepresented.


Definition sqrt_step (stepCount val : nat) : nat :=
  if Nat.even val then
    (let arg := val/2 in
     if Nat.ltb arg (S stepCount*S stepCount) then 2*stepCount+1 else val)
  else val.

Definition sqrt_alt (n : nat) : nat :=
  (nat_rec (fun _ => nat) (2*n) sqrt_step n) / 2.

Lemma sqrt_alt_correct : forall n k,
    let v := nat_rec (fun _ => nat) (2*n) sqrt_step k in
    if Nat.even v then v = 2*n /\ k*k <= n
    else v/2 = Nat.sqrt n.
Proof.
  induction k.
  - change (if Nat.even (0+2*n)
            then 2*n = 2*n /\ 0*0 <= n else (2*n) / 2 = Nat.sqrt n).
    rewrite Nat.even_add_mul_2.
    change (2 * n = 2 * n /\ 0 * 0 <= n). split.
    reflexivity. apply le_0_n.
  - pose (nat_rec (fun _ : nat => nat) (2 * n) sqrt_step k) as w.
    change (nat_rec (fun _ : nat => nat) (2 * n) sqrt_step (S k))
      with (sqrt_step k w).
    unfold sqrt_step.
    change (if Nat.even w
            then w = 2 * n /\ k*k <= n
            else w / 2 = Nat.sqrt n) in IHk.
    destruct (Nat.even w) eqn:weven.
    + (* w is even, so the computation still continues after k steps *)
      destruct (w / 2 <? S k * S k) eqn:des.
      apply Nat.ltb_lt in des.
      rewrite Nat.add_comm, Nat.even_add_mul_2.
      change ((1 + 2 * k) / 2 = Nat.sqrt n).
      rewrite Nat.mul_comm.
      rewrite Nat.div_add; simpl. 2: discriminate.
      destruct IHk. rewrite H in des.
      rewrite Nat.mul_comm, Nat.div_mul in des. 2: discriminate.
      symmetry. apply Nat.sqrt_unique.
      split; assumption.
      rewrite weven. split. apply IHk.
      destruct IHk. apply Nat.ltb_nlt, not_lt in des.
      rewrite H, Nat.mul_comm, Nat.div_mul in des.
      exact des. discriminate.
    + rewrite weven. exact IHk.
Qed.

Lemma sqrt_step_repr : FunctionRepresented 2 sqrt_step.
Proof.
  unfold sqrt_step.
  apply (IfRepresented 2 (fun i j => Nat.even j)).
  apply (EvenRepresented 2 (fun _ j => j)).
  apply (proj_represented 2 1). apply Nat.le_refl.
  apply (IfRepresented 2 (fun stepCount val => val / 2 <? S stepCount * S stepCount)
                       (fun stepCount val => 2 * stepCount + 1)).
  apply (LtbRepresented 2 (fun stepCount val : nat => val / 2)
                        (fun stepCount val : nat => S stepCount * S stepCount)).
  apply ComposeRepr_22.
  exact DivisionRepresented.
  apply (proj_represented 2 1). apply Nat.le_refl.
  apply (ConstantRepresented 2).
  apply ComposeRepr_22.
  exact MultiplicationRepresented.
  apply ComposeRepr_12.
  exact SuccessorRepresented.
  apply (proj_represented 2 0). auto.
  apply ComposeRepr_12.
  exact SuccessorRepresented.
  apply (proj_represented 2 0). auto.
  apply ComposeRepr_22.
  exact AdditionRepresented.
  apply (ComposeRepr_22 _ _ _ MultiplicationRepresented).
  apply (ConstantRepresented 2).
  apply (proj_represented 2 0). auto.
  apply (ConstantRepresented 1).
  apply (proj_represented 2 1). apply Nat.le_refl.
  apply (proj_represented 2 1). apply Nat.le_refl.
Qed.

Lemma id_lt_square : forall n, 2 <= n -> n < n*n.
Proof.
  intros n H. destruct n. inversion H.
  change (S n * S n) with (S n + n * S n).
  rewrite <- (Nat.add_0_r (S n)) at 1.
  apply Nat.add_lt_mono_l.
  apply le_S_n in H. destruct n. inversion H.
  apply le_n_S, le_0_n.
Qed.

Lemma sqrt_repr : FunctionRepresented 1 Nat.sqrt.
Proof.
  apply (FunctionRepresented_1_ext (fun n => sqrt_alt n)).
  - apply ComposeRepr_21.
    apply DivisionRepresented.
    apply (ComposeRepr_21 (fun n : nat => nat_rec (fun _ : nat => nat) n sqrt_step)
                          (fun n => 2*n)
                          (fun n => n)).
    apply nat_rec_repr.
    exact sqrt_step_repr.
    apply ComposeRepr_21.
    apply MultiplicationRepresented.
    apply (ConstantRepresented 2).
    apply (proj_represented 1 0). apply Nat.le_refl.
    apply (proj_represented 1 0). apply Nat.le_refl.
    apply (ConstantRepresented 2).
  - intro n. unfold sqrt_alt.
    pose proof (sqrt_alt_correct n n) as H.
    change (if Nat.even (nat_rec (fun _ : nat => nat) (2 * n) sqrt_step n)
            then nat_rec (fun _ : nat => nat) (2 * n) sqrt_step n = 2 * n /\ n * n <= n
            else (nat_rec (fun _ : nat => nat) (2 * n) sqrt_step n) / 2 = Nat.sqrt n) in H.
    destruct (Nat.even (nat_rec (fun _ : nat => nat) (2 * n) sqrt_step n)) eqn:des.
    2: exact H.
    destruct H.
    destruct n. reflexivity.
    destruct n. reflexivity.
    exfalso.
    pose proof (id_lt_square (S (S n))).
    apply Nat.lt_nge in H1. contradiction.
    apply le_n_S, le_n_S, le_0_n.
Qed.

Lemma biggestTriangle_repr : FunctionRepresented 1 biggestTriangle.
Proof.
  apply ComposeRepr_21.
  exact DivisionRepresented.
  apply (ComposeRepr_21 _ _ _ SubtractionRepresented).
  apply ComposeRepr_11.
  exact sqrt_repr.
  apply (ComposeRepr_21 _ _ _ AdditionRepresented).
  apply (ConstantRepresented 1).
  apply (ComposeRepr_21 _ _ _ MultiplicationRepresented).
  apply (ConstantRepresented 8).
  apply (proj_represented 1 0). apply Nat.le_refl.
  apply (ConstantRepresented 1).
  apply (ConstantRepresented 2).
Qed.

Lemma natTriangle_repr : FunctionRepresented 1 natTriangle.
Proof.
  apply ComposeRepr_21.
  exact DivisionRepresented.
  apply ComposeRepr_21.
  exact MultiplicationRepresented.
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply ComposeRepr_21.
  exact AdditionRepresented.
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply (ConstantRepresented 1).
  apply (ConstantRepresented 2).
Qed.

Transparent diagY.
Lemma diagY_repr : FunctionRepresented 1 diagY.
Proof.
  unfold diagY.
  apply ComposeRepr_21.
  exact SubtractionRepresented.
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply ComposeRepr_11.
  exact natTriangle_repr.
  exact biggestTriangle_repr.
Qed.
Opaque diagY.

Transparent diagX.
Lemma diagX_repr : FunctionRepresented 1 diagX.
Proof.
  unfold diagX.
  apply ComposeRepr_21.
  exact SubtractionRepresented.
  exact biggestTriangle_repr.
  exact diagY_repr.
Qed.
Opaque diagX.

Transparent LengthNat.
Lemma LengthNat_repr : FunctionRepresented 1 LengthNat.
Proof.
  exact diagX_repr.
Qed.
Opaque LengthNat.

Transparent diagMerge.
Lemma diagMerge_repr : FunctionRepresented 2 diagMerge.
Proof.
  unfold diagMerge.
  apply ComposeRepr_22.
  exact AdditionRepresented.
  apply (proj_represented 2 1); apply Nat.le_refl.
  apply ComposeRepr_22.
  exact DivisionRepresented.
  apply ComposeRepr_22.
  exact MultiplicationRepresented.
  exact AdditionRepresented.
  apply ComposeRepr_12.
  exact SuccessorRepresented.
  exact AdditionRepresented.
  apply (ConstantRepresented 2).
Qed.
Opaque diagMerge.

(* Generalization of nat_rec_repr on a state nat*nat.
   u,v currentStep valX valY. *)
Lemma nat_rec_2_repr : forall (u v : nat -> nat -> nat -> nat),
    FunctionRepresented 3 u
    -> FunctionRepresented 3 v
    -> FunctionRepresented
        3 (fun initX initY k
           => snd (nat_rec (fun _ => prod nat nat) (initX, initY)
                          (fun currentStep val
                           => let (valX,valY) := val in
                             (u currentStep valX valY, v currentStep valX valY)) k)).
Proof.
  intros u v urep vrep.
  pose (fun currentStep val
        => diagMerge (u currentStep (diagX val) (diagY val))
                    (v currentStep (diagX val) (diagY val)))
    as stepF.
  apply (FunctionRepresented_3_ext
           (@ncompose 2 3 (fun init n => diagY (nat_rec (fun _ => nat) init stepF n))
                      (fun k => match k with
                             | O => fun initX initY k => diagMerge initX initY
                             | _ => fun initX initY k => k
                             end))).
  - apply ComposeRepr_n.
    apply ComposeRepr_12. exact diagY_repr.
    apply nat_rec_repr. unfold stepF.
    apply ComposeRepr_22. exact diagMerge_repr.
    apply ComposeRepr_32. exact urep.
    apply (proj_represented 2 0); auto.
    apply ComposeRepr_12. exact diagX_repr.
    apply (proj_represented 2 1); auto.
    apply ComposeRepr_12. exact diagY_repr.
    apply (proj_represented 2 1); auto.
    apply ComposeRepr_32. exact vrep.
    apply (proj_represented 2 0); auto.
    apply ComposeRepr_12. exact diagX_repr.
    apply (proj_represented 2 1); auto.
    apply ComposeRepr_12. exact diagY_repr.
    apply (proj_represented 2 1); auto.
    intros [|k].
    apply ComposeRepr_23. exact diagMerge_repr.
    apply (proj_represented 3 0); auto.
    apply (proj_represented 3 1); auto.
    apply (proj_represented 3 2); auto.
  - simpl.
    assert (forall k initX initY,
               nat_rec (fun _ => nat) (diagMerge initX initY) stepF k
               = let (i,j) := nat_rec (fun _ => prod nat nat) (initX,initY)
                                      (fun (currentStep : nat) (val : nat * nat) =>
                                         let (n, p) := val in
                                         (u currentStep n p, v currentStep n p)) k in
                 diagMerge i j).
    induction k. reflexivity.
    intros. simpl. rewrite IHk. clear IHk.
    unfold stepF.
    destruct (nat_rec (fun _ => prod nat nat) (initX, initY)
         (fun (currentStep : nat) (val : nat * nat) =>
          let (n, p) := val in (u currentStep n p, v currentStep n p)) k).
    rewrite diagXMergeId, diagYMergeId. reflexivity.
    intros i j k. rewrite H.
    destruct (nat_rec (fun _ => prod nat nat) (i, j)
         (fun (currentStep : nat) (x : nat * nat) =>
          let (n, p) := x in (u currentStep n p, v currentStep n p)) k).
    rewrite diagYMergeId. reflexivity.
Qed.

(* Recursion that transports a parameter.
   It specializes nat_rec_2_repr, with a constant first coordinate.
   u param currentStep val must return the next value. *)
Lemma nat_rec_param_repr : forall (u : nat -> nat -> nat -> nat),
    FunctionRepresented 3 u
    -> FunctionRepresented 3 (fun param init => nat_rec (fun _ => nat) init (u param)).
Proof.
  intros u urep.
  pose (fun currentStep valX valY : nat => valX) as stepX.
  pose (fun currentStep valX valY => u valX currentStep valY) as stepY.
  refine (FunctionRepresented_3_ext _ _ (nat_rec_2_repr stepX stepY _ _) _).
  - apply (proj_represented 3 1); auto. 
  - unfold stepY.
    apply ComposeRepr_33. exact urep.
    apply (proj_represented 3 1); auto.
    apply (proj_represented 3 0); auto.
    apply (proj_represented 3 2); auto.
  - intros param j.
    assert (forall k : nat,
               nat_rec (fun _ => prod nat nat) (param, j)
       (fun (currentStep : nat) (val : nat * nat) =>
        let (valX, valY) := val in
        (stepX currentStep valX valY, stepY currentStep valX valY)) k
               = (param, nat_rec (fun _ : nat => nat) j (u param) k)).
    induction k. reflexivity.
    simpl.
    destruct (nat_rec (fun _ => prod nat nat) (param, j)
             (fun (currentStep : nat) (val : nat * nat) =>
              let (valX, valY) := val in
              (stepX currentStep valX valY, stepY currentStep valX valY)) k).
    inversion IHk. unfold stepX, stepY. reflexivity.
    intro k. rewrite H. reflexivity.
Qed.

Lemma nat_rec_param_2_repr : forall (u : nat -> nat -> nat -> nat -> nat),
    FunctionRepresented 4 u
    -> FunctionRepresented 4 (fun p q init => nat_rec (fun _ => nat) init (u p q)).
Proof.
  intros u urep.
  pose (fun pq currentStep val : nat
        => u (diagX pq) (diagY pq) currentStep val) as v.
  apply (FunctionRepresented_4_ext
           (@ncompose 3 4 (fun pq init => nat_rec (fun _ => nat) init (v pq))
                      (fun k => match k with
                            | 0 => fun p q init i => diagMerge p q
                            | 1 => fun p q init i => init
                            | _ => fun p q init i => i end))).
  - apply ComposeRepr_n.
    apply nat_rec_param_repr.
    unfold v. apply ComposeRepr_43. exact urep.
    apply ComposeRepr_13. exact diagX_repr.
    apply (proj_represented 3 0); auto.
    apply ComposeRepr_13. exact diagY_repr.
    apply (proj_represented 3 0); auto.
    apply (proj_represented 3 1); auto.
    apply (proj_represented 3 2); auto.
    intros [|k].
    apply ComposeRepr_24. exact diagMerge_repr.
    apply (proj_represented 4 0); auto.
    apply (proj_represented 4 1); auto.
    destruct k.
    apply (proj_represented 4 2); auto.
    apply (proj_represented 4 3); auto.
  - intros. simpl. unfold v. simpl.
    rewrite diagXMergeId, diagYMergeId. reflexivity.
Qed.

Lemma nat_rec_param_3_repr : forall (u : nat -> nat -> nat -> nat -> nat -> nat),
    FunctionRepresented 5 u
    -> FunctionRepresented 5 (fun p q r init => nat_rec (fun _ => nat) init (u p q r)).
Proof.
  intros u urep. 
  pose (fun pq r currentStep val : nat
        => u (diagX pq) (diagY pq) r currentStep val) as v.
  apply (FunctionRepresented_5_ext
           (@ncompose 4 5 (fun pq r init => nat_rec (fun _ => nat) init (v pq r))
                      (fun k => match k with
                            | 0 => fun p q r init i => diagMerge p q
                            | 1 => fun p q r init i => r
                            | 2 => fun p q r init i => init
                            | _ => fun p q r init i => i end))).
  - apply ComposeRepr_n.
    apply nat_rec_param_2_repr.
    unfold v. apply ComposeRepr_54. exact urep.
    apply ComposeRepr_14. exact diagX_repr.
    apply (proj_represented 4 0); auto.
    apply ComposeRepr_14. exact diagY_repr.
    apply (proj_represented 4 0); auto.
    apply (proj_represented 4 1); auto.
    apply (proj_represented 4 2); auto.
    apply (proj_represented 4 3); auto.
    intros [|k].
    apply ComposeRepr_25. exact diagMerge_repr.
    apply (proj_represented 5 0); apply le_n_S, le_0_n. 
    apply (proj_represented 5 1); auto.
    destruct k.
    apply (proj_represented 5 2); auto.
    destruct k.
    apply (proj_represented 5 3); auto.
    apply (proj_represented 5 4); auto.
  - intros. simpl. unfold v.
    rewrite diagXMergeId, diagYMergeId. reflexivity.
Qed.

Transparent TailNat.
Lemma TailNat_repr : FunctionRepresented 1 TailNat.
Proof.
  apply (FunctionRepresented_1_ext
           (fun n => if Nat.eqb (LengthNat n) 0
                  then NilNat else diagMerge (pred (LengthNat n)) (diagY (diagY n)))).
  apply (IfRepresented 1 (fun n => LengthNat n =? 0)).
  apply (EqbRepresented 1).
  exact LengthNat_repr.
  apply (ConstantRepresented 0).
  apply (ConstantRepresented 0).
  apply (ComposeRepr_21 _ _ _ diagMerge_repr).
  apply ComposeRepr_11.
  apply (FunctionRepresented_1_ext (fun n => n - 1)).
  apply ComposeRepr_21.
  exact SubtractionRepresented.
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply (ConstantRepresented 1).
  intro n. rewrite Nat.sub_1_r. reflexivity.
  exact LengthNat_repr.
  apply ComposeRepr_11; exact diagY_repr.
  intro n. unfold TailNat.
  destruct (LengthNat n); reflexivity.
Qed.

Lemma NthTailNat_repr : FunctionRepresented 2 NthTailNat.
Proof.
  pose proof (FunctionRepresented_2_ext).
  apply (FunctionRepresented_2_ext
           (fun init => nat_rec (fun _ => nat) init (fun n k => TailNat k))).
  - apply nat_rec_repr.
    apply ComposeRepr_12.
    2: apply (proj_represented 2 1), Nat.le_refl.
    exact TailNat_repr.
  - induction k. reflexivity. simpl.
    rewrite IHk. clear IHk. revert k n. induction k.
    reflexivity. intro n. simpl. rewrite IHk. reflexivity.
Qed.

Lemma HeadNat_repr : FunctionRepresented 1 HeadNat.
Proof.
  unfold HeadNat.
  apply (FunctionRepresented_1_ext
           (fun n => if Nat.eqb (LengthNat n) 0
                  then NilNat else diagX (diagY n))).
  apply (IfRepresented 1 (fun n => LengthNat n =? 0) (fun n => NilNat) (fun n => diagX (diagY n))).
  apply (EqbRepresented 1 _ _ LengthNat_repr).
  apply (ConstantRepresented 0).
  apply (ConstantRepresented 0).
  apply ComposeRepr_11.
  exact diagX_repr. exact diagY_repr.
  intro n. destruct (LengthNat n); reflexivity.
Qed.

Transparent ConsNat.
Lemma ConsNat_repr : FunctionRepresented 2 ConsNat.
Proof.
  unfold ConsNat.
  apply ComposeRepr_22.
  exact diagMerge_repr.
  apply ComposeRepr_12.
  exact SuccessorRepresented.
  apply ComposeRepr_12.
  exact LengthNat_repr.
  apply (proj_represented 2 1); apply Nat.le_refl.
  apply ComposeRepr_22.
  exact diagMerge_repr.
  apply (proj_represented 2 0); auto.
  apply ComposeRepr_12.
  exact diagY_repr.
  apply (proj_represented 2 1); apply Nat.le_refl.
Qed.
Lemma ConsNat_fst_repr : forall v,
    FunctionRepresented 1 (ConsNat v).
Proof.
  intro v.
  apply ComposeRepr_21. exact ConsNat_repr.
  apply (ConstantRepresented v).
  apply (proj_represented 1 0); apply Nat.le_refl.
Qed. 
Opaque ConsNat.

Transparent CoordNat.
Lemma CoordNat_repr : FunctionRepresented 2 CoordNat.
Proof.
  unfold CoordNat.
  apply ComposeRepr_12.
  exact HeadNat_repr. exact NthTailNat_repr.
Qed.
Lemma CoordNat_fst_repr : forall v,
    FunctionRepresented 1 (fun n => CoordNat n v).
Proof.
  intro v.
  apply ComposeRepr_21. exact CoordNat_repr.
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply (ConstantRepresented v).
Qed. 
Opaque CoordNat.

(* Useless if ConcatNat can be defined by a nat_rec on nat*nat *)
Definition ConcatReverseRec (n p : nat) : nat -> prod nat nat :=
  nat_rec (fun _ => prod nat nat) (n,p)
          (fun _ val
           => let (i,j) := val in
             (TailNat i, ConsNat (HeadNat i) j)).
Definition ConcatReverseNat (n p : nat) : nat :=
  snd (ConcatReverseRec n p (LengthNat n)).
Definition ReverseNat (n : nat) : nat := ConcatReverseNat n NilNat.

Lemma LengthConcatReverseX : forall k n p : nat,
    LengthNat (fst (ConcatReverseRec n p k))
    = LengthNat n - k.
Proof.
  induction k.
  - intros. simpl. rewrite Nat.sub_0_r. reflexivity.
  - intros. simpl. specialize (IHk n p).
    destruct (ConcatReverseRec n p k). simpl. simpl in IHk.
    rewrite LengthTailNat, IHk.
    rewrite Nat.sub_succ_r. reflexivity.
Qed.

Lemma ConcatReverseRec_succ : forall step n p k,
    ConcatReverseRec (ConsNat k n) p (S step)
    = ConcatReverseRec n (ConsNat k p) step.
Proof.
  induction step.
  - intros. simpl.
    rewrite TailConsNat, HeadConsNat. reflexivity.
  - intros. 
    change (ConcatReverseRec (ConsNat k n) p (S (S step)))
      with (let (i, j) := ConcatReverseRec (ConsNat k n) p (S step) in
            (TailNat i, ConsNat (HeadNat i) j)).
    rewrite IHstep. reflexivity.
Qed.

Lemma ConcatReverseNil : forall p,
    ConcatReverseNat NilNat p = p.
Proof.
  intro p. unfold ConcatReverseNat.
  change (LengthNat NilNat) with 0.
  simpl. reflexivity.
Qed.

Lemma ConcatReverseCons : forall n p k,
    ConcatReverseNat (ConsNat k n) p = ConcatReverseNat n (ConsNat k p).
Proof.
  intros. unfold ConcatReverseNat.
  rewrite LengthConsNat.
  rewrite ConcatReverseRec_succ. reflexivity.
Qed.

Lemma LengthConcatReverseNat : forall n p : nat,
    LengthNat (ConcatReverseNat n p) = LengthNat n + LengthNat p.
Proof.
  assert (forall l n p,
             l = LengthNat n ->
             LengthNat (ConcatReverseNat n p) = LengthNat n + LengthNat p).
  induction l.
  - intros. unfold ConcatReverseNat. rewrite <- H.
    simpl. reflexivity.
  - intros.
    assert (0 < LengthNat n).
    { rewrite <- H. apply le_n_S, le_0_n. }
    rewrite (HeadTailDecompNat n H0).
    rewrite ConcatReverseCons, LengthConsNat, IHl.
    rewrite LengthTailNat, LengthConsNat.
    destruct (LengthNat n). discriminate H.
    simpl. rewrite Nat.add_succ_r. reflexivity.
    rewrite LengthTailNat.
    destruct (LengthNat n). discriminate H.
    simpl. inversion H. reflexivity.
  - intros. apply (H (LengthNat n)). reflexivity.
Qed.

Lemma ConcatReverse_spec : forall n p q : nat,
    ConcatReverseNat p (ConcatNat n q)
    = ConcatReverseNat (ConcatReverseNat n p) q.
Proof.
  assert (forall l n p q,
             l = LengthNat n
             -> ConcatReverseNat p (ConcatNat n q)
               = ConcatReverseNat (ConcatReverseNat n p) q).
  induction l.
  - intros. unfold ReverseNat, ConcatReverseNat, ConcatReverseRec.
    rewrite <- H. simpl.
    unfold ConcatNat.
    rewrite <- H. reflexivity.
  - intros.
    assert (0 < LengthNat n) as lenpos.
    { rewrite <- H. apply le_n_S, le_0_n. }
    rewrite (HeadTailDecompNat n lenpos).
    rewrite ConcatConsNat.
    rewrite ConcatReverseCons.
    rewrite <- IHl.
    rewrite ConcatReverseCons. reflexivity.
    rewrite LengthTailNat.
    rewrite <- H. reflexivity.
  - intros. apply (H (LengthNat n)). reflexivity.
Qed.

Lemma CoordConcatReverseNatSecond : forall f g k,
    CoordNat (ConcatReverseNat f g) (k + LengthNat f) = CoordNat g k.
Proof.
  apply (Seq_rect (fun f => forall g k,
    CoordNat (ConcatReverseNat f g) (k + LengthNat f) = CoordNat g k)).
  - intros. unfold ConcatReverseNat. rewrite H, Nat.add_0_r.
    simpl. reflexivity.
  - intros. rewrite ConcatReverseCons.
    specialize (H (ConsNat hd g) (S k)).
    rewrite LengthConsNat, Nat.add_succ_r.
    simpl in H. rewrite H.
    rewrite CoordConsTailNat. reflexivity.
Qed.

Lemma CoordConcatReverseNatFirst : forall n g k,
    k < LengthNat n
    -> CoordNat (ConcatReverseNat n g) k = CoordNat n (LengthNat n - S k).
Proof.
  apply (Seq_rect (fun n => forall g k,
    k < LengthNat n
    -> CoordNat (ConcatReverseNat n g) k = CoordNat n (LengthNat n - S k))).
  - intros. exfalso. rewrite H in H0. inversion H0.
  - intros. rewrite LengthConsNat in H0.
    rewrite ConcatReverseCons, LengthConsNat. simpl.
    apply Nat.le_succ_r in H0. destruct H0.
    + rewrite H. destruct (LengthNat tl - k) eqn:des.
      exfalso. apply Nat.sub_0_le in des.
      apply (Nat.lt_irrefl k). exact (Nat.lt_le_trans _ _ _ H0 des).
      rewrite CoordConsTailNat.
      apply f_equal.
      apply Nat.add_sub_eq_l.
      simpl. rewrite <- Nat.add_succ_r, <- des.
      rewrite Nat.add_comm. rewrite Nat.sub_add.
      reflexivity. apply (Nat.le_trans _ (S k)).
      apply le_S, Nat.le_refl.
      exact H0. exact H0.
    + inversion H0.
      change (LengthNat tl) with (0 + LengthNat tl) at 1.
      rewrite CoordConcatReverseNatSecond.
      rewrite Nat.sub_diag.
      rewrite CoordConsHeadNat, CoordConsHeadNat. reflexivity.
Qed.

Lemma ConcatReverse_repr : FunctionRepresented 2 ConcatReverseNat.
Proof.
  pose (fun currentStep n p : nat => TailNat n) as stepX.
  pose (fun currentStep n p : nat => ConsNat (HeadNat n) p) as stepY.
  refine (ComposeRepr_32
            _
            (fun n p => n)
            (fun n p => p)
            (fun n p => LengthNat n)
            (nat_rec_2_repr stepX stepY _ _) _ _ _).
  apply ComposeRepr_13. exact TailNat_repr.
  apply (proj_represented 3 1); auto. 
  unfold stepY.
  apply ComposeRepr_23. exact ConsNat_repr.
  apply ComposeRepr_13. exact HeadNat_repr.
  apply (proj_represented 3 1); auto. 
  apply (proj_represented 3 2); auto.
  apply (proj_represented 2 0); auto.
  apply (proj_represented 2 1); auto.
  apply ComposeRepr_12. exact LengthNat_repr.
  apply (proj_represented 2 0); auto.
Qed.

Lemma ConcatNat_repr : FunctionRepresented 2 ConcatNat.
Proof.
  apply (FunctionRepresented_2_ext (fun n p => ConcatReverseNat (ReverseNat n) p)).
  - apply ComposeRepr_22.
    exact ConcatReverse_repr.
    unfold ReverseNat.
    apply ComposeRepr_22.
    exact ConcatReverse_repr.
    apply (proj_represented 2 0); auto.
    apply (ConstantRepresented 0).
    apply (proj_represented 2 1); auto.
  - intros n k.
    pose proof (ConcatReverse_spec n NilNat k).
    rewrite ConcatReverseNil in H.
    symmetry. exact H.
Qed.

Lemma PAnatRepresented : FunctionRepresented 1 PAnat.
Proof.
  apply (FunctionRepresented_1_ext
           (nat_rec (fun _ => nat) PAzero (fun _ k => PAsucc k))).
  apply (ComposeRepr_21 (fun init => nat_rec (fun _ => nat) init (fun _ k => PAsucc k))).
  apply nat_rec_repr.
  apply ComposeRepr_12.
  unfold PAsucc, Lop1, Lop.
  apply ComposeRepr_21.
  exact ConsNat_repr.
  apply (ConstantRepresented 8).
  apply ComposeRepr_21.
  exact ConsNat_repr.
  apply (ConstantRepresented 0).
  apply ComposeRepr_21.
  exact ConsNat_repr.
  apply (proj_represented 1 0); apply Nat.le_refl.
  apply (ConstantRepresented 0).
  apply (proj_represented 2 1); apply Nat.le_refl.
  apply (ConstantRepresented PAzero).
  apply (proj_represented 1 0); apply Nat.le_refl.
  induction n. reflexivity.
  simpl. rewrite IHn. reflexivity.
Qed.

Definition TruncateNat (n len : nat) : nat :=
  ReverseNat (NthTailNat (ReverseNat n) (LengthNat n - len)).

Lemma LengthTruncateNat : forall n len,
    LengthNat (TruncateNat n len) = Nat.min len (LengthNat n).
Proof.
  intros. unfold TruncateNat, ReverseNat.
  rewrite LengthConcatReverseNat, LengthNthTailNat.
  rewrite LengthConcatReverseNat.
  change (LengthNat NilNat) with 0.
  rewrite Nat.add_0_r, Nat.add_0_r.
  destruct (le_lt_dec (LengthNat n) len).
  rewrite Nat.min_r. 2: exact l.
  pose proof (Nat.sub_0_le (LengthNat n) len) as [_ H].
  rewrite H, Nat.sub_0_r. reflexivity. exact l.
  rewrite Nat.min_l.
  apply Nat.add_sub_eq_l.
  rewrite Nat.sub_add. reflexivity.
  apply Nat.lt_le_incl, l.
  apply Nat.lt_le_incl, l.
Qed.

Lemma CoordTruncateNat : forall i j p,
    p < j ->
    CoordNat (TruncateNat i j) p = CoordNat i p.
Proof.
  intros. unfold TruncateNat, ReverseNat.
  destruct (le_lt_dec (LengthNat i) j).
  apply Nat.sub_0_le in l. rewrite l. simpl.
  rewrite <- ConcatReverse_spec, ConcatReverseNil.
  destruct (le_lt_dec (LengthNat i) p).
  rewrite CoordNatAboveLength, CoordNatAboveLength. reflexivity.
  exact l0. rewrite LengthConcatNat.
  change (LengthNat NilNat) with 0.
  rewrite Nat.add_0_r. exact l0.
  apply CoordConcatNatFirst. exact l0.
  assert (LengthNat i - (LengthNat i - j) = j).
  { apply Nat.add_sub_eq_l.
    rewrite Nat.sub_add. reflexivity. apply Nat.lt_le_incl, l. }
  rewrite CoordConcatReverseNatFirst.
  rewrite LengthNthTailNat, LengthConcatReverseNat.
  change (LengthNat NilNat) with 0.
  rewrite Nat.add_0_r.
  rewrite CoordNthTailNat.
  rewrite H0.
  replace (LengthNat i - j + (j - S p)) with (LengthNat i - S p).
  rewrite CoordConcatReverseNatFirst.
  apply f_equal.
  apply Nat.add_sub_eq_l.
  simpl. rewrite <- Nat.add_succ_r.
  rewrite Nat.sub_add. reflexivity.
  exact (Nat.lt_trans _ _ _ H l).
  apply Nat.sub_lt.
  exact (Nat.lt_trans _ _ _ H l).
  apply le_n_S, le_0_n.
  apply Nat.add_sub_eq_l.
  rewrite Nat.add_comm, <- Nat.add_assoc.
  rewrite Nat.sub_add. 2: exact H.
  rewrite Nat.sub_add. reflexivity.
  apply Nat.lt_le_incl, l.
  rewrite LengthNthTailNat, LengthConcatReverseNat.
  change (LengthNat NilNat) with 0.
  rewrite Nat.add_0_r.
  rewrite H0. exact H.
Qed.

Lemma TruncateNat_repr : FunctionRepresented 2 TruncateNat.
Proof.
  unfold TruncateNat.
  apply ComposeRepr_12.
  unfold ReverseNat.
  apply ComposeRepr_21. exact ConcatReverse_repr.
  apply (proj_represented 1 0); auto.
  apply (ConstantRepresented 0).
  apply ComposeRepr_22. exact NthTailNat_repr.
  apply ComposeRepr_22. exact ConcatReverse_repr.
  apply (proj_represented 2 0); auto.
  apply (ConstantRepresented 0).
  apply ComposeRepr_22.
  apply SubtractionRepresented.
  apply ComposeRepr_12. exact LengthNat_repr.
  apply (proj_represented 2 0); auto.
  apply (proj_represented 2 1); auto.
Qed.

Definition Fix_cumul (rec : forall currentStep:nat, (forall y : nat, y < currentStep -> nat) -> nat)
  : nat -> nat
  := nat_rec (fun _ => nat) NilNat
             (fun currentStep previousValues
              => ConcatNat previousValues (ConsNat (rec currentStep (fun y H => CoordNat previousValues y)) NilNat)).

Lemma Fix_cumul_succ : forall rec k,
    Fix_cumul rec (S k)
    = ConcatNat (Fix_cumul rec k) (ConsNat (rec k (fun y H => CoordNat (Fix_cumul rec k) y)) NilNat).
Proof.
  reflexivity.
Qed.

Lemma Fix_cumul_len : forall rec k,
    LengthNat (Fix_cumul rec k) = k.
Proof.
  induction k.
  - reflexivity.
  - rewrite Fix_cumul_succ, LengthConcatNat, IHk, LengthConsNat.
    rewrite Nat.add_succ_r. change (LengthNat NilNat) with 0.
    rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma Fix_cumul_last : forall rec k,
    CoordNat (Fix_cumul rec (S k)) k
    = rec k (fun (y : nat) (_ : y < k) => CoordNat (Fix_cumul rec k) y).
Proof.
  intros rec k. destruct k.
  - unfold Fix_cumul. simpl.
    rewrite ConcatNilNat, CoordConsHeadNat. reflexivity.
  - rewrite Fix_cumul_succ.
    rewrite <- (Fix_cumul_len rec (S k)) at 3.
    rewrite <- (Nat.add_0_l (LengthNat (Fix_cumul rec (S k)))).
    rewrite CoordConcatNatSecond.
    rewrite CoordConsHeadNat.
    reflexivity.
Qed.

Lemma Fix_cumul_cumul : forall j i k rec,
    i <= j ->
    k < i ->
    CoordNat (Fix_cumul rec i) k = CoordNat (Fix_cumul rec j) k.
Proof.
  induction j.
  - intros. inversion H. rewrite H1 in H0. inversion H0.
  - intros.
    apply Nat.le_succ_r in H. destruct H.
    + rewrite Fix_cumul_succ.
      rewrite IHj.
      rewrite CoordConcatNatFirst. reflexivity.
      rewrite Fix_cumul_len.
      exact (Nat.lt_le_trans _ _ _ H0 H).
      exact H. exact H0.
    + subst i. reflexivity.
Qed.

Lemma Fix_alt : forall (rec : forall currentStep:nat, (forall y : nat, y < currentStep -> nat) -> nat)
                  (k : nat),
    (forall i p q, (forall j (H:j<i), p j H = q j H) -> rec i p = rec i q) ->
    Fix lt_wf (fun _ => nat) rec k = CoordNat (Fix_cumul rec (S k)) k.
Proof.
  intros rec.
  apply (Fix lt_wf (fun k => (forall (i : nat) (p q : forall x : nat, x < i -> nat),
   (forall (j : nat) (H : j < i), p j H = q j H) -> rec i p = rec i q) ->
  Fix lt_wf (fun _ : nat => nat) rec k = CoordNat (Fix_cumul rec (S k)) k)).
  intros k IHk rec_ext.
  rewrite Fix_eq, Fix_cumul_last.
  apply rec_ext. intros.
  rewrite (IHk _ H rec_ext).
  apply Fix_cumul_cumul.
  exact H. apply Nat.le_refl.
  intros. apply rec_ext.
  intros. apply H.
Qed.

Lemma Fix_repr : forall (rec : forall currentStep:nat, (forall y : nat, y < currentStep -> nat) -> nat),
    FunctionRepresented 2 (fun currentStep previousValues
                           => rec currentStep (fun y _ => CoordNat previousValues y))
    -> (forall i p q, (forall j (H:j<i), p j H = q j H) -> rec i p = rec i q)
    -> FunctionRepresented 1 (Fix lt_wf (fun _ => nat) rec).
Proof.
  intros rec H rec_ext.
  apply (FunctionRepresented_1_ext (fun n => CoordNat (Fix_cumul rec (S n)) n)).
  - apply ComposeRepr_21.
    exact CoordNat_repr.
    unfold Fix_cumul.
    apply (ComposeRepr_21
             (fun n : nat =>
     nat_rec (fun _ : nat => nat) n
       (fun currentStep previousValues : nat =>
        ConcatNat previousValues
          (ConsNat
             (rec currentStep
                (fun (y : nat) (_ : y < currentStep) => CoordNat previousValues y))
             NilNat)))).
    apply nat_rec_repr.
    apply ComposeRepr_22.
    exact ConcatNat_repr.
    apply (proj_represented 2 1); auto.
    apply ComposeRepr_22.
    exact ConsNat_repr.
    exact H.
    apply (ConstantRepresented NilNat).
    apply (ConstantRepresented NilNat).
    exact SuccessorRepresented.
    apply (proj_represented 1 0); auto.
  - intro n. symmetry. apply Fix_alt. exact rec_ext.
Qed.

Lemma diagMergeParamLt : forall y param_i,
    y < diagY param_i
    -> diagMerge (diagX param_i) y < param_i.
Proof.
  intros.
  rewrite <- diagSplitMergeId.
  apply diagMergeIncrLt.
  apply Nat.le_refl. exact H.
Qed.

Lemma Fix_param_repr
  : forall (f : nat -> forall currentStep:nat, (forall y : nat, y < currentStep -> nat) -> nat),
    FunctionRepresented 3
    (fun param currentStep previousValues : nat =>
     f param currentStep
       (fun (y : nat) (_ : y < currentStep) =>
        diagY (CoordNat previousValues (diagMerge param y))))
    -> (forall i p q param, (forall j (H:j<i), p j H = q j H) -> f param i p = f param i q)
    -> FunctionRepresented 2 (fun param => Fix lt_wf (fun _ => nat) (f param)).
Proof.
  intros f frep fext.
  apply (FunctionRepresented_2_ext
           (fun param i
            => diagY (Fix lt_wf (fun _ => nat)
                         (fun param_i (rec : forall y : nat, y < param_i -> nat)
                          => let p := diagX param_i in
                            let i := diagY param_i in
                            diagMerge p (f p (diagY param_i)
                              (fun y (H:y<i) => diagY (rec (diagMerge p y)
                                                        (diagMergeParamLt y param_i H)))))
                         (diagMerge param i)))).
  - apply ComposeRepr_12. exact diagY_repr.
    apply (ComposeRepr_12). 2: exact diagMerge_repr.
    apply Fix_repr. simpl.
    apply ComposeRepr_22. exact diagMerge_repr.
    apply ComposeRepr_12. exact diagX_repr.
    apply (proj_represented 2 0); auto.
    apply (ComposeRepr_32 _ _ _ _ frep).
    apply ComposeRepr_12. exact diagX_repr.
    apply (proj_represented 2 0); auto.
    apply ComposeRepr_12. exact diagY_repr.
    apply (proj_represented 2 0); auto.
    apply (proj_represented 2 1); auto.
    intros. simpl. apply f_equal, fext.
    intros. apply f_equal, H.
  - intros n k. revert k n.
    pose (fun k => forall param : nat, 
    Fix lt_wf (fun _ : nat => nat)
       (fun (param_i : nat) (rec : forall y : nat, y < param_i -> nat) =>
        let p := diagX param_i in
        let i := diagY param_i in
        diagMerge p (f p (diagY param_i)
          (fun (y : nat) (H : y < i) =>
           diagY (rec (diagMerge p y) (diagMergeParamLt y param_i H)))))
       (diagMerge param k) = diagMerge param (Fix lt_wf (fun _ : nat => nat) (f param) k))
      as P.
    assert (forall k, P k) as allP.
    apply (Fix lt_wf P).
    intros k IHk param.
    rewrite Fix_eq.
    rewrite diagXMergeId, diagYMergeId. simpl.
    apply f_equal.
    rewrite Fix_eq.
    apply fext. intros y H.
    rewrite IHk, diagYMergeId. reflexivity. exact H.
    intros. apply fext.
    exact H.
    intros. simpl. apply f_equal.
    apply fext. intros. rewrite H. reflexivity.
    intros k n. rewrite allP, diagYMergeId. reflexivity.
Qed.

Lemma MapNat_repr : forall (f : nat -> nat -> nat),
    FunctionRepresented 2 f
    -> FunctionRepresented 2 (fun n : nat => MapNat (f n)).
Proof.
  intros f frep.
  apply Fix_param_repr.
  apply (FunctionRepresented_3_ext
             (fun param currentStep previousValues : nat =>
     if LengthNat currentStep <=? 0
     then NilNat
     else
      ConsNat (f param (HeadNat currentStep))
        (diagY (CoordNat previousValues (diagMerge param (TailNat currentStep)))))).
  - apply (IfRepresented 3).
    apply (LebRepresented 3).
    apply ComposeRepr_13. exact LengthNat_repr.
    apply (proj_represented 3 1); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 0).
    apply ComposeRepr_23. exact ConsNat_repr.
    apply ComposeRepr_23. exact frep.
    apply (proj_represented 3 0); auto.
    apply ComposeRepr_13. exact HeadNat_repr.
    apply (proj_represented 3 1); auto.
    apply ComposeRepr_13. exact diagY_repr.
    apply ComposeRepr_23. exact CoordNat_repr.
    apply (proj_represented 3 2); auto.
    apply ComposeRepr_23. exact diagMerge_repr.
    apply (proj_represented 3 0); auto.
    apply ComposeRepr_13. exact TailNat_repr.
    apply (proj_represented 3 1); auto.
  - intros. unfold MapNatRec.
    destruct (le_lt_dec (LengthNat j) 0).
    inversion l. rewrite Nat.leb_refl. reflexivity.
    destruct (LengthNat j <=? 0) eqn:des. 2: reflexivity.
    apply Nat.leb_le in des. exfalso.
    apply (Nat.lt_irrefl 0).
    apply (Nat.lt_le_trans _ _ _ l des).
  - intros. unfold MapNatRec.
    destruct (le_lt_dec (LengthNat i) 0). reflexivity.
    rewrite H. reflexivity.
Qed. 

Lemma FixBool_repr : forall (rec : forall currentStep:nat, (forall y : nat, y < currentStep -> bool) -> bool),
    FunctionRepresentedBool 2 (fun currentStep previousValues : nat =>
      rec currentStep
        (fun (y : nat) (_ : y < currentStep) => CoordNat previousValues y =? 1))
    -> (forall i p q, (forall j (H:j<i), p j H = q j H) -> rec i p = rec i q)
    -> FunctionRepresentedBool 1 (Fix lt_wf (fun _ => bool) rec).
Proof.
  intros rec H rec_ext.
  unfold FunctionRepresentedBool. simpl.
  pose (fun currentStep H0 => if rec currentStep (fun y ylt => H0 y ylt =? 1) then 1 else 0)
    as recnat.
  apply (FunctionRepresented_1_ext (Fix lt_wf (fun _ => nat) recnat)).
  - apply Fix_repr. exact H.
    intros. unfold recnat.
    rewrite (rec_ext _ _ (fun (y : nat) (ylt : y < i) => q y ylt =? 1)).
    reflexivity. intros. rewrite H0. reflexivity.
  - apply (Fix lt_wf). intros n IHn.
    rewrite Fix_eq.
    rewrite Fix_eq.
    unfold recnat at 1. simpl.
    replace (rec n (fun (y : nat) (_ : y < n) => Fix lt_wf (fun _ : nat => nat) recnat y =? 1))
      with (rec n (fun (y : nat) (_ : y < n) => Fix lt_wf (fun _ : nat => bool) rec y)).
    reflexivity.
    apply rec_ext. intros. rewrite IHn.
    destruct (Fix lt_wf (fun _ : nat => bool) rec j); reflexivity.
    exact H0. exact rec_ext.
    intros. unfold recnat.
    replace (rec x (fun (y : nat) (ylt : y < x) => f y ylt =? 1))
      with (rec x (fun (y : nat) (ylt : y < x) => g y ylt =? 1)).
    reflexivity. apply rec_ext.
    intros. rewrite H0. reflexivity.
Qed.

Lemma TreeFoldNat_repr : forall (f : nat -> (nat -> nat) -> nat) init,
    FunctionRepresented
      2 (fun n previousValues : nat => f n (CoordNat previousValues))
    -> (forall n r s, (forall i, i < LengthNat n -> r i = s i) -> f n r = f n s)
    -> FunctionRepresented 1 (TreeFoldNat f init).
Proof.
  intros f init H fext.
  apply Fix_repr.
  apply (FunctionRepresented_2_ext
    (@ncompose 2 2 (fun n previousValues : nat =>
                      if LengthNat n <=? 0
                      then init
                      else
                        f n (CoordNat previousValues))
               (fun k => match k with
                      | O => fun n _ => n
                      | _ => fun n prev => MapNat (CoordNat prev) n
                      end))).
  - apply ComposeRepr_n.
    apply (IfRepresented 2 (fun i j => LengthNat i <=? 0)).
    apply (LebRepresented 2).
    apply ComposeRepr_12.
    exact LengthNat_repr.
    apply (proj_represented 2 0); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented init).
    exact H.
    intros [|k].
    apply (proj_represented 2 0); auto.
    apply (ComposeRepr_22 _ (fun i j => j) (fun i j => i) (MapNat_repr _ CoordNat_repr)).
    apply (proj_represented 2 1); auto.
    apply (proj_represented 2 0); auto.
  - intros n k. simpl.
    unfold TreeFoldNatRec.
    destruct (le_lt_dec (LengthNat n) 0).
    inversion l. rewrite H1. reflexivity.
    destruct (LengthNat n <=? 0) eqn:des.
    exfalso.
    apply Nat.leb_le in des.
    apply (Nat.lt_irrefl 0).
    exact (Nat.lt_le_trans _ _ _ l des).
    apply fext. intros i H0.
    rewrite CoordMapNat. reflexivity. exact H0.
  - intros i p q H0. unfold TreeFoldNatRec.
    destruct (le_lt_dec (LengthNat i) 0).
    reflexivity. apply fext.
    intros. apply H0.
Qed.

Lemma MapCoordNat2_repr :
  FunctionRepresented 2
    (fun param_n q : nat =>
       MapNat (fun k : nat => diagY (CoordNat q (diagMerge (diagX param_n) k)))
              (diagY param_n)).
Proof.
  apply (FunctionRepresented_2_ext
           (@ncompose 2 2 (fun param_q => 
                             MapNat (fun k : nat => diagY (CoordNat (diagY param_q) (diagMerge (diagX param_q) k))))
                      (fun k => match k with
                             | 0 => fun param_n q => diagMerge (diagX param_n) q
                             | _ => fun param_n q => diagY param_n end))).
  - apply ComposeRepr_n.
    apply MapNat_repr.
    apply ComposeRepr_12. exact diagY_repr.
    apply ComposeRepr_22. exact CoordNat_repr.
    apply ComposeRepr_12. exact diagY_repr.
    apply (proj_represented 2 0); auto.
    apply ComposeRepr_22. exact diagMerge_repr.
    apply ComposeRepr_12. exact diagX_repr.
    apply (proj_represented 2 0); auto.
    apply (proj_represented 2 1); auto.
    intros [|k].
    apply ComposeRepr_22. exact diagMerge_repr.
    apply ComposeRepr_12. exact diagX_repr.
    apply (proj_represented 2 0); auto.
    apply (proj_represented 2 1); auto.
    apply ComposeRepr_12. exact diagY_repr.
    apply (proj_represented 2 0); auto.
  - simpl. intros n k.
    apply MapNatExt. intros i H0.
    rewrite diagXMergeId, diagYMergeId. reflexivity.
Qed.

Definition TreeFoldNat2Rec (f : nat -> nat -> (nat -> nat) -> nat)
           init (pn : nat) (rec : forall k : nat, k < pn -> nat) :=
  let p := diagX pn in
  let n := diagY pn in
  match le_lt_dec (LengthNat n) 0 with
  | left _ => diagMerge p init
  | right l => diagMerge p (f p n (fun i => diagY (rec (diagMerge p (CoordNat n i))
                                                   (diagMerge_param_lt _ _ l))))
  end.

Lemma TreeFoldNat_repr_2 : forall (f : nat -> nat -> (nat -> nat) -> nat) init,
    FunctionRepresented
      3 (fun param n previousValues : nat => f param n (CoordNat previousValues))
    -> (forall param n r s,
          (forall i, i < LengthNat n -> r i = s i)
          -> f param n r = f param n s)
    -> FunctionRepresented 2 (fun param => TreeFoldNat (f param) init).
Proof.
  (* TODO reuse Fix_param_repr *)
  intros f init H fext.
  apply (FunctionRepresented_2_ext
           (fun param i
            => diagY (Fix lt_wf (fun _ => nat)
                         (TreeFoldNat2Rec f init) (diagMerge param i)))).
  - apply ComposeRepr_12. exact diagY_repr.
    apply (ComposeRepr_12 _ diagMerge).
    2: exact diagMerge_repr.
    apply Fix_repr.
    + simpl.
      unfold TreeFoldNat2Rec.
      apply (FunctionRepresented_2_ext
    (@ncompose 2 2 (fun param_n previousValues : nat =>
                      if LengthNat (diagY param_n) <=? 0
                      then diagMerge (diagX param_n) init
                      else
                        diagMerge (diagX param_n)
                                  (f (diagX param_n) (diagY param_n) (CoordNat previousValues)))
               (fun k => match k with
                      | O => fun parn _ => parn
                      | _ => fun parn prev => MapNat (fun k => diagY (CoordNat prev (diagMerge (diagX parn) k)))
                                                 (diagY parn)
                      end))).
      apply ComposeRepr_n.
      apply (IfRepresented 2 (fun n p => LengthNat (diagY n) <=? 0)).
      apply (LebRepresented 2).
      apply ComposeRepr_12. exact LengthNat_repr.
      apply ComposeRepr_12. exact diagY_repr.
      apply (proj_represented 2 0); auto.
      apply (ConstantRepresented 0).
      apply ComposeRepr_22. exact diagMerge_repr.
      apply ComposeRepr_12. exact diagX_repr.
      apply (proj_represented 2 0); auto.
      apply (ConstantRepresented init).
      apply ComposeRepr_22. exact diagMerge_repr.
      apply ComposeRepr_12. exact diagX_repr.
      apply (proj_represented 2 0); auto.
      apply (ComposeRepr_32 _ _ _ _ H).
      apply ComposeRepr_12. exact diagX_repr.
      apply (proj_represented 2 0); auto.
      apply ComposeRepr_12. exact diagY_repr.
      apply (proj_represented 2 0); auto.
      apply (proj_represented 2 1); auto.
      intros [|k].
      apply (proj_represented 2 0); auto.
      apply MapCoordNat2_repr.
      intros n p. simpl.
      destruct (le_lt_dec (LengthNat (diagY n)) 0).
      apply Nat.leb_le in l. rewrite l. reflexivity.
      destruct (LengthNat (diagY n) <=? 0) eqn:des.
      exfalso. apply Nat.leb_le in des.
      inversion des. rewrite H1 in l. inversion l.
      apply f_equal. apply fext.
      intros i H0. rewrite CoordMapNat. reflexivity. exact H0.
    + intros i p q H0.
      unfold TreeFoldNat2Rec.
      destruct (le_lt_dec (LengthNat (diagY i)) 0). reflexivity.
      apply f_equal. apply fext.
      intros. apply f_equal, H0.
  - assert (forall n param : nat,
               Fix lt_wf (fun _ : nat => nat) (TreeFoldNat2Rec f init) (diagMerge param n)
               = diagMerge param (TreeFoldNat (f param) init n)) as H0.
    apply (Fix lt_wf
               (fun n => forall param : nat,
               Fix lt_wf (fun _ : nat => nat) (TreeFoldNat2Rec f init) (diagMerge param n)
               = diagMerge param (TreeFoldNat (f param) init n))).
    intros n IHn param.
    rewrite Fix_eq.
    unfold TreeFoldNat2Rec.
    rewrite diagYMergeId, diagXMergeId.
    unfold TreeFoldNat.
    rewrite Fix_eq. unfold TreeFoldNatRec.
    destruct (le_lt_dec (LengthNat n) 0). reflexivity.
    apply f_equal.
    apply fext. intros i H0.
    unfold TreeFoldNat2Rec in IHn.
    rewrite IHn.
    rewrite diagYMergeId. reflexivity.
    apply CoordLower, LengthPositive, l.
    intros. unfold TreeFoldNatRec.
    destruct (le_lt_dec (LengthNat x) 0). reflexivity.
    apply fext. intros. apply H0.
    intros. unfold TreeFoldNat2Rec.
    destruct (le_lt_dec (LengthNat (diagY x)) 0). reflexivity.
    apply f_equal.
    apply fext. intros. apply f_equal, H0.
    intros.
    rewrite H0, diagYMergeId. reflexivity.
Qed.

(* When the recursor may be called out of bounds, as in Subst. *)
Lemma TreeFoldNat_repr_2_ill_formed : forall (f : nat -> nat -> (nat -> nat) -> nat) init,
    FunctionRepresented 3
    (fun param n k : nat =>
     f param n (fun i : nat => diagY (CoordNat k (diagMerge param (CoordNat n i)))))
    -> (forall param n r s, (forall i, r i = s i) -> f param n r = f param n s)
    -> FunctionRepresented 2 (fun param => TreeFoldNat (f param) init).
Proof.
  intros f init H fext.
  apply (FunctionRepresented_2_ext
           (fun param i
            => diagY (Fix lt_wf (fun _ => nat)
                         (TreeFoldNat2Rec f init) (diagMerge param i)))).
  - apply ComposeRepr_12. exact diagY_repr.
    apply (ComposeRepr_12 _ diagMerge).
    2: exact diagMerge_repr.
    apply Fix_repr.
    + simpl.
      apply (FunctionRepresented_2_ext
              (fun currentStep previousValues : nat =>
     if LengthNat (diagY currentStep) <=? 0
     then diagMerge (diagX currentStep) init
     else
      diagMerge (diagX currentStep)
        (f (diagX currentStep) (diagY currentStep)
           (fun i : nat =>
            diagY
              (CoordNat previousValues
                 (diagMerge (diagX currentStep) (CoordNat (diagY currentStep) i))))))).
      apply (IfRepresented 2 (fun n p => LengthNat (diagY n) <=? 0)).
      apply (LebRepresented 2).
      apply ComposeRepr_12. exact LengthNat_repr.
      apply ComposeRepr_12. exact diagY_repr.
      apply (proj_represented 2 0); auto.
      apply (ConstantRepresented 0).
      apply ComposeRepr_22. exact diagMerge_repr.
      apply ComposeRepr_12. exact diagX_repr.
      apply (proj_represented 2 0); auto.
      apply (ConstantRepresented init).
      apply ComposeRepr_22. exact diagMerge_repr.
      apply ComposeRepr_12. exact diagX_repr.
      apply (proj_represented 2 0); auto.
      apply (ComposeRepr_32 _ _ _ _ H).
      apply ComposeRepr_12. exact diagX_repr.
      apply (proj_represented 2 0); auto.
      apply ComposeRepr_12. exact diagY_repr.
      apply (proj_represented 2 0); auto.
      apply (proj_represented 2 1); auto.
      intros n p. simpl. unfold TreeFoldNat2Rec.
      destruct (le_lt_dec (LengthNat (diagY n)) 0).
      apply Nat.leb_le in l. rewrite l. reflexivity.
      destruct (LengthNat (diagY n) <=? 0) eqn:des.
      exfalso. apply Nat.leb_le in des.
      inversion des. rewrite H1 in l. inversion l.
      apply f_equal. apply fext.
      intros i. reflexivity.
    + intros i p q H0.
      unfold TreeFoldNat2Rec.
      destruct (le_lt_dec (LengthNat (diagY i)) 0). reflexivity.
      apply f_equal. apply fext.
      intros. apply f_equal, H0.
  - assert (forall n param : nat,
               Fix lt_wf (fun _ : nat => nat) (TreeFoldNat2Rec f init) (diagMerge param n)
               = diagMerge param (TreeFoldNat (f param) init n)) as H0.
    apply (Fix lt_wf
               (fun n => forall param : nat,
               Fix lt_wf (fun _ : nat => nat) (TreeFoldNat2Rec f init) (diagMerge param n)
               = diagMerge param (TreeFoldNat (f param) init n))).
    intros n IHn param.
    rewrite Fix_eq.
    unfold TreeFoldNat2Rec.
    rewrite diagYMergeId, diagXMergeId.
    unfold TreeFoldNat.
    rewrite Fix_eq. unfold TreeFoldNatRec.
    destruct (le_lt_dec (LengthNat n) 0). reflexivity.
    apply f_equal.
    apply fext. intros i.
    unfold TreeFoldNat2Rec in IHn.
    rewrite IHn.
    rewrite diagYMergeId. reflexivity.
    apply CoordLower, LengthPositive, l.
    intros. unfold TreeFoldNatRec.
    destruct (le_lt_dec (LengthNat x) 0). reflexivity.
    apply fext. intros. apply H0.
    intros. unfold TreeFoldNat2Rec.
    destruct (le_lt_dec (LengthNat (diagY x)) 0). reflexivity.
    apply f_equal.
    apply fext. intros. apply f_equal, H0.
    intros.
    rewrite H0, diagYMergeId. reflexivity.
Qed.

Lemma TreeFoldNatBool_repr : forall (f : nat -> (nat -> bool) -> bool) (init : bool),
    FunctionRepresentedBool 2
    (fun n previousValues : nat =>
       f n (fun i : nat => CoordNat previousValues i =? 1))
    -> (forall n r s, (forall i, i < LengthNat n -> r i = s i) -> f n r = f n s)
    -> FunctionRepresentedBool 1 (TreeFoldNat f init).
Proof.
  intros f init H fext.
  apply FixBool_repr.
  apply (FunctionRepresented_2_ext
    (@ncompose 2 2 (fun n previousValues : nat =>
                      if LengthNat n <=? 0
                      then (if init then 1 else 0)
                      else
                        (if f n (fun i => CoordNat previousValues i =? 1) then 1 else 0))
               (fun k => match k with
                      | O => fun n _ => n
                      | _ => fun n prev => MapNat (CoordNat prev) n
                      end))).
  - apply ComposeRepr_n.
    apply (IfRepresented 2 (fun i j => LengthNat i <=? 0)).
    apply (LebRepresented 2).
    apply ComposeRepr_12.
    exact LengthNat_repr.
    apply (proj_represented 2 0); auto.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented (if init then 1 else 0)).
    exact H.
    intros [|k].
    apply (proj_represented 2 0); auto.
    apply (ComposeRepr_22 _ (fun i j => j) (fun i j => i) (MapNat_repr _ CoordNat_repr)).
    apply (proj_represented 2 1); auto.
    apply (proj_represented 2 0); auto.
  - intros n k. simpl.
    unfold TreeFoldNatRec.
    destruct (le_lt_dec (LengthNat n) 0).
    inversion l. rewrite H1. reflexivity.
    destruct (LengthNat n <=? 0) eqn:des.
    exfalso.
    apply Nat.leb_le in des.
    apply (Nat.lt_irrefl 0).
    exact (Nat.lt_le_trans _ _ _ l des).
    replace (f n (fun i : nat => CoordNat (MapNat (CoordNat k) n) i =? 1))
      with (f n (fun i : nat => CoordNat k (CoordNat n i) =? 1)).
    reflexivity.
    apply fext. intros i H0.
    rewrite CoordMapNat. reflexivity. exact H0.
  - intros. unfold TreeFoldNatRec.
    destruct (le_lt_dec (LengthNat i) 0).
    reflexivity. apply fext.
    intros. apply H0.
Qed.

Definition AndNat (n e : nat) : bool :=
  diagY (nat_rec (fun _ : nat => nat) (diagMerge n 1)
                 (fun currentStep val : nat =>
                    diagMerge (diagX val)
                              (if CoordNat (diagX val) currentStep =? 1
                               then diagY val else 0))
                 e)
  =? 1.

Lemma AndNat_specX : forall e n,
    diagX (nat_rec (fun _ : nat => nat) (diagMerge n 1)
                 (fun currentStep val : nat =>
                    diagMerge (diagX val)
                              (if CoordNat (diagX val) currentStep =? 1
                               then diagY val else 0))
                 e) = n.
Proof.
  induction e.
  - intro n. simpl. apply diagXMergeId.
  - intros. simpl. rewrite diagXMergeId, IHe. reflexivity.
Qed.

Lemma AndNat_spec : forall e n,
    AndNat n e = true <-> forall k, k < e -> CoordNat n k = 1.
Proof.
  induction e.
  - intros. unfold AndNat. simpl.
    rewrite diagYMergeId. simpl.
    split. intros. exfalso. inversion H0.
    intros. reflexivity.
  - intros. unfold AndNat. simpl.
    rewrite diagYMergeId.
    rewrite AndNat_specX.
    destruct (CoordNat n e =? 1) eqn:des.
    + unfold AndNat in IHe. specialize (IHe n).
      rewrite IHe. clear IHe. split.
      intros. apply Nat.le_succ_r in H0. destruct H0.
      apply H, H0. inversion H0. apply Nat.eqb_eq, des.
      intros. apply H.
      apply (Nat.lt_trans _ _ _ H0).
      apply Nat.le_refl.
    + simpl. split. intro H. discriminate H.
      intro H. specialize (H e (Nat.le_refl _)).
      rewrite H in des. discriminate des.
Qed.

Lemma AndNat_repr : FunctionRepresentedBool 2 AndNat.
Proof.
  unfold AndNat.
  apply (EqbRepresented 2).
  apply (ComposeRepr_12 _ _ diagY_repr).
  apply (ComposeRepr_22 (fun init : nat => nat_rec _ init
                                             (fun currentStep val : nat =>
        diagMerge (diagX val)
          (if CoordNat (diagX val) currentStep =? 1 then diagY val else 0)))).
  apply nat_rec_repr.
  apply ComposeRepr_22. exact diagMerge_repr.
  apply ComposeRepr_12. exact diagX_repr.
  apply (proj_represented 2 1); auto.
  apply (IfRepresented 2 (fun n k => CoordNat (diagX k) n =? 1)).
  apply (EqbRepresented 2).
  apply ComposeRepr_22. exact CoordNat_repr.
  apply ComposeRepr_12. exact diagX_repr.
  apply (proj_represented 2 1); auto.
  apply (proj_represented 2 0); auto.
  apply (ConstantRepresented 1).
  apply ComposeRepr_12. exact diagY_repr.
  apply (proj_represented 2 1); auto.
  apply (ConstantRepresented 0).
  apply ComposeRepr_22. exact diagMerge_repr.
  apply (proj_represented 2 0); auto.
  apply (ConstantRepresented 1).
  apply (proj_represented 2 1); auto.
  apply (ConstantRepresented 1).
Qed.
