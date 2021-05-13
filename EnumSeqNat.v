(** Enumeration of the finite sequences of natural numbers.
    It is done by iterating the diagonal enumeration of the discrete plane nat*nat
    (aka Cantor pairing function). This deviates from Gödel's original work,
    which used the prime decomposition theorem instead, to simplify the proofs.

    Instead of using the list datatype, we will define a function
    CoordNat : nat -> nat -> nat
    such that CoordNat n i is the i-th coordinate of the sequence
    that number n represents. By doing this we remain in the framework of
    arithmetic and primitive recursive functions. *)

Require Import PeanoNat.
Require Import ArithRing.
Require Import Arith.Compare_dec.
Require Import Arith.Wf_nat.


(** The diagonal enumeration of the discrete plane nat*nat, diagSplit,
    and its inverse function diagMerge. *)

Definition diagMerge (i j : nat) : nat
  := j + ((i+j) * S (i+j))/2.

(* 0, 1, 3, 6, ... *)
Definition natTriangle (n : nat) : nat := (n * (n+1)) / 2.

(* Biggest k such as k*(k+1) <= 2n *)
Definition biggestTriangle (n : nat) : nat :=
  (Nat.sqrt (1+8*n) - 1) / 2.

Definition diagY (n : nat) : nat := n - natTriangle (biggestTriangle n).
Definition diagX (n : nat) : nat := biggestTriangle n - diagY n.

Lemma bt_plus_one : forall n, biggestTriangle n + 1 = (Nat.sqrt (1+8*n) + 1) / 2.
Proof.
  intro n. unfold biggestTriangle.
  rewrite Nat.add_comm, <- Nat.div_add_l. 2: discriminate.
  f_equal. rewrite Nat.mul_1_l.
  pose proof (Nat.sqrt_le_square (1+8*n) 1).
  destruct (Nat.sqrt (1 + 8 * n)). exfalso.
  simpl (1*1) in H. destruct H as [H _]. apply (Nat.lt_irrefl 0), H.
  rewrite <- (Nat.add_0_r 1) at 1.
  apply Nat.add_le_mono_l, le_0_n. simpl.
  rewrite Nat.sub_0_r, Nat.add_comm. reflexivity.
Qed.

Lemma RemarkableIdentity : forall n, (n+1)*(n-1) = n*n - 1.
Proof.
  intro n. destruct n. reflexivity.
  simpl. rewrite Nat.sub_0_r, Nat.sub_0_r. ring.
Qed.

Lemma bt_below : forall n:nat, natTriangle (biggestTriangle n) <= n.
Proof.
  intro n. apply (Nat.div_le_upper_bound _ 2). discriminate.
  apply (Nat.mul_le_mono_pos_l _ _ 2). apply le_S, Nat.le_refl.
  rewrite Nat.mul_assoc, Nat.mul_assoc. change (2*2) with 4.
  apply (Nat.le_trans _ ((Nat.sqrt (1+8*n) - 1)*(biggestTriangle n + 1))).
  apply Nat.mul_le_mono_r, Nat.mul_div_le. discriminate.
  rewrite bt_plus_one, Nat.mul_comm.
  apply (Nat.mul_le_mono_pos_l _ _ 2). apply le_S, Nat.le_refl.
  rewrite Nat.mul_assoc, Nat.mul_assoc. change (2*4) with 8.
  apply (Nat.le_trans _ ((Nat.sqrt (1+8*n) + 1)*(Nat.sqrt (1+8*n) - 1))).
  apply Nat.mul_le_mono_r, Nat.mul_div_le. discriminate.
  rewrite RemarkableIdentity.
  apply (Nat.le_trans _ ((1+8*n)-1)).
  apply Nat.sub_le_mono_r.
  apply Nat.sqrt_specif.
  change (1 + (8*n) - 1) with (8*n - 0).
  rewrite Nat.sub_0_r. apply Nat.le_refl.
Qed.

Lemma twiceNatTriangle : forall n, 2 * natTriangle n = n*(n+1).
Proof.
  intro n. unfold natTriangle.
  destruct (Nat.Even_or_Odd n); destruct H; subst n.
  - rewrite <- Nat.mul_assoc. apply f_equal.
    rewrite Nat.mul_comm, Nat.div_mul. reflexivity. discriminate.
  - replace (2 * x + 1 + 1) with ((x+1)*2) by ring.
    rewrite Nat.mul_assoc, Nat.div_mul. 2: discriminate. ring.
Qed.

Lemma bt_above : forall n:nat, n < natTriangle (1 + biggestTriangle n).
Proof.
  intro n.
  apply (Nat.mul_lt_mono_pos_l 2). apply le_S, Nat.le_refl.
  rewrite twiceNatTriangle.
  rewrite Nat.add_comm, bt_plus_one.
  pose proof (Nat.sqrt_specif (1+8*n)) as [_ H].
  rewrite <- (Nat.add_comm 1).
  change (1 + Nat.sqrt (1 + 8 * n)) with (S (Nat.sqrt (1 + 8 * n))).
  remember (S (Nat.sqrt (1 + 8 * n))) as i.
  clear Heqi. unfold lt in H.
  replace (S (1+8*n)) with (2*(1+4*n)) in H by ring.
  apply Nat.div_le_lower_bound in H. 2: discriminate.
  apply (Nat.mul_lt_mono_pos_l 2). apply le_S, Nat.le_refl.
  rewrite Nat.mul_assoc. change (2*2) with 4.
  apply (Nat.le_trans _ _ _ H). clear H.
  destruct (Nat.Even_or_Odd i).
  - destruct H. subst i.
    rewrite (Nat.mul_comm 2 x).
    rewrite (Nat.div_mul x 2). 2: discriminate.
    rewrite <- Nat.mul_assoc. rewrite (Nat.mul_comm 2).
    rewrite Nat.mul_assoc.
    rewrite (Nat.div_mul _ 2). 2: discriminate.
    rewrite (Nat.mul_comm 2), Nat.mul_assoc.
    apply Nat.mul_le_mono_r.
    apply Nat.mul_le_mono_l.
    rewrite <- (Nat.add_0_r x) at 1.
    apply Nat.add_le_mono_l, le_0_n.
  - destruct H. subst i.
    rewrite (Nat.add_comm (2*x) 1).
    rewrite (Nat.mul_comm 2 x), Nat.div_add. 2: discriminate.
    change (1/2) with 0. rewrite Nat.add_0_l.
    replace ((1 + x * 2) * (1 + x * 2)) with (1+(2*x*(x+1))*2) by ring.
    rewrite Nat.div_add. 2: discriminate.
    change (1/2) with 0. rewrite Nat.add_0_l.
    rewrite Nat.mul_assoc. apply Nat.le_refl.
Qed. 

Lemma natTriangleSucc : forall n:nat, natTriangle (S n) = natTriangle n + S n.
Proof.
  intro n. unfold natTriangle.
  rewrite <- (Nat.add_comm (S n)).
  rewrite <- Nat.div_add_l. 2: discriminate.
  f_equal. ring.
Qed.

Lemma diagSplitMergeId:
  forall n : nat, diagMerge (diagX n) (diagY n) = n.
Proof.
  intro n. unfold diagMerge, diagX.
  rewrite Nat.sub_add. unfold diagY, natTriangle.
  rewrite (Nat.add_comm _ 1).
  rewrite Nat.sub_add. reflexivity.
  pose proof (bt_below n) as H.
  unfold natTriangle in H.
  rewrite (Nat.add_comm _ 1) in H. exact H.
  unfold diagY.
  apply Nat.le_sub_le_add_l.
  apply le_S_n.
  rewrite <- Nat.add_succ_r, <- natTriangleSucc.
  apply bt_above.
Qed.

Lemma natTriangleInc : forall n p:nat,
    p < n -> natTriangle p < natTriangle n.
Proof.
  induction n. intros. inversion H.
  intros p H. apply Nat.le_succ_r in H. destruct H.
  rewrite natTriangleSucc. apply (Nat.lt_le_trans _ _ _ (IHn _ H)).
  rewrite <- (Nat.add_0_r (natTriangle n)) at 1.
  apply Nat.add_le_mono_l, le_0_n.
  inversion H.
  rewrite natTriangleSucc.
  rewrite Nat.add_comm. simpl. apply le_n_S.
  rewrite <- (Nat.add_0_l (natTriangle n)) at 1.
  apply Nat.add_le_mono_r, le_0_n.
Qed.

Lemma natTriangleLe : forall n p:nat,
    p <= n -> natTriangle p <= natTriangle n.
Proof.
  intros. destruct n. inversion H. apply Nat.le_refl.
  apply Nat.le_succ_r in H. destruct H.
  apply Nat.lt_le_incl, natTriangleInc, le_n_S, H.
  rewrite H. apply Nat.le_refl.
Qed.

Lemma diagMergeTriangle : forall i j,
    biggestTriangle (diagMerge i j) = i + j.
Proof.
  intros i j.
  destruct (Nat.lt_trichotomy (biggestTriangle (diagMerge i j)) (i+j)).
  - exfalso. unfold lt in H.
    apply natTriangleLe in H.
    apply (Nat.lt_le_trans _ _ _ (bt_above (diagMerge i j))) in H.
    rewrite <- (Nat.add_0_l (natTriangle (i+j))) in H.
    unfold diagMerge, natTriangle in H.
    rewrite <- (Nat.add_comm 1) in H.
    apply Nat.add_lt_mono_r in H. inversion H.
  - destruct H. exact H. exfalso.
    apply natTriangleLe in H.
    pose proof (bt_below (diagMerge i j)) as H0.
    apply (Nat.le_trans _ _ _ H) in H0. clear H.
    rewrite natTriangleSucc, Nat.add_comm in H0.
    unfold natTriangle, diagMerge in H0.
    rewrite <- (Nat.add_comm 1) in H0.
    apply Nat.add_le_mono_r in H0.
    apply (Nat.lt_irrefl (S(i+j))). apply (Nat.le_lt_trans _ _ _ H0), le_n_S.
    apply (Nat.add_le_mono_r 0), le_0_n.
Qed.

Lemma diagYMergeId : forall i j : nat, diagY (diagMerge i j) = j.
Proof.
  intros i j. unfold diagY.
  rewrite diagMergeTriangle.
  unfold diagMerge, natTriangle.
  rewrite <- (Nat.add_comm 1). apply Nat.add_sub.
Qed.

Lemma diagXMergeId : forall i j : nat, diagX (diagMerge i j) = i.
Proof.
  intros i j.
  unfold diagX. rewrite diagYMergeId, diagMergeTriangle.
  apply Nat.add_sub.
Qed.


(** Enumeration of finite sequences of natural numbers. *)

(* We store the length of the list in its first element, like Pascal strings.
   We could have defined the length as the first index where the tail becomes
   zero (like C strings), but then lists (0,0,0) and (0,0,0,0) would have
   both been represented by zero. *)
Definition LengthNat : nat -> nat := diagX.

Definition NilNat : nat := O.
Definition ConsNat (n : nat) (l : nat) : nat := (* make list n :: l *)
  diagMerge (S (LengthNat l)) (diagMerge n (diagY l)).
Definition HeadNat (n : nat) : nat :=
  match LengthNat n with
  | O => NilNat
  | S _ => diagX (diagY n)
  end. 
Definition TailNat (n : nat) : nat :=
  match LengthNat n with
  | O => NilNat
  | S k => diagMerge k (diagY (diagY n))
  end.

Fixpoint NthTailNat (list k : nat) : nat :=
  match k with
  | O => list
  | S p => NthTailNat (TailNat list) p
  end.

Lemma TailConsNat : forall (n m : nat), TailNat (ConsNat n m) = m.
Proof.
  intros n m. unfold TailNat, ConsNat, LengthNat.
  rewrite diagXMergeId, diagYMergeId, diagYMergeId.
  apply (diagSplitMergeId m).
Qed.

Lemma NthTailConsNat : forall h tl k,
    NthTailNat (ConsNat h tl) (S k) = NthTailNat tl k.
Proof.
  induction k.
  - simpl. rewrite TailConsNat. reflexivity.
  - change (NthTailNat (TailNat (ConsNat h tl)) (S k) = NthTailNat tl (S k)).
    rewrite TailConsNat. reflexivity.
Qed.

Lemma LengthNilNat : LengthNat NilNat = 0.
Proof.
  reflexivity.
Qed. 

Lemma LengthConsNat : forall h n, LengthNat (ConsNat h n) = S (LengthNat n).
Proof.
  intros h n.
  unfold ConsNat, LengthNat. rewrite diagXMergeId. reflexivity.
Qed.

Lemma LengthTailNat : forall n:nat, LengthNat (TailNat n) = pred (LengthNat n).
Proof.
  intro n. unfold TailNat, LengthNat.
  destruct (diagX n). reflexivity. simpl.
  rewrite diagXMergeId. reflexivity.
Qed.

Lemma LengthNthTailNat : forall k n, LengthNat (NthTailNat n k) = LengthNat n - k.
Proof.
  induction k.
  - intro n. rewrite Nat.sub_0_r. reflexivity.
  - intro n. simpl. rewrite IHk, LengthTailNat.
    destruct (LengthNat n); reflexivity.
Qed. 

Definition CoordNat (list i : nat) : nat := HeadNat (NthTailNat list i).

Lemma HeadTailDecompNat : forall n:nat,
    0 < LengthNat n -> n = ConsNat (CoordNat n 0) (TailNat n).
Proof.
  intros n H.
  unfold ConsNat, CoordNat, TailNat, HeadNat, LengthNat.
  unfold LengthNat in H.
  pose proof (diagSplitMergeId n). simpl.
  destruct (diagX n). exfalso; inversion H.
  rewrite diagXMergeId, diagYMergeId.
  rewrite diagSplitMergeId. symmetry. exact H0.
Qed.

Lemma CoordConsHeadNat : forall (n h : nat),
    CoordNat (ConsNat h n) O = h.
Proof.
  intros n h. unfold CoordNat, ConsNat, HeadNat, LengthNat. simpl.
  rewrite diagXMergeId, diagYMergeId, diagXMergeId. reflexivity.
Qed.

Lemma CoordConsTailNat : forall (i n h : nat),
    CoordNat (ConsNat h n) (S i) = CoordNat n i.
Proof.
  intros. unfold CoordNat. simpl. rewrite TailConsNat. reflexivity.
Qed.

Lemma CoordNatAboveLength : forall i n,
    LengthNat n <= i
    -> CoordNat n i = 0.
Proof.
  intros. unfold CoordNat.
  pose proof (LengthNthTailNat i n) as H0.
  pose proof (Nat.sub_0_le (LengthNat n) i) as [_ H1].
  rewrite (H1 H) in H0.
  unfold HeadNat, LengthNat. unfold LengthNat in H0.
  rewrite H0. reflexivity.
Qed.

Lemma CoordTailNat : forall n i, CoordNat (TailNat n) i = CoordNat n (S i).
Proof.
  reflexivity.
Qed. 

Lemma diagMergeIncr : forall a b c d,
    a <= b
    -> c <= d
    -> diagMerge a c <= diagMerge b d.
Proof.
  intros. unfold diagMerge.
  apply Nat.add_le_mono. exact H0.
  apply Nat.div_le_mono. discriminate.
  apply Nat.mul_le_mono.
  apply Nat.add_le_mono; assumption.
  apply le_n_S.
  apply Nat.add_le_mono; assumption.
Qed.

Lemma biggestTrianglePos : forall n:nat, 0 < biggestTriangle (S n).
Proof.
  intro n. apply Nat.div_str_pos. split.
  apply le_S, Nat.le_refl.
  assert (9 <= 1 + 8 * S n) as H.
  { change (S n) with (1+n). rewrite Nat.mul_add_distr_l.
    rewrite Nat.add_assoc. rewrite <- (Nat.add_0_r 9).
    apply Nat.add_le_mono_l, le_0_n. }
  pose proof (Nat.sqrt_le_square (1 + 8 * S n) 3) as [H0 _].
  specialize (H0 H).
  destruct (Nat.sqrt (1+8*S n)). inversion H0.
  apply le_S_n. simpl. rewrite Nat.sub_0_r. exact H0.
Qed.

Lemma diagSplitSndLower : forall n:nat, 0 < n -> diagY n < n.
Proof.
  intros. unfold diagY.
  destruct n. inversion H. clear H. apply le_n_S.
  destruct (biggestTriangle (S n)) eqn:des.
  exfalso. pose proof (biggestTrianglePos n).
  rewrite des in H. inversion H.
  rewrite natTriangleSucc, Nat.add_comm. simpl.
  apply Nat.le_sub_l.
Qed.

Lemma diagSplitFstLe : forall n:nat, diagX n <= n.
Proof.
  intro n. rewrite <- (diagSplitMergeId n).
  rewrite diagXMergeId. unfold diagMerge.
  apply (Nat.le_trans _ (0 + (diagX n+0) * S (diagX n + 0) / 2)).
  - rewrite Nat.add_0_l, Nat.add_0_r.
    apply Nat.div_le_lower_bound. auto.
    rewrite (Nat.mul_comm (diagX n)).
    simpl.
    apply Nat.add_le_mono_l.
    rewrite Nat.add_0_r.
    destruct (diagX n). apply Nat.le_refl.
    rewrite <- (Nat.mul_1_l (S n0)) at 1.
    apply Nat.mul_le_mono_r.
    apply le_n_S, le_0_n.
  - apply (diagMergeIncr (diagX n) (diagX n) 0 (diagY n)).
    apply Nat.le_refl. apply le_0_n.
Qed.

Lemma TailLe : forall n, TailNat n <= n.
Proof.
  intros. unfold TailNat, LengthNat.
  destruct (diagX n) eqn:des.
  apply le_0_n. apply (Nat.le_trans _ (diagMerge (diagX n) (diagY n))).
  apply diagMergeIncr. rewrite des. apply le_S, Nat.le_refl.
  destruct (diagY n). apply Nat.le_refl.
  apply Nat.lt_le_incl, diagSplitSndLower.
  apply le_n_S, le_0_n.
  rewrite diagSplitMergeId. apply Nat.le_refl.
Qed.

Lemma HeadLower : forall n, 0 < n -> HeadNat n < n.
Proof.
  intros. unfold HeadNat, LengthNat.
  pose proof (diagSplitMergeId n).
  destruct (diagX n) eqn:des. exact H.
  apply (Nat.le_lt_trans _ _ _ (diagSplitFstLe _)).
  apply diagSplitSndLower, H.
Qed.

Lemma NthTailLe : forall i n, NthTailNat n i <= n.
Proof.
  induction i.
  - intros. apply Nat.le_refl.
  - intros. simpl.
    apply (Nat.le_trans _ _ _ (IHi _)).
    destruct n. apply Nat.le_refl.
    apply (TailLe (S n)).
Qed.

Lemma CoordLower : forall (n i : nat), 0 < n -> CoordNat n i < n.
Proof.
  intros n i npos. unfold CoordNat.
  destruct (NthTailNat n i) eqn:des. exact npos.
  apply (Nat.lt_le_trans _ (NthTailNat n i)).
  rewrite des. apply HeadLower, le_n_S, le_0_n.
  apply NthTailLe.
Qed.

(* Concatenation of lists n and p, under the hypothesis that LengthNat n = lengthN. *)
Fixpoint ConcatWithLength (n lengthN p : nat) : nat :=
  match lengthN with
  | O => p
  | S j => ConsNat (diagX n) (ConcatWithLength (diagY n) j p)
  end.
Definition ConcatNat (n p : nat) : nat :=
  ConcatWithLength (diagY n) (LengthNat n) p.

Lemma LengthConcatNat : forall (n p : nat),
    LengthNat (ConcatNat n p) = LengthNat n + LengthNat p.
Proof.
  intros. unfold ConcatNat, LengthNat.
  revert p.
  generalize (diagY n) as k.
  generalize (diagX n) as lengthK.
  clear n.
  induction lengthK.
  - reflexivity.
  - intros k p. simpl. unfold ConsNat, LengthNat.
    rewrite diagXMergeId, IHlengthK. reflexivity.
Qed.

Lemma ConcatNilNat : forall n, ConcatNat NilNat n = n.
Proof.
  reflexivity.
Qed.

Lemma ConcatConsNat : forall i j k,
    ConcatNat (ConsNat i j) k = ConsNat i (ConcatNat j k).
Proof.
  intros. unfold ConcatNat, ConsNat, LengthNat.
  rewrite diagXMergeId, diagYMergeId.
  simpl. rewrite diagXMergeId, diagYMergeId.
  generalize (diagX j) as a.
  generalize (diagY j) as b. clear j. intros b a.
  revert a b i k.
  induction a. reflexivity.
  intros.
  simpl.
  rewrite IHa. reflexivity.
Qed.

Lemma CoordConcatNatFirst : forall f g k,
    k < LengthNat f
    -> CoordNat (ConcatNat f g) k = CoordNat f k.
Proof.
  assert (forall l f g k,
             l = LengthNat f
    -> k < LengthNat f
    -> CoordNat (ConcatNat f g) k = CoordNat f k).
  induction l.
  - intros. rewrite <- H in H0. inversion H0.
  - intros.
    rewrite (HeadTailDecompNat f), ConcatConsNat.
    destruct k. rewrite CoordConsHeadNat, CoordConsHeadNat. reflexivity.
    rewrite CoordConsTailNat, CoordConsTailNat.
    apply IHl. rewrite LengthTailNat, <- H. reflexivity.
    rewrite LengthTailNat, <- H. simpl. apply le_S_n.
    rewrite H. exact H0.
    rewrite <- H. apply le_n_S, le_0_n.
  - intros. apply (H (LengthNat f)).
    reflexivity. exact H0.
Qed.

Lemma CoordConcatNatSecond : forall f g k,
    CoordNat (ConcatNat f g) (k + LengthNat f) = CoordNat g k.
Proof.
  assert (forall l f g k,
             l = LengthNat f
             -> CoordNat (ConcatNat f g) (k + LengthNat f) = CoordNat g k).
  induction l.
  - intros. unfold ConcatNat, LengthNat. unfold LengthNat in H.
    rewrite <- H.
    simpl. rewrite Nat.add_0_r. reflexivity.
  - intros.
    rewrite (HeadTailDecompNat f) at 1.
    rewrite ConcatConsNat, <- H.
    rewrite Nat.add_succ_r, CoordConsTailNat.
    replace l with (LengthNat (TailNat f)).
    apply IHl. rewrite LengthTailNat, <- H. reflexivity.
    rewrite LengthTailNat, <- H. reflexivity.
    rewrite <- H. apply le_n_S, le_0_n.
  - intros. apply (H (LengthNat f)). reflexivity.
Qed.

Fixpoint SetCoordNat (n coord val : nat) : nat :=
  if Nat.ltb coord (LengthNat n) then
    match coord with
    | O => ConsNat val (TailNat n)
    | S k => ConsNat (CoordNat n 0) (SetCoordNat (TailNat n) k val)
    end
  else n.

Lemma SetCoordNatAbove : forall n coord val,
    LengthNat n <= coord
    -> SetCoordNat n coord val = n.
Proof.
  intros. destruct coord. simpl.
  inversion H. rewrite H1. reflexivity.
  simpl. destruct (S coord <? LengthNat n) eqn:des. 2: reflexivity.
  exfalso. apply Nat.ltb_lt in des.
  apply (Nat.lt_irrefl (S coord)).
  exact (Nat.lt_le_trans _ _ _ des H).
Qed.

Lemma SetCoordIdemNat : forall coord n,
    SetCoordNat n coord (CoordNat n coord) = n.
Proof.
  induction coord.
  - intro n. simpl.
    destruct (0 <? LengthNat n) eqn:des. 2: reflexivity.
    rewrite <- HeadTailDecompNat. reflexivity.
    apply Nat.ltb_lt, des.
  - intro n. simpl.
    destruct (S coord <? LengthNat n) eqn:des. 2: reflexivity.
    rewrite <- CoordTailNat.
    rewrite (IHcoord (TailNat n)).
    rewrite <- HeadTailDecompNat. reflexivity.
    destruct (LengthNat n). inversion des.
    apply le_n_S, le_0_n.
Qed.

Lemma SetCoordConsNat_0 : forall n p val,
    SetCoordNat (ConsNat n p) 0 val = ConsNat val p.
Proof.
  intros. simpl.
  rewrite LengthConsNat. simpl.
  rewrite TailConsNat. reflexivity.
Qed.

Lemma SetCoordConsNat : forall coord n p val,
    SetCoordNat (ConsNat n p) (S coord) val
    = ConsNat n (SetCoordNat p coord val).
Proof.
  induction coord.
  - intros. simpl. rewrite LengthConsNat.
    destruct (LengthNat p) eqn:des. reflexivity.
    simpl. rewrite TailConsNat, des. simpl.
    rewrite CoordConsHeadNat. reflexivity.
  - intros.
    change (SetCoordNat (ConsNat n p) (S (S coord)) val)
      with (if Nat.ltb (S (S coord)) (LengthNat (ConsNat n p)) then
              ConsNat (CoordNat (ConsNat n p) 0) (SetCoordNat (TailNat (ConsNat n p)) (S coord) val)
            else (ConsNat n p)).
    simpl (ConsNat n (SetCoordNat p (S coord) val)).
    rewrite LengthConsNat.
    change (S (S coord) <? S (LengthNat p)) with ((S coord) <? (LengthNat p)).
    destruct (S coord <? LengthNat p) eqn:des. 2: reflexivity.
    rewrite CoordConsHeadNat. apply f_equal.
    rewrite TailConsNat.
    destruct (LengthNat p) eqn:lenp. exfalso; inversion des.
    rewrite (HeadTailDecompNat p) at 1.
    rewrite IHcoord. reflexivity. rewrite lenp. apply le_n_S, le_0_n.
Qed.

Lemma LengthSetCoordNat : forall coord n val,
    LengthNat (SetCoordNat n coord val) = LengthNat n.
Proof.
  induction coord.
  - intros. simpl.
    destruct (0 <? LengthNat n) eqn:des. 2: reflexivity.
    rewrite LengthConsNat, LengthTailNat.
    destruct (LengthNat n). discriminate. reflexivity.
  - intros. simpl.
    destruct (S coord <? LengthNat n) eqn:des. 2: reflexivity.
    rewrite LengthConsNat, IHcoord, LengthTailNat.
    destruct (LengthNat n). discriminate. reflexivity.
Qed.

Lemma CoordSetCoordNat : forall i n val,
    CoordNat (SetCoordNat n i val) i
    = (if Nat.ltb i (LengthNat n) then val else CoordNat n i).
Proof.
  induction i.
  - intros. simpl. destruct (0 <? LengthNat n). 2: reflexivity.
    apply CoordConsHeadNat.
  - intros. simpl.
    destruct (S i <? LengthNat n) eqn:des. 2: reflexivity.
    rewrite CoordConsTailNat.
    rewrite (IHi (TailNat n)).
    destruct (i <? LengthNat (TailNat n)) eqn:des2. reflexivity.
    rewrite LengthTailNat in des2.
    destruct (LengthNat n). inversion des.
    simpl in des2.
    change (S i <? S n0) with (i <? n0) in des.
    rewrite des in des2. discriminate.
Qed.

Lemma CoordSetCoordDiffNat : forall i n val k,
    i <> k
    -> CoordNat (SetCoordNat n i val) k = CoordNat n k.
Proof.
  induction i.
  - intros. simpl.
    destruct (0 <? LengthNat n) eqn:des.
    destruct k. exfalso. apply H. reflexivity.
    rewrite CoordConsTailNat.
    apply CoordTailNat.
    reflexivity.
  - intros. simpl. destruct (S i <? LengthNat n) eqn:des.
    2: reflexivity. destruct k.
    apply CoordConsHeadNat.
    rewrite CoordConsTailNat, IHi.
    apply CoordTailNat.
    intro abs. rewrite abs in H. apply H. reflexivity.
Qed.

Lemma SetCoordDiffNat : forall i n val,
    SetCoordNat n i val <> n
    -> (i < LengthNat n /\ CoordNat n i <> val).
Proof.
  intros. split.
  destruct i. simpl in H.
  destruct (0 <? LengthNat n) eqn:des. apply Nat.ltb_lt in des. exact des.
  exfalso. apply H. reflexivity.
  simpl in H.
  destruct (S i <? LengthNat n) eqn:des. apply Nat.ltb_lt in des. exact des.
  exfalso. apply H. reflexivity.
  revert i n H. induction i.
  - intros. simpl in H.
    destruct (0 <? LengthNat n) eqn:des. apply Nat.ltb_lt in des.
    intro abs.
    rewrite (HeadTailDecompNat n des) in H at 2.
    rewrite abs in H. apply H. reflexivity.
    exfalso. apply H. reflexivity.
  - intros. simpl in H. destruct (S i <? LengthNat n) eqn:des.
    2: contradict H; reflexivity.
    intro abs. rewrite <- CoordTailNat in abs.
    apply (IHi (TailNat n)). 2: exact abs.
    intro H0. rewrite H0, <- HeadTailDecompNat in H.
    apply H. reflexivity.
    apply Nat.ltb_lt in des. apply (Nat.le_lt_trans _ (S i)).
    apply le_0_n. exact des.
Qed.

Lemma SetCoordTailNat : forall n i v,
    SetCoordNat (TailNat n) i v
    = TailNat (SetCoordNat n (S i) v).
Proof.
  induction i.
  - intro v. simpl. rewrite LengthTailNat. simpl.
    destruct (LengthNat n). reflexivity. simpl.
    destruct n0. reflexivity. simpl.
    rewrite TailConsNat. reflexivity.
  - intro v. simpl. rewrite LengthTailNat.
    destruct (LengthNat n). reflexivity. simpl.
    change (S (S i) <? S n0) with (S i <? n0).
    destruct (S i <? n0). 2: reflexivity.
    rewrite TailConsNat. reflexivity.
Qed.

Lemma NthTailSetCoordNat : forall k n i v,
    i < k
    -> NthTailNat (SetCoordNat n i v) k = NthTailNat n k.
Proof.
  induction k.
  - intros. inversion H.
  - intros. destruct i.
    simpl. destruct (0 <? LengthNat n). 2: reflexivity.
    rewrite TailConsNat. reflexivity.
    change (NthTailNat (TailNat (SetCoordNat n (S i) v)) k = NthTailNat n (S k)).
    rewrite <- SetCoordTailNat. apply IHk. apply le_S_n, H.
Qed.

Lemma SetSetIdemNat : forall i n v w,
    SetCoordNat (SetCoordNat n i v) i w = SetCoordNat n i w.
Proof.
  induction i.
  - intros. simpl.
    destruct (LengthNat n) eqn:des. simpl.
    rewrite des. reflexivity. simpl.
    rewrite LengthConsNat. simpl.
    rewrite TailConsNat. reflexivity.
  - intros. simpl.
    destruct (S i <? LengthNat n) eqn:des.
    2: rewrite des; reflexivity.
    rewrite LengthConsNat, LengthSetCoordNat, LengthTailNat.
    simpl. destruct (LengthNat n) eqn:lenN. inversion des.
    simpl. rewrite des.
    rewrite CoordConsHeadNat, TailConsNat, IHi. reflexivity.
Qed.

Lemma SetSetCommuteDiff : forall i j n v w,
    i <> j
    -> SetCoordNat (SetCoordNat n i v) j w
      = SetCoordNat (SetCoordNat n j w) i v.
Proof.
  assert (forall j i n v w,
    i < j
    -> SetCoordNat (SetCoordNat n i v) j w
      = SetCoordNat (SetCoordNat n j w) i v).
  induction j.
  - intros. inversion H.
  - intros. simpl.
    rewrite LengthSetCoordNat.
    destruct (S j <? LengthNat n) eqn:des. 2: reflexivity.
    apply Nat.ltb_lt in des.
    destruct i.
    + simpl. rewrite LengthConsNat, LengthSetCoordNat, LengthTailNat.
      destruct (LengthNat n) eqn:lenN. inversion des.
      simpl. rewrite CoordConsHeadNat, TailConsNat, TailConsNat. reflexivity.
    + apply le_S_n in H.
      rewrite SetCoordConsNat, <- IHj. 2: exact H.
      simpl (SetCoordNat n (S i) v) at 1.
      pose proof (Nat.ltb_lt (S i) (LengthNat n)) as [_ H0].
      rewrite H0, CoordConsHeadNat.
      rewrite <- SetCoordTailNat. reflexivity.
      apply (Nat.le_lt_trans _ (S j)). apply le_S, H. exact des.
  - intros. destruct (le_lt_dec j i). 2: apply H, l.
    destruct (le_lt_dec i j).
    exfalso. apply H0. apply Nat.le_antisymm; assumption.
    symmetry. apply H, l0.
Qed.

Lemma LengthPositive : forall n:nat, 0 < LengthNat n -> 0 < n.
Proof.
  intros [|n] H.
  - exfalso. inversion H.
  - apply le_n_S, le_0_n.
Qed.

(* Fold of a natural number interpreted as a tree. The list interpretation
   CoordNat is applied recursively to each list's element, to make a tree.
   The well-founded recursion is used on the strict order < of nat,
   which extracts simply in OCaml without fuel.
   match le_lt_dec (LengthNat n) 0 stops the recursion on ill-formed lists,
   we could allow it to continue one step further by match n instead. *)
Definition TreeFoldNatRec {A : Type} (f : nat -> (nat -> A) -> A) (a : A)
           (n : nat) (rec : forall k : nat, k < n -> A) : A
  := match le_lt_dec (LengthNat n) 0 with
     | left _ => a
     | right l => f n (fun i => rec (CoordNat n i) (CoordLower n i (LengthPositive _ l)))
     end.
Definition TreeFoldNat {A : Type} (f : nat -> (nat -> A) -> A) (b : A) : nat -> A
  := Fix lt_wf (fun _ => A) (TreeFoldNatRec f b).

Definition TreeFoldNat_nil : forall {A : Type} (f : nat -> (nat -> A) -> A) (b : A),
    TreeFoldNat f b 0 = b.
Proof.
  reflexivity.
Qed. 

(* Find number k in sequence n, from beginning to coordinate last excluded. *)
Fixpoint FindNat (n k last : nat) : bool :=
  match last with
  | 0 => false
  | S p => Nat.eqb k (CoordNat n p) || FindNat n k p
  end.

Lemma FindNat_true : forall n k last,
    prod (FindNat n k last = true -> { p:nat | p < last /\ k = CoordNat n p })
         ({ p:nat | p < last /\ k = CoordNat n p } -> FindNat n k last = true).
Proof.
  split.
  - induction last.
    + intro H. discriminate.
    + intro H. simpl in H.
      apply Bool.orb_prop in H. destruct (k =? CoordNat n last) eqn:des.
      * clear H IHlast. exists last.
        split. apply Nat.le_refl.
        apply Nat.eqb_eq in des. exact des.
      * destruct IHlast as [p H1]. destruct H. discriminate. exact H.
        destruct H1. subst k. exists p. split.
        apply le_S, H0. reflexivity.
  - induction last.
    intros [p [H _]]. inversion H.
    intros [p [H H0]]. subst k.
    simpl. apply Bool.orb_true_intro.
    apply Nat.le_succ_r in H. destruct H.
    right. apply IHlast. exists p. split. exact H. reflexivity.
    inversion H. subst p. left. apply Nat.eqb_refl.
Qed.

(* Map f to list n up to index i excluded. *)
Fixpoint MapNatRec (f : nat -> nat) (n i : nat) : nat :=
  match i with
  | 0 => n
  | S k => SetCoordNat (MapNatRec f n k) k (f (CoordNat n k))
  end.

Definition MapNat f n := MapNatRec f n (LengthNat n).

Lemma LengthMapRecNat : forall i f n, LengthNat (MapNatRec f n i) = LengthNat n.
Proof.
  induction i; [reflexivity|].
  simpl. intros. rewrite LengthSetCoordNat, IHi. reflexivity.
Qed.

Lemma LengthMapNat : forall f n, LengthNat (MapNat f n) = LengthNat n.
Proof.
  intros. unfold MapNat. apply LengthMapRecNat.
Qed.

Lemma CoordMapNat : forall f n k,
    k < LengthNat n
    -> CoordNat (MapNat f n) k = f (CoordNat n k).
Proof.
  assert (forall i f n k,
    i <= LengthNat n
    -> k < i
    -> CoordNat (MapNatRec f n i) k = f (CoordNat n k)).
  induction i.
  - intros. inversion H0.
  - intros. simpl. apply Nat.le_succ_r in H0.
    destruct H0.
    + rewrite CoordSetCoordDiffNat. apply IHi.
      apply (Nat.le_trans _ (S i)). apply le_S, Nat.le_refl.
      exact H. exact H0. intro abs. subst k. exact (Nat.lt_irrefl i H0).
    + inversion H0. subst k. clear H0 IHi.
      rewrite CoordSetCoordNat, LengthMapRecNat.
      apply Nat.ltb_lt in H. rewrite H. reflexivity.
  - intros. apply H.
    apply Nat.le_refl. exact H0.
Qed.

Lemma MapConsNat : forall f h tl,
    MapNat f (ConsNat h tl) = ConsNat (f h) (MapNat f tl).
Proof.
  assert (forall i f h tl,
    i <= LengthNat tl ->
    MapNatRec f (ConsNat h tl) (S i) = ConsNat (f h) (MapNatRec f tl i)).
  induction i.
  - intros. simpl. rewrite LengthConsNat. simpl.
    rewrite CoordConsHeadNat, TailConsNat. reflexivity.
  - intros.
    change (SetCoordNat (MapNatRec f (ConsNat h tl) (S i)) (S i) (f (CoordNat (ConsNat h tl) (S i)))
            = ConsNat (f h) (MapNatRec f tl (S i))).
    rewrite IHi. rewrite SetCoordConsNat.
    apply f_equal. simpl. rewrite CoordConsTailNat. reflexivity.
    apply (Nat.le_trans _ (S i)). apply le_S, Nat.le_refl. exact H.
  - intros. unfold MapNat.
    rewrite LengthConsNat, H. reflexivity. apply Nat.le_refl.
Qed.

Lemma MapIdNat : forall n, MapNat (fun x => x) n = n.
Proof.
  intros. unfold MapNat.
  induction (LengthNat n). reflexivity.
  simpl. rewrite IHn0. apply SetCoordIdemNat.
Qed.

Lemma MapNatExt : forall f g n,
    (forall k, k < LengthNat n -> f (CoordNat n k) = g (CoordNat n k))
    -> MapNat f n = MapNat g n.
Proof.
  intros. unfold MapNat.
  induction (LengthNat n). reflexivity.
  simpl. rewrite IHn0, H. reflexivity.
  apply Nat.le_refl. intros. apply H.
  apply (Nat.lt_le_trans _ _ _ H0). apply le_S, Nat.le_refl.
Qed.

Lemma MapNatSetAbove : forall coord f p i val,
    i <= coord
    -> MapNatRec f (SetCoordNat p coord val) i
      = SetCoordNat (MapNatRec f p i) coord val.
Proof.
  induction i.
  - reflexivity.
  - intros. simpl.
    rewrite IHi.
    rewrite CoordSetCoordDiffNat.
    apply SetSetCommuteDiff.
    intro abs. rewrite abs in H.
    exact (Nat.lt_irrefl i H).
    intro abs. rewrite abs in H.
    exact (Nat.lt_irrefl i H).
    apply (Nat.le_trans _ (S i)).
    apply le_S, Nat.le_refl. exact H.
Qed.

Lemma MapMapNat : forall f g n,
    MapNat g (MapNat f n) = MapNat (fun x => g (f x)) n.
Proof.
  assert (forall i (f g : nat -> nat) (n : nat),
             i <= LengthNat n ->
             MapNatRec g (MapNatRec f n i) i =
             MapNatRec (fun x : nat => g (f x)) n i).
  induction i; [reflexivity|].
  intros. simpl. rewrite MapNatSetAbove.
  2: apply Nat.le_refl. rewrite IHi, SetSetIdemNat.
  rewrite CoordSetCoordNat, LengthMapRecNat.
  apply Nat.ltb_lt in H. rewrite H. reflexivity.
  apply (Nat.le_trans _ (S i)). apply le_S, Nat.le_refl. exact H.
  intros. unfold MapNat. rewrite LengthMapRecNat. apply H.
  apply Nat.le_refl.
Qed.

Lemma MapNatDiff : forall f p,
    MapNat f p <> p
    -> { j:nat | j < LengthNat p /\ f (CoordNat p j) <> CoordNat p j }.
Proof.
  intros f p. unfold MapNat.
  induction (LengthNat p).
  - intros. exfalso. simpl in H. apply H. reflexivity.
  - intros. simpl in H.
    destruct (Nat.eq_dec (MapNatRec f p n) p).
    rewrite e in H.
    apply SetCoordDiffNat in H. destruct H. exists n.
    split. apply Nat.le_refl. intro abs. symmetry in abs. contradiction.
    destruct (IHn n0). exists x. split. 2: apply a.
    apply le_S, a.
Qed.

Lemma MapNatTruncated : forall f p,
    NthTailNat p (LengthNat p) = 0
    -> NthTailNat (MapNat f p) (LengthNat p) = 0.
Proof.
  assert (forall i (f : nat -> nat) (p : nat),
             i <= LengthNat p ->
  NthTailNat p (LengthNat p) = 0 ->
  NthTailNat (MapNatRec f p i) (LengthNat p) = 0).
  induction i.
  - intros. simpl. exact H0.
  - intros. simpl. rewrite NthTailSetCoordNat. 2: exact H.
    apply IHi. refine (Nat.le_trans _ _ _ _ H). apply le_S, Nat.le_refl.
    exact H0.
  - intros. apply H. apply Nat.le_refl. exact H0.
Qed.

Fixpoint RangeNat (start len : nat) : nat :=
  match len with
  | O => NilNat
  | S k => ConsNat start (RangeNat (S start) k)
  end.

Lemma LengthRangeNat : forall len start,
    LengthNat (RangeNat start len) = len.
Proof.
  induction len.
  reflexivity. simpl.
  intros. rewrite LengthConsNat, IHlen. reflexivity.
Qed.

Lemma CoordRangeNat : forall len start k,
    k < len
    -> CoordNat (RangeNat start len) k = start + k.
Proof.
  induction len.
  intros. inversion H.
  intros. simpl. 
  destruct k. rewrite CoordConsHeadNat, Nat.add_0_r. reflexivity.
  rewrite CoordConsTailNat, IHlen, Nat.add_succ_r. reflexivity.
  apply le_S_n, H.
Qed.

Lemma RangeNatTruncated : forall len start,
    NthTailNat (RangeNat start len) len = 0.
Proof.
  induction len.
  reflexivity. intros. simpl. rewrite TailConsNat.
  apply IHlen.
Qed. 

Lemma TruncatedEqNat : forall n p,
    LengthNat n = LengthNat p
    -> NthTailNat n (LengthNat n) = 0
    -> NthTailNat p (LengthNat p) = 0
    -> (forall k, k < LengthNat n -> CoordNat n k = CoordNat p k)
    -> n = p.
Proof.
  assert (forall i n p,
             i = LengthNat n
    -> LengthNat n = LengthNat p
    -> NthTailNat n (LengthNat n) = 0
    -> NthTailNat p (LengthNat p) = 0
    -> (forall k, k < LengthNat n -> CoordNat n k = CoordNat p k)
    -> n = p).
  induction i.
  - intros. rewrite <- H in H1. rewrite <- H in H0. rewrite <- H0 in H2.
    simpl in H1. rewrite H1. simpl in H2. rewrite H2. reflexivity.
  - intros. specialize (IHi (TailNat n) (TailNat p)).
    rewrite (HeadTailDecompNat n), (HeadTailDecompNat p).
    rewrite H3, IHi. reflexivity.
    rewrite LengthTailNat, <- H. reflexivity.
    rewrite LengthTailNat, LengthTailNat, H0. reflexivity.
    rewrite LengthTailNat. destruct (LengthNat n). discriminate H. exact H1.
    rewrite LengthTailNat. rewrite H0 in H.
    destruct (LengthNat p). discriminate H. exact H2.
    intros k H4. rewrite CoordTailNat, CoordTailNat. apply H3.
    rewrite LengthTailNat in H4. destruct (LengthNat n).
    discriminate H. apply le_n_S. exact H4.
    rewrite <- H. apply le_n_S, le_0_n.
    rewrite <- H0, <- H. apply le_n_S, le_0_n.
    rewrite <- H. apply le_n_S, le_0_n.
  - intros. apply (H (LengthNat n) n p eq_refl H0 H1 H2 H3).
Qed.

Global Opaque ConsNat. (* prevent the type checker from freezing *)
Global Opaque TailNat.
Global Opaque LengthNat.
Global Opaque CoordNat.
Global Opaque diagX diagY diagMerge.
