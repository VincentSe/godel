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


(** Enumeration of finite sequences of natural numbers.

    Ideally we would define a computable bijection between list nat and nat,
    but practically it is simpler to define a retraction
    encode : list nat >-> nat  and  CoordNat : nat ->> list nat.
    encode iterates diagMerge on the elements of the list, and finally
    diagMerges the length of the list at the beginning. It is similar to strings
    in the Pascal programming language. Conversely, CoordNat first extracts the
    length and then extracts length elements with diagX and diagY.

    We call truncated a number in the range of encode, it is the standard
    code of the corresponding list. Those truncated numbers are characterized
    by the vanishing of the tail after length iterations.

    We also have this important property: encode (x_0, ..., x_n) is strictly
    greater than all x_i's. This allows to consider a natural number as a list
    of lists, and therefore as a tree. The decreasing of coordinates makes
    well founded recursions on those trees.

    Instead of Pascal strings we could have considered C strings. Those make a
    bijection between nat and the lists of nat that do not finish by 0.
    It appears simpler than our retraction, but lacks the decreasing property
    of coordinates. *)

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

Lemma HeadConsNat : forall (n m : nat), HeadNat (ConsNat n m) = n.
Proof.
  intros n m. unfold HeadNat, ConsNat, LengthNat.
  rewrite diagXMergeId.
  rewrite diagYMergeId.
  rewrite diagXMergeId.
  reflexivity.
Qed.

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

Lemma NthTailNthTailNat : forall p i n,
  NthTailNat (NthTailNat i p) n = NthTailNat i (p + n).
Proof.
  induction p. reflexivity.
  intros. simpl.
  rewrite IHp. reflexivity.
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

Lemma CoordNthTailNat : forall j i n,
    CoordNat (NthTailNat i j) n = CoordNat i (j+n).
Proof.
  induction j. reflexivity.
  intros. simpl. rewrite IHj. reflexivity.
Qed.

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

Lemma LengthNat_wf : well_founded (fun n p : nat => LengthNat n < LengthNat p).
Proof.
  assert (forall l x,
             LengthNat x <= l
             -> Acc (fun n p : nat => LengthNat n < LengthNat p) x).
  induction l.
  - intros. apply Acc_intro.
    intros y H0. exfalso. inversion H.
    rewrite H2 in H0. inversion H0.
  - intros. apply Acc_intro. intros y H0.
    apply IHl. apply le_S_n.
    apply (Nat.le_trans _ _ _ H0). exact H.
  - intros x. apply (H (LengthNat x)). apply Nat.le_refl.
Qed.

Lemma Seq_rect : forall (P : nat -> Type),
    (forall n:nat, LengthNat n = O -> P n)
    -> (forall hd tl:nat, P tl -> P (ConsNat hd tl))
    -> forall n:nat, P n.
Proof.
  intros P P0 Pcons.
  apply (Fix LengthNat_wf). intros n IHn.
  destruct (le_lt_dec (LengthNat n) 0) as [l|l].
  - apply P0, Nat.le_0_r, l.
  - rewrite (HeadTailDecompNat n l). apply Pcons.
    apply IHn. rewrite LengthTailNat.
    destruct (LengthNat n). inversion l. apply Nat.le_refl.
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

Lemma diagMergeIncrLt : forall x y z t,
    x <= y ->
    z < t ->
    diagMerge x z < diagMerge y t.
Proof.
  intros.
  assert (forall a b c, b < c -> diagMerge a b < diagMerge a c) as H1.
  { intros. unfold diagMerge.
    apply (Nat.lt_le_trans _ (c + (a + b) * S (a + b) / 2)).
    apply (Nat.add_lt_mono_r b c), H1.
    apply Nat.add_le_mono_l.
    apply Nat.div_le_mono. discriminate.
    apply Nat.mul_le_mono_nonneg. apply le_0_n.
    apply Nat.add_le_mono_l. apply Nat.lt_le_incl, H1.
    apply le_0_n. apply le_n_S.
    apply Nat.add_le_mono_l.
    apply Nat.lt_le_incl, H1. }
  apply (Nat.le_lt_trans _ (diagMerge y z)).
  apply diagMergeIncr. exact H. apply Nat.le_refl.
  apply H1, H0.
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
  - apply le_0_n.
  - rewrite <- (diagSplitMergeId n) at 2.
    apply diagMergeIncr. rewrite des. apply le_S, Nat.le_refl.
    destruct (diagY n). apply Nat.le_refl.
    apply Nat.lt_le_incl, diagSplitSndLower.
    apply le_n_S, le_0_n.
Qed.

Lemma TailLt : forall n, 0 < n -> TailNat n < n.
Proof.
  intros. unfold TailNat, LengthNat.
  destruct (diagX n) eqn:des. exact H.
  rewrite <- (diagSplitMergeId n) at 2.
  rewrite des.
  apply (Nat.le_lt_trans _ (diagMerge n0 (diagY n))).
  apply diagMergeIncr. apply Nat.le_refl.
  apply Nat.le_sub_l. generalize (diagY n); intro p.
  unfold diagMerge.
  apply Nat.add_lt_mono_l.
  change ((S n0 + p) * S (S n0 + p))
    with (1*2 + (n0 + p + (n0 + p) * S (S (n0 + p)))).
  rewrite (Nat.add_comm (1*2)).
  rewrite Nat.div_add. 2: discriminate.
  rewrite (Nat.add_comm _ 1). apply le_n_S.
  apply Nat.div_le_mono. discriminate.
  rewrite Nat.mul_comm. simpl.
  apply Nat.add_le_mono_l.
  apply Nat.mul_le_mono_l.
  apply le_S, le_S, Nat.le_refl.
Qed.

Lemma HeadLt : forall n, 0 < n -> HeadNat n < n.
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
  rewrite des. apply HeadLt, le_n_S, le_0_n.
  apply NthTailLe.
Qed.

Lemma CoordLe : forall (n i : nat), CoordNat n i <= n.
Proof.
  intros n i. unfold CoordNat.
  unfold HeadNat.
  destruct (LengthNat (NthTailNat n i)) eqn:des. apply le_0_n.
  apply (Nat.le_trans _ _ _ (diagSplitFstLe _)).
  apply (Nat.le_trans _ (NthTailNat n i)).
  2: apply NthTailLe.
  unfold diagY.
  apply Nat.le_sub_l.
Qed.

Lemma LengthPositive : forall n:nat, 0 < LengthNat n -> 0 < n.
Proof.
  intros [|n] H.
  - exfalso. inversion H.
  - apply le_n_S, le_0_n.
Qed.

Lemma TruncatedDiffNat : forall n p,
    LengthNat n = LengthNat p
    -> NthTailNat n (LengthNat n) = NthTailNat p (LengthNat p)
    -> n <> p
    -> { k:nat | k < LengthNat n /\ CoordNat n k <> CoordNat p k }.
Proof.
  apply (Seq_rect (fun n => forall p,
    LengthNat n = LengthNat p
    -> NthTailNat n (LengthNat n) = NthTailNat p (LengthNat p)
    -> n <> p
    -> { k:nat | k < LengthNat n /\ CoordNat n k <> CoordNat p k })).
  - intros. exfalso. rewrite H in H1. rewrite H in H0.
    rewrite <- H0 in H1. simpl in H1. contradict H2. exact H1.
  - intros.
    rewrite LengthConsNat in H0.
    rewrite LengthConsNat, NthTailConsNat in H1.
    destruct (Nat.eq_dec tl (TailNat p)).
    + subst tl. exists 0. split.
      rewrite LengthConsNat. apply le_n_S, le_0_n.
      rewrite CoordConsHeadNat. intro abs. subst hd.
      assert (0 < LengthNat p) as ppos.
      { rewrite <- H0. apply le_n_S, le_0_n. }
      rewrite <- (HeadTailDecompNat _ ppos) in H2.
      apply H2. reflexivity.
    + specialize (H (TailNat p)). destruct H as [k H].
      rewrite LengthTailNat, <- H0. reflexivity.
      rewrite LengthTailNat.
      simpl. rewrite H1.
      replace (LengthNat p) with (S (pred (LengthNat p))) at 1.
      reflexivity.
      rewrite <- H0. reflexivity. exact n.
      exists (S k). split. rewrite LengthConsNat.
      apply le_n_S, H.
      rewrite CoordConsTailNat.
      rewrite CoordTailNat in H. apply H.
Qed.

Lemma TruncatedEqNat : forall n p,
    LengthNat n = LengthNat p
    -> NthTailNat n (LengthNat n) = NthTailNat p (LengthNat p)
    -> (forall k, k < LengthNat n -> CoordNat n k = CoordNat p k)
    -> n = p.
Proof.
  intros. destruct (Nat.eq_dec n p).
  exact e. exfalso.
  pose proof (TruncatedDiffNat n p H H0 n0) as [k H2].
  destruct H2. specialize (H1 k H2).
  apply H3, H1.
Qed. 

(* Concatenation defined tail-recursively. This uses a double reversal of the
   first list, but it is necessary to get access to general recursive functions. *)
Definition ConcatReverseRec (n p : nat) : nat -> prod nat nat :=
  nat_rec (fun _ => prod nat nat) (n,p)
          (fun _ val
           => let (i,j) := val in
             (TailNat i, ConsNat (HeadNat i) j)).
Definition ConcatReverseNat (n p : nat) : nat :=
  snd (ConcatReverseRec n p (LengthNat n)).
Definition ReverseNat (n : nat) : nat := ConcatReverseNat n NilNat.
Definition ConcatNat n p : nat := ConcatReverseNat (ReverseNat n) p.

Lemma ConcatReverseConsRec : forall step n p k,
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

Lemma ConcatReverseConsNat : forall n p k,
    ConcatReverseNat (ConsNat k n) p = ConcatReverseNat n (ConsNat k p).
Proof.
  intros. unfold ConcatReverseNat.
  rewrite LengthConsNat.
  rewrite ConcatReverseConsRec. reflexivity.
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
    rewrite ConcatReverseConsNat, LengthConsNat, IHl.
    rewrite LengthTailNat, LengthConsNat.
    destruct (LengthNat n). discriminate H.
    simpl. rewrite Nat.add_succ_r. reflexivity.
    rewrite LengthTailNat.
    destruct (LengthNat n). discriminate H.
    simpl. inversion H. reflexivity.
  - intros. apply (H (LengthNat n)). reflexivity.
Qed.

Lemma CoordConcatReverseNatSecond : forall f g k,
    CoordNat (ConcatReverseNat f g) (k + LengthNat f) = CoordNat g k.
Proof.
  apply (Seq_rect (fun f => forall g k,
    CoordNat (ConcatReverseNat f g) (k + LengthNat f) = CoordNat g k)).
  - intros. unfold ConcatReverseNat. rewrite H, Nat.add_0_r.
    simpl. reflexivity.
  - intros. rewrite ConcatReverseConsNat.
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
    rewrite ConcatReverseConsNat, LengthConsNat. simpl.
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

Lemma ConcatLength0 : forall n p,
    LengthNat n = 0
    -> ConcatNat n p = p.
Proof.
  intros. unfold ConcatNat, ConcatReverseNat, ReverseNat.
  rewrite LengthConcatReverseNat, H. reflexivity.
Qed.

Lemma ConcatNilNat : forall n, ConcatNat NilNat n = n.
Proof.
  reflexivity.
Qed.

Lemma ConcatReverseNatTruncated : forall n p,
    NthTailNat (ConcatReverseNat n p) (LengthNat (ConcatReverseNat n p))
    = NthTailNat p (LengthNat p).
Proof.
  assert (forall n p, NthTailNat (ConcatReverseNat n p) (LengthNat n) = p).
  { apply (Seq_rect (fun n => forall p, NthTailNat (ConcatReverseNat n p) (LengthNat n) = p)).
    intros. unfold ConcatReverseNat. rewrite H. reflexivity.
    intros. rewrite ConcatReverseConsNat, LengthConsNat.
    change (S (LengthNat tl)) with (1 + LengthNat tl).
    rewrite Nat.add_comm.
    rewrite <- NthTailNthTailNat. rewrite H. simpl.
    rewrite TailConsNat. reflexivity. }
  intros. rewrite LengthConcatReverseNat.
  rewrite <- NthTailNthTailNat. rewrite H. reflexivity.
Qed.

Lemma LengthReverseNat : forall n,
    LengthNat (ReverseNat n) = LengthNat n.
Proof.
  intros. unfold ReverseNat.
  rewrite LengthConcatReverseNat.
  change (LengthNat NilNat) with 0.
  rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma CoordReverseNat : forall n k,
    k < LengthNat n ->
    CoordNat (ReverseNat n) k = CoordNat n (LengthNat n - S k).
Proof.
  intros. apply CoordConcatReverseNatFirst. exact H.
Qed.

Lemma LengthConcatNat : forall (n p : nat),
    LengthNat (ConcatNat n p) = LengthNat n + LengthNat p.
Proof.
  intros.
  unfold ConcatNat.
  rewrite LengthConcatReverseNat, LengthReverseNat.
  reflexivity.
Qed. 

Lemma ConcatNatTruncated : forall n p,
    NthTailNat (ConcatNat n p) (LengthNat (ConcatNat n p))
    = NthTailNat p (LengthNat p).
Proof.
  intros n p. apply ConcatReverseNatTruncated.
Qed.

Lemma CoordConcatNatFirst : forall f g k,
    k < LengthNat f
    -> CoordNat (ConcatNat f g) k = CoordNat f k.
Proof.
  intros. unfold ConcatNat.
  rewrite CoordConcatReverseNatFirst.
  2: rewrite LengthReverseNat; exact H.
  rewrite LengthReverseNat, CoordReverseNat.
  apply f_equal. destruct (LengthNat f). inversion H.
  apply Nat.add_sub_eq_l. simpl.
  rewrite Nat.sub_add. reflexivity.
  apply le_S_n. exact H.
  destruct (LengthNat f). inversion H. simpl.
  apply le_n_S. apply Nat.le_sub_l.
Qed. 

Lemma ConcatConsNat : forall hd tl k,
    ConcatNat (ConsNat hd tl) k = ConsNat hd (ConcatNat tl k).
Proof.
  intros. apply TruncatedEqNat. 
  - rewrite LengthConcatNat.
    rewrite LengthConsNat, LengthConsNat.
    rewrite LengthConcatNat.
    reflexivity.
  - rewrite ConcatNatTruncated.
    rewrite LengthConsNat. 
    change (NthTailNat k (LengthNat k) =
  NthTailNat (TailNat (ConsNat hd (ConcatNat tl k)))
    (LengthNat (ConcatNat tl k))).
    rewrite TailConsNat, ConcatNatTruncated. reflexivity.
  - intros. rewrite LengthConcatNat, LengthConsNat in H.
    simpl in H. apply le_S_n in H. destruct k0.
    + rewrite CoordConsHeadNat.
      rewrite CoordConcatNatFirst. apply CoordConsHeadNat.
      rewrite LengthConsNat. 
      apply le_n_S, le_0_n.
    + rewrite CoordConsTailNat.
      destruct (le_lt_dec (LengthNat tl) k0).
      * unfold ConcatNat.
        rewrite <- (Nat.sub_add _ _ l). 
        pose proof (LengthReverseNat tl).
        rewrite <- H0 at 4.
        rewrite CoordConcatReverseNatSecond. clear H0.
        pose proof (LengthReverseNat (ConsNat hd tl)).
        rewrite LengthConsNat in H0.
        rewrite <- Nat.add_succ_r.
        rewrite <- H0.
        rewrite CoordConcatReverseNatSecond. reflexivity.
      * rewrite CoordConcatNatFirst.
        2: rewrite LengthConsNat; apply le_n_S; exact l.
        rewrite CoordConsTailNat.
        rewrite CoordConcatNatFirst. reflexivity. exact l.
Qed.

Lemma CoordConcatNatSecond : forall f g k,
    CoordNat (ConcatNat f g) (k + LengthNat f) = CoordNat g k.
Proof.
  apply (Seq_rect (fun f => forall g k,
                       CoordNat (ConcatNat f g) (k + LengthNat f) = CoordNat g k)).
  - intros. rewrite ConcatLength0, H, Nat.add_0_r. reflexivity. exact H.
  - intros. rewrite ConcatConsNat, LengthConsNat, Nat.add_succ_r.
    rewrite CoordConsTailNat, H. reflexivity.
Qed.

Lemma NthTailConcatNat : forall n p k,
    NthTailNat (ConcatNat n p) (LengthNat n + k) = NthTailNat p k.
Proof.
  apply (Seq_rect (fun n =>  forall p k,
    NthTailNat (ConcatNat n p) (LengthNat n + k) = NthTailNat p k)).
  - intros. rewrite ConcatLength0. rewrite H. reflexivity. exact H.
  - intros. rewrite ConcatConsNat, LengthConsNat.
    simpl. rewrite TailConsNat, H. reflexivity.
Qed.

Lemma diagMerge_param_lt : forall pn i,
    0 < LengthNat (diagY pn) ->
    diagMerge (diagX pn) (CoordNat (diagY pn) i) < pn.
Proof.
  intros.
  rewrite <- (diagSplitMergeId pn) at 3.
  apply diagMergeIncrLt. apply Nat.le_refl.
  apply CoordLower, LengthPositive, H.
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

(* Find number k in sequence n, from beginning to coordinate last excluded.
   Tail recursive. *)
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

(* Map f to list n and truncate it. *)
Definition MapNatRec (f : nat -> nat) (n : nat) (rec : forall k, k<n -> nat) : nat
  := match le_lt_dec (LengthNat n) 0 with
     | left _ => NilNat  (* truncate at length 0 *)
     | right l => ConsNat (f (HeadNat n)) (rec (TailNat n) (TailLt _ (LengthPositive _ l))) end.
Definition MapNat (f : nat -> nat) : nat -> nat := Fix lt_wf (fun _ => nat) (MapNatRec f).

Lemma MapNilNat : forall f,
    MapNat f NilNat = NilNat.
Proof.
  reflexivity.
Qed.

Lemma MapLength0Nat : forall f n, LengthNat n = 0 ->
    MapNat f n = NilNat.
Proof.
  intros. unfold MapNat. rewrite Fix_eq.
  unfold MapNatRec. rewrite H. reflexivity.
  intros. unfold MapNatRec.
  destruct (le_lt_dec (LengthNat x) 0). reflexivity.
  rewrite H0. reflexivity.
Qed.

Lemma MapConsNat : forall f h tl,
    MapNat f (ConsNat h tl) = ConsNat (f h) (MapNat f tl).
Proof.
  intros. unfold MapNat. rewrite Fix_eq.
  unfold MapNatRec. rewrite LengthConsNat; simpl.
  rewrite HeadConsNat, TailConsNat. reflexivity.
  intros. unfold MapNatRec.
  destruct (le_lt_dec (LengthNat x) 0). reflexivity.
  rewrite H. reflexivity.
Qed.

Lemma LengthMapNat : forall f n, LengthNat (MapNat f n) = LengthNat n.
Proof.
  intro f.
  apply (Seq_rect (fun n => LengthNat (MapNat f n) = LengthNat n)).
  - intros. rewrite MapLength0Nat, H. reflexivity. exact H.
  - intros. rewrite MapConsNat, LengthConsNat, LengthConsNat, H.
    reflexivity.
Qed.

Lemma CoordMapNat : forall f n k,
    k < LengthNat n
    -> CoordNat (MapNat f n) k = f (CoordNat n k).
Proof.
  intro f.
  apply (Seq_rect (fun n => forall k,
    k < LengthNat n
    -> CoordNat (MapNat f n) k = f (CoordNat n k))).
  - intros. exfalso. rewrite H in H0. inversion H0.
  - intros. rewrite MapConsNat. destruct k.
    rewrite CoordConsHeadNat, CoordConsHeadNat. reflexivity.
    specialize (H k).
    rewrite CoordConsTailNat, CoordConsTailNat. apply H.
    rewrite LengthConsNat in H0.
    apply le_S_n, H0.
Qed.

Lemma TailMapNat : forall f n,
    TailNat (MapNat f n) = MapNat f (TailNat n).
Proof.
  intro f. apply Seq_rect.
  - intros. rewrite MapLength0Nat, MapLength0Nat.
    reflexivity. rewrite LengthTailNat, H. reflexivity. exact H.
  - intros hd tl H.
    rewrite MapConsNat, TailConsNat, TailConsNat. reflexivity.
Qed.

Lemma MapNatExt : forall f g n,
    (forall k, k < LengthNat n -> f (CoordNat n k) = g (CoordNat n k))
    -> MapNat f n = MapNat g n.
Proof.
  intros f g.
  apply (Seq_rect (fun n => (forall k, k < LengthNat n -> f (CoordNat n k) = g (CoordNat n k))
    -> MapNat f n = MapNat g n)).
  - intros. rewrite MapLength0Nat, MapLength0Nat.
    reflexivity. exact H. exact H.
  - intros. rewrite MapConsNat, MapConsNat, H.
    specialize (H0 0).
    rewrite CoordConsHeadNat in H0. rewrite H0. reflexivity.
    rewrite LengthConsNat. apply le_n_S, le_0_n.
    intros k H1. specialize (H0 (S k)).
    rewrite CoordConsTailNat in H0. apply H0.
    rewrite LengthConsNat. apply le_n_S, H1.
Qed.

Lemma MapMapNat : forall f g n,
    MapNat g (MapNat f n) = MapNat (fun x => g (f x)) n.
Proof.
  intros f g.
  apply (Seq_rect (fun n => MapNat g (MapNat f n) = MapNat (fun x => g (f x)) n)).
  - intros n H. rewrite MapLength0Nat, MapLength0Nat.
    reflexivity. exact H. rewrite LengthMapNat. exact H.
  - intros. rewrite MapConsNat, MapConsNat, MapConsNat.
    apply f_equal. exact H.
Qed.

Lemma MapNatTruncated : forall f p,
    NthTailNat (MapNat f p) (LengthNat p) = 0.
Proof.
  intro f.
  apply (Seq_rect (fun p => NthTailNat (MapNat f p) (LengthNat p) = 0)).
  - intros. rewrite MapLength0Nat. rewrite H. reflexivity. exact H.
  - intros. rewrite MapConsNat, LengthConsNat, NthTailConsNat. exact H.
Qed.

Lemma MapConcatNat : forall f l h,
    MapNat f (ConcatNat l h) = ConcatNat (MapNat f l) (MapNat f h).
Proof.
  intro f.
  apply (Seq_rect (fun l => forall h,
    MapNat f (ConcatNat l h) = ConcatNat (MapNat f l) (MapNat f h))).
  - intros. rewrite (MapLength0Nat f n). 2: exact H.
    rewrite ConcatNilNat. apply f_equal.
    apply ConcatLength0, H.
  - intros. rewrite ConcatConsNat, MapConsNat, MapConsNat, ConcatConsNat, H.
    reflexivity.
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

Lemma MapNatDiff : forall f p,
    NthTailNat p (LengthNat p) = 0
    -> MapNat f p <> p
    -> { j:nat | j < LengthNat p /\ f (CoordNat p j) <> CoordNat p j }.
Proof.
  intros f p ptrunc H.
  pose proof (TruncatedDiffNat (MapNat f p) p) as [k H1].
  apply LengthMapNat.
  rewrite LengthMapNat. rewrite MapNatTruncated.
  symmetry. exact ptrunc. exact H.
  destruct H1. rewrite LengthMapNat in H0. exists k. split.
  exact H0. rewrite CoordMapNat in H1. exact H1. exact H0.
Qed.

Fixpoint MaxSeqNatRec (l i : nat) : nat :=
  match i with
  | O => O
  | S k => Nat.max (MaxSeqNatRec l k) (CoordNat l k)
  end.
Definition MaxSeqNat (l : nat) : nat := MaxSeqNatRec l (LengthNat l).

Lemma MaxConsNat : forall l n,
    MaxSeqNat (ConsNat n l) = Nat.max n (MaxSeqNat l).
Proof.
  assert (forall i n l,
             MaxSeqNatRec (ConsNat n l) (S i) = Nat.max n (MaxSeqNatRec l i)).
  induction i.
  - intros. simpl.
    rewrite CoordConsHeadNat, Nat.max_comm. reflexivity.
  - intros.
    change (Nat.max (MaxSeqNatRec (ConsNat n l) (S i)) (CoordNat (ConsNat n l) (S i))
            = Nat.max n (MaxSeqNatRec l (S i))).
    rewrite IHi, CoordConsTailNat. simpl.
    rewrite Nat.max_assoc. reflexivity.
  - intros. unfold MaxSeqNat.
    rewrite LengthConsNat.
    apply (H (LengthNat l)).
Qed.

Lemma MaxConcatNat : forall l h,
    MaxSeqNat (ConcatNat l h) = Nat.max (MaxSeqNat l) (MaxSeqNat h).
Proof.
  apply (Seq_rect (fun l => forall h,
                       MaxSeqNat (ConcatNat l h) = Nat.max (MaxSeqNat l) (MaxSeqNat h))).
  - intros. rewrite ConcatLength0.
    replace (MaxSeqNat n) with 0. reflexivity.
    unfold MaxSeqNat. rewrite H. reflexivity. exact H.
  - intros. rewrite ConcatConsNat, MaxConsNat, MaxConsNat, H.
    rewrite Nat.max_assoc. reflexivity.
Qed.


Global Opaque ConsNat. (* prevent the type checker from freezing *)
Global Opaque TailNat.
Global Opaque LengthNat.
Global Opaque CoordNat.
Global Opaque diagX diagY diagMerge.
