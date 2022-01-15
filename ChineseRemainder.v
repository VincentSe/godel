(** The Chinese remainder theorem. *)

Require Import ZArith.
Require Import ZArith.Znumtheory.
Require Import EnumSeqNat.

Lemma ChineseRemainder_two : forall n p a b : Z,
    0 < n ->
    0 < p ->
    0 <= a < n ->
    0 <= b < p ->
    rel_prime n p -> exists x:Z, (0 <= x < n*p) /\ (x mod n = a) /\ (x mod p = b).
Proof.
  intros n p a b npos ppos apos bpos coprime.
  destruct (rel_prime_bezout _ _ coprime) as [u v H0].
  exists ((a*v*p+b*u*n) mod (n*p)).
  assert (n <> 0) as nz.
  { intro abs. rewrite abs in npos. inversion npos. }
  assert (p <> 0) as pz.
  { intro abs. rewrite abs in ppos. inversion ppos. }
  split.
  apply Z.mod_pos_bound, Z.mul_pos_pos; assumption. split.
  - rewrite Z.rem_mul_r.
    rewrite (Z.mul_comm n), Z.mod_add, Z.mod_mod.
    rewrite Z.mod_add.
    rewrite <- Z.mul_assoc, <- Zdiv.Zmult_mod_idemp_r.
    assert ((u * n + v * p) mod n = 1 mod n) as H.
    rewrite H0. reflexivity.
    rewrite Z.add_comm, Z.mod_add in H. rewrite H.
    rewrite Zdiv.Zmult_mod_idemp_r, Z.mul_1_r.
    apply Zdiv.Zmod_small, apos.
    exact nz. exact nz. exact nz. exact nz. exact nz. exact ppos.
  - rewrite (Z.mul_comm n), Z.rem_mul_r.
    rewrite (Z.mul_comm p), Z.mod_add, Z.mod_mod.
    rewrite Z.add_comm, Z.mod_add.
    rewrite <- Z.mul_assoc, <- Zdiv.Zmult_mod_idemp_r.
    assert ((u * n + v * p) mod p = 1 mod p) as H.
    rewrite H0. reflexivity.
    rewrite Z.mod_add in H. rewrite H.
    rewrite Zdiv.Zmult_mod_idemp_r, Z.mul_1_r.
    apply Zdiv.Zmod_small, bpos.
    exact pz. exact pz. exact pz. exact pz. exact pz. exact npos.
Qed.

Lemma ZdivideFact : forall (n:nat) (r:Z),
    0 < r <= Z.of_nat n
    -> (r | Z.of_nat (fact n)).
Proof.
  induction n.
  - intros. destruct H. apply (Z.lt_le_trans _ _ _ H) in H0.
    apply Z2Nat.inj_lt in H0. simpl in H0. inversion H0.
    apply Z.le_refl. apply Z.le_refl.
  - intros.
    change (fact (S n)) with ((S n) * fact n)%nat.
    rewrite Nat2Z.inj_mul.
    rewrite Nat2Z.inj_succ in H.
    rewrite Nat2Z.inj_succ.
    destruct (Z.lt_trichotomy r (Z.succ (Z.of_nat n))).
    apply Zlt_succ_le in H0.
    + destruct (IHn r) as [x H1]. split. apply H. exact H0.
      exists (Z.succ (Z.of_nat n)*x).
      rewrite <- Z.mul_assoc, <- H1. reflexivity.
    + destruct H0.
      exists (Z.of_nat (fact n)). rewrite H0, Z.mul_comm. reflexivity.
      exfalso. apply (Z.lt_irrefl (Z.succ (Z.of_nat n))).
      apply (Z.lt_le_trans _ _ _ H0). apply H.
Qed.

Lemma ChineseRemainder : forall modulos remainders : nat,
    LengthNat modulos = LengthNat remainders
    -> (forall i, i < LengthNat modulos -> CoordNat remainders i < CoordNat modulos i)%nat
    -> (forall i j, (i < j < LengthNat modulos)%nat
              -> rel_prime (Z.of_nat (CoordNat modulos i))
                          (Z.of_nat (CoordNat modulos j)))
    -> exists x:nat, forall i, (i < LengthNat modulos
                  -> x mod (CoordNat modulos i) = CoordNat remainders i)%nat.
Proof.
  assert (forall len modulos remainders : nat,
             len = LengthNat modulos
    -> LengthNat modulos = LengthNat remainders
    -> (forall i, i < LengthNat modulos -> CoordNat remainders i < CoordNat modulos i)%nat
    -> (forall i j, (i < j < LengthNat modulos)%nat
              -> rel_prime (Z.of_nat (CoordNat modulos i))
                          (Z.of_nat (CoordNat modulos j)))
    -> exists x:nat, forall i, (i < LengthNat modulos
                   -> x mod (CoordNat modulos i) = CoordNat remainders i)%nat).
  induction len.
  - intros. exists O. intros. exfalso. rewrite <- H in H3. inversion H3.
  - intros. destruct len.
    exists (CoordNat remainders 0).
    intros. destruct i. apply Nat.mod_small.
    exact (H1 _ H3). exfalso. rewrite <- H in H3.
    apply le_S_n in H3. inversion H3.
    assert (0 < LengthNat modulos)%nat as lenpos.
    { rewrite <- H. apply le_n_S, Nat.le_0_l. }
    assert (0 < CoordNat modulos 0)%nat as c0pos.
    { specialize (H1 O lenpos).
      exact (Nat.le_lt_trans _ _ _ (Nat.le_0_l _) H1). }
    assert (0 < CoordNat modulos 1)%nat as c1pos.
    { specialize (H1 1%nat).
      apply (Nat.le_lt_trans _ (CoordNat remainders 1)).
      apply Nat.le_0_l. apply H1. rewrite <- H. apply le_n_S, le_n_S, Nat.le_0_l. }
    destruct (ChineseRemainder_two
                (Z.of_nat (CoordNat modulos 0))
                (Z.of_nat (CoordNat modulos 1))
                (Z.of_nat (CoordNat remainders 0))
                (Z.of_nat (CoordNat remainders 1))) as [x2 [x2pos chineseX2]].
    apply (Nat2Z.inj_lt 0). exact c0pos.
    apply (Nat2Z.inj_lt 0). exact c1pos.
    split. apply Zle_0_nat. apply Nat2Z.inj_lt, H1, lenpos.
    split. apply Zle_0_nat. apply Nat2Z.inj_lt, H1.
    rewrite <- H. apply le_n_S, le_n_S, Nat.le_0_l.
    apply H2. split. apply Nat.le_refl.
    rewrite <- H. apply le_n_S, le_n_S, Nat.le_0_l.
    destruct (IHlen (ConsNat (CoordNat modulos 0 * CoordNat modulos 1)
                             (TailNat (TailNat modulos)))
                    (ConsNat (Z.to_nat x2) (TailNat (TailNat remainders)))).
    + rewrite LengthConsNat, LengthTailNat, LengthTailNat, <- H. reflexivity.
    + rewrite LengthConsNat, LengthConsNat.
      rewrite LengthTailNat, LengthTailNat, LengthTailNat, LengthTailNat.
      rewrite <- H0, <- H. reflexivity.
    + intros. destruct i. rewrite CoordConsHeadNat, CoordConsHeadNat.
      apply Nat2Z.inj_lt. rewrite Z2Nat.id, Nat2Z.inj_mul.
      apply x2pos. apply x2pos.
      rewrite CoordConsTailNat, CoordConsTailNat.
      rewrite CoordTailNat, CoordTailNat, CoordTailNat, CoordTailNat.
      apply H1.
      rewrite LengthConsNat, LengthTailNat, LengthTailNat in H3.
      rewrite <- H. apply le_n_S. rewrite <- H in H3.
      simpl in H3. exact H3.
    + intros i j H3. destruct H3.
      destruct j. exfalso. inversion H3.
      rewrite LengthConsNat, LengthTailNat, LengthTailNat, <- H in H4.
      simpl in H4.
      rewrite CoordConsTailNat. destruct i.
      rewrite CoordConsHeadNat.
      apply rel_prime_sym. rewrite Nat2Z.inj_mul.
      apply rel_prime_mult.
      rewrite CoordTailNat, CoordTailNat.
      apply rel_prime_sym, H2. split. apply le_n_S, Nat.le_0_l.
      rewrite <- H. apply le_n_S. apply H4.
      rewrite CoordTailNat, CoordTailNat.
      apply rel_prime_sym, H2. split. apply le_n_S, le_n_S, Nat.le_0_l.
      rewrite <- H. apply le_n_S. apply H4.
      rewrite CoordConsTailNat.
      rewrite CoordTailNat, CoordTailNat, CoordTailNat, CoordTailNat.
      apply H2. split. apply le_n_S, H3.
      rewrite <- H. apply le_n_S, H4.
    + exists x. intros i H4.
      rewrite LengthConsNat, LengthTailNat, LengthTailNat, <- H in H3.
      simpl in H3.
      assert (0 < S len)%nat by apply le_n_S, Nat.le_0_l.
      destruct i.
      * specialize (H3 O H5).
        rewrite CoordConsHeadNat, CoordConsHeadNat in H3.
        transitivity ((x mod (CoordNat modulos 0 * CoordNat modulos 1)) mod (CoordNat modulos 0))%nat.
        symmetry.
        apply Nat2Z.inj_iff. rewrite Nat2Z.inj_mod, Nat2Z.inj_mod, Nat2Z.inj_mod.
        rewrite Nat2Z.inj_mul.
        rewrite Z.rem_mul_r, (Z.mul_comm (Z.of_nat (CoordNat modulos 0))).
        rewrite Z.mod_add, Z.mod_mod. reflexivity.
        intro abs. apply (Nat2Z.inj_iff _ 0) in abs.
        rewrite abs in c0pos. inversion c0pos.
        intro abs. apply (Nat2Z.inj_iff _ 0) in abs.
        rewrite abs in c0pos. inversion c0pos.
        intro abs. apply (Nat2Z.inj_iff _ 0) in abs.
        rewrite abs in c0pos. inversion c0pos.
        apply (Nat2Z.inj_lt 0). exact c1pos.
        rewrite H3. destruct chineseX2 as [chineseX2 _].
        rewrite <- (Z2Nat.id x2) in chineseX2.
        rewrite <- Nat2Z.inj_mod in chineseX2.
        apply Nat2Z.inj_iff, chineseX2.
        apply x2pos.
      * destruct i.
        specialize (H3 O H5).
        rewrite CoordConsHeadNat, CoordConsHeadNat in H3.
        transitivity ((x mod (CoordNat modulos 0 * CoordNat modulos 1)) mod (CoordNat modulos 1))%nat.
        symmetry.
        apply Nat2Z.inj_iff. rewrite Nat2Z.inj_mod, Nat2Z.inj_mod, Nat2Z.inj_mod.
        rewrite Nat2Z.inj_mul.
        rewrite (Z.mul_comm (Z.of_nat (CoordNat modulos 0))), Z.rem_mul_r.
        rewrite (Z.mul_comm (Z.of_nat (CoordNat modulos 1))).
        rewrite Z.mod_add, Z.mod_mod. reflexivity.
        intro abs. apply (Nat2Z.inj_iff _ 0) in abs.
        rewrite abs in c1pos. inversion c1pos.
        intro abs. apply (Nat2Z.inj_iff _ 0) in abs.
        rewrite abs in c1pos. inversion c1pos.
        intro abs. apply (Nat2Z.inj_iff _ 0) in abs.
        rewrite abs in c1pos. inversion c1pos.
        apply (Nat2Z.inj_lt 0). exact c0pos.
        rewrite H3. destruct chineseX2 as [_ chineseX2].
        rewrite <- (Z2Nat.id x2) in chineseX2.
        rewrite <- Nat2Z.inj_mod in chineseX2.
        apply Nat2Z.inj_iff, chineseX2.
        apply x2pos.
        rewrite <- H in H4. apply le_S_n in H4.
        specialize (H3 (S i) H4).
        rewrite CoordConsTailNat, CoordConsTailNat in H3.
        rewrite CoordTailNat, CoordTailNat, CoordTailNat, CoordTailNat in H3.
        exact H3.
  - intros. exact (H (LengthNat modulos) modulos remainders eq_refl H0 H1 H2).
Qed.

