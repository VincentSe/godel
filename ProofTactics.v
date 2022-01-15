(** Here we show that IsProof is strong enough to prove basic tactics.
    Although simple, IsProof ZFCaxioms can formalize all of today's mathematics.
    This file is the counterpart of PeanoModel.v, where we show that IsProof
    is not too strong, it does not prove everything. *)

Require Import PeanoNat.
Require Import Arith.Wf_nat.
Require Import Arith.Compare_dec.
Require Import EnumSeqNat.
Require Import Formulas.
Require Import Substitutions.
Require Import IsFreeForSubst.
Require Import Proofs.

Lemma ProofStack : forall IsAxiom (n:nat) proof,
    IsProofLoop IsAxiom proof (LengthNat proof) = true
    -> n < LengthNat proof
    -> IsProof IsAxiom (CoordNat proof n) (NthTailNat proof n) = true.
Proof.
  induction n.
  - intros. simpl.
    apply andb_true_intro. split. 2: exact H.
    apply andb_true_intro. split.
    apply Nat.eqb_refl. apply Nat.leb_le. exact H0.
  - intros.
    destruct (LengthNat proof) eqn:des.
    inversion H0.
    rewrite (HeadTailDecompNat proof) in H.
    2: rewrite des; apply le_n_S, le_0_n.
    pose proof (LengthTailNat proof).
    rewrite des in H1. simpl in H1.
    rewrite <- H1 in H.
    rewrite IsProofLoop_cons in H.
    apply andb_prop in H. destruct H.
    specialize (IHn (TailNat proof) H2).
    simpl.
    rewrite <- CoordTailNat. apply IHn.
    subst n0. apply le_S_n. exact H0.
Qed.

Lemma AxiomIsProved : forall IsAxiom (n:nat),
    IsAxiom n = true
    -> IsLproposition n = true
    -> IsProved IsAxiom n.
Proof.
  intros. exists (ConsNat n NilNat).
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  - rewrite CoordConsHeadNat. apply Nat.eqb_refl.
  - rewrite LengthConsNat. reflexivity.
  - rewrite LengthConsNat. simpl.
    apply andb_true_intro. split. 2: reflexivity.
    unfold IsProofStep.
    do 4 (apply Bool.orb_true_intro; left).
    rewrite CoordConsHeadNat.
    apply andb_true_intro. split; assumption.
Qed.

Lemma WeakenProof : forall IsAxiom StrongerAxioms (prop proof:nat),
    (forall n:nat, IsAxiom n = true -> StrongerAxioms n = true)
    -> IsProof IsAxiom prop proof = true
    -> IsProof StrongerAxioms prop proof = true.
Proof.
  assert (forall l proof IsAxiom StrongerAxioms,
             LengthNat proof = l
             -> (forall n : nat, IsAxiom n = true -> StrongerAxioms n = true)
             -> IsProofLoop IsAxiom proof (LengthNat proof) = true
             -> IsProofLoop StrongerAxioms proof (LengthNat proof) = true) as rec.
  induction l.
  - intros. rewrite H. reflexivity.
  - intros. rewrite H. simpl.
    apply andb_true_intro.
    rewrite H in H1.
    simpl in H1. apply andb_prop in H1. destruct H1 as [proofstep H1].
    split.
    apply Bool.orb_true_intro.
    apply Bool.orb_prop in proofstep.
    destruct proofstep; [left | right; exact H2].
    apply Bool.orb_prop in H2.
    apply Bool.orb_true_intro.
    destruct H2; [left | right; exact H2].
    apply Bool.orb_prop in H2.
    apply Bool.orb_true_intro.
    destruct H2; [left | right; exact H2].
    apply Bool.orb_prop in H2.
    apply Bool.orb_true_intro.
    destruct H2; [left | right; exact H2].
    apply andb_true_intro. apply andb_prop in H2.
    split. apply H0, H2. apply H2.
    pose proof (LengthTailNat proof) as H2.
    rewrite H in H2. simpl in H2.
    rewrite <- H2. apply (IHl (TailNat proof) IsAxiom).
    exact H2. exact H0.
    rewrite H2. apply H1.
  - intros. apply andb_prop in H0.
    destruct H0 as [H0 proofloop].
    apply andb_true_intro. split. exact H0.
    exact (rec (LengthNat proof) proof IsAxiom _ eq_refl H proofloop).
Qed.

Lemma WeakenProvable : forall IsAxiom StrongerAxioms (prop:nat),
    (forall n:nat, IsAxiom n = true -> StrongerAxioms n = true)
    -> IsProved IsAxiom prop
    -> IsProved StrongerAxioms prop.
Proof.
  intros. destruct H0. exists x.
  apply (WeakenProof IsAxiom StrongerAxioms). exact H. exact H0.
Qed.

Lemma IsProvedPropAx : forall IsAxiom f,
    IsPropositionalAxiom f = true
    -> IsProved IsAxiom f.
Proof.
  intros. exists (ConsNat f NilNat).
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  rewrite CoordConsHeadNat. apply Nat.eqb_refl.
  rewrite LengthConsNat. apply Nat.leb_le, le_n_S, le_0_n.
  rewrite IsProofLoop_propax. reflexivity. exact H.
Qed.

Lemma ModusPonensHyp : forall IsAxiom h p q,
    IsLproposition h = true
    -> IsLproposition p = true
    -> IsLproposition q = true
    -> IsProved IsAxiom (Limplies (Limplies h (Limplies p q))
                                 (Limplies (Limplies h p) (Limplies h q))).
Proof.
  intros.
  apply IsProvedPropAx, Ax2IsPropAx, Ax2IsAx2; assumption.
Qed.

Lemma IsProvedEqAx : forall IsAxiom f,
    IsEqualityAxiom f = true
    -> IsProved IsAxiom f.
Proof.
  intros. exists (ConsNat f NilNat).
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  rewrite CoordConsHeadNat. apply Nat.eqb_refl.
  rewrite LengthConsNat. apply Nat.leb_le, le_n_S, le_0_n.
  rewrite IsProofLoop_eqax. reflexivity. exact H.
Qed.

Lemma IndepPremiseIsIndepPremise : forall v f g,
    IsLproposition f = true
    -> IsLproposition g = true
    -> VarOccursFreeInFormula v f = false
    -> IsIndependenceOfPremise (Limplies (Lforall v (Limplies f g))
                                        (Limplies f (Lforall v g))) = true.
Proof.
  intros. apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  - rewrite IsLproposition_implies, IsLproposition_forall.
    rewrite IsLproposition_implies, IsLproposition_implies, IsLproposition_forall.
    rewrite H, H0. reflexivity.
  - apply LimpliesIsImplies.
  - rewrite CoordNat_implies_1. apply LforallIsForall.
  - rewrite CoordNat_implies_1, CoordNat_forall_2. apply LimpliesIsImplies.
  - rewrite CoordNat_implies_2. apply LimpliesIsImplies.
  - rewrite CoordNat_implies_2, CoordNat_implies_2. apply LforallIsForall.
  - rewrite CoordNat_implies_1, CoordNat_implies_2.
    rewrite CoordNat_implies_1, CoordNat_forall_2, CoordNat_implies_1.
    apply Nat.eqb_refl.
  - rewrite CoordNat_implies_1, CoordNat_implies_2.
    rewrite CoordNat_implies_2, CoordNat_forall_2, CoordNat_implies_2.
    rewrite CoordNat_forall_2. apply Nat.eqb_refl.
  - rewrite CoordNat_implies_1, CoordNat_implies_2.
    rewrite CoordNat_forall_1, CoordNat_implies_2, CoordNat_forall_1.
    apply Nat.eqb_refl.
  - apply Bool.negb_true_iff.
    rewrite CoordNat_implies_1, CoordNat_implies_2, CoordNat_implies_1.
    rewrite CoordNat_forall_1. exact H1.
Qed.

Lemma IsProvedIndepPremise : forall IsAxiom v f g,
    IsLproposition f = true
    -> IsLproposition g = true
    -> VarOccursFreeInFormula v f = false
    -> IsProved IsAxiom (Limplies (Lforall v (Limplies f g))
                                 (Limplies f (Lforall v g))).
Proof.
  intros. exists (ConsNat (Limplies (Lforall v (Limplies f g))
                               (Limplies f (Lforall v g))) NilNat).
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  rewrite CoordConsHeadNat. apply Nat.eqb_refl.
  rewrite LengthConsNat. apply Nat.leb_le, le_n_S, le_0_n.
  rewrite LengthConsNat. simpl.
  rewrite Bool.andb_true_r.
  apply Bool.orb_true_intro; right.
  apply Bool.orb_true_intro. left.
  apply Bool.orb_true_intro. right.
  rewrite CoordConsHeadNat.
  apply IndepPremiseIsIndepPremise; assumption.
Qed.

Lemma ConcatProofs : forall IsAxiom f g,
    IsProofLoop IsAxiom f (LengthNat f) = true
    -> IsProofLoop IsAxiom g (LengthNat g) = true
    -> IsProofLoop IsAxiom (ConcatNat f g) (LengthNat (ConcatNat f g)) = true.
Proof.
  intro IsAxiom.
  assert (forall l f g,
             LengthNat f = l
             -> IsProofLoop IsAxiom f (LengthNat f) = true
    -> IsProofLoop IsAxiom g (LengthNat g) = true
    -> IsProofLoop IsAxiom (ConcatNat f g) (LengthNat (ConcatNat f g)) = true).
  induction l.
  - intros. rewrite LengthConcatNat, H.
    rewrite ConcatLength0. exact H1. exact H.
  - intros. rewrite LengthConcatNat, H. simpl.
    apply andb_true_intro.
    rewrite (HeadTailDecompNat f), LengthConsNat in H0.
    2: rewrite H; apply le_n_S, le_0_n.
    simpl in H0.
    apply andb_prop in H0. destruct H0.
    split.
    rewrite CoordConcatNatFirst. 2: rewrite H; apply le_n_S, le_0_n.
    clear H1 IHl.
    apply Bool.orb_true_intro.
    rewrite CoordConsHeadNat, TailConsNat in H0.
    apply Bool.orb_prop in H0.
    destruct H0. left.
    apply Bool.orb_true_intro.
    apply Bool.orb_prop in H0.
    destruct H0. left.
    apply Bool.orb_true_intro.
    apply Bool.orb_prop in H0.
    destruct H0; [left | right; exact H0].
    apply Bool.orb_true_intro.
    apply Bool.orb_prop in H0.
    destruct H0; [left | right; exact H0].
    exact H0.
    (* Modus ponens *)
    right.
    apply IsModusPonens_true in H0.
    apply IsModusPonens_true.
    destruct H0 as [n H0]. exists n.
    replace (TailNat (ConcatNat f g)) with (ConcatNat (TailNat f) g).
    rewrite CoordConcatNatFirst.
    destruct H0, H1, H3. split.
    rewrite LengthConcatNat.
    apply (Nat.lt_le_trans _ _ _ H0).
    rewrite <- Nat.add_0_r at 1.
    apply Nat.add_le_mono_l, le_0_n. split.
    exact H1. split. exact H3.
    apply FindNat_true. apply FindNat_true in H4.
    destruct H4 as [p [H4 H5]]. exists p.
    split. rewrite LengthConcatNat.
    apply (Nat.lt_le_trans _ _ _ H4).
    rewrite <- Nat.add_0_r at 1.
    apply Nat.add_le_mono_l, le_0_n.
    rewrite CoordConcatNatFirst. exact H5. exact H4.
    apply H0.
    rewrite (HeadTailDecompNat f), TailConsNat, ConcatConsNat, TailConsNat.
    reflexivity. rewrite H. apply le_n_S, le_0_n.
    (* Quantifier axioms *)
    right.
    apply Bool.orb_true_intro.
    apply Bool.orb_prop in H0.
    destruct H0; [left | right; exact H0].
    apply Bool.orb_true_intro.
    apply Bool.orb_prop in H0.
    destruct H0; [left | right; exact H0].
    apply Bool.orb_true_intro.
    apply Bool.orb_prop in H0.
    destruct H0; [left | right; exact H0].
    apply andb_prop in H0. destruct H0.
    apply andb_true_intro. split. exact H0.
    apply FindNat_true in H1.
    apply FindNat_true. destruct H1 as [p H1]. exists p.
    destruct H1. split. rewrite LengthTailNat, LengthConcatNat.
    apply (Nat.lt_le_trans _ _ _ H1).
    rewrite LengthTailNat. apply Nat.pred_le_mono.
    rewrite <- Nat.add_0_r at 1.
    apply Nat.add_le_mono_l, le_0_n.
    rewrite H3.
    rewrite (HeadTailDecompNat f) at 2.
    rewrite ConcatConsNat, TailConsNat.
    symmetry. apply CoordConcatNatFirst, H1.
    rewrite H. apply le_n_S, le_0_n.
    rewrite (HeadTailDecompNat f).
    2: rewrite H; apply le_n_S, le_0_n.
    rewrite ConcatConsNat, TailConsNat.
    replace l with (LengthNat (TailNat f)).
    rewrite <- LengthConcatNat. apply IHl.
    rewrite LengthTailNat, H. reflexivity.
    rewrite TailConsNat in H2. exact H2. exact H1.
    rewrite LengthTailNat, H. reflexivity.
  - intros. exact (H (LengthNat f) _ _ eq_refl H0 H1).
Qed.

Lemma LimpliesElim : forall IsAxiom (f g:nat),
    IsProved IsAxiom (Limplies f g)
    -> IsProved IsAxiom f
    -> IsProved IsAxiom g.
Proof.
  intros.
  destruct H as [pf H]. destruct H0 as [pg H0].
  exists (ConsNat g (ConcatNat pf pg)).
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  rewrite CoordConsHeadNat. apply Nat.eqb_refl.
  apply Nat.leb_le. rewrite LengthConsNat. apply le_n_S, le_0_n.
  apply andb_prop in H. destruct H.
  apply andb_prop in H. destruct H.
  apply Nat.eqb_eq in H. apply Nat.leb_le in H2.
  apply andb_prop in H0. destruct H0.
  apply andb_prop in H0. destruct H0.
  rewrite IsProofLoop_mp.
  apply ConcatProofs. apply H1.
  apply H3.
  apply IsModusPonens_true.
  exists 0. split. rewrite LengthConcatNat.
  apply (Nat.le_trans _ _ _ H2).
  rewrite <- Nat.add_0_r at 1.
  apply Nat.add_le_mono_l, le_0_n.
  rewrite CoordConcatNatFirst. rewrite <- H.
  split. apply LimpliesIsImplies. split.
  rewrite CoordNat_implies_2. reflexivity.
  apply FindNat_true. exists (LengthNat pf).
  split.
  rewrite LengthConcatNat. unfold lt.
  change (S (LengthNat pf)) with (1+LengthNat pf).
  rewrite Nat.add_comm.
  apply Nat.add_le_mono_l. apply Nat.leb_le in H4. exact H4.
  rewrite CoordNat_implies_1.
  change (LengthNat pf) with (0 + LengthNat pf).
  rewrite CoordConcatNatSecond. apply Nat.eqb_eq in H0. exact H0.
  exact H2.
Qed.

Lemma LandIntro : forall IsAxiom (f g:nat),
    IsProved IsAxiom f
    -> IsProved IsAxiom g
    -> IsProved IsAxiom (Land f g).
Proof.
  intros IsAxiom f g H H0.
  apply (LimpliesElim _ g). 2: exact H0.
  apply (LimpliesElim _ f). 2: exact H.
  apply IsProvedPropAx.
  apply Ax6IsPropAx, Ax6IsAx6.
  exact (IsProvedIsLproposition IsAxiom _ H).
  exact (IsProvedIsLproposition IsAxiom _ H0).
Qed.

Lemma LandElim1_impl : forall IsAxiom (f g:nat),
    IsLproposition f = true
    -> IsLproposition g = true
    -> IsProved IsAxiom (Limplies (Land f g) f).
Proof.
  intros.
  apply IsProvedPropAx.
  apply Ax7IsPropAx, Ax7IsAx7; assumption.
Qed.

Lemma LandElim1 : forall IsAxiom (f g:nat),
    IsProved IsAxiom (Land f g)
    -> IsProved IsAxiom f.
Proof.
  intros.
  pose proof (IsProvedIsLproposition IsAxiom _ H) as andprop.
  rewrite IsLproposition_and in andprop.
  apply andb_prop in andprop.
  apply (LimpliesElim _ (Land f g)). 2: exact H.
  apply IsProvedPropAx.
  apply Ax7IsPropAx, Ax7IsAx7.
  apply andprop. apply andprop.
Qed.

Lemma LandElim2_impl : forall IsAxiom (f g:nat),
    IsLproposition f = true
    -> IsLproposition g = true
    -> IsProved IsAxiom (Limplies (Land f g) g).
Proof.
  intros.
  apply IsProvedPropAx.
  apply Ax8IsPropAx, Ax8IsAx8; assumption.
Qed.

Lemma LandElim2 : forall IsAxiom (f g:nat),
    IsProved IsAxiom (Land f g)
    -> IsProved IsAxiom g.
Proof.
  intros.
  pose proof (IsProvedIsLproposition IsAxiom _ H) as andprop.
  rewrite IsLproposition_and in andprop.
  apply andb_prop in andprop.
  apply (LimpliesElim _ (Land f g)). 2: exact H.
  apply IsProvedPropAx.
  apply Ax8IsPropAx, Ax8IsAx8.
  apply andprop. apply andprop.
Qed.

Lemma LorIntro1 : forall IsAxiom (f g:nat),
    IsLproposition g = true
    -> IsProved IsAxiom f
    -> IsProved IsAxiom (Lor f g).
Proof.
  intros.
  pose proof (IsProvedIsLproposition IsAxiom _ H0) as fprop.
  apply (LimpliesElim _ f). 2: exact H0.
  apply IsProvedPropAx, Ax9IsPropAx, Ax9IsAx9.
  exact fprop. exact H.
Qed.

Lemma LorIntro1_impl : forall IsAxiom (f g:nat),
    IsLproposition f = true
    -> IsLproposition g = true
    -> IsProved IsAxiom (Limplies f (Lor f g)).
Proof.
  intros.
  apply IsProvedPropAx, Ax9IsPropAx, Ax9IsAx9.
  exact H. exact H0.
Qed.

Lemma LorIntro2_impl : forall IsAxiom (f g:nat),
    IsLproposition f = true
    -> IsLproposition g = true
    -> IsProved IsAxiom (Limplies g (Lor f g)).
Proof.
  intros.
  apply IsProvedPropAx, Ax10IsPropAx, Ax10IsAx10.
  exact H. exact H0.
Qed.

Lemma LorIntro2 : forall IsAxiom (f g:nat),
    IsLproposition f = true
    -> IsProved IsAxiom g
    -> IsProved IsAxiom (Lor f g).
Proof.
  intros.
  pose proof (IsProvedIsLproposition IsAxiom _ H0) as gprop.
  apply (LimpliesElim _ g). 2: exact H0.
  apply IsProvedPropAx, Ax10IsPropAx, Ax10IsAx10.
  exact H. exact gprop.
Qed.

Lemma LforallIntro : forall IsAxiom (f v:nat),
    IsProved IsAxiom f
    -> IsProved IsAxiom (Lforall v f).
Proof.
  intros IsAxiom f v [pf H].
  exists (ConsNat (Lforall v f) pf).
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  rewrite CoordConsHeadNat. apply Nat.eqb_refl.
  apply Nat.leb_le. rewrite LengthConsNat.
  apply le_n_S, le_0_n.
  apply andb_prop in H. destruct H.
  rewrite LengthConsNat. simpl.
  apply andb_true_intro. split.
  2: rewrite TailConsNat; exact H0.
  apply Bool.orb_true_intro. right.
  apply Bool.orb_true_intro. left.
  apply Bool.orb_true_intro. left.
  apply Bool.orb_true_intro. left.
  apply andb_prop in H. destruct H.
  apply andb_true_intro. split.
  rewrite CoordConsHeadNat. apply LforallIsForall.
  apply FindNat_true. exists 0.
  split. rewrite TailConsNat.
  apply Nat.leb_le in H1. exact H1.
  rewrite TailConsNat.
  rewrite CoordConsHeadNat, CoordNat_forall_2.
  apply Nat.eqb_eq in H. exact H.
Qed.

Lemma LforallIntroHyp : forall IsAxiom h v p,
    VarOccursFreeInFormula v h = false
    -> IsProved IsAxiom (Limplies h p)
    -> IsProved IsAxiom (Limplies h (Lforall v p)).
Proof.
  intros.
  pose proof (IsProvedIsLproposition _ _ H0).
  rewrite IsLproposition_implies in H1.
  apply andb_prop in H1. destruct H1.
  apply (LimpliesElim _ (Lforall v (Limplies h p))).
  apply IsProvedIndepPremise; assumption.
  apply LforallIntro, H0.
Qed.

Lemma SpecializationIsSpecialization : forall prop v t,
    IsLproposition prop = true
    -> IsLterm t = true
    -> IsFreeForSubst t v prop = true
    -> IsSpecialization (Limplies (Lforall v prop) (Subst t v prop)) = true.
Proof.
  intros prop v t propprop tterm free.
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  - rewrite IsLproposition_implies.
    apply andb_true_intro. split.
    rewrite IsLproposition_forall. exact propprop.
    rewrite SubstIsLproposition. reflexivity. exact propprop. exact tterm.
  - apply LimpliesIsImplies.
  - apply Bool.orb_true_intro. left.
    rewrite CoordNat_implies_1.
    apply andb_true_intro. split.
    apply LforallIsForall. simpl.
    rewrite CoordNat_forall_1, CoordNat_forall_2.
    rewrite CoordNat_implies_2.
    apply andb_true_intro.
    destruct (VarOccursFreeInFormula v prop) eqn:des.
    split.
    rewrite FindSubstTerm_true. exact free. exact propprop. exact des.
    rewrite FindSubstTerm_true, Nat.eqb_refl. reflexivity.
    exact propprop. exact des.
    split.
    apply IsFreeForSubst_nosubst. exact propprop. exact des.
    rewrite Subst_nosubst, Subst_nosubst, Nat.eqb_refl. reflexivity.
    exact des. exact des.
Qed.

Lemma LforallElim_impl : forall IsAxiom (f v t:nat),
    IsLproposition f = true
    -> IsLterm t = true
    -> IsFreeForSubst t v f = true
    -> IsProved IsAxiom (Limplies (Lforall v f) (Subst t v f)).
Proof.
  intros.
  exists (ConsNat (Limplies (Lforall v f) (Subst t v f)) NilNat).
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  rewrite CoordConsHeadNat. apply Nat.eqb_refl.
  rewrite LengthConsNat. apply Nat.leb_le, le_n_S, le_0_n.
  rewrite IsProofLoop_specialization. reflexivity.
  apply SpecializationIsSpecialization.
  exact H.
  exact H0. exact H1.
Qed.

Lemma LforallElim : forall IsAxiom (f v t:nat),
    IsProved IsAxiom (Lforall v f)
    -> IsLterm t = true
    -> IsFreeForSubst t v f = true
    -> IsProved IsAxiom (Subst t v f).
Proof.
  intros.
  apply (LimpliesElim _ (Lforall v f)). 2: exact H.
  apply LforallElim_impl.
  pose proof (IsProvedIsLproposition IsAxiom _ H).
  rewrite IsLproposition_forall in H2. exact H2.
  exact H0. exact H1.
Qed.

Lemma LforallElim_2 : forall IsAxiom (f v t w u:nat),
    IsProved IsAxiom (Lforall w (Lforall v f))
    -> IsLterm t = true
    -> IsLterm u = true
    -> v <> w
    -> IsFreeForSubst t v (Subst u w f) = true
    -> IsFreeForSubst u w (Lforall v f) = true
    -> IsProved IsAxiom (Subst t v (Subst u w f)).
Proof.
  intros.
  apply LforallElim. 2: exact H0. 2: exact H3.
  pose proof (Subst_forall u w v f).
  apply Nat.eqb_neq in H2. rewrite H2 in H5.
  rewrite <- H5.
  apply LforallElim. exact H. exact H1. exact H4.
Qed.

Lemma SpecializationIsSpecializationExists : forall prop v t,
    IsLproposition prop = true
    -> IsLterm t = true
    -> IsFreeForSubst t v prop = true
    -> IsSpecialization (Limplies (Subst t v prop) (Lexists v prop)) = true.
Proof.
  intros prop v t propprop tterm free.
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  - rewrite IsLproposition_implies.
    apply andb_true_intro. split.
    rewrite SubstIsLproposition. reflexivity. exact propprop. exact tterm.
    rewrite IsLproposition_exists. exact propprop.
  - apply LimpliesIsImplies.
  - apply Bool.orb_true_intro; right.
    rewrite CoordNat_implies_1, CoordNat_implies_2.
    apply andb_true_intro. split.
    apply LexistsIsExists. simpl.
    rewrite CoordNat_exists_1, CoordNat_exists_2.
    apply andb_true_intro.
    destruct (VarOccursFreeInFormula v prop) eqn:des.
    split.
    rewrite FindSubstTerm_true. exact free. exact propprop. exact des.
    rewrite FindSubstTerm_true, Nat.eqb_refl. reflexivity.
    exact propprop. exact des.
    split.
    apply IsFreeForSubst_nosubst. exact propprop. exact des.
    rewrite Subst_nosubst, Subst_nosubst, Nat.eqb_refl. reflexivity.
    exact des. exact des.
Qed.

Lemma LexistsIntro_impl : forall IsAxiom (f v t:nat),
    IsLterm t = true
    -> IsLproposition f = true
    -> IsFreeForSubst t v f = true
    -> IsProved IsAxiom (Limplies (Subst t v f) (Lexists v f)).
Proof.
  intros.
  exists (ConsNat (Limplies (Subst t v f) (Lexists v f)) NilNat).
  apply andb_true_intro. split.
  apply andb_true_intro. split.
  rewrite CoordConsHeadNat. apply Nat.eqb_refl.
  rewrite LengthConsNat. apply Nat.leb_le, le_n_S, le_0_n.
  rewrite IsProofLoop_specialization. reflexivity.
  apply SpecializationIsSpecializationExists.
  exact H0. exact H. exact H1.
Qed.

Lemma LexistsIntro : forall IsAxiom (f v t:nat),
    IsLterm t = true
    -> IsLproposition f = true
    -> IsFreeForSubst t v f = true
    -> IsProved IsAxiom (Subst t v f)
    -> IsProved IsAxiom (Lexists v f).
Proof.
  intros.
  apply (LimpliesElim _ (Subst t v f)). 2: exact H2.
  apply LexistsIntro_impl; assumption.
Qed.

Lemma LexistsIntroIdemVar : forall IsAxiom (f v:nat),
    IsLproposition f = true
    -> IsProved IsAxiom (Limplies f (Lexists v f)).
Proof.
  intros. 
  rewrite <- (SubstIdemVar _ H v) at 1.
  apply LexistsIntro_impl. apply IsLterm_var.
  exact H. apply IsFreeForSubstIdemVar. exact H.
Qed. 

Lemma ExistsElimIsExistsElim : forall v p q,
    IsLproposition p = true
    -> IsLproposition q = true
    -> VarOccursFreeInFormula v q = false
    -> IsExistsElim (Limplies (Lexists v p)
                             (Limplies (Lforall v (Limplies p q)) q)) = true.
Proof.
  intros.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  - rewrite IsLproposition_implies, IsLproposition_exists.
    rewrite IsLproposition_implies, IsLproposition_forall.
    rewrite IsLproposition_implies, H, H0. reflexivity.
  - apply LimpliesIsImplies.
  - rewrite CoordNat_implies_1.
    apply LexistsIsExists.
  - rewrite CoordNat_implies_2.
    apply LimpliesIsImplies.
  - rewrite CoordNat_implies_2, CoordNat_implies_1.
    apply LforallIsForall.
  - rewrite CoordNat_implies_2, CoordNat_implies_1, CoordNat_forall_2.
    apply LimpliesIsImplies.
  - rewrite CoordNat_implies_2, CoordNat_implies_1, CoordNat_forall_2.
    rewrite CoordNat_implies_1, CoordNat_implies_1, CoordNat_exists_2.
    apply Nat.eqb_refl.
  - rewrite CoordNat_implies_2, CoordNat_implies_1, CoordNat_forall_2.
    rewrite CoordNat_implies_2, CoordNat_implies_2.
    apply Nat.eqb_refl.
  - rewrite CoordNat_implies_1, CoordNat_implies_2, CoordNat_implies_1.
    rewrite CoordNat_forall_1, CoordNat_exists_1.
    apply Nat.eqb_refl.
  - rewrite CoordNat_implies_2, CoordNat_implies_1, CoordNat_implies_2.
    rewrite CoordNat_forall_1.
    apply Bool.negb_true_iff, H1.
Qed.

Lemma LexistsElim : forall IsAxiom (v p q:nat),
    VarOccursFreeInFormula v q = false
    -> IsProved IsAxiom (Lexists v p)
    -> IsProved IsAxiom (Lforall v (Limplies p q))
    -> IsProved IsAxiom q.
Proof.
  intros.
  pose proof (IsProvedIsLproposition _ _ H0) as pprop.
  pose proof (IsProvedIsLproposition _ _ H1) as qprop.
  rewrite IsLproposition_exists in pprop.
  rewrite IsLproposition_forall, IsLproposition_implies in qprop.
  apply andb_prop in qprop.
  apply (LimpliesElim _ (Lforall v (Limplies p q))).
  apply (LimpliesElim _ (Lexists v p)).
  - exists (ConsNat (Limplies (Lexists v p)
                             (Limplies (Lforall v (Limplies p q)) q)) NilNat).
    apply andb_true_intro; split.
    apply andb_true_intro; split.
    rewrite CoordConsHeadNat. apply Nat.eqb_refl.
    rewrite LengthConsNat. apply Nat.leb_refl.
    rewrite LengthConsNat.
    simpl.
    rewrite CoordConsHeadNat, TailConsNat.
    apply andb_true_intro; split. 2: reflexivity.
    apply Bool.orb_true_intro. right.
    apply Bool.orb_true_intro. right.
    apply ExistsElimIsExistsElim. exact pprop. apply qprop.
    exact H.
  - exact H0.
  - exact H1.
Qed.

(* Aka ex falso quodlibet.
   Proving even a single contradiction implies proving all propositions.
   This is also known as the principle of explosion. *)
Lemma FalseElim : forall IsAxiom (f:nat),
    IsProved IsAxiom (Land f (Lnot f))
    -> forall (prop:nat), IsLproposition prop = true -> IsProved IsAxiom prop.
Proof.
  intros IsAxiom f pr prop propprop.
  assert (IsLproposition f = true) as fprop.
  { apply IsProvedIsLproposition in pr.
    rewrite IsLproposition_and in pr.
    apply andb_prop in pr. apply pr. }
  apply (LimpliesElim _ (Lnot f)).
  apply (LimpliesElim _ f).
  apply IsProvedPropAx, Ax5IsPropAx, Ax5IsAx5.
  exact fprop. exact propprop.
  apply (LandElim1 _ _ _ pr).
  apply (LandElim2 _ _ _ pr).
Qed.

Lemma LeqRefl : forall IsAxiom (t:nat),
    IsLterm t = true -> IsProved IsAxiom (Leq t t).
Proof.
  intros IsAxiom t tterm.
  pose proof (LforallElim IsAxiom (Leq (Lvar 0) (Lvar 0)) 0 t).
  rewrite Subst_eq in H.
  rewrite SubstTerm_var in H. simpl in H. apply H.
  apply LforallIntro. apply IsProvedEqAx.
  apply Bool.orb_true_intro. left.
  apply Bool.orb_true_intro. left.
  apply Bool.orb_true_intro. left.
  apply Bool.orb_true_intro. left.
  apply Nat.eqb_refl. exact tterm.
  apply IsFreeForSubst_rel2.
Qed.

Lemma LeqSym_impl : forall IsAxiom (t u:nat),
    IsLterm t = true
    -> IsLterm u = true
    -> IsProved IsAxiom (Limplies (Leq t u) (Leq u t)).
Proof.
  intros IsAxiom t u tterm uterm.
  assert (IsProved IsAxiom (Limplies (Leq (Lvar 0) (Lvar 1)) (Leq (Lvar 1) (Lvar 0)))).
  { apply IsProvedEqAx.
    apply Bool.orb_true_intro; left.
    apply Bool.orb_true_intro; left.
    apply Bool.orb_true_intro; left.
    apply Bool.orb_true_intro; right.
    apply Nat.eqb_refl. }
  (* Bump u's variable to avoid captures *)
  pose (MaxVarTerm u) as m.
  apply (LforallIntro IsAxiom _ 0) in H.
  apply (LforallElim IsAxiom _ 0 (Lvar (S (S m)))) in H.
  rewrite Subst_implies, Subst_eq, Subst_eq in H.
  rewrite SubstTerm_var, SubstTerm_var in H. simpl in H.
  (* Specialize u *)
  apply (LforallIntro IsAxiom _ 1) in H.
  apply (LforallElim IsAxiom _ 1 u) in H.
  rewrite Subst_implies, Subst_eq, Subst_eq in H.
  rewrite SubstTerm_var, SubstTerm_var in H. simpl in H.
  (* Specialize t *)
  apply (LforallIntro IsAxiom _ (S (S m))) in H.
  apply (LforallElim IsAxiom _ (S (S m)) t) in H.
  rewrite Subst_implies, Subst_eq, Subst_eq in H.
  rewrite SubstTerm_var in H. simpl in H.
  rewrite Nat.eqb_refl in H.
  rewrite SubstTerm_nosubst in H.
  exact H.
  apply MaxVarTermDoesNotOccur.
  apply le_S, Nat.le_refl.
  exact uterm. exact tterm.
  rewrite IsFreeForSubst_implies.
  apply andb_true_intro; split.
  unfold Leq. apply IsFreeForSubst_rel2.
  unfold Leq. apply IsFreeForSubst_rel2.
  exact uterm.
  rewrite IsFreeForSubst_implies.
  apply andb_true_intro; split.
  unfold Leq. apply IsFreeForSubst_rel2.
  unfold Leq. apply IsFreeForSubst_rel2.
  apply IsLterm_var.
  rewrite IsFreeForSubst_implies.
  apply andb_true_intro; split.
  unfold Leq. apply IsFreeForSubst_rel2.
  unfold Leq. apply IsFreeForSubst_rel2.
Qed.

Lemma LeqSym : forall IsAxiom (t u:nat),
    IsProved IsAxiom (Leq t u)
    -> IsProved IsAxiom (Leq u t).
Proof.
  intros. pose proof (IsProvedIsLproposition _ _ H).
  rewrite IsLproposition_eq in H0. apply andb_prop in H0.
  apply (LimpliesElim _ (Leq t u)). 2: exact H.
  apply LeqSym_impl; apply H0.
Qed.

Lemma LeqTrans_bumpvars : forall IsAxiom (n:nat),
    IsProved IsAxiom (Limplies (Land (Leq (Lvar n) (Lvar (1+n)))
                                     (Leq (Lvar (1+n)) (Lvar (2+n))))
                               (Leq (Lvar n) (Lvar (2+n)))).
Proof.
  intros.
  pose proof (LforallElim_2 IsAxiom
                            (Limplies (Land (Leq (Lvar 0) (Lvar 1))
                                            (Leq (Lvar 1) (Lvar (2+n))))
                                      (Leq (Lvar 0) (Lvar (2+n))))
                            0 (Lvar n) 1 (Lvar (1+n))) as felim.
  rewrite Subst_implies, Subst_eq, Subst_and, Subst_eq, Subst_eq in felim.
  rewrite Subst_implies, Subst_eq, Subst_and, Subst_eq, Subst_eq in felim.
  do 3 rewrite SubstTerm_var in felim. simpl in felim.
  do 3 rewrite SubstTerm_var in felim. simpl in felim.
  apply felim; clear felim.
  2: apply IsLterm_var. 2: apply IsLterm_var. 2: discriminate.
  apply LforallIntro, LforallIntro.
  pose proof (LforallElim IsAxiom
                          (Limplies (Land (Leq (Lvar 0) (Lvar 1))
                                          (Leq (Lvar 1) (Lvar 2)))
                                    (Leq (Lvar 0) (Lvar 2)))
                          2 (Lvar (2+n))) as felim.
  rewrite Subst_implies, Subst_eq, Subst_and, Subst_eq, Subst_eq in felim.
  do 3 rewrite SubstTerm_var in felim. simpl in felim.
  apply felim; clear felim.
  apply LforallIntro.
  apply IsProvedEqAx.
  apply Bool.orb_true_intro; left.
  apply Bool.orb_true_intro; left.
  apply Bool.orb_true_intro; right.
  apply Nat.eqb_refl. apply IsLterm_var.
  rewrite IsFreeForSubst_implies, IsFreeForSubst_and.
  unfold Leq. do 3 rewrite IsFreeForSubst_rel2. reflexivity.
  rewrite IsFreeForSubst_implies, IsFreeForSubst_and.
  unfold Leq. do 3 rewrite IsFreeForSubst_rel2. reflexivity.
  rewrite IsFreeForSubst_forall, IsFreeForSubst_implies, IsFreeForSubst_and.
  unfold Leq. do 3 rewrite IsFreeForSubst_rel2.
  rewrite VarOccursInTerm_var.
  simpl (true && true && true && negb (0 =? S n))%bool.
  rewrite Bool.orb_true_r. reflexivity.
Qed.

Lemma LeqTrans : forall IsAxiom (t u v:nat),
    IsProved IsAxiom (Leq t u)
    -> IsProved IsAxiom (Leq u v)
    -> IsProved IsAxiom (Leq t v).
Proof.
  intros.
  pose proof (IsProvedIsLproposition _ _ H) as tuprop.
  pose proof (IsProvedIsLproposition _ _ H0) as uvprop.
  rewrite IsLproposition_eq in uvprop.
  rewrite IsLproposition_eq in tuprop.
  apply andb_prop in tuprop. apply andb_prop in uvprop.
  apply (LimpliesElim _ (Land (Leq t u) (Leq u v))).
  2: exact (LandIntro _ _ _ H H0).
  pose (Nat.max (MaxVarTerm t) (Nat.max (MaxVarTerm u) (MaxVarTerm v)))
    as m.
  assert (MaxVarTerm t < S m).
  { apply le_n_S. unfold m.
    apply (Nat.le_trans _ _ _ (Nat.le_refl _) (Nat.le_max_l _ _)). }
  assert (MaxVarTerm u < S m).
  { apply le_n_S. unfold m.
    refine (Nat.le_trans _ _ _ _ (Nat.le_max_r _ _)).
    apply (Nat.le_trans _ _ _ (Nat.le_refl _) (Nat.le_max_l _ _)). }
  assert (MaxVarTerm v < S m).
  { apply le_n_S. unfold m.
    refine (Nat.le_trans _ _ _ _ (Nat.le_max_r _ _)).
    apply (Nat.le_trans _ _ _ (Nat.le_refl _) (Nat.le_max_r _ _)). }
  pose proof (LforallElim_2 IsAxiom
                            (Limplies (Land (Leq (Lvar (1+m)) (Lvar (2+m)))
                                            (Leq (Lvar (2+m)) v))
                                      (Leq (Lvar (1+m)) v))
                            (1+m) t (2+m) u) as felim.
  do 2 rewrite Subst_implies, Subst_and, Subst_eq, Subst_eq, Subst_eq in felim.
  do 2 rewrite SubstTerm_var in felim.
  rewrite Nat.eqb_refl in felim.
  assert (forall i j:nat, S i <= j -> i =? j = false).
  { intros. apply Nat.eqb_neq. intro abs. rewrite abs in H4.
    exact (Nat.lt_irrefl _ H4). }
  rewrite H4 in felim.
  rewrite SubstTerm_var, Nat.eqb_refl in felim.
  rewrite (SubstAboveMaxVarTerm t (1+m) u) in felim. 2: exact H2.
  rewrite (SubstAboveMaxVarTerm u (2+m) v) in felim.
  rewrite (SubstAboveMaxVarTerm t (1+m) v) in felim.
  2: exact H3. 2: apply uvprop.
  apply felim; clear felim.
  apply LforallIntro, LforallIntro.
  pose proof (LforallElim IsAxiom
                          (Limplies (Land (Leq (Lvar (1+m)) (Lvar (2+m)))
                                          (Leq (Lvar (2+m)) (Lvar (3+m))))
                                    (Leq (Lvar (1+m)) (Lvar (3+m))))
                          (3+m) v) as felim.
  rewrite Subst_implies, Subst_and, Subst_eq, Subst_eq, Subst_eq in felim.
  do 3 rewrite SubstTerm_var in felim. simpl in felim.
  rewrite Nat.eqb_refl, H4, H4 in felim.
  apply felim; clear felim.
  apply LforallIntro, LeqTrans_bumpvars.
  apply uvprop.
  rewrite IsFreeForSubst_implies, IsFreeForSubst_and.
  unfold Leq. do 3 rewrite IsFreeForSubst_rel2. reflexivity.
  apply Nat.le_refl. apply le_S, Nat.le_refl.
  apply tuprop. apply tuprop. apply Nat.eqb_neq. rewrite H4. reflexivity.
  apply Nat.le_refl.
  rewrite IsFreeForSubst_implies, IsFreeForSubst_and.
  unfold Leq. do 3 rewrite IsFreeForSubst_rel2. reflexivity.
  rewrite IsFreeForSubst_forall.
  rewrite IsFreeForSubst_implies, IsFreeForSubst_and.
  unfold Leq. do 3 rewrite IsFreeForSubst_rel2.
  rewrite MaxVarTermDoesNotOccur.
  simpl (true && true && true && negb false)%bool.
  rewrite Bool.orb_true_r. reflexivity.
  exact H2. apply tuprop. apply le_S, H3. apply uvprop. apply tuprop.
  apply Nat.le_refl.
Qed.

Lemma IsInconsistentEquiv : forall IsAxiom,
    IsInconsistent IsAxiom
    -> forall prop:nat, IsLproposition prop = true -> IsProved IsAxiom prop.
Proof.
  intros. apply (FalseElim IsAxiom (Leq (Lvar 0) (Lvar 0))).
  2: exact H0. apply LandIntro. apply LeqRefl, IsLterm_var.
  exact H.
Qed.

Lemma IsConsistentEquiv : forall IsAxiom prop,
    IsLproposition prop = true
    -> (forall n:nat, IsProof IsAxiom prop n = false)
    -> IsConsistent IsAxiom.
Proof.
  intros. intro incons.
  pose proof (IsInconsistentEquiv IsAxiom incons prop H) as [pr prf].
  specialize (H0 pr). rewrite H0 in prf.
  discriminate.
Qed.

Lemma LimpliesRefl : forall IsAxiom (f:nat),
    IsLproposition f = true
    -> IsProved IsAxiom (Limplies f f).
Proof.
  intros.
  apply (LimpliesElim _ (Limplies f (Limplies f f))).
  2: apply IsProvedPropAx, Ax1IsPropAx, Ax1IsAx1; exact H.
  apply (LimpliesElim _ (Limplies f (Limplies (Limplies f f) f))).
  apply IsProvedPropAx, Ax2IsPropAx, Ax2IsAx2. exact H.
  rewrite IsLproposition_implies.
  apply andb_true_intro. split. exact H. exact H. exact H.
  apply IsProvedPropAx, Ax1IsPropAx, Ax1IsAx1. exact H.
  rewrite IsLproposition_implies.
  apply andb_true_intro. split. exact H. exact H.
Qed.

Lemma LimpliesTrans : forall IsAxiom (f g h:nat),
    IsProved IsAxiom (Limplies f g)
    -> IsProved IsAxiom (Limplies g h)
    -> IsProved IsAxiom (Limplies f h).
Proof.
  intros.
  pose proof (IsProvedIsLproposition IsAxiom _ H) as fgprop.
  rewrite IsLproposition_implies in fgprop.
  pose proof (IsProvedIsLproposition IsAxiom _ H0) as ghprop.
  rewrite IsLproposition_implies in ghprop.
  apply andb_prop in fgprop. apply andb_prop in ghprop.
  apply (LimpliesElim _ (Limplies f g)). 2: exact H.
  apply (LimpliesElim _ (Limplies f (Limplies g h))).
  apply IsProvedPropAx, Ax2IsPropAx, Ax2IsAx2.
  apply fgprop. apply ghprop. apply ghprop.
  apply (LimpliesElim _ (Limplies g h)). 2: exact H0.
  apply IsProvedPropAx, Ax1IsPropAx, Ax1IsAx1.
  rewrite IsLproposition_implies. apply andb_true_intro.
  split. apply fgprop. apply ghprop. apply fgprop.
Qed.

Lemma LimpliesTrans_impl : forall IsAxiom (f g h:nat),
    IsLproposition f = true
    -> IsProved IsAxiom (Limplies g h)
    -> IsProved IsAxiom (Limplies (Limplies f g) (Limplies f h)).
Proof.
  intros.
  pose proof (IsProvedIsLproposition IsAxiom _ H0) as ghprop.
  rewrite IsLproposition_implies in ghprop.
  apply andb_prop in ghprop.
  apply (LimpliesElim _ (Limplies f (Limplies g h))).
  apply IsProvedPropAx, Ax2IsPropAx, Ax2IsAx2.
  exact H. apply ghprop. apply ghprop.
  apply (LimpliesElim _ (Limplies g h)). 2: exact H0.
  apply IsProvedPropAx, Ax1IsPropAx, Ax1IsAx1.
  rewrite IsLproposition_implies. apply andb_true_intro.
  split. apply ghprop. apply ghprop. exact H.
Qed.

Lemma NotByContradiction : forall IsAxiom prop,
    IsProved IsAxiom (Limplies prop (Lnot prop))
    -> IsProved IsAxiom (Lnot prop).
Proof.
  intros.
  pose proof (IsProvedIsLproposition _ _ H) as propprop.
  rewrite IsLproposition_implies in propprop.
  apply andb_prop in propprop.
  apply (LimpliesElim _ (Limplies prop (Lnot prop))).
  2: exact H. clear H.
  apply (LimpliesElim _ (Limplies prop prop)).
  2: apply LimpliesRefl.
  apply IsProvedPropAx, Ax3IsPropAx, Ax3IsAx3.
  apply propprop. apply propprop. apply propprop.
Qed.

Lemma LandIntroHyp : forall IsAxiom h p q,
    IsProved IsAxiom (Limplies h p)
    -> IsProved IsAxiom (Limplies h q)
    -> IsProved IsAxiom (Limplies h (Land p q)).
Proof.
  intros.
  pose proof (IsProvedIsLproposition _ _ H) as hpprop.
  rewrite IsLproposition_implies in hpprop.
  apply andb_prop in hpprop. destruct hpprop as [hprop pprop].
  pose proof (IsProvedIsLproposition _ _ H0) as hqprop.
  rewrite IsLproposition_implies in hqprop.
  apply andb_prop in hqprop. destruct hqprop as [_ qprop].
  assert (IsProved IsAxiom (Limplies p (Limplies q (Land p q)))).
  { apply IsProvedPropAx, Ax6IsPropAx, Ax6IsAx6.
    apply pprop. apply qprop. }
  apply (LimpliesTrans IsAxiom h p) in H1. 2: exact H. clear H.
  pose proof (ModusPonensHyp IsAxiom h q (Land p q) hprop qprop).
  rewrite IsLproposition_and, pprop, qprop in H.
  specialize (H eq_refl).
  pose proof (LimpliesElim IsAxiom _ _ H H1).
  exact (LimpliesElim IsAxiom _ _ H2 H0).
Qed.

(* Reduce hypotheses to 1 conjunction, then apply tactics with 1 hypothesis. *)
Lemma PullHypothesis : forall IsAxiom h p q,
    IsProved IsAxiom (Limplies (Land h p) q)
    -> IsProved IsAxiom (Limplies h (Limplies p q)).
Proof.
  intros.
  pose proof (IsProvedIsLproposition _ _ H) as hpqprop.
  rewrite IsLproposition_implies, IsLproposition_and in hpqprop.
  apply andb_prop in hpqprop. destruct hpqprop.
  apply andb_prop in H0.
  apply (LimpliesTrans _ _ (Limplies p (Land h p))).
  apply IsProvedPropAx, Ax6IsPropAx, Ax6IsAx6; apply H0.
  apply LimpliesTrans_impl, H. apply H0.
Qed.

Lemma PushHypothesis : forall IsAxiom h p q,
    IsProved IsAxiom (Limplies h (Limplies p q))
    -> IsProved IsAxiom (Limplies (Land h p) q).
Proof.
  intros.
  pose proof (IsProvedIsLproposition _ _ H) as hpqprop.
  rewrite IsLproposition_implies, IsLproposition_implies in hpqprop.
  apply andb_prop in hpqprop. destruct hpqprop as [hprop pqprop].
  apply andb_prop in pqprop. destruct pqprop as [pprop qprop].
  assert (IsProved IsAxiom (Limplies (Land h p) (Limplies p q))).
  { apply (LimpliesTrans _ _ h).
    exact (LandElim1_impl IsAxiom h p hprop pprop). exact H. }
  pose proof (LandElim2_impl IsAxiom h p hprop pprop).
  pose proof (ModusPonensHyp IsAxiom (Land h p) p q).
  rewrite IsLproposition_and, hprop, pprop in H2.
  specialize (H2 eq_refl eq_refl qprop).
  pose proof (LimpliesElim IsAxiom _ _ H2 H0).
  exact (LimpliesElim IsAxiom _ _ H3 H1).
Qed.

Lemma IsProvedContraposition : forall IsAxiom (f g : nat),
    IsProved IsAxiom (Limplies f g)
    -> IsProved IsAxiom (Limplies (Lnot g) (Lnot f)).
Proof.
  intros.
  pose proof (IsProvedIsLproposition _ _ H).
  rewrite IsLproposition_implies in H0. apply andb_prop in H0.
  apply (LimpliesTrans _ _ (Limplies f (Lnot g))).
  apply IsProvedPropAx, Ax1IsPropAx, Ax1IsAx1.
  rewrite IsLproposition_not. apply H0. apply H0.
  apply (LimpliesElim _ (Limplies f g)).
  apply IsProvedPropAx, Ax3IsPropAx, Ax3IsAx3.
  apply H0. apply H0. exact H.
Qed.

Lemma LnotLnotIntro : forall IsAxiom f,
    IsProved IsAxiom f -> IsProved IsAxiom (Lnot (Lnot f)).
Proof.
  intros. 
  pose proof (IsProvedIsLproposition _ _ H) as fprop.
  apply (LimpliesElim _ (Limplies (Lnot f) (Lnot f))).
  apply (LimpliesElim _ (Limplies (Lnot f) f)).
  apply IsProvedPropAx, Ax3IsPropAx, Ax3IsAx3.
  rewrite IsLproposition_not. exact fprop. exact fprop.
  apply (LimpliesElim _ f).
  apply IsProvedPropAx, Ax1IsPropAx, Ax1IsAx1. exact fprop.
  rewrite IsLproposition_not. exact fprop. exact H.
  apply LimpliesRefl.
  rewrite IsLproposition_not. exact fprop.
Qed. 

Lemma FalseElim_impl : forall IsAxiom (f prop:nat),
    IsProved IsAxiom (Lnot f)
    -> IsLproposition prop = true
    -> IsProved IsAxiom (Limplies f prop).
Proof.
  intros IsAxiom f prop pr propprop.
  pose proof (IsProvedIsLproposition _ _ pr).
  rewrite IsLproposition_not in H.
  apply (LimpliesElim _ (Lnot f)). 2: exact pr.
  apply PullHypothesis.
  apply (LimpliesTrans _ _ (Land f (Lnot f))).
  apply LandIntroHyp.
  apply LandElim2_impl. rewrite IsLproposition_not. exact H. exact H.
  apply LandElim1_impl. rewrite IsLproposition_not. exact H. exact H.
  apply PushHypothesis.
  apply IsProvedPropAx, Ax5IsPropAx, Ax5IsAx5.
  exact H. exact propprop.
Qed. 

Lemma IsProvedContraposition_impl : forall IsAxiom (f g : nat),
    IsLproposition f = true
    -> IsLproposition g = true
    -> IsProved IsAxiom (Limplies (Limplies f g) (Limplies (Lnot g) (Lnot f))).
Proof.
  intros.
  apply PullHypothesis.
  apply (LimpliesTrans _ _ (Land (Limplies f g) (Limplies f (Lnot g)))).
  apply LandIntroHyp.
  apply LandElim1_impl.
  rewrite IsLproposition_implies, H, H0. reflexivity.
  rewrite IsLproposition_not. exact H0.
  apply (LimpliesTrans _ _ (Lnot g)).
  apply LandElim2_impl.
  rewrite IsLproposition_implies, H, H0. reflexivity.
  rewrite IsLproposition_not. exact H0.
  apply IsProvedPropAx, Ax1IsPropAx, Ax1IsAx1.
  rewrite IsLproposition_not. exact H0. exact H.
  apply PushHypothesis.
  apply IsProvedPropAx, Ax3IsPropAx, Ax3IsAx3.
  exact H. exact H0.
Qed.

Lemma LandElim11_impl : forall IsAxiom (f g h:nat),
    IsLproposition f = true
    -> IsLproposition g = true
    -> IsLproposition h = true
    -> IsProved IsAxiom (Limplies (Land (Land f g) h) f).
Proof.
  intros. apply (LimpliesTrans _ _ (Land f g)).
  apply LandElim1_impl.
  rewrite IsLproposition_and, H, H0. reflexivity.
  exact H1.
  apply LandElim1_impl; assumption.
Qed.

Lemma LandElim12_impl : forall IsAxiom (f g h:nat),
    IsLproposition f = true
    -> IsLproposition g = true
    -> IsLproposition h = true
    -> IsProved IsAxiom (Limplies (Land (Land f g) h) g).
Proof.
  intros. apply (LimpliesTrans _ _ (Land f g)).
  apply LandElim1_impl.
  rewrite IsLproposition_and, H, H0. reflexivity.
  exact H1.
  apply LandElim2_impl; assumption.
Qed.

Lemma LequivRefl : forall IsAxiom (f:nat),
    IsLproposition f = true
    -> IsProved IsAxiom (Lequiv f f).
Proof.
  intros. apply LandIntro; apply LimpliesRefl, H.
Qed.

Lemma LequivSym : forall IsAxiom (f g:nat),
    IsProved IsAxiom (Lequiv f g)
    -> IsProved IsAxiom (Lequiv g f).
Proof.
  intros. apply LandIntro.
  apply LandElim2 in H. exact H.
  apply LandElim1 in H. exact H.
Qed.

Lemma LequivTrans : forall IsAxiom (f g h:nat),
    IsProved IsAxiom (Lequiv f g)
    -> IsProved IsAxiom (Lequiv g h)
    -> IsProved IsAxiom (Lequiv f h).
Proof.
  intros. apply LandIntro.
  apply (LimpliesTrans _ _ g). apply LandElim1 in H. exact H.
  apply LandElim1 in H0. exact H0.
  apply (LimpliesTrans _ _ g). apply LandElim2 in H0. exact H0.
  apply LandElim2 in H. exact H.
Qed.

Lemma MaxVarChange : forall IsAxiom prop v w,
    MaxVar prop < w
    -> IsProved IsAxiom prop
    -> IsProved IsAxiom (Subst (Lvar w) v prop).
Proof.
  intros.
  apply LforallElim. apply LforallIntro, H0.
  apply IsLterm_var.
  apply MaxVarFreeSubst_var. 2: exact H.
  apply IsProvedIsLproposition in H0. exact H0.
Qed.

Lemma IsFreeForSubst_EqTerms : forall i terms1 terms2 u v,
    IsFreeForSubst u v (EqTerms terms1 terms2 i) = true.
Proof.
  induction i.
  - intros. simpl. unfold Leq. apply IsFreeForSubst_rel2.
  - intros. simpl. rewrite IsFreeForSubst_and, IHi.
    simpl. unfold Leq. apply IsFreeForSubst_rel2.
Qed. 

Definition ProgressiveSubst (terms1 terms2 numSubsts : nat) : nat :=
  MapNat (fun k => if le_lt_dec numSubsts k
                then CoordNat terms1 k else CoordNat terms2 k)
         (RangeNat 0 (LengthNat terms1)).

Lemma ProgressiveSubstLength : forall terms1 terms2 numSubsts,
    LengthNat (ProgressiveSubst terms1 terms2 numSubsts) = LengthNat terms1.
Proof.
  intros. unfold ProgressiveSubst.
  rewrite LengthMapNat, LengthRangeNat. reflexivity.
Qed.

Lemma ProgressiveSubstTruncated : forall terms1 terms2 numSubst,
    NthTailNat (ProgressiveSubst terms1 terms2 numSubst) (LengthNat terms1) = 0.
Proof.
  intros. unfold ProgressiveSubst.
  rewrite <- (LengthRangeNat (LengthNat terms1) 0) at 2.
  apply MapNatTruncated.
Qed.

Lemma ProgressiveSubstInit : forall terms1 terms2,
    NthTailNat terms1 (LengthNat terms1) = 0
    -> ProgressiveSubst terms1 terms2 0 = terms1.
Proof.
  intros. apply TruncatedEqNat.
  apply ProgressiveSubstLength.
  rewrite ProgressiveSubstLength. rewrite ProgressiveSubstTruncated.
  symmetry. exact H.
  intros k H0. rewrite ProgressiveSubstLength in H0.
  unfold ProgressiveSubst. rewrite CoordMapNat, CoordRangeNat.
  reflexivity. exact H0. rewrite LengthRangeNat. exact H0.
Qed.

Lemma ProgressiveSubstComplete : forall terms1 terms2 numSubst,
    LengthNat terms1 <= numSubst
    -> LengthNat terms1 = LengthNat terms2
    -> NthTailNat terms2 (LengthNat terms2) = 0
    -> ProgressiveSubst terms1 terms2 numSubst = terms2.
Proof.
  intros. apply TruncatedEqNat.
  rewrite ProgressiveSubstLength. exact H0.
  rewrite ProgressiveSubstLength. rewrite ProgressiveSubstTruncated.
  symmetry. exact H1.
  intros k H2. rewrite ProgressiveSubstLength in H2.
  unfold ProgressiveSubst. rewrite CoordMapNat, CoordRangeNat.
  simpl. destruct (le_lt_dec numSubst k). 2: reflexivity.
  exfalso. apply (Nat.lt_irrefl k).
  apply (Nat.lt_le_trans _ _ _ H2).
  apply (Nat.le_trans _ _ _ H l). exact H2.
  rewrite LengthRangeNat. exact H2.
Qed.

Lemma Subst_EqTerms : forall u v i terms1 terms2,
    i < LengthNat terms1
    -> i < LengthNat terms2
    -> Subst u v (EqTerms terms1 terms2 i)
      = EqTerms (MapNat (SubstTerm u v) terms1)
                (MapNat (SubstTerm u v) terms2) i.
Proof.
  induction i.
  - intros. simpl.
    rewrite Subst_eq, CoordMapNat, CoordMapNat.
    reflexivity. exact H0. exact H.
  - intros. simpl.
    rewrite Subst_and. apply f_equal2.
    + rewrite IHi. reflexivity.
      apply (Nat.le_trans _ (S (S i))).
      apply le_S, Nat.le_refl. exact H.
      apply (Nat.le_trans _ (S (S i))).
      apply le_S, Nat.le_refl. exact H0.
    + clear IHi. rewrite Subst_eq, CoordMapNat, CoordMapNat.
      reflexivity. exact H0. exact H.
Qed.

Lemma ProgressiveSubstIncr : forall terms1 terms2 h numSubst,
    numSubst < LengthNat terms1
    -> (forall k, k < LengthNat terms1 -> S numSubst <= k
            -> h (CoordNat terms1 k) = CoordNat terms1 k)
    -> h (CoordNat terms1 numSubst) = CoordNat terms2 numSubst
    -> (forall k, k < LengthNat terms1 -> k < numSubst
            -> h (CoordNat terms2 k) = CoordNat terms2 k)
    -> MapNat h (ProgressiveSubst terms1 terms2 numSubst)
      = ProgressiveSubst terms1 terms2 (S numSubst).
Proof.
  intros. unfold ProgressiveSubst. rewrite MapMapNat.
  apply MapNatExt. intros k H3. rewrite LengthRangeNat in H3.
  rewrite CoordRangeNat, Nat.add_0_l. 2: exact H3.
  destruct (le_lt_dec numSubst k), (le_lt_dec (S numSubst) k).
  - clear l. apply H0; assumption. 
  - replace k with numSubst. exact H1.
    apply Nat.le_antisymm. exact l. apply le_S_n, l0.
  - exfalso. apply (Nat.lt_irrefl k). apply (Nat.lt_le_trans _ _ _ l).
    refine (Nat.le_trans _ _ _ _ l0). apply le_S, Nat.le_refl.
  - clear l0. apply H2; assumption.
Qed.

Lemma LeqElim_rel_bumpvars : forall IsAxiom (r arity n:nat),
    1 <= arity ->
    2 * arity <= n ->
    IsProved IsAxiom (Limplies (EqTerms (EvenVars n arity)
                                        (EvenVars (S n) arity) (pred arity))
                               (Lequiv (Lrel r (EvenVars n arity))
                                       (Lrel r (EvenVars (S n) arity)))).
Proof.
  assert (forall i j, 1 + 2*i =? 2*j = false) as oddneqeven.
  { intros. apply Nat.eqb_neq. intro abs.
    pose proof (Nat.odd_add_mul_2 1 i).
    rewrite abs, Nat.odd_1 in H.
    pose proof (Nat.odd_add_mul_2 0 j).
    rewrite Nat.add_0_l, H, Nat.odd_0 in H0. discriminate. }
  assert (forall i r terms1 terms2 u v,
             IsFreeForSubst u v (Limplies (EqTerms terms1 terms2 i)
                                          (Lequiv (Lrel r terms1) (Lrel r terms2))) = true)
    as allfree.
  { intros.
    rewrite IsFreeForSubst_implies, IsFreeForSubst_EqTerms.
    simpl.
    rewrite IsFreeForSubst_equiv, IsFreeForSubst_rel.
    rewrite IsFreeForSubst_rel. reflexivity.
    unfold Lrel. rewrite CoordConsHeadNat. reflexivity.
    unfold Lrel. rewrite CoordConsHeadNat. reflexivity. }
  assert (forall numSubst IsAxiom r arity n,
             1 <= arity ->
             2 * arity <= n ->
             numSubst <= arity ->
             IsProved IsAxiom (Limplies (EqTerms (ProgressiveSubst
                                                    (EvenVars 0 arity)
                                                    (EvenVars n arity)
                                                    numSubst)
                                                 (ProgressiveSubst
                                                    (EvenVars 1 arity)
                                                    (EvenVars (S n) arity)
                                                    numSubst)
                                                 (pred arity))
                                        (Lequiv (Lrel r (ProgressiveSubst
                                                    (EvenVars 0 arity)
                                                    (EvenVars n arity)
                                                    numSubst))
                                                (Lrel r (ProgressiveSubst
                                                    (EvenVars 1 arity)
                                                    (EvenVars (S n) arity)
                                                    numSubst))))).
  induction numSubst.
  - intros. simpl. apply IsProvedEqAx.
    apply Bool.orb_true_intro; right.
    apply andb_true_intro; split.
    apply andb_true_intro; split.
    apply andb_true_intro; split.
    apply LimpliesIsImplies.
    rewrite CoordNat_implies_2, CoordNat_equiv_1, CoordNat_implies_1.
    rewrite LengthLrel, ProgressiveSubstLength.
    destruct arity. inversion H.
    rewrite LengthEvenVarsNat. reflexivity.
    rewrite CoordNat_implies_1, CoordNat_implies_2.
    rewrite CoordNat_equiv_1, CoordNat_implies_1, LengthLrel, ProgressiveSubstLength.
    simpl. rewrite Nat.sub_0_r.
    rewrite ProgressiveSubstInit, ProgressiveSubstInit, LengthEvenVarsNat.
    apply Nat.eqb_refl.
    rewrite LengthEvenVarsNat. apply EvenVarsTruncated.
    rewrite LengthEvenVarsNat. apply EvenVarsTruncated.
    rewrite CoordNat_implies_2, CoordNat_equiv_1.
    rewrite CoordNat_implies_1, CoordNat_rel_1, LengthLrel, ProgressiveSubstLength.
    rewrite ProgressiveSubstInit, ProgressiveSubstInit, LengthEvenVarsNat.
    replace (2 + arity - 2) with arity. apply Nat.eqb_refl.
    simpl. rewrite Nat.sub_0_r. reflexivity.
    rewrite LengthEvenVarsNat. apply EvenVarsTruncated.
    rewrite LengthEvenVarsNat. apply EvenVarsTruncated.
  - intros. specialize (IHnumSubst IsAxiom r arity n H H0).
    apply (LforallIntro _ _ (2 * numSubst)) in IHnumSubst.
    apply (LforallElim IsAxiom _ _ (Lvar (n+2*numSubst))) in IHnumSubst.
    2: apply IsLterm_var. 2: apply allfree.
    rewrite Subst_implies, Subst_equiv, Subst_rel, Subst_rel in IHnumSubst.
    rewrite Subst_EqTerms in IHnumSubst.
    2: rewrite ProgressiveSubstLength.
    3: rewrite ProgressiveSubstLength.
    apply (LforallIntro _ _ (1 + 2 * numSubst)) in IHnumSubst.
    apply (LforallElim IsAxiom _ _ (Lvar (S n+2*numSubst))) in IHnumSubst.
    2: apply IsLterm_var. 2: apply allfree.
    rewrite Subst_implies, Subst_equiv, Subst_rel, Subst_rel in IHnumSubst.
    rewrite Subst_EqTerms in IHnumSubst.
    rewrite MapMapNat, MapMapNat in IHnumSubst.
    rewrite ProgressiveSubstIncr, ProgressiveSubstIncr in IHnumSubst.
    exact IHnumSubst.
    + rewrite LengthEvenVarsNat. exact H1.
    + clear IHnumSubst. intros k H2 H3.
      rewrite CoordEvenVarsNat.
      rewrite SubstTerm_var, oddneqeven, SubstTerm_var.
      destruct (1 + 2 * k =? 1 + 2 * numSubst) eqn:des. 2: reflexivity.
      exfalso. apply Nat.eqb_eq in des. 
      apply (Nat.lt_irrefl numSubst).
      apply (Nat.lt_le_trans _ _ _ H3).
      apply (Nat.mul_le_mono_pos_l  _ _ 2). auto.
      apply (Nat.add_le_mono_l _ _ 1). rewrite des. apply Nat.le_refl.
      rewrite LengthEvenVarsNat in H2. exact H2.
    + clear IHnumSubst.
      rewrite CoordEvenVarsNat, CoordEvenVarsNat.
      rewrite SubstTerm_var, oddneqeven, SubstTerm_var, Nat.eqb_refl.
      reflexivity. exact H1. exact H1.
    + clear IHnumSubst. intros k H2 H3.
      rewrite LengthEvenVarsNat in H2.
      rewrite CoordEvenVarsNat, SubstTerm_var. 2: exact H2.
      destruct (S n + 2 * k =? 2 * numSubst) eqn:des.
      apply Nat.eqb_eq in des.
      exfalso.
      apply (Nat.lt_irrefl numSubst).
      apply (Nat.lt_le_trans _ _ _ H1).
      apply (Nat.mul_le_mono_pos_l  _ _ 2). auto.
      apply (Nat.le_trans _ _ _ H0). rewrite <- des. 
      simpl. apply le_S.
      rewrite <- (Nat.add_0_r n) at 1.
      apply Nat.add_le_mono_l, le_0_n.
      rewrite SubstTerm_var.
      destruct (S n + 2 * k =? 1 + 2 * numSubst) eqn:des2.
      2: reflexivity. exfalso. apply Nat.eqb_eq in des2.
      apply (Nat.lt_irrefl numSubst).
      apply (Nat.lt_le_trans _ _ _ H1).
      apply (Nat.mul_le_mono_pos_l  _ _ 2). auto.
      apply (Nat.le_trans _ _ _ H0).
      apply (Nat.add_le_mono_l _ _ 1). rewrite <- des2.
      simpl. apply le_n_S.
      rewrite <- (Nat.add_0_r n) at 1.
      apply Nat.add_le_mono_l, le_0_n.
    + rewrite LengthEvenVarsNat. exact H1.
    + clear IHnumSubst. intros k H2 H3.
      rewrite LengthEvenVarsNat in H2.
      rewrite CoordEvenVarsNat, SubstTerm_var, Nat.add_0_l. 2: exact H2.
      destruct (2 * k =? 2 * numSubst) eqn:des. exfalso.
      apply Nat.eqb_eq in des. apply Nat.mul_cancel_l in des. 2: discriminate.
      rewrite des in H3. exact (Nat.lt_irrefl _ H3).
      rewrite SubstTerm_var, Nat.eqb_sym, oddneqeven. reflexivity.
    + clear IHnumSubst.
      rewrite CoordEvenVarsNat, SubstTerm_var, Nat.eqb_refl, SubstTerm_var.
      2: exact H1.
      rewrite CoordEvenVarsNat. 2: exact H1.
      destruct (n + 2 * numSubst =? 1 + 2 * numSubst) eqn:des. 2: reflexivity.
      exfalso. apply Nat.eqb_eq in des.
      apply Nat.add_cancel_r in des. subst n.
      destruct arity. inversion H. simpl in H0.
      apply le_S_n in H0. rewrite Nat.add_succ_r in H0. inversion H0.
    + clear IHnumSubst. intros k H2 H3.
      rewrite LengthEvenVarsNat in H2.
      rewrite CoordEvenVarsNat. 2: exact H2.
      rewrite SubstTerm_var.
      destruct (n + 2 * k =? 2 * numSubst) eqn:des.
      apply Nat.eqb_eq in des. exfalso.
      apply (Nat.lt_irrefl numSubst).
      apply (Nat.lt_le_trans _ _ _ H1).
      apply (Nat.mul_le_mono_pos_l  _ _ 2). auto.
      apply (Nat.le_trans _ _ _ H0). rewrite <- des.
      rewrite <- (Nat.add_0_r n) at 1.
      apply Nat.add_le_mono_l, le_0_n.
      rewrite SubstTerm_var.
      destruct (n + 2 * k =? 1 + 2 * numSubst) eqn:des2. 2: reflexivity.
      exfalso. apply Nat.eqb_eq in des2.
      apply (Nat.lt_irrefl numSubst).
      apply (Nat.lt_le_trans _ _ _ H1).
      apply (Nat.mul_le_mono_pos_l  _ _ 2). auto.
      apply (Nat.le_trans _ _ _ H0).
      apply (Nat.add_le_mono_l _ _ 1). rewrite <- des2. 
      rewrite Nat.add_comm.
      apply Nat.add_le_mono_l. 
      destruct k. 2: apply le_n_S, le_0_n.
      exfalso. rewrite Nat.mul_0_r, Nat.add_0_r in des2.
      clear des. subst n.
      apply (Nat.div_le_mono _ _ 2) in H0. 2: discriminate.
      rewrite Nat.mul_comm, Nat.div_mul in H0. 2: discriminate.
      rewrite Nat.mul_comm, Nat.add_comm, Nat.div_add_l in H0.
      simpl in H0. rewrite Nat.add_0_r in H0.
      apply (Nat.lt_irrefl numSubst).
      exact (Nat.lt_le_trans _ _ _ H1 H0). discriminate.
    + clear IHnumSubst. rewrite LengthMapNat, ProgressiveSubstLength.
      destruct arity. inversion H.
      rewrite LengthEvenVarsNat.
      apply Nat.le_refl.
    + clear IHnumSubst. rewrite LengthMapNat, ProgressiveSubstLength.
      destruct arity. inversion H.
      rewrite LengthEvenVarsNat. apply Nat.le_refl.
    + rewrite LengthEvenVarsNat.
      destruct arity. inversion H. apply Nat.le_refl.
    + rewrite LengthEvenVarsNat.
      destruct arity. inversion H. apply Nat.le_refl.
    + refine (Nat.le_trans _ _ _ _ H1). apply le_S, Nat.le_refl.
  - intros. specialize (H arity IsAxiom r arity n H0 H1 (Nat.le_refl _)).
    rewrite ProgressiveSubstComplete, ProgressiveSubstComplete in H.
    exact H. rewrite LengthEvenVarsNat.
    apply Nat.le_refl.
    rewrite LengthEvenVarsNat, LengthEvenVarsNat. reflexivity.
    rewrite LengthEvenVarsNat. apply EvenVarsTruncated.
    rewrite LengthEvenVarsNat. apply Nat.le_refl.
    rewrite LengthEvenVarsNat, LengthEvenVarsNat. reflexivity.
    rewrite LengthEvenVarsNat. apply EvenVarsTruncated.
Qed.

Lemma LeqElim_rel_aux :
  forall IsAxiom (r terms1 terms2:nat) m,
    LengthNat terms1 = LengthNat terms2
    -> 1 <= LengthNat terms1
    -> IsLproposition (Lrel r terms1) = true
    -> IsLproposition (Lrel r terms2) = true
    -> 2 * LengthNat terms1 <= m
    -> MaxVar (Lrel r terms1) <= m
    -> MaxVar (Lrel r terms2) <= m
    -> forall numSubst,
        numSubst <= LengthNat terms1 ->
        IsProved IsAxiom (Limplies (EqTerms (ProgressiveSubst
                                                    (EvenVars m (LengthNat terms1))
                                                    terms1 numSubst)
                                                 (ProgressiveSubst
                                                    (EvenVars (S m) (LengthNat terms1))
                                                    terms2 numSubst)
                                                 (pred (LengthNat terms1)))
                                        (Lequiv (Lrel r (ProgressiveSubst
                                                    (EvenVars m (LengthNat terms1))
                                                    terms1 numSubst))
                                                (Lrel r (ProgressiveSubst
                                                    (EvenVars (S m) (LengthNat terms1))
                                                    terms2 numSubst)))).
Proof.
  intros IsAxiom r terms1 terms2 m samelength poslength terms1prop terms2prop
         m1 m2 m3.
  apply IsLproposition_rel in terms1prop.
  destruct terms1prop as [terms1trunc terms1terms].
  apply IsLproposition_rel in terms2prop.
  destruct terms2prop as [terms2trunc terms2terms].
  assert (forall i j, 1 + 2*i =? 2*j = false) as oddneqeven.
  { intros. apply Nat.eqb_neq. intro abs.
    pose proof (Nat.odd_add_mul_2 1 i).
    rewrite abs, Nat.odd_1 in H.
    pose proof (Nat.odd_add_mul_2 0 j).
    rewrite Nat.add_0_l, H, Nat.odd_0 in H0. discriminate. } 
  assert (forall a b c, (a + b =? a + c) = (b =? c)) as canceladd.
  { intros. destruct (b =? c) eqn:des. apply Nat.eqb_eq in des.
    subst c. apply Nat.eqb_refl. apply Nat.eqb_neq. intro abs.
    apply Nat.add_cancel_l in abs.
    rewrite abs, Nat.eqb_refl in des. discriminate. } 
  induction numSubst.
  - intros _.
    rewrite ProgressiveSubstInit, ProgressiveSubstInit.
    apply LeqElim_rel_bumpvars. exact poslength. exact m1.
    rewrite LengthEvenVarsNat. apply EvenVarsTruncated.
    rewrite LengthEvenVarsNat. apply EvenVarsTruncated.
  - intros.
    assert (numSubst <= LengthNat terms1).
    { refine (Nat.le_trans _ _ _ _ H). apply le_S, Nat.le_refl. }
    specialize (IHnumSubst H0).
    apply (LforallIntro _ _ (m + 2 * numSubst)) in IHnumSubst.
    apply (LforallElim IsAxiom _ _ (CoordNat terms1 numSubst)) in IHnumSubst.
    2: apply terms1terms, H.
    rewrite Subst_implies, Subst_equiv, Subst_rel, Subst_rel in IHnumSubst.
    rewrite Subst_EqTerms in IHnumSubst.
    2: rewrite ProgressiveSubstLength.
    3: rewrite ProgressiveSubstLength.
    apply (LforallIntro _ _ (S m + 2 * numSubst)) in IHnumSubst.
    apply (LforallElim IsAxiom _ _ (CoordNat terms2 numSubst)) in IHnumSubst.
    rewrite Subst_implies, Subst_equiv, Subst_rel, Subst_rel in IHnumSubst.
    rewrite Subst_EqTerms in IHnumSubst.
    rewrite MapMapNat, MapMapNat in IHnumSubst.
    rewrite ProgressiveSubstIncr, ProgressiveSubstIncr in IHnumSubst.
    exact IHnumSubst.
    + rewrite LengthEvenVarsNat. exact H.
    + clear IHnumSubst. intros k H1 H2.
      rewrite LengthEvenVarsNat in H1.
      rewrite CoordEvenVarsNat, SubstTerm_var. 2: exact H1.
      replace (S m + 2 * k) with (m + (1+(2*k))).
      rewrite canceladd, oddneqeven.
      rewrite SubstTerm_var.
      replace (m + (1+(2*k))) with (S m + 2 * k).
      rewrite canceladd.
      destruct (2 * k =? 2 * numSubst) eqn:des. 2: reflexivity.
      exfalso. apply Nat.eqb_eq in des.
      apply Nat.mul_cancel_l in des. subst numSubst.
      exact (Nat.lt_irrefl k H2). discriminate.
      simpl. rewrite Nat.add_succ_r. reflexivity.
      simpl. rewrite Nat.add_succ_r. reflexivity.
    + clear IHnumSubst.
      rewrite CoordEvenVarsNat. 2: exact H.
      rewrite SubstTerm_var.
      replace (S m + 2 * numSubst) with (m + (1+(2*numSubst))).
      rewrite canceladd, oddneqeven.
      rewrite SubstTerm_var, Nat.eqb_refl. reflexivity.
      simpl. rewrite Nat.add_succ_r. reflexivity.
    + clear IHnumSubst. intros k H1 H2.
      rewrite LengthEvenVarsNat in H1.
      assert (MaxVarTerm (CoordNat terms2 k) < m + 2 * numSubst).
      { destruct numSubst. inversion H2.
        simpl. rewrite Nat.add_succ_r. apply le_n_S.
        rewrite samelength in H1.
        apply (Nat.le_trans _ _ _ (MaxVar_rel_lower r terms2 k H1)).
        apply (Nat.le_trans _ _ _ m3).
        rewrite <- (Nat.add_0_r m) at 1.
        apply Nat.add_le_mono_l, le_0_n. } 
      rewrite SubstTerm_nosubst, SubstTerm_nosubst. reflexivity.
      apply MaxVarTermDoesNotOccur. exact H3.
      apply terms2terms. rewrite <- samelength. exact H1.
      apply MaxVarTermDoesNotOccur.
      rewrite SubstTerm_nosubst. 
      apply (Nat.lt_le_trans _ _ _ H3).
      apply le_S, Nat.le_refl.
      apply MaxVarTermDoesNotOccur. exact H3.
      apply terms2terms. rewrite <- samelength. exact H1.
      apply IsSubstTermLterm.
      apply terms2terms. rewrite <- samelength. exact H1.
      apply terms1terms. exact H.
    + clear IHnumSubst. rewrite LengthEvenVarsNat. exact H.
    + clear IHnumSubst. intros k H1 H2.
      rewrite LengthEvenVarsNat in H1.
      rewrite CoordEvenVarsNat. 2: exact H1.
      rewrite SubstTerm_var, canceladd.
      destruct (2 * k =? 2 * numSubst) eqn:des.
      exfalso. apply Nat.eqb_eq in des.
      apply Nat.mul_cancel_l in des. subst numSubst.
      exact (Nat.lt_irrefl k H2). discriminate.
      rewrite SubstTerm_var.
      replace (S m + 2 * numSubst) with (m + (1+(2*numSubst))).
      rewrite canceladd, Nat.eqb_sym, oddneqeven. reflexivity.
      simpl. rewrite Nat.add_succ_r. reflexivity.
    + clear IHnumSubst. rewrite CoordEvenVarsNat. 2: exact H.
      rewrite SubstTerm_var, Nat.eqb_refl.
      rewrite SubstTerm_nosubst. reflexivity.
      apply MaxVarTermDoesNotOccur.
      simpl. apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_rel_lower r terms1 numSubst H)).
      apply (Nat.le_trans _ _ _ m2).
      rewrite <- (Nat.add_0_r m) at 1.
      apply Nat.add_le_mono_l, le_0_n.
      apply terms1terms. exact H.
    + clear IHnumSubst. intros k H1 H2.
      rewrite LengthEvenVarsNat in H1.
      assert (MaxVarTerm (CoordNat terms1 k) < m + 2 * numSubst).
      { destruct numSubst. inversion H2.
        simpl. rewrite Nat.add_succ_r. apply le_n_S.
        apply (Nat.le_trans _ _ _ (MaxVar_rel_lower r terms1 k H1)).
        apply (Nat.le_trans _ _ _ m2).
        rewrite <- (Nat.add_0_r m) at 1.
        apply Nat.add_le_mono_l, le_0_n. }
      rewrite SubstTerm_nosubst, SubstTerm_nosubst. reflexivity.
      apply MaxVarTermDoesNotOccur. exact H3.
      apply terms1terms. exact H1.
      rewrite SubstTerm_nosubst.
      apply MaxVarTermDoesNotOccur.
      apply (Nat.lt_le_trans _ _ _ H3). apply le_S, Nat.le_refl.
      apply terms1terms. exact H1.
      apply MaxVarTermDoesNotOccur. exact H3.
      apply terms1terms. exact H1.
    + clear IHnumSubst.
      rewrite LengthMapNat, ProgressiveSubstLength, LengthEvenVarsNat.
      destruct (LengthNat terms1). inversion H. apply Nat.le_refl.
    + clear IHnumSubst.
      rewrite LengthMapNat, ProgressiveSubstLength, LengthEvenVarsNat.
      destruct (LengthNat terms1). inversion H. apply Nat.le_refl.
    + apply terms2terms. rewrite <- samelength. exact H.
    + rewrite IsFreeForSubst_implies, IsFreeForSubst_EqTerms.
      rewrite Bool.andb_true_l.
      rewrite IsFreeForSubst_equiv, IsFreeForSubst_rel, IsFreeForSubst_rel.
      reflexivity.
      unfold Lrel. rewrite CoordConsHeadNat. reflexivity.
      unfold Lrel. rewrite CoordConsHeadNat. reflexivity.
    + rewrite LengthEvenVarsNat.
      destruct (LengthNat terms1). inversion H. apply Nat.le_refl.
    + rewrite LengthEvenVarsNat.
      destruct (LengthNat terms1). inversion H. apply Nat.le_refl.
    + rewrite IsFreeForSubst_implies, IsFreeForSubst_EqTerms.
      rewrite Bool.andb_true_l.
      rewrite IsFreeForSubst_equiv, IsFreeForSubst_rel, IsFreeForSubst_rel.
      reflexivity.
      unfold Lrel. rewrite CoordConsHeadNat. reflexivity.
      unfold Lrel. rewrite CoordConsHeadNat. reflexivity.
Qed.

Lemma LeqElim_rel : forall IsAxiom (r terms1 terms2:nat),
    LengthNat terms1 = LengthNat terms2
    -> 1 <= LengthNat terms1
    -> NthTailNat terms1 (LengthNat terms1) = 0
    -> NthTailNat terms2 (LengthNat terms2) = 0
    -> (forall k, k < LengthNat terms1 -> IsLterm (CoordNat terms1 k) = true)
    -> (forall k, k < LengthNat terms2 -> IsLterm (CoordNat terms2 k) = true)
    -> IsProved IsAxiom (Limplies (EqTerms terms1 terms2 (pred (LengthNat terms1)))
                                 (Lequiv (Lrel r terms1) (Lrel r terms2))).
Proof.
  intros IsAxiom r terms1 terms2 samelength poslength terms1trunc terms2trunc
  terms1terms terms2terms.
  pose (Nat.max (2 * LengthNat terms1)
                (Nat.max (MaxVar (Lrel r terms1)) (MaxVar (Lrel r terms2))))
    as m.
  assert (IsLproposition (Lrel r terms1) = true) as terms1prop.
  { apply IsLproposition_rel. split; assumption. }
  assert (IsLproposition (Lrel r terms2) = true) as terms2prop.
  { apply IsLproposition_rel. split; assumption. }
  assert (2 * LengthNat terms1 <= m) by apply Nat.le_max_l.
  assert (MaxVar (Lrel r terms1) <= m).
  { refine (Nat.le_trans _ _ _ _ (Nat.le_max_r _ _)). apply Nat.le_max_l. }
  assert (MaxVar (Lrel r terms2) <= m).
  refine (Nat.le_trans _ _ _ _ (Nat.le_max_r _ _)).
  apply Nat.le_max_r.
  pose proof (LeqElim_rel_aux IsAxiom r terms1 terms2 m samelength
                              poslength terms1prop terms2prop H H0 H1
                              (LengthNat terms1) (Nat.le_refl _)) as aux.
  rewrite ProgressiveSubstComplete, ProgressiveSubstComplete in aux.
  exact aux. rewrite LengthEvenVarsNat.
  apply Nat.le_refl.
  rewrite LengthEvenVarsNat. exact samelength. exact terms2trunc.
  rewrite LengthEvenVarsNat. apply Nat.le_refl.
  rewrite LengthEvenVarsNat. reflexivity. exact terms1trunc.
Qed.

Lemma LeqElim_rel2 : forall IsAxiom (r t s u v:nat),
    IsProved IsAxiom (Leq t s)
    -> IsProved IsAxiom (Leq u v)
    -> IsProved IsAxiom (Lequiv (Lrel2 r t u) (Lrel2 r s v)).
Proof.
  intros.
  pose proof (IsProvedIsLproposition IsAxiom _ H) as tsterm.
  pose proof (IsProvedIsLproposition IsAxiom _ H0) as uvterm.
  unfold Leq in tsterm. rewrite IsLproposition_rel2 in tsterm.
  unfold Leq in uvterm. rewrite IsLproposition_rel2 in uvterm.
  apply andb_prop in tsterm. destruct tsterm as [tterm sterm].
  apply andb_prop in uvterm. destruct uvterm as [uterm vterm].
  apply (LimpliesElim _ (Land (Leq t s) (Leq u v))).
  2: apply LandIntro; assumption. 
  pose proof (LeqElim_rel IsAxiom r (ConsNat t (ConsNat u NilNat))
                          (ConsNat s (ConsNat v NilNat))) as H1.
  do 4 rewrite LengthConsNat in H1.
  specialize (H1 eq_refl). simpl in H1.
  do 2 rewrite CoordConsTailNat in H1.
  rewrite LengthNilNat in H1. simpl in H1.
  do 4 rewrite CoordConsHeadNat in H1. apply H1.
  apply le_S, Nat.le_refl.
  rewrite TailConsNat, TailConsNat. reflexivity.
  rewrite TailConsNat, TailConsNat. reflexivity.
  intros. destruct k. rewrite CoordConsHeadNat. exact tterm.
  destruct k. rewrite CoordConsTailNat, CoordConsHeadNat. exact uterm.
  exfalso. apply le_S_n, le_S_n in H2. inversion H2.
  intros. destruct k. rewrite CoordConsHeadNat. exact sterm.
  destruct k. rewrite CoordConsTailNat, CoordConsHeadNat. exact vterm.
  exfalso. apply le_S_n, le_S_n in H2. inversion H2.
Qed.

Lemma RemoveRedundantHypothesis : forall IsAxiom h p q,
    IsProved IsAxiom (Limplies h (Limplies p q))
    -> IsProved IsAxiom (Limplies h p)
    -> IsProved IsAxiom (Limplies h q).
Proof.
  intros.
  pose proof (IsProvedIsLproposition _ _ H) as hpqprop.
  rewrite IsLproposition_implies, IsLproposition_implies in hpqprop.
  apply andb_prop in hpqprop. destruct hpqprop as [hprop pqprop].
  apply andb_prop in pqprop. destruct pqprop as [pprop qprop].
  apply (LimpliesElim _ (Limplies h p)). 2: exact H0.
  apply (LimpliesElim _ (Limplies h (Limplies p q))). 2: exact H.
  apply IsProvedPropAx, Ax2IsPropAx, Ax2IsAx2; assumption.
Qed.

Lemma DropHypothesis : forall IsAxiom p q,
    IsLproposition p = true
    -> IsProved IsAxiom q
    -> IsProved IsAxiom (Limplies p q).
Proof.
  intros.
  apply (LimpliesElim _ q).
  apply IsProvedPropAx, Ax1IsPropAx, Ax1IsAx1.
  exact (IsProvedIsLproposition IsAxiom _ H0). exact H. exact H0.
Qed.

Lemma LimpliesElim_impl : forall IsAxiom (f g:nat),
    IsLproposition g = true
    -> IsProved IsAxiom f
    -> IsProved IsAxiom (Limplies (Limplies f g) g).
Proof.
  intros.
  pose proof (IsProvedIsLproposition _ _ H0) as fprop.
  refine (LimpliesElim _ f _ _ H0).
  apply PullHypothesis.
  apply (LimpliesTrans _ _ (Land (Limplies f g) f)).
  apply LandIntroHyp.
  apply LandElim2_impl. exact fprop.
  rewrite IsLproposition_implies, fprop. exact H.
  apply LandElim1_impl. exact fprop.
  rewrite IsLproposition_implies, fprop. exact H.
  apply PushHypothesis. apply LimpliesRefl.
  rewrite IsLproposition_implies, fprop. exact H.
Qed.

Lemma LorElim : forall IsAxiom a b c,
    IsProved IsAxiom (Limplies a c)
    -> IsProved IsAxiom (Limplies b c)
    -> IsProved IsAxiom (Limplies (Lor a b) c).
Proof.
  intros.
  pose proof (IsProvedIsLproposition IsAxiom _ H).
  pose proof (IsProvedIsLproposition IsAxiom _ H0).
  rewrite IsLproposition_implies in H1.
  apply andb_prop in H1. destruct H1.
  rewrite IsLproposition_implies in H2.
  apply andb_prop in H2. destruct H2 as [H2 _].
  apply (LimpliesElim _ (Limplies b c)). 2: exact H0.
  apply (LimpliesElim _ (Limplies a c)). 2: exact H.
  apply IsProvedPropAx, Ax11IsPropAx, Ax11IsAx11.
  apply H1. apply H2. apply H3.
Qed.

Lemma LorElimHyp : forall IsAxiom h a b c,
    IsProved IsAxiom (Limplies (Land h a) c)
    -> IsProved IsAxiom (Limplies (Land h b) c)
    -> IsProved IsAxiom (Limplies (Land h (Lor a b)) c).
Proof.
  intros.
  pose proof (IsProvedIsLproposition IsAxiom _ H).
  pose proof (IsProvedIsLproposition IsAxiom _ H0).
  rewrite IsLproposition_implies, IsLproposition_and in H1.
  apply andb_prop in H1. destruct H1. apply andb_prop in H1.
  rewrite IsLproposition_implies, IsLproposition_and in H2.
  apply andb_prop in H2. destruct H2 as [H2 _].
  apply andb_prop in H2.
  assert (IsProved IsAxiom (Limplies (Limplies a c)
                                     (Limplies (Limplies b c) (Limplies (Lor a b) c)))).
  { apply IsProvedPropAx, Ax11IsPropAx, Ax11IsAx11.
    apply H1. apply H2. apply H3. }
  apply PullHypothesis in H.
  pose proof (LimpliesTrans _ _ _ _ H H4) as H5. clear H4.
  apply PullHypothesis in H0.
  pose proof (RemoveRedundantHypothesis _ _ _ _ H5 H0).
  apply PushHypothesis. exact H4.
Qed.

Lemma LexistsElim_impl : forall IsAxiom v p q,
    VarOccursFreeInFormula v q = false
    -> IsProved IsAxiom (Lforall v (Limplies p q))
    -> IsProved IsAxiom (Limplies (Lexists v p) q).
Proof.
  intros.
  pose proof (IsProvedIsLproposition _ _ H0) as pqprop.
  rewrite IsLproposition_forall, IsLproposition_implies in pqprop.
  apply andb_prop in pqprop. destruct pqprop as [pprop qprop].
  assert (IsProved IsAxiom
                   (Limplies (Lexists v p) (Limplies (Lforall v (Limplies p q)) q))).
  { exists (ConsNat (Limplies (Lexists v p)
                       (Limplies (Lforall v (Limplies p q)) q)) NilNat).
    apply andb_true_intro; split.
    apply andb_true_intro; split.
    rewrite CoordConsHeadNat. apply Nat.eqb_refl.
    rewrite LengthConsNat. apply Nat.leb_refl.
    rewrite LengthConsNat.
    simpl.
    rewrite CoordConsHeadNat, TailConsNat.
    apply andb_true_intro; split. 2: reflexivity.
    apply Bool.orb_true_intro. right.
    apply Bool.orb_true_intro. right.
    apply ExistsElimIsExistsElim. apply pprop. apply qprop. exact H. }
  apply PushHypothesis in H1.
  refine (LimpliesTrans _ _ _ _ _ H1). clear H1.
  apply LandIntroHyp. apply LimpliesRefl.
  rewrite IsLproposition_exists. exact pprop.
  apply DropHypothesis. 2: exact H0.
  rewrite IsLproposition_exists. exact pprop.
Qed.

Lemma LexistsElimHyp : forall IsAxiom h v p q,
    VarOccursFreeInFormula v q = false
    -> IsProved IsAxiom (Limplies h (Lforall v (Limplies p q)))
    -> IsProved IsAxiom (Limplies (Land h (Lexists v p)) q).
Proof.
  intros.
  pose proof (IsProvedIsLproposition _ _ H0).
  rewrite IsLproposition_implies, IsLproposition_forall, IsLproposition_implies
    in H1.
  apply andb_prop in H1. destruct H1 as [hprop pprop].
  apply andb_prop in pprop.
  assert (IsProved IsAxiom (Limplies (Lexists v p)
                                     (Limplies (Lforall v (Limplies p q)) q)))
    as exelim.
  { exists (ConsNat (Limplies (Lexists v p)
                             (Limplies (Lforall v (Limplies p q)) q)) NilNat).
    apply andb_true_intro; split.
    apply andb_true_intro; split.
    rewrite CoordConsHeadNat. apply Nat.eqb_refl.
    rewrite LengthConsNat. apply Nat.leb_refl.
    rewrite LengthConsNat.
    simpl.
    rewrite CoordConsHeadNat, TailConsNat.
    apply andb_true_intro; split. 2: reflexivity.
    apply Bool.orb_true_intro. right.
    apply Bool.orb_true_intro. right.
    apply ExistsElimIsExistsElim. apply pprop. apply pprop. exact H. }
  apply PushHypothesis.
  apply (LimpliesTrans _ _ _ _ H0).
  clear H0 hprop h.
  apply PullHypothesis.
  apply PushHypothesis in exelim. 
  refine (LimpliesTrans _ _ _ _ _ exelim).
  apply LandIntroHyp.
  apply LandElim2_impl.
  rewrite IsLproposition_forall, IsLproposition_implies.
  apply andb_true_intro; split; apply pprop.
  rewrite IsLproposition_exists. apply pprop.
  apply LandElim1_impl.
  rewrite IsLproposition_forall, IsLproposition_implies.
  apply andb_true_intro; split; apply pprop.
  rewrite IsLproposition_exists. apply pprop.
Qed.

Lemma LeqElim_op_bumpvars : forall IsAxiom (o arity n:nat),
    1 <= arity ->
    2 * arity <= n ->
    IsProved IsAxiom (Limplies (EqTerms (EvenVars n arity)
                                        (EvenVars (S n) arity) (pred arity))
                               (Leq (Lop o (EvenVars n arity))
                                    (Lop o (EvenVars (S n) arity)))).
Proof.
  assert (forall i j, 1 + 2*i =? 2*j = false) as oddneqeven.
  { intros. apply Nat.eqb_neq. intro abs.
    pose proof (Nat.odd_add_mul_2 1 i).
    rewrite abs, Nat.odd_1 in H.
    pose proof (Nat.odd_add_mul_2 0 j).
    rewrite Nat.add_0_l, H, Nat.odd_0 in H0. discriminate. }
  assert (forall i o terms1 terms2 u v,
             IsFreeForSubst u v (Limplies (EqTerms terms1 terms2 i)
                                          (Leq (Lop o terms1) (Lop o terms2))) = true)
    as allfree.
  { intros.
    rewrite IsFreeForSubst_implies, IsFreeForSubst_EqTerms.
    simpl. unfold Leq. rewrite IsFreeForSubst_rel2. reflexivity. }
  assert (forall numSubst IsAxiom o arity n,
             1 <= arity ->
             2 * arity <= n ->
             numSubst <= arity ->
             IsProved IsAxiom (Limplies (EqTerms (ProgressiveSubst
                                                    (EvenVars 0 arity)
                                                    (EvenVars n arity)
                                                    numSubst)
                                                 (ProgressiveSubst
                                                    (EvenVars 1 arity)
                                                    (EvenVars (S n) arity)
                                                    numSubst)
                                                 (pred arity))
                                        (Leq (Lop o (ProgressiveSubst
                                                    (EvenVars 0 arity)
                                                    (EvenVars n arity)
                                                    numSubst))
                                                (Lop o (ProgressiveSubst
                                                    (EvenVars 1 arity)
                                                    (EvenVars (S n) arity)
                                                    numSubst))))).
  induction numSubst.
  - intros. simpl. apply IsProvedEqAx.
    apply Bool.orb_true_intro; left.
    apply Bool.orb_true_intro; right.
    apply andb_true_intro; split.
    apply andb_true_intro; split.
    apply andb_true_intro; split.
    apply LimpliesIsImplies. unfold Leq, Lrel2, Lrel.
    rewrite CoordNat_implies_2.
    do 2 rewrite CoordConsTailNat.
    rewrite CoordConsHeadNat.
    rewrite LengthLop, ProgressiveSubstLength.
    destruct arity. inversion H.
    rewrite LengthEvenVarsNat. reflexivity.
    rewrite CoordNat_implies_1, CoordNat_implies_2.
    unfold Leq, Lrel2.
    rewrite CoordNat_rel. rewrite CoordConsHeadNat, LengthLop, ProgressiveSubstLength.
    simpl. rewrite Nat.sub_0_r.
    rewrite ProgressiveSubstInit, ProgressiveSubstInit, LengthEvenVarsNat.
    apply Nat.eqb_refl.
    rewrite LengthEvenVarsNat. apply EvenVarsTruncated.
    rewrite LengthEvenVarsNat. apply EvenVarsTruncated.
    rewrite CoordNat_implies_2. unfold Leq, Lrel2.
    rewrite CoordNat_rel. rewrite CoordConsHeadNat, LengthLop.
    rewrite ProgressiveSubstLength. unfold Lop.
    rewrite CoordConsTailNat, CoordConsHeadNat.
    rewrite ProgressiveSubstInit, ProgressiveSubstInit, LengthEvenVarsNat.
    replace (2 + arity - 2) with arity. apply Nat.eqb_refl.
    simpl. rewrite Nat.sub_0_r. reflexivity.
    rewrite LengthEvenVarsNat. apply EvenVarsTruncated.
    rewrite LengthEvenVarsNat. apply EvenVarsTruncated.
  - intros. specialize (IHnumSubst IsAxiom o arity n H H0).
    apply (LforallIntro _ _ (2 * numSubst)) in IHnumSubst.
    apply (LforallElim IsAxiom _ _ (Lvar (n+2*numSubst))) in IHnumSubst.
    2: apply IsLterm_var. 2: apply allfree.
    rewrite Subst_implies, Subst_eq, SubstTerm_op,
      Subst_EqTerms, SubstTerm_op in IHnumSubst.
    2: rewrite ProgressiveSubstLength.
    3: rewrite ProgressiveSubstLength.
    apply (LforallIntro _ _ (1 + 2 * numSubst)) in IHnumSubst.
    apply (LforallElim IsAxiom _ _ (Lvar (S n+2*numSubst))) in IHnumSubst.
    2: apply IsLterm_var. 2: apply allfree.
    rewrite Subst_implies, Subst_eq,
      SubstTerm_op, SubstTerm_op in IHnumSubst.
    rewrite Subst_EqTerms in IHnumSubst.
    rewrite MapMapNat, MapMapNat in IHnumSubst.
    rewrite ProgressiveSubstIncr, ProgressiveSubstIncr in IHnumSubst.
    exact IHnumSubst.
    + rewrite LengthEvenVarsNat. exact H1.
    + clear IHnumSubst. intros k H2 H3.
      rewrite CoordEvenVarsNat.
      rewrite SubstTerm_var, oddneqeven, SubstTerm_var.
      destruct (1 + 2 * k =? 1 + 2 * numSubst) eqn:des. 2: reflexivity.
      exfalso. apply Nat.eqb_eq in des. 
      apply (Nat.lt_irrefl numSubst).
      apply (Nat.lt_le_trans _ _ _ H3).
      apply (Nat.mul_le_mono_pos_l  _ _ 2). auto.
      apply (Nat.add_le_mono_l _ _ 1). rewrite des. apply Nat.le_refl.
      rewrite LengthEvenVarsNat in H2. exact H2.
    + clear IHnumSubst.
      rewrite CoordEvenVarsNat, CoordEvenVarsNat.
      rewrite SubstTerm_var, oddneqeven, SubstTerm_var, Nat.eqb_refl.
      reflexivity. exact H1. exact H1.
    + clear IHnumSubst. intros k H2 H3.
      rewrite LengthEvenVarsNat in H2.
      rewrite CoordEvenVarsNat, SubstTerm_var. 2: exact H2.
      destruct (S n + 2 * k =? 2 * numSubst) eqn:des.
      apply Nat.eqb_eq in des.
      exfalso.
      apply (Nat.lt_irrefl numSubst).
      apply (Nat.lt_le_trans _ _ _ H1).
      apply (Nat.mul_le_mono_pos_l  _ _ 2). auto.
      apply (Nat.le_trans _ _ _ H0). rewrite <- des. 
      simpl. apply le_S.
      rewrite <- (Nat.add_0_r n) at 1.
      apply Nat.add_le_mono_l, le_0_n.
      rewrite SubstTerm_var.
      destruct (S n + 2 * k =? 1 + 2 * numSubst) eqn:des2.
      2: reflexivity. exfalso. apply Nat.eqb_eq in des2.
      apply (Nat.lt_irrefl numSubst).
      apply (Nat.lt_le_trans _ _ _ H1).
      apply (Nat.mul_le_mono_pos_l  _ _ 2). auto.
      apply (Nat.le_trans _ _ _ H0).
      apply (Nat.add_le_mono_l _ _ 1). rewrite <- des2.
      simpl. apply le_n_S.
      rewrite <- (Nat.add_0_r n) at 1.
      apply Nat.add_le_mono_l, le_0_n.
    + rewrite LengthEvenVarsNat. exact H1.
    + clear IHnumSubst. intros k H2 H3.
      rewrite LengthEvenVarsNat in H2.
      rewrite CoordEvenVarsNat, SubstTerm_var, Nat.add_0_l. 2: exact H2.
      destruct (2 * k =? 2 * numSubst) eqn:des. exfalso.
      apply Nat.eqb_eq in des. apply Nat.mul_cancel_l in des. 2: discriminate.
      rewrite des in H3. exact (Nat.lt_irrefl _ H3).
      rewrite SubstTerm_var, Nat.eqb_sym, oddneqeven. reflexivity.
    + clear IHnumSubst.
      rewrite CoordEvenVarsNat, SubstTerm_var, Nat.eqb_refl, SubstTerm_var.
      2: exact H1.
      rewrite CoordEvenVarsNat. 2: exact H1.
      destruct (n + 2 * numSubst =? 1 + 2 * numSubst) eqn:des. 2: reflexivity.
      exfalso. apply Nat.eqb_eq in des.
      apply Nat.add_cancel_r in des. subst n.
      destruct arity. inversion H. simpl in H0.
      apply le_S_n in H0. rewrite Nat.add_succ_r in H0. inversion H0.
    + clear IHnumSubst. intros k H2 H3.
      rewrite LengthEvenVarsNat in H2.
      rewrite CoordEvenVarsNat. 2: exact H2.
      rewrite SubstTerm_var.
      destruct (n + 2 * k =? 2 * numSubst) eqn:des.
      apply Nat.eqb_eq in des. exfalso.
      apply (Nat.lt_irrefl numSubst).
      apply (Nat.lt_le_trans _ _ _ H1).
      apply (Nat.mul_le_mono_pos_l  _ _ 2). auto.
      apply (Nat.le_trans _ _ _ H0). rewrite <- des.
      rewrite <- (Nat.add_0_r n) at 1.
      apply Nat.add_le_mono_l, le_0_n.
      rewrite SubstTerm_var.
      destruct (n + 2 * k =? 1 + 2 * numSubst) eqn:des2. 2: reflexivity.
      exfalso. apply Nat.eqb_eq in des2.
      apply (Nat.lt_irrefl numSubst).
      apply (Nat.lt_le_trans _ _ _ H1).
      apply (Nat.mul_le_mono_pos_l  _ _ 2). auto.
      apply (Nat.le_trans _ _ _ H0).
      apply (Nat.add_le_mono_l _ _ 1). rewrite <- des2. 
      rewrite Nat.add_comm.
      apply Nat.add_le_mono_l. 
      destruct k. 2: apply le_n_S, le_0_n.
      exfalso. rewrite Nat.mul_0_r, Nat.add_0_r in des2.
      clear des. subst n.
      apply (Nat.div_le_mono _ _ 2) in H0. 2: discriminate.
      rewrite Nat.mul_comm, Nat.div_mul in H0. 2: discriminate.
      rewrite Nat.mul_comm, Nat.add_comm, Nat.div_add_l in H0.
      simpl in H0. rewrite Nat.add_0_r in H0.
      apply (Nat.lt_irrefl numSubst).
      exact (Nat.lt_le_trans _ _ _ H1 H0). discriminate.
    + clear IHnumSubst. rewrite LengthMapNat, ProgressiveSubstLength.
      destruct arity. inversion H.
      rewrite LengthEvenVarsNat.
      apply Nat.le_refl.
    + clear IHnumSubst. rewrite LengthMapNat, ProgressiveSubstLength.
      destruct arity. inversion H.
      rewrite LengthEvenVarsNat. apply Nat.le_refl.
    + rewrite LengthEvenVarsNat.
      destruct arity. inversion H. apply Nat.le_refl.
    + rewrite LengthEvenVarsNat.
      destruct arity. inversion H. apply Nat.le_refl.
    + refine (Nat.le_trans _ _ _ _ H1). apply le_S, Nat.le_refl.
  - intros. specialize (H arity IsAxiom o arity n H0 H1 (Nat.le_refl _)).
    rewrite ProgressiveSubstComplete, ProgressiveSubstComplete in H.
    exact H. rewrite LengthEvenVarsNat.
    apply Nat.le_refl.
    rewrite LengthEvenVarsNat, LengthEvenVarsNat. reflexivity.
    rewrite LengthEvenVarsNat. apply EvenVarsTruncated.
    rewrite LengthEvenVarsNat. apply Nat.le_refl.
    rewrite LengthEvenVarsNat, LengthEvenVarsNat. reflexivity.
    rewrite LengthEvenVarsNat. apply EvenVarsTruncated. 
Qed.

Lemma LeqElim_vars_op : forall IsAxiom (o terms1 terms2 : nat),
    LengthNat terms1 = LengthNat terms2
    -> 1 <= LengthNat terms1
    -> NthTailNat terms1 (LengthNat terms1) = 0
    -> NthTailNat terms2 (LengthNat terms2) = 0
    -> (forall k, k < LengthNat terms1 -> IsLterm (CoordNat terms1 k) = true)
    -> (forall k, k < LengthNat terms2 -> IsLterm (CoordNat terms2 k) = true)
    -> IsProved IsAxiom
               (Limplies (EqTerms terms1 terms2 (pred (LengthNat terms1)))
                         (Leq (Lop o terms1) (Lop o terms2))).
Proof.
  intros IsAxiom o terms1 terms2 samelength poslength terms1trunc terms2trunc
  terms1terms terms2terms.
  pose (Nat.max (2 * LengthNat terms1)
                (Nat.max (MaxVar (Lrel 0 terms1)) (MaxVar (Lrel 0 terms2))))
    as m.
  assert (forall i j, 1 + 2*i =? 2*j = false) as oddneqeven.
  { intros. apply Nat.eqb_neq. intro abs.
    pose proof (Nat.odd_add_mul_2 1 i).
    rewrite abs, Nat.odd_1 in H.
    pose proof (Nat.odd_add_mul_2 0 j).
    rewrite Nat.add_0_l, H, Nat.odd_0 in H0. discriminate. } 
  assert (forall a b c, (a + b =? a + c) = (b =? c)) as canceladd.
  { intros. destruct (b =? c) eqn:des. apply Nat.eqb_eq in des.
    subst c. apply Nat.eqb_refl. apply Nat.eqb_neq. intro abs.
    apply Nat.add_cancel_l in abs.
    rewrite abs, Nat.eqb_refl in des. discriminate. }
  assert (forall numSubst,
             numSubst <= LengthNat terms1 ->
             IsProved IsAxiom (Limplies (EqTerms (ProgressiveSubst
                                                    (EvenVars m (LengthNat terms1))
                                                    terms1 numSubst)
                                                 (ProgressiveSubst
                                                    (EvenVars (S m) (LengthNat terms1))
                                                    terms2 numSubst)
                                                 (pred (LengthNat terms1)))
                                        (Leq (Lop o (ProgressiveSubst
                                                    (EvenVars m (LengthNat terms1))
                                                    terms1 numSubst))
                                                (Lop o (ProgressiveSubst
                                                    (EvenVars (S m) (LengthNat terms1))
                                                    terms2 numSubst))))).
  induction numSubst.
  - intros _.
    rewrite ProgressiveSubstInit, ProgressiveSubstInit.
    apply LeqElim_op_bumpvars. exact poslength. apply Nat.le_max_l.
    rewrite LengthEvenVarsNat. apply EvenVarsTruncated.
    rewrite LengthEvenVarsNat. apply EvenVarsTruncated.
  - intros.
    assert (numSubst <= LengthNat terms1).
    refine (Nat.le_trans _ _ _ _ H). apply le_S, Nat.le_refl.
    specialize (IHnumSubst H0).
    apply (LforallIntro _ _ (m + 2 * numSubst)) in IHnumSubst.
    apply (LforallElim IsAxiom _ _ (CoordNat terms1 numSubst)) in IHnumSubst.
    2: apply terms1terms, H.
    rewrite Subst_implies, Subst_eq,
      SubstTerm_op, SubstTerm_op in IHnumSubst.
    rewrite Subst_EqTerms in IHnumSubst.
    2: rewrite ProgressiveSubstLength.
    3: rewrite ProgressiveSubstLength.
    apply (LforallIntro _ _ (S m + 2 * numSubst)) in IHnumSubst.
    apply (LforallElim IsAxiom _ _ (CoordNat terms2 numSubst)) in IHnumSubst.
    rewrite Subst_implies, Subst_eq,
      SubstTerm_op, SubstTerm_op in IHnumSubst.
    rewrite Subst_EqTerms in IHnumSubst.
    rewrite MapMapNat, MapMapNat in IHnumSubst.
    rewrite ProgressiveSubstIncr, ProgressiveSubstIncr in IHnumSubst.
    exact IHnumSubst.
    + rewrite LengthEvenVarsNat. exact H.
    + clear IHnumSubst. intros k H1 H2.
      rewrite LengthEvenVarsNat in H1.
      rewrite CoordEvenVarsNat, SubstTerm_var. 2: exact H1.
      replace (S m + 2 * k) with (m + (1+(2*k))).
      rewrite canceladd, oddneqeven.
      rewrite SubstTerm_var.
      replace (m + (1+(2*k))) with (S m + 2 * k).
      rewrite canceladd.
      destruct (2 * k =? 2 * numSubst) eqn:des. 2: reflexivity.
      exfalso. apply Nat.eqb_eq in des.
      apply Nat.mul_cancel_l in des. subst numSubst.
      exact (Nat.lt_irrefl k H2). discriminate.
      simpl. rewrite Nat.add_succ_r. reflexivity.
      simpl. rewrite Nat.add_succ_r. reflexivity.
    + clear IHnumSubst.
      rewrite CoordEvenVarsNat. 2: exact H.
      rewrite SubstTerm_var.
      replace (S m + 2 * numSubst) with (m + (1+(2*numSubst))).
      rewrite canceladd, oddneqeven.
      rewrite SubstTerm_var, Nat.eqb_refl. reflexivity.
      simpl. rewrite Nat.add_succ_r. reflexivity.
    + clear IHnumSubst. intros k H1 H2.
      rewrite LengthEvenVarsNat in H1.
      assert (MaxVarTerm (CoordNat terms2 k) < m + 2 * numSubst).
      { destruct numSubst. inversion H2.
        simpl. rewrite Nat.add_succ_r. apply le_n_S.
        rewrite samelength in H1.
        apply (Nat.le_trans _ _ _ (MaxVar_rel_lower 0 terms2 k H1)).
        apply (Nat.le_trans _ (m+0)).
        rewrite Nat.add_0_r.
        unfold m. rewrite Nat.max_assoc. apply Nat.le_max_r.
        apply Nat.add_le_mono_l, le_0_n. } 
      rewrite SubstTerm_nosubst, SubstTerm_nosubst. reflexivity.
      apply MaxVarTermDoesNotOccur. exact H3.
      apply terms2terms. rewrite <- samelength. exact H1.
      apply MaxVarTermDoesNotOccur.
      rewrite SubstTerm_nosubst. 
      apply (Nat.lt_le_trans _ _ _ H3).
      apply le_S, Nat.le_refl.
      apply MaxVarTermDoesNotOccur. exact H3.
      apply terms2terms. rewrite <- samelength. exact H1.
      apply IsSubstTermLterm.
      apply terms2terms. rewrite <- samelength. exact H1.
      apply terms1terms. exact H.
    + clear IHnumSubst. rewrite LengthEvenVarsNat. exact H.
    + clear IHnumSubst. intros k H1 H2.
      rewrite LengthEvenVarsNat in H1.
      rewrite CoordEvenVarsNat. 2: exact H1.
      rewrite SubstTerm_var, canceladd.
      destruct (2 * k =? 2 * numSubst) eqn:des.
      exfalso. apply Nat.eqb_eq in des.
      apply Nat.mul_cancel_l in des. subst numSubst.
      exact (Nat.lt_irrefl k H2). discriminate.
      rewrite SubstTerm_var.
      replace (S m + 2 * numSubst) with (m + (1+(2*numSubst))).
      rewrite canceladd, Nat.eqb_sym, oddneqeven. reflexivity.
      simpl. rewrite Nat.add_succ_r. reflexivity.
    + clear IHnumSubst. rewrite CoordEvenVarsNat. 2: exact H.
      rewrite SubstTerm_var, Nat.eqb_refl.
      rewrite SubstTerm_nosubst. reflexivity.
      apply MaxVarTermDoesNotOccur.
      simpl. apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_rel_lower 0 terms1 numSubst H)).
      apply (Nat.le_trans _ (m+0)).
      rewrite Nat.add_0_r. unfold m.
      rewrite Nat.max_comm, <- Nat.max_assoc. apply Nat.le_max_l.
      apply Nat.add_le_mono_l, le_0_n.
      apply terms1terms. exact H.
    + clear IHnumSubst. intros k H1 H2.
      rewrite LengthEvenVarsNat in H1.
      assert (MaxVarTerm (CoordNat terms1 k) < m + 2 * numSubst).
      { destruct numSubst. inversion H2.
        simpl. rewrite Nat.add_succ_r. apply le_n_S.
        apply (Nat.le_trans _ _ _ (MaxVar_rel_lower 0 terms1 k H1)).
        apply (Nat.le_trans _ (m+0)).
        rewrite Nat.add_0_r.
        unfold m. rewrite Nat.max_comm, <- Nat.max_assoc. apply Nat.le_max_l.
        apply Nat.add_le_mono_l, le_0_n. }
      rewrite SubstTerm_nosubst, SubstTerm_nosubst. reflexivity.
      apply MaxVarTermDoesNotOccur. exact H3.
      apply terms1terms. exact H1.
      rewrite SubstTerm_nosubst.
      apply MaxVarTermDoesNotOccur.
      apply (Nat.lt_le_trans _ _ _ H3). apply le_S, Nat.le_refl.
      apply terms1terms. exact H1.
      apply MaxVarTermDoesNotOccur. exact H3.
      apply terms1terms. exact H1.
    + clear IHnumSubst.
      rewrite LengthMapNat, ProgressiveSubstLength, LengthEvenVarsNat.
      destruct (LengthNat terms1). inversion H. apply Nat.le_refl.
    + clear IHnumSubst.
      rewrite LengthMapNat, ProgressiveSubstLength, LengthEvenVarsNat.
      destruct (LengthNat terms1). inversion H. apply Nat.le_refl.
    + apply terms2terms. rewrite <- samelength. exact H.
    + rewrite IsFreeForSubst_implies, IsFreeForSubst_EqTerms.
      rewrite Bool.andb_true_l. unfold Leq.
      rewrite IsFreeForSubst_rel2. reflexivity.
    + rewrite LengthEvenVarsNat.
      destruct (LengthNat terms1). inversion H. apply Nat.le_refl.
    + rewrite LengthEvenVarsNat.
      destruct (LengthNat terms1). inversion H. apply Nat.le_refl.
    + rewrite IsFreeForSubst_implies, IsFreeForSubst_EqTerms.
      rewrite Bool.andb_true_l. unfold Leq.
      rewrite IsFreeForSubst_rel2.
      reflexivity.
  - specialize (H (LengthNat terms1) (Nat.le_refl _)).
    rewrite ProgressiveSubstComplete, ProgressiveSubstComplete in H.
    exact H. rewrite LengthEvenVarsNat.
    apply Nat.le_refl.
    rewrite LengthEvenVarsNat. exact samelength. exact terms2trunc.
    rewrite LengthEvenVarsNat. apply Nat.le_refl.
    rewrite LengthEvenVarsNat. reflexivity. exact terms1trunc.
Qed.

Lemma LeqElim_op1 : forall IsAxiom (o t s : nat),
    IsProved IsAxiom (Leq t s)
    -> IsProved IsAxiom (Leq (Lop1 o t) (Lop1 o s)).
Proof.
  intros.
  pose proof (IsProvedIsLproposition IsAxiom _ H) as tsterm.
  unfold Leq in tsterm. rewrite IsLproposition_rel2 in tsterm.
  apply andb_prop in tsterm. destruct tsterm as [tterm sterm].
  apply (LimpliesElim _ (Leq t s)). 2: exact H. clear H.
  pose proof (LeqElim_vars_op IsAxiom o (ConsNat t NilNat) (ConsNat s NilNat)).
  rewrite LengthConsNat, LengthConsNat in H.
  specialize (H eq_refl). simpl in H.
  rewrite LengthNilNat in H. simpl in H.
  rewrite CoordConsHeadNat, CoordConsHeadNat in H. apply H.
  apply le_n_S, le_0_n.
  rewrite TailConsNat. reflexivity.
  rewrite TailConsNat. reflexivity.
  intros k H0. destruct k. rewrite CoordConsHeadNat. exact tterm.
  exfalso. apply le_S_n in H0. inversion H0.
  intros k H0. destruct k. rewrite CoordConsHeadNat. exact sterm.
  exfalso. apply le_S_n in H0. inversion H0. 
Qed.

Lemma LeqElim_op2 : forall IsAxiom (o t s u v : nat),
    IsProved IsAxiom (Leq t s)
    -> IsProved IsAxiom (Leq u v)
    -> IsProved IsAxiom (Leq (Lop2 o t u) (Lop2 o s v)).
Proof.
  intros.
  pose proof (IsProvedIsLproposition IsAxiom _ H) as tsterm.
  unfold Leq in tsterm. rewrite IsLproposition_rel2 in tsterm.
  pose proof (IsProvedIsLproposition IsAxiom _ H0) as uvterm.
  unfold Leq in uvterm. rewrite IsLproposition_rel2 in uvterm.
  apply andb_prop in tsterm. destruct tsterm as [tterm sterm].
  apply andb_prop in uvterm. destruct uvterm as [uterm vterm].
  apply (LimpliesElim _ (Land (Leq t s) (Leq u v))). 
  2: apply LandIntro; assumption. 
  pose proof (LeqElim_vars_op IsAxiom o (ConsNat t (ConsNat u NilNat))
                              (ConsNat s (ConsNat v NilNat))) as H1.
  do 4 rewrite LengthConsNat in H1.
  specialize (H1 eq_refl). simpl in H1.
  rewrite LengthNilNat in H1. simpl in H1.
  rewrite CoordConsHeadNat, CoordConsHeadNat in H1.
  rewrite CoordConsTailNat, CoordConsTailNat in H1.
  rewrite CoordConsHeadNat, CoordConsHeadNat in H1.
  apply H1. apply le_n_S, le_0_n.
  rewrite TailConsNat, TailConsNat. reflexivity.
  rewrite TailConsNat, TailConsNat. reflexivity.
  intros k H2. destruct k. rewrite CoordConsHeadNat. exact tterm.
  destruct k. rewrite CoordConsTailNat, CoordConsHeadNat. exact uterm.
  exfalso. apply le_S_n, le_S_n in H2. inversion H2.
  intros k H2. destruct k. rewrite CoordConsHeadNat. exact sterm.
  destruct k. rewrite CoordConsTailNat, CoordConsHeadNat. exact vterm.
  exfalso. apply le_S_n, le_S_n in H2. inversion H2.
Qed. 

Lemma LeqElim_vars_term : forall term,
    IsLterm term = true
    -> forall IsAxiom x y z,
      IsProved IsAxiom
               (Limplies (Leq (Lvar x) (Lvar y))
                         (Leq (SubstTerm (Lvar x) z term)
                              (SubstTerm (Lvar y) z term))).
Proof.
  apply (Lterm_rect (fun term => forall IsAxiom x y z,
      IsProved IsAxiom
               (Limplies (Leq (Lvar x) (Lvar y))
                         (Leq (SubstTerm (Lvar x) z term)
                              (SubstTerm (Lvar y) z term))))).
  - (* Lvar *)
    intros. rewrite SubstTerm_var, SubstTerm_var.
    destruct (v =? z) eqn:des. apply LimpliesRefl.
    rewrite IsLproposition_eq, IsLterm_var, IsLterm_var. reflexivity.
    apply (LimpliesElim _ (Leq (Lvar v) (Lvar v))).
    apply IsProvedPropAx, Ax1IsPropAx, Ax1IsAx1.
    rewrite IsLproposition_eq, IsLterm_var. reflexivity.
    rewrite IsLproposition_eq, IsLterm_var, IsLterm_var. reflexivity.
    apply LeqRefl, IsLterm_var.
  - (* Lop *)
    intros. 
    destruct (LengthNat terms) eqn:lenTerms.
    simpl in termsTrunc. subst terms.
    rewrite SubstTerm_op, SubstTerm_op.
    simpl.
    apply (LimpliesElim _ (Leq (Lop o 0) (Lop o 0))).
    apply IsProvedPropAx, Ax1IsPropAx, Ax1IsAx1.
    pose proof (IsLterm_const). unfold Lconst in H.
    rewrite IsLproposition_eq, H.
    simpl. rewrite MapNilNat. apply H.
    rewrite IsLproposition_eq, IsLterm_var, IsLterm_var. reflexivity.
    apply LeqRefl.
    pose proof (IsLterm_const). unfold Lconst in H.
    rewrite H. reflexivity.
    apply (LimpliesTrans
             _ _ (EqTerms (MapNat (SubstTerm (Lvar x) z) terms)
                          (MapNat (SubstTerm (Lvar y) z) terms)
                          n)).
    + assert (forall i, i < LengthNat terms
                   -> IsProved IsAxiom
                              (Limplies (Leq (Lvar x) (Lvar y))
                                        (EqTerms (MapNat (SubstTerm (Lvar x) z) terms)
                                                 (MapNat (SubstTerm (Lvar y) z) terms) i))).
      induction i.
      simpl. intros.
      rewrite CoordMapNat, CoordMapNat.
      apply IHterms. apply le_n_S, le_0_n. exact H. exact H.
      intros. 
      simpl. apply LandIntroHyp. apply IHi.
      apply (Nat.le_trans _ (S (S i))).
      apply le_S, Nat.le_refl. exact H.
      rewrite CoordMapNat, CoordMapNat.
      apply IHterms. rewrite <- lenTerms. exact H. exact H. exact H.
      change n with (pred (S n)). rewrite <- lenTerms.
      apply H. rewrite lenTerms. apply Nat.le_refl.
    + rewrite SubstTerm_op, SubstTerm_op.
      change n with (pred (S n)).
      rewrite <- lenTerms.
      rewrite <- (LengthMapNat (SubstTerm (Lvar x) z) terms).
      apply LeqElim_vars_op.
      rewrite LengthMapNat, LengthMapNat. reflexivity.
      rewrite LengthMapNat, lenTerms. apply le_n_S, le_0_n.
      rewrite LengthMapNat. 
      apply MapNatTruncated. 
      rewrite LengthMapNat. apply MapNatTruncated.
      intros k H. rewrite LengthMapNat in H.
      rewrite CoordMapNat. apply IsSubstTermLterm. apply IHterms.
      rewrite <- lenTerms. exact H. apply IsLterm_var. exact H.
      intros k H. rewrite LengthMapNat in H.
      rewrite CoordMapNat. apply IsSubstTermLterm. apply IHterms.
      rewrite <- lenTerms. exact H. apply IsLterm_var. exact H. 
Qed.

Lemma LeqElim_vars_atom : forall IsAxiom r terms x y z,
    (forall n:nat, n < LengthNat terms -> IsLterm (CoordNat terms n) = true)
    -> NthTailNat terms (LengthNat terms) = 0
    -> IsProved IsAxiom
               (Limplies (Leq (Lvar x) (Lvar y))
                         (Limplies
                            (Lrel r (MapNat (SubstTerm (Lvar x) z) terms))
                            (Lrel r (MapNat (SubstTerm (Lvar y) z) terms)))).
Proof.
  intros.
  pose proof (LeqElim_rel IsAxiom r (MapNat (SubstTerm (Lvar x) z) terms)
                          (MapNat (SubstTerm (Lvar y) z) terms) ).
  rewrite LengthMapNat, LengthMapNat in H1.
  specialize (H1 eq_refl).
  destruct (LengthNat terms) eqn:lenTerms.
  - simpl in H0. subst terms.
    assert (IsLproposition (Lrel r 0) = true).
    rewrite IsLproposition_rel. split. reflexivity.
    intros. inversion H0.
    apply (LimpliesElim _ (Limplies (Lrel r 0) (Lrel r 0))).
    2: apply LimpliesRefl, H0.
    apply IsProvedPropAx, Ax1IsPropAx, Ax1IsAx1.
    rewrite MapNilNat, MapNilNat.
    change NilNat with 0.
    rewrite IsLproposition_implies, H0. reflexivity.
    rewrite IsLproposition_eq, IsLterm_var, IsLterm_var. reflexivity.
  - apply (LimpliesTrans
             _ _ (EqTerms (MapNat (SubstTerm (Lvar x) z) terms)
                          (MapNat (SubstTerm (Lvar y) z) terms)
                          n)).
    + clear H1.
      assert (forall i, 1 <= i <= LengthNat terms
                   -> IsProved IsAxiom
                              (Limplies (Leq (Lvar x) (Lvar y))
                                        (EqTerms (MapNat (SubstTerm (Lvar x) z) terms)
                                                 (MapNat (SubstTerm (Lvar y) z) terms) (pred i)))).
      induction i.
      simpl. intros. destruct H1. exfalso. inversion H1.
      simpl. intros. destruct i.
      simpl. rewrite CoordMapNat, CoordMapNat.
      apply LeqElim_vars_term. apply H, le_n_S, le_0_n.
      rewrite lenTerms. apply le_n_S, le_0_n.
      rewrite lenTerms. apply le_n_S, le_0_n.
      simpl. apply LandIntroHyp. apply IHi.
      split. apply le_n_S, le_0_n. apply (Nat.le_trans _ (S (S i))).
      apply le_S, Nat.le_refl. apply H1.
      rewrite CoordMapNat, CoordMapNat.
      apply LeqElim_vars_term. apply H. rewrite <- lenTerms. apply H1.
      apply H1. apply H1.
      change n with (pred (S n)). rewrite <- lenTerms.
      apply H1. split. rewrite lenTerms. apply le_n_S, le_0_n.
      apply Nat.le_refl.
    + apply (LimpliesTrans _ _ (Lequiv (Lrel r (MapNat (SubstTerm (Lvar x) z) terms))
                                       (Lrel r (MapNat (SubstTerm (Lvar y) z) terms)))).
      apply H1. apply le_n_S, le_0_n.
      rewrite <- lenTerms. apply MapNatTruncated.
      rewrite <- lenTerms. apply MapNatTruncated.
      intros k H2. rewrite CoordMapNat.
      apply IsSubstTermLterm. apply H. exact H2. apply IsLterm_var.
      rewrite lenTerms. exact H2.
      intros k H2. rewrite CoordMapNat.
      apply IsSubstTermLterm. apply H. exact H2. apply IsLterm_var.
      rewrite lenTerms. exact H2.
      assert (IsLproposition (Lrel r (MapNat (SubstTerm (Lvar x) z) terms)) = true).
      { apply IsLproposition_rel. split.
        rewrite LengthMapNat. apply MapNatTruncated.
        intros. rewrite CoordMapNat.
        apply IsSubstTermLterm. apply H.
        rewrite LengthMapNat, lenTerms in H2. exact H2.
        apply IsLterm_var.
        rewrite LengthMapNat in H2. exact H2. }
      assert (IsLproposition (Lrel r (MapNat (SubstTerm (Lvar y) z) terms)) = true).
      { apply IsLproposition_rel. split.
        rewrite LengthMapNat. apply MapNatTruncated.
        intros. rewrite CoordMapNat.
        apply IsSubstTermLterm. apply H.
        rewrite LengthMapNat, lenTerms in H3. exact H3.
        apply IsLterm_var.
        rewrite LengthMapNat in H3. exact H3. }
      apply LandElim1_impl.
      rewrite IsLproposition_implies, H2, H3. reflexivity.
      rewrite IsLproposition_implies, H2, H3. reflexivity.
Qed.

(* Particular case of LeqElim where t = Lvar x and u = Lvar y.
   LeqElim will be obtained by specialization of the variables. *)
Lemma LeqElim_vars : forall prop,
    IsLproposition prop = true
    -> forall IsAxiom x y z, IsFreeForSubst (Lvar x) z prop = true
    -> IsFreeForSubst (Lvar y) z prop = true
    -> IsProved IsAxiom (Limplies (Leq (Lvar x) (Lvar y))
                                 (Limplies (Subst (Lvar x) z prop)
                                           (Subst (Lvar y) z prop))).
Proof.
  apply (Lproposition_rect (fun prop => forall IsAxiom (x y z : nat),
    IsFreeForSubst (Lvar x) z prop = true
    -> IsFreeForSubst (Lvar y) z prop = true
  -> IsProved IsAxiom
    (Limplies (Leq (Lvar x) (Lvar y))
       (Limplies (Subst (Lvar x) z prop) (Subst (Lvar y) z prop))))).
  - (* Lrel *)
    intros.
    rewrite Subst_rel, Subst_rel.
    apply LeqElim_vars_atom. exact elemterms. exact termsTrunc.
  - (* Lnot, by contraposition *)
    intros.
    rewrite Subst_not, Subst_not.
    apply (LimpliesTrans _ _ (Limplies (Subst (Lvar y) z prop)
                                       (Subst (Lvar x) z prop))).
    apply (LimpliesTrans _ _ (Leq (Lvar y) (Lvar x))).
    apply LeqSym_impl. apply IsLterm_var. apply IsLterm_var.
    apply IHprop.
    rewrite IsFreeForSubst_not in H0. exact H0.
    rewrite IsFreeForSubst_not in H. exact H.
    apply IsProvedContraposition_impl.
    apply SubstIsLproposition. apply propprop. apply IsLterm_var.
    apply SubstIsLproposition. apply propprop. apply IsLterm_var.
  - (* Limplies *)
    (* f = Limplies g h. Show that (Limplies g(Y) g(X)) and
     L implies h(X) h(Y), then transitivity of implication. *)
    intros.
    rewrite Subst_implies, Subst_implies.
    rewrite IsFreeForSubst_implies in H. apply andb_prop in H.
    rewrite IsFreeForSubst_implies in H0. apply andb_prop in H0.
    apply PullHypothesis, PullHypothesis.
    assert (IsLproposition (Leq (Lvar x) (Lvar y)) = true) as hyp1prop.
    { unfold Leq. rewrite IsLproposition_rel2.
      rewrite IsLterm_var, IsLterm_var. reflexivity. }
    assert (IsLproposition (Limplies (Subst (Lvar x) z g)
                                     (Subst (Lvar x) z h)) = true)
      as hyp2prop.
    { rewrite IsLproposition_implies.
      apply andb_true_intro; split.
      apply SubstIsLproposition. apply gprop. apply IsLterm_var.
      apply SubstIsLproposition. apply hprop. apply IsLterm_var. }
    assert (IsLproposition (Subst (Lvar y) z g) = true) as hyp3prop.
    { apply SubstIsLproposition. apply gprop. apply IsLterm_var. }
    apply (LimpliesTrans _ _ (Land (Leq (Lvar x) (Lvar y))
                                   (Subst (Lvar x) z h))).
    apply LandIntroHyp.
    exact (LandElim11_impl _ _ _ _ hyp1prop hyp2prop hyp3prop).
    apply (LimpliesTrans _ _ (Land (Limplies (Subst (Lvar x) z g)
                                             (Subst (Lvar x) z h))
                                   (Subst (Lvar x) z g))).
    apply LandIntroHyp.
    exact (LandElim12_impl _ _ _ _ hyp1prop hyp2prop hyp3prop).
    apply PushHypothesis.
    apply (LimpliesTrans _ _ (Leq (Lvar y) (Lvar x))).
    apply (LimpliesTrans _ _ (Leq (Lvar x) (Lvar y))).
    exact (LandElim1_impl IsAxiom _ _ hyp1prop hyp2prop).
    apply LeqSym_impl. apply IsLterm_var. apply IsLterm_var.
    apply IHg. apply H0. apply H.
    apply PushHypothesis, LimpliesRefl. exact hyp2prop.
    apply PushHypothesis, IHh.
    apply H. apply H0.
  - (* Lor *)
    intros. rewrite Subst_or, Subst_or.
    rewrite IsFreeForSubst_or in H. apply andb_prop in H.
    rewrite IsFreeForSubst_or in H0. apply andb_prop in H0.
    apply PullHypothesis, LorElimHyp.
    apply (LimpliesTrans _ _ (Subst (Lvar y) z g)).
    apply PushHypothesis, IHg. apply H. apply H0.
    apply IsProvedPropAx, Ax9IsPropAx, Ax9IsAx9.
    apply SubstIsLproposition. exact gprop. apply IsLterm_var.
    apply SubstIsLproposition. exact hprop. apply IsLterm_var.
    apply (LimpliesTrans _ _ (Subst (Lvar y) z h)).
    apply PushHypothesis, IHh. apply H. apply H0.
    apply IsProvedPropAx, Ax10IsPropAx, Ax10IsAx10.
    apply SubstIsLproposition. exact gprop. apply IsLterm_var.
    apply SubstIsLproposition. exact hprop. apply IsLterm_var.
  - (* Land *)
    intros.
    rewrite Subst_and, Subst_and.
    rewrite IsFreeForSubst_and in H. apply andb_prop in H.
    rewrite IsFreeForSubst_and in H0. apply andb_prop in H0.
    assert (IsLproposition (Leq (Lvar x) (Lvar y)) = true) as hyp1prop.
    { unfold Leq. rewrite IsLproposition_rel2.
      rewrite IsLterm_var, IsLterm_var. reflexivity. }
    assert (IsLproposition (Land (Subst (Lvar x) z g) (Subst (Lvar x) z h)) = true)
      as hyp2prop.
    { rewrite IsLproposition_and, SubstIsLproposition, SubstIsLproposition.
      reflexivity. exact hprop. apply IsLterm_var. exact gprop. apply IsLterm_var. }
    apply PullHypothesis, LandIntroHyp.
    apply (LimpliesTrans _ _ (Land (Leq (Lvar x) (Lvar y))
                                   (Subst (Lvar x) z g))).
    apply LandIntroHyp.
    apply (LandElim1_impl). exact hyp1prop.
    rewrite IsLproposition_and, SubstIsLproposition, SubstIsLproposition.
    reflexivity. exact hprop. apply IsLterm_var. apply gprop. apply IsLterm_var.
    apply (LimpliesTrans _ _ (Land (Subst (Lvar x) z g) (Subst (Lvar x) z h))).
    apply LandElim2_impl. exact hyp1prop. exact hyp2prop.
    apply LandElim1_impl.
    apply SubstIsLproposition. exact gprop. apply IsLterm_var.
    apply SubstIsLproposition. exact hprop. apply IsLterm_var.
    apply PushHypothesis, IHg. apply H. apply H0.
    apply (LimpliesTrans _ _ (Land (Leq (Lvar x) (Lvar y)) (Subst (Lvar x) z h))).
    apply LandIntroHyp.
    apply LandElim1_impl. exact hyp1prop. exact hyp2prop.
    apply (LimpliesTrans _ _ (Land (Subst (Lvar x) z g) (Subst (Lvar x) z h))).
    apply LandElim2_impl. exact hyp1prop. exact hyp2prop.
    apply LandElim2_impl.
    apply SubstIsLproposition. exact gprop. apply IsLterm_var.
    apply SubstIsLproposition. exact hprop. apply IsLterm_var.
    apply PushHypothesis, IHh. apply H. apply H0.
  - (* Lforall *)
    intros.
    assert (IsLproposition (Leq (Lvar x) (Lvar y)) = true) as hyp1prop.
    { unfold Leq. rewrite IsLproposition_rel2.
      rewrite IsLterm_var, IsLterm_var. reflexivity. }
    rewrite IsFreeForSubst_forall in H.
    rewrite IsFreeForSubst_forall in H0.
    rewrite Subst_forall, Subst_forall.
    rewrite Nat.eqb_sym in H. rewrite Nat.eqb_sym in H0.
    destruct (v =? z) eqn:des. clear H H0.
    apply DropHypothesis.
    unfold Leq. rewrite IsLproposition_rel2, IsLterm_var, IsLterm_var.
    reflexivity.
    apply LimpliesRefl.
    rewrite IsLproposition_forall. apply propprop.
    destruct (VarOccursFreeInFormula z prop) eqn:zsubst.
    (* A substitution in z occurs *)
    simpl in H. apply andb_prop in H.
    simpl in H0. apply andb_prop in H0.
    apply PullHypothesis.
    apply LforallIntroHyp.
    rewrite VarOccursFreeInFormula_and.
    unfold Leq.
    rewrite VarOccursFreeInFormula_rel2.
    rewrite VarOccursInTerm_var, VarOccursInTerm_var.
    rewrite VarOccursFreeInFormula_forall, Nat.eqb_refl. simpl.
    rewrite Bool.orb_false_r.
    rewrite VarOccursInTerm_var in H.
    rewrite VarOccursInTerm_var in H0.
    destruct H, H0.
    apply Bool.negb_true_iff in H1.
    apply Bool.negb_true_iff in H2.
    rewrite H1, H2. reflexivity.
    apply (LimpliesTrans _ _ (Land (Leq (Lvar x) (Lvar y))
                                   (Subst (Lvar x) z prop))).
    apply LandIntroHyp.
    apply (LandElim1_impl _ _ _ hyp1prop).
    rewrite IsLproposition_forall.
    apply SubstIsLproposition. exact propprop. apply IsLterm_var.
    apply (LimpliesTrans _ _ (Lforall v (Subst (Lvar x) z prop))).
    apply (LandElim2_impl _ _ _ hyp1prop).
    rewrite IsLproposition_forall.
    apply SubstIsLproposition. exact propprop. apply IsLterm_var.
    assert (IsLproposition (Subst (Lvar x) z prop) = true).
    { apply SubstIsLproposition. exact propprop. apply IsLterm_var. }
    rewrite <- (SubstIdemVar (Subst (Lvar x) z prop) H1 v) at 2.
    apply LforallElim_impl.
    apply SubstIsLproposition. exact propprop.
    apply IsLterm_var. apply IsLterm_var.
    apply IsFreeForSubst_closed.
    apply SubstIsLproposition. exact propprop. apply IsLterm_var.
    intros. rewrite VarOccursInTerm_var. apply Nat.eqb_neq, H2.
    apply PushHypothesis, IHprop.
    apply H. apply H0. clear H H0.
    rewrite Subst_nosubst, Subst_nosubst.
    apply DropHypothesis.
    unfold Leq. rewrite IsLproposition_rel2, IsLterm_var, IsLterm_var.
    reflexivity.
    apply LimpliesRefl.
    rewrite IsLproposition_forall. apply propprop.
    exact zsubst. exact zsubst.
  - (* Lexists *)
    intros.
    rewrite IsFreeForSubst_exists in H.
    rewrite IsFreeForSubst_exists in H0.
    rewrite Subst_exists, Subst_exists.
    rewrite Nat.eqb_sym.
    destruct (z =? v) eqn:des. clear H H0.
    apply DropHypothesis.
    unfold Leq. rewrite IsLproposition_rel2, IsLterm_var, IsLterm_var.
    reflexivity.
    apply LimpliesRefl.
    rewrite IsLproposition_exists. apply propprop.
    destruct (VarOccursFreeInFormula z prop) eqn:zsubst.
    (* A substitution in z occurs *)
    simpl in H. apply andb_prop in H.
    simpl in H0. apply andb_prop in H0.
    rewrite Bool.negb_true_iff in H.
    rewrite Bool.negb_true_iff in H0.
    apply PullHypothesis, LexistsElimHyp, LforallIntroHyp.
    rewrite VarOccursFreeInFormula_exists, Nat.eqb_refl. reflexivity.
    unfold Leq. rewrite VarOccursFreeInFormula_rel2.
    rewrite (proj2 H), (proj2 H0). reflexivity.
    apply PullHypothesis.
    apply (LimpliesTrans _ _ (Subst (Lvar y) z prop)).
    apply PushHypothesis, IHprop. apply H. apply H0.
    assert (IsLproposition (Subst (Lvar y) z prop) = true).
    { apply SubstIsLproposition. exact propprop. apply IsLterm_var. }
    rewrite <- (SubstIdemVar (Subst (Lvar y) z prop) H1 v) at 1. clear H1.
    apply LexistsIntro_impl. apply IsLterm_var.
    apply SubstIsLproposition. exact propprop. apply IsLterm_var.
    apply IsFreeForSubst_closed.
    apply SubstIsLproposition. exact propprop. apply IsLterm_var.
    intros. rewrite VarOccursInTerm_var. apply Nat.eqb_neq, H1.
    rewrite Subst_nosubst, Subst_nosubst.
    apply DropHypothesis.
    unfold Leq. rewrite IsLproposition_rel2, IsLterm_var, IsLterm_var.
    reflexivity.
    apply LimpliesRefl.
    rewrite IsLproposition_exists. apply propprop.
    exact zsubst. exact zsubst.
Qed.

Lemma LeqElim : forall IsAxiom prop t u v,
    IsLproposition prop = true
    -> IsLterm t = true
    -> IsLterm u = true
    -> IsFreeForSubst t v prop = true
    -> IsFreeForSubst u v prop = true
    -> IsProved IsAxiom (Limplies (Leq t u)
                                 (Limplies (Subst t v prop)
                                           (Subst u v prop))).
Proof.
  intros IsAxiom prop t u v propprop tterm uterm. intros.
  pose (S (Nat.max (MaxVar prop) (MaxVarTerm u))) as m.
  assert (forall n:nat, Nat.eqb n (S n) = false) as succneq.
  { intro n. apply Nat.eqb_neq. intro abs.
    apply (Nat.lt_irrefl n). rewrite abs at 2. apply Nat.le_refl. }
  assert (IsFreeForSubst (Lvar m) v prop = true) as mfreesubst.
  { apply MaxVarFreeSubst_var. exact propprop.
    apply le_n_S. apply Nat.le_max_l. }
  assert (IsFreeForSubst (Lvar (S m)) v prop = true) as smfreesubst.
  { apply MaxVarFreeSubst_var. exact propprop.
    apply le_n_S, le_S. apply Nat.le_max_l. }
  pose proof (LeqElim_vars prop propprop IsAxiom m (S m) v
                           mfreesubst smfreesubst) as substvars.
  (* Specialize u in substvars *)
  apply (LforallIntro _ _ (S m)) in substvars.
  apply (LforallElim IsAxiom _ _ u) in substvars.
  2: exact uterm.
  rewrite Subst_implies, Subst_eq, Subst_implies in substvars.
  rewrite SubstTerm_var, SubstTerm_var, Nat.eqb_refl, succneq in substvars.
  rewrite (SubstSubstNested prop propprop u (Lvar (S m)) (S m) v) in substvars.
  rewrite SubstTerm_var, Nat.eqb_refl in substvars.
  3: exact smfreesubst.
  rewrite Subst_nosubst in substvars.
  (* Specialize t in substvars *)
  apply (LforallIntro _ _ m) in substvars.
  apply (LforallElim IsAxiom _ _ t) in substvars. 2: exact tterm.
  rewrite Subst_implies, Subst_eq, Subst_implies in substvars.
  rewrite SubstTerm_var, Nat.eqb_refl in substvars.
  rewrite SubstTerm_nosubst, SubstSubstNested in substvars.
  rewrite SubstTerm_var, Nat.eqb_refl in substvars.
  rewrite (Subst_nosubst _ m t) in substvars.
  exact substvars.
  (* Finish by proving there was no variable captures *)
  apply MaxVarDoesNotOccurFree.
  apply SubstIsLproposition. exact propprop. exact uterm.
  apply (Nat.le_trans _ (S (Nat.max (MaxVarTerm u) (MaxVar prop)))).
  apply le_n_S, MaxVar_Subst.
  apply le_n_S. rewrite Nat.max_comm. apply Nat.le_refl. exact propprop.
  apply MaxVarDoesNotOccurFree. exact propprop. apply le_n_S, Nat.le_max_l.
  apply MaxVarFreeSubst_var. exact propprop. apply le_n_S, Nat.le_max_l.
  apply MaxVarTermDoesNotOccur. apply le_n_S, Nat.le_max_r.
  exact uterm.
  (* IsFreeForSubst t m ... *)
  rewrite IsFreeForSubst_implies.
  unfold Leq. rewrite IsFreeForSubst_rel2, IsFreeForSubst_implies. simpl.
  apply andb_true_intro. split.
  rewrite IsFreeForSubstVarChange. exact H.
  exact propprop. exact tterm.
  apply MaxVarDoesNotOccurFree. exact propprop. apply le_n_S, Nat.le_max_l.
  apply MaxVarFreeSubst_var. exact propprop. apply le_n_S, Nat.le_max_l.
  apply IsFreeForSubst_nosubst.
  apply SubstIsLproposition. exact propprop. exact uterm.
  apply MaxVarDoesNotOccurFree.
  apply SubstIsLproposition. exact propprop. exact uterm.
  apply le_n_S.
  apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
  rewrite Nat.max_comm. apply Nat.le_refl.
  apply MaxVarDoesNotOccurFree.
  apply SubstIsLproposition. exact propprop. apply IsLterm_var.
  apply le_n_S.
  apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
  rewrite MaxVarTerm_var. apply Nat.max_lub. apply Nat.le_refl.
  apply le_S, Nat.le_max_l.
  apply MaxVarDoesNotOccurFree. exact propprop. apply le_n_S, le_S, Nat.le_max_l.
  (* IsFreeForSubst u (S m) ... *)
  rewrite IsFreeForSubst_implies.
  unfold Leq. rewrite IsFreeForSubst_rel2, IsFreeForSubst_implies. simpl.
  apply andb_true_intro; split.
  apply IsFreeForSubst_nosubst.
  apply SubstIsLproposition. exact propprop. apply IsLterm_var.
  destruct (Nat.eq_dec (S m) v).
  rewrite <- e.
  apply VarOccursFreeInFormula_SubstIdem.
  exact propprop.
  rewrite VarOccursInTerm_var, Nat.eqb_sym. apply succneq.
  rewrite VarOccursFreeInFormula_SubstDiff.
  apply MaxVarDoesNotOccurFree. exact propprop. apply le_n_S, le_S, Nat.le_max_l.
  exact propprop. exact n.
  rewrite VarOccursInTerm_var, Nat.eqb_sym. apply succneq.
  rewrite IsFreeForSubstVarChange. exact H0.
  exact propprop. exact uterm.
  apply MaxVarDoesNotOccurFree. exact propprop. apply le_n_S, le_S, Nat.le_max_l.
  apply MaxVarFreeSubst_var. exact propprop. apply le_n_S, le_S, Nat.le_max_l.
Qed.

Lemma LeqElimSubstVar : forall IsAxiom v t prop,
    IsLproposition prop = true
    -> IsLterm t = true
    -> IsFreeForSubst t v prop = true
    -> IsProved IsAxiom (Subst t v prop)
    -> IsProved IsAxiom (Limplies (Leq (Lvar v) t) prop).
Proof.
  intros.
  pose proof (LeqElim IsAxiom prop t (Lvar v) v H H0
                      (IsLterm_var _) H1) as H3.
  rewrite SubstIdemVar in H3.
  2: exact H.
  apply (LimpliesTrans _ _ (Leq t (Lvar v))).
  apply LeqSym_impl. apply IsLterm_var. exact H0.
  apply (RemoveRedundantHypothesis
           IsAxiom (Leq t (Lvar v))
           (Subst t v prop) 
           prop).
  apply H3. 
  apply IsFreeForSubstIdemVar. exact H.
  apply DropHypothesis. rewrite IsLproposition_eq.
  rewrite H0, IsLterm_var. reflexivity. exact H2. 
Qed.

Lemma LforallElimIdemVar : forall IsAxiom prop v,
    IsProved IsAxiom (Lforall v prop)
    -> IsProved IsAxiom prop.
Proof.
  intros.
  pose proof (IsProvedIsLproposition _ _ H).
  rewrite IsLproposition_forall in H0. 
  apply (LforallElim IsAxiom prop v (Lvar v)) in H.
  rewrite SubstIdemVar in H. exact H. exact H0.
  apply IsLterm_var. apply IsFreeForSubstIdemVar. exact H0.
Qed. 

Lemma DropFirstHypothesis : forall IsAxiom f g h,
    IsLproposition f = true ->
    IsProved IsAxiom (Limplies g h) ->
    IsProved IsAxiom (Limplies (Land f g) h).
Proof.
  intros.
  pose proof (IsProvedIsLproposition _ _ H0).
  rewrite IsLproposition_implies in H1. apply andb_prop in H1.
  apply (LimpliesTrans _ _ g).
  apply LandElim2_impl. exact H. apply H1. exact H0.
Qed.

Lemma DropSecondHypothesis : forall IsAxiom f g h,
    IsLproposition g = true ->
    IsProved IsAxiom (Limplies f h) ->
    IsProved IsAxiom (Limplies (Land f g) h).
Proof.
  intros.
  pose proof (IsProvedIsLproposition _ _ H0).
  rewrite IsLproposition_implies in H1. apply andb_prop in H1.
  apply (LimpliesTrans _ _ f).
  apply LandElim1_impl. apply H1. exact H. exact H0.
Qed.

Lemma CommuteHypotheses : forall IsAxiom f g h,
    IsProved IsAxiom (Limplies (Land f g) h) ->
    IsProved IsAxiom (Limplies (Land g f) h).
Proof.
  intros.
  pose proof (IsProvedIsLproposition _ _ H).
  rewrite IsLproposition_implies in H0. apply andb_prop in H0.
  destruct H0. rewrite IsLproposition_and in H0. apply andb_prop in H0.
  apply (LimpliesTrans _ _ (Land f g)).
  apply LandIntroHyp.
  apply LandElim2_impl. apply H0. apply H0.
  apply LandElim1_impl. apply H0. apply H0.
  exact H.
Qed.

