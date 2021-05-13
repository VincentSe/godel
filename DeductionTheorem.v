(** The theorem of deduction is the special case of LimpliesIntro when
    the hypothesis is a closed formula. It also allows to consistently add
    a closed formula P to the axioms when P is not refutable. *)

Require Import PeanoNat.
Require Import Arith.Wf_nat.
Require Import EnumSeqNat.
Require Import Formulas.
Require Import Substitutions.
Require Import Proofs.
Require Import ProofTactics.

Lemma DeductionTheorem : forall (IsAxiom : nat -> bool) (f:nat),
    IsLproposition f = true
    -> (forall v:nat, VarOccursFreeInFormula v f = false)
    -> forall g, IsProved (fun n:nat => IsAxiom n || Nat.eqb n f)%bool g
    -> IsProved IsAxiom (Limplies f g).
Proof.
  intros IsAxiom f fprop fclosed.
  assert (forall len pr g,
             LengthNat pr = len
             -> IsProof (fun n : nat => (IsAxiom n || Nat.eqb n f)%bool) g pr = true
             -> IsProved IsAxiom (Limplies f g)).
  apply (Fix lt_wf (fun len => forall pr g,
             LengthNat pr = len
             -> IsProof (fun n : nat => (IsAxiom n || Nat.eqb n f)%bool) g pr = true
             -> IsProved IsAxiom (Limplies f g))).
  - intros len IHlen pr g prLen prf.
    assert (IsLproposition g = true) as gprop.
    { apply (IsProvedIsLproposition (fun n : nat => (IsAxiom n || (n =? f))%bool)).
      exists pr. exact prf. }
    assert (forall k, 1 <= k < LengthNat pr
                 -> IsProved IsAxiom (Limplies f (CoordNat pr k)))
      as shorterProofs.
    { intros k [kpos H]. subst len.
      refine (IHlen (LengthNat pr - k) _ (NthTailNat pr k) (CoordNat pr k) _ _).
      apply PeanoNat.Nat.sub_lt. apply (Nat.le_trans _ (S k)).
      apply le_S, Nat.le_refl. exact H. exact kpos.
      apply LengthNthTailNat.
      apply ProofStack.
      apply andb_prop in prf. apply prf. exact H. }
    clear IHlen.
    (* Then prove g = CoordNat pr 0 by weaving the shorter proofs. *)
    apply andb_prop in prf. destruct prf as [H prf].
    apply andb_prop in H. destruct H.
    apply Nat.leb_le in H0.
    destruct len. exfalso. rewrite prLen in H0. inversion H0.
    rewrite prLen in prf. simpl in prf.
    apply andb_prop in prf. destruct prf as [prf restOfProof].
    apply Nat.eqb_eq in H. rewrite <- H in prf.
    unfold IsProofStep in prf.
    rewrite gprop, Bool.andb_true_r in prf.
    destruct (IsAxiom g || (g =? f) || IsPropositionalAxiom g || IsEqualityAxiom g)%bool
             eqn:gax.
    2: destruct (IsModusPonens g (TailNat pr)) eqn:gmp.
    + (* g is proved by IsAxiom *)
      clear prf. destruct (g =? f) eqn:geqf.
      apply Nat.eqb_eq in geqf. rewrite <- geqf. apply LimpliesRefl, gprop.
      apply (LimpliesElim _ g).
      apply IsProvedPropAx, Ax1IsPropAx, Ax1IsAx1.
      exact gprop. exact fprop.
      exists (ConsNat g NilNat).
      apply andb_true_intro; split.
      apply andb_true_intro; split.
      rewrite CoordConsHeadNat. apply Nat.eqb_refl.
      rewrite LengthConsNat. reflexivity. 
      rewrite LengthConsNat. simpl.
      rewrite Bool.andb_true_r, TailConsNat, CoordConsHeadNat.
      unfold IsProofStep. rewrite gprop.
      destruct (IsAxiom g). reflexivity.
      destruct (IsPropositionalAxiom g). reflexivity.
      simpl in gax. rewrite gax. reflexivity.
    + (* Modus ponens. There is an index k such as
         CoordNat pr (S k) = Limplies h g.
         So shorterProofs gives IsProved IsAxiom (Limplies f (Limplies h g)). *)
      clear prf gax.
      apply IsModusPonens_true in gmp.
      destruct gmp as [k [klen [kimp [gmp findhyp]]]].
      rewrite CoordTailNat in kimp.
      rewrite CoordTailNat in gmp.
      apply FindNat_true in findhyp.
      destruct findhyp as [j findhyp].
      assert (IsProved IsAxiom (Limplies f (Limplies (CoordNat pr (S j)) g))).
      { specialize (shorterProofs (S k)).
        apply Nat.eqb_eq in kimp. rewrite kimp in shorterProofs.
        destruct findhyp. rewrite CoordTailNat in H2.
        rewrite H2, CoordTailNat in shorterProofs.
        rewrite gmp. apply shorterProofs. split.
        apply le_n_S, le_0_n. rewrite LengthTailNat in klen.
        destruct (LengthNat pr). inversion H0. apply le_n_S, klen. }
      assert (IsProved IsAxiom (Limplies f (CoordNat pr (S j)))).
      { apply (shorterProofs (S j)). split.
        apply le_n_S, le_0_n. destruct findhyp as [jlen findhyp].
        rewrite LengthTailNat in jlen.
        destruct (LengthNat pr). inversion H0. apply le_n_S, jlen. }
      apply (LimpliesElim _ (Limplies f (CoordNat pr (S j)))).
      2: exact H2.
      apply (LimpliesElim _ (Limplies f (Limplies (CoordNat pr (S j)) g))).
      2: exact H1.
      apply IsProvedPropAx, Ax2IsPropAx, Ax2IsAx2.
      exact fprop. 2: exact gprop. 
      pose proof (IsProvedIsLproposition IsAxiom _ H2).
      rewrite IsLproposition_implies in H3.
      apply andb_prop in H3. apply H3.
    + (* quantifier axiom *)
      simpl in prf. unfold IsQuantifierAxiom in prf.
      destruct (IsGeneralization g (TailNat pr)) eqn:ggen.
      clear prf. unfold IsGeneralization in ggen.
      apply andb_prop in ggen. destruct ggen.
      apply FindNat_true in H2. destruct H2 as [k [klen H2]].
      apply Nat.eqb_eq in H1.
      assert (IsProved IsAxiom (Limplies f (CoordNat g 2))).
      { rewrite CoordTailNat in H2. rewrite H2.
        apply (shorterProofs (S k)). split.
        apply le_n_S, le_0_n.
        rewrite LengthTailNat in klen.
        destruct (LengthNat pr). inversion H0. apply le_n_S, klen. }
      apply (LforallIntro IsAxiom _ (CoordNat g 1)) in H3.
      rewrite H1.
      apply (LimpliesElim _ (Lforall (CoordNat g 1) (Limplies f (CoordNat g 2)))).
      2: exact H3.
      apply IsProvedIndepPremise. exact fprop.
      rewrite H1, IsLproposition_forall in gprop. exact gprop.
      apply fclosed.
      (* Now g is proved by IsAxiom *)
      simpl in prf.
      apply (LimpliesElim _ g).
      apply IsProvedPropAx, Ax1IsPropAx, Ax1IsAx1.
      exact gprop. exact fprop.
      exists (ConsNat g NilNat).
      apply andb_true_intro; split.
      apply andb_true_intro; split.
      rewrite CoordConsHeadNat. apply Nat.eqb_refl.
      rewrite LengthConsNat. reflexivity. 
      rewrite LengthConsNat. simpl.
      rewrite Bool.andb_true_r, TailConsNat, CoordConsHeadNat.
      unfold IsProofStep. rewrite gprop.
      unfold IsQuantifierAxiom.
      rewrite <- (Bool.orb_assoc (IsGeneralization g NilNat)).
      rewrite <- (Bool.orb_assoc (IsGeneralization g NilNat)).
      rewrite prf, Bool.orb_true_r, Bool.orb_true_r. reflexivity.
  - intros g [pr prf].
    exact (H (LengthNat pr) pr g eq_refl prf).
Qed.


(* If a closed proposition ax is not refuted by IsAxiom,
   then IsAxiom is consistent and so is IsAxiom+ax. *)
Lemma AddConsistentAxiom : forall IsAxiom ax,
    (forall v:nat, VarOccursFreeInFormula v ax = false)
    -> IsLproposition ax = true
    -> (forall n:nat, IsProof IsAxiom (Lnot ax) n = false)
    -> (forall n:nat, IsProof (fun n:nat => IsAxiom n || Nat.eqb n ax)%bool (Lnot ax) n = false).
Proof.
  intros. 
  destruct (IsProof (fun n0 : nat => (IsAxiom n0 || Nat.eqb n0 ax)%bool) (Lnot ax) n)
           eqn:des.
  2: reflexivity. exfalso.
  assert (IsProved (fun n0 : nat => (IsAxiom n0 || Nat.eqb n0 ax)%bool) (Lnot ax))
    as notconsist.
  exists n. exact des.
  apply DeductionTheorem in notconsist. 2: exact H0. 2: exact H.
  apply NotByContradiction in notconsist.
  destruct notconsist as [pr prf].
  specialize (H1 pr). rewrite H1 in prf. discriminate.
Qed.
