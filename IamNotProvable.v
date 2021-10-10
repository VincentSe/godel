(** This proves Gödel's first incompleteness theorem.

    It constructs a Pi_1 arithmetic formula G that satisfies the equation
    IsWeakHeytingAxiom  |--  G <-> ~IsProved IsAxiom G
    We may interpret G as roughly saying "I am not provable by IsAxiom".
    Under additional hypotheses on IsAxiom, we will show that G is true in
    the standard model of arithmetic, and that G is not provable by IsAxiom.
    G is not refutable either, by its truth in the standard model.
    Because G is not provable, there are models of arithmetic where it is false.
    In other words, G has non-standard proofs only.

    The most difficult hypothesis on IsAxiom will be its consistency, which is
    necessary to avoid proving G (and ~G). We will also require that IsAxiom extends
    arithmetic, to lift G in the language of IsAxiom. *)

Require Import PeanoNat.
Require Import Arith.Wf_nat.
Require Import Arith.Compare_dec.
Require Import EnumSeqNat.
Require Import Formulas.
Require Import Proofs.
Require Import Substitutions.
Require Import IsFreeForSubst.
Require Import PeanoAxioms.
Require Import ProofTactics.
Require Import PeanoModel.
Require Import HeytingModel.
Require Import HeytingRepresentation.
Require Import BoolRepresented.
Require Import DeductionTheorem.
Require Import BetaRepr.
Require Import EnumSeqNat_repr.
Require Import IsProof_repr.
Require Import Consistency.


(* Theta composes arithmetic predicate prop with self-application,
   prop(X0(X0)). *)
Definition Theta (prop : nat) : nat :=
  ComposePropFunc prop SubstSelfZeroRepresented.
  
Lemma ComposePropFuncSpec :
  forall (A : nat) (B : nat -> nat) (k : nat) (Brep : FunctionRepresented 1 B),
    IsLproposition A = true
    -> (forall v, 1 <= v -> VarOccursFreeInFormula v A = false)
    -> IsProved IsWeakHeytingAxiom
               (Lequiv (Subst (PAnat (B k)) 0 A)
                       (Subst (PAnat k) 0 (ComposePropFunc A (fr_prop _ _ Brep)))).
Proof.
  intros.
  unfold ComposePropFunc.
  pose (Nat.max (MaxVar A) (MaxVar Brep)) as m.
  fold m.
  rewrite Subst_exists; simpl.
  rewrite Subst_and, SubstSubstIdem, SubstTerm_var. simpl.
  apply LandIntro.
  - refine (LimpliesTrans
              IsWeakHeytingAxiom _ _ _ _
              (LexistsIntro_impl IsWeakHeytingAxiom _ _ (PAnat (B k)) _ _ _)).
    + rewrite Subst_and.
      apply LandIntroHyp.
      apply DropHypothesis.
      apply SubstIsLproposition.
      exact H. apply IsLterm_PAnat.
      rewrite SubstSubstDiffCommutes.
      rewrite (SubstSubstNested _ (fr_propprop _ _ Brep)), SubstTerm_var.
      rewrite Nat.eqb_refl.
      pose proof (FormulaRepresents_alt
                    1 B Brep (ConsNat k NilNat)
                    (fr_rep _ _ Brep) (fr_propprop _ _ Brep) (B k)) as H1.
      simpl in H1.
      rewrite CoordConsHeadNat in H1.
      destruct H1 as [H1 _].
      specialize (H1 eq_refl).
      rewrite SubstSubstDiffCommutes. exact H1.
      discriminate. apply PAnat_closed. apply PAnat_closed.
      apply MaxVarDoesNotOccurFree. apply fr_propprop.
      apply le_n_S, Nat.le_max_r.
      apply MaxVarFreeSubst_var. apply fr_propprop.
      apply le_n_S, Nat.le_max_r.
      discriminate. apply PAnat_closed. apply PAnat_closed.
      rewrite (SubstSubstNested _ H), SubstTerm_var, Nat.eqb_refl.
      apply LimpliesRefl.
      apply SubstIsLproposition. exact H.
      apply IsLterm_PAnat.
      apply MaxVarDoesNotOccurFree.
      exact H. apply le_n_S, Nat.le_max_l.
      apply MaxVarFreeSubst_var.
      exact H. apply le_n_S, Nat.le_max_l.
    + apply IsLterm_PAnat.
    + rewrite IsLproposition_and.
      rewrite SubstIsLproposition.
      apply SubstIsLproposition.
      exact H. apply IsLterm_var.
      apply SubstIsLproposition. apply fr_propprop.
      apply IsLterm_var. apply IsLterm_PAnat.
    + apply IsFreeForSubst_PAnat.
      rewrite IsLproposition_and.
      rewrite SubstIsLproposition.
      apply SubstIsLproposition.
      exact H. apply IsLterm_var.
      apply SubstIsLproposition. apply fr_propprop.
      apply IsLterm_var. apply IsLterm_PAnat.
  - apply LexistsElim_impl.
    apply VarOccursFreeInFormula_SubstClosed.
    apply MaxVarDoesNotOccurFree. exact H.
    apply le_n_S, Nat.le_max_l. apply PAnat_closed.
    apply LforallIntro.
    apply PushHypothesis.
    (* Replace Lvar (S m) by PAnat (B k). *)
    apply (LimpliesTrans _ _ (Leq (Lvar (S m)) (PAnat (B k)))).
    pose proof (fr_rep _ _ Brep (ConsNat k NilNat)) as H1.
    simpl in H1.
    rewrite CoordConsHeadNat in H1.
    apply (LforallElim _ _ _ (Lvar (S m))) in H1.
    rewrite Subst_equiv, Subst_eq, SubstTerm_var, SubstTerm_PAnat in H1.
    simpl in H1.
    rewrite SubstSubstDiffCommutes. 
    apply LandElim1 in H1. exact H1.
    discriminate. apply PAnat_closed. 
    rewrite VarOccursInTerm_var. reflexivity.
    apply IsLterm_var.
    rewrite IsFreeForSubst_equiv.
    unfold Leq. rewrite IsFreeForSubst_rel2, Bool.andb_true_r.
    apply MaxVarFreeSubst_var.
    apply SubstIsLproposition. apply fr_propprop.
    apply IsLterm_PAnat.
    apply le_n_S.
    apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
    apply Nat.max_lub.
    rewrite MaxVarTerm_PAnat. apply le_0_n.
    apply Nat.le_max_r.
    apply LeqElimSubstVar.
    rewrite IsLproposition_implies.
    rewrite SubstIsLproposition.
    apply SubstIsLproposition. exact H.
    apply IsLterm_PAnat.
    exact H. apply IsLterm_var. apply IsLterm_PAnat.
    apply IsFreeForSubst_PAnat.
    rewrite IsLproposition_implies.
    rewrite SubstIsLproposition.
    apply SubstIsLproposition. exact H.
    apply IsLterm_PAnat. exact H.
    apply IsLterm_var. 
    rewrite Subst_implies.
    rewrite SubstSubstNested, SubstTerm_var, Nat.eqb_refl.
    rewrite (Subst_nosubst _ (S m)).
    apply LimpliesRefl.
    apply SubstIsLproposition. exact H.
    apply IsLterm_PAnat.
    apply VarOccursFreeInFormula_SubstClosed.
    apply MaxVarDoesNotOccurFree. exact H.
    apply le_n_S, Nat.le_max_l. apply PAnat_closed.
    exact H.
    apply MaxVarDoesNotOccurFree. exact H.
    apply le_n_S, Nat.le_max_l.
    apply MaxVarFreeSubst_var. exact H.
    apply le_n_S, Nat.le_max_l. 
Qed.


(* Gödel's famous self-referencing formulas,
   Theta(prop)(Theta(prop)) = prop(Theta(prop)(Theta(prop))).
   Informally, GodelFormula(prop) is a fixpoint of prop.
   By taking prop(X0) := "X0 is not provable",
   we obtain a formula G equivalent to "G is not provable". *)
Definition GodelFormula (prop : nat) : nat :=
  Subst (PAnat (Theta prop)) 0 (Theta prop).

Lemma GodelFormula_closed : forall prop : nat,
    IsLproposition prop = true
    -> (forall n, 0 < n -> VarOccursFreeInFormula n prop = false)
    -> forall v, VarOccursFreeInFormula v (GodelFormula prop) = false.
Proof.
  intros.
  assert (IsLproposition (Theta prop) = true) as thetaprop.
  { apply ComposePropFuncIsProp. exact H. apply fr_propprop. }
  unfold GodelFormula.
  destruct v.
  - apply VarOccursFreeInFormula_SubstIdem.
    exact thetaprop. apply PAnat_closed.
  - rewrite VarOccursFreeInFormula_SubstDiff.
    2: exact thetaprop. 2: discriminate.
    unfold Theta.
    apply ComposePropFuncVars.
    exact H. apply fr_propprop.
    intros. exact (H0 _ H1).
    intros. apply fr_vars, H1.
    apply le_n_S, le_0_n.
    apply PAnat_closed.
Qed.

Lemma GodelFormulaIsLproposition : forall prop : nat,
    IsLproposition prop = true
    -> IsLproposition (GodelFormula prop) = true.
Proof.
  intros.
  apply SubstIsLproposition.
  2: apply IsLterm_PAnat.
  unfold Theta.
  apply ComposePropFuncIsProp. exact H.
  apply fr_propprop.
Qed.

(* Formalization of the fixpoint equation
   G = Theta(prop)(Theta(prop)) = prop(Theta(prop)(Theta(prop))) = prop(G).
   The equality is replaced by logical equivalence of arithmetical propositions,
   proved by IsWeakHeytingAxiom. *)
Lemma PropFixesGodelFormula : forall (prop : nat),
    IsLproposition prop = true
    -> (forall v:nat, 0 < v -> VarOccursFreeInFormula v prop = false)
    -> IsProved IsWeakHeytingAxiom
               (Lequiv (GodelFormula prop)
                       (Subst (PAnat (GodelFormula prop)) 0 prop)).
Proof.
  intros prop propprop zeroonlyfree.
  pose proof (ComposePropFuncSpec
                prop (fun prop : nat => Subst (PAnat prop) 0 prop)
                (Theta prop) SubstSelfZeroRepresented propprop zeroonlyfree) as H.
  simpl in H.
  apply LandIntro.
  - apply DeductionTheorem.
    apply GodelFormulaIsLproposition, propprop.
    apply GodelFormula_closed, zeroonlyfree. exact propprop.
    assert (IsProved (fun n : nat => (IsWeakHeytingAxiom n || (n =? GodelFormula prop))%bool)
                     (GodelFormula prop)) as GprovesItself.
    { apply AxiomIsProved. apply Bool.orb_true_intro.
      right. apply Nat.eqb_refl. apply GodelFormulaIsLproposition.
      exact propprop. }
    unfold GodelFormula at 2 in GprovesItself.
    unfold Theta at 2 in GprovesItself.
    apply (WeakenProvable
             IsWeakHeytingAxiom
             (fun n : nat => (IsWeakHeytingAxiom n || (n =? GodelFormula prop))%bool))
      in H. 
    apply LandElim2 in H.
    exact (LimpliesElim _ _ _ H GprovesItself).
    intros n H0.
    rewrite H0. reflexivity.
  - unfold GodelFormula at 2.
    unfold Theta at 2.
    apply DeductionTheorem.
    apply SubstIsLproposition. exact propprop. apply IsLterm_PAnat.
    intro v.
    destruct v. apply VarOccursFreeInFormula_SubstIdem.
    exact propprop.
    apply PAnat_closed.
    rewrite VarOccursFreeInFormula_SubstDiff.
    apply zeroonlyfree. apply le_n_S, le_0_n.
    exact propprop. discriminate.
    apply PAnat_closed.
    apply (WeakenProvable
             IsWeakHeytingAxiom
             (fun n : nat => (IsWeakHeytingAxiom n || (n =? Subst (PAnat (GodelFormula prop)) 0 prop))%bool))
      in H. 
    apply LandElim1 in H.
    apply (LimpliesElim _ _ _ H).
    apply AxiomIsProved.
    unfold GodelFormula. rewrite Nat.eqb_refl.
    apply Bool.orb_true_r.
    apply SubstIsLproposition. exact propprop.
    apply IsLterm_PAnat.
    intros. rewrite H0. reflexivity.
Qed.

(* Pi_1 closed formula expressing the non provability of itself. *)
Definition IamNotProvable (IsAxiom : nat -> bool) IsAxiomRep (InterpArithLprop : nat) : nat
  := GodelFormula (Lnot (IsProvedArith IsAxiom IsAxiomRep InterpArithLprop)).

Lemma IamNotProvable_spec : forall IsAxiom IsAxiomRep InterpArithLprop,
  IsLproposition InterpArithLprop = true ->
  (forall v : nat, 2 <= v -> VarOccursFreeInFormula v InterpArithLprop = false) ->
  let G := IamNotProvable IsAxiom IsAxiomRep InterpArithLprop in
  IsProved IsWeakHeytingAxiom
           (Lequiv G (Subst (PAnat G) 0
                            (Lnot (IsProvedArith IsAxiom IsAxiomRep InterpArithLprop)))).
Proof.
  intros.
  apply PropFixesGodelFormula.
  rewrite IsLproposition_not.
  apply IsProvedArithIsLprop, H.
  intros w H1. rewrite VarOccursFreeInFormula_not.
  apply IsProvedArithVars. exact H. exact H0. exact H1.
Qed.

(* The truth of IamNotProvable in the standard model of arithmetic is absolute,
   it says that the brute force search over all proof:nat never terminates.
   However we cannot lift this to IsProved IsWeakHeytingAxiom, because
   the Gödel formula is Pi_1 and not Sigma_1. There are non standard proofs of G. *)
Lemma IamNotProvableTrueEquiv
  : forall (IsAxiom : nat -> bool) IsAxiomRep (InterpArith : nat -> nat)
      (InterpArithRepr : FunctionRepresented 1 InterpArith)
      varValues,
    let G := IamNotProvable IsAxiom IsAxiomRep InterpArithRepr in
    ((~IsProved IsAxiom (InterpArith G)) <-> HAstandardModel G varValues).
Proof.
  intros IsAxiom IsAxiomRep InterpArith InterpArithRepr varValues.
  simpl.
  pose (IamNotProvable IsAxiom IsAxiomRep InterpArithRepr) as g.
  fold g.
  pose proof (IamNotProvable_spec
                IsAxiom IsAxiomRep _ (fr_propprop _ _ InterpArithRepr)
                (fr_vars _ _ InterpArithRepr))
    as gequiv.
  simpl in gequiv. fold g in gequiv.
  pose proof (IsProvedArith_sat
                IsAxiom IsAxiomRep InterpArithRepr InterpArith g varValues
                (fr_propprop _ _ InterpArithRepr) (fr_rep _ _ InterpArithRepr))
    as gprovable.
  pose proof (HAstandardModel_correction
                IsWeakHeytingAxiom _ HAaxiomsSatisfied gequiv) as H.
  split.
  - intros gtrue.
    specialize (H varValues).
    rewrite HAstandardModel_equiv in H. rewrite H.
    destruct gprovable as [_ H0].
    rewrite HAstandardModel_Subst, HAstandardModel_not.
    intro gsat.
    contradict gtrue. apply H0.
    rewrite HAstandardModel_Subst. exact gsat.
    apply IsFreeForSubst_PAnat.
    apply IsProvedArithIsLprop, fr_propprop.
    apply IsFreeForSubst_PAnat.
    rewrite IsLproposition_not.
    apply IsProvedArithIsLprop, fr_propprop.
  - intros gtrue proof.
    destruct gprovable as [H0 _].
    specialize (H0 proof).
    specialize (H varValues).
    rewrite HAstandardModel_equiv in H.
    destruct H as [H _]. specialize (H gtrue).
    rewrite Subst_not, HAstandardModel_not in H.
    contradiction.
Qed.

(* If IsAxiom proves IamNotProvable, then by IamNotProvable_spec
   IsAxiom also proves ~IamNotProvable, which is a contradiction in IsAxiom. *)
Lemma IamNotProvableNotProvable
  : forall (IsAxiom : nat -> bool) IsAxiomRep (InterpArith : nat -> nat)
      (InterpArithRepr : FunctionRepresented 1 InterpArith),
    (forall prop : nat, IsProved IsWeakHeytingAxiom prop
                 -> IsProved IsAxiom (InterpArith prop))
    -> (forall prop, IsLproposition prop = true
               -> InterpArith (Lnot prop) = Lnot (InterpArith prop))
    -> IsProved IsAxiom (InterpArith (IamNotProvable IsAxiom IsAxiomRep InterpArithRepr))
    -> IsInconsistent IsAxiom.
Proof.
  intros IsAxiom IsAxiomRep InterpArith InterpArithRepr.
  intros IsAxiomExtendsHA InterpNot liarproof.
  pose (IamNotProvable IsAxiom IsAxiomRep InterpArithRepr) as G.
  apply (FalseElim IsAxiom (InterpArith G)).
  2: rewrite IsLproposition_not, IsLproposition_eq, IsLterm_var; reflexivity.
  apply LandIntro. exact liarproof.
  (* Proof of IsProved IsAxiom (Lnot (InterpArith G)).
     By extension of Heyting arithmetic, it suffices to prove
     IsProved IsWeakHeytingAxiom (Lnot G). *)
  rewrite <- InterpNot.
  2: apply GodelFormulaIsLproposition; rewrite IsLproposition_not
  ; apply IsProvedArithIsLprop, fr_propprop.
  apply IsAxiomExtendsHA.
  pose proof (IamNotProvable_spec
                IsAxiom IsAxiomRep _ (fr_propprop _ _ InterpArithRepr)
                (fr_vars _ _ InterpArithRepr))
    as H.
  simpl in H. fold G in H. rewrite Subst_not in H.
  apply LandElim1, IsProvedContraposition in H.
  apply (LimpliesElim _ _ _ H). clear H.
  apply LnotLnotIntro.
  (* Proof of
     IsProved IsWeakHeytingAxiom
              (Subst (PAnat G) 0 (IsProvedArith IsAxiom InterpArithLprop))
     which is the arithmetization of IsProved IsAxiom (InterpArith G). *)
  fold G in liarproof.
  apply (ArithmetizeProof IsAxiom IsAxiomRep) in liarproof.
  pose proof (ComposePropFuncSpec
                (IsProvedAsLprop IsAxiom IsAxiomRep) InterpArith G InterpArithRepr
                (IsProvedAsLpropIsLproposition IsAxiom IsAxiomRep)
                (IsProvedAsLpropVars _ _)) as H.
  apply LandElim1 in H.
  apply (LimpliesElim _ _ _ H).
  exact liarproof.
Qed.

(* The contraposition of the previous lemma, which is the usual way of
   phrasing that Gödel's sentence is not provable. Constructively this lemma
   is slightly weaker. *)
Lemma IamNotProvableNotProvableConsistent
  : forall (IsAxiom : nat -> bool) IsAxiomRep (InterpArith : nat -> nat)
      (InterpArithRepr : FunctionRepresented 1 InterpArith),
    (forall prop : nat, IsProved IsWeakHeytingAxiom prop
                 -> IsProved IsAxiom (InterpArith prop))
    -> (forall prop, IsLproposition prop = true
               -> InterpArith (Lnot prop) = Lnot (InterpArith prop))
    -> IsConsistent IsAxiom
    -> ~IsProved IsAxiom (InterpArith (IamNotProvable IsAxiom IsAxiomRep InterpArithRepr)).
Proof.
  intros. intro abs.
  pose proof (IamNotProvableNotProvable
                IsAxiom IsAxiomRep InterpArith InterpArithRepr H H0 abs).
  contradiction.
Qed.

(* Change the previous conclusion "IamNotProvable is not proved by IsAxiom"
   into the equivalent "IamNotProvable is true". *)
Lemma IamNotProvableTrue
  : forall (IsAxiom : nat -> bool) IsAxiomRep (InterpArith : nat -> nat)
      (InterpArithRepr : FunctionRepresented 1 InterpArith),
    (forall prop : nat, IsProved IsWeakHeytingAxiom prop
                 -> IsProved IsAxiom (InterpArith prop))
    -> (forall prop, IsLproposition prop = true
               -> InterpArith (Lnot prop) = Lnot (InterpArith prop))
    -> IsConsistent IsAxiom
    -> HAstandardModelSat (IamNotProvable IsAxiom IsAxiomRep InterpArithRepr).
Proof.
  intros. intro varValues.
  apply (IamNotProvableTrueEquiv _ _ _ InterpArithRepr).
  exact (IamNotProvableNotProvableConsistent _ _ _ _ H H0 H1).
Qed.

(* Variant of the previous lemma where IsAxiom is a sub-theory of true
   arithmetic (instead of an extension of IsWeakHeytingAxiom).
   Its consistency is given by the standard model of arithmetic. *)
Lemma IamNotProvableSubTrueArith : forall (IsAxiom : nat -> bool) IsAxiomRep,
    (forall ax:nat, IsAxiom ax = true -> HAstandardModelSat ax)
    -> HAstandardModelSat (IamNotProvable IsAxiom IsAxiomRep IdRepresented).
Proof.
  (* By contradiction : if there was a proof of IamNotProvable by IsAxiom,
     then IamNotProvable would be true in the standard model of arithmetic.
     But then the initial proof would not exist. *)
  intros IsAxiom IsAxiomRep IsAxiomSat varValues.
  apply (IamNotProvableTrueEquiv _ _ _ IdRepresented).
  intro proofG.
  pose proof (HAstandardModel_correction IsAxiom _ IsAxiomSat proofG) as H.
  specialize (H varValues).
  rewrite <- (IamNotProvableTrueEquiv _ _ _ IdRepresented) in H.
  contradiction.
Qed.

Lemma IsWeakHeytingAxiomRep : FunctionRepresentedBool 1 IsWeakHeytingAxiom.
Proof.
  apply (OrRepresented 1).
  apply (OrRepresented 1).
  apply (OrRepresented 1).
  apply (OrRepresented 1).
  apply (OrRepresented 1).
  apply (OrRepresented 1).
  apply (OrRepresented 1).
  - apply (EqbRepresented 1).
    apply (proj_represented 1 0); auto.
    apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply ComposeRepr_11. exact Lnot_repr.
    apply ComposeRepr_21. exact Leq_repr.
    apply ComposeRepr_21. exact Lop1_repr.
    apply (ConstantRepresented 0).
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 0).
    apply ComposeRepr_21. exact Lop_repr.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply (proj_represented 1 0); auto.
    apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
    apply ComposeRepr_21. exact ConsNat_repr.
    2: apply (ConstantRepresented 0).
    apply ComposeRepr_21. exact Lor_repr.
    apply ComposeRepr_21. exact Leq_repr.
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented PAzero).
    apply ComposeRepr_21. exact Lexists_repr.
    apply (ConstantRepresented 1).
    apply ComposeRepr_21. exact Leq_repr.
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 0).
    unfold PAsucc.
    apply ComposeRepr_21. exact Lop1_repr.
    apply (ConstantRepresented 0).
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 1).
  - apply (EqbRepresented 1).
    apply (proj_represented 1 0); auto.
    apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply ComposeRepr_21. exact Lforall_repr.
    apply (ConstantRepresented 1).
    apply ComposeRepr_21. exact Limplies_repr.
    apply ComposeRepr_21. exact Leq_repr.
    apply ComposeRepr_21. exact Lop1_repr.
    apply (ConstantRepresented 0).
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 0).
    apply ComposeRepr_21. exact Lop1_repr.
    apply (ConstantRepresented 0).
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 1).
    apply ComposeRepr_21. exact Leq_repr.
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 0).
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 1).
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply (proj_represented 1 0); auto.
    apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply ComposeRepr_21. exact Leq_repr.
    apply ComposeRepr_21.
    apply ComposeRepr_32. exact Lop2_repr.
    apply (ConstantRepresented 0).
    apply (proj_represented 2 0); auto.
    apply (proj_represented 2 1); auto.
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented PAzero).
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply (proj_represented 1 0); auto.
    apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply ComposeRepr_21. exact Lforall_repr.
    apply (ConstantRepresented 1).
    apply ComposeRepr_21. exact Leq_repr.
    apply ComposeRepr_21.
    apply ComposeRepr_32. exact Lop2_repr.
    apply (ConstantRepresented 0).
    apply (proj_represented 2 0); auto.
    apply (proj_represented 2 1); auto.
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 0).
    apply ComposeRepr_21. exact Lop1_repr.
    apply (ConstantRepresented 0).
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 1).
    apply ComposeRepr_21. exact Lop1_repr.
    apply (ConstantRepresented 0).
    apply ComposeRepr_31. exact Lop2_repr.
    apply (ConstantRepresented 0).
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 0).
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 1).
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply (proj_represented 1 0); auto.
    apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply ComposeRepr_21. exact Leq_repr.
    apply ComposeRepr_21. 
    apply ComposeRepr_32. exact Lop2_repr.
    apply (ConstantRepresented 1).
    apply (proj_represented 2 0); auto.
    apply (proj_represented 2 1); auto.
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented PAzero).
    apply (ConstantRepresented PAzero).
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply (proj_represented 1 0); auto.
    apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply ComposeRepr_21. exact Lforall_repr.
    apply (ConstantRepresented 1).
    apply ComposeRepr_21. exact Leq_repr.
    apply ComposeRepr_21. 
    apply ComposeRepr_32. exact Lop2_repr.
    apply (ConstantRepresented 1).
    apply (proj_represented 2 0); auto.
    apply (proj_represented 2 1); auto.
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 0).
    apply ComposeRepr_11.
    apply ComposeRepr_21. exact Lop1_repr.
    apply (ConstantRepresented 0).
    apply (proj_represented 1 0); auto.
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 1).
    apply ComposeRepr_11.
    apply ComposeRepr_21.
    apply ComposeRepr_32. exact Lop2_repr.
    apply (ConstantRepresented 0).
    apply (proj_represented 2 0); auto.
    apply (proj_represented 2 1); auto.
    apply ComposeRepr_21.
    apply ComposeRepr_32. exact Lop2_repr.
    apply (ConstantRepresented 1).
    apply (proj_represented 2 0); auto.
    apply (proj_represented 2 1); auto.
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 0).
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 1).
    apply (proj_represented 1 0); auto.
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 0).
    apply (ConstantRepresented 0).
  - apply (EqbRepresented 1).
    apply (proj_represented 1 0); auto.
    apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
    apply (ComposeRepr_11 _ _ (ConsNat_fst_repr _)).
    apply ComposeRepr_21. exact ConsNat_repr.
    apply ComposeRepr_21. exact Lforall_repr.
    apply (ConstantRepresented 1).
    apply ComposeRepr_21.
    apply (ComposeRepr_22 _ _ _ Land_repr).
    exact Limplies_repr.
    apply ComposeRepr_22. exact Limplies_repr.
    apply (proj_represented 2 1); auto.
    apply (proj_represented 2 0); auto.
    apply ComposeRepr_21. 
    apply ComposeRepr_32. exact Lrel2_repr.
    apply (ConstantRepresented 1).
    apply (proj_represented 2 0); auto.
    apply (proj_represented 2 1); auto.
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 0).
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 1).
    apply ComposeRepr_21. exact Lexists_repr.
    apply (ConstantRepresented 2).
    apply ComposeRepr_21. exact Leq_repr.
    apply ComposeRepr_21.
    apply ComposeRepr_32. exact Lop2_repr.
    apply (ConstantRepresented 0).
    apply (proj_represented 2 0); auto.
    apply (proj_represented 2 1); auto.
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 2).
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 0).
    apply ComposeRepr_11. exact Lvar_repr.
    apply (ConstantRepresented 1).
    apply (ConstantRepresented 0). 
Qed.

Lemma IamNotProvableHeytingTrue
  : HAstandardModelSat (IamNotProvable _ IsWeakHeytingAxiomRep IdRepresented).
Proof.
  apply IamNotProvableSubTrueArith.
  intros ax H.
  apply (HAstandardModel_correction _ _ HAaxiomsSatisfied).
  apply AxiomIsProved. exact H.
  apply PAaxiomIsLproposition.
  unfold IsWeakPeanoAxiom. rewrite H. reflexivity.
Qed.

(* Here we use a model of IsAxiom that satisfies IamNotProvable.
   A syntactical proof is also possible. *)
Lemma IamNotProvableNotRefutable : forall (IsAxiom : nat -> bool) IsAxiomRep,
    (forall n:nat, IsAxiom n = true -> HAstandardModelSat n)
    -> forall n, IsProof IsAxiom (Lnot (IamNotProvable IsAxiom IsAxiomRep IdRepresented)) n = false.
Proof.
  intros.
  destruct (IsProof IsAxiom (Lnot (IamNotProvable IsAxiom IsAxiomRep IdRepresented)) n) eqn:des.
  2: reflexivity.
  exfalso.
  assert (IsProved IsAxiom (Lnot (IamNotProvable IsAxiom IsAxiomRep IdRepresented))).
  { exists n. exact des. }
  pose proof (HAstandardModel_correction IsAxiom _ H H0 (fun _ => 0)).
  rewrite HAstandardModel_not in H1.
  contradict H1. apply IamNotProvableSubTrueArith, H.
Qed.

Lemma IsWeakPeanoAxiomRep : FunctionRepresentedBool 1 IsWeakPeanoAxiom.
Proof.
  apply (OrRepresented 1 _ _ IsWeakHeytingAxiomRep).
  exact IsPropAx4_repr.
Qed. 

(* Peano's G is also true, because PA is a consistent extension of HA. *)
Lemma IamNotProvablePeanoTrue
  : HAstandardModelSat (IamNotProvable _ IsWeakPeanoAxiomRep IdRepresented).
Proof.
  intro varValues.
  apply (IamNotProvableTrueEquiv _ _ _ IdRepresented).
  intro proofG.
  apply (IamNotProvableNotProvable IsWeakPeanoAxiom _ _ IdRepresented) in proofG.
  exact (PAconsistent proofG).
  intros. apply (WeakenProvable IsWeakHeytingAxiom IsWeakPeanoAxiom).
  intros. unfold IsWeakPeanoAxiom. rewrite H0. reflexivity. exact H.
  reflexivity.
Qed.
