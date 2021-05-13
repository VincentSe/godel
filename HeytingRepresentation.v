(** The axioms of Heyting arithmetic intend to describe natural numbers,
    functions are not directly available as values for variables.
    However, Heyting arithmetic can emulate functions with propositions :
    we say that an arithmetic proposition P represents a function f:nat->nat
    when P(x,y) is equivalent to f(x) = y. Those propositions P are sometimes
    called functional classes, because they satisfy the functional property :
    P(x,y) /\ P(x,z) -> y = z.
    A theorem states that all computable functions are represented by Sigma_1
    arithmetic formulas. We won't prove this theorem though, and merely show
    that all functions until IsProof are represented. *)

Require Import Arith.Compare_dec.
Require Import Numbers.NaryFunctions.
Require Import PeanoNat.
Require Import EnumSeqNat.
Require Import Formulas.
Require Import Substitutions.
Require Import IsFreeForSubst.
Require Import Proofs.
Require Import PeanoAxioms.
Require Import ProofTactics.
Require Import HeytingModel.

Fixpoint nfun_eval (arity x : nat) (f : nfun nat arity nat) { struct arity } : nat.
Proof.
  destruct arity.
  - exact f.
  - exact (nfun_eval arity (TailNat x) (f (CoordNat x 0))).
Defined.

(* x is a sequence of natural numbers, substituted for the free variables of prop,
   up to Lvar arity excluded. *)
Fixpoint nprop_subst (arity i x prop : nat) { struct arity } : nat.
Proof.
  destruct arity.
  - exact prop.
  - exact (nprop_subst arity (S i) x (Subst (PAnat (CoordNat x i)) i prop)).
Defined.

(* prop could be required Sigma_1 in this definition. However, even with a
   Sigma_1 prop, Lforall arity makes this representation formula Pi_2 and
   we cannot weaken it to a satisfaction in the standard model of arithmetic. *)
Definition FormulaRepresents (arity : nat) (u : nfun nat arity nat) (prop : nat) : Prop :=
  forall args:nat,
    IsProved IsWeakHeytingAxiom
             (Lforall arity (Lequiv (nprop_subst arity 0 args prop)
                                    (Leq (Lvar arity)
                                         (PAnat (nfun_eval arity args u))))).

(* All functions defined in Coq without axioms are computable, so they are
   represented by arithmetic propositions. But this theorem cannot be proved
   in Coq so we must reprove it for each function that interests us.
   We could also add in this record that fr_prop is Sigma_1. *)
Record FunctionRepresented (arity : nat) (u : nfun nat arity nat) : Set :=
  {
  fr_prop :> nat;
  fr_rep : FormulaRepresents arity u fr_prop;
  fr_propprop : IsLproposition fr_prop = true;
  fr_vars : forall v:nat, arity < v -> VarOccursFreeInFormula v fr_prop = false;
  (* lemma fr_freevar below will add
     VarOccursFreeInFormula arity fr_prop = true *)
  }.

Lemma nprop_subst_IsLprop : forall arity prop args i,
    IsLproposition prop = true
    -> IsLproposition (nprop_subst arity i args prop) = true.
Proof.
  induction arity.
  - intros. exact H.
  - intros. simpl. rewrite IHarity. reflexivity.
    apply SubstIsLproposition. exact H. apply IsLterm_PAnat.
Qed.

(* Lift the equivalence in the meta-theory *)
Lemma FormulaRepresents_alt : forall arity (u : nfun nat arity nat) (prop args : nat),
    FormulaRepresents arity u prop
    -> IsLproposition prop = true
    -> (forall j, nfun_eval arity args u = j
            <-> IsProved IsWeakHeytingAxiom
                       (Subst (PAnat j) arity (nprop_subst arity 0 args prop))).
Proof.
  intros arity u prop args urep propprop j. specialize (urep args).
  apply (LforallElim IsWeakHeytingAxiom _ arity (PAnat j)) in urep.
  rewrite Subst_equiv, Subst_eq, SubstTerm_var, Nat.eqb_refl in urep.
  rewrite SubstTerm_PAnat in urep.
  split.
  - intro uj. subst j.
    apply LandElim2 in urep.
    apply (LimpliesElim _ (Leq (PAnat (nfun_eval arity args u))
                               (PAnat (nfun_eval arity args u)))).
    exact urep. apply LeqRefl. apply IsLterm_PAnat.
  - intro uj.
    apply LandElim1 in urep.
    pose proof (LimpliesElim _ _ _ urep uj) as H0. clear urep uj.
    apply HAstandardModel_correction in H0. 2: exact HAaxiomsSatisfied.
    specialize (H0 (fun _ => 0)).
    rewrite HAstandardModel_eq in H0.
    rewrite HAstandardModelTerm_PAnat, HAstandardModelTerm_PAnat in H0.
    symmetry. exact H0.
  - apply IsLterm_PAnat.
  - apply IsFreeForSubst_PAnat.
    rewrite IsLproposition_equiv, nprop_subst_IsLprop, IsLproposition_eq.
    rewrite IsLterm_var, IsLterm_PAnat. reflexivity.
    exact propprop.
Qed.

(* Functions are represented by Sigma_1 formulas, and those are provable
   iff they are true in the standard model of arithmetic. *)
Lemma FormulaRepresents_sat : forall arity (u : nfun nat arity nat) (prop args : nat),
    FormulaRepresents arity u prop
    -> IsLproposition prop = true
    -> (forall j varValues,
          nfun_eval arity args u = j
          <-> HAstandardModel (Subst (PAnat j) arity (nprop_subst arity 0 args prop))
                            varValues).
Proof.
  intros arity u prop args urep propprop j varValues.
  specialize (urep args).
  apply (LforallElim _ _ arity (PAnat j)) in urep.
  split.
  - intro uj. subst j.
    apply HAstandardModel_correction in urep. 2: exact HAaxiomsSatisfied.
    specialize (urep varValues).
    rewrite Subst_equiv, HAstandardModel_equiv in urep.
    destruct urep as [_ urep]. apply urep.
    rewrite HAstandardModel_Subst, HAstandardModel_eq.
    rewrite HAstandardModelTerm_PAnat, HAstandardModelTerm_PAnat.
    rewrite HAstandardModelTerm_var. 
    unfold setValue. rewrite Nat.eqb_refl. reflexivity.
    apply IsFreeForSubst_PAnat.
    rewrite IsLproposition_eq, IsLterm_var, IsLterm_PAnat. reflexivity.
  - intro uj.
    rewrite Subst_equiv in urep.
    apply LandElim1 in urep.
    apply HAstandardModel_correction in urep. 2: exact HAaxiomsSatisfied.
    specialize (urep varValues).
    rewrite HAstandardModel_implies in urep.
    specialize (urep uj). clear uj.
    rewrite Subst_eq, SubstTerm_var, SubstTerm_PAnat in urep. simpl in urep.
    rewrite HAstandardModel_eq, Nat.eqb_refl in urep.
    rewrite HAstandardModelTerm_PAnat, HAstandardModelTerm_PAnat in urep.
    symmetry. exact urep.
  - apply IsLterm_PAnat.
  - apply IsFreeForSubst_PAnat.
    rewrite IsLproposition_equiv.
    apply andb_true_intro. split.
    apply nprop_subst_IsLprop. exact propprop.
    rewrite IsLproposition_eq, IsLterm_var, IsLterm_PAnat. reflexivity.
Qed.

Lemma nprop_subst_closed : forall arity i args prop v,
    IsLproposition prop = true
    -> VarOccursFreeInFormula v prop = false
    -> VarOccursFreeInFormula v (nprop_subst arity i args prop) = false.
Proof.
  induction arity. intros. exact H0.
  intros. simpl. rewrite IHarity. reflexivity.
  apply SubstIsLproposition. exact H. apply IsLterm_PAnat.
  destruct (Nat.eq_dec v i). subst i.
  rewrite VarOccursFreeInFormula_SubstIdem. reflexivity.
  exact H. apply PAnat_closed.
  rewrite VarOccursFreeInFormula_SubstDiff. exact H0.
  exact H. exact n. apply PAnat_closed.
Qed. 

Lemma fr_freevar : forall arity u (urep : FunctionRepresented arity u),
    VarOccursFreeInFormula arity urep = true.
Proof.
  intros. destruct (VarOccursFreeInFormula arity urep) eqn:nooccur.
  reflexivity. exfalso.
  pose proof (FormulaRepresents_sat
                _ u _ 0 (fr_rep _ _ urep) (fr_propprop _ _ urep)).
  assert (exists k:nat, k <> nfun_eval arity 0 u).
  { destruct (nfun_eval arity 0 u). exists 1. discriminate.
    exists 0. discriminate. }
  assert (VarOccursFreeInFormula arity (nprop_subst arity 0 0 urep) = false)
    as substnoc.
  { apply nprop_subst_closed. apply fr_propprop. exact nooccur. }
  destruct H0 as [k kneq].
  pose proof (H (nfun_eval arity 0 u) (fun _ => 0)) as [H0 _].
  specialize (H0 eq_refl).
  rewrite Subst_nosubst in H0. 2: exact substnoc. 
  pose proof (H k (fun _ => 0)) as [_ H1].
  rewrite Subst_nosubst in H1. 2: exact substnoc. 
  specialize (H1 H0). rewrite H1 in kneq. apply kneq. reflexivity. 
Qed.
 
Lemma IdRepresented : FunctionRepresented 1 (fun n:nat => n).
Proof.
  apply (Build_FunctionRepresented 1 _ (Leq (Lvar 1) (Lvar 0))).
  - intros k. apply LforallIntro. simpl.
    rewrite Subst_eq, SubstTerm_var, SubstTerm_var; simpl.
    apply LequivRefl.
    rewrite IsLproposition_eq, IsLterm_var, IsLterm_PAnat.
    reflexivity.
  - rewrite IsLproposition_eq, IsLterm_var, IsLterm_var. reflexivity.
  - intros. unfold Leq. rewrite VarOccursFreeInFormula_rel2.
    rewrite VarOccursInTerm_var, VarOccursInTerm_var.
    destruct v. inversion H. destruct v. apply le_S_n in H. inversion H.
    reflexivity. 
Qed.

Lemma SuccessorRepresented : FunctionRepresented 1 S.
Proof.
  apply (Build_FunctionRepresented 1 _ (Leq (Lvar 1) (PAsucc (Lvar 0)))).
  - intros k. apply LforallIntro. simpl.
    rewrite Subst_eq, SubstTerm_var,
    SubstTerm_PAsucc, SubstTerm_var; simpl.
    apply LequivRefl.
    unfold PAsucc.
    rewrite IsLproposition_eq, IsLterm_var, IsLterm_op1. apply IsLterm_PAnat.
  - unfold PAsucc.
    rewrite IsLproposition_eq, IsLterm_var, IsLterm_op1. apply IsLterm_var.
  - intros. unfold Leq. rewrite VarOccursFreeInFormula_rel2.
    unfold PAsucc.
    rewrite VarOccursInTerm_var, VarOccursInTerm_op1, VarOccursInTerm_var.
    destruct v. inversion H. destruct v. apply le_S_n in H. inversion H.
    reflexivity.
Qed.

Lemma AdditionRepresented : FunctionRepresented 2 Nat.add.
Proof.
  apply (Build_FunctionRepresented 2 _ (Leq (Lvar 2) (PAplus (Lvar 0) (Lvar 1)))).
  - intros args. simpl. rewrite CoordTailNat.
    remember (CoordNat args 0) as i.
    remember (CoordNat args 1) as j.
    apply LforallIntro.
    rewrite Subst_eq, SubstTerm_var. simpl.
    rewrite Subst_eq, SubstTerm_var. simpl.
    rewrite SubstTerm_PAplus, SubstTerm_var. simpl.
    rewrite SubstTerm_PAplus, SubstTerm_var. simpl.
    rewrite SubstTerm_var. simpl.
    rewrite SubstTerm_PAnat.
    apply (LeqElim_rel2 _ 0). apply LeqRefl. apply IsLterm_var.
    apply PAplus_normalize.
  - rewrite IsLproposition_eq, IsLterm_var. simpl.
    unfold PAplus. rewrite IsLterm_op2.
    rewrite IsLterm_var, IsLterm_var. reflexivity.
  - intros. unfold Leq. rewrite VarOccursFreeInFormula_rel2.
    unfold PAplus.
    rewrite VarOccursInTerm_var, VarOccursInTerm_op2, VarOccursInTerm_var.
    rewrite VarOccursInTerm_var.
    destruct v. inversion H.
    destruct v. apply le_S_n in H. inversion H.
    destruct v. apply le_S_n, le_S_n in H. inversion H.
    reflexivity. 
Qed.

Lemma MultiplicationRepresented : FunctionRepresented 2 Nat.mul.
Proof.
  apply (Build_FunctionRepresented 2 _ (Leq (Lvar 2) (PAmult (Lvar 0) (Lvar 1)))).
  - intros args. simpl. rewrite CoordTailNat.
    remember (CoordNat args 0) as i.
    remember (CoordNat args 1) as j.
    apply LforallIntro.
    rewrite Subst_eq, SubstTerm_var. simpl.
    rewrite Subst_eq, SubstTerm_var. simpl.
    rewrite SubstTerm_PAmult, SubstTerm_var. simpl.
    rewrite SubstTerm_PAmult, SubstTerm_var. simpl.
    rewrite SubstTerm_var. simpl.
    rewrite SubstTerm_PAnat.
    apply (LeqElim_rel2 _ 0). apply LeqRefl. apply IsLterm_var.
    apply PAmult_normalize.
  - rewrite IsLproposition_eq, IsLterm_var. simpl.
    unfold PAmult. rewrite IsLterm_op2.
    rewrite IsLterm_var, IsLterm_var. reflexivity.
  - intros. unfold Leq. rewrite VarOccursFreeInFormula_rel2.
    unfold PAmult.
    rewrite VarOccursInTerm_var, VarOccursInTerm_op2, VarOccursInTerm_var.
    rewrite VarOccursInTerm_var.
    destruct v. inversion H.
    destruct v. apply le_S_n in H. inversion H.
    destruct v. apply le_S_n, le_S_n in H. inversion H.
    reflexivity. 
Qed.

(* 
Definition IsDelta0Rec (f : nat) (rec : nat -> bool) : bool :=
  match CoordNat f 0 with
  | LnotHead => rec 1
  | LimpliesHead
  | LorHead
  | LandHead => rec 1 && rec 2
  | LforallHead => (* forall Xn, Xn <= t -> ... *)
    (IsLimplies (CoordNat f 2)
     && Nat.eqb (CoordNat (CoordNat f 2) 1)
                (PAle (CoordNat (CoordNat (CoordNat f 2) 1) 2)
                      (CoordNat (CoordNat (CoordNat f 2) 1) 3))
     && negb (VarOccursInTerm (CoordNat f 1)
                              (CoordNat (CoordNat (CoordNat f 2) 1) 1)))%bool
  | LexistsHead =>
    (IsLand (CoordNat f 2)
     && Nat.eqb (CoordNat (CoordNat f 2) 1)
                (PAle (CoordNat (CoordNat (CoordNat f 2) 1) 2)
                      (CoordNat (CoordNat (CoordNat f 2) 1) 3))
     && negb (VarOccursInTerm (CoordNat f 1)
                              (CoordNat (CoordNat (CoordNat f 2) 1) 1)))%bool
  | LrelHead => true
  | _ => false
  end.

Definition IsDelta0 : nat -> bool := TreeFoldNat IsDelta0Rec false.

Definition IsSigma1Rec (f : nat) (rec : nat -> bool) : bool :=
  match CoordNat f 0 with
  | LnotHead
  | LimpliesHead
  | LorHead
  | LandHead
  | LforallHead => IsDelta0 f
  | LexistsHead => rec 1
  | LrelHead => true
  | _ => false
  end.

Definition IsSigma1 : nat -> bool := TreeFoldNat IsSigma1Rec false.

Definition IsPi1Rec (f : nat) (rec : nat -> bool) : bool :=
  match CoordNat f 0 with
  | LnotHead
  | LimpliesHead
  | LorHead
  | LandHead
  | LforallHead => rec 1
  | LexistsHead => IsDelta0 f
  | LrelHead => true
  | _ => false
  end.

Definition IsPi1 : nat -> bool := TreeFoldNat IsPi1Rec false.
*)


(* Compose the formulas representing functions A and B.
   B represents a nat^Barity -> nat function,
   is applied first and feeds the Avar-th variable of A.
   This works when Barity <= Aarity, otherwise Aarity must
   be incremented to Barity before using this, see
   IncrOutputVarRepr below. *)
Definition ComposeRepr (Aprop Avar Bprop Barity : nat) : nat :=
  let m := S (Nat.max (MaxVar Bprop) (MaxVar Aprop)) in
  Lexists m (Land (Subst (Lvar m) Barity Bprop)
                  (Subst (Lvar m) Avar Aprop)).

(* TODO
(* Formula that represents the composition A(B_1,...,B_k)
   where k is the arity of A and all the B_i's have the same arity. *)
Definition ComposeRepr (Aprop Aarity Bprops Barity : nat) : nat :=
*)

Lemma ComposeReprLprop : forall A Avar B Barity,
    IsLproposition A = true
    -> IsLproposition B = true
    -> IsLproposition (ComposeRepr A Avar B Barity) = true.
Proof.
  intros.
  unfold ComposeRepr.
  rewrite IsLproposition_exists, IsLproposition_and.
  rewrite SubstIsLproposition, SubstIsLproposition. reflexivity.
  exact H. apply IsLterm_var. exact H0. apply IsLterm_var.
Qed.

Lemma ComposeReprVars : forall A Avar B Barity v,
    IsLproposition A = true
    -> IsLproposition B = true
    -> VarOccursFreeInFormula v (ComposeRepr A Avar B Barity)
      = ((VarOccursFreeInFormula v A && negb (Nat.eqb v Avar))
         || (VarOccursFreeInFormula v B && negb (Nat.eqb v Barity)))%bool.
Proof.
  intros.
  unfold ComposeRepr.
  rewrite VarOccursFreeInFormula_exists.
  destruct (v =? S (Nat.max (MaxVar B) (MaxVar A))) eqn:des.
  - simpl. apply Nat.eqb_eq in des. subst v.
    rewrite MaxVarDoesNotOccurFree, MaxVarDoesNotOccurFree.
    reflexivity. exact H0.
    apply le_n_S, Nat.le_max_l.
    exact H. apply le_n_S, Nat.le_max_r.
  - simpl. rewrite VarOccursFreeInFormula_and.
    rewrite Bool.orb_comm. apply f_equal2.
    + destruct (v =? Avar) eqn:vzero.
      apply Nat.eqb_eq in vzero. subst v.
      rewrite VarOccursFreeInFormula_SubstIdem.
      simpl. rewrite Bool.andb_false_r. reflexivity.
      exact H.
      rewrite VarOccursInTerm_var. exact des.
      simpl. rewrite Bool.andb_true_r.
      rewrite VarOccursFreeInFormula_SubstDiff. reflexivity.
      exact H. apply Nat.eqb_neq in vzero. exact vzero.
      rewrite VarOccursInTerm_var. exact des.
    + destruct (v =? Barity) eqn:varity.
      simpl. rewrite Bool.andb_false_r. 
      apply Nat.eqb_eq in varity. subst v.
      rewrite VarOccursFreeInFormula_SubstIdem.
      reflexivity. exact H0.
      rewrite VarOccursInTerm_var. exact des.
      simpl. rewrite Bool.andb_true_r.
      rewrite VarOccursFreeInFormula_SubstDiff. reflexivity.
      exact H0. apply Nat.eqb_neq in varity. exact varity.
      rewrite VarOccursInTerm_var. exact des.
Qed.

(* Probably an equivalence... *)
Lemma ComposeRepr_sat : forall Aprop (B : nat -> nat) (Bprop prop : nat) varValues,
    IsLproposition Aprop = true
    -> IsLproposition Bprop = true
    -> FormulaRepresents 1 B Bprop
    -> (HAstandardModel (Subst (PAnat (B prop)) 0 Aprop) varValues
       <-> HAstandardModel (Subst (PAnat prop) 0 (ComposeRepr Aprop 0 Bprop 1)) varValues).
Proof.
  intros Aprop B Bprop prop varValues Apropprop Bpropprop Brep.
  pose (Nat.max (MaxVar Bprop) (MaxVar Aprop)) as m.
  split.
  - intro Asat.
    unfold ComposeRepr.
    pose proof FormulaRepresents_sat as toto. 
    pose proof (FormulaRepresents_sat
                  1 _ _ (ConsNat prop NilNat) Brep Bpropprop (B prop) varValues)
      as [rep _].
    simpl in rep. rewrite CoordConsHeadNat in rep.
    specialize (rep eq_refl).
    rewrite Subst_exists; simpl.
    rewrite Subst_and.
    rewrite HAstandardModel_exists. exists (B prop).
    rewrite HAstandardModel_and. split.
    + rewrite HAstandardModel_Subst, HAstandardModelTerm_PAnat in rep.
      rewrite SubstSubstDiffCommutes.
      rewrite HAstandardModel_Subst, HAstandardModelTerm_var.
      fold m.
      replace (setValue (S m) (B prop) varValues (S m)) with (B prop)
        by (unfold setValue; rewrite Nat.eqb_refl; reflexivity).
      rewrite (HAstandardModel_ext
                 _ _
                 (setValue (S m) (B prop) (setValue 1 (B prop) varValues))).
      rewrite VarIndep.
      exact rep.
      apply MaxVarDoesNotOccurFree.
      apply SubstIsLproposition. exact Bpropprop.
      apply IsLterm_PAnat.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      apply Nat.max_lub. rewrite MaxVarTerm_PAnat. apply le_0_n.
      apply Nat.le_max_l.
      intro n. destruct m. reflexivity.
      apply SetSetValueCommute; discriminate. 
      apply MaxVarFreeSubst_var.
      apply SubstIsLproposition. exact Bpropprop.
      apply IsLterm_PAnat.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      apply Nat.max_lub. rewrite MaxVarTerm_PAnat. apply le_0_n.
      apply Nat.le_max_l. discriminate.
      apply PAnat_closed.
      rewrite VarOccursInTerm_var. reflexivity.
      apply IsFreeForSubst_PAnat.
      apply SubstIsLproposition. exact Bpropprop. apply IsLterm_PAnat.
    + fold m.
      rewrite Subst_nosubst.
      rewrite HAstandardModel_Subst, HAstandardModelTerm_var.
      replace (setValue (S m) (B prop) varValues (S m)) with (B prop)
        by (unfold setValue; rewrite Nat.eqb_refl; reflexivity).
      rewrite HAstandardModel_Subst, HAstandardModelTerm_PAnat in Asat.
      rewrite (HAstandardModel_ext
                 _ _
                 (setValue (S m) (B prop) (setValue 0 (B prop) varValues)))
        by (apply SetSetValueCommute; discriminate). 
      rewrite VarIndep. exact Asat.
      apply MaxVarDoesNotOccurFree.
      exact Apropprop.
      apply le_n_S, Nat.le_max_r.
      apply IsFreeForSubst_PAnat.
      exact Apropprop.
      apply MaxVarFreeSubst_var.
      exact Apropprop.
      apply le_n_S, Nat.le_max_r.
      apply VarOccursFreeInFormula_SubstIdem.
      exact Apropprop.
      rewrite VarOccursInTerm_var. reflexivity.
  - intro Asat. unfold ComposeRepr in Asat.
    fold m in Asat.
    rewrite Subst_exists in Asat; simpl in Asat.
    rewrite HAstandardModel_exists in Asat.
    destruct Asat as [iap prf].
    rewrite Subst_and in prf.
    rewrite HAstandardModel_and in prf. destruct prf.
    rewrite SubstSubstIdem, SubstTerm_var in H0; simpl in H0.
    assert (B prop = iap).
    { pose proof (FormulaRepresents_sat 1
                    _ _ (ConsNat prop NilNat) Brep Bpropprop iap varValues) as [_ rep].
      simpl in rep. rewrite CoordConsHeadNat in rep.
      apply rep. clear rep.
      rewrite SubstSubstDiffCommutes, HAstandardModel_Subst in H.
      rewrite HAstandardModelTerm_var in H.
      rewrite HAstandardModel_Subst, HAstandardModelTerm_PAnat.
      replace (setValue (S m) iap varValues (S m))
        with iap in H
        by (unfold setValue; rewrite Nat.eqb_refl; reflexivity).
      rewrite (HAstandardModel_ext
                 _ _
                 (setValue (S m) iap (setValue 1 iap varValues))) in H.
      rewrite VarIndep in H. exact H.
      apply MaxVarDoesNotOccurFree.
      apply SubstIsLproposition. exact Bpropprop.
      apply IsLterm_PAnat.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      apply Nat.max_lub. rewrite MaxVarTerm_PAnat. apply le_0_n.
      apply Nat.le_max_l.
      intro n. destruct m. reflexivity. apply SetSetValueCommute. discriminate.
      apply IsFreeForSubst_PAnat.
      apply SubstIsLproposition. exact Bpropprop.
      apply IsLterm_PAnat.
      apply MaxVarFreeSubst_var.
      apply SubstIsLproposition. exact Bpropprop.
      apply IsLterm_PAnat.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
      apply Nat.max_lub. rewrite MaxVarTerm_PAnat. apply le_0_n.
      apply Nat.le_max_l. discriminate.
      apply PAnat_closed.
      rewrite VarOccursInTerm_var. reflexivity. }
    clear H. subst iap.
    rewrite HAstandardModel_Subst, HAstandardModelTerm_PAnat.
    rewrite HAstandardModel_Subst, HAstandardModelTerm_var in H0.
    replace (setValue (S m) (B prop) varValues (S m)) with (B prop) in H0
      by (unfold setValue; rewrite Nat.eqb_refl; reflexivity).
    rewrite (HAstandardModel_ext
               _ _
               (setValue (S m) (B prop) (setValue 0 (B prop) varValues)))
      in H0
      by (apply SetSetValueCommute; discriminate).
    rewrite VarIndep in H0. exact H0.
    apply MaxVarDoesNotOccurFree.
    exact Apropprop.
    apply le_n_S, Nat.le_max_r.
    apply MaxVarFreeSubst_var.
    apply Apropprop.
    apply le_n_S, Nat.le_max_r.
    apply IsFreeForSubst_PAnat.
    exact Apropprop.
Qed.

Lemma nprop_subst_exists : forall args arity i prop v,
    i + arity <= v
    -> nprop_subst arity i args (Lexists v prop)
      = Lexists v (nprop_subst arity i args prop).
Proof.
  induction arity; [reflexivity|].
  intros. simpl.
  replace (Subst (PAnat (CoordNat args i)) i (Lexists v prop))
    with (Lexists v (Subst (PAnat (CoordNat args i)) i prop)).
  rewrite IHarity. reflexivity.
  rewrite Nat.add_succ_r in H. exact H.
  rewrite Subst_exists.
  destruct (v =? i) eqn:des. 2: reflexivity.
  exfalso. apply Nat.eqb_eq in des. subst i.
  rewrite <- (Nat.add_0_r v) in H at 2.
  apply Nat.add_le_mono_l in H. inversion H.
Qed.

Lemma nprop_subst_and : forall args arity i f g,
    nprop_subst arity i args (Land f g)
    = Land (nprop_subst arity i args f) (nprop_subst arity i args g).
Proof.
  induction arity; [reflexivity|].
  intros. simpl.
  rewrite Subst_and, IHarity. reflexivity.
Qed.

Lemma nprop_subst_SubstDiffCommutes : forall arity i args prop v t,
    i + arity <= v
    -> (forall k, i <= k < arity + i -> VarOccursInTerm k t = false)
    -> Subst t v (nprop_subst arity i args prop)
      = nprop_subst arity i args (Subst t v prop).
Proof.
  induction arity; [reflexivity|].
  intros. simpl. rewrite IHarity.
  apply f_equal. apply SubstSubstDiffCommutes.
  intro abs. subst i. apply (Nat.lt_irrefl v).
  refine (Nat.lt_le_trans _ _ _ _ H). 
  rewrite Nat.add_succ_r. apply le_n_S.
  rewrite <- (Nat.add_0_r v) at 1.
  apply Nat.add_le_mono_l, le_0_n.
  apply H0. split. apply Nat.le_refl.
  simpl. apply le_n_S.
  rewrite <- (Nat.add_0_l i) at 1.
  apply Nat.add_le_mono_r, le_0_n.
  apply PAnat_closed.
  rewrite Nat.add_succ_r in H. exact H.
  intros k H1. apply H0. split. apply (Nat.le_trans _ (S i)).
  apply le_S, Nat.le_refl. apply H1.
  rewrite Nat.add_succ_r in H1. apply H1.
Qed.

Lemma nprop_subst_id : forall arity maxvar prop args i,
    (forall v, maxvar <= v < arity + i -> VarOccursFreeInFormula v prop = false)
    -> maxvar <= i
    -> nprop_subst arity i args prop = prop.
Proof.
  induction arity. reflexivity.
  intros. simpl. rewrite Subst_nosubst.
  apply (IHarity maxvar). intros.
  apply H. rewrite Nat.add_succ_r in H1. exact H1.
  apply (Nat.le_trans _ _ _ H0). apply le_S, Nat.le_refl.
  apply H. split. exact H0.
  simpl. apply le_n_S.
  rewrite <- (Nat.add_0_l i) at 1.
  apply Nat.add_le_mono_r, le_0_n.
Qed.

Lemma nprop_subst_truncate : forall arity maxvar prop args i,
    IsLproposition prop = true
    -> (forall v, maxvar <= v < arity + i -> VarOccursFreeInFormula v prop = false)
    -> nprop_subst arity i args prop
      = nprop_subst (Nat.min arity (maxvar - i)) i args prop.
Proof.
  induction arity ; [reflexivity|].
  intros maxvar prop args i propprop propclosed.
  destruct (le_lt_dec (S arity) (maxvar - i)).
  rewrite Nat.min_l. reflexivity. exact l.
  rewrite Nat.min_r. 2: apply Nat.lt_le_incl, l.
  simpl (nprop_subst (S arity) i args prop).
  destruct (le_lt_dec maxvar i).
  - replace (maxvar - i) with 0.
    change (nprop_subst (S arity) i args prop = prop).
    apply (nprop_subst_id _ maxvar).
    intros. apply propclosed. exact H. exact l0.
    symmetry. apply (Nat.sub_0_le maxvar i), l0.
  - rewrite (IHarity maxvar).
    rewrite Nat.min_r.
    change (nprop_subst (S (maxvar - S i)) i args prop
            = nprop_subst (maxvar - i) i args prop).
    replace (S (maxvar - S i)) with (maxvar - i). reflexivity.
    rewrite Nat.sub_succ_r.
    destruct (maxvar - i) eqn:des. 2: reflexivity. exfalso.
    apply Nat.sub_0_le in des.
    apply (Nat.lt_irrefl i).
    apply (Nat.lt_le_trans _ _ _ l0 des).
    apply le_S_n in l.
    refine (Nat.le_trans _ _ _ _ l).
    apply Nat.sub_le_mono_l. apply le_S, Nat.le_refl.
    apply SubstIsLproposition. exact propprop. apply IsLterm_PAnat.
    intros v H0.
    rewrite VarOccursFreeInFormula_SubstDiff.
    apply propclosed.
    rewrite Nat.add_succ_r in H0. exact H0.
    exact propprop.
    intro abs. subst i.
    apply (Nat.lt_irrefl v).
    apply (Nat.lt_le_trans _ _ _ l0 (proj1 H0)).
    apply PAnat_closed.
Qed.

Lemma MaxVar_nprop_subst : forall arity i args prop,
    MaxVar (nprop_subst arity i args prop) <= MaxVar prop.
Proof.
  induction arity; [reflexivity|].
  intros. simpl.
  apply (Nat.le_trans _ _ _ (IHarity (S i) _ _)).
  apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
  apply Nat.max_lub. rewrite MaxVarTerm_PAnat.
  apply le_0_n. apply Nat.le_refl.
Qed. 

(* TODO remove arityA. This assumes arityB <= arityA and just fills B's variables. *)
Lemma ComposeRepr_spec
  : forall IsAxiom Aprop Avar arityA arityB (B : nfun nat arityB nat)
      (args : nat) (Brep : FunctionRepresented arityB B),
    IsLproposition Aprop = true
    -> (forall n, IsWeakHeytingAxiom n = true -> IsAxiom n = true)
    -> arityA <= MaxVar Aprop
    -> IsProved IsAxiom
               (Lequiv (nprop_subst (Nat.max arityA arityB) 0 args
                                    (Subst (PAnat (nfun_eval arityB args B)) Avar Aprop))
                       (nprop_subst (Nat.max arityA arityB) 0 args (ComposeRepr Aprop Avar Brep arityB))).
Proof.
  intros IsAxiom Aprop Avar arityA arityB B args Brep Apropprop.
  intros IsAxiomExtendsHA varfree.
  pose (Nat.max (MaxVar Brep) (MaxVar Aprop)) as m.
  assert (Nat.max arityA arityB <= m) as arityle.
  { apply Nat.max_lub.
    apply (Nat.le_trans _ _ _ varfree). apply Nat.le_max_r.
    destruct (le_lt_dec arityB (MaxVar Brep)). 
    apply (Nat.le_trans _ _ _ l). apply Nat.le_max_l.
    pose proof (fr_freevar _ _ Brep).
    pose proof (MaxVarDoesNotOccurFree _ (fr_propprop _ _ Brep) _ l).
    rewrite H0 in H. discriminate H. }
  unfold ComposeRepr; fold m.
  rewrite nprop_subst_exists.
  2: apply le_S, arityle.
  rewrite nprop_subst_and.
  apply LandIntro. 
  - assert (IsLproposition
              (Land (nprop_subst (Nat.max arityA arityB) 0 args (Subst (Lvar (S m)) arityB Brep))
                    (nprop_subst (Nat.max arityA arityB) 0 args (Subst (Lvar (S m)) Avar Aprop)))
            = true)
      as H.
    { rewrite IsLproposition_and, nprop_subst_IsLprop, nprop_subst_IsLprop.
      reflexivity. apply SubstIsLproposition. exact Apropprop.
      apply IsLterm_var. apply SubstIsLproposition.
      apply fr_propprop. apply IsLterm_var. }
    apply (LimpliesTrans
             _ _ (Subst (PAnat (nfun_eval arityB args B)) (S m)
                        (Land (nprop_subst (Nat.max arityA arityB) 0 args (Subst (Lvar (S m)) arityB Brep))
                              (nprop_subst (Nat.max arityA arityB) 0 args (Subst (Lvar (S m)) Avar Aprop))))).
    2: apply LexistsIntro_impl.
    2: apply IsLterm_PAnat. 2: exact H.
    rewrite Subst_and.
    rewrite nprop_subst_SubstDiffCommutes.
    rewrite SubstSubstNested, SubstTerm_var, Nat.eqb_refl.
    rewrite nprop_subst_SubstDiffCommutes.
    rewrite SubstSubstNested, SubstTerm_var, Nat.eqb_refl.
    apply LandIntroHyp.
    + apply DropHypothesis. apply nprop_subst_IsLprop.
      apply SubstIsLproposition. exact Apropprop.
      apply IsLterm_PAnat.
      pose proof (FormulaRepresents_alt arityB _ _ args
                                        (fr_rep _ _ Brep) (fr_propprop _ _ Brep)
                                        (nfun_eval arityB args B))
        as [H0 _].
      specialize (H0 eq_refl).
      rewrite (nprop_subst_truncate _ arityB), Nat.sub_0_r.
      rewrite Nat.min_r. 2: apply Nat.le_max_r.
      rewrite <- nprop_subst_SubstDiffCommutes.
      apply (WeakenProvable IsWeakHeytingAxiom _ _ IsAxiomExtendsHA). exact H0.
      apply Nat.le_refl.
      intros k H1. apply PAnat_closed.
      apply SubstIsLproposition. apply fr_propprop. apply IsLterm_PAnat.
      intros k H1. rewrite Nat.add_0_r in H1.
      destruct (Nat.lt_trichotomy k arityB).
      exfalso. apply (Nat.lt_irrefl k).
      apply (Nat.lt_le_trans _ _ _ H2). apply H1.
      destruct H2. subst k.
      rewrite VarOccursFreeInFormula_SubstIdem. reflexivity.
      apply fr_propprop. apply PAnat_closed. 
      rewrite VarOccursFreeInFormula_SubstDiff.
      apply fr_vars, H2. apply fr_propprop.
      intro abs. subst k. exact (Nat.lt_irrefl _ H2).
      apply PAnat_closed. 
    + apply LimpliesRefl. apply nprop_subst_IsLprop.
      apply SubstIsLproposition. exact Apropprop. apply IsLterm_PAnat.
    + exact Apropprop.
    + apply MaxVarDoesNotOccurFree. 
      apply Apropprop.
      apply le_n_S, Nat.le_max_r.
    + apply MaxVarFreeSubst_var. apply Apropprop.
      apply le_n_S, Nat.le_max_r.
    + apply le_S, arityle.
    + intros k H0. apply PAnat_closed.
    + apply fr_propprop.
    + apply MaxVarDoesNotOccurFree. 
      apply fr_propprop.
      apply le_n_S, Nat.le_max_l.
    + apply MaxVarFreeSubst_var. apply fr_propprop.
      apply le_n_S, Nat.le_max_l.
    + apply le_S, arityle.
    + intros k H0. apply PAnat_closed.
    + rewrite IsFreeForSubst_and, IsFreeForSubst_PAnat, IsFreeForSubst_PAnat.
      reflexivity.
      apply nprop_subst_IsLprop, SubstIsLproposition.
      exact Apropprop. apply IsLterm_var.
      apply nprop_subst_IsLprop.
      apply SubstIsLproposition.
      apply fr_propprop. apply IsLterm_var.
  - apply LexistsElim_impl.
    apply nprop_subst_closed.
    apply SubstIsLproposition. exact Apropprop. apply IsLterm_PAnat.
    destruct (Nat.eq_dec (S m) Avar). subst Avar.
    rewrite VarOccursFreeInFormula_SubstIdem. reflexivity.
    exact Apropprop. apply PAnat_closed.
    rewrite VarOccursFreeInFormula_SubstDiff.
    apply MaxVarDoesNotOccurFree. 
    apply Apropprop.
    apply le_n_S, Nat.le_max_r. 
    exact Apropprop. exact n. apply PAnat_closed.
    apply LforallIntro.
    apply PushHypothesis.
    apply (LimpliesTrans _ _ (Leq (Lvar (S m)) (PAnat (nfun_eval arityB args B)))).
    pose proof (fr_rep _ _ Brep) as Brepp.
    specialize (Brepp args). simpl in Brepp.
    apply (LforallElim _ _ arityB (Lvar (S m))) in Brepp. 
    rewrite Subst_equiv, Subst_eq, SubstTerm_var, Nat.eqb_refl in Brepp.
    rewrite SubstTerm_PAnat in Brepp. apply LandElim1 in Brepp.
    rewrite (nprop_subst_truncate _ arityB), Nat.sub_0_r.
    rewrite Nat.min_r. 2: apply Nat.le_max_r. 
    apply (WeakenProvable IsWeakHeytingAxiom _ _ IsAxiomExtendsHA). 
    rewrite <- nprop_subst_SubstDiffCommutes. exact Brepp.
    apply Nat.le_refl.
    intros k H. rewrite VarOccursInTerm_var.
    apply Nat.eqb_neq. intro abs.
    destruct H as [_ H]. rewrite abs, Nat.add_0_r in H.
    apply (Nat.lt_irrefl (S m)).
    apply (Nat.lt_le_trans _ _ _ H), le_S.
    exact (Nat.le_trans _ _ _ (Nat.le_max_r _ _) arityle).
    apply SubstIsLproposition. apply fr_propprop. apply IsLterm_var.
    intros v H.
    destruct (Nat.lt_trichotomy v arityB).
    exfalso. apply (Nat.lt_irrefl v).
    apply (Nat.lt_le_trans _ _ _ H0), H. destruct H0. subst v.
    rewrite VarOccursFreeInFormula_SubstIdem. reflexivity.
    apply fr_propprop. rewrite VarOccursInTerm_var.
    apply Nat.eqb_neq. intro abs. rewrite abs in arityle.
    apply (Nat.lt_irrefl m).
    exact (Nat.le_trans _ _ _ (Nat.le_max_r _ _) arityle). 
    rewrite VarOccursFreeInFormula_SubstDiff.
    apply fr_vars, H0. apply fr_propprop.
    intro abs. rewrite abs in H0. exact (Nat.lt_irrefl _ H0).
    rewrite VarOccursInTerm_var.
    apply Nat.eqb_neq. intro abs. rewrite abs, Nat.add_0_r in H.
    apply (Nat.lt_irrefl m). destruct H.
    apply (Nat.lt_trans _ (S m)). apply Nat.le_refl.
    apply (Nat.lt_le_trans _ _ _ H1 arityle).
    apply IsLterm_var.
    unfold Leq. rewrite IsFreeForSubst_equiv, IsFreeForSubst_rel2.
    rewrite MaxVarFreeSubst_var. reflexivity.
    apply nprop_subst_IsLprop, fr_propprop.
    apply le_n_S.
    apply (Nat.le_trans _ _ _ (MaxVar_nprop_subst _ _ _ _)).
    apply Nat.le_max_l.
    apply LeqElimSubstVarPAnat.
    rewrite IsLproposition_implies.
    rewrite nprop_subst_IsLprop, nprop_subst_IsLprop. reflexivity.
    apply SubstIsLproposition. exact Apropprop. apply IsLterm_PAnat.
    apply SubstIsLproposition. exact Apropprop. apply IsLterm_var.
    rewrite Subst_implies.
    rewrite nprop_subst_SubstDiffCommutes.
    rewrite SubstSubstNested, SubstTerm_var, Nat.eqb_refl. 
    rewrite nprop_subst_SubstDiffCommutes.
    rewrite (Subst_nosubst _ (S m)). apply LimpliesRefl.
    apply nprop_subst_IsLprop.
    apply SubstIsLproposition. exact Apropprop. apply IsLterm_PAnat.
    destruct (Nat.eq_dec (S m) Avar). subst Avar.
    rewrite VarOccursFreeInFormula_SubstIdem. reflexivity.
    exact Apropprop. apply PAnat_closed. 
    rewrite VarOccursFreeInFormula_SubstDiff.
    apply MaxVarDoesNotOccurFree. 
    apply Apropprop.
    apply le_n_S, Nat.le_max_r.
    exact Apropprop. exact n. apply PAnat_closed.
    apply le_S, arityle.
    intros k H. apply PAnat_closed. exact Apropprop.
    apply MaxVarDoesNotOccurFree. 
    apply Apropprop.
    apply le_n_S, Nat.le_max_r.
    apply MaxVarFreeSubst_var. apply Apropprop.
    apply le_n_S, Nat.le_max_r.
    apply le_S, arityle.
    intros k H. apply PAnat_closed.
Qed.

Lemma ComposeRepr_eval : forall IsAxiom Aprop (B : nat -> nat) (prop : nat)
                           (Brep : FunctionRepresented 1 B),
    IsLproposition Aprop = true
    -> (forall n, IsWeakHeytingAxiom n = true -> IsAxiom n = true)
    -> (IsProved IsAxiom (Subst (PAnat (B prop)) 0 Aprop)
       <-> IsProved IsAxiom (Subst (PAnat prop) 0 (ComposeRepr Aprop 0 Brep 1))).
Proof.
  intros.
  pose proof (ComposeRepr_spec IsAxiom Aprop 0 0 1 B (ConsNat prop NilNat)
                               Brep H H0 (le_0_n _)).
  simpl in H1. rewrite CoordConsHeadNat in H1.
  rewrite SubstSubstIdem, SubstTerm_PAnat in H1.
  pose proof (LandElim1 _ _ _ H1) as H3.
  pose proof (LandElim2 _ _ _ H1) as H4. clear H1.
  split.
  - intro H2.
    refine (LimpliesElim _ _ _ _ H2). exact H3.
  - intro H2.
    refine (LimpliesElim _ _ _ _ H2). exact H4.
Qed.

Lemma ComposeRepr_1 : forall u v : nat -> nat,
    FunctionRepresented 1 u
    -> FunctionRepresented 1 v
    -> FunctionRepresented 1 (fun n => u (v n)).
Proof.
  intros. 
  apply (Build_FunctionRepresented 1 _ (ComposeRepr H 0 H0 1)).
  - intro args. simpl. remember (CoordNat args 0) as i.
    pose proof (fr_rep _ _ H (ConsNat (v i) NilNat)) as urep.
    simpl in urep. rewrite CoordConsHeadNat in urep.
    pose proof (ComposeRepr_spec IsWeakHeytingAxiom H 0 0 1 v (ConsNat i NilNat) H0
                                 (fr_propprop _ _ H) (fun n x => x) (le_0_n _))
      as H1.
    simpl in H1; rewrite CoordConsHeadNat in H1.
    rewrite SubstSubstIdem, SubstTerm_PAnat in H1. 
    apply LforallIntro.
    apply (LequivTrans _ _ (Subst (PAnat (v i)) 0 H)).
    apply LequivSym; exact H1.
    clear H1. apply LforallElimIdemVar in urep.
    exact urep.
  - apply ComposeReprLprop. apply fr_propprop. apply fr_propprop.
  - intros. rewrite ComposeReprVars.
    destruct v0. inversion H1.
    destruct v0. apply le_S_n in H1. inversion H1. simpl.
    rewrite fr_vars, fr_vars. reflexivity. exact H1. exact H1.
    apply fr_propprop. apply fr_propprop. 
Qed.

(* TODO compose u of any arity to v with arity 2, at any variable *)
Lemma ComposeRepr_21 : forall u v : nat -> nat -> nat,
    FunctionRepresented 2 u
    -> FunctionRepresented 2 v
    -> FunctionRepresented 2 (fun n k => u (v n k) k).
Proof.
  intros u v urep vrep.
  apply (Build_FunctionRepresented 2 _ (ComposeRepr urep 0 vrep 2)).
  - intro args. simpl.
    rewrite CoordTailNat.
    pose proof (ComposeRepr_spec
                  IsWeakHeytingAxiom urep 0 0 2 v args vrep
                  (fr_propprop _ _ urep) (fun n x => x) (le_0_n _))
      as H1. 
    simpl in H1. rewrite CoordTailNat in H1.
    remember (CoordNat args 0) as i.
    remember (CoordNat args 1) as j.
    pose proof (fr_rep _ _ urep (ConsNat (v i j) (ConsNat j NilNat))) as urepp.
    simpl in urepp.
    rewrite CoordConsHeadNat, CoordConsTailNat, CoordConsHeadNat in urepp.
    rewrite CoordTailNat, CoordConsTailNat, CoordConsHeadNat in urepp.
    apply LforallIntro.
    apply (LequivTrans _ _ (Subst (PAnat j) 1 (Subst (PAnat i) 0 (Subst (PAnat (v i j)) 0 urep)))).
    apply LequivSym, H1.
    clear H1. apply LforallElimIdemVar in urepp. 
    rewrite SubstSubstIdem, SubstTerm_PAnat. exact urepp.
  - apply ComposeReprLprop. apply fr_propprop. apply fr_propprop.
  - intros. rewrite ComposeReprVars.
    destruct v0. inversion H. apply le_S_n in H. 
    destruct v0. inversion H. apply le_S_n in H.
    destruct v0. inversion H.
    rewrite fr_vars, fr_vars. reflexivity.
    apply le_n_S, le_n_S. exact H.
    apply le_n_S, le_n_S. exact H.
    apply fr_propprop. apply fr_propprop. 
Qed.

Lemma ComposeRepr_22 : forall u v : nat -> nat -> nat,
    FunctionRepresented 2 u
    -> FunctionRepresented 2 v
    -> FunctionRepresented 2 (fun n k => u n (v n k)).
Proof.
  intros u v urep vrep.
  apply (Build_FunctionRepresented 2 _ (ComposeRepr urep 1 vrep 2)).
  - intro args. simpl.
    rewrite CoordTailNat.
    pose proof (ComposeRepr_spec
                  IsWeakHeytingAxiom urep 1 0 2 v args vrep
                  (fr_propprop _ _ urep) (fun n x => x) (le_0_n _))
      as H1. 
    simpl in H1. rewrite CoordTailNat in H1.
    remember (CoordNat args 0) as i.
    remember (CoordNat args 1) as j.
    pose proof (fr_rep _ _ urep (ConsNat i (ConsNat (v i j) NilNat))) as urepp.
    simpl in urepp.
    rewrite CoordConsHeadNat, CoordConsTailNat, CoordConsHeadNat in urepp.
    rewrite CoordTailNat, CoordConsTailNat, CoordConsHeadNat in urepp.
    apply LforallIntro.
    apply (LequivTrans _ _ (Subst (PAnat j) 1 (Subst (PAnat i) 0 (Subst (PAnat (v i j)) 1 urep)))).
    apply LequivSym, H1.
    clear H1. apply LforallElimIdemVar in urepp. 
    rewrite (SubstSubstDiffCommutes _ 0 1).
    rewrite SubstSubstIdem, SubstTerm_PAnat. exact urepp.
    discriminate. apply PAnat_closed.
    apply PAnat_closed.
  - apply ComposeReprLprop. apply fr_propprop. apply fr_propprop.
  - intros. rewrite ComposeReprVars.
    destruct v0. inversion H. apply le_S_n in H. 
    destruct v0. inversion H. apply le_S_n in H.
    destruct v0. inversion H.
    rewrite fr_vars, fr_vars. reflexivity.
    apply le_n_S, le_n_S. exact H.
    apply le_n_S, le_n_S. exact H.
    apply fr_propprop. apply fr_propprop. 
Qed.

Lemma ComposeRepr_31 : forall (u v : nfun nat 3 nat),
    FunctionRepresented 3 u
    -> FunctionRepresented 3 v
    -> FunctionRepresented 3 (fun i j k => u i (v i j k) k).
Proof.
  intros u v urep vrep.
  apply (Build_FunctionRepresented 3 _ (ComposeRepr urep 1 vrep 3)).
  - intro args. simpl.
    do 3 rewrite CoordTailNat.
    remember (CoordNat args 0) as i.
    remember (CoordNat args 1) as j.
    remember (CoordNat args 2) as k.
    pose proof (ComposeRepr_spec
                  IsWeakHeytingAxiom urep 1 0 3 v
                  args vrep
                  (fr_propprop _ _ urep) (fun n x => x) (le_0_n _))
      as H1. 
    simpl in H1. do 3 rewrite CoordTailNat in H1.
    rewrite <- Heqi, <- Heqj, <- Heqk in H1.
    apply LforallIntro.
    apply (LequivTrans _ _ (Subst (PAnat k) 2
                                  (Subst (PAnat j) 1 (Subst (PAnat i) 0 (Subst (PAnat (v i j k)) 1 urep))))).
    apply LequivSym, H1. clear H1.
    pose proof (fr_rep _ _ urep (ConsNat i (ConsNat (v i j k) (ConsNat k NilNat))))
      as urepp.
    simpl in urepp.
    do 3 rewrite CoordTailNat in urepp.
    do 3 rewrite CoordConsTailNat in urepp.
    do 3 rewrite CoordConsHeadNat in urepp.
    apply LforallElimIdemVar in urepp. 
    rewrite (SubstSubstDiffCommutes _ 0 1).
    rewrite SubstSubstIdem, SubstTerm_PAnat. 
    exact urepp.
    discriminate. apply PAnat_closed.
    apply PAnat_closed.
  - apply ComposeReprLprop. apply fr_propprop. apply fr_propprop.
  - intros v0 H. rewrite ComposeReprVars.
    destruct v0. inversion H. apply le_S_n in H. 
    destruct v0. inversion H. apply le_S_n in H.
    destruct v0. inversion H. apply le_S_n in H.
    destruct v0. inversion H. clear H.
    rewrite fr_vars, fr_vars. reflexivity.
    apply le_n_S, le_n_S, le_n_S, le_n_S, le_0_n.
    apply le_n_S, le_n_S, le_n_S, le_n_S, le_0_n.
    apply fr_propprop. apply fr_propprop. 
Qed.

Lemma FunctionRepresented_1_ext : forall (u v : nat -> nat),
    FunctionRepresented 1 u
    -> (forall n:nat, u n = v n)
    -> FunctionRepresented 1 v.
Proof.
  intros. apply (Build_FunctionRepresented 1 _ H).
  - intro args. simpl. rewrite <- H0. apply (fr_rep _ _ H).
  - apply fr_propprop.
  - apply fr_vars.
Qed.

Lemma FunctionRepresented_2_ext : forall (u v : nat -> nat -> nat),
    FunctionRepresented 2 u
    -> (forall n k:nat, u n k = v n k)
    -> FunctionRepresented 2 v.
Proof.
  intros. apply (Build_FunctionRepresented 2 _ H).
  - intros args. simpl. rewrite <- H0. apply (fr_rep _ _ H).
  - apply fr_propprop.
  - apply fr_vars.
Qed.

Lemma FunctionRepresented_3_ext : forall (u v : nat -> nat -> nat -> nat),
    FunctionRepresented 3 u
    -> (forall i j k:nat, u i j k = v i j k)
    -> FunctionRepresented 3 v.
Proof.
  intros. apply (Build_FunctionRepresented 3 _ H).
  - intros args. simpl. rewrite <- H0. apply (fr_rep _ _ H).
  - apply fr_propprop.
  - apply fr_vars.
Qed.

Definition IncrOutputVarRepr (Aprop Aarity : nat) : nat :=
  Lexists Aarity (Land (Leq (Lvar (S Aarity)) (Lvar Aarity)) Aprop).

Fixpoint AddVariable (arity : nat) (u : nfun nat arity nat) {struct arity}
  : nfun nat (S arity) nat.
Proof.
  destruct arity.
  - exact (fun _ => u).
  - exact (fun arg => AddVariable arity (u arg)).
Defined.

Lemma IncrOutputVarRepr_Lprop : forall arity prop,
    IsLproposition prop = true
    -> IsLproposition (IncrOutputVarRepr prop arity) = true.
Proof.
  intros. unfold IncrOutputVarRepr.
  rewrite IsLproposition_exists, IsLproposition_and, IsLproposition_eq.
  rewrite IsLterm_var, IsLterm_var. apply H.
Qed.

Lemma nfun_eval_AddVariable : forall arity args u,
    nfun_eval (S arity) args (AddVariable arity u)
    = nfun_eval arity args u.
Proof.
  induction arity; [reflexivity|].
  intros args u.
  change (nfun_eval (S arity) (TailNat args)
    (AddVariable arity (u (CoordNat args 0))) =
           nfun_eval arity (TailNat args) (u (CoordNat args 0))).
  rewrite IHarity. reflexivity.
Qed. 

Lemma IncrOutputVarRepresented : forall arity (u : nfun nat arity nat),
    FunctionRepresented arity u
    -> FunctionRepresented (S arity) (AddVariable arity u). 
Proof.
  intros arity u urep.
  assert (S arity =? arity = false) as succneq.
  { destruct (S arity =? arity) eqn:des. 2: reflexivity.
    exfalso. apply Nat.eqb_eq in des. apply (Nat.lt_irrefl arity).
    rewrite <- des at 2. apply Nat.le_refl. }
  apply (Build_FunctionRepresented
           (S arity) _ (IncrOutputVarRepr urep arity)).
  intro args.
  rewrite (nprop_subst_truncate _ arity), Nat.sub_0_r, Nat.min_r. 
  2: apply le_S, Nat.le_refl. 
  unfold IncrOutputVarRepr.
  rewrite nprop_subst_exists, nprop_subst_and. 2: apply Nat.le_refl.
  rewrite nfun_eval_AddVariable.
  rewrite (nprop_subst_truncate _ 0), Nat.sub_0_r, Nat.min_r. simpl.
  apply LforallIntro, LandIntro.
  - apply LexistsElim_impl.
    unfold Leq. rewrite VarOccursFreeInFormula_rel2, VarOccursInTerm_var.
    rewrite PAnat_closed. rewrite Nat.eqb_sym, succneq. reflexivity.
    apply LforallIntro, PushHypothesis, LeqElimSubstVar.
    rewrite IsLproposition_implies, nprop_subst_IsLprop, IsLproposition_eq.
    rewrite IsLterm_var, IsLterm_PAnat. reflexivity. apply fr_propprop.
    apply IsLterm_var. unfold Leq.
    rewrite IsFreeForSubst_implies, IsFreeForSubst_rel2.
    rewrite IsFreeForSubst_nosubst. reflexivity.
    apply nprop_subst_IsLprop, fr_propprop.
    apply nprop_subst_closed. apply fr_propprop.
    apply fr_vars. apply Nat.le_refl.
    rewrite Subst_implies, Subst_eq, SubstTerm_var, Nat.eqb_refl, SubstTerm_PAnat.
    rewrite Subst_nosubst.
    pose proof (fr_rep _ _ urep args).
    apply LforallElimIdemVar in H.
    apply LandElim1 in H. exact H.
    apply nprop_subst_closed. apply fr_propprop.
    apply fr_vars, Nat.le_refl.
  - apply (LimpliesTrans
             _ _ (Subst (PAnat (nfun_eval arity args u)) arity
                        (Land (Leq (Lvar (S arity)) (Lvar arity)) (nprop_subst arity 0 args urep)))).
    2: apply LexistsIntro_impl. 2: apply IsLterm_PAnat.
    3: rewrite IsFreeForSubst_PAnat. 3: reflexivity.
    rewrite Subst_and, Subst_eq, SubstTerm_var, succneq, SubstTerm_var, Nat.eqb_refl.
    apply LandIntroHyp. apply LimpliesRefl.
    rewrite IsLproposition_eq, IsLterm_var, IsLterm_PAnat. reflexivity.
    apply DropHypothesis.
    rewrite IsLproposition_eq, IsLterm_var, IsLterm_PAnat. reflexivity.
    pose proof (FormulaRepresents_alt arity u urep args
                                      (fr_rep _ _ urep) (fr_propprop _ _ urep)
                                      (nfun_eval arity args u)) as [H _].
    specialize (H eq_refl). exact H.
    rewrite IsLproposition_and, IsLproposition_eq, IsLterm_var, IsLterm_var.
    apply nprop_subst_IsLprop, fr_propprop.
    rewrite IsLproposition_and, IsLproposition_eq, IsLterm_var, IsLterm_var.
    apply nprop_subst_IsLprop, fr_propprop.
  - apply le_0_n.
  - rewrite IsLproposition_eq, IsLterm_var, IsLterm_var. reflexivity.
  - intros v H. unfold Leq.
    rewrite VarOccursFreeInFormula_rel2, VarOccursInTerm_var, VarOccursInTerm_var.
    destruct H. rewrite Nat.add_0_r in H0.
    apply Bool.orb_false_intro; apply Nat.eqb_neq.
    intro abs. rewrite abs in H0.
    apply (Nat.lt_irrefl arity). 
    exact (Nat.lt_trans _ _ _ (Nat.le_refl _) H0).
    intro abs. rewrite abs in H0.
    exact (Nat.lt_irrefl arity H0).
  - apply IncrOutputVarRepr_Lprop, fr_propprop.
  - intros v H. unfold IncrOutputVarRepr.
    rewrite VarOccursFreeInFormula_exists.
    destruct (v =? arity) eqn:des. reflexivity. simpl.
    unfold Leq.
    rewrite VarOccursFreeInFormula_and, VarOccursFreeInFormula_rel2.
    rewrite VarOccursInTerm_var, VarOccursInTerm_var, des.
    apply Bool.orb_false_intro.
    destruct (v =? S arity) eqn:des2. 2: reflexivity.
    exfalso. apply Nat.eqb_eq in des2. rewrite des2, Nat.add_0_r in H.
    exact (Nat.lt_irrefl _ (proj2 H)).
    apply fr_vars. destruct (Nat.lt_trichotomy arity v). exact H0.
    destruct H0. rewrite H0, Nat.eqb_refl in des. discriminate des.
    exfalso. apply (Nat.lt_irrefl v).
    apply (Nat.lt_le_trans _ _ _ H0 (proj1 H)).
  - apply IncrOutputVarRepr_Lprop, fr_propprop.
  - intros v H. unfold IncrOutputVarRepr.
    rewrite VarOccursFreeInFormula_exists.
    destruct (v =? arity) eqn:des. reflexivity. simpl. unfold Leq.
    rewrite VarOccursFreeInFormula_and, VarOccursFreeInFormula_rel2.
    rewrite VarOccursInTerm_var, VarOccursInTerm_var, des.
    rewrite fr_vars.
    destruct (v =? S arity) eqn:des2. 2: reflexivity. exfalso.
    apply Nat.eqb_eq in des2. rewrite des2 in H.
    exact (Nat.lt_irrefl _ H).
    exact (Nat.lt_trans _ (S arity) _ (Nat.le_refl _) H).
Qed.


Global Opaque ComposeRepr.
