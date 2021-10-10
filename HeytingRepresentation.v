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

(* args is a sequence of natural numbers, substituted for the free variables
   Lvar v included up to Lvar (v+numSubst) excluded. *)
Fixpoint PAnat_subst_multi (numSubst v args A : nat) { struct numSubst } : nat.
Proof.
  destruct numSubst as [|k].
  - exact A.
  - exact (PAnat_subst_multi
             k v args (Subst (PAnat (CoordNat args k)) (v+k) A)).
Defined.

(* prop could be required Sigma_1 in this definition. However, even with a
   Sigma_1 prop, Lforall arity makes this representation formula Pi_2 and
   we cannot weaken it to a satisfaction in the standard model of arithmetic. *)
Definition FormulaRepresents (arity : nat) (u : nfun nat arity nat) (prop : nat) : Prop :=
  forall args:nat,
    IsProved IsWeakHeytingAxiom
             (Lforall arity (Lequiv (PAnat_subst_multi arity 0 args prop)
                                    (Leq (Lvar arity)
                                         (PAnat (nfun_eval arity args u))))).

(* The limit case arity=0 also works, it is the representation of a constant u:nat. *)
Lemma FormulaRepresents_0 : forall (u prop : nat),
    FormulaRepresents 0 u prop
    <-> IsProved IsWeakHeytingAxiom (Lequiv prop (Leq (Lvar 0) (PAnat u))).
Proof.
  intros u prop. unfold FormulaRepresents. simpl. split.
  - intros H. specialize (H 0).
    apply LforallElimIdemVar in H. exact H.
  - intros H _. apply LforallIntro. exact H.
Qed. 

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

Lemma PAnat_subst_multi_IsLprop : forall arity prop args i,
    IsLproposition prop = true
    -> IsLproposition (PAnat_subst_multi arity i args prop) = true.
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
                       (Subst (PAnat j) arity (PAnat_subst_multi arity 0 args prop))).
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
    rewrite IsLproposition_equiv, PAnat_subst_multi_IsLprop, IsLproposition_eq.
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
          <-> HAstandardModel (Subst (PAnat j) arity (PAnat_subst_multi arity 0 args prop))
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
    apply PAnat_subst_multi_IsLprop. exact propprop.
    rewrite IsLproposition_eq, IsLterm_var, IsLterm_PAnat. reflexivity.
Qed.

Lemma PAnat_subst_multi_closed : forall arity i args prop v,
    IsLproposition prop = true
    -> VarOccursFreeInFormula v prop = false
    -> VarOccursFreeInFormula v (PAnat_subst_multi arity i args prop) = false.
Proof.
  induction arity. intros. exact H0.
  intros. simpl. rewrite IHarity. reflexivity.
  apply SubstIsLproposition. exact H. apply IsLterm_PAnat.
  clear IHarity.
  destruct (Nat.eq_dec v (i+arity)). subst v.
  rewrite VarOccursFreeInFormula_SubstIdem. reflexivity.
  exact H. apply PAnat_closed.
  rewrite VarOccursFreeInFormula_SubstDiff. exact H0.
  exact H. exact n. apply PAnat_closed.
Qed. 

Lemma PAnat_subst_multi_in_range : forall arity i args prop v,
    IsLproposition prop = true
    -> i <= v < i + arity
    -> VarOccursFreeInFormula v (PAnat_subst_multi arity i args prop) = false.
Proof.
  induction arity.
  - intros. exfalso. destruct H0.
    rewrite Nat.add_0_r in H1.
    apply (Nat.lt_irrefl i). exact (Nat.le_lt_trans _ _ _ H0 H1).
  - intros. simpl. destruct H0.
    rewrite Nat.add_succ_r in H1.
    apply Nat.le_succ_r in H1. destruct H1.
    + apply IHarity. apply SubstIsLproposition. exact H.
      apply IsLterm_PAnat. split; assumption.
    + inversion H1. subst v. clear H0 H1 IHarity.
      apply PAnat_subst_multi_closed.
      apply SubstIsLproposition. exact H.
      apply IsLterm_PAnat.
      apply VarOccursFreeInFormula_SubstIdem. exact H.
      apply PAnat_closed.
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
  assert (VarOccursFreeInFormula arity (PAnat_subst_multi arity 0 0 urep) = false)
    as substnoc.
  { apply PAnat_subst_multi_closed. apply fr_propprop. exact nooccur. }
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

Definition MaxVarList (list : nat) : nat := MaxSeqNat (MapNat MaxVar list).

Lemma MaxVarListCons : forall A Bk,
    MaxVarList (ConsNat A Bk) = Nat.max (MaxVar A) (MaxVarList Bk).
Proof.
  intros. unfold MaxVarList.
  rewrite MapConsNat, MaxConsNat. reflexivity.
Qed.

(* Lexists v (Lexists (v+1) ... (Lexists (v+varCount) A)) *)
Fixpoint LexistsMulti (v varCount A : nat) {struct varCount} : nat :=
  match varCount with
  | O => A
  | S k => LexistsMulti v k (Lexists (v+k) A)
  end.

Lemma LexistsMultiLprop : forall varCount v A,
    IsLproposition A = true
    -> IsLproposition (LexistsMulti v varCount A) = true.
Proof.
  induction varCount.
  intros. exact H.
  intros. simpl. 
  apply IHvarCount.
  rewrite IsLproposition_exists. exact H.
Qed.

Lemma LexistsMultiImplies : forall varCount v A B,
    IsProved IsWeakHeytingAxiom (Limplies A B)
    -> IsProved IsWeakHeytingAxiom
               (Limplies
                  (LexistsMulti v varCount A)
                  (LexistsMulti v varCount B)).
Proof.
  induction varCount.
  - intros. exact H.
  - intros. simpl. apply IHvarCount.
    apply LexistsElim_impl.
    rewrite VarOccursFreeInFormula_exists.
    rewrite Nat.eqb_refl. reflexivity.
    apply LforallIntro.
    apply (LimpliesTrans _ _ _ _ H).
    pose proof (IsProvedIsLproposition _ _ H).
    rewrite IsLproposition_implies in H0.
    apply andb_prop in H0. destruct H0.
    rewrite <- (SubstIdemVar B H1 (v+varCount)) at 1.
    apply LexistsIntro_impl. apply IsLterm_var.
    exact H1.
    apply IsFreeForSubstIdemVar. exact H1.
Qed.

Lemma LexistsMultiIntro : forall varCount v A vals,
    IsLproposition A = true ->
    IsProved IsWeakHeytingAxiom 
             (Limplies (PAnat_subst_multi varCount v vals A)
                       (LexistsMulti v varCount A)).
Proof.
  induction varCount.
  - intros. apply LimpliesRefl, LexistsMultiLprop, H.
  - intros. simpl.
    specialize (IHvarCount v (Subst (PAnat (CoordNat vals varCount)) (v + varCount) A) vals).
    refine (LimpliesTrans IsWeakHeytingAxiom _ _ _ (IHvarCount _) _).
    apply SubstIsLproposition. exact H.
    apply IsLterm_PAnat.
    apply LexistsMultiImplies.
    apply LexistsIntro_impl. apply IsLterm_PAnat.
    exact H.
    apply IsFreeForSubst_PAnat. exact H.
Qed.

Lemma LexistsMultiIntroHyp : forall varCount v A H vals,
    IsLproposition A = true
    -> IsProved IsWeakHeytingAxiom 
               (Limplies H (PAnat_subst_multi varCount v vals A))
    -> IsProved IsWeakHeytingAxiom 
             (Limplies H (LexistsMulti v varCount A)).
Proof.
  intros.
  apply (LimpliesTrans IsWeakHeytingAxiom _ _ _ H1).
  apply LexistsMultiIntro, H0.
Qed. 

Lemma LexistsMultiSucc : forall v varCount A,
    LexistsMulti v (S varCount) A = LexistsMulti v varCount (Lexists (v + varCount) A).
Proof.
  reflexivity.
Qed.

Lemma LexistsMultiElim : forall varCount v A B,
    (forall k, k<varCount -> VarOccursFreeInFormula (v + k) B = false)
    -> IsProved IsWeakHeytingAxiom (Limplies A B)
    -> IsProved IsWeakHeytingAxiom 
               (Limplies (LexistsMulti v varCount A) B).
Proof.
  induction varCount.
  - intros. exact H0.
  - intros. simpl. apply IHvarCount.
    intros. apply H. apply (Nat.lt_trans _ _ _ H1). apply Nat.le_refl.
    apply LexistsElim_impl.
    apply H. apply Nat.le_refl.
    apply LforallIntro. exact H0.
Qed. 
 
(* Shift list of variables : Xv -> Xv+shift, ..., X0 -> Xshift.
   The substitutions are done in reverse order, otherwise X0 -> X1
   would collide with the next substitution for X1. *)
Fixpoint ShiftVars (v shift A : nat) {struct v} : nat :=
  match v with
  | O => Subst (Lvar shift) O A
  | S k => ShiftVars k shift (Subst (Lvar (v+shift)) v A)
  end.

Fixpoint LandMultiRec Ak A i {struct i} : nat :=
  match i with
  | O => A
  | S k => Land A (LandMultiRec (TailNat Ak) (HeadNat Ak) k)
  end.
Definition LandMulti Ak A : nat := LandMultiRec Ak A (LengthNat Ak).

Lemma LandMultiCons : forall Bk A B,
    LandMulti (ConsNat B Bk) A = Land A (LandMulti Bk B).
Proof.
  intros Bk A B.
  unfold LandMulti. rewrite LengthConsNat.
  simpl. apply f_equal. rewrite TailConsNat.
  change (HeadNat (ConsNat B Bk))
    with (CoordNat (ConsNat B Bk) 0).
  rewrite CoordConsHeadNat. reflexivity.
Qed.

Lemma LandMultiLprop : forall Ak A,
    IsLproposition A = true
    -> (forall i, i < LengthNat Ak -> IsLproposition (CoordNat Ak i) = true)
    -> IsLproposition (LandMulti Ak A) = true.
Proof.
  apply (Seq_rect (fun Ak => forall A, IsLproposition A = true
    -> (forall i, i < LengthNat Ak -> IsLproposition (CoordNat Ak i) = true)
    -> IsLproposition (LandMulti Ak A) = true)).
  - intros. unfold LandMulti. rewrite H. exact H0.
  - intros. rewrite LandMultiCons. rewrite IsLproposition_and, H0.
    apply H. specialize (H1 0).
    rewrite CoordConsHeadNat in H1. apply H1.
    rewrite LengthConsNat. apply le_n_S, le_0_n.
    intros i H2. specialize (H1 (S i)).
    rewrite CoordConsTailNat in H1. apply H1.
    rewrite LengthConsNat. apply le_n_S, H2.
Qed.

Lemma LandMultiVars : forall Bk v A,
    VarOccursFreeInFormula v A = false
    -> (forall k, k < LengthNat Bk -> VarOccursFreeInFormula v (CoordNat Bk k) = false)
    -> VarOccursFreeInFormula v (LandMulti Bk A) = false.
Proof.
  apply (Seq_rect (fun Bk => forall v A,
    VarOccursFreeInFormula v A = false
    -> (forall k, k < LengthNat Bk ->
            VarOccursFreeInFormula v (CoordNat Bk k) = false)
    -> VarOccursFreeInFormula v (LandMulti Bk A) = false)).
  - intros. unfold LandMulti. rewrite H. exact H0.
  - intros.
    rewrite LandMultiCons, VarOccursFreeInFormula_and, H0. simpl.
    apply H. specialize (H1 0).
    rewrite CoordConsHeadNat in H1. apply H1.
    rewrite LengthConsNat. apply le_n_S, le_0_n.
    intros k H2. specialize (H1 (S k)).
    rewrite CoordConsTailNat in H1. apply H1.
    rewrite LengthConsNat. apply le_n_S, H2.
Qed.

Lemma LandMultiMaxVar : forall Bk A,
    MaxVar (LandMulti Bk A) = Nat.max (MaxVar A) (MaxVarList Bk).
Proof.
  apply (Seq_rect (fun Bk => forall A,
                       MaxVar (LandMulti Bk A) = Nat.max (MaxVar A) (MaxVarList Bk))).
  - intros. unfold LandMulti. rewrite H. simpl.
    unfold MaxVarList, MaxSeqNat. rewrite LengthMapNat, H.
    simpl. rewrite Nat.max_comm. reflexivity.
  - intros. rewrite LandMultiCons, MaxVar_and, H.
    unfold MaxVarList. rewrite MapConsNat, MaxConsNat.
    reflexivity.
Qed.

Lemma LandMultiIntro : forall Bk hyp A IsAxiom,
    IsProved IsAxiom (Limplies hyp A)
    -> (forall k, k < LengthNat Bk -> IsProved IsAxiom (Limplies hyp (CoordNat Bk k)))
    -> IsProved IsAxiom (Limplies hyp (LandMulti Bk A)).
Proof.
  apply (Seq_rect (fun Bk => forall hyp A IsAxiom,
    IsProved IsAxiom (Limplies hyp A)
    -> (forall k, k < LengthNat Bk -> IsProved IsAxiom (Limplies hyp (CoordNat Bk k)))
    -> IsProved IsAxiom (Limplies hyp (LandMulti Bk A)))).
  - intros. unfold LandMulti. rewrite H. exact H0.
  - intros. rewrite LandMultiCons. apply LandIntroHyp.
    exact H0. apply H. specialize (H1 0).
    rewrite CoordConsHeadNat in H1. apply H1.
    rewrite LengthConsNat. apply le_n_S, le_0_n.
    intros k H2. specialize (H1 (S k)).
    rewrite CoordConsTailNat in H1. apply H1.
    rewrite LengthConsNat. apply le_n_S, H2.
Qed.

Lemma LandMultiElim1 : forall A Bk,
    IsLproposition A = true
    -> (forall i, i < LengthNat Bk -> IsLproposition (CoordNat Bk i) = true)
    -> IsProved IsWeakHeytingAxiom (Limplies (LandMulti Bk A) A).
Proof.
  intros. unfold LandMulti.
  destruct (LengthNat Bk) eqn:des.
  - apply LimpliesRefl. exact H.
  - simpl. apply LandElim1_impl. exact H.
    pose proof (LengthTailNat Bk).
    rewrite des in H1. simpl in H1.
    rewrite <- H1. apply LandMultiLprop.
    apply (H0 0). apply le_n_S, le_0_n.
    intros. apply (H0 (S i)). apply le_n_S.
    rewrite H1 in H2. exact H2.
Qed.
 

(* Shift all Bk's outputs variables by varShift *)
Definition BindOutputs (A Bk Barity varShift : nat) : nat :=
  LandMulti (MapNat
               (fun k => Subst (Lvar (k+varShift)) Barity (CoordNat Bk k))
               (RangeNat 0 (LengthNat Bk))) A.

(* Formula that represents the composition A(B_0,...,B_{k-1})
   where k is the arity of A and all the B_i's have the same arity.
   The case arityA = LengthNat Bk = 0 also works, it just bumps A's output
   Lvar 0 to Lvar Barity. *)
Definition ComposeRepr (A Bk Barity : nat) : nat :=
  let v := S (Nat.max (MaxVar A) (Nat.max Barity (MaxVarList Bk))) in
  LexistsMulti v (S (LengthNat Bk))
               (BindOutputs
                  (Land (Leq (Lvar (LengthNat Bk + v)) (Lvar Barity))
                        (ShiftVars (LengthNat Bk) v A))
                  Bk Barity v).

Lemma BindPropVarsLprop : forall A Bprops Barity varShift,
    IsLproposition A = true
    -> (forall k, k < LengthNat Bprops -> IsLproposition (CoordNat Bprops k) = true)
    -> IsLproposition (BindOutputs A Bprops Barity varShift) = true.
Proof.
  intros. apply LandMultiLprop.
  exact H. intros. rewrite LengthMapNat, LengthRangeNat in H1.
  rewrite CoordMapNat. apply SubstIsLproposition.
  apply H0. rewrite CoordRangeNat. exact H1. exact H1.
  apply IsLterm_var. rewrite LengthRangeNat. exact H1.
Qed.

Lemma ShiftVarsLprop : forall (v shift A : nat),
    IsLproposition A = true
    -> IsLproposition (ShiftVars v shift A) = true.
Proof.
  induction v.
  intros. apply SubstIsLproposition. exact H. apply IsLterm_var.
  intros. apply IHv, SubstIsLproposition. exact H. apply IsLterm_var.
Qed.

Lemma ComposeReprLprop : forall Aprop Bprops Barity,
    IsLproposition Aprop = true
    -> (forall i, i < LengthNat Bprops -> IsLproposition (CoordNat Bprops i) = true)
    -> IsLproposition (ComposeRepr Aprop Bprops Barity) = true.
Proof.
  intros.
  apply LexistsMultiLprop.
  apply BindPropVarsLprop.
  rewrite IsLproposition_and, IsLproposition_eq, IsLterm_var, IsLterm_var.
  apply ShiftVarsLprop. exact H.
  exact H0.
Qed.

Lemma LexistsMultiVars : forall varCount v w A,
    VarOccursFreeInFormula w (LexistsMulti v varCount A)
    = andb (VarOccursFreeInFormula w A)
           (orb (Nat.ltb w v) (Nat.leb (v+varCount) w)).
Proof.
  induction varCount.
  - intros. simpl. rewrite Nat.add_0_r.
    replace ((w <? v) || (v <=? w))%bool with true.
    rewrite Bool.andb_true_r. reflexivity.
    destruct (le_lt_dec v w).
    apply Nat.leb_le in l. rewrite l, Bool.orb_true_r. reflexivity.
    apply Nat.ltb_lt in l. rewrite l. reflexivity.
  - intros. simpl. rewrite IHvarCount, VarOccursFreeInFormula_exists.
    destruct (VarOccursFreeInFormula w A) eqn:occur. 
    2: simpl; rewrite Bool.andb_false_r; reflexivity. 
    rewrite Bool.andb_true_r. simpl.
    destruct (w =? v + varCount) eqn:des. simpl.
    + apply Nat.eqb_eq in des. subst w.
      symmetry. apply Bool.orb_false_intro.
      apply Nat.ltb_nlt. intro abs.
      rewrite <- (Nat.add_0_r v) in abs at 2.
      apply Nat.add_lt_mono_l in abs. inversion abs.
      apply Nat.leb_nle. intro abs.
      apply Nat.add_le_mono_l in abs.
      exact (Nat.lt_irrefl _ abs).
    + destruct (w <? v) eqn:wv. reflexivity.
      simpl. apply Nat.ltb_nlt, not_lt in wv.
      destruct (Nat.lt_trichotomy (v+varCount) w).
      transitivity true.
      apply Nat.leb_le, Nat.lt_le_incl, H.
      symmetry. apply Nat.leb_le.
      rewrite Nat.add_succ_r. exact H.
      destruct H. exfalso.
      rewrite H, Nat.eqb_refl in des. discriminate des.
      transitivity false.
      apply Nat.leb_nle. intro abs.
      apply (Nat.lt_irrefl w).
      exact (Nat.lt_le_trans _ _ _ H abs).
      symmetry.
      apply Nat.leb_nle. intro abs.
      rewrite Nat.add_succ_r in abs.
      apply (Nat.lt_irrefl w).
      exact (Nat.lt_trans _ _ _ H abs).
Qed.

Lemma BindPropVarsVars : forall v A Bprops Barity varShift,
    (v < varShift \/ LengthNat Bprops + varShift < v)
    -> VarOccursFreeInFormula v A = false
    -> (forall k, k < LengthNat Bprops ->
            VarOccursFreeInFormula v (CoordNat Bprops k) = false)
    -> (forall k, k < LengthNat Bprops -> IsLproposition (CoordNat Bprops k) = true)
    -> VarOccursFreeInFormula v (BindOutputs A Bprops Barity varShift) = false.
Proof.
  intros. apply LandMultiVars. exact H0.
  intros. rewrite LengthMapNat, LengthRangeNat in H3.
  rewrite CoordMapNat, CoordRangeNat. simpl.
  assert (v <> k + varShift).
  { intro abs. destruct H.
    rewrite <- (Nat.add_0_l varShift) in H.
    rewrite abs in H.
    apply Nat.add_lt_mono_r in H. inversion H.
    rewrite abs in H.
    apply Nat.add_lt_mono_r in H.
    apply (Nat.lt_irrefl k).
    exact (Nat.lt_trans _ _ _ H3 H). }
  destruct (Nat.eq_dec v Barity). rewrite e.
  apply VarOccursFreeInFormula_SubstIdem.
  apply H2, H3.
  rewrite VarOccursInTerm_var. apply Nat.eqb_neq.
  intro abs. rewrite <- e in abs.
  rewrite abs in H4. apply H4. reflexivity.
  rewrite VarOccursFreeInFormula_SubstDiff. apply H1, H3.
  apply H2, H3. exact n.
  rewrite VarOccursInTerm_var. apply Nat.eqb_neq.
  intro abs. rewrite abs in H4. apply H4. reflexivity.
  exact H3. rewrite LengthRangeNat. exact H3.
Qed.

(* ShiftVars v varShift A shifts variables X0,...,Xv to XvarShift,...,Xv+varShift.
   All free variables of A are shifted and variable w is not in the shift range. *)
Lemma ShiftVarsVars : forall (v w varShift A : nat),
    IsLproposition A = true
    -> (w < varShift \/ v + varShift < w)
    -> VarOccursFreeInFormula w (ShiftVars v varShift A)
      = andb (VarOccursFreeInFormula w A) (Nat.ltb v w).
Proof.
  induction v.
  - intros. simpl. destruct w.
    + rewrite Nat.ltb_irrefl, Bool.andb_false_r.
      destruct H0. 2: inversion H0. 
      apply VarOccursFreeInFormula_SubstIdem. exact H.
      rewrite VarOccursInTerm_var. apply Nat.eqb_neq.
      intro abs. subst varShift. apply (Nat.lt_irrefl 0 H0).
    + rewrite VarOccursFreeInFormula_SubstDiff.
      replace (0 <? S w) with true.
      rewrite Bool.andb_true_r. reflexivity.
      symmetry. apply Nat.ltb_lt. apply le_n_S, le_0_n.
      exact H. discriminate.
      rewrite VarOccursInTerm_var. apply Nat.eqb_neq. intro abs.
      subst varShift. destruct H0; exact (Nat.lt_irrefl _ H0).
  - intros w varShift A Aprop H.
    simpl. rewrite IHv. clear IHv.
    + destruct H.
      (* w < varShift *)
      destruct (Nat.eq_dec w (S v)). subst w.
      rewrite Nat.ltb_irrefl, Bool.andb_false_r.
      replace (v <? S v) with true. 
      rewrite Bool.andb_true_r.
      apply VarOccursFreeInFormula_SubstIdem. exact Aprop.
      rewrite VarOccursInTerm_var. apply Nat.eqb_neq.
      intro abs.
      rewrite <- (Nat.add_0_r (S v)) in abs at 1.
      rewrite (Nat.add_cancel_l 0 varShift (S v)) in abs.
      rewrite <- abs in H. inversion H.
      symmetry. apply Nat.ltb_lt. apply Nat.le_refl.
      rewrite VarOccursFreeInFormula_SubstDiff. 
      destruct (VarOccursFreeInFormula w A). 2: reflexivity. simpl.
      destruct (Nat.lt_trichotomy w (S v)).
      apply le_S_n in H0.
      replace (S v <? w) with false.
      apply Nat.ltb_ge, H0.
      symmetry. apply Nat.ltb_ge.
      apply (Nat.le_trans _ _ _ H0). apply le_S, Nat.le_refl.
      destruct H0. exfalso. rewrite H0 in n. exact (n eq_refl).
      replace (S v <? w) with true.
      apply Nat.ltb_lt.
      refine (Nat.lt_trans _ _ _ _ H0). apply Nat.le_refl.
      symmetry. apply Nat.ltb_lt, H0.
      exact Aprop. exact n.
      rewrite VarOccursInTerm_var.
      apply Nat.eqb_neq. intros abs. subst w.
      rewrite <- (Nat.add_0_l varShift) in H at 2.
      rewrite <- (Nat.add_lt_mono_r (S v) 0 varShift) in H. inversion H.
      (* S v + varShift < w *)
      replace (S v <? w) with true. rewrite Bool.andb_true_r.
      replace (v <? w) with true. rewrite Bool.andb_true_r.
      rewrite VarOccursFreeInFormula_SubstDiff. reflexivity.
      exact Aprop.
      intro abs. subst w.
      rewrite <- (Nat.add_0_r (S v)) in H at 2.
      apply Nat.add_lt_mono_l in H. inversion H.
      rewrite VarOccursInTerm_var.
      apply Nat.eqb_neq. intro abs. subst w.
      exact (Nat.lt_irrefl _ H).
      symmetry. apply Nat.ltb_lt.
      refine (Nat.le_lt_trans _ _ _ _ H).
      simpl. apply le_S.
      rewrite <- (Nat.add_0_r v) at 1.
      apply Nat.add_le_mono_l, le_0_n. 
      symmetry. apply Nat.ltb_lt.
      refine (Nat.le_lt_trans _ _ _ _ H).
      rewrite <- (Nat.add_0_r (S v)) at 1.
      apply Nat.add_le_mono_l, le_0_n. 
    + apply SubstIsLproposition. exact Aprop. apply IsLterm_var.
    + destruct H. left. exact H. right.
      refine (Nat.lt_trans _ _ _ _ H). apply Nat.le_refl.
Qed.

Lemma ComposeReprVars : forall A Bk Barity,
    IsLproposition A = true
    -> (forall v, LengthNat Bk < v -> VarOccursFreeInFormula v A = false)
    -> (forall k v, k < LengthNat Bk ->
              Barity < v ->
         VarOccursFreeInFormula v (CoordNat Bk k) = false)
    -> (forall k, k < LengthNat Bk -> IsLproposition (CoordNat Bk k) = true)
    -> forall v, Barity < v ->
           VarOccursFreeInFormula v (ComposeRepr A Bk Barity) = false.
Proof.
  intros A Bk Barity. intros Aprop vA vB Bprop v H.
  unfold ComposeRepr.
  rewrite LexistsMultiVars.
  (* Trivial when v is in the quantified existential variables *)
  destruct ((v <? S (Nat.max (MaxVar A) (Nat.max Barity (MaxVarList Bk))))
    || (S (Nat.max (MaxVar A) (Nat.max Barity (MaxVarList Bk))) +
        S (LengthNat Bk) <=? v))%bool eqn:occur.
  2: rewrite Bool.andb_false_r; reflexivity.
  rewrite Bool.andb_true_r.
  apply Bool.orb_prop in occur.
  (* Now v is not a quantified existential *)
  apply BindPropVarsVars. 
  destruct occur. left. apply Nat.ltb_lt, H0.
  right. apply Nat.leb_le in H0.
  rewrite Nat.add_comm. refine (Nat.le_trans _ _ _ _ H0).
  simpl.
  apply le_n_S.
  rewrite Nat.add_succ_r. apply Nat.le_refl.
  unfold Leq.
  rewrite VarOccursFreeInFormula_and, VarOccursFreeInFormula_rel2.
  rewrite VarOccursInTerm_var, VarOccursInTerm_var.
  apply Bool.orb_false_intro.
  apply Bool.orb_false_intro.
  apply Nat.eqb_neq. intro abs.
  destruct occur.
  apply Nat.ltb_lt in H0.
  rewrite abs in H0.
  rewrite <- (Nat.add_0_l (S (Nat.max (MaxVar A) (Nat.max Barity (MaxVarList Bk)))))
    in H0 at 2.
  apply Nat.add_lt_mono_r in H0. inversion H0.
  apply Nat.leb_le in H0.
  rewrite Nat.add_comm in abs.
  rewrite Nat.add_succ_r, <- abs in H0.
  apply (Nat.lt_irrefl v). exact H0.
  apply Nat.eqb_neq. intro abs. rewrite abs in H.
  exact (Nat.lt_irrefl _ H).
  rewrite ShiftVarsVars.
  destruct (LengthNat Bk <? v) eqn:des.
  rewrite Bool.andb_true_r. apply vA, Nat.ltb_lt, des.
  rewrite Bool.andb_false_r. reflexivity.
  exact Aprop.
  destruct occur. left. apply Nat.ltb_lt. exact H0.
  right.
  apply Nat.leb_le in H0. unfold lt.
  rewrite Nat.add_comm. rewrite Nat.add_succ_r in H0. exact H0.
  intros k H3. apply vB. exact H3. exact H. exact Bprop.
Qed.

Lemma PAnat_subst_multi_exists_multi : forall args substCount i A v existCount,
    (* Disjoint existential variables and substitution variables *)
    i + substCount <= v
    -> PAnat_subst_multi substCount i args (LexistsMulti v existCount A)
      = LexistsMulti v existCount (PAnat_subst_multi substCount i args A).
Proof.
  assert (forall existCount n i v A ,
             i < v
             -> Subst n i (LexistsMulti v existCount A)
               = LexistsMulti v existCount (Subst n i A)) as H.
  { induction existCount. reflexivity.
    intros. simpl. rewrite IHexistCount. 2: exact H.
    apply f_equal.
    rewrite Subst_exists.
    destruct (v + existCount =? i) eqn:des.
    2: reflexivity. exfalso.
    apply Nat.eqb_eq in des. subst i.
    rewrite <- (Nat.add_0_r v) in H at 2.
    apply Nat.add_lt_mono_l in H. inversion H. }
  induction substCount; [reflexivity|].
  intros i A v existCount H1. simpl.
  rewrite H.
  rewrite IHsubstCount. reflexivity.
  apply Nat.lt_le_incl.
  rewrite Nat.add_succ_r in H1.
  exact H1.
  rewrite Nat.add_succ_r in H1.
  exact H1.
Qed.

Lemma PAnat_subst_multi_exists : forall args substCount i A v,
    (* Disjoint existential variables and substitution variables *)
    i + substCount <= v
    -> PAnat_subst_multi substCount i args (Lexists v A)
      = Lexists v (PAnat_subst_multi substCount i args A).
Proof.
  intros.
  pose proof (PAnat_subst_multi_exists_multi args substCount i A v 1 H).
  simpl in H0.
  rewrite Nat.add_0_r in H0. exact H0.
Qed.

Lemma PAnat_subst_multi_and : forall args arity i f g,
    PAnat_subst_multi arity i args (Land f g)
    = Land (PAnat_subst_multi arity i args f) (PAnat_subst_multi arity i args g).
Proof.
  induction arity; [reflexivity|].
  intros. simpl.
  rewrite Subst_and, IHarity. reflexivity.
Qed.

Lemma PAnat_subst_multi_and_multi : forall Ak args arity i A,
    PAnat_subst_multi arity i args (LandMulti Ak A)
    = LandMulti (MapNat (PAnat_subst_multi arity i args) Ak)
                (PAnat_subst_multi arity i args A).
Proof.
  apply (Seq_rect (fun Ak => forall args arity i A,
    PAnat_subst_multi arity i args (LandMulti Ak A)
    = LandMulti (MapNat (PAnat_subst_multi arity i args) Ak)
                (PAnat_subst_multi arity i args A))).
  - intros. unfold LandMulti, MapNat.
    rewrite H. simpl. rewrite H. reflexivity.
  - intros. rewrite LandMultiCons, PAnat_subst_multi_and.
    rewrite MapConsNat, LandMultiCons.
    apply f_equal. apply H.
Qed.

Lemma PAnat_subst_multi_SubstDiffCommutes : forall arity i args prop v t,
    (v < i \/ i + arity <= v)
    -> (forall k, i <= k < arity + i -> VarOccursInTerm k t = false)
    -> Subst t v (PAnat_subst_multi arity i args prop)
      = PAnat_subst_multi arity i args (Subst t v prop).
Proof.
  induction arity; [reflexivity|].
  intros. simpl. rewrite IHarity.
  apply f_equal. apply SubstSubstDiffCommutes.
  - intro abs. subst v.
    destruct H.
    rewrite <- (Nat.add_0_r i) in H at 2.
    apply Nat.add_lt_mono_l in H. inversion H.
    rewrite Nat.add_succ_r in H.
    exact (Nat.lt_irrefl _ H).
  - apply H0. split.
    rewrite <- (Nat.add_0_r i) at 1.
    apply Nat.add_le_mono_l, le_0_n.
    rewrite Nat.add_comm.
    apply Nat.le_refl.
  - apply PAnat_closed.
  - destruct H. left. exact H. right.
    rewrite Nat.add_succ_r in H.
    apply Nat.lt_le_incl, H.
  - intros k H1. apply H0. split. apply H1.
    apply (Nat.lt_trans _ (arity+i)). apply H1.
    apply Nat.le_refl.
Qed.

Lemma PAnat_subst_multi_id : forall arity maxvar prop args i,
    (forall v, maxvar <= v < arity + i -> VarOccursFreeInFormula v prop = false)
    -> maxvar <= i
    -> PAnat_subst_multi arity i args prop = prop.
Proof.
  induction arity. reflexivity.
  intros. simpl. rewrite Subst_nosubst.
  apply (IHarity maxvar). intros.
  apply H. split. apply H1.
  apply (Nat.lt_trans _ (arity+i)).
  apply H1. apply Nat.le_refl.
  exact H0. apply H.
  split. apply (Nat.le_trans _ _ _ H0).
  rewrite <- (Nat.add_0_r i) at 1.
  apply Nat.add_le_mono_l, le_0_n.
  simpl. apply le_n_S.
  rewrite Nat.add_comm. apply Nat.le_refl.
Qed.

(*
Lemma PAnat_subst_multi_truncate : forall arity maxvar prop args i,
    IsLproposition prop = true
    -> (forall v, maxvar <= v < arity + i -> VarOccursFreeInFormula v prop = false)
    -> PAnat_subst_multi arity i args prop
      = PAnat_subst_multi (Nat.min arity (maxvar - i)) i args prop.
Proof.
  induction arity ; [reflexivity|].
  intros maxvar prop args i propprop propclosed.
  destruct (le_lt_dec (S arity) (maxvar - i)).
  rewrite Nat.min_l. reflexivity. exact l.
  rewrite Nat.min_r. 2: apply Nat.lt_le_incl, l.
  simpl (PAnat_subst_multi (S arity) i args prop).
  destruct (le_lt_dec maxvar i).
  - replace (maxvar - i) with 0.
    change (PAnat_subst_multi (S arity) i args prop = prop).
    apply (PAnat_subst_multi_id _ maxvar).
    intros. apply propclosed. exact H. exact l0.
    symmetry. apply (Nat.sub_0_le maxvar i), l0.
  - rewrite (IHarity maxvar).
    rewrite Nat.min_r.
    change (PAnat_subst_multi (S (maxvar - S i)) i args prop
            = PAnat_subst_multi (maxvar - i) i args prop).
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
*)

Lemma MaxVar_PAnat_subst_multi : forall arity i args prop,
    MaxVar (PAnat_subst_multi arity i args prop) <= MaxVar prop.
Proof.
  induction arity; [reflexivity|].
  intros. simpl.
  apply (Nat.le_trans _ _ _ (IHarity i _ _)).
  apply (Nat.le_trans _ _ _ (MaxVar_Subst _ _ _)).
  apply Nat.max_lub. rewrite MaxVarTerm_PAnat.
  apply le_0_n. apply Nat.le_refl.
Qed. 

(* Evaluate multiple functions Bk on args *)
Definition nfun_eval_multi arityB (Bk : nat -> nfun nat arityB nat) (evalCount args : nat) : nat
  := MapNat (fun k => nfun_eval arityB args (Bk k))
            (RangeNat 0 evalCount).

Fixpoint extract_seq {X : nat -> Type} (f : forall k, X k)
         (g : forall k, X k -> nat) (len : nat) {struct len} : nat :=
  match len with
  | O => NilNat
  | S i => ConcatNat (extract_seq f g i) (ConsNat (g _ (f i)) NilNat)
  end.

Lemma extract_seq_length : forall {X} (f : forall k, X k) g len,
    LengthNat (extract_seq f g len) = len.
Proof.
  induction len.
  - reflexivity.
  - simpl. rewrite LengthConcatNat, IHlen, LengthConsNat.
    rewrite LengthNilNat, Nat.add_comm. reflexivity.
Qed.

Lemma extract_seq_coord : forall {X} (f : forall k, X k) g len i,
    i < len ->
    CoordNat (extract_seq f g len) i = g _ (f i).
Proof.
  induction len.
  - intros. exfalso; inversion H.
  - intros. simpl. apply Nat.le_succ_r in H. destruct H.
    + rewrite CoordConcatNatFirst. apply IHlen, H.
      rewrite extract_seq_length. exact H.
    + inversion H.
      rewrite <- (extract_seq_length f g len) at 4.
      change (LengthNat (extract_seq f g len)) with
          (0 + LengthNat (extract_seq f g len)).
      rewrite CoordConcatNatSecond, CoordConsHeadNat.
      reflexivity.
Qed.

Lemma extract_seq_maxvar : forall {X} (f : forall k, X k) g len k,
    k < len
    -> MaxVar (g _ (f k)) <= MaxVarList (extract_seq f g len).
Proof.
  induction len.
  - intros. exfalso; inversion H.
  - intros. simpl. apply Nat.le_succ_r in H. destruct H.
    + apply (Nat.le_trans _ _ _ (IHlen k H)). clear IHlen.
      unfold MaxVarList.
      rewrite MapConcatNat, MaxConcatNat.
      apply Nat.le_max_l.
    + inversion H. subst k.
      unfold MaxVarList.
      rewrite MapConcatNat, MaxConcatNat.
      refine (Nat.le_trans _ _ _ _ (Nat.le_max_r _ _)).
      rewrite MapConsNat. simpl.
      unfold MapNat. rewrite LengthNilNat. simpl.
      unfold MaxSeqNat. rewrite LengthConsNat, LengthNilNat.
      simpl.
      rewrite CoordConsHeadNat. apply Nat.le_refl.
Qed.

Lemma extract_seq_map : forall {X} (f : forall k, X k) (g : forall k, X k -> nat) h len,
    MapNat h (extract_seq f g len) = extract_seq f (fun k r => h (g k r)) len.
Proof.
  induction len.
  - reflexivity.
  - intros. simpl.
    rewrite MapConcatNat, IHlen. f_equal.
    rewrite MapConsNat. reflexivity.
Qed.

Lemma BindOutputs_subst : forall args A arityA Bk arityB m,
    arityB <= m
    -> (forall k v, k < arityA ->
              arityB < v ->
            VarOccursFreeInFormula v (CoordNat Bk k) = false)
    -> (forall v, v < arityB -> VarOccursFreeInFormula v A = false)
    -> PAnat_subst_multi arityB 0 args (BindOutputs A Bk arityB m)
      = BindOutputs A (MapNat (PAnat_subst_multi arityB 0 args) Bk) arityB m.
Proof.
  intros. unfold BindOutputs.
  rewrite PAnat_subst_multi_and_multi.
  apply f_equal2.
  - rewrite MapMapNat, LengthMapNat.
    apply MapNatExt. intros k H3.
    rewrite LengthRangeNat in H3.
    rewrite CoordRangeNat. 2: exact H3. simpl.
    rewrite CoordMapNat. 2: exact H3.
    rewrite PAnat_subst_multi_SubstDiffCommutes. reflexivity.
    right.
    apply Nat.le_refl. intros i [_ H4].
    rewrite VarOccursInTerm_var. apply Nat.eqb_neq. intro abs.
    rewrite abs in H4.
    apply (Nat.lt_irrefl arityB).
    apply (Nat.le_lt_trans _ _ _ H).
    apply (Nat.le_lt_trans _ (k+m)).
    rewrite <- (Nat.add_0_l m) at 1.
    apply Nat.add_le_mono_r, le_0_n.
    rewrite Nat.add_0_r in H4. exact H4.
  - apply (PAnat_subst_multi_id _ 0).
    intros. apply H1. rewrite Nat.add_0_r in H2.
    apply H2. apply Nat.le_refl. 
Qed.

Lemma PAnat_subst_multi_one : forall numSubst v w args A,
    IsLproposition A = true
    -> w < numSubst
    -> (forall k, v <= k < v + numSubst
            -> VarOccursFreeInFormula k A = true
            -> k = v + w)
    -> PAnat_subst_multi numSubst v args A
      = Subst (PAnat (CoordNat args w)) (v+w) A.
Proof.
  induction numSubst.
  - intros. exfalso. inversion H0.
  - intros. simpl.
    apply Nat.le_succ_r in H0. destruct H0.
    + (* w < numSubst *)
      rewrite (IHnumSubst v w). apply f_equal.
      rewrite Subst_nosubst. reflexivity.
      specialize (H1 (v+numSubst)).
      destruct (VarOccursFreeInFormula (v+numSubst) A). 2: reflexivity.
      exfalso.
      apply Nat.add_cancel_l in H1.
      rewrite H1 in H0. exact (Nat.lt_irrefl _ H0).
      split. 2: rewrite Nat.add_succ_r; apply Nat.le_refl.
      rewrite <- (Nat.add_0_r v) at 1.
      apply Nat.add_le_mono_l, le_0_n.
      reflexivity. 
      apply SubstIsLproposition. exact H.
      apply IsLterm_PAnat. exact H0.
      intros k H4 H5. 
      apply (H1 k).
      split. apply H4.
      rewrite Nat.add_succ_r. apply (Nat.lt_trans _ (v+numSubst)).
      apply H4. apply Nat.le_refl.
      rewrite VarOccursFreeInFormula_SubstDiff in H5.
      exact H5. exact H. intro abs.
      destruct H4. rewrite abs in H3.
      exact (Nat.lt_irrefl _ H3).
      apply PAnat_closed. 
    + (* w = v *)
      inversion H0. subst w. clear H0.
      rewrite (PAnat_subst_multi_id _ v). reflexivity.
      2: exact (Nat.le_refl _).
      intros k H3.
      rewrite VarOccursFreeInFormula_SubstDiff.
      specialize (H1 k).
      destruct (VarOccursFreeInFormula k A). 2: reflexivity.
      exfalso.
      assert (k = v + numSubst).
      { apply H1. 2: reflexivity. split. apply H3.
        rewrite Nat.add_comm. destruct H3.
        apply (Nat.lt_trans _ (numSubst + v)).
        exact H2. apply Nat.le_refl. }
      subst k. destruct H3.
      rewrite Nat.add_comm in H2. exact (Nat.lt_irrefl _ H2).
      exact H. intro abs. subst k. destruct H3.
      rewrite Nat.add_comm in H2. exact (Nat.lt_irrefl _ H2).
      apply PAnat_closed.
Qed.

Lemma FullySubstituteRepr
  : forall k varShift arityA arityB args
      (Bk : nat -> nfun nat arityB nat) C,
    k < arityA
    -> IsLproposition C = true
    -> MaxVar C < varShift
    -> PAnat_subst_multi arityA varShift
                        (nfun_eval_multi arityB Bk arityA args)
                        (Subst (Lvar (k+varShift)) arityB C)
      = Subst (PAnat (nfun_eval arityB args (Bk k))) arityB C.
Proof.
  intros.
  rewrite (PAnat_subst_multi_one _ _ k).
  unfold nfun_eval_multi.
  rewrite CoordMapNat, CoordRangeNat. simpl.
  rewrite SubstSubstNested.
  rewrite SubstTerm_var, Nat.add_comm, Nat.eqb_refl. reflexivity.
  exact H0.
  apply MaxVarDoesNotOccurFree. exact H0.
  apply (Nat.lt_le_trans _ _ _ H1).
  rewrite <- (Nat.add_0_r varShift) at 1.
  apply Nat.add_le_mono_l, le_0_n.
  apply MaxVarFreeSubst. exact H0.
  intros w H2. rewrite VarOccursInTerm_var in H2.
  apply Nat.eqb_eq in H2. subst w.
  apply (Nat.lt_le_trans _ _ _ H1).
  rewrite <- (Nat.add_0_l varShift) at 1.
  apply Nat.add_le_mono_r, le_0_n.
  exact H.
  rewrite LengthRangeNat. exact H.
  apply SubstIsLproposition. exact H0.
  apply IsLterm_var. exact H.
  intros i H2 H3.
  destruct (Nat.eq_dec i (varShift + k)). exact e.
  exfalso.
  destruct (Nat.eq_dec i arityB).
  subst i.
  rewrite VarOccursFreeInFormula_SubstIdem in H3. discriminate.
  exact H0.
  rewrite VarOccursInTerm_var.
  apply Nat.eqb_neq. rewrite Nat.add_comm. exact n.
  rewrite VarOccursFreeInFormula_SubstDiff in H3.
  pose proof (MaxVarDoesNotOccurFree C H0 i).
  rewrite H3 in H4. discriminate H4.
  apply (Nat.lt_le_trans _ _ _ H1). apply H2.
  exact H0. exact n0.
  rewrite VarOccursInTerm_var.
  apply Nat.eqb_neq. rewrite Nat.add_comm. exact n.
Qed.

(* Iteration of SubstSubstDiffCommutes. *)
Lemma ShiftVars_subst : forall v w varShift A u,
    (forall k, k<=v -> w <> k+varShift)
    -> (forall k, k<=v -> VarOccursInTerm k u = false)
    -> v < w
    -> ShiftVars v varShift (Subst u w A)
      = Subst u w (ShiftVars v varShift A).
Proof.
  induction v.
  - intros w varShift A u woccur uoccur vw. simpl.
    rewrite SubstSubstDiffCommutes. reflexivity.
    intro abs. rewrite <- abs in vw. exact (Nat.lt_irrefl _ vw).
    rewrite VarOccursInTerm_var.
    apply Nat.eqb_neq. apply (woccur 0), Nat.le_refl.
    apply uoccur, Nat.le_refl.
  - intros w varShift A u woccur uoccur vw. simpl.
    rewrite SubstSubstDiffCommutes. apply IHv.
    intros K H. apply woccur.
    apply (Nat.le_trans _ _ _ H). apply le_S, Nat.le_refl.
    intros k H. apply uoccur.
    apply (Nat.le_trans _ _ _ H). apply le_S, Nat.le_refl.
    apply (Nat.lt_trans _ (S v)). exact (Nat.le_refl _). exact vw.
    intro abs. rewrite abs in vw. exact (Nat.lt_irrefl _ vw).
    rewrite VarOccursInTerm_var.
    apply Nat.eqb_neq. intro abs. subst w.
    specialize (woccur (S v) (Nat.le_refl _)).
    contradict woccur. reflexivity.
    apply uoccur. apply Nat.le_refl.
Qed.

Lemma PAnat_subst_multi_ShiftVars : forall A varShift arityA args,
    IsLproposition A = true ->
    arityA <= MaxVar A < varShift ->
    PAnat_subst_multi arityA varShift args (ShiftVars arityA varShift A)
    = Subst (Lvar (arityA+varShift)) arityA (PAnat_subst_multi arityA 0 args A).
Proof.
  intros A varShift.
  destruct (Nat.eq_dec varShift 1). (* strange special case for varShift = 1 *)
  intros. subst varShift. destruct arityA. reflexivity.
  exfalso. destruct H0. apply (Nat.le_lt_trans _ _ _ H0) in H1.
  apply le_S_n in H1. inversion H1.
  induction arityA. reflexivity.
  intros args Aprop learity. simpl.
  rewrite ShiftVars_subst. 4: exact (Nat.le_refl _).
  rewrite <- PAnat_subst_multi_SubstDiffCommutes.
  2: right; exact (Nat.le_refl _).
  rewrite <- PAnat_subst_multi_SubstDiffCommutes.
  rewrite IHarityA.
  rewrite SubstSubstDiffCommutes.
  apply f_equal.
  rewrite SubstSubstNested, SubstTerm_var, Nat.add_comm, Nat.eqb_refl.
  apply PAnat_subst_multi_SubstDiffCommutes.
  right. apply Nat.le_refl.
  intros k H; apply PAnat_closed.
  apply PAnat_subst_multi_IsLprop, Aprop. 
  apply PAnat_subst_multi_closed.
  exact Aprop.
  apply MaxVarDoesNotOccurFree. exact Aprop.
  apply (Nat.lt_le_trans _ (varShift+0)).
  rewrite Nat.add_0_r. apply learity.
  apply Nat.add_le_mono_l, le_0_n.
  apply MaxVarFreeSubst.
  apply PAnat_subst_multi_IsLprop, Aprop.
  intros w H.
  rewrite VarOccursInTerm_var in H.
  apply Nat.eqb_eq in H. subst w.
  apply (Nat.le_lt_trans _ _ _ (MaxVar_PAnat_subst_multi _ _ _ _)).
  apply (Nat.lt_le_trans _ (0+varShift)).
  apply learity. apply Nat.add_le_mono_r, le_0_n.
  change (S arityA) with (1 + arityA).
  intro abs. apply Nat.add_cancel_r in abs.
  contradict n. exact abs.
  apply PAnat_closed.
  rewrite VarOccursInTerm_var.
  apply Nat.eqb_neq. intro abs.
  apply (Nat.lt_irrefl (varShift + arityA)).
  rewrite abs at 2. rewrite Nat.add_comm. apply Nat.le_refl.
  exact Aprop. split. apply (Nat.le_trans _ (S arityA)).
  apply le_S, Nat.le_refl. apply learity. apply learity.
  left. apply (Nat.le_lt_trans _ (MaxVar A)); apply learity.
  intros k H. rewrite VarOccursInTerm_var.
  apply Nat.eqb_neq. intro abs. subst k. 
  destruct H.
  rewrite <- Nat.add_succ_r in H0.
  apply Nat.add_lt_mono_l in H0.
  apply (Nat.lt_irrefl varShift).
  apply (Nat.lt_trans _ (S varShift)).
  apply Nat.le_refl. exact H0.
  intros k H. apply PAnat_closed.
  intros k H abs. 
  destruct learity.
  rewrite abs in H0.
  apply (Nat.le_lt_trans _ _ _ H0) in H1.
  rewrite <- (Nat.add_0_l varShift) in H1 at 2.
  apply Nat.add_lt_mono_r in H1. inversion H1.
  intros k H. rewrite VarOccursInTerm_var.
  apply Nat.eqb_neq. intro abs. subst k.
  rewrite <- Nat.add_succ_r in H.
  rewrite <- (Nat.add_0_r arityA) in H at 2.
  apply Nat.add_le_mono_l in H. inversion H.
Qed.

Lemma ComposeRepr_spec_left : forall
 (A arityA arityB : nat)
  (Bk : nat -> nat ^^ arityB --> nat)
  (args : nat)
  (Brep : forall k : nat, FunctionRepresented arityB (Bk k))
  (Aprop : IsLproposition A = true)
  (arityAlastFree : VarOccursFreeInFormula arityA A = true)
  (varfree : forall v : nat, arityA < v -> VarOccursFreeInFormula v A = false)
  (m : nat)
  (Heqm : m =
         Nat.max (MaxVar A)
           (Nat.max arityB
              (MaxVarList
                 (extract_seq Brep
                    (fun (k : nat)
                       (r : (fun k0 : nat => FunctionRepresented arityB (Bk k0)) k)
                     => r) arityA))))
  (absm : arityB <= m)
  (arityAleM : arityA <= MaxVar A),
  IsProved IsWeakHeytingAxiom
    (Limplies
       (Lexists (arityA + S m)
          (Land (Leq (Lvar (arityA + S m)) (Lvar arityB))
             (Subst (Lvar (arityA + S m)) arityA
                (PAnat_subst_multi arityA 0 (nfun_eval_multi arityB Bk arityA args) A))))
       (LexistsMulti (S m) (S arityA)
          (BindOutputs
             (Land (Leq (Lvar (arityA + S m)) (Lvar arityB))
                (ShiftVars arityA (S m) A))
             (extract_seq Brep
                (fun (k : nat) (r : FunctionRepresented arityB (Bk k)) =>
                 PAnat_subst_multi arityB 0 args r) arityA) arityB 
             (S m)))).
Proof.
  intros.
  (* Separate the last variable, which won't be a PAnat *)
  rewrite LexistsMultiSucc.
  apply (LexistsMultiIntroHyp
            arityA (S m) _ _ (nfun_eval_multi arityB Bk arityA args)).
  rewrite IsLproposition_exists.
  apply BindPropVarsLprop.
  rewrite IsLproposition_and, IsLproposition_eq, IsLterm_var, IsLterm_var.
  apply ShiftVarsLprop. exact Aprop.
  intros k H. rewrite extract_seq_coord.
  apply PAnat_subst_multi_IsLprop. apply fr_propprop.
  rewrite extract_seq_length in H. exact H.
  rewrite PAnat_subst_multi_exists. 2: exact (Nat.le_refl _).
  unfold BindOutputs.
  rewrite PAnat_subst_multi_and_multi.
  rewrite MapMapNat, extract_seq_length.
  rewrite (MapNatExt _ (fun k =>
                          Subst (PAnat (nfun_eval arityB args (Bk k))) arityB
                                (PAnat_subst_multi arityB 0 args (Brep k)))).
  rewrite PAnat_subst_multi_and.
  rewrite (PAnat_subst_multi_id arityA (S m) _ _ (S m)).
  3: exact (Nat.le_refl _). rewrite (Nat.add_comm (S m) arityA).
  rewrite PAnat_subst_multi_ShiftVars.
  pose proof (LexistsIntro_impl).
  apply LexistsElim_impl.
  rewrite VarOccursFreeInFormula_exists, Nat.eqb_refl. reflexivity.
  apply LforallIntro.
  assert (IsLproposition (LandMulti
                            (MapNat
                               (fun k : nat =>
                                  Subst (PAnat (nfun_eval arityB args (Bk k))) arityB
                                        (PAnat_subst_multi arityB 0 args (Brep k))) (RangeNat 0 arityA))
                            (Land (Leq (Lvar (arityA + S m)) (Lvar arityB))
                                  (Subst (Lvar (arityA + S m)) arityA
                                         (PAnat_subst_multi arityA 0 (nfun_eval_multi arityB Bk arityA args) A)))) =
          true)
    as hypProp.
  { apply LandMultiLprop. rewrite IsLproposition_and, IsLproposition_eq.
    rewrite IsLterm_var, IsLterm_var. apply SubstIsLproposition.
    apply PAnat_subst_multi_IsLprop. exact Aprop.
    apply IsLterm_var. intros i H0. rewrite LengthMapNat in H0.
    rewrite CoordMapNat. 2: exact H0.
    apply SubstIsLproposition.
    apply PAnat_subst_multi_IsLprop. apply fr_propprop.
    apply IsLterm_PAnat. }
  refine (LimpliesTrans IsWeakHeytingAxiom _ _ _ _
                        (LexistsIntro_impl IsWeakHeytingAxiom _ _
                                           (Lvar (arityA + S m)) _ _ _)).
  rewrite SubstIdemVar.
  apply LandMultiIntro. 
  apply LimpliesRefl.
  rewrite IsLproposition_and, IsLproposition_eq.
  rewrite IsLterm_var, IsLterm_var.
  apply SubstIsLproposition.
  apply PAnat_subst_multi_IsLprop. exact Aprop.
  apply IsLterm_var.
  intros k H0. rewrite LengthMapNat in H0.
  rewrite CoordMapNat. 2: exact H0.
  rewrite LengthRangeNat in H0.
  rewrite CoordRangeNat. 2: exact H0.
  apply DropHypothesis.
  rewrite IsLproposition_and, IsLproposition_eq, IsLterm_var, IsLterm_var.
  apply SubstIsLproposition.
  apply PAnat_subst_multi_IsLprop. exact Aprop.
  apply IsLterm_var.
  pose proof (FormulaRepresents_alt
                arityB (Bk k) _ args (fr_rep _ _ (Brep k))
                (fr_propprop _ _ (Brep k)) (nfun_eval arityB args (Bk k)))
    as [H1 _].
  apply H1. reflexivity.
  exact hypProp. apply IsLterm_var. exact hypProp.
  apply IsFreeForSubstIdemVar. exact hypProp.
  exact Aprop.
  split. exact arityAleM. 
  apply le_n_S. rewrite Heqm. apply Nat.le_max_l.
  intros v H. unfold Leq.
  rewrite VarOccursFreeInFormula_rel2, VarOccursInTerm_var, VarOccursInTerm_var.
  apply Bool.orb_false_intro.
  apply Nat.eqb_neq. intro abs. destruct H.
  rewrite abs in H0. exact (Nat.lt_irrefl _ H0).
  apply Nat.eqb_neq. intro abs. destruct H.
  rewrite abs in H. apply (Nat.lt_irrefl m).
  exact (Nat.lt_le_trans _ _ _ H absm).
  intros k H. rewrite LengthRangeNat in H.
  rewrite extract_seq_coord, CoordRangeNat. 
  apply (FullySubstituteRepr k (S m) arityA arityB).
  exact H.
  apply PAnat_subst_multi_IsLprop, fr_propprop.
  apply (Nat.le_lt_trans _ _ _ (MaxVar_PAnat_subst_multi _ _ _ _)).
  apply le_n_S.
  rewrite Heqm.
  refine (Nat.le_trans _ _ _ _ (Nat.le_max_r _ _)).
  refine (Nat.le_trans _ _ _ _ (Nat.le_max_r _ _)).
  apply (extract_seq_maxvar Brep (fun f r => fr_prop _ _ r)).
  exact H.
  exact H. rewrite CoordRangeNat. exact H. exact H.
Qed.

Lemma LandMultiFlip : forall Bk B A,
    IsLproposition A = true
    -> IsLproposition B = true
    -> (forall k, k < LengthNat Bk -> IsLproposition (CoordNat Bk k) = true)
    -> IsProved IsWeakHeytingAxiom 
               (Limplies (LandMulti (ConsNat B Bk) A)
                         (LandMulti (ConsNat A Bk) B)).
Proof.
  intros. rewrite LandMultiCons, LandMultiCons.
  apply LandIntroHyp.
  - apply (LimpliesTrans _ _ (LandMulti Bk B)).
    apply LandElim2_impl.
    exact H.
    apply LandMultiLprop.
    exact H0. exact H1.
    apply LandMultiElim1. exact H0. exact H1.
  - destruct (LengthNat Bk) eqn:des.
    unfold LandMulti. rewrite des. apply LandElim1_impl.
    exact H. exact H0.
    rewrite (HeadTailDecompNat Bk).
    rewrite LandMultiCons, LandMultiCons.
    apply LandIntroHyp. apply LandElim1_impl. exact H.
    rewrite IsLproposition_and, H0.
    apply LandMultiLprop. apply H1. apply le_n_S, le_0_n.
    intros i H2. rewrite CoordTailNat. apply H1.
    rewrite LengthTailNat, des in H2.
    apply le_n_S, H2.
    apply (LimpliesTrans _ _ (Land B (LandMulti (TailNat Bk) (CoordNat Bk 0)))).
    apply LandElim2_impl. exact H.
    rewrite IsLproposition_and, H0.
    apply LandMultiLprop. apply H1. apply le_n_S, le_0_n.
    intros i H2. rewrite CoordTailNat. apply H1.
    rewrite LengthTailNat, des in H2.
    apply le_n_S, H2.
    apply LandElim2_impl. exact H0.
    apply LandMultiLprop. apply H1. apply le_n_S, le_0_n.
    intros. rewrite CoordTailNat. apply H1.
    rewrite LengthTailNat, des in H2.
    apply le_n_S, H2.
    rewrite des. apply le_n_S, le_0_n. 
Qed.

Lemma PAnat_subst_multi_assoc : forall arityA args i k A,
  Subst (PAnat k) i (PAnat_subst_multi arityA (S i) args A)
  = PAnat_subst_multi (S arityA) i (ConsNat k args) A.
Proof.
  induction arityA.
  - intros. simpl. rewrite Nat.add_0_r.
    rewrite CoordConsHeadNat. reflexivity.
  - intros. simpl.
    rewrite <- PAnat_subst_multi_SubstDiffCommutes.
    rewrite SubstSubstDiffCommutes, IHarityA. simpl. 
    rewrite PAnat_subst_multi_SubstDiffCommutes. apply f_equal.
    rewrite CoordConsTailNat, Nat.add_succ_r.
    rewrite SubstSubstDiffCommutes. reflexivity.
    intro abs.
    apply (Nat.lt_irrefl (i+arityA)).
    rewrite <- abs at 2. apply Nat.le_refl.
    apply PAnat_closed. apply PAnat_closed.
    right. apply le_S, Nat.le_refl.
    intros j H; apply PAnat_closed.
    intro abs. apply (Nat.lt_irrefl i).
    rewrite abs at 2. apply le_n_S.
    rewrite <- (Nat.add_0_r i) at 1.
    apply Nat.add_le_mono_l, le_0_n. 
    apply PAnat_closed. apply PAnat_closed.
    right. apply Nat.le_refl.
    intros. apply PAnat_closed.
Qed.

Lemma LandMultiSubstElim : forall arityA i A arityB varShift
                             (Bk : nat -> nfun nat arityB nat) (args : nat)
      (Brep : forall k, FunctionRepresented arityB (Bk k)),
    IsLproposition A = true -> 
    arityB < varShift ->
    (forall k, i <= k < i+arityA -> MaxVar (Brep k) < varShift) ->
  IsProved IsWeakHeytingAxiom
    (Limplies
       (LandMulti
          (MapNat
             (fun k : nat =>
              Subst (Lvar (k + varShift)) arityB
                (PAnat_subst_multi arityB 0 args (Brep k))) 
             (RangeNat i arityA))
          A)
       (PAnat_subst_multi arityA (i+varShift)
                          (nfun_eval_multi arityB (fun k => Bk (i+k)) arityA args) A)).
Proof.
  induction arityA.
  - intros. simpl.
    unfold MapNat. change (LengthNat NilNat) with 0. simpl.
    unfold LandMulti. change (LengthNat NilNat) with 0.
    apply LimpliesRefl. exact H.
  - intros i A arityB varShift Bk args Brep Aprop arbshift bkshift.
    simpl (RangeNat i (S arityA)).
    rewrite MapConsNat. 
    refine (LimpliesTrans _ _ _ _ (LandMultiFlip _ _ _ _ _ _) _).
    exact Aprop.
    apply SubstIsLproposition.
    apply PAnat_subst_multi_IsLprop. apply fr_propprop.
    apply IsLterm_var. intros k H0. rewrite LengthMapNat in H0.
    rewrite CoordMapNat. 2: exact H0. rewrite LengthRangeNat in H0.
    apply SubstIsLproposition.
    apply PAnat_subst_multi_IsLprop. apply fr_propprop.
    apply IsLterm_var. rewrite LandMultiCons.
    apply CommuteHypotheses, PushHypothesis.
    apply (LimpliesTrans _ _ (PAnat_subst_multi arityA (S i + varShift)
                     (nfun_eval_multi arityB (fun k => Bk (S i+ k)) arityA args) A)).
    apply IHarityA. exact Aprop. clear IHarityA. exact arbshift. 
    intros k H. apply bkshift. split.
    apply (Nat.le_trans _ (S i)). apply le_S, Nat.le_refl. apply H.
    rewrite Nat.add_succ_r. apply H. clear IHarityA.
    (* Add substitution of the first variable *)
    apply PullHypothesis, CommuteHypotheses, PushHypothesis.
    apply (LimpliesTrans
             _ _ (Leq (Lvar (i+varShift)) (PAnat (nfun_eval arityB args (Bk i))))).
    pose proof (fr_rep _ _ (Brep i) args) as H.
    apply (LforallElim _ _ _ (Lvar (i+varShift))) in H.
    rewrite Subst_equiv, Subst_eq, SubstTerm_var, Nat.eqb_refl, SubstTerm_PAnat in H.
    apply LandElim1 in H. exact H.
    apply IsLterm_var.
    apply MaxVarFreeSubst.
    rewrite IsLproposition_equiv.
    rewrite PAnat_subst_multi_IsLprop, IsLproposition_eq, IsLterm_var.
    apply IsLterm_PAnat. apply fr_propprop.
    intros w H0.
    rewrite VarOccursInTerm_var in H0. apply Nat.eqb_eq in H0. subst w.
    rewrite MaxVar_equiv. unfold Leq. rewrite MaxVar_rel2.
    rewrite MaxVarTerm_var, MaxVarTerm_PAnat.
    apply Nat.max_lub_lt.
    apply (Nat.le_lt_trans _ _ _ (MaxVar_PAnat_subst_multi _ _ _ _)).
    apply (Nat.lt_le_trans _ varShift).
    apply (bkshift i). split. apply Nat.le_refl.
    rewrite Nat.add_succ_r. apply le_n_S.
    rewrite <- (Nat.add_0_r i) at 1.
    apply Nat.add_le_mono_l, le_0_n.
    rewrite <- (Nat.add_0_l varShift) at 1.
    apply Nat.add_le_mono_r, le_0_n.
    rewrite Nat.max_comm. simpl.
    apply (Nat.lt_le_trans _ _ _ arbshift).
    rewrite <- (Nat.add_0_l varShift) at 1.
    apply Nat.add_le_mono_r, le_0_n.
    apply LeqElimSubstVarPAnat.
    rewrite IsLproposition_implies.
    rewrite PAnat_subst_multi_IsLprop, PAnat_subst_multi_IsLprop.
    reflexivity. exact Aprop. exact Aprop.
    rewrite Subst_implies.
    rewrite PAnat_subst_multi_assoc.
    rewrite Subst_nosubst.
    replace (ConsNat (nfun_eval arityB args (Bk i))
             (nfun_eval_multi arityB (fun k : nat => Bk (S i + k)) arityA args))
      with (nfun_eval_multi arityB (fun k : nat => Bk (i + k)) (S arityA) args).
    apply LimpliesRefl.
    apply PAnat_subst_multi_IsLprop. exact Aprop.
    unfold nfun_eval_multi. simpl (RangeNat 0 (S arityA)).
    rewrite MapConsNat, Nat.add_0_r.
    apply f_equal.
    apply TruncatedEqNat.
    rewrite LengthMapNat, LengthMapNat, LengthRangeNat, LengthRangeNat.
    reflexivity.
    rewrite LengthMapNat, LengthMapNat, MapNatTruncated, MapNatTruncated.
    rewrite LengthRangeNat, LengthRangeNat, RangeNatTruncated, RangeNatTruncated.
    reflexivity.
    intros k H. rewrite LengthMapNat in H.
    rewrite CoordMapNat. 2: exact H.
    rewrite CoordMapNat. rewrite LengthRangeNat in H.
    rewrite CoordRangeNat, CoordRangeNat. simpl.
    rewrite Nat.add_succ_r. reflexivity. exact H. exact H.
    rewrite LengthRangeNat. rewrite LengthRangeNat in H. exact H.
    apply PAnat_subst_multi_in_range. exact Aprop.
    split. apply Nat.le_refl.
    rewrite Nat.add_succ_r. apply le_n_S.
    rewrite <- (Nat.add_0_r (i+varShift)) at 1.
    apply Nat.add_le_mono_l, le_0_n.
Qed.

(* Evaluating ComposeRepr A Bk Barity on args is the same as
   evaluating the Bk's first and then evaluate A on those values. *)
Lemma ComposeRepr_spec
  : forall A arityA arityB (Bk : nat -> nfun nat arityB nat) (args : nat)
      (Brep : forall k, FunctionRepresented arityB (Bk k)),
    IsLproposition A = true
    -> VarOccursFreeInFormula arityA A = true
    -> (forall v, arityA < v -> VarOccursFreeInFormula v A = false)
    (* Equivalence between formulas with 1 free variable, Lvar arityB *)
    -> let m := arityA + S (Nat.max (MaxVar A) (Nat.max arityB (MaxVarList (extract_seq Brep (fun k r => fr_prop _ _ r) arityA)))) in 
    IsProved IsWeakHeytingAxiom 
             (Lequiv (Lexists m (Land (Leq (Lvar m) (Lvar arityB))
                                      (Subst (Lvar m) arityA
                              (PAnat_subst_multi arityA 0
                                    (nfun_eval_multi arityB Bk arityA args) A))))
                       (PAnat_subst_multi arityB 0
                                    args (ComposeRepr A (extract_seq Brep (fun k r => fr_prop _ _ r) arityA) arityB))).
Proof.
  intros A arityA arityB Bk args Brep Aprop arityAlastFree varfree.
  unfold ComposeRepr.
  rewrite extract_seq_length.
  remember (Nat.max (MaxVar A)
                    (Nat.max arityB (MaxVarList (extract_seq Brep (fun k r => fr_prop _ _ r) arityA))))
           as m.
  assert (arityB <= m) as absm.
  { rewrite Heqm.
    apply (Nat.le_trans _ _ _ (Nat.le_max_l _ _) (Nat.le_max_r _ _)). }
  assert (arityA <= MaxVar A) as arityAleM.
  { destruct (le_lt_dec arityA (MaxVar A)). exact l.
    exfalso.
    pose proof (MaxVarDoesNotOccurFree A Aprop arityA l) as H.
    rewrite arityAlastFree in H. discriminate. } 
  rewrite PAnat_subst_multi_exists_multi. 2: apply le_S, absm.
  rewrite (BindOutputs_subst _ _ arityA). 2: apply le_S, absm.
  rewrite extract_seq_map.
  apply LandIntro.
  - exact (ComposeRepr_spec_left _ _ _ _ _ _
                                 Aprop arityAlastFree varfree m Heqm absm arityAleM).
  - apply LexistsMultiElim.
    intros k H. unfold Leq.
    rewrite VarOccursFreeInFormula_exists.
    rewrite VarOccursFreeInFormula_and, VarOccursFreeInFormula_rel2.
    rewrite VarOccursInTerm_var, VarOccursInTerm_var.
    apply Nat.le_succ_r in H. destruct H.
    2: inversion H; rewrite Nat.add_comm, Nat.eqb_refl; reflexivity.
    apply Bool.andb_false_intro2.
    apply Bool.orb_false_intro.
    apply Bool.orb_false_intro.
    apply Nat.eqb_neq. intro abs.
    rewrite Nat.add_comm in abs.
    apply Nat.add_cancel_r in abs.
    rewrite abs in H. exact (Nat.lt_irrefl _ H).
    apply Nat.eqb_neq. intro abs.
    apply (Nat.lt_irrefl arityB).
    apply (Nat.le_lt_trans _ _ _ absm). unfold lt.
    rewrite <- (Nat.add_0_r (S m)).
    rewrite <- abs.
    apply Nat.add_le_mono_l, le_0_n.
    apply VarOccursFreeInFormula_SubstClosed.
    apply PAnat_subst_multi_closed. exact Aprop.
    apply MaxVarDoesNotOccurFree. exact Aprop.
    simpl.
    apply le_n_S. apply (Nat.le_trans _ (m+0)).
    rewrite Nat.add_0_r, Heqm. apply Nat.le_max_l.
    apply Nat.add_le_mono_l, le_0_n.
    rewrite VarOccursInTerm_var.
    apply Nat.eqb_neq. intro abs.
    rewrite Nat.add_comm in abs.
    apply Nat.add_cancel_r in abs.
    rewrite abs in H. exact (Nat.lt_irrefl _ H).
    refine (LimpliesTrans IsWeakHeytingAxiom
                         _ _ _ _
     (LexistsIntro_impl IsWeakHeytingAxiom
                                  _ (arityA + S m) (Lvar (arityA + S m)) _ _ _)).
    rewrite SubstIdemVar.
    unfold BindOutputs.
    rewrite extract_seq_length. 
    rewrite (MapNatExt _ (fun k => Subst (Lvar (k + S m)) arityB (PAnat_subst_multi arityB 0 args (Brep k)))).
    apply LandIntroHyp.
    refine (LimpliesTrans _ _ _ _
                          (LandMultiElim1 _ _ _ _) _).
    rewrite IsLproposition_and, IsLproposition_eq, IsLterm_var, IsLterm_var.
    apply ShiftVarsLprop. exact Aprop.
    intros i H. rewrite LengthMapNat, LengthRangeNat in H.
    rewrite CoordMapNat. apply SubstIsLproposition.
    apply PAnat_subst_multi_IsLprop. apply fr_propprop.
    apply IsLterm_var. rewrite LengthRangeNat. exact H.
    apply LandElim1_impl.
    rewrite IsLproposition_eq, IsLterm_var. apply IsLterm_var.
    apply ShiftVarsLprop. exact Aprop.
    refine (LimpliesTrans _ _ _ _
                         (LandMultiSubstElim _ _ _ _ _ _ _ _ _ _ _) _).
    rewrite IsLproposition_and, IsLproposition_eq, IsLterm_var, IsLterm_var.
    apply ShiftVarsLprop, Aprop.
    apply le_n_S, absm.
    intros k [_ H]. apply le_n_S.
    rewrite Heqm.
    refine (Nat.le_trans _ _ _ _ (Nat.le_max_r _ _)).
    refine (Nat.le_trans _ _ _ _ (Nat.le_max_r _ _)).
    refine (Nat.le_trans _ _ _ _ (extract_seq_maxvar _ _ _ k _)).
    apply Nat.le_refl. exact H.
    rewrite PAnat_subst_multi_and.
    rewrite PAnat_subst_multi_ShiftVars.
    apply LandElim2_impl.
    apply PAnat_subst_multi_IsLprop.
    rewrite IsLproposition_eq, IsLterm_var. apply IsLterm_var.
    apply SubstIsLproposition.
    apply PAnat_subst_multi_IsLprop, Aprop.
    apply IsLterm_var. exact Aprop.
    split. exact arityAleM. apply le_n_S.
    rewrite Heqm. apply Nat.le_max_l.
    intros k H. rewrite LengthRangeNat in H.
    rewrite extract_seq_coord, CoordRangeNat. reflexivity.
    exact H. rewrite CoordRangeNat. exact H. exact H.
    rewrite IsLproposition_and, IsLproposition_eq, IsLterm_var, IsLterm_var.
    apply SubstIsLproposition.
    apply PAnat_subst_multi_IsLprop. exact Aprop.
    apply IsLterm_var. apply IsLterm_var.
    rewrite IsLproposition_and, IsLproposition_eq, IsLterm_var, IsLterm_var.
    apply SubstIsLproposition.
    apply PAnat_subst_multi_IsLprop. exact Aprop.
    apply IsLterm_var.
    apply IsFreeForSubstIdemVar.
    rewrite IsLproposition_and, IsLproposition_eq, IsLterm_var, IsLterm_var.
    apply SubstIsLproposition.
    apply PAnat_subst_multi_IsLprop. exact Aprop.
    apply IsLterm_var.
  - intros k v H0 H1.
    rewrite extract_seq_coord. 
    exact (fr_vars _ _ (Brep k) _ H1). exact H0.
  - intros v H. unfold Leq.
    rewrite VarOccursFreeInFormula_and, VarOccursFreeInFormula_rel2.
    rewrite VarOccursInTerm_var, VarOccursInTerm_var.
    apply Bool.orb_false_intro.
    apply Bool.orb_false_intro.
    apply Nat.eqb_neq. intro abs. rewrite abs in H.
    apply (Nat.lt_le_trans _ _ _ H) in absm.
    rewrite Nat.add_succ_r in absm.
    rewrite <- (Nat.add_0_l m) in absm at 2.
    apply (Nat.add_lt_mono_r (S arityA)) in absm. inversion absm.
    apply Nat.eqb_neq. intro abs.
    rewrite abs in H. exact (Nat.lt_irrefl _ H).
    rewrite ShiftVarsVars.
    destruct (arityA <? v) eqn:des.
    apply Nat.ltb_lt in des.
    rewrite Bool.andb_true_r. apply varfree, des.
    rewrite Bool.andb_false_r. reflexivity.
    exact Aprop. left. apply le_n_S.
    refine (Nat.le_trans _ _ _ _ absm).
    apply Nat.lt_le_incl, H.
Qed.

(* Composition u(v0, v1, ..., vn-1) *)
Fixpoint ncompose {n p : nat} (u : nfun nat n nat) (vk : nat -> nfun nat p nat)
         {struct n} : nfun nat p nat.
Proof.
  destruct n.
  - (* constant p-ary function *)
    exact (ncurry nat nat p (fun _ => u)).
  - exact (ncurry nat nat p (fun xp => let v0 := nuncurry _ _ _ (vk 0) xp in
                                nuncurry _ _ _ (ncompose n p (u v0) (fun k => vk (S k))) xp)).
Defined.

Fixpoint seq_nprod (args n : nat) : nprod nat n :=
  match n with
  | O => tt
  | S k => pair (HeadNat args) (seq_nprod (TailNat args) k)
  end.

Lemma nfun_eval_curry : forall arity args f,
    nfun_eval arity args (ncurry nat nat arity f)
    = f (seq_nprod args arity).
Proof.
  induction arity. reflexivity.
  intros. simpl. rewrite IHarity. reflexivity.
Qed.

Lemma nfun_eval_uncurry : forall arity args f,
    nuncurry nat nat arity f (seq_nprod args arity)
    = nfun_eval arity args f.
Proof.
  induction arity. reflexivity.
  intros. simpl. rewrite IHarity. reflexivity.
Qed.

Lemma nfun_eval_ext : forall arity f x y,
    (forall k, k < arity -> CoordNat x k = CoordNat y k)
    -> nfun_eval arity x f = nfun_eval arity y f.
Proof.
  induction arity. reflexivity.
  intros. simpl. rewrite H.
  apply (IHarity (f (CoordNat y 0)) (TailNat x) (TailNat y)).
  intros. rewrite CoordTailNat, CoordTailNat. apply H.
  apply le_n_S, H0. apply le_n_S, le_0_n.
Qed.

Lemma nfun_eval_ncompose : forall n arity args (u : nfun nat n nat) (vk : nat -> nfun nat arity nat),
  nfun_eval _ args (ncompose u vk)
  = nfun_eval _ (nfun_eval_multi arity vk n args) u.
Proof.
  induction n.
  - intros. simpl. revert args. clear vk.
    induction arity. reflexivity.
    simpl. intro args. apply IHarity.
  - intros. simpl. rewrite nfun_eval_curry.
    rewrite nfun_eval_uncurry. rewrite IHn.
    unfold nfun_eval_multi at 3.
    rewrite CoordMapNat, CoordRangeNat. simpl.
    rewrite nfun_eval_uncurry.
    apply nfun_eval_ext.
    intros k H.
    unfold nfun_eval_multi. simpl.
    rewrite MapConsNat, TailConsNat.
    rewrite CoordMapNat, CoordMapNat. 
    rewrite CoordRangeNat, CoordRangeNat. reflexivity.
    exact H. exact H. rewrite LengthRangeNat. exact H.
    rewrite LengthRangeNat. exact H.
    apply le_n_S, le_0_n.
    rewrite LengthRangeNat.
    apply le_n_S, le_0_n.
Qed.

Lemma ComposeRepr_n : forall n arity (u : nfun nat n nat) (vk : nat -> nfun nat arity nat),
    FunctionRepresented n u
    -> (forall k, FunctionRepresented arity (vk k)) (* only k < n is used *)
    -> FunctionRepresented arity (ncompose u vk).
Proof.
  intros n arity u vk uRep vRep. 
  apply (Build_FunctionRepresented
           arity _ (ComposeRepr uRep
                               (extract_seq vRep
                    (fun (k : nat)
                       (r : (fun k0 : nat => FunctionRepresented arity (vk k0)) k)
                     => r) n) 
                               arity)).
  - intro args.
    pose proof (ComposeRepr_spec
                  uRep n arity vk args vRep
                  (fr_propprop _ _ uRep) (fr_freevar _ _ uRep) (fr_vars _ _ uRep))
      as H1.
    apply LforallIntro.
    remember (n +
                S
                  (Nat.max (MaxVar uRep)
                     (Nat.max arity
                        (MaxVarList
                           (extract_seq vRep
                              (fun (k : nat) (r : FunctionRepresented arity (vk k))
                               => r) n))))) as m.
    apply LequivSym.
    refine (LequivTrans _ _ _ _ _ H1). clear H1.
    (* ComposeRepr is removed *)
    rewrite nfun_eval_ncompose.
    (* ncompose is removed *)
    assert (m =? arity = false) as H.
    { apply Nat.eqb_neq. intro abs. apply (Nat.lt_irrefl arity).
      rewrite <- abs at 2. rewrite Heqm. 
      rewrite Nat.add_succ_r. apply le_n_S.
      rewrite Nat.max_comm, <- Nat.max_assoc.
      apply (Nat.le_trans _ (n+arity)).
      apply (Nat.add_le_mono_r 0 n), le_0_n.
      apply Nat.add_le_mono_l. apply Nat.le_max_l. }
    assert (VarOccursFreeInFormula arity
    (Subst (Lvar m) n (PAnat_subst_multi n 0 (nfun_eval_multi arity vk n args) uRep)) =
            false)
      as aritynooccur.
    { destruct (Nat.lt_trichotomy arity n).
      rewrite VarOccursFreeInFormula_SubstDiff.
      apply PAnat_subst_multi_in_range.
      apply fr_propprop.
      split. apply le_0_n. exact H0.
      apply PAnat_subst_multi_IsLprop. apply fr_propprop.
      intro abs. rewrite abs in H0. exact (Nat.lt_irrefl n H0).
      rewrite VarOccursInTerm_var, Nat.eqb_sym. exact H.
      destruct H0. subst arity.
      apply VarOccursFreeInFormula_SubstIdem.
      apply PAnat_subst_multi_IsLprop. apply fr_propprop.
      rewrite VarOccursInTerm_var. rewrite Nat.eqb_sym. exact H.
      rewrite VarOccursFreeInFormula_SubstDiff.
      apply PAnat_subst_multi_closed. apply fr_propprop.
      apply fr_vars, H0.
      apply PAnat_subst_multi_IsLprop. apply fr_propprop.
      intro abs. rewrite abs in H0. exact (Nat.lt_irrefl n H0).
      rewrite VarOccursInTerm_var. rewrite Nat.eqb_sym. exact H. } 
    apply LandIntro.
    + apply LeqElimSubstVar.
      rewrite IsLproposition_exists, IsLproposition_and, IsLproposition_eq.
      rewrite IsLterm_var, IsLterm_var.
      apply SubstIsLproposition.
      apply PAnat_subst_multi_IsLprop.
      apply fr_propprop. apply IsLterm_var.
      apply IsLterm_PAnat.
      apply IsFreeForSubst_PAnat.
      rewrite IsLproposition_exists, IsLproposition_and, IsLproposition_eq.
      rewrite IsLterm_var, IsLterm_var.
      apply SubstIsLproposition.
      apply PAnat_subst_multi_IsLprop.
      apply fr_propprop. apply IsLterm_var.
      rewrite Subst_exists.
      rewrite H.
      rewrite Subst_and, Subst_eq, SubstTerm_var.
      rewrite H. rewrite SubstTerm_var, Nat.eqb_refl.
      rewrite Subst_nosubst.
      apply (LexistsIntro IsWeakHeytingAxiom
                          _ _ (PAnat (nfun_eval n (nfun_eval_multi arity vk n args) u))).
      apply IsLterm_PAnat.
      rewrite IsLproposition_and, IsLproposition_eq, IsLterm_var.
      rewrite IsLterm_PAnat. apply SubstIsLproposition.
      apply PAnat_subst_multi_IsLprop. 
       apply fr_propprop. apply IsLterm_var.
      apply IsFreeForSubst_PAnat.
      rewrite IsLproposition_and, IsLproposition_eq, IsLterm_var.
      rewrite IsLterm_PAnat. apply SubstIsLproposition.
      apply PAnat_subst_multi_IsLprop. 
      apply fr_propprop. apply IsLterm_var.
      rewrite Subst_and, Subst_eq, SubstTerm_var, Nat.eqb_refl.
      apply LandIntro.
      rewrite SubstTerm_PAnat.
      apply LeqRefl. apply IsLterm_PAnat.
      rewrite SubstSubstNested, SubstTerm_var, Nat.eqb_refl.
      apply (FormulaRepresents_alt
                    n u (fr_prop _ _ uRep)
                    (nfun_eval_multi arity vk n args)
                    (fr_rep _ _ uRep)
                    (fr_propprop _ _ uRep)).
      reflexivity.
      apply PAnat_subst_multi_IsLprop. 
      apply fr_propprop.
      apply PAnat_subst_multi_closed.
      apply fr_propprop.
      apply MaxVarDoesNotOccurFree. apply fr_propprop.
      rewrite Heqm, Nat.add_succ_r.
      apply le_n_S.
      apply (Nat.le_trans _ (n+MaxVar uRep)).
      apply (Nat.add_le_mono_r 0 n), le_0_n.
      apply Nat.add_le_mono_l. apply Nat.le_max_l.
      apply MaxVarFreeSubst_var.
      apply PAnat_subst_multi_IsLprop. 
      apply fr_propprop.
      rewrite Heqm, Nat.add_succ_r.
      apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_PAnat_subst_multi _ _ _ _)).
      apply (Nat.le_trans _ (n+MaxVar uRep)).
      apply (Nat.add_le_mono_r 0 n), le_0_n.
      apply Nat.add_le_mono_l. apply Nat.le_max_l.
      exact aritynooccur.
    + apply LexistsElim_impl.
      unfold Leq.
      rewrite VarOccursFreeInFormula_rel2, VarOccursInTerm_var.
      rewrite PAnat_closed, H. reflexivity. 
      apply LforallIntro.
      apply PushHypothesis.
      apply (LimpliesTrans _ _ (Leq (Lvar arity) (Lvar m))).
      apply LeqSym_impl. apply IsLterm_var. apply IsLterm_var.
      apply LeqElimSubstVar.
      rewrite IsLproposition_implies.
      rewrite SubstIsLproposition.
      rewrite IsLproposition_eq, IsLterm_var.
      apply IsLterm_PAnat.
      apply PAnat_subst_multi_IsLprop. apply fr_propprop.
      apply IsLterm_var. apply IsLterm_var.
      rewrite IsFreeForSubst_implies.
      unfold Leq. rewrite IsFreeForSubst_rel2, Bool.andb_true_r.
      apply IsFreeForSubst_nosubst.
      apply SubstIsLproposition.
      apply PAnat_subst_multi_IsLprop. apply fr_propprop.
      apply IsLterm_var.
      exact aritynooccur.
      rewrite Subst_implies.
      rewrite Subst_nosubst, Subst_eq, SubstTerm_var, Nat.eqb_refl.
      2: exact aritynooccur.
      rewrite SubstTerm_PAnat. 
      pose proof (fr_rep _ _ uRep (nfun_eval_multi arity vk n args)).
      apply (LforallElim IsWeakHeytingAxiom _ _ (Lvar m)) in H0.
      rewrite Subst_equiv, Subst_eq, SubstTerm_var in H0.
      rewrite SubstTerm_PAnat, Nat.eqb_refl in H0.
      apply LandElim1 in H0. exact H0.
      apply IsLterm_var. unfold Leq.
      rewrite IsFreeForSubst_equiv, IsFreeForSubst_rel2, Bool.andb_true_r.
      apply MaxVarFreeSubst_var.
      apply PAnat_subst_multi_IsLprop. apply fr_propprop.
      rewrite Heqm, Nat.add_succ_r. apply le_n_S.
      apply (Nat.le_trans _ _ _ (MaxVar_PAnat_subst_multi _ _ _ _)).
      apply (Nat.le_trans _ (n+MaxVar uRep)).
      apply (Nat.add_le_mono_r 0 n), le_0_n.
      apply Nat.add_le_mono_l. apply Nat.le_max_l.
  - apply ComposeReprLprop. apply fr_propprop. 
    intros i H. rewrite extract_seq_coord.
    apply fr_propprop. rewrite extract_seq_length in H. exact H.
  - intros. apply ComposeReprVars.
    apply fr_propprop.
    intros. apply fr_vars.
    rewrite extract_seq_length in H0. exact H0.
    intros.
    rewrite extract_seq_coord. 
    rewrite extract_seq_length in H0.
    apply fr_vars. exact H1.
    rewrite extract_seq_length in H0. exact H0.
    intros. rewrite extract_seq_coord. 
    apply fr_propprop.
    rewrite extract_seq_length in H0. exact H0. exact H.
Qed.

Lemma ComposeRepr_11 : forall (u: nat -> nat) (v : nat -> nat),
    FunctionRepresented 1 u
    -> FunctionRepresented 1 v
    -> FunctionRepresented 1 (fun n => u (v n)).
Proof.
  intros u v urep vrep.
  apply (ComposeRepr_n 1 1 u (fun k => v) urep).
  intros [|k]. exact vrep. exact vrep.
Qed. 

Lemma ComposeRepr_12 : forall (u:nat->nat) (v : nat -> nat -> nat),
    FunctionRepresented 1 u
    -> FunctionRepresented 2 v
    -> FunctionRepresented 2 (fun n k => u (v n k)).
Proof.
  intros u v urep vrep.
  apply (ComposeRepr_n 1 2 u (fun k => v) urep).
  intros [|k]. exact vrep. exact vrep.
Qed. 

Lemma ComposeRepr_21 : forall (u: nat -> nat -> nat) (v w : nat -> nat),
    FunctionRepresented 2 u
    -> FunctionRepresented 1 v
    -> FunctionRepresented 1 w
    -> FunctionRepresented 1 (fun n => u (v n) (w n)).
Proof.
  intros u v w urep vrep wrep.
  apply (ComposeRepr_n 2 1 u (fun k => match k with | O => v | S _ => w end) urep).
  intros [|k]. exact vrep. exact wrep.
Qed. 

Lemma ComposeRepr_22 : forall u v w : nat -> nat -> nat,
    FunctionRepresented 2 u
    -> FunctionRepresented 2 v
    -> FunctionRepresented 2 w
    -> FunctionRepresented 2 (fun n k => u (v n k) (w n k)).
Proof.
  intros u v w urep vrep wrep.
  apply (ComposeRepr_n 2 2 u (fun k => match k with
                                    | O => v
                                    | _ => w
                                    end) urep).
  intros k. 
  destruct k. exact vrep. exact wrep.
Qed.

Lemma ComposeRepr_13 : forall (u:nat->nat) (v : nat -> nat -> nat -> nat),
    FunctionRepresented 1 u
    -> FunctionRepresented 3 v
    -> FunctionRepresented 3 (fun i j k => u (v i j k)).
Proof.
  intros u v urep vrep.
  apply (ComposeRepr_n 1 3 u (fun k => v) urep).
  intros [|k]. exact vrep. exact vrep.
Qed. 

Lemma ComposeRepr_31 : forall (u : nat -> nat -> nat -> nat) (v w s : nat -> nat),
    FunctionRepresented 3 u
    -> FunctionRepresented 1 v
    -> FunctionRepresented 1 w
    -> FunctionRepresented 1 s
    -> FunctionRepresented 1 (fun n => u (v n) (w n) (s n)).
Proof.
  intros u v w s urep vrep wrep srep.
  apply (ComposeRepr_n 3 1 u (fun k => match k with
                                    | O => v
                                    | 1 => w
                                    | _ => s end) urep).
  intros [|k]. exact vrep.
  destruct k. exact wrep. exact srep.
Qed. 

Lemma ComposeRepr_23 : forall (u : nat -> nat -> nat) (v w : nat -> nat -> nat -> nat),
    FunctionRepresented 2 u
    -> FunctionRepresented 3 v
    -> FunctionRepresented 3 w
    -> FunctionRepresented 3 (fun i j k => u (v i j k) (w i j k)).
Proof.
  intros u v w urep vrep wrep.
  apply (ComposeRepr_n 2 3 u (fun k => match k with
                                    | O => v
                                    | S i => w
                                    end) urep).
  intros k. 
  destruct k. exact vrep.
  destruct k. exact wrep. exact wrep.
Qed.

Lemma ComposeRepr_32 : forall u (v w t : nat -> nat -> nat),
    FunctionRepresented 3 u
    -> FunctionRepresented 2 v
    -> FunctionRepresented 2 w
    -> FunctionRepresented 2 t
    -> FunctionRepresented 2 (fun i j => u (v i j) (w i j) (t i j)).
Proof.
  intros u v w t urep vrep wrep trep.
  apply (ComposeRepr_n 3 2 u (fun k => match k with
                                    | O => v
                                    | 1 => w
                                    | _ => t
                                    end) urep).
  intros k. 
  destruct k. exact vrep.
  destruct k. exact wrep. exact trep.
Qed. 

Lemma ComposeRepr_33 : forall u v w t : nat -> nat -> nat -> nat,
    FunctionRepresented 3 u
    -> FunctionRepresented 3 v
    -> FunctionRepresented 3 w
    -> FunctionRepresented 3 t
    -> FunctionRepresented 3 (fun i j k => u (v i j k) (w i j k) (t i j k)).
Proof.
  intros u v w t urep vrep wrep trep.
  apply (ComposeRepr_n 3 3 u (fun k => match k with
                                    | O => v
                                    | 1 => w
                                    | _ => t
                                    end) urep).
  intros k. 
  destruct k. exact vrep.
  destruct k. exact wrep. exact trep.
Qed.

Lemma ComposeRepr_14 : forall (u:nat->nat) (v : nat -> nat -> nat -> nat -> nat),
    FunctionRepresented 1 u
    -> FunctionRepresented 4 v
    -> FunctionRepresented 4 (fun i j k l => u (v i j k l)).
Proof.
  intros u v urep vrep.
  apply (ComposeRepr_n 1 4 u (fun k => v) urep).
  intros _. exact vrep.
Qed. 

Lemma ComposeRepr_24 : forall (u : nat -> nat -> nat) v w,
    FunctionRepresented 2 u
    -> FunctionRepresented 4 v
    -> FunctionRepresented 4 w
    -> FunctionRepresented 4 (fun i j k l => u (v i j k l) (w i j k l)).
Proof.
  intros u v w urep vrep wrep.
  apply (ComposeRepr_n 2 4 u (fun k => match k with
                                    | O => v
                                    | S i => w
                                    end) urep).
  intros k. 
  destruct k. exact vrep.
  destruct k. exact wrep. exact wrep.
Qed. 

Lemma ComposeRepr_43 : forall u (v w t s : nat -> nat -> nat -> nat),
    FunctionRepresented 4 u
    -> FunctionRepresented 3 v
    -> FunctionRepresented 3 w
    -> FunctionRepresented 3 t
    -> FunctionRepresented 3 s
    -> FunctionRepresented 3 (fun i j k => u (v i j k) (w i j k) (t i j k) (s i j k)).
Proof.
  intros u v w t s urep vrep wrep trep srep.
  apply (ComposeRepr_n 4 3 u (fun k => match k with
                                    | O => v
                                    | 1 => w
                                    | 2 => t
                                    | _ => s
                                    end) urep).
  intros k. 
  destruct k. exact vrep.
  destruct k. exact wrep.
  destruct k. exact trep. exact srep.
Qed. 

Lemma ComposeRepr_15 : forall (u:nat->nat) (v : nat -> nat -> nat -> nat -> nat -> nat),
    FunctionRepresented 1 u
    -> FunctionRepresented 5 v
    -> FunctionRepresented 5 (fun i j k l m => u (v i j k l m)).
Proof.
  intros u v urep vrep.
  apply (ComposeRepr_n 1 5 u (fun k => v) urep).
  intros _. exact vrep.
Qed. 

Lemma ComposeRepr_25 : forall (u : nat -> nat -> nat) v w,
    FunctionRepresented 2 u
    -> FunctionRepresented 5 v
    -> FunctionRepresented 5 w
    -> FunctionRepresented 5 (fun i j k l m => u (v i j k l m) (w i j k l m)).
Proof.
  intros u v w urep vrep wrep.
  apply (ComposeRepr_n 2 5 u (fun k => match k with
                                    | O => v
                                    | S i => w
                                    end) urep).
  intros k. 
  destruct k. exact vrep. exact wrep.
Qed. 

Lemma ComposeRepr_35 : forall (u : nat -> nat -> nat -> nat) v w t,
    FunctionRepresented 3 u
    -> FunctionRepresented 5 v
    -> FunctionRepresented 5 w
    -> FunctionRepresented 5 t
    -> FunctionRepresented 5 (fun i j k l m => u (v i j k l m) (w i j k l m) (t i j k l m)).
Proof.
  intros u v w t urep vrep wrep trep.
  apply (ComposeRepr_n 3 5 u (fun k => match k with
                                    | O => v
                                    | 1 => w
                                    | _ => t
                                    end) urep).
  intros k. 
  destruct k. exact vrep.
  destruct k. exact wrep.
  exact trep.
Qed. 

Lemma ComposeRepr_54 : forall u (v w t s q : nat -> nat -> nat -> nat -> nat),
    FunctionRepresented 5 u
    -> FunctionRepresented 4 v
    -> FunctionRepresented 4 w
    -> FunctionRepresented 4 t
    -> FunctionRepresented 4 s
    -> FunctionRepresented 4 q
    -> FunctionRepresented 4 (fun i j k l => u (v i j k l) (w i j k l) (t i j k l) (s i j k l) (q i j k l)).
Proof.
  intros u v w t s q urep vrep wrep trep srep qrep.
  apply (ComposeRepr_n 5 4 u (fun k => match k with
                                    | O => v
                                    | 1 => w
                                    | 2 => t
                                    | 3 => s
                                    | _ => q
                                    end) urep).
  intros k. 
  destruct k. exact vrep.
  destruct k. exact wrep.
  destruct k. exact trep.
  destruct k. exact srep.
  exact qrep.
Qed. 


Lemma FunctionRepresented_ext : forall arity (u v : nfun nat arity nat),
    FunctionRepresented arity u
    -> (forall x, nuncurry _ _ _ u x = nuncurry _ _ _ v x)
    -> FunctionRepresented arity v.
Proof.
  intros. apply (Build_FunctionRepresented arity _ H).
  - intro args. simpl.
    replace (nfun_eval arity args v) with (nfun_eval arity args u).
    exact (fr_rep _ _ H args).
    clear H.
    revert arity args u v H0. induction arity.
    intros. exact (H0 tt).
    intros. simpl.
    specialize (IHarity (TailNat args) (u (CoordNat args 0))
                        (v (CoordNat args 0))).
    apply IHarity. intro x.
    apply (H0 (pair (CoordNat args 0) x)).
  - apply fr_propprop.
  - apply fr_vars.
Qed.

Lemma FunctionRepresented_1_ext : forall (u v : nat -> nat),
    FunctionRepresented 1 u
    -> (forall n:nat, u n = v n)
    -> FunctionRepresented 1 v.
Proof.
  intros.
  apply (FunctionRepresented_ext 1 u v H).
  intros. simpl. destruct x. apply H0.
Qed.

Lemma FunctionRepresented_2_ext : forall (u v : nat -> nat -> nat),
    FunctionRepresented 2 u
    -> (forall n k:nat, u n k = v n k)
    -> FunctionRepresented 2 v.
Proof.
  intros.
  apply (FunctionRepresented_ext 2 u v H).
  intros. simpl. destruct x, n0. apply H0.
Qed.

Lemma FunctionRepresented_3_ext : forall (u v : nat -> nat -> nat -> nat),
    FunctionRepresented 3 u
    -> (forall i j k:nat, u i j k = v i j k)
    -> FunctionRepresented 3 v.
Proof.
  intros.
  apply (FunctionRepresented_ext 3 u v H).
  intros. simpl. destruct x, n0, n1. apply H0.
Qed.

Lemma FunctionRepresented_4_ext : forall (u v : nat -> nat -> nat -> nat -> nat),
    FunctionRepresented 4 u
    -> (forall i j k l:nat, u i j k l = v i j k l)
    -> FunctionRepresented 4 v.
Proof.
  intros.
  apply (FunctionRepresented_ext 4 u v H).
  intros. simpl. destruct x, n0, n1, n2. apply H0.
Qed.

Lemma FunctionRepresented_5_ext : forall (u v : nat -> nat -> nat -> nat -> nat -> nat),
    FunctionRepresented 5 u
    -> (forall i j k l m:nat, u i j k l m = v i j k l m)
    -> FunctionRepresented 5 v.
Proof.
  intros.
  apply (FunctionRepresented_ext 5 u v H).
  intros. simpl. destruct x, n0, n1, n2, n3. apply H0.
Qed.

Fixpoint proj_func (i j : nat) : nfun nat i nat.
Proof.
  destruct i.
  - exact O.
  - destruct j.
    + exact (fun x => ncurry nat nat i (fun _ => x)).
    + exact (fun x => proj_func i j).
Defined.

Lemma nfun_eval_proj : forall i j args,
    j < i ->
    nfun_eval i args (proj_func i j) = CoordNat args j.
Proof.
  induction i.
  - intros. exfalso. inversion H.
  - intros. simpl. destruct j.
    apply nfun_eval_curry.
    rewrite IHi. apply CoordTailNat.
    apply le_S_n, H.
Qed.

(* Avoid infinite loop in type checker *)
Lemma PAnat_subst_multi_succ : forall i args A,
    PAnat_subst_multi (S i) 0 args A
    = PAnat_subst_multi i 0 args (Subst (PAnat (CoordNat args i)) i A).
Proof.
  reflexivity.
Qed.
Opaque PAnat_subst_multi.

Lemma PAnat_subst_multi_eq_const : forall i j k args,
    i <= k ->
    PAnat_subst_multi i 0 args (Leq (Lvar k) (PAnat j))
    = Leq (Lvar k) (PAnat j).
Proof.
  induction i. reflexivity.
  intros. rewrite PAnat_subst_multi_succ.
  rewrite Subst_eq, SubstTerm_var, SubstTerm_PAnat.
  replace (k =? i) with false.
  apply IHi. apply (Nat.le_trans _ (S i)).
  apply le_S, Nat.le_refl. exact H.
  symmetry.
  apply Nat.eqb_neq. intro abs.
  rewrite abs in H.
  exact (Nat.lt_irrefl i H).
Qed.

Lemma PAnat_subst_multi_eq : forall i j k args,
    j < i ->
    i <= k -> 
    PAnat_subst_multi i 0 args (Leq (Lvar k) (Lvar j))
    = Leq (Lvar k) (PAnat (CoordNat args j)).
Proof.
  induction i.
  - intros. exfalso. inversion H.
  - intros. rewrite PAnat_subst_multi_succ.
    rewrite Subst_eq, SubstTerm_var.
    replace (k =? i) with false.
    rewrite SubstTerm_var.
    apply Nat.le_succ_r in H. destruct H.
    + replace (j =? i) with false.
      apply IHi. exact H.
      apply (Nat.le_trans _ (S i)).
      apply le_S, Nat.le_refl. exact H0.
      symmetry. apply Nat.eqb_neq. intro abs.
      subst j. exact (Nat.lt_irrefl i H).
    + inversion H. subst j. rewrite Nat.eqb_refl.
      apply PAnat_subst_multi_eq_const.
      apply (Nat.le_trans _ (S i)).
      apply le_S, Nat.le_refl. exact H0.
    + symmetry. apply Nat.eqb_neq. intro abs.
      subst k. exact (Nat.lt_irrefl i H0).
Qed.

Lemma proj_represented : forall i j,
    j < i -> FunctionRepresented i (proj_func i j).
Proof.
  intros i j jlti.
  apply (Build_FunctionRepresented i _ (Leq (Lvar i) (Lvar j))).
  - intro args. rewrite nfun_eval_proj. 2: exact jlti.
    apply LforallIntro. rewrite PAnat_subst_multi_eq. 2: exact jlti.
    apply LequivRefl.
    rewrite IsLproposition_eq, IsLterm_var.
    apply IsLterm_PAnat. apply Nat.le_refl.
  - rewrite IsLproposition_eq, IsLterm_var.
    apply IsLterm_var.
  - intros. unfold Leq.
    rewrite VarOccursFreeInFormula_rel2.
    rewrite VarOccursInTerm_var, VarOccursInTerm_var.
    replace (v =? i) with false. simpl.
    apply Nat.eqb_neq. intro abs. subst v.
    apply (Nat.lt_irrefl i).
    apply (Nat.lt_trans _ _ _ H jlti). symmetry.
    apply Nat.eqb_neq. intro abs. subst v.
    exact (Nat.lt_irrefl i H).
Qed.

Lemma ConstantRepresented : forall (u k : nat),
    FunctionRepresented k (ncurry nat nat k (fun _ => u)).
Proof.
  intros u k.
  apply (Build_FunctionRepresented k _ (Leq (Lvar k) (PAnat u))).
  intro args. apply LforallIntro.
  rewrite nfun_eval_curry.
  rewrite PAnat_subst_multi_eq_const.
  apply LequivRefl.
  rewrite IsLproposition_eq, IsLterm_var.
  apply IsLterm_PAnat. apply Nat.le_refl.
  rewrite IsLproposition_eq, IsLterm_var.
  apply IsLterm_PAnat.
  intros v H. unfold Leq.
  rewrite VarOccursFreeInFormula_rel2, VarOccursInTerm_var.
  rewrite PAnat_closed, Bool.orb_false_r.
  apply Nat.eqb_neq. intro abs.
  subst v. exact (Nat.lt_irrefl k H).
Qed.
    
Global Opaque ComposeRepr.
