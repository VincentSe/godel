Require Import PeanoNat.
Require Import Numbers.NaryFunctions.
Require Import HeytingRepresentation.
Require Import BetaRepr.

Definition FunctionRepresentedBool (arity : nat) (u : nfun nat arity bool) : Set :=
  FunctionRepresented arity (nfun_to_nfun _ _ _ (fun b:bool => if b then 1 else 0) _ u). 

Lemma nuncurry_ncurry : forall B arity (f : nprod nat arity -> B) x,
    nuncurry nat _ arity (ncurry nat _ arity f) x = f x.
Proof.
  induction arity.
  - intros. simpl. destruct x. reflexivity.
  - intros. simpl. destruct x. apply IHarity.
Qed.

Lemma nuncurry_nfun_to_nfun : forall A B arity (f : A -> B) (g : nfun nat arity A) x,
    nuncurry _ _ arity (nfun_to_nfun _ _ _ f arity g) x
    = f (nuncurry _ _ _ g x).
Proof.
  induction arity. reflexivity.
  intros. simpl. destruct x. apply IHarity.
Qed.

Lemma FunctionRepresentedBool_ext : forall arity (u v : nfun nat arity bool),
    FunctionRepresentedBool arity u
    -> (forall x, nuncurry _ _ _ u x = nuncurry _ _ _ v x)
    -> FunctionRepresentedBool arity v.
Proof.
  intros.
  apply (FunctionRepresented_ext arity (nfun_to_nfun nat bool nat (fun b : bool => if b then 1 else 0) arity u) _ H).
  intro x. 
  rewrite nuncurry_nfun_to_nfun, nuncurry_nfun_to_nfun.
  rewrite H0. reflexivity.
Qed. 

Lemma NegRepresented : forall arity (u : nfun nat arity bool),
    FunctionRepresentedBool arity u ->
    FunctionRepresentedBool arity (nfun_to_nfun _ _ _ negb _ u).
Proof.
  intros.
  apply (FunctionRepresented_ext
           arity (@ncompose 1 arity (fun i => 1 - i)%nat (fun _ => nfun_to_nfun _ _ _ (fun b:bool => if b then 1 else 0) _ u))).
  apply ComposeRepr_n.
  apply ComposeRepr_21.
  exact SubtractionRepresented.
  apply (ConstantRepresented 1).
  apply (proj_represented 1 0). apply Nat.le_refl.
  intros _. exact H. 
  intro x. unfold ncompose.
  rewrite nuncurry_ncurry, nuncurry_ncurry.
  rewrite nuncurry_nfun_to_nfun, nuncurry_nfun_to_nfun.
  rewrite nuncurry_nfun_to_nfun.
  destruct (nuncurry nat bool arity u x); reflexivity.
Qed.

Lemma AndRepresented : forall arity (u v : nfun nat arity bool),
    FunctionRepresentedBool arity u ->
    FunctionRepresentedBool arity v ->
    FunctionRepresentedBool arity (ncurry nat _ arity (fun x => nuncurry _ _ _ u x
                                                           && nuncurry _ _ _ v x)%bool).
Proof.
  intros.
  pose (nfun_to_nfun _ _ _ (fun b:bool => if b then 1 else 0) _ u)%nat as charu.
  pose (nfun_to_nfun _ _ _ (fun b:bool => if b then 1 else 0) _ v)%nat as charv.
  apply (FunctionRepresented_ext
           arity (@ncompose 2 arity Nat.mul (fun k => match k with
                                                   | O => charu
                                                   | S i => charv end))).
  apply ComposeRepr_n.
  exact MultiplicationRepresented.
  intros [|k]. exact H. exact H0.
  intros x. simpl.
  rewrite nuncurry_ncurry, nuncurry_ncurry.
  rewrite nuncurry_ncurry, nuncurry_nfun_to_nfun.
  rewrite nuncurry_ncurry.
  unfold charu, charv.
  rewrite nuncurry_nfun_to_nfun, nuncurry_nfun_to_nfun.
  destruct (nuncurry nat bool arity u x), (nuncurry nat bool arity v x); reflexivity.
Qed. 

Lemma IfRepresented : forall arity (u : nfun nat arity bool) (v w : nfun nat arity nat),
    FunctionRepresentedBool arity u ->
    FunctionRepresented arity v ->
    FunctionRepresented arity w ->
    FunctionRepresented
      arity (ncurry nat nat arity (fun x => if nuncurry _ _ _ u x
                                     then nuncurry _ _ _ v x
                                     else nuncurry _ _ _ w x)).
Proof.
  intros.
  pose (nfun_to_nfun _ _ _ (fun b:bool => if b then 1 else 0) _ u)%nat as charu.
  pose (nfun_to_nfun _ _ _ (fun b:bool => if b then 1 else 0) _
                     (nfun_to_nfun _ _ _ negb _ u))%nat as ncharu.
  pose (@ncompose 2 arity Nat.mul (fun k => match k with
                                         | O => charu
                                         | S i => v end)) as vpart.
  pose (@ncompose 2 arity Nat.mul (fun k => match k with
                                         | O => ncharu
                                         | S i => w end)) as wpart.
  apply (FunctionRepresented_ext
           arity (@ncompose 2 arity Nat.add (fun k => match k with
                                                   | O => vpart
                                                   | S i => wpart end))).
  apply ComposeRepr_n.
  apply AdditionRepresented.
  intros [|k]. 
  - (* vpart represented *)
    apply ComposeRepr_n.
    apply MultiplicationRepresented.
    intros [|i]. exact H. exact H0.
  - (* wpart represented *)
    apply ComposeRepr_n.
    apply MultiplicationRepresented.
    intros [|i].
    apply NegRepresented, H.
    exact H1.
  - intro x. rewrite nuncurry_ncurry.
    unfold ncompose;
    rewrite nuncurry_ncurry, nuncurry_ncurry, nuncurry_ncurry.
    unfold vpart, wpart.
    unfold ncompose;
    rewrite nuncurry_ncurry, nuncurry_ncurry, nuncurry_ncurry, nuncurry_ncurry.
    rewrite nuncurry_ncurry, nuncurry_ncurry.
    unfold charu.
    rewrite nuncurry_nfun_to_nfun.
    unfold ncharu.
    rewrite nuncurry_nfun_to_nfun.
    rewrite nuncurry_nfun_to_nfun.
    destruct (nuncurry nat bool arity u x). simpl.
    rewrite Nat.add_0_r, Nat.add_0_r. reflexivity. simpl.
    rewrite Nat.add_0_r. reflexivity.
Qed. 

Lemma IfRepresentedBool : forall arity (u : nfun nat arity bool) (v w : nfun nat arity bool),
    FunctionRepresentedBool arity u ->
    FunctionRepresentedBool arity v ->
    FunctionRepresentedBool arity w ->
    FunctionRepresentedBool
      arity (ncurry _ _ arity (fun x => if nuncurry _ _ _ u x
                                     then nuncurry _ _ _ v x
                                     else nuncurry _ _ _ w x)).
Proof.
  intros.
  unfold FunctionRepresentedBool.
  apply (FunctionRepresented_ext arity 
       (ncurry _ _ arity
          (fun x : nat ^ arity =>
           if nuncurry nat bool arity u x
           then (nuncurry nat _ arity (nfun_to_nfun nat bool nat (fun b : bool => if b then 1 else 0) arity v) x)
           else (nuncurry nat _ arity (nfun_to_nfun nat bool nat (fun b : bool => if b then 1 else 0) arity w) x)))).
  apply (IfRepresented arity u _ _ H H0 H1).
  intros.
  rewrite nuncurry_ncurry.
  rewrite nuncurry_nfun_to_nfun.
  rewrite nuncurry_nfun_to_nfun.
  rewrite nuncurry_nfun_to_nfun.
  rewrite nuncurry_ncurry.
  destruct (nuncurry nat bool arity u x); reflexivity.
Qed. 

Lemma OddRepresented : forall arity (f : nfun nat arity nat),
    FunctionRepresented arity f ->
    FunctionRepresentedBool arity (nfun_to_nfun _ _ _ Nat.odd _ f).
Proof.
  intros arity f H.
  apply (FunctionRepresented_ext
           arity (@ncompose 1 arity (fun i : nat => Nat.modulo i 2) (fun _ => f))).
  apply ComposeRepr_n.
  apply ComposeRepr_21.
  apply mod_repr.
  apply (proj_represented 1 0). apply Nat.le_refl.
  apply (ConstantRepresented 2).
  intro n. exact H.
  intro n. unfold ncompose.
  rewrite nuncurry_ncurry, nuncurry_ncurry.
  rewrite nuncurry_nfun_to_nfun.
  rewrite nuncurry_nfun_to_nfun.
  generalize (nuncurry _ _ _ f n) as p. induction p.
  reflexivity. 
  rewrite Nat.odd_succ, <- Nat.negb_odd.
  destruct (Nat.odd p) eqn:des.
  change (S p) with (1 + p).
  rewrite Nat.add_mod.
  rewrite IHp. reflexivity. discriminate.
  change (S p) with (1 + p).
  rewrite Nat.add_mod.
  rewrite IHp. reflexivity. discriminate.
Qed.

Lemma EvenRepresented : forall arity (f : nfun nat arity nat),
    FunctionRepresented arity f ->
    FunctionRepresentedBool arity (nfun_to_nfun _ _ _ Nat.even _ f).
Proof.
  intros.
  apply (FunctionRepresentedBool_ext
           arity
           (nfun_to_nfun _ _ _ negb _ (nfun_to_nfun nat nat bool Nat.odd arity f))).
  apply NegRepresented.
  apply OddRepresented, H.
  intro n. simpl.
  rewrite nuncurry_nfun_to_nfun.
  rewrite nuncurry_nfun_to_nfun.
  rewrite nuncurry_nfun_to_nfun.
  rewrite <- Nat.negb_even, Bool.negb_involutive.
  reflexivity.
Qed.

Lemma IsZeroRepresented
  : FunctionRepresented 1 (fun n => match n with | O => 1 | S _ => O end).
Proof.
  apply (FunctionRepresented_1_ext
           (nat_rec (fun _ => nat) 1 (fun stepCount val => 0))).
  2: intros [|n]; reflexivity.
  pose proof ComposeRepr_21.
  apply (ComposeRepr_21 (fun i => nat_rec (fun _ : nat => nat) i (fun _ _ : nat => 0))).
  apply nat_rec_repr.
  apply (ConstantRepresented 0).
  apply (ConstantRepresented 1).
  apply (proj_represented 1 0). apply Nat.le_refl.
Qed. 

Lemma LebRepresented : forall arity (f g : nfun nat arity nat),
    FunctionRepresented arity f ->
    FunctionRepresented arity g ->
    FunctionRepresentedBool arity (ncurry nat _ arity (fun x => nuncurry _ _ _ f x
                                                           <=? nuncurry _ _ _ g x)%bool).
Proof.
  intros arity f g frep grep.
  apply (FunctionRepresented_ext
           arity
           (@ncompose 2 arity (fun i j => if i <=? j then 1 else 0)
                      (fun k => match k with
                             | O => f
                             | S _ => g end))).
  apply ComposeRepr_n.
  - change (FunctionRepresented 2 (fun a a0 : nat => if a <=? a0 then 1 else 0)).
    apply (FunctionRepresented_2_ext
             (fun i j => match i - j with | O => 1 | S _ => O end)). 
    apply (ComposeRepr_12 (fun n => match n with | O => 1 | S _ => O end)).
    exact IsZeroRepresented.
    exact SubtractionRepresented.
    intros n k.
    destruct (n <=? k) eqn:des.
    apply Nat.leb_le, Nat.sub_0_le in des.
    rewrite des. reflexivity.
    pose proof (Nat.sub_0_le n k).
    apply Nat.leb_nle in des.
    destruct (n-k). 2: reflexivity.
    exfalso. contradict des. apply H. reflexivity.
  - intros [|k]. exact frep. exact grep.
  - intros. simpl.
    rewrite nuncurry_ncurry, nuncurry_ncurry.
    rewrite nuncurry_ncurry, nuncurry_nfun_to_nfun.
    rewrite nuncurry_ncurry. reflexivity.
Qed.

Lemma LtbRepresented : forall arity (f g : nfun nat arity nat),
    FunctionRepresented arity f ->
    FunctionRepresented arity g ->
    FunctionRepresentedBool arity (ncurry nat _ arity (fun x => nuncurry _ _ _ f x
                                                           <? nuncurry _ _ _ g x)%bool).
Proof.
  intros arity f g frep grep.
  apply (FunctionRepresented_ext
           arity
           (@ncompose 2 arity (fun i j => if i <? j then 1 else 0)
                      (fun k => match k with
                             | O => f
                             | S _ => g end))).
  apply ComposeRepr_n.
  - change (FunctionRepresented 2 (fun a a0 : nat => if S a <=? a0 then 1 else 0)).
    apply (FunctionRepresented_2_ext
             (fun i j => match S i - j with | O => 1 | S _ => O end)).
    apply (ComposeRepr_12 (fun n => match n with | O => 1 | S _ => O end)).
    exact IsZeroRepresented.
    apply (ComposeRepr_22).
    exact SubtractionRepresented.
    apply ComposeRepr_12.
    exact SuccessorRepresented.
    apply (proj_represented 2 0). auto.
    apply (proj_represented 2 1). apply Nat.le_refl.
    intros n k.
    destruct (S n <=? k) eqn:des.
    apply Nat.leb_le, Nat.sub_0_le in des.
    rewrite des. reflexivity.
    pose proof (Nat.sub_0_le (S n) k).
    apply Nat.leb_nle in des.
    destruct (S n-k). 2: reflexivity.
    exfalso. contradict des. apply H. reflexivity.
  - intros [|k]. exact frep. exact grep.
  - intros. simpl.
    rewrite nuncurry_ncurry, nuncurry_ncurry.
    rewrite nuncurry_ncurry, nuncurry_nfun_to_nfun.
    rewrite nuncurry_ncurry. reflexivity.
Qed.

Lemma EqbRepresented : forall arity (f g : nfun nat arity nat),
    FunctionRepresented arity f ->
    FunctionRepresented arity g ->
    FunctionRepresentedBool
      arity (ncurry nat _ arity (fun x => (nuncurry _ _ _ f x =? nuncurry _ _ _ g x))).
Proof.
  intros.
  apply (FunctionRepresented_ext
           arity
           (@ncompose 2 arity (fun i j => if i =? j then 1 else 0)
                      (fun k => match k with
                             | O => f
                             | S _ => g end))).
  apply ComposeRepr_n.
  - apply (FunctionRepresentedBool_ext
             2 (fun i j => Nat.leb i j && Nat.leb j i)%bool).
    apply (AndRepresented 2 Nat.leb).
    apply (LebRepresented 2).
    apply (proj_represented 2 0). auto.
    apply (proj_represented 2 1). apply Nat.le_refl.
    unfold FunctionRepresentedBool.
    change (FunctionRepresented 2 (fun i j => if j <=? i then 1 else 0)).
    apply (FunctionRepresented_ext
             2 (@ncompose 2 2 (fun i j => if i <=? j then 1 else 0)
                          (fun k => match k with
                                 | O => (fun i j => j)
                                 | S _ => (fun i j => i) end))).
    apply ComposeRepr_n.
    apply (LebRepresented 2).
    apply (proj_represented 2 0). auto.
    apply (proj_represented 2 1). apply Nat.le_refl.
    intros [|k].
    apply (proj_represented 2 1). apply Nat.le_refl.
    apply (proj_represented 2 0). auto.
    reflexivity.
    intros. simpl. destruct x, n0.
    destruct (n <=? n0) eqn:des.
    apply Nat.leb_le in des.
    destruct (n0 <=? n) eqn:des2.
    apply Nat.leb_le in des2.
    rewrite (Nat.le_antisymm _ _ des des2), Nat.eqb_refl. reflexivity.
    apply Nat.leb_nle in des2.
    destruct (n =? n0) eqn:des3.
    exfalso. apply Nat.eqb_eq in des3.
    rewrite des3 in des2. contradict des2. apply Nat.le_refl.
    reflexivity. simpl.
    apply Nat.leb_nle in des.
    destruct (n =? n0) eqn:des3. 2: reflexivity.
    exfalso. apply Nat.eqb_eq in des3.
    rewrite des3 in des. contradict des. apply Nat.le_refl.
  - intros [|k]. exact H. exact H0.
  - intro x. simpl.
    rewrite nuncurry_ncurry, nuncurry_ncurry.
    rewrite nuncurry_ncurry, nuncurry_nfun_to_nfun, nuncurry_ncurry.
    reflexivity.
Qed.

Lemma OrRepresented : forall arity (u v : nfun nat arity bool),
    FunctionRepresentedBool arity u ->
    FunctionRepresentedBool arity v ->
    FunctionRepresentedBool arity (ncurry nat _ arity (fun x => nuncurry _ _ _ u x
                                                           || nuncurry _ _ _ v x)%bool).
Proof.
  intros.
  pose (nfun_to_nfun _ _ _ (fun b:bool => if b then 1 else 0) _ u)%nat as charu.
  pose (nfun_to_nfun _ _ _ (fun b:bool => if b then 1 else 0) _ v)%nat as charv.
  apply (FunctionRepresented_ext
           arity (@ncompose 2 arity
                            (fun i j => if i =? 1 then 1 else j)
                            (fun k => match k with
                                   | O => charu
                                   | S i => charv end))). 
  apply ComposeRepr_n.
  apply (IfRepresented 2 (fun i j => i =? 1)).
  apply (EqbRepresented 2).
  apply (proj_represented 2 0); auto.
  apply (ConstantRepresented 1).
  apply (ConstantRepresented 1).
  apply (proj_represented 2 1); auto.
  intros [|k]. exact H. exact H0.
  intros x. simpl.
  rewrite nuncurry_ncurry, nuncurry_ncurry.
  rewrite nuncurry_ncurry, nuncurry_nfun_to_nfun.
  rewrite nuncurry_ncurry.
  unfold charu, charv.
  rewrite nuncurry_nfun_to_nfun, nuncurry_nfun_to_nfun.
  destruct (nuncurry nat bool arity u x), (nuncurry nat bool arity v x); reflexivity.
Qed. 


  
