Require Coq.Setoids.Setoid.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.EqNat.

Require Import Shared.
Require Import Meta.

(*
=============
Partial maps
=============
*)

Ltac case_id_eq_dec :=
  match goal with
    | _ : _ |- context[id_eq_dec _ _] =>
      repeat(elim id_eq_dec); intros; subst; try(congruence)
  end.

Ltac case_extend :=
  match goal with 
    | _ : _ |- context[extend _ _ _ _] =>
      unfold extend; case_id_eq_dec 
  end.

Ltac case_drop :=
  match goal with 
    | _ : _ |- context[drop _ _ _] =>
      unfold drop; cases_if
  end.

Lemma extend_eq :
  forall A B (eqd : ID A) Gamma x y (v : B),
    x = y ->
    extend Gamma x v y = Some v.
Proof with case_extend.
  introv...
Qed.

Hint Resolve extend_eq.

Lemma extend_neq :
  forall A B (eqd : ID A) Gamma x y (v : B),
    x <> y ->
    extend Gamma x v y = Gamma y.
Proof with case_extend.
  introv...
Qed.

Hint Resolve extend_neq.

Lemma extend_order :
  forall A B (eqd : ID A) Gamma x y z (v1 v2 : B),
    x <> y ->
    extend (extend Gamma x v1) y v2 z =
    extend (extend Gamma y v2) x v1 z.
Proof with case_extend.
  introv...
Qed.

Hint Resolve extend_order.

Lemma extend_shadow :
  forall A B (eqd : ID A) Gamma x y (v1 v2 : B),
    extend (extend Gamma x v1) x v2 y=
    extend Gamma x v2 y.
Proof with case_extend.
  introv... 
Qed.  

Hint Resolve extend_shadow.

(*
====
IDs
====
*)

Lemma class_id_eq_refl : 
  forall c, 
    class_id_eq c c = true.
Proof with auto using beq_nat_refl. 
  destruct c. simpl... 
Qed.

Lemma interface_id_eq_refl : 
  forall i, 
    interface_id_eq i i = true.
Proof with auto using beq_nat_refl. 
  destruct i. simpl... 
Qed.

Lemma class_id_eq_eq : 
  forall c c', 
    class_id_eq c c' = true <->
    c = c'.
Proof with auto using beq_nat_true, class_id_eq_refl.
  intros [n] [n']. 
  split.
  + case n; case n'...
  + intros []... 
Qed.

Lemma class_id_neq_neq :
  forall c c',
    class_id_eq c c' = false <->
    c <> c'.
Proof with auto.
  intros [n] [n']. 
  split; simpl; intros.
  + destruct (id_eq_dec (Cid n) (Cid n'))... 
    inv_eq. rewrite <- beq_nat_refl in H; congruence.
  + destruct (eq_nat_dec n n').
    - subst. congruence. 
    - rewrite beq_nat_false_iff...
Qed.

Lemma interface_id_eq_eq : 
  forall i i', 
    interface_id_eq i i' = true <->
    i = i'.
Proof with auto using beq_nat_true, interface_id_eq_refl.
  intros [n] [n']. 
  split.
  + destruct n; destruct n'... 
  + intros []... 
Qed.

Lemma field_id_neq_neq :
  forall f f',
    field_id_eq f f' = false <->
    f <> f'.
Proof with auto.
  intros [n] [n']. 
  split; simpl; intros.
  + destruct (id_eq_dec (Fid n) (Fid n'))... 
    inv_eq. rewrite <- beq_nat_refl in H; congruence.
  + destruct (eq_nat_dec n n').
    - subst. congruence. 
    - rewrite beq_nat_false_iff...
Qed.

Lemma method_id_eq_refl : 
  forall m, 
    method_id_eq m m = true.
Proof with auto using beq_nat_refl. 
  intros [n]. simpl... 
Qed.

Lemma method_id_eq_eq : 
  forall m m', 
    method_id_eq m m' = true <->
    m = m'.
Proof with auto using beq_nat_true, method_id_eq_refl.
  intros [n] [n']. 
  split.
  + destruct n; destruct n'... 
  + intros []... 
Qed.

Lemma region_id_eq_refl :
  forall r,
    region_id_eq r r = true.
Proof with eauto.
  introv.
  destruct r. 
  simpl. rewrite <- beq_nat_refl...
Qed.

Lemma lock_eq_refl :
  forall L,
    lock_eq L L = true.
Proof with eauto.
  introv.
  destruct L. 
  simpl. rewrite <- beq_nat_refl. rewrite region_id_eq_refl...
Qed.

Lemma lock_eq_eq : 
  forall L L', 
    lock_eq L L' = true <->
    L = L'.
Proof with auto using lock_eq_refl, beq_nat_refl.
  intros [l [n]] [l' [n']]. 
  split; simpls.
  + introv Heq. apply Bool.andb_true_iff in Heq as [Heq Heq']. 
    symmetry in Heq. apply beq_nat_eq in Heq.
    symmetry in Heq'. apply beq_nat_eq in Heq'.
    subst...
  + introv Heq. inv Heq.
    apply Bool.andb_true_iff.
    split...
Qed.

