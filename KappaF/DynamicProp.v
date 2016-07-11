Require Import SyntaxProp.
Require Export Dynamic.
Require Import Shared.

(*
=====
step
=====
*)

(*
Lemma step_done : 
  forall P cfg,
    cfg_done cfg ->
    ~ exists cfg', P / cfg ==> cfg'.
Proof with auto.
  intros P [[[H V] n] T] cfgDone.
  simpls. 
  destruct T... 
  simpls. 
  destruct e...
  intros contra. destruct contra as [cfg' Hstep].
  inv Hstep; 
    match goal with 
        Hctx : is_econtext _ |- _ => 
        inv Hctx 
    end; congruence.
Qed.

Lemma step_irreflexive :
  forall P cfg,
    ~ P / cfg ==> cfg.
Proof with auto.
  intros P [[[H V] n] T].
  induction T; try(contra)...
  induction e; intros contra; 
  inversion contra; try(omega); subst; 
  match goal with
    | [Hctx : is_econtext _ |- _ ] => inv Hctx
  end; congruence.
Qed.
*)

Lemma step_n_monotonic :
  forall P H H' V V' n n' T T',
    P / (H, V, n, T) ==> (H', V', n', T') ->
    n <= n'.
Proof with eauto.
  introv Hstep.
  gen T'.
  induction T as [| |]; intros; inv Hstep...
  gen e'. 
  induction e0; introv Hstep;
  inv Hstep; try(malformed_context);
  try(inv_eq)...
Qed.

