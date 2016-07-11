Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import List.

Require Export Syntax.

Reserved Notation " P '/' cfg '==>' cfg' " (at level 40).

Inductive step (P : program) : configuration -> configuration -> Prop :=
(***************)
(* Parallelism *)
(***************)
  | EvalAsyncLeft :
      forall H H' V V' n n' T1 T1' T2 e,
        P / (H, V, n, T1) ==>
          (H', V', n', T1') ->
        P / (H, V, n, T_Async T1 T2 e) ==>
          (H', V', n', T_Async T1' T2 e)
  | EvalAsyncRight :
      forall H H' V V' n n' T1 T2 T2' e,
        P / (H, V, n, T2) ==>
          (H', V', n', T2') ->
        P / (H, V, n, T_Async T1 T2 e) ==>
          (H', V', n', T_Async T1 T2' e)
  | EvalAsyncJoin :
      forall H V n e1 T2 Ls e,
        threads_done(T_Thread Ls e1) ->
        threads_done(T2) ->
        P / (H, V, n, T_Async (T_Thread Ls e1) T2 e) ==>
          (H, V, n, T_Thread Ls e)
  | EvalSpawn :
      forall H V n e1 e2 e3 Ls,
        P / (H, V, n, T_Thread Ls (EPar e1 e2 e3)) ==>
          (H, V, n, T_Async (T_Thread Ls e1) (T_Thread nil e2) e3)
  | EvalSpawnContext :
      forall H V n ctx e e1 e2 e3 Ls,
        is_econtext ctx ->
        P / (H, V, n, T_Thread Ls e) ==>
          (H, V, n, T_Async (T_Thread Ls e1) (T_Thread nil e2) e3) ->
        P / (H, V, n, T_Thread Ls (ctx e)) ==>
          (H, V, n, T_Async (T_Thread Ls e1) (T_Thread nil e2) (ctx e3))
(*****************)
(* Single thread *)
(*****************)
  | EvalContext :
      forall H H' V V' n n' ctx e e' Ls Ls',
        is_econtext ctx ->
        P / (H, V, n, T_Thread Ls e) ==>
          (H', V', n', T_Thread Ls' e') ->
        P / (H, V, n, T_Thread Ls (ctx e)) ==>
          (H', V', n', T_Thread Ls' (ctx e'))
  | EvalVar :
      forall H V n x v Ls,
        V x = Some v ->
        P / (H, V, n, T_Thread Ls (EVar (DV x))) ==>
          (H, V, n, T_Thread Ls (EVal v))
  | EvalConsume :
      forall H V n x v Ls,
        V x = Some v ->
        P / (H, V, n, T_Thread Ls (EConsume (DV x))) ==>
          (H, extend V x VNull, n, T_Thread Ls (EVal v))
  | EvalCast :
      forall H V n v t Ls,
        P / (H, V, n, T_Thread Ls (ECast t (EVal v))) ==>
          (H, V, n, T_Thread Ls (EVal v))
  | EvalNew :
      forall H V n c i fs RL ms Ls,
        classLookup P c = (Some (Cls c i fs ms)) ->
        declsToRegionLocks fs RL ->
        P / (H, V, n, T_Thread Ls (ENew c)) ==>
          (heapExtend H (c, declsToFields fs, RL),
           V, n, T_Thread Ls (EVal (VLoc (length H))))
  | EvalCall :
      forall H V n x l m v c mtds y body t t' Ls,
        V x = Some (VLoc l) ->
        (exists F RL, heapLookup H l = Some (c, F, RL)) ->
        methods P (TClass c) = Some mtds ->
        methodLookup mtds m = Some (Method m (y, t) t' body) ->
        P / (H, V, n, T_Thread Ls (ECall (DV x) m (EVal v))) ==>
          (H, extend (extend V (dthis, n) (VLoc l)) (DVar n, n) v, S n,
           T_Thread Ls (subst y (DVar n, n) (subst this (dthis, n) (sigma n body))))
  | EvalSelect :
      forall H V n x l f c F RL v Ls,
        V x = Some (VLoc l) ->
        heapLookup H l = Some (c, F, RL) ->
        F f = Some v ->
        P / (H, V, n, T_Thread Ls (ESelect (DV x) f)) ==>
          (H, V, n, T_Thread Ls (EVal v))
  | EvalConsumeField :
      forall H V n x l f c F RL v Ls,
        V x = Some (VLoc l) ->
        heapLookup H l = Some (c, F, RL) ->
        F f = Some v ->
        P / (H, V, n, T_Thread Ls (EConsumeField (DV x) f)) ==>
          (heapUpdate H l (c, extend F f VNull, RL), V, n, T_Thread Ls (EVal v))
  | EvalUpdate :
      forall H V n x l f v c F RL Ls,
        V x = Some (VLoc l) ->
        heapLookup H l = Some (c, F, RL) ->
        P / (H, V, n, T_Thread Ls (EUpdate (DV x) f (EVal v))) ==>
          (heapUpdate H l (c, extend F f v, RL), V, n, T_Thread Ls (EVal VNull))
  | EvalLet :
      forall H V n frame x v body Ls,
        P / (H, V, n, T_Thread Ls (ELet x frame (EVal v) body)) ==>
          (H, extend V (DVar n, frame) v, S n, T_Thread Ls ((subst x (DVar n, frame) body)))
  | EvalAssert :
      forall H V n x y l e Ls,
        V x = Some (VLoc l) ->
        V y = Some (VLoc l) ->
        P / (H, V, n, T_Thread Ls (EAssert (DV x) (DV y) e)) ==>
          (H, V, n, T_Thread Ls e)
(***********)
(* Locking *)
(***********)
  | EvalWlock :
      forall H V n x r l e c F RL Ls,
        V x = Some (VLoc l) ->
        heapLookup H l = Some (c, F, RL) ->
        RL r = Some (LReaders 0) ->
        ~ In (l, r) Ls ->
        P / (H, V, n, T_Thread Ls (EWlock (DV x) r e)) ==>
          (heapUpdate H l (c, F, extend RL r LLocked), V, n, T_Thread ((l, r) :: Ls) (EWlocked (l, r) e))
  | EvalWlock_Reentrant :
      forall H V n x r l e c F RL Ls,
        V x = Some (VLoc l) ->
        heapLookup H l = Some (c, F, RL) ->
        RL r = Some LLocked ->
        In (l, r) Ls ->
        P / (H, V, n, T_Thread Ls (EWlock (DV x) r e)) ==>
          (H, V, n, T_Thread Ls e)
  | EvalWlock_Release :
      forall H V n r l v c F RL Ls,
        heapLookup H l = Some (c, F, RL) ->
        RL r = Some LLocked ->
        In (l, r) Ls ->
        P / (H, V, n, T_Thread Ls (EWlocked (l, r) (EVal v))) ==>
          (heapUpdate H l (c, F, extend RL r (LReaders 0)), V, n, T_Thread (remove id_eq_dec (l, r) Ls) (EVal v))
  | EvalRlock :
      forall H V n x r l m e c F RL Ls,
        V x = Some (VLoc l) ->
        heapLookup H l = Some (c, F, RL) ->
        RL r = Some (LReaders m) ->
        P / (H, V, n, T_Thread Ls (ERlock (DV x) r e)) ==>
          (heapUpdate H l (c, F, extend RL r (LReaders (S m))), V, n, T_Thread Ls (ERlocked (l, r) e))
  | EvalRlock_Reentrant :
      forall H V n x r l e c F RL Ls,
        V x = Some (VLoc l) ->
        heapLookup H l = Some (c, F, RL) ->
        RL r = Some LLocked ->
        In (l, r) Ls ->
        P / (H, V, n, T_Thread Ls (ERlock (DV x) r e)) ==>
          (H, V, n, T_Thread Ls e)
  | EvalRlock_Release :
      forall H V n r l m v c F RL Ls,
        heapLookup H l = Some (c, F, RL) ->
        RL r = Some (LReaders m) ->
        P / (H, V, n, T_Thread Ls (ERlocked (l, r) (EVal v))) ==>
          (heapUpdate H l (c, F, extend RL r (LReaders (pred m))), V, n, T_Thread Ls (EVal v))
(**************)
(* Exceptions *)
(**************)
  | EvalEXN_AsyncLeft :
      forall H V n T1 T2 e,
        threads_exn(T1) ->
        P / (H, V, n, T_Async T1 T2 e) ==>
          (H, V, n, T_EXN (leftmost_locks T1))
  | EvalEXN_AsyncRight :
      forall H V n T1 T2 e,
        threads_exn(T2) ->
        P / (H, V, n, T_Async T1 T2 e) ==>
          (H, V, n, T_EXN (leftmost_locks T1))
  | EvalEXN_Context :
      forall ctx H V n e Ls,
        is_econtext ctx ->
        P / (H, V, n, T_Thread Ls e) ==> 
           (H, V, n, T_EXN Ls) ->
        P / (H, V, n, T_Thread Ls (ctx e)) ==>
          (H, V, n, T_EXN Ls)
  | EvalEXN_Call :
      forall H V n x m v Ls,
        V x = Some VNull ->
        P / (H, V, n, T_Thread Ls (ECall (DV x) m (EVal v))) ==>
          (H, V, n, T_EXN Ls)
  | EvalEXN_Select :
      forall H V n x f Ls,
        V x = Some VNull ->
        P / (H, V, n, T_Thread Ls (ESelect (DV x) f)) ==>
          (H, V, n, T_EXN Ls)
  | EvalEXN_ConsumeField :
      forall H V n x f Ls,
        V x = Some VNull ->
        P / (H, V, n, T_Thread Ls (EConsumeField (DV x) f)) ==>
          (H, V, n, T_EXN Ls)
  | EvalEXN_Update :
      forall H V n x f v Ls,
        V x = Some VNull ->
        P / (H, V, n, T_Thread Ls (EUpdate (DV x) f (EVal v))) ==>
          (H, V, n, T_EXN Ls)
  | EvalEXN_WLock :
      forall H V n x r e Ls,
        V x = Some VNull ->
        P / (H, V, n, T_Thread Ls (EWlock (DV x) r e)) ==>
          (H, V, n, T_EXN Ls)
  | EvalEXN_RLock :
      forall H V n x r e Ls,
        V x = Some VNull ->
        P / (H, V, n, T_Thread Ls (ERlock (DV x) r e)) ==>
          (H, V, n, T_EXN Ls)
  | EvarEXN_AssertL :
      forall H V n x y e Ls,
        V x = Some VNull ->
        P / (H, V, n, T_Thread Ls (EAssert (DV x) (DV y) e)) ==>
          (H, V, n, T_EXN Ls)
  | EvarEXN_AssertR :
      forall H V n x y e Ls,
        V y = Some VNull ->
        P / (H, V, n, T_Thread Ls (EAssert (DV x) (DV y) e)) ==>
          (H, V, n, T_EXN Ls)
  | EvarEXN_Assert :
      forall H V n x y l1 l2 e Ls,
        V x = Some (VLoc l1) ->
        V y = Some (VLoc l2) ->
        l1 <> l2 ->
        P / (H, V, n, T_Thread Ls (EAssert (DV x) (DV y) e)) ==>
          (H, V, n, T_EXN Ls)
      
  where " P '/' cfg '==>' cfg' " := (step P cfg cfg').

Hint Constructors step.

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "EvalAsyncLeft" 
  | Case_aux c "EvalAsyncRight" 
  | Case_aux c "EvalAsyncJoin" 
  | Case_aux c "EvalSpawn" 
  | Case_aux c "EvalSpawnContext" 

  | Case_aux c "EvalContext" 
  | Case_aux c "EvalVar" 
  | Case_aux c "EvalConsume" 
  | Case_aux c "EvalNew" 
  | Case_aux c "EvalCall" 
  | Case_aux c "EvalSelect"
  | Case_aux c "EvalConsumeField"
  | Case_aux c "EvalUpdate" 
  | Case_aux c "EvalLet" 
  | Case_aux c "EvalAssert" 

  | Case_aux c "EvalWlock"
  | Case_aux c "EvalWlock_Reentrant"
  | Case_aux c "EvalWlock_Release"
  | Case_aux c "EvalRlock"
  | Case_aux c "EvalRlock_Reentrant"
  | Case_aux c "EvalRlock_Release"

  | Case_aux c "EvalEXN_AsyncLeft"
  | Case_aux c "EvalEXN_AsyncRight"
  | Case_aux c "EvalEXN_Context"
  | Case_aux c "EvalEXN_Call"
  | Case_aux c "EvalEXN_Select"
  | Case_aux c "EvalEXN_Update"
  | Case_aux c "EvalEXN_Assert"
  ].

Definition multistep (P : program) := clos_refl_trans_1n configuration (step P).
Notation " P '/' cfg '==>*' cfg' " := (multistep P cfg cfg') (at level 40).

Inductive cfg_blocked : configuration -> Prop :=
  | Blocked_Deadlock :
      forall H V n T1 T2 e,
        cfg_blocked (H, V, n, T1) ->
        cfg_blocked (H, V, n, T2) ->
        cfg_blocked (H, V, n, T_Async T1 T2 e)
  | Blocked_Left :
      forall H V n T1 T2 e,
        cfg_blocked (H, V, n, T1) ->
        threads_done T2 ->
        cfg_blocked (H, V, n, T_Async T1 T2 e)
  | Blocked_Right :
      forall H V n T1 T2 e,
        threads_done T1 ->
        cfg_blocked (H, V, n, T2) ->
        cfg_blocked (H, V, n, T_Async T1 T2 e)
  | Blocked_WW :
      forall H V n x r e l c F RL Ls,
        V x = Some (VLoc l) ->
        heapLookup H l = Some (c, F, RL) ->
        RL r = Some LLocked ->
        ~ In (l, r) Ls ->
        cfg_blocked (H, V, n, T_Thread Ls (EWlock (DV x) r e))
  | Blocked_WR :
      forall H V n x r e l c F RL m Ls,
        V x = Some (VLoc l) ->
        heapLookup H l = Some (c, F, RL) ->
        RL r = Some (LReaders m) ->
        m > 0 ->
        cfg_blocked (H, V, n, T_Thread Ls (EWlock (DV x) r e))
  | Blocked_RW :
      forall H V n x r e l c F RL Ls,
        V x = Some (VLoc l) ->
        heapLookup H l = Some (c, F, RL) ->
        RL r = Some LLocked ->
        ~ In (l, r) Ls ->
        cfg_blocked (H, V, n, T_Thread Ls (ERlock (DV x) r e))
  | Blocked_Context :
      forall H V n ctx e Ls,
        is_econtext ctx -> 
        cfg_blocked (H, V, n, T_Thread Ls e) ->
        cfg_blocked (H, V, n, T_Thread Ls (ctx e)).

  


