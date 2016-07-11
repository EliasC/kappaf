Require Export Syntax.
Require Import Types.

(*
--------
Program
--------
*)

Inductive wfMethodSig (P : program) : methodSig -> Prop :=
  WF_Msig : 
    forall m x t t',
      wfType P t ->
      wfType P t' ->
      wfMethodSig P (MethodSig m (x, t) t').

Inductive wfInterface (P : program) : interfaceDecl -> Prop :=
  | WF_Interface : 
      forall i msigs,
        Forall (wfMethodSig P) msigs ->
        wfInterface P (Interface i msigs)
  | WF_ExtInterface :
      forall i i1 i2 msigs1 msigs2,
        methodSigs P (TInterface i1) msigs1 ->
        methodSigs P (TInterface i2) msigs2 ->
        (forall m msig, methodSigLookup msigs1 m = Some msig -> methodSigLookup msigs2 m = None) ->
        (forall m msig, methodSigLookup msigs2 m = Some msig -> methodSigLookup msigs1 m = None) ->
        wfInterface P (ExtInterface i i1 i2).

Inductive wfFieldDecl (P : program) : fieldDecl -> Prop :=
  | WF_Field : 
      forall f t r,
        wfType P t ->
        wfFieldDecl P (Field f t r).

Inductive wfMethodDecl (P : program) (c : class_id) : methodDecl -> Prop :=
  | WF_Method : 
      forall m x t t' e,
      wfType P t ->
      (* This should be derivable, but this makes things simpler *)
      wfType P t' -> 
      x <> this ->
      (* This should be derivable! *)
      remove id_eq_dec x 
             (remove id_eq_dec this (freeVars e)) = nil ->
      exprStatic e ->
        (let Gamma := extend 
                        (extend empty 
                                (env_var (SV x)) t)
                        (env_var (SV this)) (TClass c) in
         P ; Gamma |- e \in t') ->
        wfMethodDecl P c (Method m (x, t) t' e).

Inductive wfClassDecl (P : program) : classDecl -> Prop :=
  | WF_Class : 
      forall c i fs ms msigs,
        methodSigs P (TInterface i) msigs ->
        extractSigs ms = msigs ->
        Forall (wfFieldDecl P) fs ->
        Forall (wfMethodDecl P c) ms ->
        wfClassDecl P (Cls c i fs ms).

Inductive wfProgram : program -> ty -> Prop :=
  | WF_Program :
      forall cds ids e t,
        Forall (wfClassDecl (cds, ids, e)) cds ->
        Forall (wfInterface (cds, ids, e)) ids ->
        (cds, ids, e); empty |- e \in t ->
        wfProgram (cds, ids, e) t.

(*
-------
Heap
-------
*)

Inductive wfFields (P : program) (Gamma : env) (c : class_id) (F : dyn_fields) : Prop :=
  WF_Fields : 
    forall fs,
      fields P (TClass c) = Some fs ->
      (forall f t r, fieldLookup fs f = Some (Field f t r) -> 
                   exists v, F f = Some v /\ P; Gamma |- EVal v \in t) ->
      wfFields P Gamma c F.      

Inductive wfRegionLocks (P : program) (c : class_id) (RL : region_locks) : Prop :=
  | WF_RegionLocks :
      forall fs,
        fields P (TClass c) = Some fs ->
        (forall f t r, fieldLookup fs f = Some (Field f t r) -> 
                       exists status, RL r = Some status) ->
        wfRegionLocks P c RL.

Inductive wfHeap (P : program) (Gamma : env) : heap -> Prop :=
  WF_Heap : 
    forall H,
      wfEnv P Gamma ->
      (forall l c, Gamma (env_loc l) = Some (TClass c) -> 
                   exists F RL, heapLookup H l = Some (c, F, RL) /\ 
                                wfFields P Gamma c F /\
                                wfRegionLocks P c RL) ->
      (forall l, heapLookup H l <> None -> exists c, Gamma (env_loc l) = Some (TClass c)) ->
      wfHeap P Gamma H.

(*
------
Vars
------
*)

Definition freshVars (n : nat) (V : dvar_map) := 
  (forall n' frame', n <= n' -> fresh V (DVar n', frame')) 
  /\
  (forall n' frame', n <= frame' -> fresh V (DVar n', frame')).

Inductive wfVars (P : program) (Gamma : env) (n : nat) (V : dvar_map) : Prop :=
  WF_Vars : 
      wfEnv P Gamma ->
      (forall x t, Gamma (env_var (DV x)) = Some t -> exists v, V x = Some v /\ P; Gamma |- (EVal v) \in t) ->
      (forall x, V x <> None -> Gamma (env_var (DV x)) <> None) ->
      freshVars n V ->
      wfVars P Gamma n V.

(*
------
Locks
------
*)

Inductive wfLock (H : heap) : lock -> Prop :=
  | WF_Lock :
      forall l r c F RL,
        heapLookup H l = Some (c, F, RL) ->
        RL r = Some LLocked ->
        wfLock H (l, r).      

Inductive wfHeldLocks (H : heap) (Ls : list lock) : Prop :=
  | WF_HeldLocks :
      Forall (wfLock H) Ls ->
      wfHeldLocks H Ls.

Inductive wfWLocks (Ls : list lock) (e : expr) : Prop :=
  | WF_WLocks :
      (forall l r, In (l, r) (wlocks e) -> In (l, r) Ls) ->
      NoDup (wlocks e) ->
      wfWLocks Ls e.

Inductive wfRLocks (H : heap) (T : threads) : Prop :=
  | WF_RLocks : 
      (forall l r,
         In (l, r) (t_rlocks T) ->
         (exists c F RL n, 
            heapLookup H l = Some (c, F, RL) /\
            RL r = Some (LReaders n) /\
            length (filter (lock_eq (l, r)) (t_rlocks T)) <= n)) ->
      wfRLocks H T.

Inductive disjointLocks (T1 T2 : threads) : Prop :=
  | DisjointLocks :
      (forall L, In L (heldLocks T1) -> ~ In L (heldLocks T2)) ->
      (forall L, In L (heldLocks T2) -> ~ In L (heldLocks T1)) ->
      disjointLocks T1 T2.

Inductive wfLocking (H : heap) : threads -> Prop :=
  | WF_Locking_Thread :
      forall Ls e, 
        wfHeldLocks H Ls ->
        NoDup Ls -> 
        wfWLocks Ls e ->
        wfRLocks H (T_Thread Ls e) ->
        wfLocking H (T_Thread Ls e)
  | WF_Locking_Async : 
      forall T1 T2 e,
        wfWLocks (leftmost_locks T1) e -> 
        (forall L, In L (wlocks e) -> ~In L (t_wlocks T1)) ->
        wfRLocks H (T_Async T1 T2 e) ->
        disjointLocks T1 T2 ->
        wfLocking H T1 ->
        wfLocking H T2 ->
        wfLocking H (T_Async T1 T2 e)
  | WF_Locking_EXN : 
      forall Ls,
        wfHeldLocks H Ls -> 
        wfLocking H (T_EXN Ls).

(*
--------
Threads
--------
*)

Inductive wfThreads (P : program) (Gamma : env) (frame : frame_id): threads -> ty -> Prop :=
  | WF_Thread : 
      forall Ls e t, 
        freeVars e = nil ->
        frameFresh frame e ->
        P; Gamma |- e \in t ->
        wfThreads P Gamma frame (T_Thread Ls e) t
  | WF_Async : 
      forall T1 T2 e t t1 t2,
        freeVars e = nil ->
        frameFresh frame e ->
        P; Gamma |- e \in t ->
        wfThreads P Gamma frame T1 t1 ->
        wfThreads P Gamma frame T2 t2 ->
        wfThreads P Gamma frame (T_Async T1 T2 e) t
  | WF_EXN : 
      forall t Ls,
        wfType P t ->
        wfEnv P Gamma ->
        wfThreads P Gamma frame (T_EXN Ls) t.

(*
--------------
Configuration
--------------
*)

Inductive wfConfiguration (P : program) (Gamma : env) : configuration -> ty -> Prop := 
  | WF_Cfg :
      forall H V n T t,
        0 < n ->
        wfHeap P Gamma H ->
        wfVars P Gamma n V ->
        wfThreads P Gamma n T t ->
        wfLocking H T -> 
        wfConfiguration P Gamma (H, V, n, T) t.
