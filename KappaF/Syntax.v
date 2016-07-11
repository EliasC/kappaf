Require Import List.
Import ListNotations.

Require Export Meta.
Require Export Shared.

(*
======
Types
======
*)

Inductive ty : Type :=
  | TClass : class_id -> ty
  | TInterface : interface_id -> ty
  | TUnit : ty.

(*
============
Expressions
============
*)

Inductive val : Type :=
  | VNull : val
  | VLoc  : loc -> val.

Inductive var : Type :=
  | SV : svar -> var
  | DV : (dvar * frame_id) -> var.

Inductive expr : Type :=
  | EVal : val -> expr
  | EVar : var -> expr
  | EConsume : var -> expr
  | ENew : class_id -> expr
  | ECall : var -> method_id -> expr -> expr
  | ESelect : var -> field_id -> expr
  | EConsumeField : var -> field_id -> expr
  | EUpdate : var -> field_id -> expr -> expr
  | ELet : svar -> frame_id -> expr -> expr -> expr
  | ECast : ty -> expr -> expr
  | EPar : expr -> expr -> expr -> expr
  | EWlock : var -> region_id -> expr -> expr
  | ERlock : var -> region_id -> expr -> expr
  | EWlocked : lock -> expr -> expr
  | ERlocked : lock -> expr -> expr
  | EAssert : var -> var -> expr -> expr
.

Tactic Notation "expr_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "EVal"
  | Case_aux c "EVar"
  | Case_aux c "EConsume"
  | Case_aux c "ENew"
  | Case_aux c "ECall"  
  | Case_aux c "ESelect"
  | Case_aux c "EConsumeField"
  | Case_aux c "EUpdate"
  | Case_aux c "ELet"
  | Case_aux c "ECast"
  | Case_aux c "EPar"
  | Case_aux c "EWlock"
  | Case_aux c "ERlock"
  | Case_aux c "EWlocked"
  | Case_aux c "ERlocked"
  | Case_aux c "EAssert"
].

Definition econtext := expr -> expr.

Definition ctx_call (x : _) (m : _) : econtext := (fun e => ECall x m e).
Hint Unfold ctx_call.
Definition ctx_update (x : _) (f : _) : econtext := (fun e => EUpdate x f e).
Hint Unfold ctx_update.
Definition ctx_let (x : _) (frame : _) (body : _) : econtext := (fun e => ELet x frame e body).
Hint Unfold ctx_let.
Definition ctx_cast (t : _) : econtext := (fun e => ECast t e).
Hint Unfold ctx_cast.
Definition ctx_wlocked (L : _) : econtext := (fun e => EWlocked L e).
Hint Unfold ctx_wlocked.
Definition ctx_rlocked (L : _) : econtext := (fun e => ERlocked L e).
Hint Unfold ctx_rlocked.

Inductive is_econtext : econtext -> Prop := 
  | EC_Call : 
      forall x m,
        is_econtext (ctx_call x m)
  | EC_FieldAssign : 
      forall x f,
        is_econtext (ctx_update x f)
  | EC_Let :
      forall x frame body,
        is_econtext (ctx_let x frame body)
  | EC_Cast :
      forall t,
        is_econtext (ctx_cast t)
  | EC_Wlocked :
      forall L,
        is_econtext (ctx_wlocked L)
  | EC_Rlocked :
      forall L,
        is_econtext (ctx_rlocked L).

Definition isVal (e : expr) : Prop :=
  match e with
    | EVal _ => True
    | _ => False
  end.

Inductive exprStatic : expr -> Prop :=
  | StaticVar : forall x, exprStatic (EVar (SV x))
  | StaticConsume : forall x, exprStatic (EConsume (SV x))
  | StaticNull : exprStatic (EVal VNull)
  | StaticNew : forall c, exprStatic (ENew c)
  | StaticCall : forall x m arg, exprStatic arg -> exprStatic (ECall (SV x) m arg)
  | StaticSelect : forall x f, exprStatic (ESelect (SV x) f)
  | StaticConsumeField : forall x f, exprStatic (EConsumeField (SV x) f)
  | StaticUpdate : forall x f e, exprStatic e -> exprStatic (EUpdate (SV x) f e)
  | StaticLet : forall x e body, exprStatic e -> exprStatic body -> exprStatic (ELet x 0 e body)
  | StaticPar : forall e1 e2 e3, exprStatic e1 -> exprStatic e2 -> exprStatic e3 -> exprStatic (EPar e1 e2 e3)
  | StaticCast : forall t e, exprStatic e -> exprStatic (ECast t e)
  | StaticWlock : forall x r e, exprStatic e -> exprStatic (EWlock (SV x) r e)
  | StaticRlock : forall x r e, exprStatic e -> exprStatic (ERlock (SV x) r e)
  | StaticAssert : forall x y e, exprStatic e -> exprStatic (EAssert (SV x) (SV y) e)
.

Inductive frameFresh (frame : frame_id) : expr -> Prop :=
  | FF_SVar : 
      forall x, 
        frameFresh frame (EVar (SV x))
  | FF_DVar : 
      forall x n, 
        n < frame -> 
        frameFresh frame (EVar (DV (DVar x, n)))
  | FF_SConsume : 
      forall x, 
        frameFresh frame (EConsume (SV x))
  | FF_DConsume : 
      forall x n, 
        n < frame -> 
        frameFresh frame (EConsume (DV (DVar x, n)))
  | FF_Val : 
      forall v,
        frameFresh frame (EVal v)
  | FF_New : 
      forall c, 
        frameFresh frame (ENew c)
  | FF_SCall :
      forall x m arg, 
        frameFresh frame arg ->
        frameFresh frame (ECall (SV x) m arg)
  | FF_DCall :
      forall x n m arg, 
        n < frame ->
        frameFresh frame arg ->
        frameFresh frame (ECall (DV (DVar x, n)) m arg)
  | FF_SSelect :
      forall x f, 
        frameFresh frame (ESelect (SV x) f)
  | FF_DSelect :
      forall x n f, 
        n < frame ->
        frameFresh frame (ESelect (DV (DVar x, n)) f)
  | FF_SConsumeField :
      forall x f, 
        frameFresh frame (EConsumeField (SV x) f)
  | FF_DConsumeField :
      forall x n f, 
        n < frame ->
        frameFresh frame (EConsumeField (DV (DVar x, n)) f)
  | FF_SUpdate :
      forall x f rhs, 
        frameFresh frame rhs ->
        frameFresh frame (EUpdate (SV x) f rhs)
  | FF_DUpdate :
      forall x n f rhs, 
        n < frame ->
        frameFresh frame rhs ->
        frameFresh frame (EUpdate (DV (DVar x, n)) f rhs)
  | FF_Let : 
      forall x n e body, 
        n < frame ->
        frameFresh frame e ->
        frameFresh frame body ->
        frameFresh frame (ELet x n e body)
  | FF_Cast : 
      forall t e,
        frameFresh frame e ->
        frameFresh frame (ECast t e)
  | FF_Par : 
      forall e1 e2 e3,
        frameFresh frame e1 ->
        frameFresh frame e2 ->
        frameFresh frame e3 ->
        frameFresh frame (EPar e1 e2 e3)
  | FF_SWlock : 
      forall x r e,
        frameFresh frame e ->
        frameFresh frame (EWlock (SV x) r e)
  | FF_DWlock : 
      forall x n r e,
        n < frame ->
        frameFresh frame e ->
        frameFresh frame (EWlock (DV (DVar x, n)) r e)
  | FF_SRlock : 
      forall x r e,
        frameFresh frame e ->
        frameFresh frame (ERlock (SV x) r e)
  | FF_DRlock : 
      forall x n r e,
        n < frame ->
        frameFresh frame e ->
        frameFresh frame (ERlock (DV (DVar x, n)) r e)
  | FF_Wlocked : 
      forall L e,
        frameFresh frame e ->
        frameFresh frame (EWlocked L e)
  | FF_Rlocked : 
      forall L e,
        frameFresh frame e ->
        frameFresh frame (ERlocked L e)
  | FF_Assert : 
      forall x y e,
        frameFresh frame e ->
        frameFresh frame (EVar x) ->
        frameFresh frame (EVar y) ->
        frameFresh frame (EAssert x y e)
.

Definition sigma_var (n : frame_id) (x : var) :=
  match x with
    | SV x' => SV x'
    | DV (x', _) => DV (x', n)
  end.

Fixpoint sigma (n : frame_id) (e : expr) : expr :=
  match e with
    | EVar (DV (x, _)) =>
        EVar (DV (x, n))
    | EConsume (DV (x, _)) =>
        EConsume (DV (x, n))
    | ELet x _ e' body => 
        ELet x n (sigma n e') (sigma n body)
    | ECall x m arg => 
        ECall (sigma_var n x) m (sigma n arg)
    | ESelect x f => 
        ESelect (sigma_var n x) f
    | EConsumeField x f => 
        EConsumeField (sigma_var n x) f
    | EUpdate x f rhs => 
        EUpdate (sigma_var n x) f (sigma n rhs)
    | EPar e1 e2 e3 => 
        EPar (sigma n e1)
             (sigma n e2)
             (sigma n e3)
    | ECast t e => 
        ECast t (sigma n e) 
    | EWlock x r e =>
        EWlock (sigma_var n x) r (sigma n e)
    | ERlock x r e =>
        ERlock (sigma_var n x) r (sigma n e)
    | EWlocked L e =>
        EWlocked L (sigma n e)
    | ERlocked L e =>
        ERlocked L (sigma n e)
    | EAssert x y e =>
        EAssert (sigma_var n x) (sigma_var n y) (sigma n e)
    | _ => e
  end.

Fixpoint freeVars (e : expr) : list svar :=
  match e with
    | EVar (SV x) => [x]
    | EConsume (SV x) => [x]
    | ECall (SV x) _ arg => x :: (freeVars arg)
    | ECall (DV _) _ arg => (freeVars arg)
    | ESelect (SV x) _ => [x]
    | EConsumeField (SV x) _ => [x]
    | EUpdate (SV x) _ rhs => x :: (freeVars rhs)
    | EUpdate (DV _) _ rhs => freeVars rhs
    | ELet x frame e body => 
      (freeVars e) ++ 
      (List.remove id_eq_dec x (freeVars body))
    | EPar e1 e2 e3 => (freeVars e1) ++ (freeVars e2) ++ (freeVars e3)
    | ECast t e => freeVars e
    | EWlock (SV x) r e => x :: (freeVars e)
    | EWlock (DV _) r e => freeVars e
    | ERlock (SV x) r e => x :: (freeVars e)
    | ERlock (DV _) r e => freeVars e
    | EWlocked _ e => freeVars e
    | ERlocked _ e => freeVars e
    | EAssert (SV x) (SV y) e => x :: y :: freeVars e
    | EAssert (DV _) (SV y) e => y :: freeVars e
    | EAssert (SV x) (DV _) e => x :: freeVars e
    | EAssert (DV _) (DV _) e => freeVars e
    | _ => nil
  end.

Definition subst_var (x : svar) (y : dvar * frame_id) (z : var) : var := 
  match z with
    | (SV z) => if id_eq_dec x z then DV y else SV z
    | (DV z) => (DV z)
  end.

Hint Unfold subst_var.

Fixpoint subst (x : svar) (y : dvar * frame_id) (e : expr) : expr :=
  match e with
    | EVar z => EVar (subst_var x y z)
    | EConsume z => EConsume (subst_var x y z)
    | ELet z frame e' body => 
        ELet z frame (subst x y e') 
             (if id_eq_dec x z then 
                body 
              else 
                (subst x y body))
    | ECall z m arg => 
        ECall (subst_var x y z)
              m (subst x y arg)
    | ESelect z f => ESelect (subst_var x y z) f
    | EConsumeField z f => EConsumeField (subst_var x y z) f
    | EUpdate z f rhs => 
        EUpdate (subst_var x y z)
                f (subst x y rhs)
    | EPar e1 e2 e3 => 
        EPar (subst x y e1)
             (subst x y e2)
             (subst x y e3)
    | ECast t e => 
        ECast t (subst x y e)
    | EWlock z r e =>
        EWlock (subst_var x y z) r (subst x y e)
    | ERlock z r e =>
        ERlock (subst_var x y z) r (subst x y e)
    | EWlocked L e =>
        EWlocked L (subst x y e)
    | ERlocked L e =>
        ERlocked L (subst x y e)
    | EAssert z1 z2 e => 
        EAssert (subst_var x y z1) (subst_var x y z2) (subst x y e)
    | _ => e
  end.

Fixpoint wlocks (e : expr) : list lock := 
  match e with
    | ECall _ _ arg => wlocks arg
    | EUpdate _ _ rhs => wlocks rhs
    | ELet _ _ e body => wlocks e ++ wlocks body
    | ECast _ e => wlocks e
    | EPar e1 e2 e3 => wlocks e1 ++ wlocks e2 ++ wlocks e3
    | EWlock _ _ e => wlocks e
    | ERlock _ _ e => wlocks e
    | EWlocked L e => L :: wlocks e
    | ERlocked _ e => wlocks e
    | EAssert _ _ e => wlocks e
    | _ => nil
  end.

Fixpoint rlocks (e : expr) : list lock := 
  match e with
    | ECall _ _ arg => rlocks arg
    | EUpdate _ _ rhs => rlocks rhs
    | ELet _ _ e body => rlocks e ++ rlocks body
    | ECast _ e => rlocks e
    | EPar e1 e2 e3 => rlocks e1 ++ rlocks e2 ++ rlocks e3
    | EWlock _ _ e => rlocks e
    | ERlock _ _ e => rlocks e
    | EWlocked _ e => rlocks e
    | ERlocked L e => L :: rlocks e
    | EAssert _ _ e => rlocks e
    | _ => nil
  end.

Definition no_locks (e : expr) : Prop :=
  wlocks e = nil /\ rlocks e = nil.

(*
==============
Configuration
==============
*)

(*
------
Stack
------
*)

Definition dvar_map := partial_map (dvar * frame_id) val.

(*
------
Locks
------
*)

Inductive lock_status : Type :=
  | LLocked : lock_status
  | LReaders : nat -> lock_status.

Definition region_locks := partial_map region_id lock_status.

(*
-----
Heap
-----
*)

Definition dyn_fields := partial_map field_id val.

Definition object := (class_id * dyn_fields * region_locks)%type.

Definition heap := list object.

Definition heapExtend (H : heap) (obj : object) := snoc H obj.

Definition heapLookup (H : heap) (l : loc) :=
  nth_error H l.

Fixpoint heapUpdate (H : heap) (l : loc) (obj : object) :=
  match H with
  | nil => nil
  | obj' :: H' => 
    match l with
    | O    => obj :: H'
    | S l' => obj' :: (heapUpdate H' l' obj)
    end
  end.

(*
--------
Threads
--------
*)

Inductive threads :=
  | T_EXN    : list lock -> threads
  | T_Thread : list lock -> expr -> threads
  | T_Async  : threads -> threads -> expr -> threads.

Definition threads_done (thr : threads) :=
  match thr with
    | T_Thread _ (EVal _) => True
    | _ => False
  end.

Definition threads_exn (thr : threads) :=
  match thr with
    | T_EXN _ => True
    | _ => False
  end.          

Fixpoint heldLocks (T : threads) :=
  match T with
    | T_EXN Ls => Ls
    | T_Thread Ls _ => Ls
    | T_Async T1 T2 _ => heldLocks T1 ++ heldLocks T2
  end.

Fixpoint leftmost_locks (T : threads) : list lock :=
  match T with
    | T_EXN Ls => Ls
    | T_Thread Ls _ => Ls
    | T_Async T1 _ _ => leftmost_locks T1
  end.

Fixpoint t_wlocks (T : threads) :=
  match T with
    | T_EXN _ => nil
    | T_Thread _ e => wlocks e
    | T_Async T1 T2 e => t_wlocks T1 ++ t_wlocks T2 ++ wlocks e
  end.

Fixpoint t_rlocks (T : threads) :=
  match T with
    | T_EXN _ => nil
    | T_Thread _ e => rlocks e
    | T_Async T1 T2 e => t_rlocks T1 ++ t_rlocks T2 ++ rlocks e
  end.

(*
--------------
Configuration
--------------
*)

Definition configuration := (heap * dvar_map * nat * threads)%type.

Definition cfg_done (cfg : configuration) : Prop :=
  match cfg with
    | (_, _, _, thr) => threads_done thr
  end.

Definition cfg_exn (cfg : configuration) : Prop :=
  match cfg with
    | (_, _, _, thr) => threads_exn thr
  end.

(* 
========
Program
========
*)

Inductive fieldDecl : Type := 
  | Field : field_id -> ty -> region_id -> fieldDecl.

Inductive methodDecl : Type := 
  | Method : method_id -> (svar * ty) -> ty -> expr -> methodDecl.

Inductive classDecl : Type :=
  | Cls : class_id -> interface_id -> list fieldDecl -> list methodDecl -> classDecl.

Inductive methodSig : Type := 
  | MethodSig : method_id -> (svar * ty) -> ty -> methodSig.

Inductive interfaceDecl : Type :=
  | Interface : interface_id -> list methodSig -> interfaceDecl
  | ExtInterface : interface_id -> interface_id -> interface_id -> interfaceDecl.

Definition program := (list classDecl * list interfaceDecl * expr)%type.

Definition classLookup(P : program)(c : class_id) : option classDecl :=
  match P with
    | (cs, _, _) =>
      let c_eq c cls := match cls with 
                          | Cls c' _ _ _ => class_id_eq c c'
                        end
      in
      find (c_eq c) cs
  end.

Definition interfaceLookup(P : program)(i : interface_id) : option interfaceDecl :=
  match P with
    | (_, ids, _) =>
      let i_eq i intr := match intr with
                          | Interface i' _ => interface_id_eq i i'
                          | ExtInterface i' _ _ => interface_id_eq i i'
                        end
      in
      find (i_eq i) ids
  end.

Definition fieldLookup(fs : list fieldDecl)(f : field_id) :=
  let f_eq f fld := match fld with 
                     | Field f' _ _ => field_id_eq f f'
                    end
  in
  find (f_eq f) fs.

Definition fields(P : program)(t : ty) :=
  match t with
    | TClass c => match classLookup P c with
                    | Some (Cls _ _ fs _) => Some fs
                    | None => None
                  end
    | _ => None
  end.

Definition methodLookup(ms : list methodDecl)(m : method_id) :=
  let m_eq m mtd := match mtd with 
                      | Method m' _ _ _ => method_id_eq m m'
                    end
  in
  find (m_eq m) ms.

Definition methods(P : program)(t : ty) :=
  match t with
    | TClass c => match classLookup P c with
                    | Some (Cls _ _ _ ms) => Some ms
                    | None => None
                  end
    | _ => None
  end.

Definition methodSigLookup(ms : list methodSig)(m : method_id) :=
  let m_eq m mtd := match mtd with 
                      | MethodSig m' _ _ => method_id_eq m m'
                    end
  in
  find (m_eq m) ms.

Definition extractSigs(ms : list methodDecl) :=
  let extract := fun mtd => match mtd with
                              | Method m param t e => MethodSig m param t
                            end
  in
  map extract ms.

Inductive methodSigs(P : program) : ty -> list methodSig -> Prop :=
  | MSigs_Class :
      forall c i fs ms,
        classLookup P c = Some (Cls c i fs ms) ->
        methodSigs P (TClass c) (extractSigs ms)
  | MSigs_Interface :
      forall i msigs,
        interfaceLookup P i = Some (Interface i msigs) ->
        methodSigs P (TInterface i) msigs
  | MSigs_ExtInterface :
      forall i i1 i2 msigs1 msigs2,
        interfaceLookup P i = Some (ExtInterface i i1 i2) ->
        methodSigs P (TInterface i1) msigs1 ->
        methodSigs P (TInterface i2) msigs2 ->
        methodSigs P (TInterface i) (msigs1 ++ msigs2)
  | MSigs_Unit : 
      methodSigs P TUnit [].


Fixpoint declsToFields (l : list fieldDecl) :=
  match l with
    | nil => empty
    | fd :: fs => 
      match fd with 
        | Field f _ _ => 
          extend (declsToFields fs) f VNull
      end
  end.

Inductive declsToRegionLocks (fs : list fieldDecl) : region_locks -> Prop :=
  | DeclsToRegionLocks :
      forall RL,
        (forall f t r, fieldLookup fs f = Some (Field f t r) -> 
                       RL r = Some (LReaders 0)) ->
        declsToRegionLocks fs RL.



