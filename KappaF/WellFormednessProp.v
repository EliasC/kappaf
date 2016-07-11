Require Export WellFormedness.
Require Import SyntaxProp.
Require Import TypesProp.
Require Import Shared.

(*
========================
Field and method lookup
========================
*)


Lemma wfProgram_wfMethodDecl :
  forall P t' c ms m mtd,
    wfProgram P t' ->
    methods P (TClass c) = Some ms ->
    methodLookup ms m = Some mtd ->
    wfMethodDecl P c mtd.
Proof with auto.
  introv wfP Hmethods mLookup.
  inv wfP.
  unfold methods in Hmethods.
  remember (classLookup (cds, ids, e) c) as cLookup.
  symmetry in HeqcLookup.
  destruct cLookup as [[c' i fs ms'] |]...
  inv_eq.
  assert (Heq : c = c') by
      (unfold classLookup in HeqcLookup;
       apply find_true in HeqcLookup;
       apply class_id_eq_eq; auto).
  subst.
  lookup_forall as wfCls. 
  inv wfCls. 
  lookup_forall mtd as wfMtd...
Qed.


Corollary dyn_wfFieldLookup :
  forall P Gamma c F fs f t r,
    wfFields P Gamma c F ->
    fields P (TClass c) = Some fs ->
    fieldLookup fs f = Some (Field f t r) ->
    exists v, F f = Some v /\ P; Gamma |- (EVal v) \in t.
Proof with eauto.
  introv wfF Hfields fLookup.
  inv wfF. rewrite_and_invert...
Qed.

Hint Immediate dyn_wfFieldLookup.

(*
------------
Method sigs
------------
*)

Hint Constructors methodSigs.

Lemma extractSigs_sound :
  forall mtds m x t t',
    (exists e, methodLookup mtds m = Some (Method m (x, t) t' e)) <->
    methodSigLookup (extractSigs mtds) m = Some (MethodSig m (x, t) t').
Proof with eauto.
  intros. split. 
  + gen t t' m x. 
    induction mtds as [|[m [x t] t' e]]; simpl;
    introv H; inv H as [e' Hsigs]... 
    cases_if... inv_eq. 
  + gen t t' m x. 
    induction mtds as [|[m [x t] t' e]]; simpl;
    introv mLookup; inv mLookup... 
    cases_if; crush...
Qed.

Lemma methodSigs_deterministic :
  forall P t msigs1 msigs2,
    methodSigs P t msigs1 ->
    methodSigs P t msigs2 ->
    msigs1 = msigs2.
Proof with eauto.
  introv Hsigs1 Hsigs2. 
  gen msigs2.
  induction Hsigs1; introv Hsigs2; 
  inv Hsigs2; try(rewrite_and_invert)...
  rewrite IHHsigs1_1 with msigs3...
  rewrite IHHsigs1_2 with msigs4...
Qed.

Lemma methodSigs_wfType_exists : 
  forall P t' t, 
    wfProgram P t' ->
    (wfType P t <->
     exists msigs, methodSigs P t msigs).
Proof with eauto.
  introv [? ? ? wfCds wfIds wfExpr].
  split.
  + intros wfT. 
    inv wfT as [c cLookup|i iLookup|]...
    - apply classLookup_not_none in cLookup as [i [fs [ms]]]...
    - apply interfaceLookup_not_none in iLookup.
      inv iLookup as [[msigs]|[i1 [i2]]]...
      * intros. lookup_forall as wfId. inv wfId...
  + intros Hex. destruct Hex as [msigs Hsigs].
    destruct t; inv Hsigs; constructor; crush.
Qed.

Lemma methodSigs_sub :
  forall P t t1 t2 m msigs1 msigs2 msig,
    wfProgram P t ->
    subtypeOf P t1 t2 ->
    methodSigs P t1 msigs1 ->
    methodSigs P t2 msigs2 ->
    methodSigLookup msigs2 m = Some msig ->
    methodSigLookup msigs1 m = Some msig.
Proof with eauto using 
                 methodSigs_deterministic,
                 methodSigs_wfType_exists,
                 subtypeOf_wfTypeSub,
                 subtypeOf_wfTypeSup.
  introv [? ? ? ? wfCds wfIds wfExpr] Hsub
         Hsigs1 Hsigs2 Hsig.
  gen msigs1 msigs2 msig.
  subtypeOf_cases(induction Hsub) Case; intros.
  + Case "Sub_Class".
    lookup_forall as wfCd. inv wfCd.
    assert (msigs2 = (extractSigs ms))...
    subst. inv Hsigs1; rewrite_and_invert.
  + Case "Sub_InterfaceLeft".
    inv Hsigs1; rewrite_and_invert. 
    assert (msigs0 = msigs2)...
    subst. apply find_app...
  + inv Hsigs1; rewrite_and_invert. 
    assert (msigs2 = msigs3)...
    subst. apply find_app2...
    lookup_forall as wfId. 
    inverts wfId as Hsigs3 Hsigs4 sigsDisjoint1 sigsDisjoint2.
    assert (msigs0 = msigs1)...
    assert (msigs2 = msigs3)...
    subst. fold (methodSigLookup msigs1 m).
    eapply sigsDisjoint2...
  + asserts_rewrite (msigs1 = msigs2)...
  + rename msigs2 into msigs3.
    rename Hsigs2 into Hsigs3.
    assert (wfT1: wfType (cds, ids, e) t1)...
    assert (wfT2: wfType (cds, ids, e) t2)...
    eapply methodSigs_wfType_exists in wfT2 as []...
  + inv Hsigs2. inv Hsig.
Qed.

(*
Lemma methodSigs_methods :
  forall P t' t c msigs,
    wfProgram P t' ->
    methodSigs P t msigs ->
    subtypeOf P (TClass c) t ->
    exists mtds, methods P (TClass c) = Some mtds.
Proof with eauto.
  introv wfP Hsigs Hsub.
  assert (wfT1: wfType P (TClass c))
    by (eapply subtypeOf_wfType in Hsub as []; eassumption).
  inv wfT1 as [? cLookup | |].
  apply classLookup_not_none in cLookup as [i [fs [ms cLookup]]].
  simpl. rewrite cLookup...
Qed.
*)

(*
==============
Configuration
==============
*)

(*
---------
wfFields
---------
*)

Lemma wfFields_declsToFields :
  forall P t' c i fs ms Gamma,
    wfProgram P t' ->
    wfEnv P Gamma ->
    classLookup P c = Some (Cls c i fs ms) ->
    wfFields P Gamma c (declsToFields fs).
Proof with eauto using 
                 fields_wfFieldDecl, 
                 declsToFields_null.
  introv wfProgram wfEnv Hlookup. 
  assert (fields P (TClass c) = Some fs)
    by (unfolds; rewrite Hlookup; auto).
  assert (Forall (wfFieldDecl P) fs)...
  econstructor...
  intros. 
  lookup_forall as wfF. inv wfF...
Qed.

Lemma wfFields_extend :
  forall P Gamma c fs f t r F v,
    fields P (TClass c) = Some fs ->
    fieldLookup fs f = Some (Field f t r) ->
    wfFields P Gamma c F ->
    P; Gamma |- EVal v \in t ->
    wfFields P Gamma c (extend F f v).
Proof with eauto with env.
  introv Hfields fLookup wfF hasType.
  econstructor...
  introv fLookup'.
  inv wfF.
  case_extend; rewrite_and_invert...
Qed.

Lemma wfFields_envExtend : 
  forall P t' Gamma c F l c', 
    wfProgram P t' ->
    wfFields P Gamma c F ->
    wfEnv P Gamma ->
    fresh Gamma (env_loc l) ->
    wfType P (TClass c') ->
    wfFields P (extend Gamma (env_loc l) (TClass c')) c F.
Proof with eauto using hasType_extend_loc.
  introv wfP wfF wfGamma Hfresh wfT.
  inverts wfF as Hfields wfFlds.
  econstructor...
  introv Hlookup.
  apply wfFlds in Hlookup as (v & Heq & hasType)...
Qed.

Lemma wfFields_invariance :
  forall P t' c Gamma Gamma' F,
    wfProgram P t' ->
    (forall l, Gamma (env_loc l) = Gamma' (env_loc l)) ->
    wfEnv P Gamma' ->
    wfFields P Gamma c F ->
    wfFields P Gamma' c F.
Proof with eauto using hasType_wfType.
  introv wfP envSub wfGamma' wfF.
  inverts wfF as Hfields wfFld.
  econstructor...
  introv fLookup.
  apply wfFld in fLookup as (v & Ff & hasType).
  exists v. split...
  destruct v...
  + inv hasType.
    econstructor...
    rewrite <- envSub...
Qed.

Lemma wfHeap_wfObject :
  forall P Gamma H l c F RL,
    wfHeap P Gamma H ->
    heapLookup H l = Some (c, F, RL) ->
    wfFields P Gamma c F /\ wfRegionLocks P c RL.
Proof with eauto.
  introv wfH Hlookup. 
  inverts wfH as _ envModelsHeap heapMirrorsEnv. 
  assert (Hl: heapLookup H l <> None) by crush.
  apply heapMirrorsEnv in Hl.
  destruct Hl as [c' envLookup].
  apply envModelsHeap in envLookup as (F' & RL' & ? & ? & ?).
  rewrite_and_invert.
Qed.

Lemma wfHeap_wfFields :
  forall P Gamma H l c F RL,
    wfHeap P Gamma H ->
    heapLookup H l = Some (c, F, RL) ->
    wfFields P Gamma c F.
Proof with eauto.
  introv wfH Hlookup.
  eapply wfHeap_wfObject in Hlookup as []...
Qed.

Lemma wfHeap_wfRegionLocks :
  forall P Gamma H l c F RL,
    wfHeap P Gamma H ->
    heapLookup H l = Some (c, F, RL) ->
    wfRegionLocks P c RL.
Proof with eauto.
  introv wfH Hlookup.
  eapply wfHeap_wfObject in Hlookup as []...
Qed.

Lemma wfRegionLocks_declsToRegionLocks :
  forall P c fs RL,
    fields P (TClass c) = Some fs ->
    declsToRegionLocks fs RL ->
    wfRegionLocks P c RL.
Proof with eauto.
  introv fLookup HRL.
  inv HRL.
  econstructor...
Qed.

(*
-------
wfHeap
-------
*)

Hint Constructors wfHeap.


Lemma wfHeap_fresh :
  forall P Gamma H l,
    wfHeap P Gamma H ->
    heapLookup H l = None ->
    fresh Gamma (env_loc l).
Proof with eauto.
  introv wfH Hlookup. 
  inverts wfH as wfGamma envModelsHeap heapMirrorsEnv.
  unfold fresh. remember (Gamma (env_loc l)) as t...
  destruct t... 
  symmetry in Heqt. 
  assert (tClass: exists c, t = TClass c) by (inv wfGamma; eauto).
  inv tClass as [c''].
  apply envModelsHeap in Heqt.
  inv Heqt as [F' [RL [contra]]]. rewrite_and_invert.
Qed.

Lemma wfHeap_extend :
  forall P t' Gamma H c F RL,
    wfProgram P t' ->
    wfHeap P Gamma H ->
    wfType P (TClass c) ->
    wfFields P Gamma c F ->
    wfRegionLocks P c RL ->
    wfHeap P (extend Gamma (env_loc (length H)) (TClass c)) (heapExtend H (c, F, RL)).
Proof with eauto using wfHeap_wfRegionLocks with env.
  introv wfP wfH wfT wfF wfRL.
  inverts wfH as wfGamma envModelsHeap heapMirrorsEnv.
  constructor...
  + introv envLookup.
    destruct (id_eq_dec l (length H)).
    - subst. simpl_extend_hyp. inv_eq. 
      rewrite heapExtend_lookup_len.
      eexists; eexists; split; split...
      eapply wfFields_envExtend...
      eapply wfHeap_fresh...
      apply heapLookup_ge...
    - rewrite extend_neq in envLookup... 
      rewrite heapExtend_lookup_nlen...
      apply envModelsHeap in envLookup as (F' & RL' & Hlookup & wfF' & wfRL')...
      eexists; eexists; split...
      split...
      eapply wfFields_envExtend...
      eapply wfHeap_fresh...
      apply heapLookup_ge...
  + introv Hlookup.
    destruct (id_eq_dec l (length H))...
    rewrite heapExtend_lookup_nlen in Hlookup...
Qed.

Lemma wfHeap_update :
  forall P Gamma H l c F RL RL' F',
    wfHeap P Gamma H ->
    heapLookup H l = Some (c, F, RL) ->
    wfFields P Gamma c F' ->
    wfRegionLocks P c RL' ->
    wfHeap P Gamma (heapUpdate H l (c, F', RL')).
Proof with eauto.
  introv wfH Hlookup wfF' wfRL'. 
  inverts wfH as wfGamma envModelsHeap heapMirrorsEnv.
  constructor...
  + introv envLookup.
    destruct (id_eq_dec l l0).
    - subst. 
      rewrite lookup_heapUpdate_eq 
        by (apply heapLookup_lt; eauto). 
      apply envModelsHeap in envLookup as (F'' & RL'' & Hlookup' & wfF'' & wfRL'').
      rewrite_and_invert...      
    - rewrite lookup_heapUpdate_neq...
  + introv Hlookup'.
    apply heapMirrorsEnv.
    destruct (id_eq_dec l l0).
    - subst. 
      rewrite heapLookup_not_none...
    - rewrite lookup_heapUpdate_neq in Hlookup'...
Qed.

Lemma wfHeap_invariance :
  forall P t' Gamma Gamma' H,
    wfProgram P t' ->
    (forall l, Gamma (env_loc l) = Gamma' (env_loc l)) ->
    wfEnv P Gamma' ->
    wfHeap P Gamma H ->
    wfHeap P Gamma' H.
Proof with eauto using wfFields_invariance.
  introv wfP envEquiv wfGamma' wfH.
  inverts wfH as wfGamma envModelsHeap heapMirrorsEnv.
  constructor...
  + introv envLookup. rewrite <- envEquiv in envLookup.
    apply envModelsHeap in envLookup. 
    inv envLookup as (F & RL & Hlookup & wfF & wfRL)...
    exists F RL...
  + introv Hlookup. rewrite <- envEquiv... 
Qed.

(*
--------
wfVars
--------
*)

Hint Constructors wfVars.

Lemma wfVars_invariance :
  forall P t' Gamma Gamma' fsyms V,
    wfProgram P t' ->
    (forall x, Gamma x = Gamma' x) ->
    wfEnv P Gamma' ->
    wfVars P Gamma fsyms V ->
    wfVars P Gamma' fsyms V.
Proof with eauto.
  introv wfP envEquiv wfGamma' wfV.
  inverts wfV as wfGamma envModelsVars varsMirrorEnv Hfresh.
  constructor...
  + introv Vlookup.
    rewrite <- envEquiv in Vlookup.
    apply envModelsVars in Vlookup as (v & Vlookup & hasType).
    eapply hasType_subsumption with (Gamma' := Gamma') in hasType; crush...
  + introv. rewrite <- envEquiv...
Qed.

Lemma wfVars_extend :
  forall P t' Gamma n m frame V v t,
    wfProgram P t' ->
    wfVars P Gamma n V ->
    P; Gamma |- EVal v \in t ->
    m < n ->
    frame < n ->
    wfVars P (extend Gamma (env_var (DV (DVar m, frame))) t) 
           n (extend V (DVar m, frame) v).
Proof with eauto with env.
  introv wfP wfV hasType Hnlt Hflt. 
  inverts wfV as wfGamma envModelsVars varsMirrorEnv Hfresh.
  constructor; eauto 3 with env.
  + introv envLookup.
    destruct (id_eq_dec (DVar m, frame) x).
    - subst. simpl_extend_hyp.
      inv_eq. 
      exists v.
      split...
      inv hasType...
    - rewrite extend_neq in envLookup... 
      apply envModelsVars in envLookup as (v' & Vlookup & hasType').
      exists v'.
      split... 
      inv hasType'... 
  + simpl. split. 
    - introv Hle. unfold fresh.
      assert (m < n')
        by omega.
      inverts Hfresh as nFresh fFresh. 
      case_extend; [inv_eq | apply nFresh]; omega.
    - introv Hle. unfold fresh.
      assert (frame < frame')
        by omega.
      inverts Hfresh as nFresh fFresh. 
      case_extend; [inv_eq | apply fFresh]; omega.
Qed.

Lemma wfVars_heapExtend :
  forall Gamma P t' n V l c,
    wfProgram P t' ->
    wfVars P Gamma n V ->
    fresh Gamma (env_loc l) ->
    wfType P (TClass c) ->
    wfVars P (extend Gamma (env_loc l) (TClass c)) n V.
Proof with eauto with env.
  introv wfP wfV Hfresh wfT.
  inverts wfV as wfGamma envModelsVars varsMirrorEnv freshVars.
  constructor... 
  + introv envLookup.
    simpl_extend_hyp.
    apply envModelsVars in envLookup as (v & Vlookup & hasType).
    exists v.
    split...
    inv hasType...
Qed.

Lemma wfVars_ge :
  forall P Gamma n V m,
    wfVars P Gamma n V ->
    n <= m ->
    wfVars P Gamma m V.
Proof with eauto.
  introv wfV Hge.
  inverts wfV as wfGamma envModels varsMirror Hfresh.
  inverts Hfresh as nFresh fFresh.
  econstructor...
  econstructor; introv Hle. 
  assert (n <= n') by omega... 
  assert (n <= frame') by omega... 
Qed.

(*
----------
wfLocking
----------
*)

Hint Constructors wfHeldLocks.
Hint Constructors wfWLocks.
Hint Constructors wfRLocks.
Hint Constructors disjointLocks.
Hint Constructors wfLocking.

Lemma wfHeldLocks_heapExtend :
  forall H Ls c F RL,
    wfHeldLocks H Ls ->
    wfHeldLocks (heapExtend H (c, F, RL)) Ls.
Proof with eauto.
  introv wfLs.
  constructor.
  induction wfLs as [wfLs]...
  rewrite Forall_forall in wfLs.
  apply Forall_forall.
  introv HIn.
  apply wfLs in HIn as [].
  assert (Hlt: l < length H) by 
      (eapply heapLookup_lt; eauto)...
  econstructor...
  rewrite heapExtend_lookup_nlen...
  omega.
Qed.

Lemma wfRLocks_heapExtend :
  forall H T c' F' RL',
    wfRLocks H T ->
    wfRLocks (heapExtend H (c', F', RL')) T.
Proof with eauto.
  introv wfRl.
  inverts wfRl as wfRl.
  econstructor.
  introv HIn.
  pose proof (wfRl _ _ HIn) as (c & F & RL & n & Hlookup & HRL & Hle).
  assert (Hlt: l < length H) by 
      (eapply heapLookup_lt; eauto)...  
  rewrite heapExtend_lookup_nlen...
  omega.  
Qed.

Lemma wfLocking_heapExtend :
  forall H T c F RL,
    wfLocking H T ->
    wfLocking (heapExtend H (c, F, RL)) T.
Proof with eauto using wfHeldLocks_heapExtend, wfRLocks_heapExtend.
  introv wfL.
  induction wfL...
Qed. 

Lemma wfHeldLocks_heapUpdate :
  forall H Ls l c F F' RL RL',
    wfHeldLocks H Ls ->
    heapLookup H l = Some (c, F, RL) ->
    (forall r, In (l, r) Ls -> RL' r = Some LLocked) ->
    wfHeldLocks (heapUpdate H l (c, F', RL')) Ls.
Proof with eauto.
  introv wfLs Hlookup HRL'.
  induction wfLs as [wfLs]...
  rewrite Forall_forall in wfLs.
  constructor.
  apply Forall_forall.
  introv HIn. destruct x as [].
  assert(wfL: wfLock H (l0, r))...
  inverts wfL as Hlookup' HRL.
  destruct (id_eq_dec l l0).
  + subst. rewrite_and_invert. 
    apply HRL' in HIn. 
    apply WF_Lock with c F' RL'...
    rewrite lookup_heapUpdate_eq...
    apply heapLookup_lt...
  + econstructor... 
    rewrite lookup_heapUpdate_neq...
Qed.

Lemma wfRLocks_heapUpdate :
  forall H T l c F' RL',
    wfRLocks H T ->
    (forall r, In (l, r) (t_rlocks T) ->
               exists n, RL' r = Some (LReaders n) /\
                         length (filter (lock_eq (l, r)) (t_rlocks T)) <= n) ->
    wfRLocks (heapUpdate H l (c, F', RL')) T.
Proof with eauto. 
  introv wfRl wfRL'.
  inverts wfRl as wfRl.
  econstructor...
  introv HIn.
  pose proof (wfRl _ _ HIn) as (c' & F & RL & n & Hlookup & HRL & Hle).
  destruct (id_eq_dec l0 l).
  + subst. 
    apply wfRL' in HIn as (n' & HRL' & Hle').
    rewrite lookup_heapUpdate_eq...
    repeat eexists...
    apply heapLookup_lt...
  + rewrite lookup_heapUpdate_neq...
Qed.

Lemma wfLocking_heapUpdate :
  forall H T l c F F' RL RL',
    wfLocking H T ->
    heapLookup H l = Some (c, F, RL) ->
    (forall r, In (l, r) (heldLocks T) -> RL' r = Some LLocked) ->
    (forall r, In (l, r) (t_rlocks T) ->
               exists n, RL' r = Some (LReaders n) /\
                         length (filter (lock_eq (l, r)) (t_rlocks T)) <= n) ->
    wfLocking (heapUpdate H l (c, F', RL')) T.
Proof with eauto using wfHeldLocks_heapUpdate, wfRLocks_heapUpdate.
  introv wfL Hlookup HWl HRl.
  induction wfL; simpls...
  econstructor...
  + apply IHwfL1...
    - introv HIn.
      apply HWl. apply in_or_app...
    - introv HIn. 
      assert (HIn': In (l, r) (t_rlocks T1 ++ t_rlocks T2 ++ rlocks e))
        by eauto using in_or_app...
      apply HRl in HIn' as (n' & HRL & Hle)...
      exists n'. split... 
      rewrite filter_app in Hle.
      rewrite app_length in Hle.
      omega.
  + apply IHwfL2...
    - introv HIn.
      apply HWl. apply in_or_app...
    - introv HIn. 
      assert (HIn': In (l, r) (t_rlocks T1 ++ t_rlocks T2 ++ rlocks e))
        by eauto using in_or_app...
      apply HRl in HIn' as (n' & HRL & Hle)...
      exists n'. split... 
      rewrite filter_app in Hle.
      rewrite app_length in Hle.
      assert(Hle': length (filter (lock_eq (l, r)) (t_rlocks T2 ++ rlocks e)) <= n') by omega...
      rewrite filter_app in Hle'.
      rewrite app_length in Hle'.
      omega.      
Qed.

(* Lemma wfLocking_heapUpdate : *)
(*   forall H Ls e l c F F' RL, *)
(*     wfLocking H Ls e -> *)
(*     heapLookup H l = Some (c, F, RL) -> *)
(*     wfLocking (heapUpdate H l (c, F', RL)) Ls e. *)
(* Proof with eauto. *)
(*   introv wfL Hlookup. *)
(*   inverts wfL as Hwlocks Hdistinct Hrlocks. *)
(*   econstructor... *)
(*   introv Hin. *)
(*   destruct (id_eq_dec l l0). *)
(*   + subst. rewrite lookup_heapUpdate_eq... *)
(*     apply Hrlocks in Hin as (c' & F'' & RL' & n & Hlookup' & HRL' & Hrlocks')... *)
(*     rewrite_and_invert. repeat eexists... *)
(*     apply heapLookup_lt... *)
(*   + rewrite lookup_heapUpdate_neq... *)
(* Qed. *)

Lemma wfHeldLocks_taken :
  forall H Ls l r c RL F,
    wfHeldLocks H Ls ->
    In (l, r) Ls ->
    heapLookup H l = Some (c, F, RL) ->
    RL r = Some LLocked.
Proof with eauto.
  introv wfLs HIn Hlookup.
  induction wfLs as [wfLs]...
  rewrite Forall_forall in wfLs.
  apply wfLs in HIn. inv HIn.
  rewrite_and_invert...
Qed.

Lemma wfWLocks_econtext :
  forall Ls e ctx,
    is_econtext ctx ->
    wfWLocks Ls (ctx e) ->
    wfWLocks Ls e.
Proof with eauto using in_or_app.
  introv Hctx wfL.
  inv Hctx; 
    inverts wfL as Hwlocks Hdup Hrlocks;
    simpl in *...
  + eapply NoDup_app in Hdup as []...
  + inv Hdup...
Qed.

Lemma wfRLocks_econtext :
  forall H Ls e ctx,
    is_econtext ctx ->
    wfRLocks H (T_Thread Ls (ctx e)) ->
    wfRLocks H (T_Thread Ls e).
Proof with eauto using in_or_app.
  introv Hctx wfRl.
  inv Hctx; 
    inverts wfRl as wfRl;
    simpls... 
  + econstructor; simpls. 
    introv HIn. 
    assert (HIn': In (l, r) (rlocks e ++ rlocks body))...
    apply wfRl in HIn' as (c & F & RL & n & Hlookup & HRL & Hlen).
    rewrite filter_app in Hlen.
    rewrite app_length in Hlen.
    repeat eexists... omega.
  + econstructor; simpls.
    introv HIn. 
    assert (HIn': L = (l, r) \/ In (l, r) (rlocks e))...
    apply wfRl in HIn' as (c & F & RL & n & Hlookup & HRL & Hlen).
    cases_if; simpls.
    - repeat eexists... omega.
    - repeat eexists... 
Qed.

Lemma wfRLocks_async :
  forall H T1 T2 Ls e,
    wfRLocks H (T_Async T1 T2 e) ->
    wfRLocks H T1 /\ wfRLocks H T2 /\ wfRLocks H (T_Thread Ls e). 
Proof with eauto with arith.
  introv wfRl.
  inverts wfRl as wfRl; simpls.
  splits; econstructor;
  introv HIn; 
  assert(HIn': In (l, r) (t_rlocks T1 ++ t_rlocks T2 ++ rlocks e))
    by eauto using in_or_app;
  apply wfRl in HIn' as (c' & F' & RL' & n'' & Hlookup & HRL & Hle);
  repeat(rewrite filter_app in Hle);
  repeat(rewrite app_length in Hle);
  repeat eexists... 
Qed.

Lemma wfRLocks_async_commutative :
  forall H T1 T2 e,
    wfRLocks H (T_Async T1 T2 e) ->
    wfRLocks H (T_Async T2 T1 e).
Proof with eauto using in_app_or, in_or_app.
  introv wfRl.
  inv wfRl.
  econstructor.
  introv HIn; simpls.
  assert (HIn': In (l, r) (t_rlocks T1 ++ t_rlocks T2 ++ rlocks e)).
  + apply in_app_or in HIn.
    inverts HIn as HIn...
    apply in_app_or in HIn.
    inverts HIn as HIn...
  + apply H0 in HIn' as (c' & F' & RL' & n'' & Hlookup & HRL & Hle).
    repeat eexists...
    rewrite filter_app.
    rewrite filter_app.
    rewrite app_length.
    rewrite app_length.
    rewrite filter_app in Hle.
    rewrite filter_app in Hle.
    rewrite app_length in Hle.
    rewrite app_length in Hle.
    omega.
Qed.

Lemma wfLocking_econtext :
  forall ctx H Ls e,
    is_econtext ctx ->
    wfLocking H (T_Thread Ls (ctx e)) ->
    wfLocking H (T_Thread Ls e).
Proof with eauto using wfWLocks_econtext, wfRLocks_econtext. 
  introv Hctx wfL.
  inv wfL...
Qed.

Lemma wfLocking_subst :
  forall H Ls e x y,
    wfLocking H (T_Thread Ls e) ->
    wfLocking H (T_Thread Ls (subst x y e)).
Proof with eauto.
  introv wfL.
  inverts wfL as wfLs Hdup wfWl wfRl. 
  econstructor... 
  + econstructor...
    rewrite <- wlocks_subst...
    inv wfWl...
    rewrite <- wlocks_subst...
    inv wfWl...
  + econstructor; simpl...
    rewrite <- rlocks_subst...
    inv wfRl...
Qed.

Lemma wfLocking_sigma :
  forall H Ls e n,
    wfLocking H (T_Thread Ls e) ->
    wfLocking H (T_Thread Ls (sigma n e)).
Proof with eauto.
  introv wfL.
  inverts wfL as wfLs Hdup wfWl wfRl. 
  econstructor... 
  + econstructor...
    rewrite <- wlocks_sigma...
    inv wfWl...
    rewrite <- wlocks_sigma...
    inv wfWl...
  + econstructor; simpl...
    rewrite <- rlocks_sigma...
    inv wfRl...
Qed.

Lemma wlocks_static :
  forall e,
    exprStatic e ->
    wlocks e = nil.
Proof with eauto using app_eq_nil.
  introv Hstatic.
  induction Hstatic; simpl...
  apply app_eq_nil...
Qed.

Lemma rlocks_static :
  forall e,
    exprStatic e ->
    rlocks e = nil.
Proof with eauto using app_eq_nil.
  introv Hstatic.
  induction Hstatic; simpl...
  apply app_eq_nil...
Qed.

Lemma wfLocking_static :
  forall H Ls e,
    wfHeldLocks H Ls ->
    NoDup Ls ->
    exprStatic e ->
    wfLocking H (T_Thread Ls e).
Proof with eauto using wlocks_static, rlocks_static.
  introv wfLs Hdup Hstatic.
  assert (Hwl: wlocks e = nil)...
  assert (Hrl: rlocks e = nil)...
  econstructor... 
  + econstructor; rewrite Hwl...
    introv HIn... inv HIn.
  + econstructor; simpl; rewrite Hrl...
    introv HIn... inv HIn.
Qed.

Lemma disjointLocks_commutative :
  forall T1 T2,
    disjointLocks T1 T2 ->
    disjointLocks T2 T1.
Proof with eauto.
  introv Hdisj.
  inv Hdisj. constructors...
Qed.

Lemma disjointLocks_async :
  forall T T1 T2 e,
    disjointLocks T1 T /\
    disjointLocks T2 T
     <->
    disjointLocks (T_Async T1 T2 e) T.
Proof with eauto using in_or_app.
  split.
  + introv Hdisj.
    inverts Hdisj as Hdisj1 Hdisj2.
    inverts Hdisj1. inverts Hdisj2.
    constructor; simpl.
    - introv HIn.
      apply in_app_or in HIn as [|HIn]...
    - introv HIn.
      apply not_in_app...
  + introv Hdisj.
    inverts Hdisj as Hdisj1 Hdisj2.
    simpls.
    splits.
    - constructor...
      introv HIn.
      apply Hdisj2 in HIn...
    - constructor...
      introv HIn.
      apply Hdisj2 in HIn.
      eapply not_in_app in HIn as []...
Qed.

Lemma disjointLocks_leftmost :
  forall T1 T2,
    disjointLocks T1 T2 ->
    disjointLocks (T_EXN (leftmost_locks T1)) T2.
Proof with eauto using in_or_app.
  introv Hdisj.
  induction T1; simpls; inv Hdisj...
  apply IHT1_1.
  econstructor; crush...
Qed.

Lemma wfHeldLocks_app :
  forall H Ls1 Ls2,
    (wfHeldLocks H Ls1 /\ wfHeldLocks H Ls2 <-> wfHeldLocks H (Ls1 ++ Ls2)).
Proof with eauto using in_eq, in_cons.
  split.
  + introv wfLs.
    inverts wfLs as wfLs1 wfLs2.
    constructor.
    apply Forall_app...
    inv wfLs1...
    inv wfLs2...
  + introv wfLs.
    induction Ls1 as [|[l r]]; simpls...
    inverts wfLs as wfLs. 
    inverts wfLs as wfL wfLs'.
    assert(wfLs: wfHeldLocks H (Ls1 ++ Ls2))...
    apply IHLs1 in wfLs as [wfLs1 wfLs2]...
    split...
    econstructor... 
    econstructor...
    apply Forall_forall.
    rewrite Forall_forall in wfLs'.
    introv HIn.
    assert (HIn': In x (Ls1 ++ Ls2)) 
      by eauto using in_or_app...
Qed.

Lemma wfHeldLocks_cons :
  forall H Ls l r,
    wfHeldLocks H Ls ->
    wfLock H (l, r) ->
    wfHeldLocks H ((l,r) :: Ls).
Proof with eauto.    
  introv wfLs wfL.
  inv wfLs...
Qed.

Lemma wfHeldLocks_leftmost :
  forall H T,
    wfLocking H T ->
    wfHeldLocks H (leftmost_locks T).
Proof with eauto.
  introv wfL.
  induction T; inv wfL...
Qed.

Lemma wfHeldLocks_remove :
  forall H Ls L eq_dec,
    wfHeldLocks H Ls ->
    wfHeldLocks H (remove eq_dec L Ls).
Proof with eauto using wfHeldLocks_cons.
  introv wfLs.
  induction Ls as [| [l r]]...
  inverts wfLs as wfLs.
  inverts wfLs.
  simpl. cases_if...
Qed.

Corollary wfLocking_wfHeldLocks :
  forall H T,
    wfLocking H T ->
    wfHeldLocks H (heldLocks T).
Proof with eauto.
  introv wfL.
  induction T; simpls; inv wfL...
  apply wfHeldLocks_app...
Qed.

Corollary wfLocking_wfRLocks :
  forall H T,
    wfLocking H T ->
    wfRLocks H T.
Proof with eauto.
  introv wfL.
  induction T; simpls; inv wfL...
  crush.
Qed.

(*
----------
wfThreads
----------
*)

Hint Constructors wfThreads.

Corollary wfThreads_wfEnv : 
  forall P t' Gamma frame T t,
    wfProgram P t' ->
    wfThreads P Gamma frame T t ->
    wfEnv P Gamma.
Proof with eauto with env.
  introv wfP wfT. inv wfT...
Qed.

Hint Immediate wfThreads_wfEnv.

(*
Lemma wfThreads_econtext :
  forall P t' ctx Gamma frame T t,
    wfProgram P t' ->
    is_econtext ctx ->
    wfThreads P Gamma frame T t ->
    match T with
      | T_Thread e => 
        forall e',
          ctx e' = e -> 
          exists t'', wfThreads P Gamma frame (T_Thread e') t''
      | T_Async T1 T2 e => 
        forall e',
          ctx e' = e -> 
          exists t'', wfThreads P Gamma frame (T_Async T1 T2 e') t''
      | T_EXN => True
    end.
Proof with eauto using econtext_freeVars.
  introv wfP Hctx wfT.
  induction T; try(introv Heq)...
  + inverts wfT as Hfree Hfresh hasType.
    assert (freeVars e' = nil)...
    inv Hctx; inv Hfresh; inv hasType; eexists...
  + inverts wfT as Hfree Hfresh hasType.    
    assert (freeVars e' = nil)...
    inv Hctx; inv Hfresh; inv hasType; eexists...
Qed.
*)

Lemma wfThreads_invariance :
  forall P t' Gamma Gamma' frame T t,
    wfProgram P t' ->
    (forall x, Gamma x = Gamma' x) ->    
    wfThreads P Gamma  frame T t ->
    wfThreads P Gamma' frame T t.
Proof with eauto using hasType_subsumption, 
                       wfEnv_equiv with env.
  introv wfP Hequiv wfT.
  induction wfT...
Qed.

Lemma wfThreads_subsumption :
  forall P t' Gamma Gamma' frame T t,
    wfProgram P t' ->
    wfSubsumption Gamma Gamma' ->    
    wfEnv P Gamma' ->
    wfThreads P Gamma  frame T t ->
    wfThreads P Gamma' frame T t.
Proof with eauto using hasType_subsumption with env.
  introv wfP wfEnv' Hsub wfT.
  induction wfT...
Qed.

Lemma wfThreads_heapExtend :
  forall P t' Gamma frame T t c l,
    wfProgram P t' ->
    wfType P (TClass c) ->
    fresh Gamma (env_loc l) ->
    wfThreads P Gamma frame T t ->
    wfThreads P (extend Gamma (env_loc l) (TClass c)) frame T t.
Proof with eauto using hasType_extend_loc with env.
  introv wfP wfTy Hfresh wfT.
  generalize dependent t.
  induction T; intros; inv wfT... 
Qed.

Lemma wfThreads_frame_ge :
  forall P Gamma frame frame' T t,
    wfThreads P Gamma frame T t ->
    frame <= frame' ->
    wfThreads P Gamma frame' T t.
Proof with eauto using frameFresh_ge.
  introv wfT Hle.
  induction wfT...
Qed.

(*
----------------
wfConfiguration
----------------
*)

Hint Constructors wfConfiguration.

Lemma wfConfiguration_substitution : 
  forall P Gamma H V n Ls e e' t,
    freeVars e' = nil ->
    frameFresh n e' ->
    P; Gamma |- e' \in t ->
    wfLocking H (T_Thread Ls e') ->
    wfConfiguration P Gamma (H, V, n, T_Thread Ls e) t ->
    wfConfiguration P Gamma (H, V, n, T_Thread Ls e') t.
Proof with eauto.
  introv Hfree Hfresh hasType wfL wfCfg. 
  inverts wfCfg... 
Qed.

(*
Lemma wfConfiguration_wfEnv : 
  forall P t' Gamma cfg t,
    wfProgram P t' -> 
    wfConfiguration P Gamma cfg t ->
    wfEnv P Gamma.
Proof with auto.
  introv wfP wfCfg.
  inverts wfCfg as wfH...
  inv wfH...
Qed.
*)

(*
Lemma wfConfiguration_invariance : 
  forall P t' Gamma Gamma' cfg t,
    wfProgram P t' ->
    (forall x, Gamma x = Gamma' x) ->
    wfConfiguration P Gamma cfg t ->
    wfConfiguration P Gamma' cfg t.
Proof with eauto using 
                 wfHeap_invariance,
                 wfVars_invariance,
                 wfThreads_invariance.
  introv wfP Hequiv wfCfg. 
  inverts wfCfg as wfH wfV wfT. 
  assert (wfEnv P Gamma) by (inv wfH; eauto).
  assert (wfEnv P Gamma') by (eauto using wfEnv_equiv)...
Qed.
*)

Lemma wfConfiguration_heapExtend :
  forall P t' Gamma H V n T t c F RL,
    wfProgram P t' ->
    wfConfiguration P Gamma (H, V, n, T) t ->
    wfType P (TClass c) ->
    wfFields P Gamma c F ->
    wfRegionLocks P c RL ->
    wfConfiguration P (extend Gamma (env_loc (length H)) (TClass c))
                    ((heapExtend H (c, F, RL)), V, n, T) t.
Proof with eauto 6 using 
                 wfHeap_extend,
                 wfVars_heapExtend,
                 wfThreads_heapExtend,
                 wfLocking_heapExtend with env.
  introv wfP wfCfg wfTy wfF wfRL.
  inverts wfCfg.
  assert(fresh Gamma (env_loc (length H)))
    by eauto using wfHeap_fresh, heapLookup_ge...  
Qed.

Lemma wfConfiguration_heapUpdate :
  forall P t' Gamma H V n T t l c F RL RL' F',
    wfProgram P t' ->
    wfConfiguration P Gamma (H, V, n, T) t ->
    heapLookup H l = Some (c, F, RL) ->
    wfFields P Gamma c F' ->
    wfRegionLocks P c RL' ->
    (forall r, In (l, r) (heldLocks T) -> RL' r = Some LLocked) ->
    (forall r, In (l, r) (t_rlocks T) ->
               exists n, RL' r = Some (LReaders n) /\
                         length (filter (lock_eq (l, r)) (t_rlocks T)) <= n) ->
    wfConfiguration P Gamma 
                    ((heapUpdate H l (c, F', RL')), V, n, T) t.
Proof with eauto using 
                 wfHeap_update,
                 wfLocking_heapUpdate.
  introv wfP wfCfg HLookup wfF' wfRL' HRl HWl.
  inverts wfCfg...
Qed.

