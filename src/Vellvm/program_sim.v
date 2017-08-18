Require Import vellvm.
Require Import opsem_props.
Require Import memory_sim.
Require Import memory_props.

(***********************************************************************)
(* Properties of program initialization *)
Axiom genGlobalAndInitMem__wf_global: forall initGlobal initFunTable initMem
  CurLayouts CurNamedts CurProducts S,
  OpsemAux.genGlobalAndInitMem
    (OpsemAux.initTargetData CurLayouts CurNamedts Mem.empty) CurProducts
      nil nil Mem.empty = ret (initGlobal, initFunTable, initMem) ->
  wf_global (CurLayouts, CurNamedts) S initGlobal.

(* OpsemPP.initLocals__wf_lc needs wf_params that is for params.
   At initialization, we only have args...
   Actually OpsemPP.initLocals__wf_lc only needs types in params.
   So, we use the function to create a param from arg.
   We should simplify the proofs of OpsemPP.initLocals__wf_lc, and
   use only types. *)
Definition args_to_params (la: args) : params :=
List.map (fun a0 => let '(t0,attr0,id0) := a0 in (t0,attr0,value_id id0)) la.

Axiom main_wf_params: forall f t i0 a v b S CurLayouts CurNamedts CurProducts
  VarArgs,
  getParentOfFdefFromSystem (fdef_intro (fheader_intro f t i0 a v) b) S =
    ret module_intro CurLayouts CurNamedts CurProducts ->
  OpsemPP.wf_params
    (OpsemAux.initTargetData CurLayouts CurNamedts Mem.empty)
    VarArgs (args_to_params a).

Lemma s_genInitState__opsem_wf: forall S main VarArgs cfg IS
  (HwfS : wf_system S)
  (Hinit : Opsem.s_genInitState S main VarArgs Mem.empty = ret (cfg, IS)),
  OpsemPP.wf_Config cfg /\ OpsemPP.wf_State cfg IS.
Proof.
  intros.
  simpl_s_genInitState.
  assert (HeqR0':=HeqR0).
  apply getParentOfFdefFromSystem__moduleInProductsInSystemB in HeqR0'.
  destruct HeqR0' as [HMinS HinPs].
  assert (wf_namedts S (CurLayouts, CurNamedts)) as Hwfnts.
    inv HwfS.
    eapply wf_modules__wf_module in HMinS; eauto.
    inv HMinS; auto.
  split.
  split; auto.
  split.
    eapply genGlobalAndInitMem__wf_global in HeqR1; eauto.
  split; auto.
  (* split; auto. *)
  (*   intro J. congruence. *)
  split.
    eapply main_wf_params in HeqR0; eauto.
    eapply OpsemPP.wf_ExecutionContext__at_beginning_of_function; eauto.
    simpl.
    split; auto.
      intros. destruct b0 as [? [? ? t0]]. destruct t0; auto.
Qed.

Axiom genGlobalAndInitMem__wf_globals_Mem: forall 
  (initGlobal initFunTable : GVMap) (initMem : mem)
  (CurLayouts : layouts) (CurNamedts : namedts)
  (CurProducts : list product) (la : args) (lc : Opsem.GVsMap)
  (VarArgs : list GenericValue),
  OpsemAux.genGlobalAndInitMem
         (OpsemAux.initTargetData CurLayouts CurNamedts Mem.empty)
         CurProducts nil nil Mem.empty =
    ret (initGlobal, initFunTable, initMem) ->
  Opsem.initLocals
    (OpsemAux.initTargetData CurLayouts CurNamedts Mem.empty) la VarArgs =
    ret lc ->
  MemProps.wf_lc initMem lc /\
  (MemProps.wf_globals (Mem.nextblock initMem - 1) initGlobal /\
   MemProps.wf_Mem (Mem.nextblock initMem - 1)
     (OpsemAux.initTargetData CurLayouts CurNamedts Mem.empty) initMem) /\
  MoreMem.mem_inj (MemProps.inject_init (Mem.nextblock initMem - 1)) 
    initMem initMem /\
  genericvalues_inject.wf_sb_mi (Mem.nextblock initMem - 1) 
    (MemProps.inject_init (Mem.nextblock initMem - 1)) initMem initMem /\
  OpsemAux.ftable_simulation (MemProps.inject_init (Mem.nextblock initMem - 1))
    initFunTable initFunTable /\
  (forall i0 gv, 
     lookupAL GenericValue lc i0 = ret gv ->
     genericvalues_inject.gv_inject 
       (MemProps.inject_init (Mem.nextblock initMem - 1)) gv gv) /\
  MoreMem.mem_inj inject_id initMem initMem /\
  OpsemAux.ftable_simulation inject_id initFunTable initFunTable.

(***********************************************************************)
(* A measure function used by refinement proofs, which is the number of 
   commands to execute. *)
Definition measure (st:Opsem.State) : nat :=
match st with 
| {| Opsem.ECS := {| Opsem.CurCmds := cs |} :: _ |} => List.length cs
| _ => 0%nat
end.
