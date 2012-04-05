Require Import vellvm.
Require Import opsem_props.
Require Import memory_sim.
Require Import memory_props.
Require Import trans_tactic.

Definition undefined_program (P:system) (main:id) (VarArgs:list (GVsT DGVs)) :=
  exists tr, exists St, Opsem.s_goeswrong P main VarArgs tr St.

Definition defined_program (P:system) (main:id) (VarArgs:list (GVsT DGVs)) :=
  ~ (undefined_program P main VarArgs).

Inductive program_sim (P1 P2:system) (main:id) (VarArgs:list (GVsT DGVs)) :
   Prop :=
| program_sim_intro: 
    (forall tr r, 
      Opsem.s_converges P1 main VarArgs tr r -> 
      Opsem.s_converges P2 main VarArgs tr r) -> 
    (forall Tr, 
      Opsem.s_diverges P1 main VarArgs Tr -> 
      Opsem.s_diverges P2 main VarArgs Tr) ->
    (forall tr1 St1, 
      Opsem.s_goeswrong P1 main VarArgs tr1 St1 -> 
      undefined_program P2 main VarArgs) -> 
    defined_program P2 main VarArgs ->
    program_sim P1 P2 main VarArgs
.

Lemma program_sim_refl: forall P main VarArgs 
  (Hok: defined_program P main VarArgs), program_sim P P main VarArgs.
Proof.
  intros. apply program_sim_intro; intros; eauto.
    exists tr1. exists St1. auto.
Qed.

Lemma program_sim_trans: forall P1 P2 P3 main VarArgs
  (Hsim1: program_sim P1 P2 main VarArgs) 
  (Hsim2: program_sim P2 P3 main VarArgs),
  program_sim P1 P3 main VarArgs.
Proof.
  intros. inv Hsim1. inv Hsim2. constructor; intros; eauto.
    apply H1 in H7. unfold defined_program in H2. tauto. 
Qed.

Lemma program_sim__preserves__defined_program: forall P1 P2 main VarArgs
  (Hok: defined_program P2 main VarArgs) (Hsim: program_sim P1 P2 main VarArgs),
  defined_program P1 main VarArgs.
Proof.
  intros. inv Hsim. intro Hbad. 
  destruct Hbad as [tr1 [St1 Hbad]]. unfold defined_program in H2. 
  apply H1 in Hbad. tauto.
Qed.

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
  @OpsemPP.wf_params DGVs
    (OpsemAux.initTargetData CurLayouts CurNamedts Mem.empty)
    VarArgs (args_to_params a).

Lemma s_genInitState__opsem_wf: forall S main VarArgs cfg IS
  (HwfS : wf_system S)
  (Hinit : @Opsem.s_genInitState DGVs S main VarArgs Mem.empty = ret (cfg, IS)),
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
  split; auto.
    intro J. congruence.
  split.
    eapply main_wf_params in HeqR0; eauto.
    eapply OpsemPP.wf_ExecutionContext__at_beginning_of_function; eauto.
    simpl.
    split; auto.
      intros. destruct b0 as [? ? ? t0]. destruct t0; auto.
Qed.

Lemma s_genInitState__targedata: forall los nts Ps main VarArgs cfg1 IS1,
  @Opsem.s_genInitState DGVs
            [module_intro los nts Ps] main VarArgs Mem.empty = ret (cfg1, IS1) ->
  (los,nts) = OpsemAux.CurTargetData cfg1.
Proof.
  intros.
  simpl_s_genInitState.
  destruct_if. auto.
Qed.

Axiom genGlobalAndInitMem__wf_globals_Mem: forall 
  (initGlobal initFunTable : GVMap) (initMem : mem)
  (CurLayouts : layouts) (CurNamedts : namedts)
  (CurProducts : list product) (la : args) (lc : Opsem.GVsMap)
  (VarArgs : list (GVsT DGVs)),
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
     lookupAL (GVsT DGVs) lc i0 = ret gv ->
     genericvalues_inject.gv_inject 
       (MemProps.inject_init (Mem.nextblock initMem - 1)) gv gv) /\
  MoreMem.mem_inj inject_id initMem initMem /\
  OpsemAux.ftable_simulation inject_id initFunTable initFunTable.

Lemma s_isFinialState__stuck: forall St1 St2 cfg tr
  (Hfinal : @Opsem.s_isFinialState DGVs cfg St1 <> None),
  ~ Opsem.sInsn cfg St1 St2 tr.
Proof.
  intros.
  destruct St1; simpl in Hfinal.
  destruct ECS; try congruence.
  destruct e; try congruence.
  destruct CurCmds; try congruence.
  intro J.
  destruct Terminator; try congruence; destruct ECS; try congruence; inv J.
Qed.

Ltac uniq_result':=
match goal with
| J1 : ?f = Some _, J2 : None = ?f |- _ => 
    rewrite J1 in J2; congruence
end.

Lemma undefined_state__stuck: forall St1 St2 cfg tr
  (Hundef : @OpsemPP.undefined_state DGVs cfg St1),
  ~ Opsem.sInsn cfg St1 St2 tr.
Proof.
  intros.
  unfold OpsemPP.undefined_state in Hundef.
  destruct cfg; simpl in Hundef.
  destruct St1; simpl in Hundef.
  destruct ECS.
  destruct Hundef as [J | [J | [J | [J | [J | [J | [J | J]]]]]]]; inv J.
  destruct e; tinv Hundef.
  intro Hop.
  destruct CurCmds.
    destruct Hundef as
      [Hundef | [Hundef | [Hundef | [J | [J | [J | [J | J]]]]]]];
      try solve [inversion J].
      destruct Terminator; tinv Hundef.
      destruct ECS; tinv Hundef.
      destruct e; tinv Hundef.
      destruct CurCmds; tinv Hundef.
      inv Hop. uniq_result.

      destruct Terminator; tinv Hundef.
      destruct ECS; tinv Hundef.
      destruct e; tinv Hundef.
      destruct CurCmds; tinv Hundef.
      inv Hop.
      destruct Hundef as [Hundef | Hundef].
        uniq_result.

        remember (getCallerReturnID c) as R.
        destruct R; tinv Hundef.
          congruence.

      destruct CurBB as [? ? ? t]; tinv Hundef.
      destruct t; tinv Hundef.
      destruct Terminator; tinv Hundef.
      inv Hop.

    destruct Hundef as
      [Hundef | [Hundef | [Hundef | [Hundef |
        [Hundef | [Hundef | [Hundef | Hundef]]]]]]];
      tinv Hundef.
      destruct CurBB as [? ? ? t]; tinv Hundef.
      destruct t; tinv Hundef.
      destruct_cmd c; tinv Hundef.
        remember (Opsem.getOperandValue CurTargetData v Locals Globals) as R.
        destruct R; tinv Hundef.
        remember (getTypeAllocSize CurTargetData t) as R.
        destruct R; tinv Hundef.
        destruct Hundef as [gn [Hinst Hundef]].
        remember (malloc CurTargetData Mem s gn a) as R.
        destruct R; tinv Hundef.
        inv Hop. symmetry_ctx. uniq_result. rewrite H21 in HeqR1. congruence.

        remember (Opsem.getOperandValue CurTargetData v Locals Globals) as R.
        destruct R; tinv Hundef.
        remember (getTypeAllocSize CurTargetData t) as R.
        destruct R; tinv Hundef.
        destruct Hundef as [gn [Hinst Hundef]].
        remember (malloc CurTargetData Mem s gn a) as R.
        destruct R; tinv Hundef.
        inv Hop. symmetry_ctx. uniq_result. rewrite H21 in HeqR1. congruence.

      destruct_cmd c; tinv Hundef.
        remember (Opsem.getOperandValue CurTargetData v Locals Globals) as R.
        destruct R; tinv Hundef.
        destruct Hundef as [gn [Hinst Hundef]].
        remember (free CurTargetData Mem gn) as R.
        destruct R; tinv Hundef.
        inv Hop. symmetry_ctx. uniq_result. rewrite H19 in HeqR0. congruence.

      destruct_cmd c; tinv Hundef.
        remember (Opsem.getOperandValue CurTargetData v Locals Globals) as R.
        destruct R; tinv Hundef.
        destruct Hundef as [gn [Hinst Hundef]].
        remember (mload CurTargetData Mem gn t a) as R.
        destruct R; tinv Hundef.
        inv Hop. symmetry_ctx. uniq_result. rewrite H20 in HeqR0. congruence.

      destruct_cmd c; tinv Hundef.
        remember (Opsem.getOperandValue CurTargetData v Locals Globals) as R.
        destruct R; tinv Hundef.
        remember (Opsem.getOperandValue CurTargetData v0 Locals Globals) as R.
        destruct R; tinv Hundef.
        destruct Hundef as [gn [mgv [Hinst1 [Hinst2 Hundef]]]].
        remember (mstore CurTargetData Mem mgv t gn a) as R.
        destruct R; tinv Hundef.
        inv Hop. symmetry_ctx. uniq_result. rewrite H23 in HeqR1. congruence.

      destruct_cmd c; tinv Hundef.
        remember (Opsem.getOperandValue CurTargetData v Locals Globals) as R.
        destruct R; tinv Hundef.
        destruct Hundef as [fptr [Hinst Hundef]].
        remember (OpsemAux.lookupFdefViaPtr CurProducts FunTable fptr) as R.
        destruct R; tinv Hundef.
        remember (OpsemAux.lookupExFdecViaPtr CurProducts FunTable fptr) as R.
        destruct R as [f|].
          destruct f as [[fnattrs5 typ5 id5 args5 varg5] bs].
          remember (Opsem.params2GVs CurTargetData p Locals Globals) as R.
          destruct R; tinv Hundef.
          destruct Hundef as [gvs [Hinst' Hundef]].
          match goal with
          | _: match ?ef with
               | Some _ => _
               | None => _
               end |- _ => remember ef as R
          end.
          destruct R as [[[o ?]]|].
            remember (Opsem.exCallUpdateLocals CurTargetData t0 n i0 o Locals)
              as R.
            destruct R; tinv Hundef.
            inv Hop.
              symmetry_ctx. uniq_result. uniq_result'.
              symmetry_ctx. uniq_result. uniq_result'. 

            inv Hop.
              symmetry_ctx. uniq_result. uniq_result'.
              symmetry_ctx. uniq_result. uniq_result'.

          inv Hop.
            symmetry_ctx. uniq_result. uniq_result'.
            symmetry_ctx. uniq_result. uniq_result'.
Qed.

Lemma undefined_state__stuck': forall St cfg
  (Hundef : @OpsemPP.undefined_state DGVs cfg St),
  Opsem.stuck_state cfg St.
Proof.
  intros.
  unfold Opsem.stuck_state.
  intro J. destruct J as [St' [tr J]].
  revert J.
  apply undefined_state__stuck; auto.
Qed.

(* go to infra *)
Lemma wf_system__uniqSystem: forall S, wf_system S -> uniqSystem S.
Proof.
  intros.
  destruct H; auto.
Qed.

Lemma uniq_products_simulation: forall Ps1 f Ps2 f0 trans,
  NoDup (getProductsIDs (Ps1 ++ product_fdef f :: Ps2)) ->
  f0 = f ->
  Forall2
    (fun P1 P2 : product =>
     match P1, P2 with
     | product_fdef f1, product_fdef f2 =>
        if fdef_dec f0 f1 then trans f1 = f2 else f1 = f2
     | _, _ => P1 = P2
    end)
    (Ps1 ++ product_fdef f :: Ps2)
    (Ps1 ++ product_fdef (trans f) :: Ps2).
Proof.
  intros. subst.
  generalize dependent Ps1.
  induction Ps1; simpl; intros.
    constructor.
      destruct (fdef_dec f f); try congruence; auto.

      inv H.
      induction Ps2; auto.
        inv H3.
        constructor.
          destruct a; auto.      
            destruct (fdef_dec f f0); subst; auto.
             contradict H2.
             simpl. auto.
          apply IHPs2; auto.
            intro J. apply H2. simpl. auto.

    inv H.
    constructor; auto.
      destruct a; auto.      
      destruct (fdef_dec f f0); subst; auto.
        contradict H2.
        rewrite getProductsIDs_app. simpl.
        apply In_middle.
Qed.

Lemma stuck__undefined_state: forall St cfg
  (HwfCfg: OpsemPP.wf_Config cfg) (Hst: OpsemPP.wf_State cfg St) 
  (Hstck: @Opsem.stuck_state DGVs cfg St)
  (Hnfinal: @Opsem.s_isFinialState DGVs cfg St = None),
  @OpsemPP.undefined_state DGVs cfg St.
Proof.
  intros.
  apply OpsemPP.progress in Hst; auto.
  destruct Hst as [Hfinal | [Hstep | Hundef]]; try tauto.
  unfold Opsem.stuck_state in Hstck. tauto.
Qed.

Definition sop_goeswrong cfg IS : Prop :=
exists FS, exists tr, 
  @Opsem.sop_star DGVs cfg IS FS tr /\ Opsem.stuck_state cfg FS /\ 
  Opsem.s_isFinialState cfg FS = None.

Lemma sop_goeswrong__step: forall cfg St St' tr
  (Hok: ~ sop_goeswrong cfg St) (Hop: Opsem.sInsn cfg St St' tr),
  ~ sop_goeswrong cfg St'.
Proof.
  intros.
  intro J.
  destruct J as [FS [tr' [J1 [J2 J3]]]].
  apply Hok.
  exists FS. exists (tr ** tr'). 
  split; eauto. 
Qed.

Lemma sop_goeswrong__star: forall cfg St St' tr
  (Hop: Opsem.sop_star cfg St St' tr) (Hok: ~ sop_goeswrong cfg St) ,
  ~ sop_goeswrong cfg St'.
Proof.
  induction 1; auto.
  intro J.
  apply IHHop.
  eapply sop_goeswrong__step; eauto.
Qed.

Lemma defined_program__doesnt__go_wrong: forall S main VarArgs cfg IS,
  defined_program S main VarArgs ->
  Opsem.s_genInitState S main VarArgs Mem.empty = Some (cfg, IS) ->
  ~ sop_goeswrong cfg IS.
Proof.
  unfold defined_program, undefined_program.
  intros. intro J.
  apply H. destruct J as [FS [tr [J1 [J2 J3]]]].
  exists tr. exists FS. econstructor; eauto.
Qed.

Require Import mem2reg.

Lemma elim_stld_cmds_unchanged: forall f' dones' f cs0 pid dones,
  (f', false, dones') = elim_stld_cmds f cs0 pid dones ->
  f' = f.
Proof.
  intros.
  unfold elim_stld_cmds in H.
  destruct (find_init_stld cs0 pid dones) as [[[[]]|[]]|].
    destruct (find_next_stld c pid) as [[|[]]|]; inv H.
    destruct (find_next_stld c pid) as [[|[]]|]; inv H.
    inv H; auto.
Qed.

