Require Import vellvm.
Require Import opsem_props.
Require Import memory_sim.
Require Import memory_props.

(* A program that goes wrong is undefined. *)
Definition undefined_program (P:system) (main:id) (VarArgs:list GenericValue) :=
  exists tr, exists St, Opsem.s_goeswrong P main VarArgs tr St.

(* Otherwise a program is undefined. *)
Definition defined_program (P:system) (main:id) (VarArgs:list GenericValue) :=
  ~ (undefined_program P main VarArgs).

(* Equivalence of values. *)
Inductive val_result_match: val -> val -> Prop :=
  | val_result_match_int:
      forall wz i, val_result_match (Vint wz i) (Vint wz i)
  | val_result_match_float:
      forall f, val_result_match (Vfloat f) (Vfloat f)
  | val_result_match_single:
      forall f, val_result_match (Vsingle f) (Vsingle f)
  | val_result_match_ptr:
      forall b1 ofs1 b2 ofs2, 
      val_result_match (Vptr b1 ofs1) (Vptr b2 ofs2)
  | val_result_match_inttoptr:
      forall i1 i2, val_result_match (Vinttoptr i1) (Vinttoptr i2)
  | val_result_match_undef: val_result_match Vundef Vundef
.

(***********************************************************************)
(* Equivalence of generic values. *)
Definition result_match (gv1 gv2: GenericValue) : Prop :=
List.Forall2 (fun vm1 vm2 =>
              let '(v1,m1):=vm1 in
              let '(v2,m2):=vm2 in
              val_result_match v1 v2 /\ m1 = m2) gv1 gv2.

(* Following the CompCert project, we define program refinement in terms of 
   programs’ external behaviors (which include program traces of input-output 
   events, whether a program is stuck, whether a program terminates, and the 
   returned value if a program terminates): a transformed program refines its 
   original program if the behaviors of the well-defined original program include 
   all the behaviors of the transformed program. *)
Inductive program_sim (P1 P2:system) (main:id) (VarArgs:list GenericValue) :
   Prop :=
| program_sim_intro: 
    (forall tr r1, 
      Opsem.s_converges P1 main VarArgs tr r1 -> 
      exists r2, 
        Opsem.s_converges P2 main VarArgs tr r2 /\ result_match r1 r2) -> 
    (forall Tr, 
      Opsem.s_diverges P1 main VarArgs Tr -> 
      Opsem.s_diverges P2 main VarArgs Tr) ->
    (forall tr St1, 
      Opsem.s_goeswrong P1 main VarArgs tr St1 -> 
      exists St2, Opsem.s_goeswrong P2 main VarArgs tr St2) -> 
    defined_program P2 main VarArgs ->
    program_sim P1 P2 main VarArgs
.

(***********************************************************************)
(* Properties of result_match *)
Lemma val_result_match_relf: forall v, val_result_match v v.
Proof.
  induction v; constructor; auto.
Qed.

Lemma result_match_relf: forall gv, result_match gv gv.
Proof.
  unfold result_match.
  induction gv as [|[]]; auto.
    constructor; auto using val_result_match_relf.
Qed.

Lemma val_result_match_symm: forall v1 v2
  (Hinj: val_result_match v1 v2), val_result_match v2 v1.
Proof.
  intros. inv Hinj; constructor; auto.
Qed.

Lemma result_match_symm: forall gv1 gv2
  (Hinj: result_match gv1 gv2), result_match gv2 gv1.
Proof.
  unfold result_match.
  intros. 
  induction Hinj; auto.
    constructor; auto.
      destruct y. destruct x.
      destruct H.
      split.
        apply val_result_match_symm; auto.
        congruence.
Qed.

(* copied from events.v *)
Ltac drewrite_int :=
  match goal with
  | H: existT _ ?wz ?i = _ |- context [?C ?wz ?i] =>
      let R := fresh "R" in
      remember (C wz i) as R;
      match goal with
      | HeqR: _ = ?C ?wz ?i |- _ =>
        dependent rewrite H in HeqR; subst R
      end
  end.

Lemma val_result_match_trans: forall v1 v2 v3
  (Hm: val_result_match v1 v2) (Hm': val_result_match v2 v3),
  val_result_match v1 v3.
Proof.
  destruct 1; intros; inv Hm'; try constructor.
      drewrite_int. constructor.
Qed.

Lemma result_match_trans: forall gv1 gv2
  (Hm: result_match gv1 gv2) gv3 (Hm': result_match gv2 gv3),
  result_match gv1 gv3.
Proof.
  unfold result_match.
  induction 1; intros; inv Hm'; try constructor; auto.
    destruct x. destruct y. destruct y0.
    destruct H. destruct H2.
    split.
      eapply val_result_match_trans; eauto.
      congruence.
Qed.

(***********************************************************************)
(* Properties of undefined programs *)
Lemma s_goeswrong__undefined_program: forall P main VarArgs tr St
  (Hgw: Opsem.s_goeswrong P main VarArgs tr St)
  (Hdef: defined_program P main VarArgs),
  False.
Proof.
  unfold defined_program.
  intros.
  contradict Hdef.
  exists tr. exists St. auto.
Qed.

Lemma s_isFinialState__stuck: forall St1 St2 cfg tr
  (Hfinal : Opsem.s_isFinialState cfg St1 <> None),
  ~ Opsem.sInsn cfg St1 St2 tr.
Proof.
  intros.
  destruct St1; simpl in Hfinal.
  (* destruct ECS; try congruence. *)
  destruct EC; try congruence.
  destruct CurCmds; try congruence.
  intro J.
  destruct Terminator; try congruence; destruct ECS; try congruence; inv J.
Qed.

Lemma stuck__undefined_state: forall St cfg
  (HwfCfg: OpsemPP.wf_Config cfg) (Hst: OpsemPP.wf_State cfg St) 
  (Hstck: Opsem.stuck_state cfg St)
  (Hnfinal: Opsem.s_isFinialState cfg St = None),
  OpsemPP.undefined_state cfg St.
Proof.
  intros.
  apply OpsemPP.progress in Hst; auto.
  destruct Hst as [Hfinal | [Hstep | Hundef]]; try tauto.
  unfold Opsem.stuck_state in Hstck. tauto.
Qed.

Definition sop_goeswrong cfg IS : Prop :=
exists FS, exists tr, 
  Opsem.sop_star cfg IS FS tr /\ Opsem.stuck_state cfg FS /\ 
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

Lemma sop_goeswrong__plus: forall cfg St St' tr
  (Hplus: Opsem.sop_plus cfg St St' tr) (Hok: ~ sop_goeswrong cfg St),
  ~ sop_goeswrong cfg St'.
Proof.
  intros.
  apply OpsemProps.sop_plus__implies__sop_star in Hplus.
  eapply sop_goeswrong__star; eauto.
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

Lemma nonfinal_stuck_state_goes_wrong: forall Cfg St,
  Opsem.stuck_state Cfg St ->
  Opsem.s_isFinialState Cfg St = None -> sop_goeswrong Cfg St.
Proof.
  intros.
  exists St. exists E0. split; auto.
Qed.

(***********************************************************************)
(* Properties of program sim *)
Lemma program_sim_refl: forall P main VarArgs 
  (Hok: defined_program P main VarArgs), program_sim P P main VarArgs.
Proof.
  intros.
  apply program_sim_intro; intros; eauto using result_match_relf.
Qed.

Lemma program_sim_trans: forall P1 P2 P3 main VarArgs
  (Hsim1: program_sim P1 P2 main VarArgs) 
  (Hsim2: program_sim P2 P3 main VarArgs),
  program_sim P1 P3 main VarArgs.
Proof.
  intros. inv Hsim1. inv Hsim2. 
  constructor; intros; eauto.
    apply H in H7. destruct H7 as [r2 [J1 J2]].
    apply H3 in J1. destruct J1 as [r3 [J3 J4]].
    exists r3. split; eauto using result_match_trans.

    apply H1 in H7. destruct H7 as [St2 H7].
    apply s_goeswrong__undefined_program in H7; auto.
    tauto.
Qed.

Lemma program_sim__preserves__defined_program: forall P1 P2 main VarArgs
  (Hok: defined_program P2 main VarArgs) (Hsim: program_sim P1 P2 main VarArgs),
  defined_program P1 main VarArgs.
Proof.
  intros. inv Hsim. intro Hbad. 
  destruct Hbad as [tr1 [St1 Hbad]]. unfold defined_program in H2. 
  apply H1 in Hbad. 
  destruct Hbad as [St2 Hgw].
  contradict H2. exists tr1. exists St2. auto.
Qed.

Lemma program_sim_wfS_trans: forall (P1 P2 P3 : system) (main : id)
  (VarArgs : list GenericValue) (HwfS: wf_system P3) 
  (Hok: defined_program P3 main VarArgs),
  (wf_system P2 -> 
   defined_program P2 main VarArgs ->
   program_sim P1 P2 main VarArgs /\ wf_system P1 /\ 
   defined_program P1 main VarArgs) ->
  (wf_system P3 -> 
   defined_program P3 main VarArgs ->
   program_sim P2 P3 main VarArgs /\ wf_system P2 /\
   defined_program P2 main VarArgs) ->
  program_sim P1 P3 main VarArgs /\ wf_system P1 /\
  defined_program P1 main VarArgs.
Proof.
  intros.
  destruct H0 as [Hsim2 [Hwf2 Hok2]]; auto.
  destruct H as [Hsim1 [Hwf1 Hok1]]; auto.
  split; auto.
  eapply program_sim_trans; eauto.
Qed.

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

Lemma s_genInitState__targedata: forall los nts Ps main VarArgs cfg1 IS1,
  Opsem.s_genInitState
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

(***********************************************************************)
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
            destruct (fdef_dec f fdef5); subst; auto.
             contradict H2.
             simpl. auto.
          apply IHPs2; auto.
            intro J. apply H2. simpl. auto.

    inv H.
    constructor; auto.
      destruct a; auto.      
      destruct (fdef_dec f fdef5); subst; auto.
        contradict H2.
        rewrite getProductsIDs_app. simpl.
        apply In_middle.
Qed.
