Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa/compcert".
Add LoadPath "../ssa".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../TV".
Require Import ssa_def.
Require Import ssa_lib.
Require Import List.
Require Export targetdata.
Require Import monad.
Require Import Arith.
Require Import Metatheory.
Require Import genericvalues.
Require Import trace.
Require Import ssa_props.
Require Import alist.
Require Import ssa_dynamic.
Require Import ndopsem.
Require Import sb_ds_def.
Require Import sb_ns_def.

Export LLVMsyntax.
Export LLVMlib.

Definition sbEC_simulates_EC (sbEC:SBnsop.ExecutionContext) 
  (EC:NDopsem.ExecutionContext) : Prop :=
  match (sbEC, EC) with
  | (SBnsop.mkEC f1 b1 cs1 tmn1 lc1 rm1 als1, 
     NDopsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       f1 = f2 /\ b1 = b2 /\ cs1 = cs2 /\ tmn1 = tmn2 /\ lc1 = lc2 /\
       als1 = als2
  end.

Fixpoint sbECs_simulate_ECs (sbECs:SBnsop.ECStack) (ECs:NDopsem.ECStack) 
  : Prop :=
  match sbECs, ECs with
  | nil, nil => True
  | sbEC::sbECs', EC::ECs' => 
      sbEC_simulates_EC sbEC EC /\ sbECs_simulate_ECs sbECs' ECs'
  | _, _ => False
  end.

Definition sbState_simulates_State (sbSt:SBnsop.State) (St:NDopsem.State) 
  : Prop :=
  match (sbSt, St) with
  | (SBnsop.mkState S1 TD1 Ps1 ECs1 gl1 fs1 M1 MM1,
     NDopsem.mkState S2 TD2 Ps2 ECs2 gl2 fs2 M2) =>
      S1 = S2 /\ TD1 = TD2 /\ Ps1 = Ps2 /\ sbECs_simulate_ECs ECs1 ECs2 /\
      gl1 = gl2 /\ fs1 = fs2 /\ M1 = M2
  end.

Lemma returnUpdateLocals_sim : forall TD' c' rt Result lc1' lc2' rm rm' gl' 
    lc'' rm'', 
  SBnsop.returnUpdateLocals TD' c' rt Result lc1' lc2' rm rm' gl' = 
    ret (lc'', rm'') ->
  returnUpdateLocals TD' c' Result lc1' lc2' gl' = ret lc''.
Proof.
  intros.  
  unfold SBnsop.returnUpdateLocals, SBnsop.returnResult in H.
  unfold returnUpdateLocals.
  destruct (getOperandValue TD' Result lc1' gl'); 
    try solve [inversion H; auto].
  destruct (isPointerTypB rt); try solve [inversion H; auto].
    destruct (SBopsem.get_reg_metadata TD' gl' rm Result) as [[md ?]|]; 
      try solve [inversion H; auto].
    destruct c'; try solve [inversion H; auto].
    destruct n; try solve [inversion H; auto].
    unfold SBnsop.prop_reg_metadata in H.  
    destruct t; try solve [inversion H; auto].
    destruct t; try solve [inversion H; auto].

    destruct c'; try solve [inversion H; auto].
    destruct n; try solve [inversion H; auto].
    unfold SBnsop.prop_reg_metadata in H.  
    destruct t; try solve [inversion H; auto].
    destruct t; try solve [inversion H; auto].
Qed.

Lemma exCallUpdateLocals_sim : forall TD ft noret rid oResult lc rm lc'' rm'', 
  SBnsop.exCallUpdateLocals TD ft noret rid oResult lc rm = ret (lc'', rm'') ->
  exCallUpdateLocals TD ft noret rid oResult lc = ret lc''.
Proof.
  intros.  
  unfold SBnsop.exCallUpdateLocals in H.
  unfold exCallUpdateLocals.
  destruct noret0; try solve [inversion H; auto].
  destruct oResult; try solve [inversion H; auto].
  destruct ft; try solve [inversion H; auto].
  destruct (fit_gv TD ft g); tinv H.
  destruct ft; inversion H; auto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_sim : forall ps TD' b1' gl' lc1'
    rm l1,
  SBnsop.getIncomingValuesForBlockFromPHINodes TD' ps b1' gl' lc1' rm =
    Some l1 ->
  exists l2, exists l3, 
    getIncomingValuesForBlockFromPHINodes TD' ps b1' gl' lc1' = Some l2 /\ 
    split l1 = (l2, l3).
Proof.
  induction ps; simpl; intros.
    inversion H; subst.
    exists nil. exists nil. eauto.

    destruct a. 
    destruct (getValueViaBlockFromValuels l0 b1'); try solve [inversion H].
    remember (getOperandValue TD' v lc1' gl') as R0.
    destruct R0; try solve [inversion H].
    remember (SBnsop.getIncomingValuesForBlockFromPHINodes TD' ps b1' gl'
          lc1' rm) as R.
    destruct R; try solve [inversion H].
    symmetry in HeqR.
    apply IHps in HeqR.
    destruct HeqR as [l3 [l4 [J1 J2]]].
    rewrite J1.
    destruct (isPointerTypB t); inversion H; subst; clear H.
      destruct v.
        simpl in H1.
        destruct (lookupAL SBopsem.metadata rm i1); inversion H1; subst.
          simpl. rewrite J2. eauto.

        destruct (SBopsem.get_reg_metadata TD' gl' rm (value_const c)) as [md|]; 
          inversion H1; subst; simpl; eauto.
          rewrite J2. eauto.

      simpl. rewrite J2.
      destruct v; simpl in *; eauto.
Qed.

Lemma updateValuesForNewBlock_sim : forall l0 lc1' rm lc' rm' l2 l3,
  SBnsop.updateValuesForNewBlock l0 lc1' rm = (lc', rm') ->
  split l0 = (l2, l3) ->
  updateValuesForNewBlock l2 lc1' = lc'.
Proof.
  induction l0; simpl; intros.   
    inversion H0; subst.
    inversion H; subst.
    simpl; auto.

    destruct a. destruct p. 
    remember (SBnsop.updateValuesForNewBlock l0 lc1' rm) as R.
    destruct R.
    remember (split l0) as R1.
    destruct R1. inversion H0; subst.
    simpl. unfold SBnsop.prop_reg_metadata in H.
    destruct o.
      inversion H; subst.
      erewrite IHl0 with (lc1':=lc1'); eauto.

      inversion H; subst.
      erewrite IHl0 with (lc1':=lc1'); eauto.
Qed.

Lemma switchToNewBasicBlock_sim : forall TD' b' b1' gl' lc1' rm lc' rm',
  SBnsop.switchToNewBasicBlock TD' b' b1' gl' lc1' rm = ret (lc', rm') ->
  switchToNewBasicBlock TD' b' b1' gl' lc1' = ret lc'.
Proof.
  intros.
  unfold SBnsop.switchToNewBasicBlock in H.
  unfold switchToNewBasicBlock.
  remember (SBnsop.getIncomingValuesForBlockFromPHINodes TD'
    (getPHINodesFromBlock b') b1' gl' lc1' rm) as R.
  destruct R; try solve [inversion H].
  symmetry in HeqR.
  apply getIncomingValuesForBlockFromPHINodes_sim in HeqR.
  destruct HeqR as [l2 [l3 [J1 J2]]].
  rewrite J1.
  inversion H; subst.
  eapply updateValuesForNewBlock_sim in H1; eauto.
  rewrite H1. auto.
Qed.

Lemma params2GVs_sim : forall lp gl' TD' lc1' rm ogvs,
  SBnsop.params2GVs TD' lp lc1' gl' rm = ret ogvs ->
  exists gvs, exists l2, params2GVs TD' lp lc1' gl' = ret gvs /\
    split ogvs = (gvs, l2).
Proof.
  induction lp; simpl; intros.
    inversion H; subst. 
    exists nil. exists nil. auto.

    destruct a.
    destruct (getOperandValue TD' v lc1' gl'); try solve [inversion H; subst].
    remember (SBnsop.params2GVs TD' lp lc1' gl' rm) as R.
    destruct R; try solve [inversion H].
    symmetry in HeqR.
    apply IHlp in HeqR; auto.      
    destruct HeqR as [gvs [l2 [J1 J2]]].
    destruct (isPointerTypB t); inversion H; subst; 
      simpl; rewrite J2; rewrite J1; eauto.
Qed.

Lemma initializeFrameValues_sim : forall TD la rm ogvs lc lc' rm' gvs l2,
  SBnsop._initializeFrameValues TD la ogvs lc rm = Some (lc', rm') -> 
  split ogvs = (gvs, l2) ->  
  _initializeFrameValues TD la gvs lc = Some lc'.
Proof.
  induction la; simpl; intros.
    inversion H; subst; auto.

    destruct a. destruct p.
    destruct ogvs.
      simpl in H0. inversion H0; subst.
      remember (SBnsop._initializeFrameValues TD la nil lc rm) as R.
      destruct R as [[lc1 rm1]|]; tinv H.
      destruct (gundef TD t); tinv H.
      unfold SBnsop.prop_reg_metadata in H.     
      symmetry in HeqR.
      eapply IHla in HeqR; eauto. rewrite HeqR.
      destruct (isPointerTypB t); inversion H; subst; auto.

      destruct p.
      simpl in H0. 
      remember (split ogvs) as R'.
      destruct R'.
      inversion H0; subst.
      remember (SBnsop._initializeFrameValues TD la ogvs lc rm) as R.
      destruct R as [[lc1 rm1]|]; tinv H.
      symmetry in HeqR.
      eapply IHla in HeqR; eauto. rewrite HeqR.
      destruct (isPointerTypB t); try solve [inversion H; subst; auto].
        unfold SBnsop.prop_reg_metadata in H.
        destruct o; try solve [inversion H; subst; auto].
Qed.

Lemma initLocals_params2GVs_sim : forall lp gl' TD' lc1' rm ogvs la lc' rm',
  SBnsop.params2GVs TD' lp lc1' gl' rm = ret ogvs ->
  SBnsop.initLocals TD' la ogvs = ret (lc', rm') -> 
  exists gvs, params2GVs TD' lp lc1' gl' = ret gvs /\
    initLocals TD' la gvs = ret lc'.
Proof.
  unfold SBnsop.initLocals, initLocals.
  intros.
  apply params2GVs_sim in H.
  destruct H as [gvs [l2 [J1 J2]]].
  exists gvs.
  split; eauto using initializeFrameValues_sim.
Qed.

Ltac simpl_sbns_llvmns :=
  match goal with
  | [Hsim : sbState_simulates_State 
           {|
           SBnsop.CurSystem := _;
           SBnsop.CurTargetData := _;
           SBnsop.CurProducts := _;
           SBnsop.ECS := _::_::_;
           SBnsop.Globals := _;
           SBnsop.FunTable := _;
           SBnsop.Mem := _;
           SBnsop.Mmap := _ |} ?St |- _ ] =>
     destruct St as [S' TD' Ps' ECs' gl' fs' M'];
     destruct Hsim as [Hsim1 [Hims2 [Hsim3 [Hsim4 [Hsim5 [Hsim6 Hsim7]]]]]]; 
       subst;
     destruct ECs' as [|[f1' b1' cs1' tmn1' lc1' als1'] ECs']; 
       try solve [inversion Hsim4];
     simpl in Hsim4; destruct Hsim4 as [Hsim41 Hsim42];
     destruct ECs' as [|[f2' b2' cs2' tmn2' lc2' als2'] ECs'];
       try solve [inversion Hsim42];
     destruct Hsim42 as [Hsim42 Hsim43];
     destruct Hsim41 as [J1 [J2 [J3 [J4 [J5 J6]]]]]; subst;
     destruct Hsim42 as [J1 [J2 [J3 [J4 [J5 J6]]]]]; subst
  | [Hsim : sbState_simulates_State 
           {|
           SBnsop.CurSystem := _;
           SBnsop.CurTargetData := _;
           SBnsop.CurProducts := _;
           SBnsop.ECS := _::_;
           SBnsop.Globals := _;
           SBnsop.FunTable := _;
           SBnsop.Mem := _;
           SBnsop.Mmap := _ |} ?St |- _ ] =>
     destruct St as [S' TD' Ps' ECs' gl' fs' M'];
     destruct Hsim as [Hsim1 [Hims2 [Hsim3 [Hsim4 [Hsim5 [Hsim6 Hsim7]]]]]]; 
       subst;
     destruct ECs' as [|[f1' b1' cs1' tmn1' lc1' als1'] ECs']; 
       try solve [inversion Hsim4];
     simpl in Hsim4; destruct Hsim4 as [Hsim41 Hsim42];
     destruct Hsim41 as [J1 [J2 [J3 [J4 [J5 J6]]]]]; subst
  end.

Ltac invert_prop_reg_metadata :=
  match goal with
  | [H : SBnsop.prop_reg_metadata _ _ _ _ _ = (_, _) |- _ ] =>
      inversion H; subst; eauto
  end.

Lemma sbns__llvmns : forall sbSt St sbSt' tr,
  sbState_simulates_State sbSt St ->
  SBnsop.nsInsn sbSt sbSt' tr ->
  exists St', 
    NDopsem.nsInsn St St' tr /\
    sbState_simulates_State sbSt' St'.
Proof.
  intros sbSt St sbSt' tr Hsim HnsInsn.
  generalize dependent St.
  (sb_nsInsn_cases (induction HnsInsn) Case); intros; simpl_sbns_llvmns; 
    try invert_prop_reg_metadata.
  Case "nsReturn". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f2';
                 CurBB := b2';
                 CurCmds := cs';
                 Terminator := tmn2';
                 Locals := lc'';
                 Allocas := als2' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := Mem' |}.
     repeat (split; eauto using returnUpdateLocals_sim).
  Case "nsReturnVoid". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f2';
                 CurBB := b2';
                 CurCmds := cs';
                 Terminator := tmn2';
                 Locals := lc2';
                 Allocas := als2' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := Mem' |}.
     repeat (split; eauto).
  Case "nsBranch". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := block_intro l' ps' cs' tmn';
                 CurCmds := cs';
                 Terminator := tmn';
                 Locals := lc';
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto using switchToNewBasicBlock_sim).
  Case "nsBranch_uncond". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := block_intro l' ps' cs' tmn';
                 CurCmds := cs';
                 Terminator := tmn';
                 Locals := lc';
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto using switchToNewBasicBlock_sim).
  Case "nsBop". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv3;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "nsFBop". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv3;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "nsExtractValue". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv';
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "nsInsertValue". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv'';
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "nsMalloc". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 
                             ($(blk2GV TD' mb) # typ_pointer t$);
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := Mem' |}.
     repeat (split; eauto).
  Case "nsFree". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := lc1';
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := Mem' |}.
     repeat (split; eauto).
  Case "nsAlloca". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 
                             ($(blk2GV TD' mb) # typ_pointer t$);
                 Allocas := mb::als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := Mem' |}.
     repeat (split; eauto).
  Case "nsLoad_nptr". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 ($ gv # t $);
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "nsLoad_ptr". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 ($ gv # t$);
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "nsStore_nptr". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := lc1';
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := Mem' |}.
     repeat (split; eauto).
  Case "nsStore_ptr". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := lc1';
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := Mem' |}.
     repeat (split; eauto).
  Case "nsGEP". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gvp';
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "nsTrunc". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv2;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "nsExt". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv2;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "nsBitcast_nptr". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv2;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "nsBitcast_ptr". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv2;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "nsInttoptr". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv2;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "nsOthercast". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv2;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "nsIcmp". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv3;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "nsFcmp". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv3;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "nsSelect_nptr". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := if isGVZero TD' c
                           then updateAddAL _ lc1' id0 gv2
                           else updateAddAL _ lc1' id0 gv1;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "nsSelect_ptr". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := if isGVZero TD' c
                           then updateAddAL _ lc1' id0 gv2
                           else updateAddAL _ lc1' id0 gv1;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
       destruct (isGVZero TD' c); invert_prop_reg_metadata; auto.
  Case "nsCall". 
     eapply initLocals_params2GVs_sim in H4; eauto.
     destruct H4 as [gvs [J1 J2]].
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := fdef_intro (fheader_intro fa rt fid la va) lb;
                 CurBB := block_intro l' ps' cs' tmn';
                 CurCmds := cs';
                 Terminator := tmn';
                 Locals := lc';
                 Allocas := nil |} ::
              {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := insn_call rid noret0 ca ft fv lp :: cs;
                 Terminator := tmn1';
                 Locals := lc1' ;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "nsExCall". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := lc' ;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := Mem' |}.
     repeat (split; eauto using exCallUpdateLocals_sim).
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)

