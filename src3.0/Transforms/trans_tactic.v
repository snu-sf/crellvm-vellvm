Require Import vellvm.

Ltac wfCall_inv :=
match goal with
| Heq3 : exists _,
           exists _,
             exists _,
               ?B = (_, stmts_intro _ _ _),
  HBinF1 : blockInFdefB ?B ?F = true,
  HwfCall : OpsemPP.wf_call
              {|
              Opsem.CurFunction := ?F;
              Opsem.CurBB := ?B;
              Opsem.CurCmds := nil;
              Opsem.Terminator := _;
              Opsem.Locals := _;
              Opsem.Allocas := _ |}
              ({|
               Opsem.CurFunction := _;
               Opsem.CurBB := _;
               Opsem.CurCmds := ?c' :: _;
               Opsem.Terminator := _;
               Opsem.Locals := _;
               Opsem.Allocas := _ |}  :: _) |- _ =>
  let cs3 := fresh "cs3" in
  destruct Heq3 as [l3 [ps3 [cs3 Heq3]]]; subst;
  assert (HBinF1':=HBinF1);
  apply HwfCall in HBinF1';
  destruct_cmd c'; tinv HBinF1'; clear HBinF1'
end.

Ltac simpl_s_genInitState :=
  match goal with
  | Hinit: Opsem.s_genInitState _ _ _ _ = _ |- _ =>
    unfold Opsem.s_genInitState in Hinit;
    inv_mbind'
  end;
  match goal with
  | m : module |- _ =>
    destruct m as [CurLayouts CurNamedts CurProducts];
    inv_mbind'
  end;
  match goal with
  | H: ret (_, ?s0) = getEntryBlock ?f |- _ =>
    destruct s0 as [ps0 cs0 tmn0];
    destruct f as [[f t i0 a v] b];
    inv_mbind'
  end;
  try repeat match goal with
  | H: ret _ = ret _ |- _ => inv H
  end;
  symmetry_ctx.

Ltac unfold_blk2GV := unfold blk2GV, ptr2GV, val2GV.

(* go to *)
Lemma getTypeSizeInBits_and_Alignment__getTypeStoreSize: forall TD t sz al,
  getTypeSizeInBits_and_Alignment TD true t = Some (sz, al) ->
  getTypeStoreSize TD t = Some (nat_of_Z (ZRdiv (Z_of_nat sz) 8)).
Proof.
  unfold getTypeStoreSize, getTypeSizeInBits.
  intros. fill_ctxhole. auto.
Qed.

(* go to *)
Ltac inTmnOp_isnt_stuck v H3 Hwfcfg1 Hwfpp1 :=
match type of Hwfpp1 with
| OpsemPP.wf_State 
              {|
              OpsemAux.CurSystem := _;
              OpsemAux.CurTargetData := ?td;
              OpsemAux.CurProducts := _;
              OpsemAux.Globals := ?gl;
              OpsemAux.FunTable := _ |}
    {| Opsem.ECS := {| Opsem.CurFunction := _;
                       Opsem.CurBB := ?b;
                       Opsem.CurCmds := nil;
                       Opsem.Terminator := ?tmn;
                       Opsem.Locals := ?lc;
                       Opsem.Allocas := _
                     |} :: _;
       Opsem.Mem := _ |}  =>
    let G := fresh "G" in
    let gvs := fresh "gvs" in
    assert (exists gvs, Opsem.getOperandValue td v lc gl = Some gvs) as G; 
      try solve [
        destruct H3 as [l5 [ps2 [cs21 H3]]]; subst;
        destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
        destruct Hwfpp1 as 
          [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [Hinscope1 _]]]]] _]];
        inv_mbind;
        eapply OpsemPP.getOperandValue_inTmnOperans_isnt_stuck; eauto 1;
          simpl; auto
      ];
    destruct G as [gvs G]
end.

(* copied from SB *)
Lemma cmds_at_block_tail_next : forall B c cs tmn2,
  (exists l1:l, exists ps1, exists cs11, B =
    (l1, stmts_intro ps1 (cs11 ++ c :: cs) tmn2)) ->
  exists l1, exists ps1, exists cs11, B = (l1, stmts_intro ps1 (cs11 ++ cs) tmn2).
Proof.
  intros.
  destruct H as [l1 [ps1 [cs11 H]]]; subst.
  exists l1. exists ps1. exists (cs11 ++ [c]). simpl_env. auto.
Qed.

Ltac repeat_solve :=
  repeat (split; eauto 2 using cmds_at_block_tail_next).


