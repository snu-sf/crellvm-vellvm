Require Import Ensembles.
Require Import syntax.
Require Import infrastructure.
Require Import infrastructure_props.
Require Import analysis.
Require Import typings.
Require Import static.
Require Import List.
Require Import Arith.
Require Import tactics.
Require Import monad.
Require Import events.
Require Import Metatheory.
Require Import genericvalues.
Require Import alist.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import targetdata.
Require Import AST.
Require Import Maps.
Require Import maps_ext.
Require Import opsem.
Require Import vellvm_tactics.
Require Import util.

(***********************************************************)
(* This file proves the properties of operational semantics. *)

Module OpsemProps. Section OpsemProps.

Export Opsem.

(***********************************************************)
(* Properties of sop_star *)
Lemma sInsn__implies__sop_star : forall cfg state state' tr,
  sInsn cfg state state' tr ->
  sop_star cfg state state' tr.
Proof.
  intros cfg state state' tr HdsInsn.
  rewrite <- E0_right.
  eauto.
Qed.

Lemma sop_star_trans : forall cfg state1 state2 state3 tr12 tr23,
  sop_star cfg state1 state2 tr12 ->
  sop_star cfg state2 state3 tr23 ->
  sop_star cfg state1 state3 (Eapp tr12 tr23).
Proof.
  intros cfg state1 state2 state3 tr12 tr23 Hdsop12 Hdsop23.
  generalize dependent state3.
  generalize dependent tr23.
  induction Hdsop12; intros; auto.
    rewrite Eapp_assoc. eauto.
Qed.

(***********************************************************)
(* Properties of sop_plus *)
Lemma sInsn__implies__sop_plus : forall cfg state state' tr,
  sInsn cfg state state' tr ->
  sop_plus cfg state state' tr.
Proof.
  intros cfg state state' tr HdsInsn.
  rewrite <- E0_right.
  eauto.
Qed.

Lemma sop_plus__implies__sop_star : forall cfg state state' tr,
  sop_plus cfg state state' tr ->
  sop_star cfg state state' tr.
Proof.
  intros cfg state state' tr Hdsop_plus.
  inversion Hdsop_plus; subst; eauto.
Qed.

Hint Resolve sInsn__implies__sop_star sInsn__implies__sop_plus
  sop_plus__implies__sop_star.

Lemma sop_plus_star__implies__sop_plus: forall cfg S1 S2 S3 tr1 tr2,
  sop_plus cfg S1 S2 tr1 ->
  sop_star cfg S2 S3 tr2 ->
  sop_plus cfg S1 S3 (tr1 ** tr2).
Proof.
  induction 1; intros; auto.
    rewrite Eapp_assoc; auto. 
    econstructor; eauto.
    eapply sop_star_trans; eauto.
Qed.

Lemma sop_star_plus__implies__sop_plus: forall cfg S1 S2 S3 tr1 tr2,
  sop_star cfg S1 S2 tr1 ->
  sop_plus cfg S2 S3 tr2 ->
  sop_plus cfg S1 S3 (tr1 ** tr2).
Proof.
  induction 1; intros; auto.
    apply IHsop_star in H1.
    rewrite Eapp_assoc; auto. 
    econstructor; eauto.
Qed.

Lemma sop_step_plus__implies__sop_plus: forall cfg S1 S2 S3 tr1 tr2,
  sInsn cfg S1 S2 tr1 ->
  sop_plus cfg S2 S3 tr2 ->
  sop_plus cfg S1 S3 (tr1 ** tr2).
Proof.
  intros. inv H0.
  econstructor; eauto.
Qed.

(***********************************************************)
(* Properties of sop_diverges *)
Lemma sop_diverging_trans : forall cfg state tr1 state' tr2,
  sop_star cfg state state' tr1 ->
  sop_diverges cfg state' tr2 ->
  sop_diverges cfg state (Eappinf tr1 tr2).
Proof.
  intros cfg state tr1 state' tr2 state_dsop_state' state'_dsop_diverges.
  generalize dependent tr2.
  (sop_star_cases (induction state_dsop_state') Case); intros; auto.
  Case "sop_star_cons".
    rewrite Eappinf_assoc. eauto.
Qed.

Lemma sop_star_diverges'__sop_diverges': forall cfg IS1 IS2 tr1 tr2,
  sop_star cfg IS1 IS2 tr1 ->
  sop_diverges' cfg IS2 tr2 ->
  sop_diverges' cfg IS1 (Eappinf tr1 tr2).
Proof.
  induction 1; intros; auto.
    apply IHsop_star in H1.
    rewrite Eappinf_assoc.
    econstructor; eauto.
Qed.

Lemma sop_plus_diverges'__sop_diverges': forall cfg IS1 IS2 tr1 tr2,
  sop_plus cfg IS1 IS2 tr1 ->
  sop_diverges' cfg IS2 tr2 ->
  sop_diverges' cfg IS1 (Eappinf tr1 tr2).
Proof.
  intros. inv H.
  eapply sop_star_diverges'__sop_diverges' in H2; eauto.
  rewrite Eappinf_assoc.
  econstructor; eauto.
Qed.

Lemma sop_star_diverges__sop_diverges: forall cfg IS1 IS2 tr1 tr2,
  sop_star cfg IS1 IS2 tr1 ->
  sop_diverges cfg IS2 tr2 ->
  sop_diverges cfg IS1 (Eappinf tr1 tr2).
Proof.
  induction 1; intros; auto.
    apply IHsop_star in H1.
    rewrite Eappinf_assoc.
    rewrite <- E0_right at 1.
    econstructor; eauto.
Qed.

Lemma sop_diverges__sop_diverges': forall cfg IS tr,
  sop_diverges cfg IS tr -> sop_diverges' cfg IS tr.
Proof.
  cofix CIH.
  intros.
  inv H.
  inv H0.
  assert (sop_diverges cfg state0 (tr3***tr2)) as J.
    clear CIH. 
    eapply sop_star_diverges__sop_diverges; eauto.
  apply CIH in J. clear CIH.
  rewrite Eappinf_assoc.
  econstructor; eauto.
Qed.

Lemma sop_diverges'__sop_diverges: forall cfg IS tr,
  sop_diverges' cfg IS tr -> sop_diverges cfg IS tr.
Proof.
  cofix CIH.
  intros.
  inv H.
  apply CIH in H1. clear CIH.
  econstructor; eauto.
Qed.

Lemma sop_star_diverges__sop_diverges_coind: forall cfg IS1 IS2 tr1 tr2,
  Opsem.sop_star cfg IS1 IS2 tr1 ->
  Opsem.sop_diverges cfg IS2 tr2 ->
  Opsem.sop_diverges cfg IS1 (Eappinf tr1 tr2).
Proof.
  intros.
  inv H0.
  rewrite <- Eappinf_assoc.
  eapply sop_diverges_intro; eauto.
  eapply sop_star_plus__implies__sop_plus; eauto.
Qed.

Lemma sop_star_diverges'__sop_diverges'_coind: forall cfg IS1 IS2 tr1 tr2,
  Opsem.sop_star cfg IS1 IS2 tr1 ->
  Opsem.sop_diverges' cfg IS2 tr2 ->
  Opsem.sop_diverges' cfg IS1 (Eappinf tr1 tr2).
Proof.
  cofix CIH.
  intros.
  inv H0.
  inv H.
    clear CIH.
    rewrite <- Eappinf_assoc.
    econstructor; eauto.

    assert (sop_diverges' cfg state0 (tr4 *** tr0 *** tr3)) as J.
      rewrite <- Eappinf_assoc.
      eapply CIH; eauto.
      eapply sop_star_trans; eauto. 
    clear CIH.
    rewrite Eappinf_assoc.
    eapply sop_diverges_intro'; eauto.
Qed.

Section SOP_WF_DIVERGES.

Context `{Measure: Type}.
Context `{R:Measure -> Measure -> Prop}.
Context `{Hwf_founded_R: well_founded R}.

Lemma sop_wf_diverges__inv: forall m1 cfg S1 Tr
  (Hdiv: sop_wf_diverges Measure R cfg m1 S1 Tr),
  exists S2, exists m2, exists tr, exists Tr',
    sop_plus cfg S1 S2 tr /\
    sop_wf_diverges Measure R cfg m2 S2 Tr' /\
    Tr = Eappinf tr Tr'.
Proof.
  intro m1. pattern m1.
  apply (well_founded_ind Hwf_founded_R); intros.
  inv Hdiv.
    exists state2. exists m2. exists tr1. exists tr2. 
    split; auto.

    apply H in H2; auto.
    destruct H2 as [S2 [m2' [tr [Tr' [J1 [J2 J3]]]]]]; subst.
    exists S2. exists m2'. exists (Eapp tr1 tr). exists Tr'.
    split.
      eapply sop_star_plus__implies__sop_plus; eauto.
    split; auto.
      rewrite Eappinf_assoc; auto.
Qed.

Lemma sop_wf_diverges__sop_diverges: forall cfg m IS tr,
  sop_wf_diverges Measure R cfg m IS tr ->sop_diverges cfg IS tr.
Proof.
  cofix CIH.
  intros.
  inv H.
    apply sop_wf_diverges__inv in H1; auto.
    destruct H1 as [S2 [m2' [tr [Tr' [J1 [J2 J3]]]]]]; subst.
    econstructor; eauto.

    apply sop_wf_diverges__inv in H2; auto.
    destruct H2 as [S2 [m2' [tr [Tr' [J1 [J2 J3]]]]]]; subst.
    rewrite <- Eappinf_assoc.
    econstructor; eauto using sop_star_plus__implies__sop_plus.
Qed.

End SOP_WF_DIVERGES.

Ltac app_inv :=
  match goal with
  | [ H: ?f _ _ _ _ _ _ = ?f _ _ _ _ _ _ |- _ ] => inv H
  | [ H: ?f _ _ _ _ _ = ?f _ _ _ _ _ |- _ ] => inv H
  | [ H: ?f _ _ = ?f _ _ |- _ ] => inv H
  end.

(***********************************************************)
(* Inversion of operations *)
Lemma BOP_inversion : forall TD lc gl b s v1 v2 gv2,
  BOP TD lc gl b s v1 v2 = Some gv2 ->
  exists gvs1, exists gvs2,
    getOperandValue TD v1 lc gl = Some gvs1 /\
    getOperandValue TD v2 lc gl = Some gvs2 /\
    (mbop TD b s) gvs1 gvs2 = Some gv2.
Proof.
  intros TD lc gl b s v1 v2 gv2 HBOP.
  unfold BOP in HBOP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HBOP].
  remember (getOperandValue TD v2 lc gl) as ogv2.
  destruct ogv2; inv HBOP.
  eauto.
Qed.

Lemma FBOP_inversion : forall TD lc gl b fp v1 v2 gv,
  FBOP TD lc gl b fp v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    (mfbop TD b fp) gv1 gv2 = Some gv.
Proof.
  intros TD lc gl b fp v1 v2 gv HFBOP.
  unfold FBOP in HFBOP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HFBOP].
  remember (getOperandValue TD v2 lc gl) as ogv2.
  destruct ogv2; inv HFBOP.
  eauto.
Qed.

Lemma CAST_inversion : forall TD lc gl op t1 v1 t2 gv,
  CAST TD lc gl op t1 v1 t2 = Some gv ->
  exists gv1,
    getOperandValue TD v1 lc gl = Some gv1 /\
    (mcast TD op t1 t2) gv1 = Some gv.
Proof.
  intros TD lc gl op t1 v1 t2 gv HCAST.
  unfold CAST in HCAST.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; inv HCAST.
  eauto.
Qed.

Lemma TRUNC_inversion : forall TD lc gl op t1 v1 t2 gv,
  TRUNC TD lc gl op t1 v1 t2 = Some gv ->
  exists gv1,
    getOperandValue TD v1 lc gl = Some gv1 /\
    (mtrunc TD op t1 t2) gv1 = Some gv.
Proof.
  intros TD lc gl op t1 v1 t2 gv HTRUNC.
  unfold TRUNC in HTRUNC.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; inv HTRUNC.
  eauto.
Qed.

Lemma EXT_inversion : forall TD lc gl op t1 v1 t2 gv,
  EXT TD lc gl op t1 v1 t2 = Some gv ->
  exists gv1,
    getOperandValue TD v1 lc gl = Some gv1 /\
    (mext TD op t1 t2) gv1 = Some gv.
Proof.
  intros TD lc gl op t1 v1 t2 gv HEXT.
  unfold EXT in HEXT.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; inv HEXT.
  eauto.
Qed.

Lemma ICMP_inversion : forall TD lc gl cond t v1 v2 gv,
  ICMP TD lc gl cond t v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    (micmp TD cond t) gv1 gv2 = Some gv.
Proof.
  intros TD lc gl cond0 t v1 v2 gv HICMP.
  unfold ICMP in HICMP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HICMP].
  remember (getOperandValue TD v2 lc gl) as ogv2.
  destruct ogv2; inv HICMP.
  eauto.
Qed.

Lemma FCMP_inversion : forall TD lc gl cond fp v1 v2 gv,
  FCMP TD lc gl cond fp v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    (mfcmp TD cond fp) gv1 gv2 = Some gv.
Proof.
  intros TD lc gl cond0 fp v1 v2 gv HFCMP.
  unfold FCMP in HFCMP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HFCMP].
  remember (getOperandValue TD v2 lc gl) as ogv2.
  destruct ogv2; inv HFCMP.
  eauto.
Qed.

(***********************************************************)
(* Equivalence of operations *)
Lemma const2GV_eqAL : forall c gl1 gl2 TD,
  eqAL _ gl1 gl2 ->
  const2GV TD gl1 c = const2GV TD gl2 c.
Proof.
  intros. unfold const2GV.
  destruct const2GV_eqAL_aux.
  erewrite H0; eauto.
Qed.

Lemma getOperandValue_eqAL : forall lc1 gl lc2 v TD,
  eqAL _ lc1 lc2 ->
  getOperandValue TD v lc1 gl = getOperandValue TD v lc2 gl.
Proof.
  intros lc1 gl lc2 v TD HeqAL.
  unfold getOperandValue in *.
  destruct v; auto.
Qed.

Lemma BOP_eqAL : forall lc1 gl lc2 bop0 sz0 v1 v2 TD,
  eqAL _ lc1 lc2 ->
  BOP TD lc1 gl bop0 sz0 v1 v2 = BOP TD lc2 gl bop0 sz0 v1 v2.
Proof.
  intros lc1 gl lc2 bop0 sz0 v1 v2 TD HeqEnv.
  unfold BOP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Lemma FBOP_eqAL : forall lc1 gl lc2 fbop0 fp0 v1 v2 TD,
  eqAL _ lc1 lc2 ->
  FBOP TD lc1 gl fbop0 fp0 v1 v2 = FBOP TD lc2 gl fbop0 fp0 v1 v2.
Proof.
  intros lc1 gl lc2 fbop0 fp0 v1 v2 TD HeqEnv.
  unfold FBOP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Lemma CAST_eqAL : forall lc1 gl lc2 op t1 v1 t2 TD,
  eqAL _ lc1 lc2 ->
  CAST TD lc1 gl op t1 v1 t2 = CAST TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD HeqAL.
  unfold CAST in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
Qed.

Lemma TRUNC_eqAL : forall lc1 gl lc2 op t1 v1 t2 TD,
  eqAL _ lc1 lc2 ->
  TRUNC TD lc1 gl op t1 v1 t2 = TRUNC TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD HeqAL.
  unfold TRUNC in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
Qed.

Lemma EXT_eqAL : forall lc1 gl lc2 op t1 v1 t2 TD,
  eqAL _ lc1 lc2 ->
  EXT TD lc1 gl op t1 v1 t2 = EXT TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD HeqAL.
  unfold EXT in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
Qed.

Lemma ICMP_eqAL : forall lc1 gl lc2 cond t v1 v2 TD,
  eqAL _ lc1 lc2 ->
  ICMP TD lc1 gl cond t v1 v2 = ICMP TD lc2 gl cond t v1 v2.
Proof.
  intros lc1 gl lc2 cond0 t v1 v2 TD HeqAL.
  unfold ICMP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Lemma FCMP_eqAL : forall lc1 gl lc2 cond fp v1 v2 TD,
  eqAL _ lc1 lc2 ->
  FCMP TD lc1 gl cond fp v1 v2 = FCMP TD lc2 gl cond fp v1 v2.
Proof.
  intros lc1 gl lc2 cond0 fp v1 v2 TD HeqAL.
  unfold FCMP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Lemma values2GVs_eqAL : forall l0 lc1 gl lc2 TD,
  eqAL _ lc1 lc2 ->
  values2GVs TD l0 lc1 gl = values2GVs TD l0 lc2 gl.
Proof.
  induction l0 as [|[s v] l0]; intros lc1 gl lc2 TD HeqAL; simpl; auto.
    rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v); auto.
    erewrite IHl0; eauto.
Qed.

Lemma eqAL_getIncomingValuesForBlockFromPHINodes : forall TD ps B gl lc lc',
  eqAL _ lc lc' ->
  getIncomingValuesForBlockFromPHINodes TD ps B gl lc =
  getIncomingValuesForBlockFromPHINodes TD ps B gl lc'.
Proof.
  induction ps; intros; simpl; auto.
    destruct a; auto.
    destruct (getValueViaBlockFromValuels l0 B); auto.
    destruct v; simpl; erewrite IHps; eauto.
      rewrite H. auto.
Qed.

Lemma eqAL_updateValuesForNewBlock : forall vs lc lc',
  eqAL _ lc lc' ->
  eqAL _ (updateValuesForNewBlock vs lc)(updateValuesForNewBlock vs lc').
Proof.
  induction vs; intros; simpl; auto.
    destruct a; auto using eqAL_updateAddAL.
Qed.

Lemma eqAL_switchToNewBasicBlock : forall TD B1 B2 gl lc lc',
  eqAL _ lc lc' ->
  match (switchToNewBasicBlock TD B1 B2 gl lc,
         switchToNewBasicBlock TD B1 B2 gl lc') with
  | (Some lc1, Some lc1') => eqAL _ lc1 lc1'
  | (None, None) => True
  | _ => False
  end.
Proof.
  intros.
  unfold switchToNewBasicBlock.
  erewrite eqAL_getIncomingValuesForBlockFromPHINodes; eauto.
  destruct
    (getIncomingValuesForBlockFromPHINodes TD (getPHINodesFromBlock B1) B2 gl
    lc'); auto using eqAL_updateValuesForNewBlock.
Qed.

Lemma eqAL_switchToNewBasicBlock' : forall TD B1 B2 gl lc lc' lc1,
  eqAL _ lc lc' ->
  switchToNewBasicBlock TD B1 B2 gl lc = Some lc1 ->
  exists lc1', switchToNewBasicBlock TD B1 B2 gl lc' = Some lc1' /\
               eqAL _ lc1 lc1'.
Proof.
  intros.
  assert (J:=eqAL_switchToNewBasicBlock TD B1 B2 gl lc lc' H).
  rewrite H0 in J.
  destruct (switchToNewBasicBlock TD B1 B2 gl lc'); try solve [inversion J].
  exists g. auto.
Qed.

Lemma eqAL_params2GVs : forall lp TD lc gl lc',
  eqAL _ lc lc' ->
  params2GVs TD lp lc gl = params2GVs TD lp lc' gl.
Proof.
  induction lp; intros; simpl; auto.
    destruct a.
    destruct v; simpl.
      rewrite H. erewrite IHlp; eauto.
      erewrite IHlp; eauto.
Qed.

Lemma eqAL_exCallUpdateLocals : forall TD noret0 rid oResult lc lc' rt,
  eqAL _ lc lc' ->
  match (exCallUpdateLocals TD rt noret0 rid oResult lc,
         exCallUpdateLocals TD rt noret0 rid oResult lc') with
  | (Some lc1, Some lc1') => eqAL _ lc1 lc1'
  | (None, None) => True
  | _ => False
  end.
Proof.
  intros TD noret0 rid oResult lc lc' rt H1.
    unfold exCallUpdateLocals.
    destruct noret0; auto.
    destruct oResult; auto.
    destruct (fit_gv TD rt g); auto using eqAL_updateAddAL.
Qed.

Lemma eqAL_exCallUpdateLocals' : forall TD ft noret0 rid oResult lc lc' lc0,
  eqAL _ lc lc' ->
  exCallUpdateLocals TD ft noret0 rid oResult lc = Some lc0 ->
  exists lc0', exCallUpdateLocals TD ft noret0 rid oResult lc' = Some lc0' /\
               eqAL _ lc0 lc0'.
Proof.
  intros TD ft noret0 rid oResult lc lc' lc0 H H0.
  assert (J:=eqAL_exCallUpdateLocals TD noret0 rid oResult lc lc' ft H).
  rewrite H0 in J.
  destruct (exCallUpdateLocals TD ft noret0 rid oResult lc');
    try solve [inversion J].
  exists g. auto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_eq :
  forall ps TD l1 ps1 cs1 tmn1 ps2 cs2 tmn2,
  getIncomingValuesForBlockFromPHINodes TD ps
    (l1, stmts_intro ps1 cs1 tmn1) =
  getIncomingValuesForBlockFromPHINodes TD ps (l1, stmts_intro ps2 cs2 tmn2).
Proof.
  induction ps; intros; auto.
    simpl.
    erewrite IHps; eauto.
Qed.

Lemma switchToNewBasicBlock_eq :
  forall TD B l1 ps1 cs1 tmn1 ps2 cs2 tmn2 gl lc,
  switchToNewBasicBlock TD B (l1, stmts_intro ps1 cs1 tmn1) gl lc =
  switchToNewBasicBlock TD B (l1, stmts_intro ps2 cs2 tmn2) gl lc.
Proof.
  intros.
  unfold switchToNewBasicBlock.
  erewrite getIncomingValuesForBlockFromPHINodes_eq; eauto.
Qed.

(***********************************************************)
(* Uniqueness of operations *)
Lemma exCallUpdateLocals_uniq : forall TD rt noret0 rid oresult lc lc',
  uniq lc ->
  exCallUpdateLocals TD rt noret0 rid oresult lc = Some lc' ->
  uniq lc'.
Proof.
  intros.
  unfold exCallUpdateLocals in H0.
  destruct noret0; auto.
    inversion H0; subst; auto.

    destruct oresult; try solve [inversion H0].
    destruct (fit_gv TD rt g); inversion H0; subst.
      apply updateAddAL_uniq; auto.
Qed.

Lemma updateValuesForNewBlock_uniq : forall l0 lc,
  uniq lc ->
  uniq (updateValuesForNewBlock l0 lc).
Proof.
  induction l0; intros lc Uniqc; simpl; auto.
    destruct a; apply updateAddAL_uniq; auto.
Qed.

Lemma switchToNewBasicBlock_uniq : forall TD B1 B2 gl lc lc',
  uniq lc ->
  switchToNewBasicBlock TD B1 B2 gl lc = Some lc' ->
  uniq lc'.
Proof.
  intros TD B1 B2 gl lc lc' Uniqc H.
  unfold switchToNewBasicBlock in H.
  destruct (getIncomingValuesForBlockFromPHINodes TD (getPHINodesFromBlock B1)
    B2 gl lc); inversion H; subst.
  apply updateValuesForNewBlock_uniq; auto.
Qed.

Lemma initializeFrameValues_init : forall TD la l0 lc,
  _initializeFrameValues TD la l0 nil = Some lc ->
  uniq lc.
Proof.
  induction la; intros; simpl in *; auto.
    inv H. auto.

    destruct a as [[t ?] id0].
    destruct l0.
      remember (_initializeFrameValues TD la nil nil) as R.
      destruct R; tinv H.
      destruct (gundef TD t); inv H; eauto using updateAddAL_uniq.

      remember (_initializeFrameValues TD la l0 nil) as R.
      destruct R; tinv H.
      destruct ((fit_gv TD t) g); inv H;
        eauto using updateAddAL_uniq.
Qed.

Lemma initLocals_uniq : forall TD la ps lc,
  initLocals TD la ps = Some lc -> uniq lc.
Proof.
  intros la ps.
  unfold initLocals.
  apply initializeFrameValues_init; auto.
Qed.

Lemma updateValuesForNewBlock_spec4 : forall rs lc id1 gv,
  lookupAL _ rs id1 = Some gv ->
  lookupAL _ (updateValuesForNewBlock rs lc) id1 = Some gv.
Proof.
  induction rs; intros; simpl in *.
    inversion H.

    destruct a.
    destruct (id1==a); subst.
      inversion H; subst. apply lookupAL_updateAddAL_eq; auto.
      rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

(***********************************************************)
(* Properties of initLocals and initializeFrameValues *)
Lemma initLocals_spec : forall TD la gvs id1 lc,
  In id1 (getArgsIDs la) ->
  initLocals TD la gvs = Some lc ->
  exists gv, lookupAL _ lc id1 = Some gv.
Proof.
  unfold initLocals.
  induction la; intros; simpl in *.
    inversion H.

    destruct a as [[t c] id0].
    simpl in H.
    destruct H as [H | H]; subst; simpl.
      destruct gvs.
        remember (_initializeFrameValues TD la nil nil) as R1.
        destruct R1; tinv H0.
        remember (gundef TD t) as R2.
        destruct R2; inv H0.
        eauto using lookupAL_updateAddAL_eq.

        remember (_initializeFrameValues TD la gvs nil) as R1.
        destruct R1; tinv H0.
        destruct ((fit_gv TD t) g); inv H0.
        eauto using lookupAL_updateAddAL_eq.

      destruct (eq_atom_dec id0 id1); subst.
        destruct gvs.
          remember (_initializeFrameValues TD la nil nil) as R1.
          destruct R1; tinv H0.
          remember (gundef TD t) as R2.
          destruct R2; inv H0.
          eauto using lookupAL_updateAddAL_eq.

          remember (_initializeFrameValues TD la gvs nil) as R1.
          destruct R1; tinv H0.
          destruct ((fit_gv TD t) g); inv H0.
          eauto using lookupAL_updateAddAL_eq.

        destruct gvs.
          remember (_initializeFrameValues TD la nil nil) as R1.
          destruct R1; tinv H0.
          remember (gundef TD t) as R2.
          destruct R2; inv H0.
          symmetry in HeqR1.
          eapply IHla in HeqR1; eauto.
          destruct HeqR1 as [gv HeqR1].
          rewrite <- lookupAL_updateAddAL_neq; eauto.

          remember (_initializeFrameValues TD la gvs nil) as R1.
          destruct R1; tinv H0.
          destruct ((fit_gv TD t) g); inv H0.
          symmetry in HeqR1.
          eapply IHla in HeqR1; eauto.
          destruct HeqR1 as [gv HeqR1].
          rewrite <- lookupAL_updateAddAL_neq; eauto.
Qed.

Lemma In_initializeFrameValues__In_getArgsIDs: forall
  (TD : TargetData) (la : args) (gvs : list GenericValue) (id1 : atom)
  (lc : Opsem.GVsMap) (gv : GenericValue) acc,
  Opsem._initializeFrameValues TD la gvs acc = ret lc ->
  lookupAL GenericValue lc id1 = ret gv ->
  In id1 (getArgsIDs la) \/ id1 `in` dom acc.
Proof.
  induction la as [|[]]; simpl; intros.
    inv H.
    right. apply lookupAL_Some_indom in H0; auto.

    destruct p.
    destruct gvs.
      inv_mbind. 
      destruct (id_dec i0 id1); subst; auto.
      rewrite <- lookupAL_updateAddAL_neq in H0; auto.
      eapply IHla in H0; eauto.
      destruct H0 as [H0 | H0]; auto.

      inv_mbind.
      destruct (id_dec i0 id1); subst; auto.
      rewrite <- lookupAL_updateAddAL_neq in H0; auto.
      eapply IHla in H0; eauto.
      destruct H0 as [H0 | H0]; auto.
Qed.

Lemma In_initLocals__In_getArgsIDs : forall TD la gvs id1 lc gv,
  Opsem.initLocals TD la gvs = Some lc ->
  lookupAL _ lc id1 = Some gv ->
  In id1 (getArgsIDs la).
Proof.
  unfold Opsem.initLocals.
  intros.
  eapply In_initializeFrameValues__In_getArgsIDs in H; eauto.
  destruct H as [H | H]; auto.
    fsetdec.
Qed.

Lemma dom_initializeFrameValues: forall
  (TD : TargetData) (la : args) gvs lc acc,
  Opsem._initializeFrameValues TD la gvs acc = ret lc ->
  (forall i0, i0 `in` dom lc -> i0 `in` dom acc \/ In i0 (getArgsIDs la)).
Proof.
  induction la as [|[[]]]; simpl; intros.
    inv H. auto.

    destruct gvs.
      inv_mbind'.
      rewrite updateAddAL_dom_eq in H0.
      assert (i1 `in` (dom g) \/ i1 = i0) as J.
        fsetdec.
      destruct J as [J | J]; subst; auto.
        symmetry in HeqR.
        apply IHla with (i0:=i1) in HeqR; auto.
        destruct HeqR as [HeqR | HeqR]; auto.

      inv_mbind'.
      rewrite updateAddAL_dom_eq in H0.
      assert (i1 `in` (dom g0) \/ i1 = i0) as J.
        fsetdec.
      destruct J as [J | J]; subst; auto.
        symmetry in HeqR.
        apply IHla with (i0:=i1) in HeqR; auto.
        destruct HeqR as [HeqR | HeqR]; auto.
Qed.

Lemma NotIn_getArgsIDs__NotIn_initializeFrameValues: forall
  (TD : TargetData) (la : args) gvs (id1 : atom) lc acc,
  Opsem._initializeFrameValues TD la gvs acc = ret lc ->
  ~ In id1 (getArgsIDs la) /\ id1 `notin` dom acc ->
  lookupAL _ lc id1 = None.
Proof.
  induction la as [|[]]; simpl; intros.
    inv H.
    destruct H0.
    apply notin_lookupAL_None; auto.

    destruct H0 as [H1 H2].
    assert (i0 <> id1 /\ ~ In id1 (getArgsIDs la)) as J.
      split; intro; subst; contradict H1; auto.
    destruct J as [J1 J2].
    destruct p.
    destruct gvs.
      inv_mbind'.
      rewrite <- lookupAL_updateAddAL_neq; auto.
      apply notin_lookupAL_None; auto.
      intro J. symmetry in HeqR.
      apply dom_initializeFrameValues with (i0:=id1) in HeqR; auto.
      destruct HeqR; auto.

      inv_mbind'.
      rewrite <- lookupAL_updateAddAL_neq; auto.
      eapply IHla; eauto.
Qed.

Lemma NotIn_getArgsIDs__NotIn_initLocals : forall TD la gvs id1 lc,
  Opsem.initLocals TD la gvs = Some lc ->
  ~ In id1 (getArgsIDs la) ->
  lookupAL _ lc id1 = None.
Proof.
  unfold Opsem.initLocals.
  intros.
  eapply NotIn_getArgsIDs__NotIn_initializeFrameValues in H; eauto.
Qed.

(***********************************************************)
(* Properties of updateValuesForNewBlock *)
Lemma updateValuesForNewBlock_spec6 : forall lc rs id1 gvs
  (Hlk : lookupAL _ (updateValuesForNewBlock rs lc) id1 = ret gvs)
  (Hin : id1 `in` (dom rs)),
  lookupAL _ rs id1 = Some gvs.
Proof.
  induction rs; simpl; intros.
    fsetdec.

    destruct a.
    assert (id1 = i0 \/ id1 `in` dom rs) as J. fsetdec.
    destruct J as [J | J]; subst.
      rewrite lookupAL_updateAddAL_eq in Hlk; auto. inv Hlk.
      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i0 i0); auto.
        contradict n; auto.

      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id1 i0);
        subst; eauto.
        rewrite lookupAL_updateAddAL_eq in Hlk; auto.
        rewrite <- lookupAL_updateAddAL_neq in Hlk; eauto.
Qed.

Lemma updateValuesForNewBlock_spec7 : forall lc rs id1 gvs
  (Hlk : lookupAL _ (updateValuesForNewBlock rs lc) id1 = ret gvs)
  (Hnotin : id1 `notin` (dom rs)),
  lookupAL _ lc id1 = ret gvs.
Proof.
  induction rs; simpl; intros; auto.
    destruct a.

    destruct_notin.
    rewrite <- lookupAL_updateAddAL_neq in Hlk; eauto.
Qed.

Lemma updateValuesForNewBlock_spec6' : forall lc rs id1
  (Hin : id1 `in` (dom rs)),
  lookupAL _ (updateValuesForNewBlock rs lc) id1 = lookupAL _ rs id1.
Proof.
  induction rs; simpl; intros.
    fsetdec.

    destruct a.
    assert (id1 = a \/ id1 `in` dom rs) as J. fsetdec.
    destruct J as [J | J]; subst.
      rewrite lookupAL_updateAddAL_eq.
      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) a a); auto.
        contradict n; auto.

      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id1 a);
        subst; eauto.
        rewrite lookupAL_updateAddAL_eq; auto.
        rewrite <- lookupAL_updateAddAL_neq; eauto.
Qed.

Lemma updateValuesForNewBlock_spec7' : forall lc rs id1
  (Hin : id1 `notin` (dom rs)),
  lookupAL _ (updateValuesForNewBlock rs lc) id1 = lookupAL _ lc id1.
Proof.
  induction rs; simpl; intros; auto.
    destruct a. destruct_notin.
    rewrite <- lookupAL_updateAddAL_neq; eauto.
Qed.

Lemma updateValuesForNewBlock_sim : forall id0 lc lc'
  (Heq : forall id' : id,
        id' <> id0 ->
        lookupAL _ lc id' = lookupAL GenericValue lc' id')
  g0 g
  (EQ : forall id' : id,
       id' <> id0 ->
       lookupAL _ g0 id' = lookupAL _ g id'),
  forall id', id' <> id0 ->
   lookupAL _ (updateValuesForNewBlock g0 lc) id' =
   lookupAL _ (updateValuesForNewBlock g lc') id'.
Proof.
  intros.
  destruct (AtomSetProperties.In_dec id' (dom g0)).
    rewrite updateValuesForNewBlock_spec6'; auto.
    destruct (AtomSetProperties.In_dec id' (dom g)).
      rewrite updateValuesForNewBlock_spec6'; auto.

      apply notin_lookupAL_None in n.
      erewrite <- EQ in n; eauto.
      apply indom_lookupAL_Some in i0.
      destruct i0 as [gv0 i0].
      rewrite i0 in n. congruence.

    rewrite updateValuesForNewBlock_spec7'; auto.
    destruct (AtomSetProperties.In_dec id' (dom g)).
      apply notin_lookupAL_None in n.
      erewrite EQ in n; eauto.
      apply indom_lookupAL_Some in i0.
      destruct i0 as [gv0 i0].
      rewrite i0 in n. congruence.

      rewrite updateValuesForNewBlock_spec7'; auto.
Qed.

Lemma updateValuesForNewBlock_spec5: forall lc1' lc2' i0
  (Hlk: lookupAL _ lc1' i0 = lookupAL _ lc2' i0) lc2
  (Hlk: merror = lookupAL _ lc2 i0),
  lookupAL _ lc1' i0 =
    lookupAL _ (Opsem.updateValuesForNewBlock lc2 lc2') i0.
Proof.
  induction lc2 as [|[]]; simpl; intros; auto.
    destruct (i0 == a); try congruence.
    rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

(***********************************************************)
(* Properties of getIncomingValuesForBlockFromPHINodes *)
Lemma getIncomingValuesForBlockFromPHINodes_spec6 : forall TD b gl lc ps' rs id1
  (HeqR1 : ret rs = getIncomingValuesForBlockFromPHINodes TD ps' b gl lc)
  (Hin : In id1 (getPhiNodesIDs ps')),
  id1 `in` dom rs.
Proof.
  induction ps'; simpl; intros.
    inv Hin.

    destruct a. destruct b. simpl in *.
    inv_mbind. inv HeqR1.
    destruct (gv_chunks_match_typb TD g typ5).
    destruct Hin as [Hin | Hin]; subst. inv H0. simpl. auto.
    inv H0. simpl. auto.
    inv H0.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec7 : forall TD b gl lc ps' rs id1
  (HeqR1 : ret rs = getIncomingValuesForBlockFromPHINodes TD ps' b gl lc)
  (Hin : id1 `in` dom rs),
  In id1 (getPhiNodesIDs ps').
Proof.
  induction ps'; simpl; intros.
    inv HeqR1. fsetdec.

    destruct a as [i0 ?]. destruct b as [l2 ? ? ?]. simpl in *.
    inv_mbind. inv HeqR1. simpl in *.
    assert (id1 = i0 \/ id1 `in` dom l1) as J.
    destruct (gv_chunks_match_typb TD g typ5).
    inv H0. simpl in Hin.
    fsetdec.
    inv H0.
    destruct J as [J | J]; subst; eauto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec8 : forall TD b gl lc ps' rs id1
  (HeqR1 : ret rs = getIncomingValuesForBlockFromPHINodes TD ps' b gl lc)
  (Hnotin : ~ In id1 (getPhiNodesIDs ps')),
  id1 `notin` dom rs.
Proof.
  intros.
  intro J. apply Hnotin.
  eapply getIncomingValuesForBlockFromPHINodes_spec7 in HeqR1; eauto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec9: forall TD gl lc b id0 gvs0
  ps' l0,
  ret l0 = Opsem.getIncomingValuesForBlockFromPHINodes TD ps' b gl lc ->
  id0 `in` dom l0 ->
  lookupAL _ l0 id0 = ret gvs0 ->
  exists id1, exists t1, exists vls1, exists v, exists n,
    In (insn_phi id1 t1 vls1) ps' /\
    nth_error vls1 n = Some (v, getBlockLabel b) /\
    Opsem.getOperandValue TD v lc gl= Some gvs0.
Proof.
  induction ps' as [|[i0 t l0]]; simpl; intros.
    inv H. fsetdec.

    inv_mbind. simpl in *.
    destruct (id0 == i0); subst.
      destruct b. simpl in *.
      symmetry in HeqR.
      apply getValueViaLabelFromValuels__nth_list_value_l in HeqR; auto.
      destruct HeqR as [n HeqR].
      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i0 i0);
        try congruence.
      destruct (gv_chunks_match_typb TD g t).
      inv H3.
      
      exists i0. exists t. exists l0. exists v. exists n.
      split; auto. split. auto. auto. simpl in H1.
      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i0 i0).
      inv H1. eauto. apply n0 in e. inv e.
      inv H3.
      destruct (gv_chunks_match_typb TD g t).
      inv H3. simpl in H1.
      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id0 i0).
      apply n in e. inv e.
      apply IHps' in H1; auto; try fsetdec.
      destruct H1 as [id1 [t1 [vls1 [v' [n' [J1 [J2 J3]]]]]]].
      exists id1. exists t1. exists vls1. exists v'. exists n'.
      split; auto.
      apply in_dom_cons_inv in H0.
      inv H0. assert (i0 = i0). auto. apply n in H. inv H.
      auto.
      inv H3.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec9': forall TD gl lc b id0 gvs0
  ps' l0,
  ret l0 = Opsem.getIncomingValuesForBlockFromPHINodes TD ps' b gl lc ->
  id0 `in` dom l0 ->
  lookupAL _ l0 id0 = ret gvs0 ->
  exists t1, exists vls1, exists v, 
    In (insn_phi id0 t1 vls1) ps' /\
    getValueViaLabelFromValuels vls1 (getBlockLabel b) = Some v /\
    Opsem.getOperandValue TD v lc gl= Some gvs0.
Proof.
  induction ps' as [|[i0 t l0]]; simpl; intros.
    inv H. fsetdec.

    inv_mbind. simpl in *.
    destruct (id0 == i0); subst.
      destruct b. simpl in *.
      symmetry in HeqR.
      inv H1.
      destruct (gv_chunks_match_typb TD g t).
      inv H3.
      exists t. exists l0. exists v. 
      simpl in H2.
      inv H2. split; auto. split. auto. simpl.
      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i0 i0).
      auto. assert (i0 = i0). auto. apply n in H. inv H.
      inv H3.
      
      destruct (gv_chunks_match_typb TD g t).
      inv H3. simpl in H1.
      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id0 i0).
      apply n in e. inv e.

      apply IHps' in H1; auto; try fsetdec.
      destruct H1 as [t1 [vls1 [v' [J1 [J2 J3]]]]].
      exists t1. exists vls1. exists v'.
      split; auto.
      apply in_dom_cons_inv in H0.
      inv H0. assert (i0 = i0). auto. apply n in H. inv H.
      auto.
      inv H3.
Qed.

End OpsemProps. End OpsemProps.
