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
Lemma sop_plus__implies__sop_star : forall cfg state state' tr,
  sop_plus cfg state state' tr ->
  sop_star cfg state state' tr.
Proof.
  intros cfg state state' tr Hdsop_plus.
  inversion Hdsop_plus; subst; eauto.
Qed.

Hint Resolve sop_plus__implies__sop_star.

(***********************************************************)
(* Properties of sop_diverges *)
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

(***********************************************************)
(* Uniqueness of operations *)
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
    destruct Hin as [Hin | Hin]; subst; simpl; auto.
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
    assert (id1 = i0 \/ id1 `in` dom l1) as J. fsetdec.
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
      exists t. exists l0. exists v. 
      split; auto.

      apply IHps' in H1; auto; try fsetdec.
      destruct H1 as [t1 [vls1 [v' [J1 [J2 J3]]]]].
      exists t1. exists vls1. exists v'.
      split; auto.
Qed.

End OpsemProps. End OpsemProps.
