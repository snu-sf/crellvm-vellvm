Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import Maps.
Require Import opsem_props.
Require Import promotable_props.
Require Import primitives.
Require Import palloca_props.
Require Import memory_props.
Require Import mem2reg.
Require Import program_sim.
Require Import trans_tactic.
Require Import sas_msim.
Require Import memory_sim.
Require Import top_sim.

Definition sas (sid1 sid2: id) (v1 v2:value) (cs2:cmds) (b:block)
  (pinfo:PhiInfo) : Prop :=
blockInFdefB b (PI_f pinfo) = true /\
load_in_cmds (PI_id pinfo) cs2 = false /\
let '(block_intro _ _ cs _) := b in
exists cs1, exists cs3,
  cs =
  cs1 ++
  insn_store sid1 (PI_typ pinfo) v1 (value_id (PI_id pinfo)) (PI_align pinfo) ::
  cs2 ++
  insn_store sid2 (PI_typ pinfo) v2 (value_id (PI_id pinfo)) (PI_align pinfo) ::
  cs3.

Record SASInfo (pinfo: PhiInfo) := mkSASInfo {
  SAS_sid1 : id;
  SAS_sid2 : id;
  SAS_value1 : value;
  SAS_value2 : value;
  SAS_tail : cmds;
  SAS_block : block;
  SAS_prop: sas SAS_sid1 SAS_sid2 SAS_value1 SAS_value2 SAS_tail SAS_block pinfo
}.

Definition fdef_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) f1 f2
  : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then
    remove_fdef (SAS_sid1 pinfo sasinfo) f1 = f2
  else f1 = f2.

Definition cmds_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) (f1:fdef)
  cs1 cs2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then
    remove_cmds (SAS_sid1 pinfo sasinfo) cs1 = cs2
  else cs1 = cs2.

Definition block_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) (f1:fdef)
  b1 b2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then
    remove_block (SAS_sid1 pinfo sasinfo) b1 = b2
  else b1 = b2.

Lemma fdef_simulation__eq_fheader: forall pinfo sasinfo f1 f2
  (H: fdef_simulation pinfo sasinfo f1 f2),
  fheaderOfFdef f1 = fheaderOfFdef f2.
Proof.
  unfold fdef_simulation.
  intros.
  destruct (fdef_dec (PI_f pinfo) f1); inv H; auto.
    destruct (PI_f pinfo) as [fh b]; simpl; auto.
Qed.

Lemma fdef_simulation__det_right: forall pinfo sasinfo f f1 f2,
  fdef_simulation pinfo sasinfo f f1 ->
  fdef_simulation pinfo sasinfo f f2 ->
  f1 = f2.
Proof.
  unfold fdef_simulation.
  intros.
  destruct_if; congruence.
Qed.

Definition Fsim (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) := mkFunSim 
(fdef_simulation pinfo sasinfo)
(fdef_simulation__eq_fheader pinfo sasinfo)
(fdef_simulation__det_right pinfo sasinfo)
.

Definition products_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) 
  Ps1 Ps2 : Prop :=
@TopSim.products_simulation (Fsim pinfo sasinfo) Ps1 Ps2.

Definition system_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) 
  S1 S2 : Prop :=
@TopSim.system_simulation (Fsim pinfo sasinfo) S1 S2.

Definition EC_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo)
  (EC1 EC2:@Opsem.ExecutionContext DGVs) : Prop :=
  match (EC1, EC2) with
  | (Opsem.mkEC f1 b1 cs1 tmn1 lc1 als1,
     Opsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       fdef_simulation pinfo sasinfo f1 f2 /\
       tmn1 = tmn2 /\
       als1 = als2 /\
       block_simulation pinfo sasinfo f1 b1 b2 /\
       (exists l1, exists ps1, exists cs11,
         b1 = block_intro l1 ps1 (cs11++cs1) tmn1)
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++cs2) tmn2) /\
       lc1 = lc2 /\
       cmds_simulation pinfo sasinfo f1 cs1 cs2
  end.

Fixpoint ECs_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo)
  (ECs1 ECs2:@Opsem.ECStack DGVs) : Prop :=
match ECs1, ECs2 with
| nil, nil => True
| EC1::ECs1', EC2::ECs2' =>
    EC_simulation pinfo sasinfo EC1 EC2 /\
    ECs_simulation pinfo sasinfo ECs1' ECs2'
| _, _ => False
end.

Definition cs_follow_dead_store (pinfo:PhiInfo) (sasinfo: SASInfo pinfo)
  (cs:cmds) : Prop :=
let '(block_intro _ _ cs0 _) := SAS_block pinfo sasinfo in
forall cs1 cs3,
  cs0 =
  cs1 ++
    insn_store (SAS_sid1 pinfo sasinfo) (PI_typ pinfo)
      (SAS_value1 pinfo sasinfo) (value_id (PI_id pinfo)) (PI_align pinfo) ::
    SAS_tail pinfo sasinfo ++
    cs3 ->
  (exists csa, exists csb,
    cs = csb ++ cs3 /\ SAS_tail pinfo sasinfo = csa ++ csb).

Definition EC_follow_dead_store (pinfo:PhiInfo) (sasinfo: SASInfo pinfo)
  (ec:@Opsem.ExecutionContext DGVs) : Prop :=
Opsem.CurFunction ec = PI_f pinfo /\
Opsem.CurBB ec = SAS_block pinfo sasinfo /\
cs_follow_dead_store pinfo sasinfo (Opsem.CurCmds ec).

Definition in_SAS_tail (pinfo:PhiInfo) (sasinfo: SASInfo pinfo) omb 
  (TD:TargetData) (ec0:@Opsem.ExecutionContext DGVs) : Prop :=
  (EC_follow_dead_store pinfo sasinfo ec0 -> 
     match lookupAL _ (Opsem.Locals ec0) (PI_id pinfo) with
     | Some ((Vptr mb _, _)::nil) => omb = Some mb
     | _ => omb = None
     end) /\
  (~EC_follow_dead_store pinfo sasinfo ec0 -> omb = None).

Definition in_SAS_tails (pinfo:PhiInfo) (sasinfo: SASInfo pinfo) ombs TD
  (ecs:list Opsem.ExecutionContext) : Prop :=
List.Forall2 (fun ec omb => 
              in_SAS_tail pinfo sasinfo omb TD ec) ecs ombs.

Definition sas_mem_inj (pinfo:PhiInfo) (sasinfo: SASInfo pinfo) 
  (ecs1:list Opsem.ExecutionContext) (TD:TargetData) (m1 m2: mem) : Prop :=
match getTypeStoreSize TD (PI_typ pinfo) with
| Some tsz => 
    forall ombs,
      in_SAS_tails pinfo sasinfo ombs TD ecs1 ->
      SASmsim.mem_inj inject_id (ombs__ignores (Size.to_Z tsz) ombs) m1 m2
| None => False
end.

Definition mem_simulation (pinfo:PhiInfo) (sasinfo: SASInfo pinfo) TD
  (ecs1:list Opsem.ExecutionContext) Mem1 Mem2 : Prop :=
Mem.nextblock Mem1 = Mem.nextblock Mem2 /\
(forall b, Mem.bounds Mem1 b = Mem.bounds Mem2 b) /\
sas_mem_inj pinfo sasinfo ecs1 TD Mem1 Mem2.

Definition State_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo)
  (Cfg1:OpsemAux.Config) (St1:Opsem.State)
  (Cfg2:OpsemAux.Config) (St2:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg S1 TD1 Ps1 gl1 fs1) := Cfg1 in
let '(OpsemAux.mkCfg S2 TD2 Ps2 gl2 fs2) := Cfg2 in
match (St1, St2) with
| (Opsem.mkState ECs1 M1, Opsem.mkState ECs2 M2) =>
    TD1 = TD2 /\
    products_simulation pinfo sasinfo Ps1 Ps2 /\
    ECs_simulation pinfo sasinfo ECs1 ECs2 /\
    gl1 = gl2 /\ fs1 = fs2 /\ mem_simulation pinfo sasinfo TD1 ECs1 M1 M2
end.

Definition removable_State (pinfo: PhiInfo) (sasinfo: SASInfo pinfo)
  (St:@Opsem.State DGVs) : Prop :=
match St with
| Opsem.mkState
    (Opsem.mkEC f b
      (insn_store sid _ _ _ _ :: cs)
      tmn lc als::_) _ =>
    if (fdef_dec (PI_f pinfo) f) then
      if (id_dec sid (SAS_sid1 pinfo sasinfo))
      then True else False
    else False
| _ => False
end.

Lemma removable_State_dec : forall pinfo sasinfo St,
  removable_State pinfo sasinfo St \/ ~ removable_State pinfo sasinfo St.
Proof.
  destruct St.
  destruct ECS as [|[]]; auto.
  destruct CurCmds; auto.
  simpl.
  destruct_cmd c; auto.
  destruct (fdef_dec (PI_f pinfo) CurFunction); auto.
  destruct (id_dec i0 (SAS_sid1 pinfo sasinfo)); auto.
Qed.

Ltac repeat_solve :=
  repeat (match goal with
          | |- mem_simulation _ _ _ _ _ _ => idtac
          | |- _ => split; eauto 2 using cmds_at_block_tail_next
          end).

Lemma SAS_sid1_isnt_in_SAS_tail: forall pinfo sasinfo TD B1 t v v0 a cs1 tmn2 
  lc2 als2 (Huniq: uniqFdef (PI_f pinfo)),
  in_SAS_tail pinfo sasinfo None TD
    {| Opsem.CurFunction := PI_f pinfo;
       Opsem.CurBB := B1;
       Opsem.CurCmds := insn_store (SAS_sid1 pinfo sasinfo) t v v0 a:: cs1;
       Opsem.Terminator := tmn2;
       Opsem.Locals := lc2;
       Opsem.Allocas := als2 |}.
Proof. 
  unfold in_SAS_tail. simpl.
  intros. 
  unfold EC_follow_dead_store. simpl.
  split; intros J; auto.
    destruct J as [J1 [J2 J3]]; subst.
    unfold cs_follow_dead_store in J3.
    destruct sasinfo. simpl in *.
    destruct SAS_prop0 as [J4 [J5 J6]].
    destruct SAS_block0 as [? ? cs0 ?].
    destruct J6 as [cs2 [cs3 J6]]; subst.
    destruct (@J3 cs2 
                (insn_store SAS_sid4 (PI_typ pinfo) SAS_value4
                  (value_id (PI_id pinfo)) (PI_align pinfo) :: cs3)) as
      [csa [csb [J7 J8]]]; subst; auto.
    clear J3.
    simpl_env in J4. simpl_env in J7. rewrite <- J7 in J4.
    admit. (* uniqness *)
Qed.

Lemma SAS_sid1_is_in_SAS_tail: forall (pinfo : PhiInfo) (sasinfo : SASInfo pinfo)
  (tmn2 : terminator) (lc2 : Opsem.GVsMap) (als2 : list mblock) (los : layouts)
  (nts : namedts) (B : block) (align0 : align) (v1 : value) (cs : list cmd)
  (b' : Values.block)
  (Heq3 : exists l1 : l,
           exists ps1 : phinodes,
             exists cs11 : list cmd,
               B =
               block_intro l1 ps1
                 (cs11 ++
                  insn_store (SAS_sid1 pinfo sasinfo) 
                    (PI_typ pinfo) v1 (value_id (PI_id pinfo)) align0 :: cs)
                 tmn2)
  (H25 : lookupAL (GVsT DGVs) lc2 (PI_id pinfo) =
        ret ($ blk2GV (los, nts) b' # typ_pointer (PI_typ pinfo) $)) y
  (Hin: in_SAS_tail pinfo sasinfo y (los, nts)
     {|
     Opsem.CurFunction := PI_f pinfo;
     Opsem.CurBB := B;
     Opsem.CurCmds := cs;
     Opsem.Terminator := tmn2;
     Opsem.Locals := lc2;
     Opsem.Allocas := als2 |}),
  y = Some b'.
Proof.
  intros.
  destruct Hin as [J1 _]. simpl in *.
  rewrite H25 in J1. clear H25.
  apply J1. clear J1.
  destruct Heq3 as [l1 [ps1 [cs11 Heq3]]]. subst.
  split; auto. 
  assert (block_intro l1 ps1
            (cs11 ++
              insn_store (SAS_sid1 pinfo sasinfo) (PI_typ pinfo) v1
              (value_id (PI_id pinfo)) align0 :: cs) tmn2 = 
            SAS_block pinfo sasinfo) as EQ.
    admit. (* uniqness SAS *)
  simpl.
  split; auto.
    unfold cs_follow_dead_store.
    rewrite <- EQ.
    intros.
    clear - EQ H.
    destruct sasinfo. simpl in *.
    destruct SAS_prop0 as [J1 [J2 J3]].
    subst.
    destruct J3 as [cs5 [cs4 J3]].
    assert (cs11 = cs1 /\ cs = SAS_tail0 ++ cs3) as EQ'.
      admit. (* uniqness *)
    destruct EQ'; subst. clear H.
    assert (cs5 = cs1 /\ SAS_tail0 ++ 
             insn_store SAS_sid4 (PI_typ pinfo) SAS_value3
               (value_id (PI_id pinfo)) (PI_align pinfo) :: cs4 = cs3) as EQ'.
      admit. (* uniqness *)
    destruct EQ'; subst. clear J3.
    exists nil. exists SAS_tail0. simpl_env. auto.
Qed.

Lemma cmds_simulation_elim_cons_inv: forall (pinfo : PhiInfo) sasinfo
  (t : typ) (v1 v2: value) (a : align) (cs1 : list cmd) (cs2 : cmds)
  (Hcssim2 :
   cmds_simulation pinfo sasinfo (PI_f pinfo)
     (insn_store (SAS_sid1 pinfo sasinfo) t v1 v2 a :: cs1)
     cs2),
  cmds_simulation pinfo sasinfo (PI_f pinfo) cs1 cs2.
Proof.
  intros.
  unfold cmds_simulation in *.
  destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
  simpl in *.
  destruct (id_dec (SAS_sid1 pinfo sasinfo) (SAS_sid1 pinfo sasinfo));
    simpl in *; try congruence.
Qed.

Lemma cmds_simulation_nil_inv: forall pinfo sasinfo f1 cs,
  cmds_simulation pinfo sasinfo f1 nil cs -> cs = nil.
Proof.
  unfold cmds_simulation. simpl.
  intros. destruct (fdef_dec (PI_f pinfo) f1); auto.
Qed.

Lemma cmds_simulation_nelim_cons_inv: forall pinfo sasinfo F c cs2 cs',
  cmds_simulation pinfo sasinfo F (c :: cs2) cs' ->
  (PI_f pinfo = F -> getCmdLoc c <> SAS_sid1 pinfo sasinfo) ->
  exists cs2',
    cs' = c :: cs2' /\ cmds_simulation pinfo sasinfo F cs2 cs2'.
Proof.
  intros.
  unfold cmds_simulation in *.
  destruct (fdef_dec (PI_f pinfo) F); subst; simpl; eauto.
  assert (PI_f pinfo = PI_f pinfo) as EQ. auto.
  apply H0 in EQ.
  destruct (id_dec (getCmdLoc c) (SAS_sid1 pinfo sasinfo));
    simpl in *; try congruence.
  eauto.
Qed.

Lemma cs_follow_dead_store_isnt_nil: forall pinfo sasinfo,
  cs_follow_dead_store pinfo sasinfo nil -> False.
Proof.
  intros.
  unfold cs_follow_dead_store in H.
  destruct sasinfo. simpl in *.
  destruct SAS_block0.
  destruct SAS_prop0 as [J1 [J4 [cs1 [cs2 EQ]]]].
  apply H in EQ.
  destruct EQ as [csa [csb [EQ1 EQ2]]].
  symmetry in EQ1.
  apply app_eq_nil in EQ1. destruct EQ1 as [EQ11 EQ12]. inv EQ12.
Qed.

Lemma in_SAS_tail_nil: forall pinfo sasinfo TD F B tmn lc als,
  in_SAS_tail pinfo sasinfo None TD 
    {| Opsem.CurFunction := F;
       Opsem.CurBB := B;
       Opsem.CurCmds := nil;
       Opsem.Terminator := tmn;
       Opsem.Locals := lc;
       Opsem.Allocas := als |}.
Proof.
  intros.
  unfold in_SAS_tail. simpl. intros.
  split; intros J; auto.
    destruct J as [J1 [J2 J3]]. simpl in J1, J2, J3.
    eapply cs_follow_dead_store_isnt_nil in J3; eauto.
    inv J3.      
Qed.

Lemma cs_follow_dead_store_tail: forall pinfo sasinfo c cs,
  getCmdLoc c <> SAS_sid2 pinfo sasinfo ->
  cs_follow_dead_store pinfo sasinfo (c :: cs) ->
  cs_follow_dead_store pinfo sasinfo cs.
Proof.
  unfold cs_follow_dead_store.
  destruct sasinfo. simpl. intros.
  destruct SAS_block0.
  intros.
  destruct SAS_prop0 as [EQ1 [EQ2 [cs4 [cs2 EQ3]]]]; subst.
  assert (cs4 = cs1 /\
          cs3 = insn_store SAS_sid4 (PI_typ pinfo) SAS_value4
                  (value_id (PI_id pinfo)) (PI_align pinfo) :: cs2) as EQ.
    admit. (* uniqness *)
  destruct EQ as [EQ3 EQ4]; subst.
  edestruct H0 as [csa [csb [J1 J2]]]; subst; eauto.
  destruct csb.
    inv J1. contradict H; auto.

    inv J1. exists (csa++[c0]). exists csb. simpl_env. split; auto.
Qed.

Lemma cs_follow_dead_store_tail': forall pinfo sasinfo c cs
  (Hex: exists l0, exists ps0, exists tmn0, exists cs0,
          SAS_block pinfo sasinfo = block_intro l0 ps0 (cs0++c::cs) tmn0),
  getCmdLoc c <> SAS_sid1 pinfo sasinfo ->
  cs_follow_dead_store pinfo sasinfo cs ->
  cs_follow_dead_store pinfo sasinfo (c :: cs).
Proof.
  unfold cs_follow_dead_store.
  destruct sasinfo. simpl. intros.
  destruct SAS_block0.
  intros.
  destruct SAS_prop0 as [EQ1 [EQ2 [cs4 [cs2 EQ3]]]]; subst.
  assert (cs4 = cs1 /\
          cs3 = insn_store SAS_sid4 (PI_typ pinfo) SAS_value4
                  (value_id (PI_id pinfo)) (PI_align pinfo) :: cs2) as EQ.
    admit. (* uniqness *)
  destruct EQ as [EQ3 EQ4]; subst.
  apply_clear H0 in H1.
  destruct H1 as [csa [csb [J1 J2]]]; subst.
  destruct Hex as [l1 [ps0 [tmn0 [cs0 Hex]]]].
  inv Hex.
  simpl_env in H3.
  destruct csa.
    assert (c = insn_store SAS_sid3 (PI_typ pinfo) SAS_value3
                  (value_id (PI_id pinfo)) (PI_align pinfo)) as EQ.
      anti_simpl_env. auto.
    subst. simpl in H. congruence.

    assert (exists csa', c0 :: csa = csa' ++ [c]) as EQ.
      admit. (* list *)
    destruct EQ as [csa' EQ].
    rewrite EQ.
    exists csa'. exists (c::csb).
    simpl_env.
    split; auto.
Qed.

Lemma EC_follow_dead_store_tail: forall pinfo sasinfo c cs B tmn3 lc1 als3 als3'
  lc2 F (Heq: PI_f pinfo = F -> getCmdLoc c <> SAS_sid2 pinfo sasinfo),
  ~ EC_follow_dead_store pinfo sasinfo
      {| Opsem.CurFunction := F;
         Opsem.CurBB := B;
         Opsem.CurCmds := cs;
         Opsem.Terminator := tmn3;
         Opsem.Locals := lc1;
         Opsem.Allocas := als3 |} ->
  ~ EC_follow_dead_store pinfo sasinfo
      {| Opsem.CurFunction := F;
         Opsem.CurBB := B;
         Opsem.CurCmds := c :: cs;
         Opsem.Terminator := tmn3;
         Opsem.Locals := lc2;
         Opsem.Allocas := als3' |}.
Proof.
  intros.
  intro J. apply H.
  destruct J as [J1 [J2 J3]]. simpl in *.
  split; auto.
  split; auto.
    simpl.
    eapply cs_follow_dead_store_tail; eauto.
Qed.

Lemma EC_follow_dead_store_tail':forall pinfo sasinfo c cs B tmn3 lc1 als3 als3'
  lc2 F (Heq: PI_f pinfo = F -> getCmdLoc c <> SAS_sid2 pinfo sasinfo),
  EC_follow_dead_store pinfo sasinfo
      {| Opsem.CurFunction := F;
         Opsem.CurBB := B;
         Opsem.CurCmds := c :: cs;
         Opsem.Terminator := tmn3;
         Opsem.Locals := lc2;
         Opsem.Allocas := als3' |} ->
  EC_follow_dead_store pinfo sasinfo
      {| Opsem.CurFunction := F;
         Opsem.CurBB := B;
         Opsem.CurCmds := cs;
         Opsem.Terminator := tmn3;
         Opsem.Locals := lc1;
         Opsem.Allocas := als3 |}.
Proof.
  intros.
  destruct H as [J1 [J2 J3]]. simpl in *. subst.
  split; auto.
  split; auto.
    simpl.
    eapply cs_follow_dead_store_tail; eauto.
Qed.

Lemma EC_follow_dead_store_tail'':forall pinfo sasinfo c cs B tmn3 lc1 als3 als3'
  lc2 F
  (Hex: exists l0, exists ps0, exists cs0,
          B = block_intro l0 ps0 (cs0++c::cs) tmn3)
  (Heq: PI_f pinfo = F -> getCmdLoc c <> SAS_sid1 pinfo sasinfo),
  EC_follow_dead_store pinfo sasinfo
      {| Opsem.CurFunction := F;
         Opsem.CurBB := B;
         Opsem.CurCmds := cs;
         Opsem.Terminator := tmn3;
         Opsem.Locals := lc2;
         Opsem.Allocas := als3' |} ->
  EC_follow_dead_store pinfo sasinfo
      {| Opsem.CurFunction := F;
         Opsem.CurBB := B;
         Opsem.CurCmds := c::cs;
         Opsem.Terminator := tmn3;
         Opsem.Locals := lc1;
         Opsem.Allocas := als3 |}.
Proof.
  intros.
  destruct H as [J1 [J2 J3]]. simpl in *. subst.
  split; auto.
  split; auto.
    simpl.
    eapply cs_follow_dead_store_tail'; eauto.
    destruct Hex as [l0 [ps0 [cs0 Hex]]].
    rewrite Hex. eauto.
Qed.

Lemma cs_follow_dead_store_at_beginning_false: forall (pinfo : PhiInfo)
  (sasinfo : SASInfo pinfo) (l' : l) (ps' : phinodes) (cs' : cmds)
  (tmn' : terminator)
  (J2 : block_intro l' ps' cs' tmn' = SAS_block pinfo sasinfo)
  (J3 : cs_follow_dead_store pinfo sasinfo cs'),
  False.
Proof.
  intros.
  unfold cs_follow_dead_store in J3.
  rewrite <- J2 in J3.
  destruct sasinfo. simpl in *.
  rewrite <- J2 in SAS_prop0.
  destruct SAS_prop0 as [_ [_ [cs1 [cs3 J]]]].
  assert (J':=J).
  apply J3 in J.
  destruct J as [csa [csb [EQ1 EQ2]]]; subst.
  rewrite_env (
    (cs1 ++
     insn_store SAS_sid3 (PI_typ pinfo) SAS_value3
         (value_id (PI_id pinfo)) (PI_align pinfo) :: (csa ++ csb)) ++
     insn_store SAS_sid4 (PI_typ pinfo) SAS_value4
            (value_id (PI_id pinfo)) (PI_align pinfo) :: cs3
    ) in J'.
  apply app_inv_tail in J'.
  rewrite_env (nil ++ csb) in J'.
  rewrite_env (
    (cs1 ++
       insn_store SAS_sid3 (PI_typ pinfo) SAS_value3
         (value_id (PI_id pinfo)) (PI_align pinfo) ::
       csa) ++ csb
    ) in J'.
  apply app_inv_tail in J'.
  assert (
    In (insn_store SAS_sid3 (PI_typ pinfo) SAS_value3
         (value_id (PI_id pinfo)) (PI_align pinfo)) nil) as Hin.
    rewrite J'. apply in_middle.
  inv Hin.
Qed.

Lemma EC_follow_dead_store_at_begin_false: forall pinfo sasinfo F l' ps' cs' tmn'
  tmn lc2 als2,
  ~
  EC_follow_dead_store pinfo sasinfo
    {|
     Opsem.CurFunction := F;
     Opsem.CurBB := block_intro l' ps' cs' tmn';
     Opsem.CurCmds := cs';
     Opsem.Terminator := tmn;
     Opsem.Locals := lc2;
     Opsem.Allocas := als2 |}.
Proof.
  intros. intro J.
  destruct J as [J1 [J2 J3]]. simpl in *.
  eapply cs_follow_dead_store_at_beginning_false in J3; eauto.
Qed.

Lemma cs_follow_dead_store_at_end_false: forall (pinfo : PhiInfo)
  (sasinfo : SASInfo pinfo) (J3 : cs_follow_dead_store pinfo sasinfo nil),
  False.
Proof.
  intros.
  unfold cs_follow_dead_store in J3.
  destruct sasinfo. simpl in *. destruct SAS_block0.
  destruct SAS_prop0 as [_ [_ [cs1 [cs3 J]]]].
  assert (J':=J).
  apply J3 in J.
  destruct J as [csa [csb [EQ1 EQ2]]]; subst.
  assert (
    In (insn_store SAS_sid4 (PI_typ pinfo) SAS_value4
         (value_id (PI_id pinfo)) (PI_align pinfo)) nil) as Hin.
    rewrite EQ1. apply in_middle.
  inv Hin.
Qed.

Lemma EC_follow_dead_store_at_end_false: forall pinfo sasinfo F B tmn lc2 als2,
   ~
   EC_follow_dead_store pinfo sasinfo
     {|
     Opsem.CurFunction := F;
     Opsem.CurBB := B;
     Opsem.CurCmds := nil;
     Opsem.Terminator := tmn;
     Opsem.Locals := lc2;
     Opsem.Allocas := als2 |}.
Proof.
  intros. intro J.
  destruct J as [J1 [J2 J3]]. simpl in *.
  eapply cs_follow_dead_store_at_end_false in J3; eauto.
Qed.

Lemma fdef_sim__block_sim : forall pinfo sasinfo f1 f2 b1 b2 l0,
  fdef_simulation pinfo sasinfo f1 f2 ->
  lookupBlockViaLabelFromFdef f1 l0 = Some b1 ->
  lookupBlockViaLabelFromFdef f2 l0 = Some b2 ->
  block_simulation pinfo sasinfo f1 b1 b2.
Admitted. (* fsim -> bsim *)

Lemma remove_phinodes_eq: forall pinfo sasinfo l0 ps0 cs0 tmn0,
  WF_PhiInfo pinfo -> uniqFdef (PI_f pinfo) ->
  blockInFdefB (block_intro l0 ps0 cs0 tmn0) (PI_f pinfo) ->
  remove_phinodes (SAS_sid1 pinfo sasinfo) ps0 = ps0.
Admitted.  (* phi sim *)

Lemma block_simulation_inv : forall pinfo sasinfo F l1 ps1 cs1 tmn1 l2 ps2 cs2
  tmn2,
  WF_PhiInfo pinfo -> uniqFdef F ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) F ->
  block_simulation pinfo sasinfo F (block_intro l1 ps1 cs1 tmn1)
    (block_intro l2 ps2 cs2 tmn2) ->
  l1 = l2 /\ ps1 = ps2 /\
  cmds_simulation pinfo sasinfo F cs1 cs2 /\ tmn1 = tmn2.
Proof.
  intros.
  unfold block_simulation, cmds_simulation in *.
  destruct (fdef_dec (PI_f pinfo) F); inv H2; auto.
  erewrite remove_phinodes_eq; eauto.
Qed.

Lemma switchToNewBasicBlock_sim : forall TD l1 l2 ps cs1 cs2 tmn1 tmn2 B1 B2
  gl lc lc1 lc2 F pinfo sasinfo
  (H23 : @Opsem.switchToNewBasicBlock DGVs TD
          (block_intro l1 ps cs1 tmn1) B1 gl lc =
         ret lc1)
  (Hbsim2 : block_simulation pinfo sasinfo F B1 B2)
  (H2 : Opsem.switchToNewBasicBlock TD
         (block_intro l2 ps cs2 tmn2) B2 gl lc =
        ret lc2), lc1 = lc2.
Admitted. (* switch sim *)

Lemma switchToNewBasicBlock_mem_simulation: forall (pinfo : PhiInfo)
  (sasinfo : SASInfo pinfo) (gl2 : GVMap) (lc2 : Opsem.GVsMap)
  (als2 : list mblock) (M2 : mem) (los : layouts) (nts : namedts) (F : fdef)
  (B : block) tmn
  (EC : list Opsem.ExecutionContext) (Mem : mem) (cs' : cmds)
  (Hmsim : mem_simulation pinfo sasinfo (los, nts)
            ({|
             Opsem.CurFunction := F;
             Opsem.CurBB := B;
             Opsem.CurCmds := nil;
             Opsem.Terminator := tmn;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |} :: EC) Mem M2)
  (l'0 : l) (ps'0 : phinodes) (tmn'0 : terminator) (lc'0 : Opsem.GVsMap)
  (H2 : Opsem.switchToNewBasicBlock (los, nts)
         (block_intro l'0 ps'0 cs' tmn'0) B gl2 lc2 =
        ret lc'0),
  mem_simulation pinfo sasinfo (los, nts)
     ({|
      Opsem.CurFunction := F;
      Opsem.CurBB := block_intro l'0 ps'0 cs' tmn'0;
      Opsem.CurCmds := cs';
      Opsem.Terminator := tmn'0;
      Opsem.Locals := lc'0;
      Opsem.Allocas := als2 |} :: EC) Mem M2.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim3 Hmsim2]].
  split; auto.
  split; auto.
    intros.
    unfold sas_mem_inj in *. inv_mbind.
    intros.
    inv H.
    apply Hmsim2; auto. clear Hmsim2.
    constructor; auto. clear H5.
    unfold in_SAS_tail in *. simpl in *. 
    destruct H3 as [H31 H32].
    split.
      intros.
      apply EC_follow_dead_store_at_end_false in H.
      inv H.

      intro J.
      apply H32. apply EC_follow_dead_store_at_begin_false.
Qed.

Lemma unremovable_loc__neq__SAS_sid1: forall pinfo sasinfo F B c cs tmn2 lc2
  als2 EC Mem id0
  (Hnrem : ~ removable_State pinfo sasinfo
               {|Opsem.ECS := {| Opsem.CurFunction := F;
                                 Opsem.CurBB := B;
                                 Opsem.CurCmds := c :: cs;
                                 Opsem.Terminator := tmn2;
                                 Opsem.Locals := lc2;
                                 Opsem.Allocas := als2 |} :: EC;
                 Opsem.Mem := Mem |})
  (EQ : id0 = getCmdLoc c),
  PI_f pinfo = F -> id0 <> SAS_sid1 pinfo sasinfo.
Proof.
  simpl. intros.
  intro J. subst.
Admitted. (* removable neq *)

Lemma unremovable_loc__neq__SAS_sid2: forall pinfo sasinfo F B c cs tmn2 lc2
  als2 EC Mem id0
  (Hnst: match c with
         | insn_store _ _ _ _ _ => False
         | _ => True
         end)
  (Hnrem : ~ removable_State pinfo sasinfo
               {|Opsem.ECS := {| Opsem.CurFunction := F;
                                 Opsem.CurBB := B;
                                 Opsem.CurCmds := c :: cs;
                                 Opsem.Terminator := tmn2;
                                 Opsem.Locals := lc2;
                                 Opsem.Allocas := als2 |} :: EC;
                 Opsem.Mem := Mem |})
  (EQ : Some id0 = getCmdID c),
  PI_f pinfo = F -> id0 <> SAS_sid2 pinfo sasinfo.
Proof.
  simpl. intros.
  intro J. subst.
Admitted. (* removable neq *)

Lemma in_SAS_tail_update :
  forall pinfo sasinfo TD F B c cs tmn3 lc1 als3 als3' lc2 omb
  (Hneq: PI_f pinfo = F -> getCmdLoc c <> SAS_sid2 pinfo sasinfo)
  (Hneq': PI_f pinfo = F -> getCmdLoc c <> SAS_sid1 pinfo sasinfo)
  (Hex: exists l0, exists ps0, exists cs0,
          B = block_intro l0 ps0 (cs0++c::cs) tmn3)
  (Hp: PI_f pinfo = F -> 
       lookupAL (GVsT DGVs) lc2 (PI_id pinfo) =
         lookupAL (GVsT DGVs) lc1 (PI_id pinfo))
  (H1: in_SAS_tail pinfo sasinfo omb TD 
      {| Opsem.CurFunction := F;
         Opsem.CurBB := B;
         Opsem.CurCmds := cs;
         Opsem.Terminator := tmn3;
         Opsem.Locals := lc1;
         Opsem.Allocas := als3 |}),
  in_SAS_tail pinfo sasinfo omb TD
      {| Opsem.CurFunction := F;
         Opsem.CurBB := B;
         Opsem.CurCmds := c :: cs;
         Opsem.Terminator := tmn3;
         Opsem.Locals := lc2;
         Opsem.Allocas := als3' |}.
Proof.
  intros.
  destruct H1 as [H11 H12].
  split; simpl in *; intros H.
    assert (W:=H). destruct W as [W _]. simpl in W.
    rewrite Hp; try congruence.
    apply EC_follow_dead_store_tail' with (lc1:=lc1)(als3:=als3) in H; auto.
    apply H11; auto.

    apply H12.
    intro G. apply H.
    eapply EC_follow_dead_store_tail''; eauto.
Qed.

Lemma mem_simulation_update_locals :
  forall pinfo sasinfo TD F B c cs tmn3 lc1 lc2 als3 als3' ECs M1 M2
  (Hneq: PI_f pinfo = F -> getCmdLoc c <> SAS_sid2 pinfo sasinfo)
  (Hneq': PI_f pinfo = F -> getCmdLoc c <> SAS_sid1 pinfo sasinfo)
  (Hex: exists l0, exists ps0, exists cs0,
          B = block_intro l0 ps0 (cs0++c::cs) tmn3)
  (Hp: PI_f pinfo = F -> 
       lookupAL (GVsT DGVs) lc1 (PI_id pinfo) =
         lookupAL (GVsT DGVs) lc2 (PI_id pinfo))
  (Hmsim: mem_simulation pinfo sasinfo TD 
            ({| Opsem.CurFunction := F;
                Opsem.CurBB := B;
                Opsem.CurCmds := c::cs;
                Opsem.Terminator := tmn3;
                Opsem.Locals := lc1;
                Opsem.Allocas := als3 |} :: ECs) M1 M2),
  mem_simulation pinfo sasinfo TD 
    ({| Opsem.CurFunction := F;
        Opsem.CurBB := B;
        Opsem.CurCmds := cs;
        Opsem.Terminator := tmn3;
        Opsem.Locals := lc2;
        Opsem.Allocas := als3' |} :: ECs) M1 M2.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim3 Hmsim2]].
  split; auto.
  split; auto.
    unfold sas_mem_inj in *.
    inv_mbind. clear HeqR.
    intros ombs Hin.
    inv Hin.
    apply Hmsim2. clear Hmsim2.
    constructor; auto. clear H3.
    eapply in_SAS_tail_update; eauto.
Qed.

Lemma getEntryBlock__simulation: forall pinfo sasinfo f1 f2 b2,
  getEntryBlock f2 = Some b2 ->
  fdef_simulation pinfo sasinfo f1 f2 ->
  exists b1, getEntryBlock f1 = Some b1 /\ 
    block_simulation pinfo sasinfo f1 b1 b2.
Proof.
  unfold fdef_simulation.
  unfold block_simulation.
  intros.
  destruct (fdef_dec (PI_f pinfo) f1); inv H0; eauto.
    remember (PI_f pinfo) as R1.
    destruct R1 as [[? ? ? a ?] b]; simpl in *.
    destruct b; simpl in *; inv H.
    exists b. 
    split; auto.
Qed.

Lemma fdef_simulation__entry_block_simulation: forall pinfo sasinfo F1 F2 B1 B2,
  fdef_simulation pinfo sasinfo F1 F2 ->
  getEntryBlock F1 = ret B1 ->
  getEntryBlock F2 = ret B2 ->
  block_simulation pinfo sasinfo F1 B1 B2.
Proof.
  intros.
  eapply getEntryBlock__simulation in H1; eauto.
  destruct H1 as [b1 [J1 J2]].
  uniq_result. auto.
Qed.

Lemma fdef_simulation_inv: forall pinfo sasinfo fh1 fh2 bs1 bs2,
  fdef_simulation pinfo sasinfo (fdef_intro fh1 bs1) (fdef_intro fh2 bs2) ->
  fh1 = fh2 /\
  List.Forall2
    (fun b1 b2 =>
      block_simulation pinfo sasinfo (fdef_intro fh1 bs1) b1 b2) bs1 bs2.
Admitted. (* fsim *)

(*
Lemma undead_head_tail_cons_and: forall pinfo sasinfo ptr EC ECs,
  undead_head_tail pinfo sasinfo ptr (EC :: ECs) ->
  undead_head_in_tail pinfo sasinfo ptr EC /\
    undead_head_tail pinfo sasinfo ptr ECs.
Proof.
  intros.
  unfold undead_head_tail in *.
  split.
    apply H; simpl; auto.
    intros. apply H; simpl; auto.
Qed.
*)

Lemma callExternalFunction__mem_simulation_l2r: forall pinfo sasinfo 
  TD St1 M1 M2 fid0 gvss0 oresult1 M1' dck tr1 gl tret targs,
  mem_simulation pinfo sasinfo TD St1 M1 M2 ->
  callExternalOrIntrinsics TD gl M1 fid0 tret targs dck gvss0 =
    ret (oresult1, tr1, M1') ->
  exists M2', exists oresult2, exists tr2, 
    callExternalOrIntrinsics TD gl M2 fid0 tret targs dck gvss0 =
      ret (oresult2, tr2, M2') /\
    oresult1 = oresult2 /\ mem_simulation pinfo sasinfo TD St1 M1' M2' /\ 
    tr1 = tr2.
Admitted. (* excall sim *)

Lemma callExternalFunction__mem_simulation: forall pinfo sasinfo TD St1 M1 M2
  fid0 gvss0 oresult1 M1' oresult2 M2' dck tret targs gl tr1 tr2,
  mem_simulation pinfo sasinfo TD St1 M1 M2 ->
  callExternalOrIntrinsics TD gl M1 fid0 tret targs dck gvss0 = 
    ret (oresult1, tr1, M1') ->
  callExternalOrIntrinsics TD gl M2 fid0 tret targs dck gvss0 = 
    ret (oresult2, tr2, M2') ->
  oresult1 = oresult2 /\ mem_simulation pinfo sasinfo TD St1 M1' M2' /\ 
    tr1 = tr2.
Proof.
  intros.
  eapply callExternalFunction__mem_simulation_l2r in H; eauto.
  destruct H as [M2'' [oresult2' [tr2' [J1 [J2 [J3 J4]]]]]]; subst.
  uniq_result. auto.
Qed.

Ltac destruct_ctx_other :=
match goal with
| Hwfcfg: OpsemPP.wf_Config _,
  Hwfpp : OpsemPP.wf_State
            {|
            OpsemAux.CurSystem := _;
            OpsemAux.CurTargetData := ?TD;
            OpsemAux.CurProducts := _;
            OpsemAux.Globals := _;
            OpsemAux.FunTable := _
             |} _,
  Hnoalias : Promotability.wf_State _ _ _ _,
  Hsim : State_simulation _ _ _ _ ?Cfg2 ?St2 ,
  Hop2 : Opsem.sInsn _ _ _ _ |- _ =>
  destruct TD as [los nts];
  destruct Hwfcfg as [_ [Hwfg [HwfSystem HmInS]]];
  destruct Hwfpp as 
    [_ [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 _]]]] 
     [ _ HwfCall'
     ]]
    ]; subst;
  destruct Cfg2 as [S2 TD2 Ps2 gl2 fs2];
  destruct St2 as [ECs2 M2];
  simpl in Hsim;
  destruct Hsim as [EQ1 [Hpsim [Hstksim [EQ2 [EQ3 Hmsim]]]]]; subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2]; tinv Hstksim;
  destruct Hstksim as [Hecsim Hstksim];
  unfold EC_simulation in Hecsim;
  destruct Hecsim as 
      [Hfsim2 [Heq1 [Heq2 [Hbsim2 
        [Heq3 [Heq4 [Hlcsim2 Hcssim2]]]]]]]; subst;
  destruct Hnoalias as 
    [
      [[Hinscope' _] [HwfECs' HwfHT]] 
      [[Hdisjals _] HwfM]
    ]; simpl in Hdisjals;
  fold Promotability.wf_ECStack in HwfECs'
end.

Ltac destruct_ctx_return :=
match goal with
| Hwfcfg: OpsemPP.wf_Config _,
  Hwfpp : OpsemPP.wf_State
            {|
            OpsemAux.CurSystem := _;
            OpsemAux.CurTargetData := ?TD;
            OpsemAux.CurProducts := _;
            OpsemAux.Globals := _;
            OpsemAux.FunTable := _
             |} _,
  Hnoalias : Promotability.wf_State _ _ _ _,
  Hsim : State_simulation _ _ _ _ ?Cfg2 ?St2 ,
  Hop2 : Opsem.sInsn _ _ _ _ |- _ =>
  destruct TD as [los nts];
  destruct Hwfcfg as [_ [Hwfg [HwfSystem HmInS]]];
  destruct Hwfpp as 
    [_ [
     [Hreach1 [HBinF1 [HFinPs1 _]]] 
     [ 
       [
         [Hreach2 [HBinF2 [HFinPs2 _]]]
         _
       ]
       HwfCall'
     ]]
    ]; subst;
  destruct Cfg2 as [S2 TD2 Ps2 gl2 fs2];
  destruct St2 as [ECs2 M2];
  simpl in Hsim;
  destruct Hsim as [EQ1 [Hpsim [Hstksim [EQ2 [EQ3 Hmsim]]]]]; subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2]; tinv Hstksim;
  destruct Hstksim as [Hecsim Hstksim];
  destruct ECs2 as [|[F3 B3 cs3 tmn3 lc3 als3] ECs2]; tinv Hstksim;
  destruct Hstksim as [Hecsim' Hstksim];
  unfold EC_simulation in Hecsim;
  destruct Hecsim as 
      [Hfsim2 [Heq1 [Heq2 [Hbsim2 
        [Heq3 [Heq4 [Hlcsim2 Hcssim2]]]]]]]; subst;
  destruct Hecsim' as 
      [Hfsim2' [Htsim2' [Heq2' [Hbsim2' 
        [Heq3' [Heq4' [Hlcsim2' Hcssim2']]]]]]]; subst;
  destruct Hnoalias as 
    [
      [[Hinscope1' _] [[[Hinscope2' _] [HwfECs' _]] _]] 
      [[Hdisjals _] HwfM]
    ]; simpl in Hdisjals;
  fold Promotability.wf_ECStack in HwfECs';
  apply cmds_simulation_nil_inv in Hcssim2; subst;
  wfCall_inv;
  apply cmds_simulation_nelim_cons_inv in Hcssim2'; try solve [
    auto |
    try match goal with
        | |- _ = _ -> _ <> _ => admit (* rid <> pid *)
        end ];
  destruct Hcssim2' as [cs3' [Heq Hcssim2']]; subst;
  inv Hop2;
  uniq_result
end.

Lemma mem_simulation__free : forall TD Mem1 Mem2 Mem1' Mem2'
  ECs1 pinfo sasinfo EC EC' ptr
  (Hp: forall omb,
       in_SAS_tail pinfo sasinfo omb TD EC' ->
       in_SAS_tail pinfo sasinfo omb TD EC)
  (Hmsim : mem_simulation pinfo sasinfo TD 
             (EC :: ECs1) Mem1 Mem2)
  (Hmlc: free TD Mem1 ptr = ret Mem1')
  (Hmlc': free TD Mem2 ptr = ret Mem2'),
  mem_simulation pinfo sasinfo TD (EC' :: ECs1) Mem1' Mem2'.
Proof.
  intros.
  destruct Hmsim as [J1 [J2 J3]].
  apply free_inv in Hmlc.
  apply free_inv in Hmlc'.
  destruct Hmlc as [blk [ofs [hi [lo [H1 [H2 [H3 H4]]]]]]].
  destruct Hmlc' as [blk' [ofs' [hi' [lo' [H1' [H2' [H3' H4']]]]]]].
  unfold GV2ptr in *.
  destruct ptr as [|[[]][]]; inv H1. inv H1'.
  split.
    apply Mem.nextblock_free in H4'.
    apply Mem.nextblock_free in H4. 
    congruence.
  split.
    intros.
    apply Mem.bounds_free with (b:=b) in H4'; auto.
    apply Mem.bounds_free with (b:=b) in H4; auto.
    congruence.

    unfold sas_mem_inj in *.
    inv_mbind.
    intros ombs Hin'.
    assert (in_SAS_tails pinfo sasinfo ombs TD (EC :: ECs1)) as Hin.
      inv Hin'.
      constructor; auto.
    apply J3 in Hin.
    eapply SASmsim.free_inj with (delta:=0)(b1:=blk')(b2:=blk') in Hin; 
      eauto using SASmsim.inject_id_no_overlap, SASmsim.inject_id_zero_delta.
    replace (lo+0) with lo by omega.
    replace (hi+0) with hi by omega. 
    rewrite J2 in H3. rewrite <- H3' in H3. inv H3. auto.
Qed.

Lemma list_suffix_dec: forall A (Hdec: forall (x y : A), {x = y}+{x <> y})
  (l1 l2: list A), (exists l3, l1 = l3 ++ l2) \/ (~ exists l3, l1 = l3 ++ l2).
Admitted. (* list *)

Lemma cs_follow_dead_store_dec: forall (pinfo : PhiInfo) 
  (sasinfo : SASInfo pinfo) (EC : @Opsem.ExecutionContext DGVs)
  (Ha : Opsem.CurFunction EC = PI_f pinfo)
  (Hb : Opsem.CurBB EC = SAS_block pinfo sasinfo),
  cs_follow_dead_store pinfo sasinfo (Opsem.CurCmds EC) \/
    ~ cs_follow_dead_store pinfo sasinfo (Opsem.CurCmds EC).
Proof.
  destruct EC. simpl. destruct sasinfo.
  simpl. destruct pinfo. simpl in *.
  intros. subst.
  unfold sas in SAS_prop0. simpl in *.
  destruct SAS_prop0 as [J1 [J2 J3]].
  destruct SAS_block0.
  destruct J3 as [cs1 [cs3 J3]]; subst. 
  unfold cs_follow_dead_store. simpl.
  clear.
  destruct (@list_suffix_dec _ cmd_dec CurCmds
    (insn_store SAS_sid4 PI_typ SAS_value4 (value_id PI_id) PI_align :: cs3))
    as [J | J].
    destruct J as [l3 J]; subst.
    destruct (@list_suffix_dec _ cmd_dec SAS_tail0 l3) as [J' | J'].
      destruct J' as [l4 J']; subst.
      left.
      intros.
      assert (cs2=insn_store SAS_sid4 PI_typ SAS_value4 (value_id PI_id) PI_align
                    :: cs3 ) as EQ.
        admit. (* uniqness *)
      subst.
      exists l4. exists l3. auto.

      right.
      intro J.
      destruct (@J cs1 
                   (insn_store SAS_sid4 PI_typ SAS_value4 
                     (value_id PI_id) PI_align :: cs3))
        as [csa1 [csb1 [J1 J2]]]; subst; auto.
      clear J.
      assert (l3 = csb1) as EQ. admit. (* list *)
      subst.
      apply J'. exists csa1. auto.

    right.
    intro J'.
    destruct (@J' cs1 
                  (insn_store SAS_sid4 PI_typ SAS_value4 
                    (value_id PI_id) PI_align :: cs3))
      as [csa1 [csb1 [J1 J2]]]; subst; auto.
    clear J'.
    apply J. exists csb1. auto.
Qed.

Lemma EC_follow_dead_store_dec: forall pinfo sasinfo EC, 
  EC_follow_dead_store pinfo sasinfo EC \/ 
    ~ EC_follow_dead_store pinfo sasinfo EC.
Proof.
  intros.
  unfold EC_follow_dead_store.
  destruct (fdef_dec (Opsem.CurFunction EC) (PI_f pinfo)); 
    try solve [right; tauto].
  destruct (block_dec (Opsem.CurBB EC) (SAS_block pinfo sasinfo)); 
    try solve [right; tauto].
  destruct (cs_follow_dead_store_dec pinfo sasinfo EC e e0);
    try solve [right; tauto | auto].
Qed.

Lemma in_SAS_tail_ex: forall pinfo sasinfo TD EC,
  exists omb, in_SAS_tail pinfo sasinfo omb TD EC.
Proof.
  unfold in_SAS_tail.
  intros.
  destruct (@EC_follow_dead_store_dec pinfo sasinfo EC).
    destruct (lookupAL (GVsT DGVs) (Opsem.Locals EC) (PI_id pinfo)) 
      as [[|[[]][]]|]; eauto.
    exists (Some b). tauto.

    destruct (lookupAL (GVsT DGVs) (Opsem.Locals EC) (PI_id pinfo)) 
      as [[|[[]][]]|]; eauto.
    exists None. tauto.
Qed.

Lemma in_SAS_tails_ex: forall pinfo sasinfo TD ECs,
  exists ombs, in_SAS_tails pinfo sasinfo ombs TD ECs.
Proof.
  unfold in_SAS_tails.
  induction ECs; simpl; eauto.
    destruct IHECs as [ombs IHECs].
    destruct (@in_SAS_tail_ex pinfo sasinfo TD a) as [omb J].
    exists (omb::ombs). constructor; auto.
Qed.

Lemma mem_simulation__free_l2r' : forall TD Mem1 Mem2 Mem1' ECs pinfo sasinfo ptr
  (Hmsim : mem_simulation pinfo sasinfo TD ECs Mem1 Mem2)
  (Hmlc: free TD Mem1 ptr = ret Mem1'),
  exists Mem2', free TD Mem2 ptr = ret Mem2'.
Proof.
  intros.
  destruct Hmsim as [J1 [J2 J3]].
  apply free_inv in Hmlc.
  destruct Hmlc as [blk [ofs [hi [lo [H1 [H2 [H3 H4]]]]]]].
  unfold sas_mem_inj in *.
  inv_mbind.
  destruct (@in_SAS_tails_ex pinfo sasinfo TD ECs) as [ombs J].
  apply_clear J3 in J.
  eapply SASmsim.free_inj_l2r with (delta:=0)(b1:=blk)(b2:=blk) in J; 
      eauto using SASmsim.inject_id_no_overlap, SASmsim.inject_id_zero_delta.
  destruct J as [m2' [J3 J4]].
  exists m2'.
  unfold free. fill_ctxhole. rewrite H2. rewrite <- J2. rewrite <- H3.
  replace (lo+0) with lo in J3 by omega.
  replace (hi+0) with hi in J3 by omega. 
  destruct (zeq 0 0); auto. congruence.
Qed.

Lemma mem_simulation__free_l2r : forall TD Mem1 Mem2 Mem1'
  ECs1 pinfo sasinfo EC EC' ptr
  (Hp: forall omb,
       in_SAS_tail pinfo sasinfo omb TD EC' ->
       in_SAS_tail pinfo sasinfo omb TD EC)
  (Hmsim : mem_simulation pinfo sasinfo TD (EC :: ECs1) Mem1 Mem2)
  (Hmlc: free TD Mem1 ptr = ret Mem1'),
  exists Mem2',
    free TD Mem2 ptr = ret Mem2' /\
    mem_simulation pinfo sasinfo TD (EC' :: ECs1) Mem1' Mem2'.
Proof.
  intros.
  assert (Hmsim':=Hmsim).
  eapply mem_simulation__free_l2r' in Hmsim'; eauto.
  destruct Hmsim' as [Mem2' Hfree'].
  exists Mem2'.
  split; auto.
    eapply mem_simulation__free; eauto.
Qed.

Lemma in_SAS_tails__replace_head: forall TD EC' EC ECs1 ombs pinfo sasinfo
  (Hp : forall omb : monad mblock,
        in_SAS_tail pinfo sasinfo omb TD EC' ->
        in_SAS_tail pinfo sasinfo omb TD EC)
  (H1: in_SAS_tails pinfo sasinfo ombs TD (EC' :: ECs1)),
  in_SAS_tails pinfo sasinfo ombs TD (EC :: ECs1).
Proof.
  intros. inv H1. constructor; auto.
Qed.

Lemma mem_simulation__replace_head: forall TD ECs1 pinfo sasinfo EC EC'
  (Hp : forall omb : monad mblock,
        in_SAS_tail pinfo sasinfo omb TD EC' ->
        in_SAS_tail pinfo sasinfo omb TD EC) M1 M2
  (Hmsim : mem_simulation pinfo sasinfo TD (EC :: ECs1) M1 M2),
  mem_simulation pinfo sasinfo TD (EC' :: ECs1) M1 M2.
Proof.
  intros.
  destruct Hmsim as [J1 [J2 J3]].
  split; auto.
  split; auto.
    unfold sas_mem_inj in *.
    inv_mbind.
    intros ombs Hin'.
    eapply in_SAS_tails__replace_head in Hin'; eauto.
Qed.

Lemma mem_simulation__free_allocas : forall TD ECs1 pinfo sasinfo EC EC'
  (Hp: forall omb,
       in_SAS_tail pinfo sasinfo omb TD EC' ->
       in_SAS_tail pinfo sasinfo omb TD EC)
  als Mem1 Mem2 Mem1' Mem2'
  (Hmsim : mem_simulation pinfo sasinfo TD 
             (EC :: ECs1) Mem1 Mem2)
  (Hmlc: free_allocas TD Mem1 als = ret Mem1')
  (Hmlc': free_allocas TD Mem2 als = ret Mem2'),
  mem_simulation pinfo sasinfo TD (EC' :: ECs1) Mem1' Mem2'.
Proof.
  induction als; simpl; intros.
    uniq_result. 
    eapply mem_simulation__replace_head; eauto.

    inv_mbind.
    eapply mem_simulation__free with (Mem1':=m0)(Mem2':=m) in Hmsim; eauto.
Qed.

Lemma mem_simulation__remove_head: forall TD ECs1 pinfo sasinfo EC 
  (Hp : in_SAS_tail pinfo sasinfo None TD EC) M1 M2
  (Hmsim : mem_simulation pinfo sasinfo TD (EC :: ECs1) M1 M2),
  mem_simulation pinfo sasinfo TD ECs1 M1 M2.
Proof.
  intros.
  destruct Hmsim as [J1 [J2 J3]].
  split; auto.
  split; auto.
    unfold sas_mem_inj in *.
    inv_mbind.
    intros ombs Hin'.
    replace (ombs__ignores (Size.to_Z n) ombs) with
            (ombs__ignores (Size.to_Z n) (None::ombs)) by auto.
    apply J3; auto.
      constructor; auto.
Qed.

Lemma mem_simulation__return: forall (pinfo : PhiInfo) (sasinfo : SASInfo pinfo)
  (lc2 : Opsem.GVsMap) (als2 : list mblock) (tmn3 : terminator) t0 v0 
  (lc3 : Opsem.GVsMap) (als3 : list mblock) (M2 : mem) (los : layouts) 
  (nts : namedts) (F : fdef) (rid : id) tmn (F' : fdef) (B' : block) (i0 : id)
  (n : noret) (c : clattrs) (v : value) (p : params) (cs' : list cmd)
  (EC : list Opsem.ExecutionContext) (Mem : mem) (l3 : l) (ps3 : phinodes)
  (cs0 : list cmd) (Mem' : mem)
  (H0 : free_allocas (los, nts) Mem als2 = ret Mem')
  (Heq3' : exists l1 : l,
            exists ps1 : phinodes,
              exists cs11 : list cmd,
                B' =
                block_intro l1 ps1 (cs11 ++ insn_call i0 n c t0 v0 v p :: cs')
                  tmn3)
  (Hmsim : mem_simulation pinfo sasinfo (los, nts)
            ({|
             Opsem.CurFunction := F;
             Opsem.CurBB := block_intro l3 ps3 (cs0 ++ nil) tmn;
             Opsem.CurCmds := nil;
             Opsem.Terminator := tmn;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |}
             :: {|
                Opsem.CurFunction := F';
                Opsem.CurBB := B';
                Opsem.CurCmds := insn_call i0 n c t0 v0 v p :: cs';
                Opsem.Terminator := tmn3;
                Opsem.Locals := lc3;
                Opsem.Allocas := als3 |} :: EC) Mem M2)
  (Mem'0 : mem) (lc''0 : Opsem.GVsMap)
  (EQ: lookupAL (GVsT DGVs) lc3 (PI_id pinfo) =
         lookupAL (GVsT DGVs) lc''0 (PI_id pinfo))
  (H26 : free_allocas (los, nts) M2 als2 = ret Mem'0),
  mem_simulation pinfo sasinfo (los, nts)
     ({|
      Opsem.CurFunction := F';
      Opsem.CurBB := B';
      Opsem.CurCmds := cs';
      Opsem.Terminator := tmn3;
      Opsem.Locals := lc''0;
      Opsem.Allocas := als3 |} :: EC) Mem' Mem'0.
Proof.
  intros.
  eapply mem_simulation__free_allocas in Hmsim; eauto.
  apply mem_simulation__remove_head in Hmsim.
    eapply mem_simulation_update_locals in Hmsim; eauto.
      admit. (* id <> sid2 *)
      admit. (* id <> sid1 *)
    apply in_SAS_tail_nil.
Qed. 

Lemma mem_simulation__malloc: forall (pinfo : PhiInfo) (sasinfo : SASInfo pinfo)
  (tmn2 : terminator) (lc2 : Opsem.GVsMap) (als2 als2': list mblock)
  (M2 : mem) (los : layouts) (nts : namedts) (F : fdef) (B : block) c align0
  (EC : list Opsem.ExecutionContext) t id0 (Hid: getCmdID c = Some id0)
  (cs : list cmd) (Mem : mem) (gn : GenericValue) (Mem' : mem) (mb : mblock)
  (Heq3 : exists l1 : l,
           exists ps1 : phinodes,
             exists cs11 : list cmd,
               B =
               block_intro l1 ps1 (cs11 ++ c :: cs)
                 tmn2)
  (Hmalloc: match c with
            | insn_malloc _ _ _ _ | insn_alloca _ _ _ _ => True
            | _ => False
            end) (Hwfpi: WF_PhiInfo pinfo)
  (Hexeq: exists l1 : l, exists ps1 : phinodes,exists cs11 : list cmd,
              B = block_intro l1 ps1 (cs11 ++ c :: cs) tmn2)
  (HBinF: blockInFdefB B F = true) (Huniq: uniqFdef F)
  (Hpalloca : palloca_props.wf_State pinfo
                ({| Opsem.ECS := {|
                         Opsem.CurFunction := F;
                         Opsem.CurBB := B;
                         Opsem.CurCmds := c :: cs;
                         Opsem.Terminator := tmn2;
                         Opsem.Locals := lc2;
                         Opsem.Allocas := als2 |} :: EC;
                    Opsem.Mem := Mem |}))
  (Hmsim : mem_simulation pinfo sasinfo (los, nts)
            ({|
             Opsem.CurFunction := F;
             Opsem.CurBB := B;
             Opsem.CurCmds := c :: cs;
             Opsem.Terminator := tmn2;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |} :: EC) Mem M2)
  (Hnrem : ~
          removable_State pinfo sasinfo
            {|
            Opsem.ECS := {|
                         Opsem.CurFunction := F;
                         Opsem.CurBB := B;
                         Opsem.CurCmds := c :: cs;
                         Opsem.Terminator := tmn2;
                         Opsem.Locals := lc2;
                         Opsem.Allocas := als2 |} :: EC;
            Opsem.Mem := Mem |})
  (Mem'0 : mem) (tsz0 : sz)
  (H2 : malloc (los, nts) Mem tsz0 gn align0 = ret (Mem', mb))
  (H25 : malloc (los, nts) M2 tsz0 gn align0 = ret (Mem'0, mb)),
  mem_simulation pinfo sasinfo (los, nts)
     ({|
      Opsem.CurFunction := F;
      Opsem.CurBB := B;
      Opsem.CurCmds := cs;
      Opsem.Terminator := tmn2;
      Opsem.Locals := updateAddAL (GVsT DGVs) lc2 id0
                        ($ blk2GV (los, nts) mb # typ_pointer t $);
      Opsem.Allocas := als2' |} :: EC) Mem' Mem'0.
Proof.
  intros.
    destruct Hmsim as [Hmsim1 [Hmim3 Hmsim2]].
    split.
      apply MemProps.nextblock_malloc in H2.
      apply MemProps.nextblock_malloc in H25.
      rewrite <- H2. rewrite <- H25. rewrite Hmsim1. auto.
    split.  
      apply MemProps.bounds_malloc in H2.
      apply MemProps.bounds_malloc in H25.
      destruct H2 as [n [H21 H22]].
      destruct H25 as [n' [H25 H26]].
      rewrite H21 in H25. inv H25.
      intro b.
      rewrite H26. rewrite H22.
      destruct (eq_block b mb); auto.

      unfold sas_mem_inj in *.
      inv_mbind. clear HeqR.
      intros ombs Hin'. 
      apply malloc_inv in H2. destruct H2 as [n0 [J1 [J2 J3]]].
      apply malloc_inv in H25. destruct H25 as [n0' [J1' [J2' J3']]].
      rewrite J1 in J1'. inv J1'.
      eapply SASmsim.alloc_inject_id_inj with (m1:=Mem)(m2:=M2); eauto.
      assert (ret getCmdLoc c = getCmdID c) as G.
        erewrite getCmdLoc_getCmdID; eauto.
      destruct (id_dec id0 (PI_id pinfo)); subst.
        destruct c; tinv Hmalloc; simpl in *; inv Hid.
          admit. (* malloc <> pid *)

          inv Hin'.
          assert (in_SAS_tails pinfo sasinfo (None::l') (los, nts)
             ({|
              Opsem.CurFunction := F;
              Opsem.CurBB := B;
              Opsem.CurCmds := insn_alloca (PI_id pinfo) t0 v a :: cs;
              Opsem.Terminator := tmn2;
              Opsem.Locals := lc2;
              Opsem.Allocas := als2 |} :: EC)) as Hin.
            unfold in_SAS_tails.
            constructor; auto.
              split; simpl; intros; auto.
                destruct H as [H _]. simpl in H. subst.
                assert (lookupAL (GVsT DGVs) lc2 (PI_id pinfo) = None) as Hnone.
                  clear - Hpalloca Hwfpi HBinF Huniq Hexeq.
                  eapply WF_PhiInfo_spec15 in Hpalloca; eauto.
                rewrite Hnone. auto.
           apply_clear Hmsim2 in Hin.
           simpl in Hin. 
           simpl.
           destruct y; auto.
             simpl_env.
             apply SASmsim.mem_inj_ignores_weaken; auto.

        apply Hmsim2.
        eapply in_SAS_tails__replace_head in Hin'; eauto.
        intros.
        apply in_SAS_tail_update with 
          (lc1:=updateAddAL (GVsT DGVs) lc2 id0
                ($ blk2GV (los, nts) mb # typ_pointer t $)) (als3:=als2); 
          eauto using unremovable_loc__neq__SAS_sid1.
          eapply unremovable_loc__neq__SAS_sid2; eauto.
            destruct c; tinv Hmalloc; auto.
          rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma in_SAS_tail__wf_ECStack_head_in_tail__no_alias_with_blk: forall
  (pinfo : PhiInfo) (sasinfo : SASInfo pinfo) (lc2 : AssocList (GVsT DGVs))
  (gv2 : GVsT DGVs) S los nts Ps (Mem : Mem.mem) F t v gl
  (Hwfv: wf_value S (module_intro los nts Ps) F v t)
  (maxb : Values.block) (Hget : getOperandValue (los,nts) v lc2 gl = ret gv2)
  (EC : Opsem.ExecutionContext) (mb : mblock)
  (H : in_SAS_tail pinfo sasinfo (ret mb) (los,nts) EC)
  (Hwfg: MemProps.wf_globals maxb gl)
  (Hnals1 : 
    Promotability.wf_ECStack_head_in_tail maxb pinfo (los,nts) Mem lc2 EC),
  MemProps.no_alias_with_blk gv2 mb.
Proof.
  intros.
  destruct H as [H1 H2]. simpl in *.
  unfold Promotability.wf_ECStack_head_in_tail in Hnals1.
  destruct (@EC_follow_dead_store_dec pinfo sasinfo EC) as [J | J].
    assert (G:=J).
    destruct G as [J1 [J2 J3]]. simpl in *. subst.
    apply_clear H1 in J.
    remember (lookupAL (GVsT DGVs) (Opsem.Locals EC) (PI_id pinfo)) as R.
    destruct R as [[|[[]][]]|]; tinv J.
    inv J. symmetry in HeqR.
    eapply wf_ECStack_head_in_tail__no_alias_with_blk; eauto.
    
    apply_clear H2 in J. congruence.
Qed.

Lemma in_SAS_tails__wf_ECStack_head_tail__no_alias_with_blk: 
  forall pinfo sasinfo lc2 gv2 los nts Mem maxb size Ps F t gl
  (Hwfg: MemProps.wf_globals maxb gl) v S
  (Hwfv: wf_value S (module_intro los nts Ps) F v t)
  (Hget : getOperandValue (los,nts) v lc2 gl = ret gv2) EC ombs
  (Hsas: in_SAS_tails pinfo sasinfo ombs (los,nts) EC)
  (Hnals: Promotability.wf_ECStack_head_tail maxb pinfo (los,nts) Mem lc2 EC),
  List.Forall (fun re => 
               let '(mb,_,_) := re in
               MemProps.no_alias_with_blk gv2 mb) (ombs__ignores size ombs).
Proof.
  intros.
  induction Hsas; simpl; intros; auto.
    apply Promotability.wf_ECStack_head_tail_cons__inv in Hnals.
    destruct Hnals as [Hnals1 Hals2].
    apply_clear IHHsas in Hals2.
    destruct y as [mb|]; auto.
    constructor; auto.
    eapply in_SAS_tail__wf_ECStack_head_in_tail__no_alias_with_blk; eauto.
Qed.

Lemma unused_pid_in_SAS_tail__wf_defs__no_alias_with_blk: forall pinfo F los nts 
  maxb Mem lc2 EC gv2 als2
  (Hinscope: if fdef_dec (PI_f pinfo) F
             then Promotability.wf_defs maxb pinfo (los,nts) Mem lc2 als2
             else True)
  gl (Hwfg: MemProps.wf_globals maxb gl) v S t Ps
  (Hwfv: wf_value S (module_intro los nts Ps) F v t)
  (Hget : getOperandValue (los,nts) v lc2 gl = ret gv2) mb
  (Hneq: used_in_value (PI_id pinfo) v = false)
  (Heq1: Opsem.CurFunction EC = F) (Heq2: Opsem.Locals EC = lc2)
  (Heq3: Opsem.Allocas EC = als2) sasinfo
  (Hsas: in_SAS_tail pinfo sasinfo (Some mb) (los,nts) EC),
  MemProps.no_alias_with_blk gv2 mb.
Proof.
  intros.
  destruct Hsas as [J1 J2].
  destruct (@EC_follow_dead_store_dec pinfo sasinfo EC) as [J | J].
    assert (G:=J).
    destruct G as [J4 [J5 J3]]. simpl in *. subst.
    destruct (fdef_dec (PI_f pinfo) (Opsem.CurFunction EC)); try congruence.
    apply_clear J1 in J.
    remember (lookupAL (GVsT DGVs) (Opsem.Locals EC) (PI_id pinfo)) as R.
    destruct R as [[|[[]][]]|]; inv J.
    clear J2. symmetry in HeqR.
    eapply wf_defs__no_alias_with_blk; eauto.
    
    apply_clear J2 in J. congruence.
Qed.

Lemma load_in_cmds_true: forall id1 id0 t align0 csb csa,
  load_in_cmds id1 (csa ++ insn_load id0 t (value_id id1) align0 :: csb) = true.
Proof.
  unfold load_in_cmds.
  intros.
  generalize false.
  induction csa; simpl; intros; eauto.
    destruct (id_dec id1 id1); try congruence. 
    simpl.
    rewrite orb_true_intro; auto.
    apply fold_left_or_spec.
    intros. subst. auto.
Qed.

Lemma load_pid_isnt_in_SAS_tail: forall pinfo sasinfo TD v t id0 align0 cs EC 
  (Hneq: used_in_value (PI_id pinfo) v = true)
  (Heq: Opsem.CurCmds EC = insn_load id0 t v align0 :: cs),
  in_SAS_tail pinfo sasinfo None TD EC.
Proof.
  unfold in_SAS_tail.
  simpl. intros.
  destruct v; inv Hneq.
  destruct (id_dec i0 (PI_id pinfo)); subst; inv H0.
  destruct (@EC_follow_dead_store_dec pinfo sasinfo EC) as [J | J].
    elimtype False.
    destruct J as [J1 [J2 J3]].
    unfold cs_follow_dead_store in J3.
    destruct sasinfo. simpl in *.
    destruct SAS_prop0 as [J4 [J5 J6]].
    destruct SAS_block0 as [? ? cs0 ?].
    destruct J6 as [cs2 [cs3 J6]]; subst. simpl in *.
    destruct (@J3 cs2 (insn_store SAS_sid4 (PI_typ pinfo) SAS_value4
                         (value_id (PI_id pinfo)) (PI_align pinfo) :: cs3)) as
      [csa [csb [J7 J6]]]; subst; auto. clear J3.
    rewrite Heq in J7.
    destruct csb; inv J7.
    rewrite load_in_cmds_true in J5. congruence.

    split; intro; auto.
      congruence.
Qed.
    
Lemma in_SAS_tails__notin_ignores_with_size': forall maxb pinfo sasinfo 
  los nts Mem lc2 EC gl
  (Hnals: Promotability.wf_ECStack_head_tail maxb pinfo (los,nts) Mem lc2 EC)
  (Hwfg: MemProps.wf_globals maxb gl) S Ps t v F 
  (Hwfv: wf_value S (module_intro los nts Ps) F v (typ_pointer t))
  b' ofs' m'
  (Hget: getOperandValue (los,nts) v lc2 gl = Some ((Vptr b' ofs', m')::nil)) ombs size'
  (Hin: in_SAS_tails pinfo sasinfo ombs (los,nts) EC) size,
  SASmsim.notin_ignores_with_size (ombs__ignores size' ombs) b'
     (Int.signed 31 ofs') size.
Proof.
  intros.
  eapply in_SAS_tails__wf_ECStack_head_tail__no_alias_with_blk 
    with (size:=size') in Hin; eauto.
  eapply SASmsim.no_alias_with_blk__notin_ignores_with_size; eauto.
Qed.   

Lemma in_SAS_tail_dec: forall pinfo sasinfo TD EC mb
  (Hnone: in_SAS_tail pinfo sasinfo None TD EC)
  (Hsome: in_SAS_tail pinfo sasinfo (Some mb) TD EC),
  False.
Proof.
  unfold in_SAS_tail.
  intros.
  destruct (@EC_follow_dead_store_dec pinfo sasinfo EC) as [J | J].
    assert (J':=J).
    apply Hnone in J. 
    apply Hsome in J'. 
    destruct (lookupAL (GVsT DGVs) (Opsem.Locals EC) (PI_id pinfo)) 
      as [[|[[]][]]|]; inv J; inv J'.

    assert (J':=J).
    apply Hnone in J. 
    apply Hsome in J'. 
    destruct (lookupAL (GVsT DGVs) (Opsem.Locals EC) (PI_id pinfo)) 
      as [[|[[]][]]|]; inv J; inv J'.
Qed.

Lemma in_SAS_tails__notin_ignores_with_size: forall maxb pinfo sasinfo 
  los nts Mem lc2 EC gl
  (Hnals: Promotability.wf_ECStack_head_tail maxb pinfo (los,nts) Mem lc2 EC)
  (Hwfg: MemProps.wf_globals maxb gl) S Ps als2 tmn2 id0 t align0 v cs B F
  (Hwfv: wf_value S (module_intro los nts Ps) F v (typ_pointer t))
  (Hinscope: if fdef_dec (PI_f pinfo) F
             then Promotability.wf_defs maxb pinfo (los,nts) Mem lc2 als2
             else True) b' ofs' m'
  (Hget: getOperandValue (los,nts) v lc2 gl = Some ((Vptr b' ofs', m')::nil)) ombs size'
  (Hin: in_SAS_tails pinfo sasinfo ombs (los,nts)
        ({|
         Opsem.CurFunction := F;
         Opsem.CurBB := B;
         Opsem.CurCmds := insn_load id0 t v align0 :: cs;
         Opsem.Terminator := tmn2;
         Opsem.Locals := lc2;
         Opsem.Allocas := als2 |} :: EC)) size,
  SASmsim.notin_ignores_with_size (ombs__ignores size' ombs) b'
     (Int.signed 31 ofs') size.
Proof.
  intros.
  inv Hin. simpl.
  eapply in_SAS_tails__notin_ignores_with_size' with (size:=size)(size':=size') 
    in H3; eauto.
  destruct y as [mb|]; auto.
    unfold SASmsim.notin_ignores_with_size in *.
    constructor; auto.
    remember (used_in_value (PI_id pinfo) v) as R.
    destruct R.
      assert (in_SAS_tail pinfo sasinfo None (los, nts)
          {| Opsem.CurFunction := F;
             Opsem.CurBB := B;
             Opsem.CurCmds := insn_load id0 t v align0 :: cs;
             Opsem.Terminator := tmn2;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |}) as Hin.
      eapply load_pid_isnt_in_SAS_tail; simpl; eauto.
      apply in_SAS_tail_dec in H1; auto.
      
      eapply unused_pid_in_SAS_tail__wf_defs__no_alias_with_blk in H1; eauto.
      simpl in H1. auto.
Qed.

Lemma mem_simulation__mload: forall (maxb : Z) (pinfo : PhiInfo) 
  (sasinfo : SASInfo pinfo) (gl2 : GVMap) (fs2 : GVMap) (tmn2 : terminator)
  (lc2 : Opsem.GVsMap) (als2 : list mblock) (M2 : mem) (S : system)
  (los : layouts) (nts : namedts) (Ps : list product) (F : fdef) (B : block)
  (id0 : id) (t : typ) (align0 : align) (v : value)
  (EC : list Opsem.ExecutionContext) (cs : list cmd) (Mem : mem)
  (mp : GenericValue) (gv : GenericValue)
  (H1 : mload (los, nts) Mem mp t align0 = ret gv)
  (Hwfg : MemProps.wf_globals maxb gl2)
  (Hmsim : mem_simulation pinfo sasinfo (los, nts)
            ({|
             Opsem.CurFunction := F;
             Opsem.CurBB := B;
             Opsem.CurCmds := insn_load id0 t v align0 :: cs;
             Opsem.Terminator := tmn2;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |} :: EC) Mem M2)
  (Hinscope' : if fdef_dec (PI_f pinfo) F
              then Promotability.wf_defs maxb pinfo (los, nts) Mem lc2 als2
              else True)
  (HwfHT : Promotability.wf_ECStack_head_tail maxb pinfo (los, nts) Mem lc2 EC)
  (gv0 : GenericValue) (H23 : mload (los, nts) M2 mp t align0 = ret gv0)
  (H21 : Opsem.getOperandValue (los, nts) v lc2 gl2 = ret mp)
  (Hwfv : wf_value S (module_intro los nts Ps) F v (typ_pointer t)),
  gv = gv0.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim3 Hmsim2]].
  simpl in HwfHT.
  apply mload_inv in H1.
  destruct H1 as [b [ofs [m [mc [J1 [J2 J3]]]]]]; subst.
  apply mload_inv in H23.
  destruct H23 as [b' [ofs' [m' [mc' [J1' [J2' J3']]]]]]; subst.
  rewrite J2 in J2'. inv J2'. inv J1'.
  unfold sas_mem_inj in Hmsim2.
  inv_mbind. clear HeqR.
  destruct (@in_SAS_tails_ex pinfo sasinfo (los,nts) 
             ({| Opsem.CurFunction := F;
                 Opsem.CurBB := B;
                 Opsem.CurCmds := insn_load id0 t v align0 :: cs;
                 Opsem.Terminator := tmn2;
                 Opsem.Locals := lc2;
                 Opsem.Allocas := als2 |} :: EC)) as [ombs Hin].
  assert (G:=Hin).
  apply_clear Hmsim2 in Hin.
  eapply SASmsim.mload_aux_inject_id_inj2; eauto.
    eapply in_SAS_tails__notin_ignores_with_size; eauto.
Qed.

Lemma in_SAS_tail_at_beginning: forall pinfo sasinfo TD F tmn' lc' als' cs' ps' 
  l',
  in_SAS_tail pinfo sasinfo None TD 
    {| Opsem.CurFunction := F;
       Opsem.CurBB := block_intro l' ps' cs' tmn';
       Opsem.CurCmds := cs';
       Opsem.Terminator := tmn';
       Opsem.Locals := lc';
       Opsem.Allocas := als' |}.
Proof.
  intros.
  unfold in_SAS_tail. simpl. intros.
  split; intros J; auto.
    contradict J.
    apply EC_follow_dead_store_at_begin_false; auto.
Qed.

Lemma mem_simulation__call: forall pinfo sasinfo TD EC ECs M1 M2
  (Hmsim : mem_simulation pinfo sasinfo TD (EC :: ECs) M1 M2)
  (l'0 : l) (ps'0 : phinodes) (tmn'0 : terminator) als' lc' F cs',
  mem_simulation pinfo sasinfo TD
    ({| Opsem.CurFunction := F;
        Opsem.CurBB := block_intro l'0 ps'0 cs' tmn'0;
        Opsem.CurCmds := cs';
        Opsem.Terminator := tmn'0;
        Opsem.Locals := lc';
        Opsem.Allocas := als' |} :: EC :: ECs) M1 M2.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim3 Hmsim2]].
  split; auto.
  split; auto.
     clear - Hmsim2.
     unfold sas_mem_inj in *.
     inv_mbind. 
     intros ombs Hin'.
     inv Hin'.

     destruct y.
       assert (in_SAS_tail pinfo sasinfo None TD
         {| Opsem.CurFunction := F;
            Opsem.CurBB := block_intro l'0 ps'0 cs' tmn'0;
            Opsem.CurCmds := cs';
            Opsem.Terminator := tmn'0;
            Opsem.Locals := lc';
           Opsem.Allocas := als' |}) as Hin.
         apply in_SAS_tail_at_beginning; auto.
       apply in_SAS_tail_dec in H1; auto. inv H1.
       
       simpl.
       apply Hmsim2; auto.
Qed.

Lemma SAS_sid2_isnt_in_SAS_tail: forall (pinfo : PhiInfo) 
  (sasinfo : SASInfo pinfo) (tmn2 : terminator) (lc2 : Opsem.GVsMap)
  (als2 : list mblock) (los : layouts) (nts : namedts) (B : block) (t : typ)
  (align0 : align) (v1 : value) (v2 : value) (cs : list cmd)
  (Heq3 : exists l1 : l,
           exists ps1 : phinodes,
             exists cs11 : list cmd,
               B =
               block_intro l1 ps1
                 (cs11 ++
                  insn_store (SAS_sid2 pinfo sasinfo) t v1 v2 align0 :: cs)
                 tmn2)
  (y : monad Values.block)
  (H1 : in_SAS_tail pinfo sasinfo y (los, nts)
         {|
         Opsem.CurFunction := PI_f pinfo;
         Opsem.CurBB := B;
         Opsem.CurCmds := cs;
         Opsem.Terminator := tmn2;
         Opsem.Locals := lc2;
         Opsem.Allocas := als2 |}), y = merror.
Proof.
  intros.
  destruct H1 as [_ H1]. apply H1. clear H1.
  intro J.
  clear - J Heq3.
  destruct J as [J1 [J2 J3]]. simpl in *. subst.
  unfold cs_follow_dead_store in J3.
  destruct Heq3 as [l1 [ps1 [cs11 Heq3]]].
  rewrite Heq3 in J3. clear J1.
  destruct sasinfo. simpl in *. subst.
  destruct SAS_prop0 as [J4 [J5 [cs1 [cs3 J6]]]]. 
  assert (insn_store SAS_sid4 t v1 v2 align0 :: cs = 
          insn_store SAS_sid4 (PI_typ pinfo) SAS_value4
            (value_id (PI_id pinfo)) (PI_align pinfo) :: cs3 /\
          cs11 = cs1 ++
            insn_store SAS_sid3 (PI_typ pinfo) SAS_value3 
              (value_id (PI_id pinfo)) (PI_align pinfo)
            :: SAS_tail0) as EQ.
    admit. (* uniqness *)
  destruct EQ as [EQ1 EQ2]; subst. clear J6.
  inv EQ1.
  destruct (@J3 cs1 (insn_store SAS_sid4 (PI_typ pinfo) SAS_value4 
                    (value_id (PI_id pinfo)) (PI_align pinfo) :: cs3))
    as [csa [csb [J6 J7]]]; simpl_env; auto.
    anti_simpl_env. 
Qed.

Lemma SAS_sid2_is_in_SAS_tail: forall (pinfo : PhiInfo) (sasinfo : SASInfo pinfo)
  (tmn2 : terminator) (lc2 : Opsem.GVsMap) (als2 : list mblock) (los : layouts)
  (nts : namedts) (B : block) (align0 : align) (v1 : value) (cs : list cmd)
  (b' : Values.block) (cm' : AST.memory_chunk)
  (Heq3 : exists l1 : l,
           exists ps1 : phinodes,
             exists cs11 : list cmd,
               B =
               block_intro l1 ps1
                 (cs11 ++
                  insn_store (SAS_sid2 pinfo sasinfo) 
                    (PI_typ pinfo) v1 (value_id (PI_id pinfo)) align0 :: cs)
                 tmn2)
  (H25 : lookupAL (GVsT DGVs) lc2 (PI_id pinfo) =
        ret ((Vptr b' (Int.repr 31 0), cm') :: nil)),
  in_SAS_tail pinfo sasinfo (ret b') (los, nts)
     {|
     Opsem.CurFunction := PI_f pinfo;
     Opsem.CurBB := B;
     Opsem.CurCmds := insn_store (SAS_sid2 pinfo sasinfo) 
                        (PI_typ pinfo) v1 (value_id (PI_id pinfo)) align0
                      :: cs;
     Opsem.Terminator := tmn2;
     Opsem.Locals := lc2;
     Opsem.Allocas := als2 |}.
Proof.
  intros.
  split; intros J; simpl.
    rewrite H25; auto.
  
    contradict J.                
    split; auto.
    simpl.
    destruct Heq3 as [l1 [ps1 [cs11 Heq3]]]. subst.
    assert (block_intro l1 ps1
             (cs11 ++
              insn_store (SAS_sid2 pinfo sasinfo) (PI_typ pinfo) v1
              (value_id (PI_id pinfo)) align0 :: cs) tmn2 = 
            SAS_block pinfo sasinfo) as EQ.
      admit. (* uniqness SAS *)
    split; auto.
      unfold cs_follow_dead_store.
      rewrite <- EQ.
      intros.
      clear - EQ H.
      destruct sasinfo. simpl in *.
      destruct SAS_prop0 as [J1 [J2 J3]].
      subst.
      destruct J3 as [cs5 [cs4 J3]].
      assert (cs11 = cs5 ++
                insn_store SAS_sid3 (PI_typ pinfo) SAS_value3 
                  (value_id (PI_id pinfo)) (PI_align pinfo)
                :: SAS_tail0 /\ cs = cs4) as EQ'.
        admit. (* uniqness *)
      destruct EQ'; subst. clear J3.
      assert (cs5 = cs1 /\ insn_store SAS_sid4 (PI_typ pinfo) v1
               (value_id (PI_id pinfo)) align0 :: cs4 = cs3) as EQ'.
        admit. (* uniqness *)
      destruct EQ'; subst. clear H.
      exists SAS_tail0. exists nil. simpl_env. auto.
Qed.

Lemma mstore_unremovable_mem_simulation: forall (maxb : Z) (pinfo : PhiInfo)
  (sasinfo : SASInfo pinfo) (gl2 : GVMap) (tmn2 : terminator) 
  (lc2 : Opsem.GVsMap) (als2 : list mblock) (M2 : mem) (S : system)
  (los : layouts) (nts : namedts) (Ps : list product) (F : fdef) (B : block)
  (sid : id) (t : typ) (align0 : align) (v1 : value) (v2 : value)
  (EC : list Opsem.ExecutionContext) (cs : list cmd) (Mem : mem)
  (HBinF1 : blockInFdefB B F = true) (mp2 : GenericValue) (gv1 : GenericValue)
  (Mem' : mem) (H3 : mstore (los, nts) Mem mp2 t gv1 align0 = ret Mem')
  (Hwfg : wf_global (los, nts) S gl2) (Hwflc1 : OpsemPP.wf_lc (los, nts) F lc2)
  (Heq3 : exists l1 : l,
           exists ps1 : phinodes,
             exists cs11 : list cmd,
               B =
               block_intro l1 ps1
                 (cs11 ++ insn_store sid t v1 v2 align0 :: cs) tmn2)
  (Hmsim : mem_simulation pinfo sasinfo (los, nts)
            ({|
             Opsem.CurFunction := F;
             Opsem.CurBB := B;
             Opsem.CurCmds := insn_store sid t v1 v2 align0 :: cs;
             Opsem.Terminator := tmn2;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |} :: EC) Mem M2)
  (Hnrem : ~
          removable_State pinfo sasinfo
            {|
            Opsem.ECS := {|
                         Opsem.CurFunction := F;
                         Opsem.CurBB := B;
                         Opsem.CurCmds := insn_store sid t v1 v2 align0 :: cs;
                         Opsem.Terminator := tmn2;
                         Opsem.Locals := lc2;
                         Opsem.Allocas := als2 |} :: EC;
            Opsem.Mem := Mem |})
  (Hinscope' : if fdef_dec (PI_f pinfo) F
              then Promotability.wf_defs maxb pinfo (los, nts) Mem lc2 als2
              else True)
  (Mem'0 : mem)
  (H24 : Opsem.getOperandValue (los, nts) v1 lc2 gl2 = ret gv1)
  (H25 : Opsem.getOperandValue (los, nts) v2 lc2 gl2 = ret mp2)
  (H28 : mstore (los, nts) M2 mp2 t gv1 align0 = ret Mem'0)
  (Hwfv : wf_value S (module_intro los nts Ps) F v1 t),
  mem_simulation pinfo sasinfo (los, nts)
     ({|
      Opsem.CurFunction := F;
      Opsem.CurBB := B;
      Opsem.CurCmds := cs;
      Opsem.Terminator := tmn2;
      Opsem.Locals := lc2;
      Opsem.Allocas := als2 |} :: EC) Mem' Mem'0.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim3 Hmsim2]].
  split.
    apply MemProps.nextblock_mstore in H3.
    apply MemProps.nextblock_mstore in H28.
    rewrite <- H3. rewrite <- H28. rewrite Hmsim1. auto.
  
  split.
    intro b.
    apply MemProps.bounds_mstore with (b':=b) in H3.
    apply MemProps.bounds_mstore with (b':=b) in H28.
    congruence.
  
    apply mstore_inversion in H28.
    destruct H28 as [b [ofs [cm [J1 J2]]]]; subst.
    apply mstore_inversion in H3.
    destruct H3 as [b' [ofs' [cm' [J1' J2']]]]; subst.
    inv J1'.
    unfold sas_mem_inj in *.
    inv_mbind.
    intros ombs Hin'.
    assert ((PI_f pinfo = F -> 
              getCmdLoc (insn_store sid t v1 v2 align0) = 
                SAS_sid2 pinfo sasinfo) \/
            (PI_f pinfo = F -> 
              getCmdLoc (insn_store sid t v1 v2 align0) <> 
                SAS_sid2 pinfo sasinfo)) as Hdec.
      simpl.
      destruct (id_dec sid (SAS_sid2 pinfo sasinfo)); auto.
    destruct Hdec as [Heq | Hneq].
    SSCase "sid = SAS_sid2".
      inv Hin'.
      destruct (fdef_dec (PI_f pinfo) F); subst.
        SSSCase "PI_f = F".
        simpl in Heq. rewrite Heq in *; auto. clear Heq.
        assert (y = None) as EQ. 
          clear - H1 Heq3.
          eapply SAS_sid2_isnt_in_SAS_tail; eauto.
        subst. simpl.
        assert (v2 = value_id (PI_id pinfo) /\ t = PI_typ pinfo) as EQ. 
          clear - Heq3 HBinF1.
          destruct Heq3 as [l1 [ps1 [cs11 Heq3]]].
          admit. (* uniqness SAS *)
        destruct EQ; subst.
        simpl in H25.
        assert (ofs' = Int.repr 31 0) as EQ. 
          apply Hinscope' in H25. clear - H25.
          destruct H25 as [[_ [[mb [H25 _]] _]] _].
          rewrite Promotability.simpl_blk2GV in H25. inv H25. auto.            
        subst.
        assert (in_SAS_tails pinfo sasinfo (Some b'::l') (los, nts)
                 ({|Opsem.CurFunction := PI_f pinfo;
                    Opsem.CurBB := B;
                    Opsem.CurCmds := 
                      insn_store (SAS_sid2 pinfo sasinfo) (PI_typ pinfo) v1 
                        (value_id (PI_id pinfo)) align0::cs;
                    Opsem.Terminator := tmn2;
                    Opsem.Locals := lc2;
                    Opsem.Allocas := als2 |} :: EC)) as Hin.
          constructor; auto.
            clear - H25 Heq3.
            eapply SAS_sid2_is_in_SAS_tail; eauto.
        apply_clear Hmsim2 in Hin. simpl in Hin.
        assert (n = sizeGenericValue gv1) as EQ. 
          clear - Hwflc1 Hwfv HeqR H24 Hwfg.
          eapply wf__getTypeStoreSize_eq_sizeGenericValue; eauto.
        rewrite EQ in *. clear EQ. 
        eapply SASmsim.mstore_aux_inject_id_inside_inj2; eauto.
        rewrite Int.signed_repr; auto using Promotability.min_le_zero_le_max.
  
        SSSCase "PI_f <> F".
        assert (y = None) as EQ. 
          destruct H1 as [_ H1].
          apply H1.
          intros [J1 _]. simpl in J1. congruence.
        subst. simpl.
        assert (in_SAS_tails pinfo sasinfo (None::l') (los, nts)
                 ({|Opsem.CurFunction := F;
                    Opsem.CurBB := B;
                    Opsem.CurCmds := 
                      insn_store sid t v1 v2 align0::cs;
                    Opsem.Terminator := tmn2;
                    Opsem.Locals := lc2;
                    Opsem.Allocas := als2 |} :: EC)) as Hin.
          constructor; auto.
            split; intro J; simpl; auto.
              destruct J as [J _]. simpl in J. congruence.
        apply_clear Hmsim2 in Hin. simpl in Hin.
        eapply SASmsim.mstore_aux_inject_id_mapped_inj2; eauto.
  
    SSCase "sid <> SAS_sid2".
      assert (in_SAS_tails pinfo sasinfo ombs (los, nts)
               ({|Opsem.CurFunction := F;
                  Opsem.CurBB := B;
                  Opsem.CurCmds := insn_store sid t v1 v2 align0 :: cs;
                  Opsem.Terminator := tmn2;
                  Opsem.Locals := lc2;
                  Opsem.Allocas := als2 |} :: EC)) as Hin.
        inv Hin'.
        constructor; auto.
        eapply in_SAS_tail_update; eauto using unremovable_loc__neq__SAS_sid1.
      apply_clear Hmsim2 in Hin.
      eapply SASmsim.mstore_aux_inject_id_mapped_inj2; eauto.
Qed.

Lemma mstore_removable_mem_simulation: forall los nts M1 mp2 gv1 a M1' pinfo lc2 
  gl2 B1 cs1 tmn2 als2 ECs1 M2 t v sasinfo v0 Ps
  (Huniq: uniqFdef (PI_f pinfo))
  (HBinF1 : blockInFdefB B1 (PI_f pinfo) = true)
  (Heq3 : exists l1 : l,
           exists ps1 : phinodes,
             exists cs11 : list cmd,
               B1 =
               block_intro l1 ps1
                 (cs11 ++ insn_store (SAS_sid1 pinfo sasinfo) t v v0 a :: cs1)
                 tmn2) maxb
  (Hinscope' : if fdef_dec (PI_f pinfo) (PI_f pinfo)
              then Promotability.wf_defs maxb pinfo (los, nts) M1 lc2 als2
              else True)
  (H23: mstore (los,nts) M1 mp2 t gv1 a = ret M1')
  (H20 : @Opsem.getOperandValue DGVs (los,nts) v0 lc2 gl2 = ret mp2)
  (H19 : Opsem.getOperandValue (los,nts) v lc2 gl2 = ret gv1) S
  (Hwfg : wf_global (los, nts) S gl2)
  (Hwflc1 : OpsemPP.wf_lc (los, nts) (PI_f pinfo) lc2)
  (Hwfv : wf_value S (module_intro los nts Ps) (PI_f pinfo) v t)
  (Hmsim: mem_simulation pinfo sasinfo (los,nts)
            ({|
             Opsem.CurFunction := PI_f pinfo;
             Opsem.CurBB := B1;
             Opsem.CurCmds := insn_store (SAS_sid1 pinfo sasinfo) t v v0 a
                              :: cs1;
             Opsem.Terminator := tmn2;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |} :: ECs1) M1 M2),
  mem_simulation pinfo sasinfo (los,nts)
            ({|
             Opsem.CurFunction := PI_f pinfo;
             Opsem.CurBB := B1;
             Opsem.CurCmds := cs1;
             Opsem.Terminator := tmn2;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |} :: ECs1) M1' M2.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim3 Hmsim2]].
  split.
    apply MemProps.nextblock_mstore in H23.
    rewrite <- H23. auto.
  split.
    intro b'.    
    eapply MemProps.bounds_mstore in H23; eauto.
    rewrite <- H23. eauto.
    
    unfold sas_mem_inj in *. inv_mbind.
    intros ombs Hin.
    inv Hin.
    assert (in_SAS_tails pinfo sasinfo (None::l') (los,nts)
             ({|
              Opsem.CurFunction := PI_f pinfo;
              Opsem.CurBB := B1;
              Opsem.CurCmds := insn_store (SAS_sid1 pinfo sasinfo) t v v0 a
                               :: cs1;
              Opsem.Terminator := tmn2;
              Opsem.Locals := lc2;
              Opsem.Allocas := als2 |} :: ECs1)) as Hin.
      constructor; auto using SAS_sid1_isnt_in_SAS_tail.
    apply Hmsim2 in Hin. clear Hmsim2.
    simpl in Hin.
    assert (v0 = value_id (PI_id pinfo) /\ t = PI_typ pinfo) as EQ.
      admit. (* by sasinfo *)
    destruct EQ; subst. simpl in H20.
    assert (exists mb, mp2 = 
              ($ (blk2GV (los,nts) mb) # (typ_pointer (PI_typ pinfo)) $)) as EQ.
      destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
      apply Hinscope' in H20.
      destruct H20 as [[_ [[mb [H20 _]] _]] _]. eauto.
    destruct EQ as [mb EQ]; subst.
    assert (y = Some mb) as EQ.
      eapply SAS_sid1_is_in_SAS_tail; eauto.
    subst.
    assert (n = sizeGenericValue gv1) as EQ.
      eapply wf__getTypeStoreSize_eq_sizeGenericValue; eauto.
    subst.
    simpl.
    eapply SASmsim.mstore_inside_inj_left; eauto.
Qed.

Ltac dse_is_sim_common_case :=
match goal with
| Hex: exists _:_, exists _:_, exists _:_, _=block_intro _ _ (_++_::_) _,      
  Hcssim2: cmds_simulation _ _ _ _ _,
  Hop2: Opsem.sInsn _ _ _ _,
  Hmsim: mem_simulation _ _ _ _ _ _ |- _ =>
  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl; try solve 
    [eauto using unremovable_loc__neq__SAS_sid1];
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result;
  repeat_solve;
  match goal with
  | |- mem_simulation _ _ _
         ({|Opsem.CurFunction := _;
            Opsem.CurBB := _;
            Opsem.CurCmds := _;
            Opsem.Terminator := _;
            Opsem.Locals:= ?lc';
            Opsem.Allocas:=?als'|}::_) _ _ =>
      apply mem_simulation_update_locals with (lc2:=lc') (als3':=als') in Hmsim; 
        simpl; try solve [
          eauto using unremovable_loc__neq__SAS_sid1 |
          eapply unremovable_loc__neq__SAS_sid2; eauto; simpl; auto |
          intros;
          match goal with
          | |- lookupAL _ ?lc ?id1 =
                lookupAL _ (updateAddAL _ ?lc _ _ ) ?id1=>
               admit  (* id <> palloca *)
          end
        ]
  end
end.

Ltac dse_is_sim_malloc :=
  destruct_ctx_other;
  match goal with 
  | Hcssim2: cmds_simulation _ _ _ _ _,
    Hop2: Opsem.sInsn _ _ _ _ |- _ =>
    apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl;
      try solve [eauto using unremovable_loc__neq__SAS_sid1];
    destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
    inv Hop2; uniq_result
  end;
  match goal with
  | Hmsim: mem_simulation _ _ _ _ ?M1 ?M2,
    H25: malloc _ ?M1 _ _ _ = Some (_, ?mb),
    H2: malloc _ ?M2 _ _ _ = Some (_, ?mb0) |- _ =>
    assert (mb0 = mb) as EQ; try solve [
      match goal with
      | |- _ = _ =>
        destruct Hmsim as [Hmsim _];
        apply MemProps.malloc_result in H25;
        apply MemProps.malloc_result in H2; subst; auto
      end
    ]
  end;
  subst;
  repeat_solve;
    eapply mem_simulation__malloc; eauto using wf_system__uniqFdef; simpl; auto.

Lemma sas_is_sim : forall maxb pinfo (sasinfo: SASInfo pinfo) Cfg1 St1 Cfg2 St2
  (Hwfpi: WF_PhiInfo pinfo) 
  (Hwfmg: MemProps.wf_globals maxb (OpsemAux.Globals Cfg1)) 
  (Hwfcfg: OpsemPP.wf_Config Cfg1) (Hwfpp: OpsemPP.wf_State Cfg1 St1) 
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1) 
  (Hpalloca: palloca_props.wf_State pinfo St1) 
  (Hsim: State_simulation pinfo sasinfo Cfg1 St1 Cfg2 St2),
  (forall (Hrem: removable_State pinfo sasinfo St1) St1' tr1
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1),
     State_simulation pinfo sasinfo Cfg1 St1' Cfg2 St2 /\ tr1 = E0) /\
  (forall (Hnrem: ~removable_State pinfo sasinfo St1) St1' St2' tr1 tr2
     (Hop2: Opsem.sInsn Cfg2 St2 St2' tr2)
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1),
     State_simulation pinfo sasinfo Cfg1 St1' Cfg2 St2' /\ tr1 = tr2).
Proof.

Local Opaque inscope_of_tmn inscope_of_cmd.

  intros.
  split; intros.
Case "removable state".

  destruct Cfg1 as [S1 [los nts] Ps1 gl1 fs1].
  destruct St1 as [ECs1 M1].
  destruct ECs1 as [|[F1 B1 [|c1 cs1] tmn1 lc1 als1] ECs1]; tinv Hrem.
  destruct_cmd c1; tinv Hrem.
  simpl in Hrem.
  destruct (fdef_dec (PI_f pinfo) F1); subst; tinv Hrem.
  destruct (id_dec i0 (SAS_sid1 pinfo sasinfo)); subst; tinv Hrem.
  
  destruct Hwfcfg as [_ [Hwfg [HwfSystem HmInS]]].
  destruct Hwfpp as 
    [_ [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 _]]]]
     [HwfECs Hwfcall]]
    ]; subst.
  fold (@OpsemPP.wf_ECStack DGVs) in HwfECs.

  destruct Hnoalias as
    [
      [[Hinscope' _] [HwfECs' HwfHT]]
      [[Hdisjals _] HwfM]
    ]; simpl in Hdisjals.
  fold Promotability.wf_ECStack in HwfECs'.

  inv Hop1.

  destruct Cfg2 as [S2 TD2 Ps2 gl2 fs2].
  destruct St2 as [ECs2 M2].

  simpl in Hsim.
  destruct Hsim as [EQ1 [Hpsim [Hstksim [EQ2 [EQ3 Hmsim]]]]]; subst.
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2]; tinv Hstksim.
  destruct Hstksim as [Hecsim Hstksim].
  unfold EC_simulation in Hecsim.
  destruct Hecsim as
      [Hfsim2 [Heq1 [Heq2 [Hbsim2
        [Heq3 [Heq4 [Hlcsim2 Hcssim2]]]]]]]; subst.

  uniq_result.
  repeat_solve.
    eapply cmds_simulation_elim_cons_inv; eauto.
    assert (wf_value S1 (module_intro los nts Ps1) (PI_f pinfo) v t) as Hwfv.
      admit. (* wf *)
    eapply mstore_removable_mem_simulation in Hmsim;
      eauto using wf_system__uniqFdef.

Case "unremovable state".
  (sInsn_cases (destruct Hop1) SCase).

SCase "sReturn".
Focus.
  destruct_ctx_return.
  repeat_solve.
    clear - H26 Hmsim H0 H1 Heq3'.
    eapply mem_simulation__return; eauto.
      admit. (* pid <> i0 *)

Unfocus.

SCase "sReturnVoid".
Focus.
  destruct_ctx_return.
  repeat_solve.
    clear - H24 Hmsim H0 Heq3'.
    eapply mem_simulation__return; eauto.
Unfocus.

SCase "sBranch".
Focus.

  destruct_ctx_other.
  apply cmds_simulation_nil_inv in Hcssim2; subst.
  inv Hop2.
  uniq_result.

  assert (block_simulation pinfo sasinfo F (block_intro l' ps' cs' tmn')
           (block_intro l'0 ps'0 cs'0 tmn'0)) as Hbsim.
    clear - H22 H1 Hfsim2.
    destruct (isGVZero (los, nts) c); eauto using fdef_sim__block_sim.
  assert (uniqFdef F) as Huniq. eauto using wf_system__uniqFdef.
  assert (blockInFdefB (block_intro l' ps' cs' tmn') F) as HBinF1'.
    admit. (* infra *)
  assert (Hbsim':=Hbsim).
  apply block_simulation_inv in Hbsim'; auto.
  destruct Hbsim' as [Heq1 [Heq2 [Hcssim' Heq5]]]; subst.

  assert (lc' = lc'0) as Heq.
    clear - H2 H23 Hbsim2.
    eapply switchToNewBasicBlock_sim in Hbsim2; eauto.
  subst.

  repeat_solve.
    exists l'0. exists ps'0. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.

    clear - H2 Hmsim.
    eapply switchToNewBasicBlock_mem_simulation; eauto.

Unfocus.

SCase "sBranch_uncond".
Focus.
  destruct_ctx_other.
  apply cmds_simulation_nil_inv in Hcssim2; subst.
  inv Hop2.
  uniq_result.

  assert (block_simulation pinfo sasinfo F (block_intro l' ps' cs' tmn')
           (block_intro l'0 ps'0 cs'0 tmn'0)) as Hbsim.
    eauto using fdef_sim__block_sim.
  assert (uniqFdef F) as Huniq. eauto using wf_system__uniqFdef.
  assert (blockInFdefB (block_intro l' ps' cs' tmn') F) as HBinF1'.
    admit. (* infra *)
  assert (Hbsim':=Hbsim).
  apply block_simulation_inv in Hbsim'; auto.
  destruct Hbsim' as [Heq1 [Heq2 [Hcssim' Heq5]]]; subst.

  assert (lc' = lc'0) as Heq.
    clear - H0 H17 Hbsim2.
    eapply switchToNewBasicBlock_sim in Hbsim2; eauto.
  subst.

  repeat_solve.
    exists l'0. exists ps'0. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.

    clear - H0 Hmsim.
    eapply switchToNewBasicBlock_mem_simulation; eauto.

Unfocus.

SCase "sBop". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sFBop". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sExtractValue". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sInsertValue". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sMalloc". abstract (dse_is_sim_malloc).
SCase "sFree".
  destruct_ctx_other.

  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl;
    try solve [eauto using unremovable_loc__neq__SAS_sid1].
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  repeat_solve.
    eapply mem_simulation__free; eauto.
    eapply mem_simulation__replace_head in Hmsim; eauto.
    intros omb Hin.
      eapply in_SAS_tail_update; eauto using unremovable_loc__neq__SAS_sid1, 
                                             unremovable_loc__neq__SAS_sid2.
        simpl. admit. (* uniqness *)

SCase "sAlloca". abstract (dse_is_sim_malloc).

SCase "sLoad".
  destruct_ctx_other.

  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl;
    try solve [eauto using unremovable_loc__neq__SAS_sid1].
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  assert (gv = gv0) as EQ.
    assert (wf_value S (module_intro los nts Ps) F v (typ_pointer t)) as Hwfv.
      admit. (* wf *)
    clear - H23 Hmsim H1 H21 HwfHT Hinscope' Hwfmg Hwfv. simpl in *.
    eapply mem_simulation__mload; eauto.
  subst.
  repeat_solve.
    eapply mem_simulation_update_locals in Hmsim; simpl; 
      eauto using unremovable_loc__neq__SAS_sid1.
      eapply unremovable_loc__neq__SAS_sid2; eauto; simpl; auto.
      admit. (* lid <> pid *)

SCase "sStore".

  destruct_ctx_other.

  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl;
    try solve [eauto using unremovable_loc__neq__SAS_sid1].
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  repeat_solve.
    assert (wf_value S (module_intro los nts Ps) F v1 t) as Hwfv.
      admit. (* wf *)
    clear - Hwfv H28 H24 H3 Hwflc1 Heq3 Hmsim HBinF1 Hinscope' H25 Hwfg Hnrem.
    eapply mstore_unremovable_mem_simulation; eauto.

SCase "sGEP". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sTrunc". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sExt". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sCast". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sIcmp". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sFcmp". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sSelect".
  destruct_ctx_other.

  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl;
    try solve [eauto using unremovable_loc__neq__SAS_sid1].
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  repeat_solve.
    destruct (isGVZero (los,nts) c).
      eapply mem_simulation_update_locals in Hmsim; simpl; 
        eauto using unremovable_loc__neq__SAS_sid1.
        eapply unremovable_loc__neq__SAS_sid2; eauto; simpl; auto.
        simpl. intros.
        admit. (* lid <> pid *)
      eapply mem_simulation_update_locals in Hmsim; simpl;
        eauto using unremovable_loc__neq__SAS_sid1.
        eapply unremovable_loc__neq__SAS_sid2; eauto; simpl; auto.
        simpl. intros.
        admit. (* lid <> pid *)

SCase "sCall".

  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl;
    try solve [eauto using unremovable_loc__neq__SAS_sid1].
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst.

  inv Hop2.

  SSCase "SCall".

  uniq_result.
  assert (Hfsim1:=Hpsim).
  eapply TopSim.lookupFdefViaPtr__simulation in Hfsim1; eauto.
  simpl in Hfsim1.
  assert (Hbsim1:=Hfsim1).
  eapply fdef_simulation__entry_block_simulation in Hbsim1; eauto.

  assert (InProductsB (product_fdef (fdef_intro
    (fheader_intro fa rt fid la va) lb)) Ps = true) as HFinPs'.
    apply OpsemAux.lookupFdefViaPtr_inversion in H1.
    destruct H1 as [fn [H11 H12]].
    eapply lookupFdefViaIDFromProducts_inv; eauto.
  assert (uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb))
    as Huniq.
    eapply wf_system__uniqFdef; eauto.
  assert (Hbsim1':=Hbsim1).
  apply block_simulation_inv in Hbsim1'; auto using entryBlockInFdef.
  destruct Hbsim1' as [Heq' [Hpsim1' [Hcsim1' Htsim1']]]; subst.
  repeat_solve.
    exists l'0. exists ps'0. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.

    apply fdef_simulation_inv in Hfsim1.
    destruct Hfsim1 as [Heq _]. inv Heq. uniq_result.
    auto.

    clear - Hmsim.
    apply mem_simulation__call; auto.

  SSCase "sExCall".

  uniq_result.

  clear - H29 H1 Hpsim.
  eapply TopSim.lookupFdefViaPtr__simulation_l2r in H1; eauto.
  simpl in H1.
  destruct H1 as [f2 [H1 H2]].
  apply OpsemAux.lookupExFdecViaPtr_inversion in H29.
  apply OpsemAux.lookupFdefViaPtr_inversion in H1.
  destruct H29 as [fn [J1 [J2 J3]]].
  destruct H1 as [fn' [J4 J5]].
  uniq_result.

SCase "sExCall".

  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl;
    try solve [eauto using unremovable_loc__neq__SAS_sid1].
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst.

  inv Hop2.

  SSCase "SCall".

  uniq_result.

  match goal with
  | Hpsim: products_simulation _ _ ?Ps ?Ps2,
    H1: OpsemAux.lookupExFdecViaPtr ?Ps _ _ = _,
    H30: OpsemAux.lookupFdefViaPtr ?Ps2 _ _ = _ |- _ =>
    clear - H30 H1 Hpsim;
    eapply TopSim.lookupExFdecViaPtr__simulation_l2r in H1; eauto;
    simpl in H1;
    apply OpsemAux.lookupExFdecViaPtr_inversion in H1;
    apply OpsemAux.lookupFdefViaPtr_inversion in H30;
    destruct H1 as [fn [J1 [J2 J3]]];
    destruct H30 as [fn' [J4 J5]]
  end.

  uniq_result.

  SSCase "sExCall".

  uniq_result.

  assert (Hlkdec:=Hpsim).
  eapply TopSim.lookupExFdecViaPtr__simulation_l2r in Hlkdec; eauto.
  uniq_result.
  eapply callExternalFunction__mem_simulation in Hmsim; eauto.
  destruct Hmsim as [EQ [Hmsim EQ']]; subst.
  uniq_result.
  repeat_solve.
    eapply mem_simulation_update_locals in Hmsim; simpl;
      eauto using unremovable_loc__neq__SAS_sid1.
      admit. (* rid <> pid *)  admit. (* cid <> pid *)

Transparent inscope_of_tmn inscope_of_cmd.

Qed.

Lemma sas_wfS: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo : PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds)
  (Hst1 : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (v0 : value)
  (Hst2 : ret inr (i1, v0) = find_next_stld cs (PI_id pinfo))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS :
     wf_system 
       [module_intro los nts
         (Ps1 ++
          product_fdef
            (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
          :: Ps2)]),
  wf_system 
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (fdef_intro fh
           (List.map (remove_block i0)
             (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))) :: Ps2)].
Admitted. (* prev WF *)

Lemma s_genInitState__sas_State_simulation: forall pinfo sasinfo S1 S2 main
  VarArgs cfg2 IS2 (Hssim: system_simulation pinfo sasinfo S1 S2)
  (Hwfpi: WF_PhiInfo pinfo) (HwfS1: wf_system S1)
  (Hinit: Opsem.s_genInitState S2 main VarArgs Mem.empty = ret (cfg2, IS2)),
  exists cfg1, exists IS1,
    Opsem.s_genInitState S1 main VarArgs Mem.empty = ret (cfg1, IS1) /\
    State_simulation pinfo sasinfo cfg1 IS1 cfg2 IS2.
Proof.
  unfold Opsem.s_genInitState.
  intros.
  inv_mbind'.
  destruct m as [los nts ps].
  inv_mbind'.
  destruct b as [l0 ps0 cs0 tmn0].
  destruct f as [[fa rt fid la va] bs].
  inv_mbind'. symmetry_ctx.
  assert (HlkF2FromS2:=HeqR).
  eapply TopSim.system_simulation__fdef_simulation_r2l in HeqR; eauto.
  destruct HeqR as [f1 [HlkF1fromS1 Hfsim]]. simpl in Hfsim.
  fill_ctxhole.
  eapply TopSim.system_simulation__getParentOfFdefFromSystem in HeqR0; eauto.
  destruct HeqR0 as [m1 [J1 J2]].
  fill_ctxhole. destruct m1 as [los1 nts1 ps1].
  destruct J2 as [J2 [J3 J4]]; subst.
  eapply TopSim.genGlobalAndInitMem_spec in HeqR1; eauto.
  destruct HeqR1 as [gl1 [fs1 [M1 [HeqR1 [EQ1 [EQ2 EQ3]]]]]]; subst.
  fill_ctxhole.
  assert (J:=HeqR2).
  eapply getEntryBlock__simulation in J; eauto.
  destruct J as [b1 [J5 J6]].
  fill_ctxhole.
  destruct b1 as [l2 ps2 cs2 tmn2].
  destruct f1 as [[fa1 rt1 fid1 la1 va1] bs1].
  assert (J:=Hfsim).
  apply fdef_simulation__eq_fheader in J.
  inv J.
  fill_ctxhole. eauto.
  match goal with
  | |- exists _:_, exists _:_, Some (?A, ?B) = _ /\ _ => exists A; exists B
  end.
  match goal with 
  | H: getParentOfFdefFromSystem _ _ = _ |- _ =>
    apply getParentOfFdefFromSystem__moduleInProductsInSystemB in H;
    destruct H as [HMinS HinPs]
  end.
  assert (J:=J6).
  apply block_simulation_inv in J; 
    eauto using entryBlockInFdef, wf_system__uniqFdef.
  destruct J as [J1 [J2 [J3 J7]]]; subst.
  assert (blockInFdefB (block_intro l0 ps0 cs0 tmn0)
           (fdef_intro (fheader_intro fa rt fid la va) bs) = true) as HBinF.
    apply entryBlockInFdef; auto.
  split; auto.
  eapply genGlobalAndInitMem__wf_globals_Mem in HeqR1; eauto.
  destruct HeqR1 as [J7 [J8 [J9 [J10 [J11 [J12 [J13 J14]]]]]]].
  repeat (split; auto).
    exists l0. exists ps0. exists nil. auto.
    exists l0. exists ps0. exists nil. auto.

    unfold sas_mem_inj. 
    assert (exists tsz, getTypeStoreSize (OpsemAux.initTargetData los nts Mem.empty)
             (PI_typ pinfo) = Some tsz) as Htsz.
      admit. (* When dse runs PI_f must be in the system, see mem2reg_correct *)
    destruct Htsz as [tsz Htsz]. fill_ctxhole.
    intros.
    eapply SASmsim.from_MoreMem_inj; eauto.
Qed.

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

Ltac s_isFinialState__sas_State_simulation cfg1 cfg2 FS1 FS2 Hstsim Hfinal := 
  destruct cfg2 as [S2 [los2 nts2] gl2 fs2];
  destruct cfg1 as [S1 [los1 nts1] gl1 fs1];
  destruct FS1 as [[|[? ? cs1 ? ?] ES1]]; 
  destruct FS2 as [[|[? ? cs2 ? ?] ES2]]; try solve [
    auto | congruence |
    destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst; inv Hstsim
  ];
  destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst;
  inv X; simpl;
  destruct Hstsim as [Hstsim Hstsim'];
  fold ECs_simulation in Hstsim';
  destruct Hstsim as [? [Htmn [? [? [? [? [? Hstsim]]]]]]]; subst;
  destruct cs1, cs2; try solve [
    auto |
    apply cmds_simulation_nil_inv in Hstsim; try congruence |
    inv Hfinal
  ].

Lemma s_isFinialState__sas_State_simulation_l2r: forall pinfo sasinfo cfg1 FS1 cfg2
  FS2 r (Hstsim : State_simulation pinfo sasinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg1 FS1 = ret r),
  Opsem.s_isFinialState cfg2 FS2 = ret r.
Proof.
  unfold Opsem.s_isFinialState.
  intros.
  s_isFinialState__sas_State_simulation cfg1 cfg2 FS1 FS2 Hstsim Hfinal.
  destruct Terminator0; auto.
    destruct ES1, ES2; try solve [auto | inv Hstsim'].
    destruct ES1, ES2; try solve [auto | inv Hstsim'].
Qed.

Lemma s_isFinialState__sas_State_simulation_l2r': forall pinfo sasinfo cfg1 FS1 cfg2
  FS2 (Hstsim : State_simulation pinfo sasinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg1 FS1 <> None),
  Opsem.s_isFinialState cfg2 FS2 <> None.
Proof.
  intros.
  remember (Opsem.s_isFinialState cfg1 FS1) as R.
  destruct R; try congruence.
  symmetry_ctx.
  eapply s_isFinialState__sas_State_simulation_l2r in Hstsim; eauto.
  congruence.
Qed.

Lemma s_isFinialState__sas_State_simulation_None_r2l:
  forall pinfo sasinfo cfg1 FS1 cfg2 FS2
  (Hstsim : State_simulation pinfo sasinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = None),
  Opsem.s_isFinialState cfg1 FS1 = None.
Proof.
  intros.
  remember (Opsem.s_isFinialState cfg1 FS1) as R.
  destruct R; try congruence.
  contradict Hfinal.
  eapply s_isFinialState__sas_State_simulation_l2r' in Hstsim; eauto.
    congruence.
Qed.

Lemma not_removable_State_inv: forall pinfo sasinfo St,
  ~ removable_State pinfo sasinfo St ->
  match St with
  | {| Opsem.ECS := {| Opsem.CurFunction := F;
                       Opsem.CurBB := _;
                       Opsem.CurCmds := c :: _;
                       Opsem.Terminator := _;
                       Opsem.Locals := _;
                       Opsem.Allocas := _ |} :: _;
       Opsem.Mem := Mem |} => 
       PI_f pinfo <> F \/ 
       match c with
       | insn_store sid _ _ _ _ => sid <> SAS_sid1 pinfo sasinfo
       | _ => True
       end
  | _ => True
  end.
Proof.
  intros.
  destruct St; auto.
  destruct ECS; auto.
  destruct e; auto.
  destruct CurCmds; auto.
  destruct c; auto.
  simpl in H.
  destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
  destruct (id_dec i0 (SAS_sid1 pinfo sasinfo)); subst; auto.
Qed.

Lemma s_isFinialState__sas_State_simulation_r2l':
  forall pinfo sasinfo cfg1 FS1 cfg2 FS2 r
  (Hnrem: ~removable_State pinfo sasinfo FS1) 
  (Hstsim : State_simulation pinfo sasinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = ret r),
  Opsem.s_isFinialState cfg1 FS1 = ret r.
Proof.
  unfold Opsem.s_isFinialState.
  intros.
  s_isFinialState__sas_State_simulation cfg1 cfg2 FS1 FS2 Hstsim Hfinal.
    destruct Terminator0; auto.
      destruct ES1, ES2; try solve [auto | inv Hstsim'].
      destruct ES1, ES2; try solve [auto | inv Hstsim'].

   apply not_removable_State_inv in Hnrem.
   apply cmds_simulation_nelim_cons_inv in Hstsim; auto. 
     destruct Hstsim as [cs2' [J1 Hstsim]]; congruence.
     admit. (* removable_State may check if getCmdLoc <> sid1 directly,
               otherwise, we need uniqness
               The current removable_State only checks id when c is store, 
               but cmds_simulation_nelim_cons_inv uses getCmdLoc,
               Changing the definition may simplify proofs.
               Refer to dae's removable_State *)
Qed.

Lemma removable_State__non_removable_State: forall pinfo sasinfo f b c cs1 tmn lc
  als ES1 lc' als' Mem Mem' (Hnodup: NoDup (getCmdsLocs (c::cs1)))
  (Hrem : removable_State pinfo sasinfo 
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := f;
                        Opsem.CurBB := b;
                        Opsem.CurCmds := c :: cs1;
                        Opsem.Terminator := tmn;
                        Opsem.Locals := lc;
                        Opsem.Allocas := als |} :: ES1;
           Opsem.Mem := Mem |}),
  ~ removable_State pinfo sasinfo 
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := f;
                        Opsem.CurBB := b;
                        Opsem.CurCmds := cs1;
                        Opsem.Terminator := tmn;
                        Opsem.Locals := lc';
                        Opsem.Allocas := als' |} :: ES1;
           Opsem.Mem := Mem' |}.
Proof.
  simpl. intros.
  destruct c; try tauto.
  destruct_if; auto.
  destruct_if; auto.
  destruct cs1; auto.
  destruct c; auto.
  destruct_if; auto.
  inv Hnodup. inv H2. intro J. apply H1. simpl. left. congruence.
Qed.

Lemma s_isFinialState__sas_State_simulation_r2l:
  forall pinfo sasinfo cfg1 FS1 cfg2 FS2 r
  (Hwfpi: WF_PhiInfo pinfo) maxb
  (Hwfmg: MemProps.wf_globals maxb (OpsemAux.Globals cfg1)) 
  (Hwfcfg: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 FS1) 
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 FS1) 
  (Hpalloca: palloca_props.wf_State pinfo FS1) 
  (Hstsim : State_simulation pinfo sasinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = ret r)
  (Hok: ~ sop_goeswrong cfg1 FS1),
  exists FS1',
    Opsem.sop_star cfg1 FS1 FS1' E0 /\
    State_simulation pinfo sasinfo cfg1 FS1' cfg2 FS2 /\
    Opsem.s_isFinialState cfg1 FS1' = ret r.
Proof.
  intros.
  destruct (removable_State_dec pinfo sasinfo FS1) as [Hrem | Hnrem].
Case "removable".
    assert (G:=Hstsim).
    destruct cfg2 as [S2 [los2 nts2] gl2 fs2];
    destruct cfg1 as [S1 [los1 nts1] gl1 fs1].
    destruct FS1 as [[|[? ? cs1 ? ?] ES1]];
    destruct FS2 as [[|[? ? cs2 ? ?] ES2]]; try solve [
      auto |
      destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst; inv Hstsim |
      inv Hrem
    ].
    destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst;
    inv X; simpl;
    destruct Hstsim as [Hstsim Hstsim'];
    fold ECs_simulation in Hstsim'.
    destruct Hstsim as [? [Htmn [? [? [? [? [? Hstsim]]]]]]]; subst;
    destruct cs1, cs2; try solve [
      auto |
      apply cmds_simulation_nil_inv in Hstsim; try congruence |
      inv Hfinal |
      inv Hrem
    ].

    assert (G':=G). 
    eapply sas_is_sim in G; eauto.
    destruct G as [G _].
    remember 
            (Opsem.s_isFinialState {|           
              OpsemAux.CurSystem := S1;
              OpsemAux.CurTargetData := (los2, nts2);
              OpsemAux.CurProducts := gl1;
              OpsemAux.Globals := fs2;
              OpsemAux.FunTable := FunTable |}
              {|
              Opsem.ECS := {|
                           Opsem.CurFunction := CurFunction;
                           Opsem.CurBB := CurBB;
                           Opsem.CurCmds := c :: cs1;
                           Opsem.Terminator := Terminator0;
                           Opsem.Locals := Locals0;
                           Opsem.Allocas := Allocas0 |} :: ES1;
              Opsem.Mem := Mem |}) as R.
    destruct R.
    SCase "isFinal".
      exists ({|
         Opsem.ECS := {|
                      Opsem.CurFunction := CurFunction;
                      Opsem.CurBB := CurBB;
                      Opsem.CurCmds := c :: cs1;
                      Opsem.Terminator := Terminator0;
                      Opsem.Locals := Locals0;
                      Opsem.Allocas := Allocas0 |} :: ES1;
         Opsem.Mem := Mem |}). 
      split; auto.
      split.
        unfold State_simulation in G'. auto.
        eapply s_isFinialState__sas_State_simulation_l2r in G'; eauto.
        uniq_result. auto.

    SCase "isntFinal".
    assert (J:=Hwfpp1).
    apply OpsemPP.progress in J; auto.
    destruct J as [Hfinal1 | [[IS1' [tr0 Hop1]] | Hundef1]]; try congruence.
      SSCase "step".
      clear G'.
      assert (Hop1':=Hop1).
      apply_clear G in Hop1'; auto.
      destruct Hop1' as [J1 J2]; subst.
      assert (Hop1':=Hop1).
      apply OpsemPP.preservation in Hop1'; auto.     
      assert (J1':=J1).
      eapply s_isFinialState__sas_State_simulation_r2l' in J1; eauto.
        exists IS1'.
        split.
          apply OpsemProps.sInsn__implies__sop_star; auto.
        split.
          unfold State_simulation in J1'. auto.
          auto.

        assert (
          c = insn_store (SAS_sid1 pinfo sasinfo) (PI_typ pinfo) 
                (SAS_value1 pinfo sasinfo) (value_id (PI_id pinfo)) 
                (PI_align pinfo)) as EQ.
          admit. (* uniqness *)
        subst.
        inv Hop1.
        eapply removable_State__non_removable_State; eauto.
          admit. (* uniqness *)

      SSCase "stuck".
      clear - Hundef1 Hok HeqR.
      apply undefined_state__stuck' in Hundef1.
      contradict Hok.
      exists {|Opsem.ECS := {|
                  Opsem.CurFunction := CurFunction;
                  Opsem.CurBB := CurBB;
                  Opsem.CurCmds := c :: cs1;
                  Opsem.Terminator := Terminator0;
                  Opsem.Locals := Locals0;
                  Opsem.Allocas := Allocas0 |} :: ES1;
               Opsem.Mem := Mem |}.
      exists E0.
      split; auto.

Case "unremovable".
    assert (J:=Hstsim).
    eapply s_isFinialState__sas_State_simulation_r2l' in Hstsim; eauto.
Qed.

Lemma cmds_simulation_nil_inv' : forall (pinfo : PhiInfo) sasinfo
  (f1 : fdef) (cs1 : list cmd) b1 tmn1 lc1 als1 ECS Mem1
  (Hnrem : ~
          removable_State pinfo sasinfo
            {|
            Opsem.ECS := {|
                         Opsem.CurFunction := f1;
                         Opsem.CurBB := b1;
                         Opsem.CurCmds := cs1;
                         Opsem.Terminator := tmn1;
                         Opsem.Locals := lc1;
                         Opsem.Allocas := als1 |} :: ECS;
            Opsem.Mem := Mem1 |}),
  cmds_simulation pinfo sasinfo f1 cs1 nil -> cs1 = nil.
Proof.
  simpl.
  unfold cmds_simulation. intros.
  destruct_if; auto.
  destruct cs1; auto.
  simpl in *.
  admit. (* see the comments in s_isFinialState__sas_State_simulation_r2l' *)
Qed.

Lemma cmds_simulation_cons_inv' : forall (pinfo : PhiInfo) sasinfo
  (f1 : fdef) b1 lc1 cs tmn1 als1 c cs2 ECS Mem1
  (Hnrem : ~
          removable_State pinfo sasinfo
            {|
            Opsem.ECS := {|
                         Opsem.CurFunction := f1;
                         Opsem.CurBB := b1;
                         Opsem.CurCmds := cs;
                         Opsem.Terminator := tmn1;
                         Opsem.Locals := lc1;
                         Opsem.Allocas := als1 |} :: ECS;
            Opsem.Mem := Mem1 |}),
  cmds_simulation pinfo sasinfo f1 cs (c::cs2) -> 
   exists cs1, 
     cs = c::cs1 /\
     cmds_simulation pinfo sasinfo f1 cs1 cs2.
Proof.
  simpl.
  unfold cmds_simulation. intros.
  destruct_if; eauto.
  destruct cs; tinv H1.
  simpl in *.
  admit. (* see the comments in s_isFinialState__sas_State_simulation_r2l' *)
Qed.

Ltac undefined_state__State_simulation_r2l_tac1 :=
  match goal with
  | Hstsim: State_simulation _ _ _ ?St1 _ ?St2 |- _ =>
    destruct St2 as [[|[? ? [|CurCmds] [] ?] [|[]]] ?]; try tauto;
    destruct CurCmds; try tauto;
    destruct St1 as [ECS ?];
    destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst;
    inv X;
    destruct ECS as [|[] ECS]; try tauto;
    destruct Hstsim as [Hstsim Hstsim'];
    destruct ECS as [|[] ECS]; try tauto;
    destruct Hstsim as [? [Htmn [? [? [? [? [? Hstsim]]]]]]]; subst;
    destruct Hstsim' as [Hstsim' _];
    destruct Hstsim' as [? [? [? [? [? [? [? Hstsim']]]]]]]; subst;
   simpl
  end.

Ltac undefined_state__State_simulation_r2l_tac3 :=
  match goal with
  | Hstsim: State_simulation _ _ _ ?St1 _ ?St2 |- _ =>
    destruct St2 as [[|[? [? ? ? tmn] CurCmds tmn' ?] ?] ?]; try tauto;
    destruct tmn; try tauto;
    destruct CurCmds; try tauto;
    destruct tmn'; try tauto;
    destruct St1 as [ECS ?];
    destruct Hstsim as [X [? [Hstsim [? [? H3]]]]]; subst;
    inv X;
    destruct ECS as [|[] ECS]; try tauto;
    destruct Hstsim as [Hstsim _];
    destruct Hstsim as [? [Htmn [? [? [H8 [? [? Hstsim]]]]]]]; subst;
    destruct H8 as [l5 [ps5 [cs5 EQ]]]; subst
  end.

Ltac undefined_state__State_simulation_r2l_tac41 :=
  match goal with
  | Hstsim: State_simulation _ _ _ ?St1 ?cfg2 ?St2 |- _ =>
    destruct St1 as [ECS ?];
    destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst;
    inv X;
    destruct ECS as [|[? ? ? ? Locals0] ECS]; try tauto;
    destruct Hstsim as [Hstsim _];
    destruct Hstsim as [? [? [? [? [H4 [H5 [? Hstsim]]]]]]]; subst
  end. 

Ltac undefined_state__d_State_simulation_r2l_tac43 := 
      match goal with
      | Hstsim: cmds_simulation _ _ _ _ (_::_) |- _ =>
      eapply cmds_simulation_cons_inv' in Hstsim; eauto; subst;
      destruct Hstsim as [c1' [J2 J3]]; subst
     end.

Lemma stacked_frame__unremovable: forall cfg EC1 EC2 ECS Mem0 pinfo sasinfo
  (HBinF: match Opsem.CurBB EC1 with 
   | block_intro _ _ _ (insn_return _ _ _) => True
   | block_intro _ _ _ (insn_return_void _) => True
   | _ => False
   end)
  (Hwfpp1 : OpsemPP.wf_State cfg
             {| Opsem.ECS := EC1 :: EC2 :: ECS; Opsem.Mem := Mem0 |}),
  ~ removable_State pinfo sasinfo
     {| Opsem.ECS := EC2 :: ECS; Opsem.Mem := Mem0 |}.
Proof.
  intros.
  destruct EC1, EC2; simpl in *. destruct cfg. destruct CurTargetData.
  destruct Hwfpp1 as 
     [_ [[_ [HbInF1 [_ [_ [_ _]]]]] [_ Hiscall]]].
  apply Hiscall in HbInF1.
  destruct CurBB as [? ? ? []]; tinv HBinF.
    destruct CurCmds0 as [|[]]; tinv HbInF1. tauto.
    destruct CurCmds0 as [|[]]; tinv HbInF1. tauto.
Qed.

Lemma mem_simulation__malloc_l2r': forall (pinfo : PhiInfo) sasinfo TD ECs M1 M2
  (Hmsim : mem_simulation pinfo sasinfo TD ECs M1 M2)
  (Mem'0 : mem) (tsz0 : sz) align0 gn mb M1'
  (H2 : malloc TD M1 tsz0 gn align0 = ret (M1', mb)),
  exists M2',
     malloc TD M2 tsz0 gn align0 = ret (M2', mb).
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmim3 Hmsim2]].
  unfold sas_mem_inj in *.
  inv_mbind. 
  destruct (@in_SAS_tails_ex pinfo sasinfo TD ECs) as [ombs J].
  apply_clear Hmsim2 in J.
  apply malloc_inv in H2. destruct H2 as [n0 [J1 [J2 J3]]].
  unfold malloc. fill_ctxhole.
  destruct_if; try congruence.
  remember (Mem.alloc M2 0 (Size.to_Z tsz0 * n0)) as R.
  destruct R as [M2' mb2].
  exists M2'.
  apply Mem.alloc_result in J3.
  symmetry in HeqR1.
  apply Mem.alloc_result in HeqR1.
  f_equal. f_equal.
  congruence.
Qed.

Lemma mem_simulation__mload_l2r: forall td gv M1 mp t align0 M2 ECs pinfo
  (H1 : mload td M1 mp t align0 = ret gv) sasinfo
  (Hmsim : mem_simulation pinfo sasinfo td ECs M1 M2),
  exists gv0, mload td M2 mp t align0 = ret gv0.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim3 Hmsim2]].
  apply mload_inv in H1.
  destruct H1 as [b [ofs [m [mc [J1 [J2 J3]]]]]]; subst.
  unfold sas_mem_inj in Hmsim2.
  inv_mbind. 
  destruct (@in_SAS_tails_ex pinfo sasinfo td ECs) as [ombs J].
  apply_clear Hmsim2 in J.
  unfold mload. repeat fill_ctxhole. simpl.
  eapply SASmsim.mload_aux_inj_ex with (b2:=b)(delta:=0) in J; eauto.
  replace (Int.signed 31 ofs + 0) with (Int.signed 31 ofs)  in J by omega.
  destruct J as [gv2 J]; eauto.
Qed.

Lemma mem_simulation__mstore_l2r: forall td M1 mp2 t gv1 align0 M1' M2 ECs
  (H3 : mstore td M1 mp2 t gv1 align0 = ret M1') pinfo sasinfo
  (Hmsim : mem_simulation pinfo sasinfo td ECs M1 M2),
  exists M2', 
    mstore td M2 mp2 t gv1 align0 = ret M2'.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim3 Hmsim2]].
  apply mstore_inversion in H3.
  destruct H3 as [b [ofs [cm [J1 J2]]]]; subst.
  unfold sas_mem_inj in *.
  inv_mbind.
  destruct (@in_SAS_tails_ex pinfo sasinfo td ECs) as [ombs J].
  apply_clear Hmsim2 in J.
  unfold mstore. simpl. 
  eapply SASmsim.mstore_aux_inject_id_mapped_inj in J; eauto.
  destruct J as [gv2 [J1 J4]]; eauto.
Qed.

Lemma mem_simulation__free_allocas_l2r : forall TD ECs1 pinfo sasinfo EC EC'
  (Hp: forall omb,
       in_SAS_tail pinfo sasinfo omb TD EC' ->
       in_SAS_tail pinfo sasinfo omb TD EC)
  als Mem1 Mem2 Mem1'
  (Hmsim : mem_simulation pinfo sasinfo TD (EC :: ECs1) Mem1 Mem2)
  (Hmlc: free_allocas TD Mem1 als = ret Mem1'),
  exists Mem2',
    free_allocas TD Mem2 als = ret Mem2' /\
    mem_simulation pinfo sasinfo TD (EC' :: ECs1) Mem1' Mem2'.
Proof.
  induction als; simpl; intros.
    uniq_result. exists Mem2. 
    split; auto.
      eapply mem_simulation__replace_head; eauto.

    inv_mbind.
    eapply mem_simulation__free_l2r with (Mem1':=m)(EC':=EC) in Hmsim; eauto.
    destruct Hmsim as [Mem2' [J1 J2]].
    rewrite J1.
    eapply IHals in J2; eauto.
Qed.

Lemma undefined_state__sas_State_simulation_r2l': forall pinfo cfg1 St1 cfg2
  St2 sasinfo 
  (Hwfpp1: OpsemPP.wf_State cfg1 St1) 
  (Hstsim : State_simulation pinfo sasinfo cfg1 St1 cfg2 St2)
  (Hnrem: ~removable_State pinfo sasinfo St1) 
  (Hundef: OpsemPP.undefined_state cfg2 St2),
  OpsemPP.undefined_state cfg1 St1.
Proof.
  intros.
  unfold OpsemPP.undefined_state in Hundef.
  destruct cfg2 as [S2 [los2 nts2] gl2 fs2].
  destruct cfg1 as [S1 [los1 nts1] gl1 fs1].
  repeat match goal with
  | Hundef : _ \/ _ |- _ => destruct Hundef as [Hundef | Hundef]
  end.
  Case "1".
    undefined_state__State_simulation_r2l_tac1.
    eapply cmds_simulation_nil_inv' in Hstsim; eauto; subst.
    assert (Hnrem' : ~
          removable_State pinfo sasinfo 
            {|
            Opsem.ECS := {|
                            Opsem.CurFunction := CurFunction2;
                            Opsem.CurBB := CurBB2;
                            Opsem.CurCmds := CurCmds1;
                            Opsem.Terminator := Terminator;
                            Opsem.Locals := Locals0;
                            Opsem.Allocas := Allocas0 |} :: ECS;
            Opsem.Mem := Mem0 |}).
      clear - Hwfpp1 H4.
      destruct H4 as [l5 [ps5 [cs5 H4]]]; subst.
      eapply stacked_frame__unremovable; eauto; simpl; auto.
    eapply cmds_simulation_cons_inv' in Hnrem'; eauto.
    destruct Hnrem' as [cs1' [J1 J3]]; subst.
    left. 
    remember (free_allocas (los2, nts2) Mem0 Allocas) as R.
    destruct R; auto.
    symmetry in HeqR. simpl in H2.
    eapply mem_simulation__free_allocas_l2r in HeqR; eauto.
    destruct HeqR as [M2' [Hfree [Hmsim']]].
    congruence.

  Case "2".
    undefined_state__State_simulation_r2l_tac1.
    eapply cmds_simulation_nil_inv' in Hstsim; eauto; subst.
    assert (Hnrem' : ~
          removable_State pinfo sasinfo
            {|
            Opsem.ECS := {|
                            Opsem.CurFunction := CurFunction2;
                            Opsem.CurBB := CurBB2;
                            Opsem.CurCmds := CurCmds1;
                            Opsem.Terminator := Terminator;
                            Opsem.Locals := Locals0;
                            Opsem.Allocas := Allocas0 |} :: ECS;
            Opsem.Mem := Mem0 |}).
      clear - Hwfpp1 H4.
      destruct H4 as [l5 [ps5 [cs5 H4]]]; subst.
      eapply stacked_frame__unremovable; eauto; simpl; auto.
    eapply cmds_simulation_cons_inv' in Hnrem'; eauto.
    destruct Hnrem' as [cs1' [J1 J3]]; subst.
    right. left. 
    destruct Hundef as [Hundef | Hundef]; auto.
    left.
    remember (free_allocas (los2, nts2) Mem0 Allocas) as R.
    destruct R; auto.
    symmetry in HeqR. simpl in H2.
    eapply mem_simulation__free_allocas_l2r in HeqR; eauto.
    destruct HeqR as [M2' [Hfree [Hmsim']]].
    congruence.

  Case "3".
    undefined_state__State_simulation_r2l_tac3.
    eapply cmds_simulation_nil_inv' in Hstsim; eauto; subst.
    right. right. left. auto.

  Case "4".
    right; right; right; left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' Locals] ?] ?]; try solve [
      tauto |
      inv_mbind; destruct Hundef as [gn [EQ Hundef]]; inv EQ; inv_mbind;
      undefined_state__State_simulation_r2l_tac41;
      undefined_state__d_State_simulation_r2l_tac43;
      repeat fill_ctxhole; exists gn; split; auto;
      remember (malloc (los2, nts2) Mem0 s gn a) as R;
      destruct R as [[]|]; auto;
      symmetry in HeqR2;
      eapply mem_simulation__malloc_l2r' in HeqR2; eauto 2;
      destruct HeqR2 as [Mem2' J4]; congruence
    ].

  Case "5".
    right. right. right. right. left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    inv_mbind; destruct Hundef as [gn [EQ Hundef]]; inv EQ; inv_mbind.
    undefined_state__State_simulation_r2l_tac41.
    undefined_state__d_State_simulation_r2l_tac43.
    repeat fill_ctxhole; exists gn. split; auto.
    remember (free (los2, nts2) Mem0 gn) as R.
    destruct R; auto.
    symmetry in HeqR1. simpl in H2.
    eapply mem_simulation__free_l2r' in HeqR1; eauto.
    destruct HeqR1 as [M2' Hfree].
    congruence.
   
  Case "6".
    right. right. right. right. right. left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    inv_mbind; destruct Hundef as [gvs [EQ Hundef]]; inv EQ; inv_mbind.
    undefined_state__State_simulation_r2l_tac41.
    undefined_state__d_State_simulation_r2l_tac43. 
    repeat fill_ctxhole; exists gvs. split; auto.
    remember (mload (los2, nts2) Mem0 gvs t a) as R.
    destruct R; auto.
    symmetry in HeqR1. simpl in H2.
    eapply mem_simulation__mload_l2r in HeqR1; eauto.
    destruct HeqR1 as [gv2 Hload].
    congruence.

  Case "7".
    right. right. right. right. right. right. left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    inv_mbind; destruct Hundef as [gv [mgv [EQ1 [EQ2 Hundef]]]]; 
      inv EQ1; inv EQ2; inv_mbind.
    undefined_state__State_simulation_r2l_tac41.
    undefined_state__d_State_simulation_r2l_tac43. 
    repeat fill_ctxhole; exists gv; exists mgv.
    split; auto.
    remember (mstore (los2, nts2) Mem0 mgv t gv a) as R.
    destruct R; auto.
    symmetry in HeqR2. simpl in H2.
    eapply mem_simulation__mstore_l2r in HeqR2; eauto.
    destruct HeqR2 as [M2' Hstore].
    congruence.

  Case "8".
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    right; right; right; right. right. right. right.
    undefined_state__State_simulation_r2l_tac41.
    inv_mbind.
    destruct Hundef as [fptr [EQ Hundef]]; inv EQ.
    inv_mbind.
    eapply cmds_simulation_cons_inv' in Hstsim; subst; eauto.
    destruct Hstsim as [cs2' [J1 J2]]; subst.
    repeat fill_ctxhole.
    exists fptr. split; auto.
    remember (OpsemAux.lookupExFdecViaPtr gl2 FunTable fptr) as R.
    destruct R as [[[]]|].
      inv_mbind.
      destruct Hundef as [gvs0 [EQ' Hundef]].
      dgvs_instantiate_inv.
      erewrite TopSim.lookupFdefViaPtr__simulation_None_l2r; eauto.
      erewrite TopSim.lookupExFdecViaPtr__simulation_r2l; eauto.
      simpl.
      exists l1. split; auto.
      remember (callExternalOrIntrinsics (los2, nts2) fs2 Mem0 i1 t0 
          (args2Typs a) d l1) as R.
      destruct R as [[[]]|]; auto.
      remember (Opsem.exCallUpdateLocals (los2, nts2) t n i0 o Locals) as R.
      destruct R; auto.
      eapply callExternalFunction__mem_simulation_l2r in H2; eauto.
        destruct H2 as [M2' [oresult2 [tr2 [W1 [W2 [W3 W4]]]]]]; subst.
        rewrite W1 in Hundef. rewrite <- HeqR4 in Hundef. auto.

      erewrite TopSim.lookupFdefViaPtr__simulation_None_l2r; eauto.
      erewrite TopSim.lookupExFdecViaPtr__simulation_None_r2l; eauto.
Qed.

Lemma undefined_state__sas_State_simulation_r2l: forall pinfo sasinfo cfg1 St1 cfg2
  St2 
  (Hwfpi: WF_PhiInfo pinfo) maxb (Hle: 0 <= maxb)
  (Hwfmg: MemProps.wf_globals maxb (OpsemAux.Globals cfg1)) 
  (Hwfcfg: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 St1) 
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 St1) 
  (Hpalloca: palloca_props.wf_State pinfo St1) 
  (Hstsim : State_simulation pinfo sasinfo cfg1 St1 cfg2 St2)
  (Hundef: OpsemPP.undefined_state cfg2 St2)
  (Hok: ~ sop_goeswrong cfg1 St1),
  exists St1', 
    Opsem.sop_star cfg1 St1 St1' E0 /\
    State_simulation pinfo sasinfo cfg1 St1' cfg2 St2 /\
    OpsemPP.undefined_state cfg1 St1'.
Proof.
  intros.
  destruct (removable_State_dec pinfo sasinfo St1) as [Hrem | Hnrem].
Case "removable".
    assert (G:=Hstsim).
    destruct cfg2 as [S2 [los2 nts2] gl2 fs2];
    destruct cfg1 as [S1 [los1 nts1] gl1 fs1].
    destruct St1 as [[|[? ? cs1 ? ?] ES1]];
    destruct St2 as [[|[? ? cs2 ? ?] ES2]]; try solve [
      auto |
      destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst; inv Hstsim |
      inv Hrem
    ].
    destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst;
    inv X; simpl;
    destruct Hstsim as [Hstsim Hstsim'];
    fold ECs_simulation in Hstsim'.
    destruct Hstsim as [? [Htmn [? [? [? [? [? Hstsim]]]]]]]; subst.
    destruct cs1; try solve [
      auto |
      apply cmds_simulation_nil_inv in Hstsim; try congruence |
      inv Hrem
    ].

    assert (G':=G). 
    eapply sas_is_sim in G; eauto.
    destruct G as [G _].
    remember 
            (Opsem.s_isFinialState {|           
              OpsemAux.CurSystem := S1;
              OpsemAux.CurTargetData := (los2, nts2);
              OpsemAux.CurProducts := gl1;
              OpsemAux.Globals := fs2;
              OpsemAux.FunTable := FunTable |}
              {|
              Opsem.ECS := {|
                           Opsem.CurFunction := CurFunction;
                           Opsem.CurBB := CurBB;
                           Opsem.CurCmds := c :: cs1;
                           Opsem.Terminator := Terminator0;
                           Opsem.Locals := Locals0;
                           Opsem.Allocas := Allocas0 |} :: ES1;
              Opsem.Mem := Mem |}) as R.
    destruct R.
    SCase "isFinal".
      simpl in HeqR. congruence.

    SCase "isntFinal".
    assert (J:=Hwfpp1).
    apply OpsemPP.progress in J; auto.
    destruct J as [Hfinal1 | [[IS1' [tr0 Hop1]] | Hundef1]]; try congruence.
      SSCase "step".
      clear G'.
      assert (Hop1':=Hop1).
      apply_clear G in Hop1'; auto.
      destruct Hop1' as [J1 J2]; subst.
      assert (Hop1':=Hop1).
      apply OpsemPP.preservation in Hop1'; auto.     
      assert (Hop1'':=Hop1).
      eapply Promotability.preservation in Hop1''; eauto.
      assert (Hop1''':=Hop1).
      eapply palloca_props.preservation in Hop1'''; eauto.
      assert (J1':=J1).
      eapply undefined_state__sas_State_simulation_r2l' in J1; eauto.
        exists IS1'.
        split.
          apply OpsemProps.sInsn__implies__sop_star; auto.
        split; auto.
          unfold State_simulation in J1'. auto.

        assert (
          c = insn_store (SAS_sid1 pinfo sasinfo) (PI_typ pinfo) 
                (SAS_value1 pinfo sasinfo) (value_id (PI_id pinfo)) 
                (PI_align pinfo)) as EQ.
          admit. (* uniqness *)
        subst.
        inv Hop1.
        eapply removable_State__non_removable_State; eauto.
          admit. (* uniqness *)

      SSCase "stuck".
      clear - Hundef1 Hok HeqR.
      apply undefined_state__stuck' in Hundef1.
      contradict Hok.
      exists {|Opsem.ECS := {|
                  Opsem.CurFunction := CurFunction;
                  Opsem.CurBB := CurBB;
                  Opsem.CurCmds := c :: cs1;
                  Opsem.Terminator := Terminator0;
                  Opsem.Locals := Locals0;
                  Opsem.Allocas := Allocas0 |} :: ES1;
               Opsem.Mem := Mem |}.
      exists E0.
      split; auto.

Case "unremovable".
    assert (J:=Hstsim).
    eapply undefined_state__sas_State_simulation_r2l' in Hstsim; eauto.
Qed.

Lemma sop_star__sas_State_simulation: forall pinfo sasinfo cfg1 IS1 cfg2 IS2 tr
  FS2 (Hwfpi: WF_PhiInfo pinfo) (Hwfpp: OpsemPP.wf_State cfg1 IS1) 
  (Hwfcfg: OpsemPP.wf_Config cfg1) maxb
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg1)) (Hless: 0 <= maxb)
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hpalloca: palloca_props.wf_State pinfo IS1) 
  (Hstsim : State_simulation pinfo sasinfo cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_star cfg2 IS2 FS2 tr) (Hok: ~ sop_goeswrong cfg1 IS1),
  exists FS1, Opsem.sop_star cfg1 IS1 FS1 tr /\
    State_simulation pinfo sasinfo cfg1 FS1 cfg2 FS2.
Proof.
  intros.
  generalize dependent cfg1.
  generalize dependent IS1.
  induction Hopstar; intros.
    exists IS1. split; auto.

    assert (forall (Hfinal1: Opsem.s_isFinialState cfg1 IS1 <> merror),
            exists FS1 : Opsem.State,
              Opsem.sop_star cfg1 IS1 FS1 (tr1 ** tr2) /\
              State_simulation pinfo sasinfo cfg1 FS1 cfg2 state3) as W.
      intros.
      apply s_isFinialState__sas_State_simulation_l2r' in Hstsim; auto.
      contradict H; eauto using s_isFinialState__stuck.
    assert (J:=Hwfpp).
    apply OpsemPP.progress in J; auto.
    destruct J as [Hfinal1 | [[IS1' [tr0 Hop1]] | Hundef1]]; auto.
      assert (OpsemPP.wf_State cfg1 IS1') as Hwfpp'.
        apply OpsemPP.preservation in Hop1; auto.
      assert (Promotability.wf_State maxb pinfo cfg1 IS1') as Hnoalias'.
        eapply Promotability.preservation in Hop1; eauto; try tauto.
      assert (palloca_props.wf_State pinfo IS1') as Hpalloca'.
        eapply palloca_props.preservation in Hop1; eauto.
      eapply sas_is_sim in Hstsim; eauto.
      destruct Hstsim as [Hstsim1 Hstsim2].
      destruct (@removable_State_dec pinfo sasinfo IS1) as [Hrm | Hnrm].
        eapply Hstsim1 in Hrm; eauto.
        destruct Hrm as [Hstsim EQ]; subst.
        admit. (* we should do induction on the measure of State_simulation *)

        eapply Hstsim2 in Hnrm; eauto.
        destruct Hnrm as [Hstsim EQ]; subst.
        eapply IHHopstar in Hstsim;
          eauto using sop_goeswrong__step, (@OpsemPP.preservation DGVs).
        destruct Hstsim as [FS1 [Hopstar1 Hstsim]].
        exists FS1.
        split; eauto.

      apply undefined_state__stuck' in Hundef1.
      remember (Opsem.s_isFinialState cfg1 IS1) as R.
      destruct R.
        apply W; congruence.
        contradict Hok. exists IS1. exists E0. split; auto.
Qed.

Lemma sop_div__sas_State_simulation: forall pinfo laainfo cfg1 IS1 cfg2 IS2 tr
  (Hwfpi: WF_PhiInfo pinfo) (Hwfpp: OpsemPP.wf_State cfg1 IS1) maxb
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg1)) (Hless: 0 <= maxb)
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hpalloca: palloca_props.wf_State pinfo IS1)
  (Hstsim : State_simulation pinfo laainfo cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_diverges cfg2 IS2 tr),
  Opsem.sop_diverges cfg1 IS1 tr.
Admitted. (* sop div *)

Lemma find_st_ld__sasinfo: forall l0 ps0 cs0 tmn0 i0 v cs (pinfo:PhiInfo) dones
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones) v0
  (i1 : id) (Hld : ret inr (i1, v0) = find_next_stld cs (PI_id pinfo))
  (HBinF : blockInFdefB (block_intro l0 ps0 cs0 tmn0) (PI_f pinfo) = true),
  exists sasinfo:SASInfo pinfo,
    SAS_sid1 pinfo sasinfo = i0 /\
    SAS_sid2 pinfo sasinfo = i1 /\
    SAS_value1 pinfo sasinfo = v /\
    SAS_value2 pinfo sasinfo = v0 /\
    SAS_block pinfo sasinfo = (block_intro l0 ps0 cs0 tmn0).
Admitted. (* sasinfo *)

Lemma sas_sim: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo : PhiInfo) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds)
  (Hst1 : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (v0 : value)
  (Hst2 : ret inr (i1, v0) = find_next_stld cs (PI_id pinfo))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
  (Hwfpi: WF_PhiInfo pinfo)
  S2 (Heq2: S2 = [module_intro los nts
                   (Ps1 ++
                     product_fdef
                     (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) :: Ps2)])
  (Hok: defined_program S2 main VarArgs)
  (HwfS : wf_system S2),
  program_sim
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (fdef_intro fh
           (List.map (remove_block i0)
             (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))) :: Ps2)]
    S2 main VarArgs.
Proof.
  intros.
  assert (blockInFdefB (block_intro l0 ps0 cs0 tmn0) (PI_f pinfo) = true)
    as HBinF.
    rewrite Heq. simpl. apply InBlocksB_middle.
  eapply find_st_ld__sasinfo in HBinF; eauto.
  destruct HBinF as [sasinfo [J1 [J2 [J3 [J4 J5]]]]]; subst.
  assert (Huniq:=HwfS). apply wf_system__uniqSystem in Huniq; auto.
  assert (system_simulation pinfo sasinfo
     [module_intro los nts
        (Ps1 ++
         product_fdef
           (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) :: Ps2)]
     [module_intro los nts
        (Ps1 ++
         product_fdef
           (remove_fdef (SAS_sid1 pinfo sasinfo)
              (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)))
         :: Ps2)]) as Hssim.
    constructor; auto.
    repeat split; auto.
    simpl in Huniq. destruct Huniq as [[_ [_ Huniq]] _].
    unfold TopSim.products_simulation. unfold fsim. unfold Fsim.
    apply uniq_products_simulation; auto.

Ltac sas_sim_init :=
match goal with
| H: Opsem.s_genInitState [module_intro ?los ?nts _] _ _ _ = Some (?cfg, ?IS), 
  pinfo: PhiInfo |- _ =>
    assert (OpsemPP.wf_Config cfg /\ OpsemPP.wf_State cfg IS) as Hwfst';
      try solve [eapply s_genInitState__opsem_wf in H; eauto using sas_wfS];
    eapply s_genInitState__sas_State_simulation in H; eauto;
    destruct H as [cfg1 [IS1 [Hinit Hstsim]]];
    assert (OpsemPP.wf_Config cfg1 /\ OpsemPP.wf_State cfg1 IS1) as Hwfst;
      try solve [eapply s_genInitState__opsem_wf; eauto];
    assert (exists maxb,
              MemProps.wf_globals maxb (OpsemAux.Globals cfg1) /\ 0 <= maxb /\
              Promotability.wf_State maxb pinfo cfg1 IS1) as Hprom;
      try solve [eapply Promotability.s_genInitState__wf_globals_promotable; eauto];
    destruct Hprom as [maxb [Hwfg [Hless Hprom]]];
    assert (palloca_props.wf_State pinfo IS1) as Hpalloca;
      try solve [eapply palloca_props.s_genInitState__palloca; eauto]
end.

Ltac sas_sim_end :=
match goal with
| Hstsim' : State_simulation ?pinfo _ ?cfg1 ?FS1 ?cfg ?FS,
  Hopstar1 : Opsem.sop_star ?cfg1 _ ?FS1 _,
  Hwfg: MemProps.wf_globals ?maxb _  |- _ =>
    assert (OpsemPP.wf_State cfg FS) as Hwfst''; 
      try solve [eapply OpsemPP.preservation_star; eauto; try tauto];
    assert (OpsemPP.wf_State cfg1 FS1) as Hwfst1'';
      try solve [eapply OpsemPP.preservation_star; eauto; try tauto];
    assert (palloca_props.wf_State pinfo FS1); try solve 
      [eapply palloca_props.preservation_star in Hopstar1; eauto; try tauto];
    assert (Promotability.wf_State maxb pinfo cfg1 FS1) as Hprom'; try solve [
      eapply Promotability.preservation_star in Hopstar1; eauto; try tauto
    ]
end.

  constructor; auto.
    intros tr t Hconv.
    inv Hconv.
    sas_sim_init.
    eapply sop_star__sas_State_simulation in Hstsim; 
      eauto using defined_program__doesnt__go_wrong; try tauto.
    destruct Hstsim as [FS1 [Hopstar1 Hstsim']].
    sas_sim_end.
    eapply s_isFinialState__sas_State_simulation_r2l in Hstsim';
      eauto using sop_goeswrong__star, defined_program__doesnt__go_wrong; try tauto.
    destruct Hstsim' as [FS1' [Hopstar1' [Hstsim'' Hfinal]]].
    assert (Opsem.sop_star cfg1 IS1 FS1' tr) as Hopstar1''.
      rewrite <- E0_right.
      eapply OpsemProps.sop_star_trans; eauto.
    econstructor; eauto.

    intros tr Hdiv.
    inv Hdiv.
    sas_sim_init.
    eapply sop_div__sas_State_simulation in Hstsim; eauto; try tauto.
    destruct Hstsim as [FS1 Hopdiv1].
    econstructor; eauto.

    intros tr t Hgowrong.
    inv Hgowrong.
    assert (OpsemPP.wf_Config cfg /\ OpsemPP.wf_State cfg t) as HwfSt.
      eapply s_genInitState__opsem_wf in H; eauto using sas_wfS.
      destruct H as [Hcfg2 HwfSt2].
      apply OpsemPP.preservation_star in H0; auto.
    assert (OpsemPP.undefined_state cfg t) as Hundef.
      apply stuck__undefined_state in H2; try solve [auto | tauto].
    sas_sim_init.
    eapply sop_star__sas_State_simulation in Hstsim;
      eauto using defined_program__doesnt__go_wrong; try tauto.
    destruct Hstsim as [FS1 [Hopstar1 Hstsim']].
    sas_sim_end.
    assert (Hundef':=Hundef).
    eapply undefined_state__sas_State_simulation_r2l in Hundef'; 
      try solve [eauto using sop_goeswrong__star, defined_program__doesnt__go_wrong | tauto].
    destruct Hundef' as [FS1' [Hopstar2 [Hsim Hundef']]].
    assert (Opsem.s_isFinialState cfg1 FS1' = merror) as Hfinal'.
      apply OpsemPP.preservation_star in Hopstar2; auto; try tauto.
      eapply s_isFinialState__sas_State_simulation_None_r2l in H2; 
        try solve [eauto | tauto].
    apply undefined_state__stuck' in Hundef'.
    exists (tr**E0). exists FS1'.
    econstructor; eauto using (@OpsemProps.sop_star_trans DGVs).   
Qed.

Lemma sas_wfPI: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo : PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds)
  (Hst1 : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (v0 : value)
  (Hst2 : ret inr (i1, v0) = find_next_stld cs (PI_id pinfo))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS :
     wf_system 
       [module_intro los nts
         (Ps1 ++
          product_fdef
            (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
          :: Ps2)]),
  WF_PhiInfo
    (update_pinfo pinfo
      (fdef_intro fh
        (List.map (remove_block i0)
           (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)))).
Admitted. (* prev WF *)

