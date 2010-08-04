Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../../../theory/metatheory".
Require Import ssa.
Require Import List.
Require Export targetdata.
Require Import monad.
Require Import Arith.
Require Import Metatheory.
Require Import ssa_mem.
Require Import genericvalues.
Require Import ssa_dynamic.
Require Import opsem_conv.
Require Import trace.
Require Import symexe_def.

Export LLVMsyntax.
Export LLVMlib.

Tactic Notation "se_db_mutind_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbCall_intro" | 
    c "dbSubblock_intro" | c "dbSubblocks_nil" | c "dbSubblocks_cons" | 
    c "dbBlock_intro" | c "dbBlocks_nil" | c "dbBlocks_cons" | 
    c "dbFdef_func" | c "dbFdef_proc" ].

Tactic Notation "se_dbCmd_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbBop" | c "dbExtractValue" | c "dbInsertValue" |
    c "dbMalloc" | c "dbFree" |
    c "dbAlloca" | c "dbLoad" | c "dbStore" | c "dbGEP" |
    c "dbExt" | c "dbCast" | c "dbIcmp" |  c "dbSelect" ].

Tactic Notation "se_dbTerminator_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbBranch" | c "dbBranch_uncond" ].

Tactic Notation "se_dbCmds_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbCmds_nil" | c "dbCmds_cons" ].

(****************************************************)
(* seop -> llvmop *)

Lemma seop_dbCmd__llvmop_dbInsn : forall TD lc als gl Mem c lc' gl' als' Mem' tr S Ps F B ECs arg tmn cs,
  SimpleSE.dbCmd TD lc als gl Mem c lc' als' gl' Mem' tr ->
  LLVMopsem.dbInsn 
    (mkState S TD Ps ((mkEC F B (c::cs) tmn lc arg als)::ECs) gl Mem)
    (mkState S TD Ps ((mkEC F B cs tmn lc' arg als')::ECs) gl' Mem')
    tr.
Proof.
  intros TD lc als gl Mem0 c lc' gl' als' Mem' tr S Ps F B ECs arg0 tmn cs H.
  (se_dbCmd_cases (destruct H) Case); eauto.
Qed.
  
Lemma seop_dbCmds__llvmop_dbop : forall TD lc als gl Mem cs cs' lc' gl' als' Mem' tr S Ps F B ECs arg tmn,
  SimpleSE.dbCmds TD lc als gl Mem cs lc' als' gl' Mem' tr ->
  LLVMopsem.dbop 
    (mkState S TD Ps ((mkEC F B (cs++cs') tmn lc arg als)::ECs) gl Mem)
    (mkState S TD Ps ((mkEC F B cs' tmn lc' arg als')::ECs) gl' Mem')
    tr.
Proof.
  intros TD lc als gl Mem0 cs cs' lc' gl' als' Mem' tr S Ps F B ECs arg0 tmn H.
  generalize dependent S.
  generalize dependent Ps.
  generalize dependent F.
  generalize dependent B.
  generalize dependent ECs.
  generalize dependent arg0.
  generalize dependent tmn.
  generalize dependent cs'.
  (se_dbCmds_cases (induction H) Case);intros; auto.
    simpl_env.
    apply seop_dbCmd__llvmop_dbInsn with (S:=S)(Ps:=Ps)(F:=F)(B:=B)(ECs:=ECs)(arg:=arg0)(tmn:=tmn)(cs:=cs++cs') in H; auto.
    eapply dbop_cons; eauto.
      apply IHdbCmds.
Qed.

Lemma seop_dbTerminator__llvmop_dbInsn : forall TD lc als gl Mem lc' tr S Ps F B ECs arg tmn l' ps' cs' tmn',
  SimpleSE.dbTerminator TD F B lc gl tmn (block_intro l' ps' cs' tmn') lc' tr ->
  LLVMopsem.dbInsn 
    (mkState S TD Ps ((mkEC F B nil tmn lc arg als)::ECs) gl Mem)
    (mkState S TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' arg als)::ECs) gl Mem)
    tr.
Proof.
  intros TD lc als gl Mem0 lc' tr S Ps F B ECs arg0 tmn l' ps' cs' tmn' H.
  inversion H; subst.
    eapply dbBranch; eauto.
      rewrite H13.
      admit. (*lookup*)
    eapply dbBranch_uncond; eauto.    
      rewrite H12.
      admit. (*lookup*)
Qed.

Definition seop_dbCall__llvmop_dbCall_prop S TD Ps lc gl Mem0 call0 lc' gl' Mem' tr
  (db:SimpleSE.dbCall S TD Ps lc gl Mem0 call0 lc' gl' Mem' tr) :=
  forall F B ECs arg tmn cs als,
  LLVMopsem.dbInsn 
    (mkState S TD Ps ((mkEC F B (call0::cs) tmn lc arg als)::ECs) gl Mem0)
    (mkState S TD Ps ((mkEC F B cs tmn lc' arg als)::ECs) gl' Mem')
    tr.
Definition seop_dbSubblock__llvmop_dbop_prop S TD Ps lc als gl Mem cs lc' als' gl' Mem' tr
  (db:SimpleSE.dbSubblock S TD Ps lc als gl Mem cs lc' als' gl' Mem' tr) :=
  forall F B ECs arg tmn cs',
  LLVMopsem.dbop 
    (mkState S TD Ps ((mkEC F B (cs++cs') tmn lc arg als)::ECs) gl Mem)
    (mkState S TD Ps ((mkEC F B cs' tmn lc' arg als')::ECs) gl' Mem')
    tr.
Definition seop_dbSubblocks__llvmop_dbop_prop S TD Ps lc als gl Mem cs lc' als' gl' Mem' tr
  (db:SimpleSE.dbSubblocks S TD Ps lc als gl Mem cs lc' als' gl' Mem' tr) :=
  forall F B ECs arg tmn cs',
  LLVMopsem.dbop 
    (mkState S TD Ps ((mkEC F B (cs++cs') tmn lc arg als)::ECs) gl Mem)
    (mkState S TD Ps ((mkEC F B cs' tmn lc' arg als')::ECs) gl' Mem')
    tr.
Definition seop_dbBlock__llvmop_dbop_prop S TD Ps F arg state state' tr
  (db:SimpleSE.dbBlock S TD Ps F arg state state' tr) :=
  forall l ps cs tmn lc als gl Mem l' ps' cs' tmn' lc' als' gl' Mem' ECs,
  state = SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps cs tmn) lc als) gl Mem ->
  state' = SimpleSE.mkState (SimpleSE.mkEC (block_intro l' ps' cs' tmn') lc' als') gl' Mem' ->
  LLVMopsem.dbop 
    (mkState S TD Ps ((mkEC F (block_intro l ps cs tmn) cs tmn lc arg als)::ECs) gl Mem)
    (mkState S TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' arg als')::ECs) gl' Mem')
    tr.
Definition seop_dbBlocks__llvmop_dbop_prop S TD Ps F arg state state' tr
  (db:SimpleSE.dbBlocks S TD Ps F arg state state' tr) :=
  forall l ps cs tmn lc als gl Mem l' ps' cs' tmn' lc' als' gl' Mem' ECs,
  state = SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps cs tmn) lc als) gl Mem ->
  state' = SimpleSE.mkState (SimpleSE.mkEC (block_intro l' ps' cs' tmn') lc' als') gl' Mem' ->
  LLVMopsem.dbop 
    (mkState S TD Ps ((mkEC F (block_intro l ps cs tmn) cs tmn lc arg als)::ECs) gl Mem)
    (mkState S TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' arg als')::ECs) gl' Mem')
    tr.
Definition seop_dbFdef__llvmop_dbFdef_prop fid rt lp S TD Ps lc gl Mem lc' gl' als' Mem' B' Rid oResult tr
  (db:SimpleSE.dbFdef fid rt lp S TD Ps lc gl Mem lc' gl' als' Mem' B' Rid oResult tr) :=
  forall ECs,
  LLVMopsem.dbFdef fid rt lp S TD Ps ECs lc gl Mem lc' gl' als' Mem' B' Rid oResult tr.

Lemma dbop_trans : forall state1 state2 state3 tr1 tr2,
  dbop state1 state2 tr1 ->
  dbop state2 state3 tr2 ->
  dbop state1 state3 (trace_app tr1 tr2).
Proof.
  intros state1 state2 state3 tr1 tr2 H.
  generalize dependent state3.
  generalize dependent tr2.
  induction H; intros; auto.
    rewrite <- trace_app_commute. eauto.
Qed.

Lemma dbInsn__dbop : forall state1 state2 tr,
  dbInsn state1 state2 tr ->
  dbop state1 state2 tr.
Proof.
  intros.
  rewrite <- trace_app_nil__eq__trace.
  eapply dbop_cons; eauto.
Qed.

Lemma seop__llvmop :
  (forall S1 TD Ps1 lc gl Mem0 call0 lc' gl' Mem' tr db, 
     seop_dbCall__llvmop_dbCall_prop S1 TD Ps1 lc gl Mem0 call0 lc' gl' Mem' tr db) /\
  (forall S1 TD Ps1 lc als gl Mem sb1 lc' als' gl' Mem' tr db,
     seop_dbSubblock__llvmop_dbop_prop S1 TD Ps1 lc als gl Mem sb1 lc' als' gl' Mem' tr db) /\
  (forall S1 TD Ps1 lc als gl Mem sbs1 lc' als' gl' Mem' tr db,
     seop_dbSubblocks__llvmop_dbop_prop S1 TD Ps1 lc als gl Mem sbs1 lc' als' gl' Mem' tr db) /\
  (forall S1 TD Ps1 F1 arg state1 state2 tr db,
     seop_dbBlock__llvmop_dbop_prop S1 TD Ps1 F1 arg state1 state2 tr db) /\
  (forall S1 TD Ps1 F1 lp state1 state2 tr db,
     seop_dbBlocks__llvmop_dbop_prop S1 TD Ps1 F1 lp state1 state2 tr db) /\
  (forall fid rt lp S1 TD Ps1 lc gl Mem lc' gl' als' Mem' B' Rid oResult tr db,
     seop_dbFdef__llvmop_dbFdef_prop fid rt lp S1 TD Ps1 lc gl Mem lc' gl' als' Mem' B' Rid oResult tr db).
Proof.
(se_db_mutind_cases
  apply SimpleSE.db_mutind with
    (P  := seop_dbCall__llvmop_dbCall_prop)
    (P0 := seop_dbSubblock__llvmop_dbop_prop)
    (P1 := seop_dbSubblocks__llvmop_dbop_prop)
    (P2 := seop_dbBlock__llvmop_dbop_prop)
    (P3 := seop_dbBlocks__llvmop_dbop_prop)
    (P4 := seop_dbFdef__llvmop_dbFdef_prop) Case);
  unfold seop_dbCall__llvmop_dbCall_prop, 
         seop_dbFdef__llvmop_dbFdef_prop, seop_dbSubblock__llvmop_dbop_prop,
         seop_dbSubblocks__llvmop_dbop_prop, seop_dbBlock__llvmop_dbop_prop,
         seop_dbBlocks__llvmop_dbop_prop; intros; subst; eauto.
Case "dbSubblock_intro".
  apply seop_dbCmds__llvmop_dbop with (Ps:=Ps)(F:=F)(B:=B)(ECs:=ECs)(arg:=arg0)(tmn:=tmn)(S:=S)(cs':=call0::cs') in d.
  eapply dbop_trans; simpl_env ; eauto.
    apply dbInsn__dbop; auto. 
      apply H.
Case "dbSubblocks_cons".
  rewrite app_ass.
  apply dbop_trans with (state2:=mkState S TD Ps (mkEC F B (cs'++cs'0) tmn lc2 arg0 als2::ECs) gl2 Mem2); eauto.
Case "dbBlock_intro".
  inversion H0; subst. clear H0.
  inversion H1; subst. clear H1.
  rewrite <- trace_app_commute.
  apply dbop_trans with (state2:=mkState S TD Ps (mkEC F (block_intro l1 ps0 (cs++cs') tmn0) cs' tmn0 lc2 arg0 als2::ECs) gl2 Mem2); eauto.
    apply seop_dbCmds__llvmop_dbop with (Ps:=Ps)(F:=F)(B:=block_intro l1 ps0 (cs++cs') tmn0)(ECs:=ECs)(arg:=arg0)(S:=S)(cs':=nil)(tmn:=tmn0) in d0.
    apply seop_dbTerminator__llvmop_dbInsn with (Ps:=Ps)(F:=F)(ECs:=ECs)(arg:=arg0)(S:=S)(als:=als')(Mem:=Mem') in d1.
    simpl_env in d0.
    apply dbop_trans with (state2:=mkState S TD Ps (mkEC F (block_intro l1 ps0 (cs++cs') tmn0) nil tmn0 lc3 arg0 als'::ECs) gl' Mem'); auto.
      apply dbInsn__dbop; auto. 
Case "dbBlocks_nil".
  inversion H0; subst. clear H0.
  auto.
Case "dbBlocks_cons".
  inversion d; subst.
  destruct B'.
  apply dbop_trans with (state2:=mkState S TD Ps (mkEC F (block_intro l1 l2 l3 t) l3 t lc4 arg0 als3::ECs) gl3 Mem3); eauto.
Case "dbFdef_func".
  apply dbFdef_func with (l':=l1)(ps':=ps1)(cs':=cs1)(tmn':=tmn1)(la:=la)(lb:=lb); auto.
    rewrite <- e. 
    admit. (*lookup*)

    rewrite <- trace_app_commute.
    apply seop_dbCmds__llvmop_dbop with (Ps:=Ps)(F:=fdef_intro (fheader_intro rt fid la) lb)(B:=block_intro l2 ps2 (cs21++cs22) (insn_return rid rt Result))(ECs:=ECs)(arg:=(params2GVs TD lp lc gl))(S:=S)(cs':=nil)(tmn:=insn_return rid rt Result) in d1.
    simpl_env in d1. 
    apply dbop_trans with (state2:=mkState S TD Ps (mkEC (fdef_intro (fheader_intro rt fid la) lb) (block_intro l2 ps2 (cs21++cs22) (insn_return rid rt Result)) (cs21++cs22) (insn_return rid rt Result) lc1 (params2GVs TD lp lc gl) als1::ECs) gl1 Mem1); auto.
    apply dbop_trans with (state2:=mkState S TD Ps (mkEC (fdef_intro (fheader_intro rt fid la) lb) (block_intro l2 ps2 (cs21++cs22) (insn_return rid rt Result)) cs22 (insn_return rid rt Result) lc2 (params2GVs TD lp lc gl) als2::ECs) gl2 Mem2); auto.
Case "dbFdef_proc".
  apply dbFdef_proc with (l':=l1)(ps':=ps1)(cs':=cs1)(tmn':=tmn1)(la:=la)(lb:=lb); auto.
    rewrite <- e. 
    admit. (*lookup*)

    rewrite <- trace_app_commute.
    apply seop_dbCmds__llvmop_dbop with (Ps:=Ps)(F:=fdef_intro (fheader_intro rt fid la) lb)(B:=block_intro l2 ps2 (cs21++cs22) (insn_return_void rid))(ECs:=ECs)(arg:=(params2GVs TD lp lc gl))(S:=S)(cs':=nil)(tmn:=insn_return_void rid) in d1.
    simpl_env in d1. 
    apply dbop_trans with (state2:=mkState S TD Ps (mkEC (fdef_intro (fheader_intro rt fid la) lb) (block_intro l2 ps2 (cs21++cs22) (insn_return_void rid)) (cs21++cs22) (insn_return_void rid) lc1 (params2GVs TD lp lc gl) als1::ECs) gl1 Mem1); auto.
    apply dbop_trans with (state2:=mkState S TD Ps (mkEC (fdef_intro (fheader_intro rt fid la) lb) (block_intro l2 ps2 (cs21++cs22) (insn_return_void rid)) cs22 (insn_return_void rid) lc2 (params2GVs TD lp lc gl) als2::ECs) gl2 Mem2); auto.
Qed.

Lemma seop_dbCall__llvmop_dbCall : forall S TD Ps lc gl Mem0 call0 lc' gl' Mem' tr F B ECs arg tmn cs als,
  SimpleSE.dbCall S TD Ps lc gl Mem0 call0 lc' gl' Mem' tr ->
  LLVMopsem.dbInsn 
    (mkState S TD Ps ((mkEC F B (call0::cs) tmn lc arg als)::ECs) gl Mem0)
    (mkState S TD Ps ((mkEC F B cs tmn lc' arg als)::ECs) gl' Mem')
    tr.
Proof.
  intros.
  destruct seop__llvmop as [J _]. 
  apply J; auto.
Qed.

Lemma seop_dbSubblock__llvmop_dbop : forall S TD Ps lc als gl Mem cs lc' als' gl' Mem' tr F B ECs arg tmn cs',
  SimpleSE.dbSubblock S TD Ps lc als gl Mem cs lc' als' gl' Mem' tr ->
  LLVMopsem.dbop 
    (mkState S TD Ps ((mkEC F B (cs++cs') tmn lc arg als)::ECs) gl Mem)
    (mkState S TD Ps ((mkEC F B cs' tmn lc' arg als')::ECs) gl' Mem')
    tr.
Proof.
  intros.
  destruct seop__llvmop as [_ [J _]]. 
  apply J; auto.
Qed.

Lemma seop_dbSubblocks__llvmop_dbop : forall S TD Ps lc als gl Mem cs lc' als' gl' Mem' tr F B ECs arg tmn cs',
  SimpleSE.dbSubblocks S TD Ps lc als gl Mem cs lc' als' gl' Mem' tr ->
  LLVMopsem.dbop 
    (mkState S TD Ps ((mkEC F B (cs++cs') tmn lc arg als)::ECs) gl Mem)
    (mkState S TD Ps ((mkEC F B cs' tmn lc' arg als')::ECs) gl' Mem')
    tr.
Proof.
  intros.
  destruct seop__llvmop as [_ [_ [J _]]]. 
  apply J; auto.
Qed.

Lemma seop_dbBlock__llvmop_dbop :  forall S TD Ps F arg tr l ps cs tmn lc als gl Mem l' ps' cs' tmn' lc' als' gl' Mem' ECs,
  SimpleSE.dbBlock S TD Ps F arg 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps cs tmn) lc als) gl Mem) 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l' ps' cs' tmn') lc' als') gl' Mem')
    tr ->
  LLVMopsem.dbop 
    (mkState S TD Ps ((mkEC F (block_intro l ps cs tmn) cs tmn lc arg als)::ECs) gl Mem)
    (mkState S TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' arg als')::ECs) gl' Mem')
    tr.
Proof.
  intros.
  destruct seop__llvmop as [_ [_ [_ [J _]]]]. 
  unfold seop_dbBlock__llvmop_dbop_prop in J.
  eapply J; eauto.
Qed.

Lemma seop_dbBlocks__llvmop_dbop : forall S TD Ps F arg tr l ps cs tmn lc als gl Mem l' ps' cs' tmn' lc' als' gl' Mem' ECs,
  SimpleSE.dbBlocks S TD Ps F arg 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps cs tmn) lc als) gl Mem) 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l' ps' cs' tmn') lc' als') gl' Mem')
    tr ->  
  LLVMopsem.dbop 
    (mkState S TD Ps ((mkEC F (block_intro l ps cs tmn) cs tmn lc arg als)::ECs) gl Mem)
    (mkState S TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' arg als')::ECs) gl' Mem')
    tr.
Proof.
  intros.
  destruct seop__llvmop as [_ [_ [_ [_ [J _]]]]]. 
  unfold seop_dbBlocks__llvmop_dbop_prop in J.
  eapply J; eauto.
Qed.

Lemma seop_dbFdef__llvmop_dbFdef : forall fid rt lp S TD Ps lc gl Mem lc' gl' als' Mem' B' Rid oResult tr ECs,
  SimpleSE.dbFdef fid rt lp S TD Ps lc gl Mem lc' gl' als' Mem' B' Rid oResult tr ->
  LLVMopsem.dbFdef fid rt lp S TD Ps ECs lc gl Mem lc' gl' als' Mem' B' Rid oResult tr.
Proof.
  intros.
  destruct seop__llvmop as [_ [_ [_ [_ [_ J]]]]]. 
  eapply J; eauto.
Qed.

(****************************************************)
(* llvmop -> seop *)

Lemma dbBlock__dbBlocks : forall S TD Ps F arg state state' tr,
  SimpleSE.dbBlock S TD Ps F arg state state' tr -> 
  SimpleSE.dbBlocks S TD Ps F arg state state' tr.
Proof.
  intros S TD Ps F arg0 state state' tr H.
  rewrite <- trace_app_nil__eq__trace.
  eapply SimpleSE.dbBlocks_cons; eauto.
Qed.

Lemma dbTerminator__dbBlock : forall TD F lc gl tmn l ps B' lc' tr als Ps S arg Mem,
  SimpleSE.dbTerminator TD F (block_intro l ps nil tmn) lc gl tmn B' lc' tr ->
  SimpleSE.dbBlock S TD Ps F arg 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps nil tmn) lc als) gl Mem)
    (SimpleSE.mkState (SimpleSE.mkEC B' lc' als) gl Mem)
    tr.
Proof.
  intros TD F lc gl tmn l0 ps B' lc' tr als Ps S arg0 Mem0 H.
  rewrite <- nil_app_trace__eq__trace.
  rewrite <- nil_app_trace__eq__trace with (tr:=trace_nil).
  assert (@nil cmd=nil++nil) as EQ. auto.
  rewrite EQ.
  apply SimpleSE.dbBlock_intro with (lc2:=lc)(als2:=als)(gl2:=gl)(Mem2:=Mem0)(lc3:=lc); auto.
Qed.

Lemma dbCmd_dbSubblock__dbSubblock : forall S TD Ps lc als gl Mem0 c lc1 als1 gl1 Mem1 tr1 cs lc2 als2 gl2 Mem2 tr2,
  SimpleSE.dbCmd TD lc als gl Mem0 c lc1 als1 gl1 Mem1 tr1 ->
  SimpleSE.dbSubblock S TD Ps lc1 als1 gl1 Mem1 cs lc2 als2 gl2 Mem2 tr2 ->
  SimpleSE.dbSubblock S TD Ps lc als gl Mem0 (c::cs) lc2 als2 gl2 Mem2 (trace_app tr1 tr2).
Proof.
  intros S TD Ps lc als gl Mem0 c lc1 als1 gl1 Mem1 tr1 cs lc2 als2 gl2 Mem2 tr2 H1 H2.
  inversion H2; subst.  
  rewrite trace_app_commute.
  assert (c::cs0++call0::nil = (c::cs0)++call0::nil) as EQ. auto.
  rewrite EQ.
  eapply SimpleSE.dbSubblock_intro; eauto.
Qed.

Lemma dbCmd_dbSubblocks__dbCmd_or_dbSubblocks : forall S TD Ps lc als gl Mem0 c lc1 als1 gl1 Mem1 tr1 cs lc2 als2 gl2 Mem2 tr2,
  SimpleSE.dbCmd TD lc als gl Mem0 c lc1 als1 gl1 Mem1 tr1 ->
  SimpleSE.dbSubblocks S TD Ps lc1 als1 gl1 Mem1 cs lc2 als2 gl2 Mem2 tr2 ->
  (SimpleSE.dbCmd TD lc als gl Mem0 c lc2 als2 gl2 Mem2 tr1 /\ 
   cs = nil /\ tr2 = trace_nil /\ 
   lc1 = lc2 /\ als1 = als2 /\ gl1 = gl2 /\ Mem1 = Mem2 
  ) \/
  (SimpleSE.dbSubblocks S TD Ps lc als gl Mem0 (c::cs) lc2 als2 gl2 Mem2 (trace_app tr1 tr2)).
Proof.
  intros S TD Ps lc als gl Mem0 c lc1 als1 gl1 Mem1 tr1 cs lc2 als2 gl2 Mem2 tr2 H1 H2.
  inversion H2; subst.
    left. repeat (split; auto).
    right. 
      rewrite trace_app_commute.
      assert (c::cs0++cs'=(c::cs0)++cs') as EQ. auto.
      rewrite EQ.
      eapply SimpleSE.dbSubblocks_cons; eauto using dbCmd_dbSubblock__dbSubblock.
Qed.

Lemma dbInsn__inv : forall S1 TD1 Ps1 F1 l1 ps1 cs1 tmn1 c cs tmn3 lc1 arg1 als1 ECs1 gl1 Mem1
                         S2 TD2 Ps2 F2 l2 ps2 cs2 tmn2 tmn4 lc2 arg2 als2 ECs2 gl2 Mem2 tr,
  dbInsn 
    (mkState S1 TD1 Ps1 (mkEC F1 (block_intro l1 ps1 cs1 tmn1) (c::cs) tmn3 lc1 arg1 als1::ECs1) gl1 Mem1) 
    (mkState S2 TD2 Ps2 (mkEC F2 (block_intro l2 ps2 cs2 tmn2) cs tmn4 lc2 arg2 als2::ECs2) gl2 Mem2)
    tr ->
  S1 = S2 /\ TD1 = TD2 /\ Ps1 = Ps2 /\ F1 = F2 /\ l1 = l2 /\ ps1 = ps2 /\
  cs1 = cs2 /\ tmn1 = tmn2 /\ tmn3 = tmn4.
Proof.
  intros.
  inversion H; subst; repeat (split; auto).
Qed.


Lemma dbTerminator_test : forall TD F l1 ps1 cs1 tmn1 lc1 gl1 B lc2 tr cs2,
  SimpleSE.dbTerminator TD F (block_intro l1 ps1 cs1 tmn1) lc1 gl1 tmn1 B lc2 tr ->
  SimpleSE.dbTerminator TD F (block_intro l1 ps1 cs2 tmn1) lc1 gl1 tmn1 B lc2 tr.
Proof.
  intros.
  inversion H; subst. clear H.
    eapply SimpleSE.dbBranch; eauto.
       admit. (*block*)
    eapply SimpleSE.dbBranch_uncond; eauto.
       admit. (*block*)
Qed.

Lemma dbCmd_dbBlock__dbBlock : forall S TD Ps lc als gl Mem0 c lc1 als1 gl1 Mem1 tr1 lc2 als2 gl2 Mem2 tr2 
  l1 ps1 cs1 tmn1 B F arg,
  SimpleSE.dbCmd TD lc als gl Mem0 c lc1 als1 gl1 Mem1 tr1 ->
  SimpleSE.dbBlock S TD Ps F arg 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 cs1 tmn1) lc1 als1) gl1 Mem1)
    (SimpleSE.mkState (SimpleSE.mkEC B lc2 als2) gl2 Mem2)
    tr2 ->
  SimpleSE.dbBlock S TD Ps F arg 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 (c::cs1) tmn1) lc als) gl Mem0)
    (SimpleSE.mkState (SimpleSE.mkEC B lc2 als2) gl2 Mem2)
    (trace_app tr1 tr2).
Proof.
  intros S TD Ps lc als gl Mem0 c lc1 als1 gl1 Mem1 tr1 lc2 als2 gl2 Mem2 tr2 
    l1 ps1 cs1 tmn1 B F arg0 H1 H2.
  inversion H2; subst.  
  rewrite trace_app_commute.
  rewrite trace_app_commute.
  apply dbCmd_dbSubblocks__dbCmd_or_dbSubblocks with (lc:=lc)(als:=als)(gl:=gl)(Mem0:=Mem0)(c:=c)(tr1:=tr1) in H20; auto.
  destruct H20 as [[J11 [EQ [EQ' [EQ1 [EQ2 [EQ3 EQ4]]]]]] | J11]; subst.
    assert (c::nil++cs'=nil++c::cs') as EQ. auto.
    rewrite EQ. clear EQ.
    rewrite trace_app_nil__eq__trace.
    rewrite <- nil_app_trace__eq__trace.
    rewrite trace_app_commute.
    eapply SimpleSE.dbBlock_intro; eauto using dbTerminator_test.

    assert (c::cs++cs'=(c::cs)++cs') as EQ. auto.
    rewrite EQ. clear EQ.
    eapply SimpleSE.dbBlock_intro; eauto using dbTerminator_test.
Qed.


Lemma dbCmd_dbBlocks__dbCmd_or_dbBlocks : forall S TD Ps lc als gl Mem0 c lc1 als1 gl1 Mem1 tr1 lc2 als2 gl2 Mem2 tr2 
  l1 ps1 cs1 tmn1 l2 ps2 cs2 tmn2 F arg,
  SimpleSE.dbCmd TD lc als gl Mem0 c lc1 als1 gl1 Mem1 tr1 ->
  SimpleSE.dbBlocks S TD Ps F arg 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 cs1 tmn1) lc1 als1) gl1 Mem1)
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l2 ps2 cs2 tmn2) lc2 als2) gl2 Mem2)
    tr2 ->
  (SimpleSE.dbCmd TD lc als gl Mem0 c lc2 als2 gl2 Mem2 tr1 /\ 
   cs1 = cs2 /\ tr2 = trace_nil /\ 
   lc1 = lc2 /\ als1 = als2 /\ gl1 = gl2 /\ Mem1 = Mem2 /\
   l1 = l2 /\ ps1 = ps2 /\ tmn1 = tmn2
  ) \/
  (SimpleSE.dbBlocks S TD Ps F arg 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 (c::cs1) tmn1) lc als) gl Mem0)
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l2 ps2 cs2 tmn2) lc2 als2) gl2 Mem2)
    (trace_app tr1 tr2)).
Proof.
  intros S TD Ps lc als gl Mem0 c lc1 als1 gl1 Mem1 tr1 lc2 als2 gl2 Mem2 tr2 
    l1 ps1 cs1 tmn1 l2 ps2 cs2 tmn2 F arg0 H1 H2.
  inversion H2; subst.
    left. repeat (split; auto).
    right. 
      rewrite trace_app_commute.
      inversion H; subst.
      eapply SimpleSE.dbBlocks_cons; eauto using dbCmd_dbBlock__dbBlock.
Qed.


Lemma dbCall__dbSubblock : forall S TD Ps lc gl Mem c lc' gl' Mem' tr als,
  SimpleSE.dbCall S TD Ps lc gl Mem c lc' gl' Mem' tr ->
  SimpleSE.dbSubblock S TD Ps 
    lc als gl Mem
    (c::nil)
    lc' als gl' Mem'
    tr.
Proof.
  intros S TD Ps lc gl Mem0 c lc' gl' Mem' tr als H.
  rewrite <- nil_app_trace__eq__trace.
  assert (c::nil=nil++c::nil) as EQ. auto.
  rewrite EQ.
  apply SimpleSE.dbSubblock_intro with (lc2:=lc)(gl2:=gl)(Mem2:=Mem0); auto.
Qed.

Lemma dbCall_isCallInst : forall S TD Ps lc gl Mem c lc' gl' Mem' tr,
  SimpleSE.dbCall S TD Ps lc gl Mem c lc' gl' Mem' tr ->
  Instruction.isCallInst c = true.
Proof.
  intros S TD Ps lc gl Mem0 c lc' gl' Mem' tr HdbCall.
  induction HdbCall; auto.
Qed.

Lemma dbInsn_Call__inv : forall S1 TD1 Ps1 F1 l1 ps1 cs1 tmn1 c cs tmn3 lc1 arg1 als1 ECs1 gl1 Mem1
                         S2 TD2 Ps2 F2 l2 ps2 cs2 tmn2 tmn4 lc2 arg2 als2 ECs2 gl2 Mem2 tr,
  
  dbInsn 
    (mkState S1 TD1 Ps1 (mkEC F1 (block_intro l1 ps1 cs1 tmn1) (c::cs) tmn3 lc1 arg1 als1::ECs1) gl1 Mem1) 
    (mkState S2 TD2 Ps2 (mkEC F2 (block_intro l2 ps2 cs2 tmn2) cs tmn4 lc2 arg2 als2::ECs2) gl2 Mem2)
    tr ->
  Instruction.isCallInst c = true ->
  S1 = S2 /\ TD1 = TD2 /\ Ps1 = Ps2 /\ F1 = F2 /\ l1 = l2 /\ ps1 = ps2 /\
  cs1 = cs2 /\ tmn1 = tmn2 /\ tmn3 = tmn4 /\ als1 = als2.
Proof.
  intros.
  inversion H; subst; try solve [inversion H0].
    repeat (split; auto).
Qed.

Lemma dbSubblock_dbBlock__dbBlock : forall S TD Ps lc als gl Mem0 cs lc1 als1 gl1 Mem1 tr1 lc2 als2 gl2 Mem2 tr2 
  l1 ps1 cs1 tmn1 B F arg,
  SimpleSE.dbSubblock S TD Ps lc als gl Mem0 cs lc1 als1 gl1 Mem1 tr1 ->
  SimpleSE.dbBlock S TD Ps F arg 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 cs1 tmn1) lc1 als1) gl1 Mem1)
    (SimpleSE.mkState (SimpleSE.mkEC B lc2 als2) gl2 Mem2)
    tr2 ->
  SimpleSE.dbBlock S TD Ps F arg 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 (cs++cs1) tmn1) lc als) gl Mem0)
    (SimpleSE.mkState (SimpleSE.mkEC B lc2 als2) gl2 Mem2)
    (trace_app tr1 tr2).
Proof.
  intros S TD Ps lc als gl Mem0 cs lc1 als1 gl1 Mem1 tr1 lc2 als2 gl2 Mem2 tr2 
    l1 ps1 cs1 tmn1 B F arg0 H1 H2.
  inversion H2; subst.  
  rewrite trace_app_commute.
  rewrite trace_app_commute.
  rewrite <- app_ass.
  eapply SimpleSE.dbBlock_intro; eauto using dbTerminator_test.
Qed.

Lemma dbSubblock_dbBlocks__dbSubblock_or_dbBlocks : forall S TD Ps lc als gl Mem0 cs lc1 als1 gl1 Mem1 tr1 lc2 als2 gl2 Mem2 tr2 
  l1 ps1 cs1 tmn1 l2 ps2 cs2 tmn2 F arg,
  SimpleSE.dbSubblock S TD Ps lc als gl Mem0 cs lc1 als1 gl1 Mem1 tr1 ->
  SimpleSE.dbBlocks S TD Ps F arg 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 cs1 tmn1) lc1 als1) gl1 Mem1)
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l2 ps2 cs2 tmn2) lc2 als2) gl2 Mem2)
    tr2 ->
  (  SimpleSE.dbSubblock S TD Ps lc als gl Mem0 cs lc1 als1 gl1 Mem1 tr1 /\ 
   cs1 = cs2 /\ tr2 = trace_nil /\ 
   lc1 = lc2 /\ als1 = als2 /\ gl1 = gl2 /\ Mem1 = Mem2 /\
   l1 = l2 /\ ps1 = ps2 /\ tmn1 = tmn2
  ) \/
  (SimpleSE.dbBlocks S TD Ps F arg 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 (cs++cs1) tmn1) lc als) gl Mem0)
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l2 ps2 cs2 tmn2) lc2 als2) gl2 Mem2)
    (trace_app tr1 tr2)).
Proof.
  intros S TD Ps lc als gl Mem0 cs lc1 als1 gl1 Mem1 tr1 lc2 als2 gl2 Mem2 tr2 
    l1 ps1 cs1 tmn1 l2 ps2 cs2 tmn2 F arg0 H1 H2.
  inversion H2; subst.
    left. repeat (split; auto).
    right. 
      rewrite trace_app_commute.
      inversion H; subst.
      eapply SimpleSE.dbBlocks_cons; eauto using dbSubblock_dbBlock__dbBlock.
Qed.


Definition llvmop_dbInsn__seop_prop state1 state2 tr
  (db:LLVMopsem.dbInsn state1 state2 tr) :=
  forall S TD Ps F l ps cs tmn lc arg als ECs gl Mem cs0,
  state1 = (mkState S TD Ps ((mkEC F (block_intro l ps cs0 tmn) cs tmn lc arg als)::ECs) gl Mem) ->
  exists l', exists ps', exists cs', exists tmn', 
  exists lc', exists als', exists gl', exists Mem', exists cs0',
  state2 = (mkState S TD Ps ((mkEC F (block_intro l' ps' cs0' tmn') cs' tmn' lc' arg als')::ECs) gl' Mem') /\
  ((cs = nil /\ Mem = Mem' /\ als = als' /\ gl = gl' /\ cs' = cs0' /\
              SimpleSE.dbTerminator TD F 
                 (block_intro l ps cs tmn) lc gl 
                 tmn 
                 (block_intro l' ps' cs' tmn') lc' 
                 tr ) \/ 
  (exists c, c::cs' = cs /\ SimpleSE.dbCmd TD lc als gl Mem c lc' als' gl' Mem' tr) \/
  (exists c, c::cs' = cs /\ SimpleSE.dbCall S TD Ps lc gl Mem c lc' gl' Mem' tr)).
Definition llvmop_dbop__seop_prop state1 state2 tr
  (db:LLVMopsem.dbop state1 state2 tr) :=
  forall S TD Ps F l ps cs tmn lc arg als ECs gl Mem l' ps' cs' tmn' lc' als' gl' Mem' cs0 cs0',
  state1 = (mkState S TD Ps ((mkEC F (block_intro l ps cs0 tmn) cs tmn lc arg als)::ECs) gl Mem) ->
  state2 = (mkState S TD Ps ((mkEC F (block_intro l' ps' cs0' tmn') cs' tmn' lc' arg als')::ECs) gl' Mem') ->
  (exists cs1, exists cs2, 
  exists tr1, exists tr2,
  exists lc1, exists als1, exists gl1, exists Mem1,
    trace_app tr1 tr2 = tr /\  
    l = l' /\
    ps = ps' /\
    cs0 = cs0' /\
    tmn = tmn' /\
    cs = cs1++cs2++cs' /\
    SimpleSE.dbSubblocks S TD Ps
      lc als gl Mem
      cs1
      lc1 als1 gl1 Mem1
      tr1 /\
    SimpleSE.dbCmds TD
      lc1 als1 gl1 Mem1
      cs2
      lc' als' gl' Mem'
      tr2) \/
  (exists cs1, exists cs2, 
  exists tr1, exists tr2, exists tr3,
  exists lc1, exists als1, exists gl1, exists Mem1,
  exists lc2, exists als2, exists gl2, exists Mem2,
    cs1++cs2++cs'=cs0' /\
    (trace_app (trace_app tr1 tr2) tr3) = tr /\
    SimpleSE.dbBlocks S TD Ps F arg 
      (SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps cs tmn) lc als) gl Mem) 
      (SimpleSE.mkState (SimpleSE.mkEC (block_intro l' ps' cs0' tmn') lc1 als1) gl1 Mem1)
      tr1 /\
    SimpleSE.dbSubblocks S TD Ps
      lc1 als1 gl1 Mem1
      cs1
      lc2 als2 gl2 Mem2
      tr2 /\
    SimpleSE.dbCmds TD
      lc2 als2 gl2 Mem2
      cs2
      lc' als' gl' Mem'
      tr3).
Definition llvmop_dbFdef__seop_dbFdef_prop fid rt lp S TD Ps ECs lc gl Mem lc' gl' als' Mem' B' Rid oResult tr
  (db:LLVMopsem.dbFdef fid rt lp S TD Ps ECs lc gl Mem lc' gl' als' Mem' B' Rid oResult tr) :=
  SimpleSE.dbFdef fid rt lp S TD Ps lc gl Mem lc' gl' als' Mem' B' Rid oResult tr.

Lemma llvmop__seop : 
  (forall state1 state2 tr db, @llvmop_dbInsn__seop_prop state1 state2 tr db) /\
  (forall state1 state2 tr db, @llvmop_dbop__seop_prop state1 state2 tr  db) /\
  (forall fid rt lp S TD Ps lc gl Mem lc' gl' als' Mem' B' Rid oResult tr ECs db, 
    @llvmop_dbFdef__seop_dbFdef_prop fid rt lp S TD Ps lc gl Mem lc' gl' als' Mem' B' Rid oResult tr ECs db).
Proof.
(db_mutind_cases
  apply LLVMopsem.db_mutind with
    (P  := llvmop_dbInsn__seop_prop)
    (P0 := llvmop_dbop__seop_prop)
    (P1 := llvmop_dbFdef__seop_dbFdef_prop) Case);
  unfold llvmop_dbInsn__seop_prop, 
         llvmop_dbop__seop_prop, 
         llvmop_dbFdef__seop_dbFdef_prop; intros; subst.
Case "dbBranch".
  inversion H; subst. clear H.
  exists l'. exists ps'. exists cs'. exists tmn'.
  exists (switchToNewBasicBlock (block_intro l' ps' cs' tmn') (block_intro l0 ps cs0 (insn_br bid Cond l1 l2)) lc0). exists als0. exists gl0. exists Mem1.
  exists cs'. split; auto.
  left. 
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
    apply SimpleSE.dbBranch with (c:=c); auto.
      rewrite e0. admit. (*lookup*)
      simpl. admit. (*switch*)

Case "dbBranch_uncond".
  inversion H; subst. clear H.
  exists l'. exists ps'. exists cs'. exists tmn'.
  exists (switchToNewBasicBlock (block_intro l' ps' cs' tmn') (block_intro l1 ps cs0 (insn_br_uncond bid l0)) lc0). exists als0. exists gl0. exists Mem1.
  exists cs'. split; auto.
  left.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
    apply SimpleSE.dbBranch_uncond; auto.
      rewrite e. admit. (*lookup*)
      simpl. admit. (*switch*)

Case "dbBop".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc'. exists als0. exists gl'. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_bop id0 bop0 sz0 v1 v2).
  split; eauto.

Case "dbExtractValue".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc'. exists als0. exists gl'. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_extractvalue id0 t v idxs).
  split; eauto.

Case "dbInsertValue".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc'. exists als0. exists gl'. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_insertvalue id0 t v t' v' idxs).
  split; eauto.

Case "dbMalloc".
  inversion H; subst. clear H. 
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc'. exists als0. exists gl'. exists Mem'.
  exists cs1. split; auto.
  right. left.
  exists (insn_malloc id0 t sz0 align0).
  split; eauto.

Case "dbFree".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc0. exists als0. exists gl0. exists Mem'.
  exists cs1. split; auto.
  right. left.
  exists (insn_free fid t v).
  split; eauto.

Case "dbAlloca".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc'. exists (mb::als0). exists gl'. exists Mem'.
  exists cs1. split; auto.
  right. left.
  exists (insn_alloca id0 t sz0 align0).
  split; eauto.

Case "dbLoad".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc'. exists als0. exists gl'. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_load id0 t v).
  split; eauto.

Case "dbStore".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc0. exists als0. exists gl0. exists Mem'.
  exists cs1. split; auto.
  right. left.
  exists (insn_store sid t v1 v2).
  split; eauto.

Case "dbGEP".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc'. exists als0. exists gl'. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_gep id0 inbounds0 t v idxs).
  split; eauto.

Case "dbExt".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc'. exists als0. exists gl'. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_ext id0 extop0 t1 v1 t2).
  split; eauto.

Case "dbCast".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc'. exists als0. exists gl'. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_cast id0 castop0 t1 v1 t2).
  split; eauto.

Case "dbIcmp".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc'. exists als0. exists gl'. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_icmp id0 cond0 t v1 v2).
  split; eauto.

Case "dbSelect".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc'. exists als0. exists gl'. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_select id0 v0 t v1 v2).
  split; eauto.

Case "dbCall".
  inversion H0; subst. clear H0.
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc''. exists als0. exists gl''. exists Mem''.
  exists cs1. split; auto.
  right. right.
  exists (insn_call rid noret0 tailc0 rt fid lp).
  split; eauto.

Case "dbop_nil".
  inversion H0; subst. clear H0. 
  left.
  exists nil. exists nil.
  exists trace_nil. exists trace_nil.
  exists lc'. exists als'. exists gl'. exists Mem'.
  repeat (split; auto).
  
Case "dbop_cons".
  destruct (@H S TD Ps F l0 ps cs tmn lc arg0 als ECs gl Mem0 cs0)
    as [l1 [ps1 [cs1 [tmn1 [lc1 [als1 [gl1 [Mem1 [cs2 [J1 J2]]]]]]]]]]; subst; auto.
  clear H.
  assert (mkState S TD Ps (mkEC F (block_intro l1 ps1 cs2 tmn1) cs1 tmn1 lc1 arg0 als1::ECs) gl1 Mem1 =
          mkState S TD Ps (mkEC F (block_intro l1 ps1 cs2 tmn1) cs1 tmn1 lc1 arg0 als1::ECs) gl1 Mem1) as J'. auto.
  apply H0 with (l'0:=l')(ps'0:=ps')(cs'0:=cs')(tmn'0:=tmn')(lc'0:=lc')(als'0:=als')(gl'0:=gl')(Mem'0:=Mem')(cs0'0:=cs0') in J'; auto.
  clear H0.
  destruct J2 as [[EQ [EQ' [EQ1 [EQ2 [EQ3 J2]]]]] | [[c [EQ J2]] | [c [EQ J2]]]]; subst.
  SCase "dbTerminator".
    destruct J' as [
                     [cs3 [cs4 [tr1 [tr2 [lc2 [als2 [gl2 [Mem2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 [EQ6 [J11 J12]]]]]]]]]]]]]]] | 
                     [cs3 [cs4 [tr1 [tr2 [tr3 [lc2 [als2 [gl2 [Mem2 [lc3 [als3 [gl3 [Mem3 [EQ1 [EQ2 [J21 [J22 J23]]]]]]]]]]]]]]]]]
                   ]; subst.
    SSCase "one block".
      subst.
      right.
      exists cs3. exists cs4.
      exists t1. exists tr1. exists tr2.
      exists lc1. exists als1. exists gl1. exists Mem1.
      exists lc2. exists als2. exists gl2. exists Mem2.
      rewrite trace_app_commute.
      repeat (split; auto).
        apply dbBlock__dbBlocks; auto using dbTerminator__dbBlock.
    
    SSCase "multi block".
      right.
      exists cs3. exists cs4.
      exists (trace_app t1 tr1). exists tr2. exists tr3.
      exists lc2. exists als2. exists gl2. exists Mem2.
      exists lc3. exists als3. exists gl3. exists Mem3.
      rewrite trace_app_commute.
      rewrite trace_app_commute.
      repeat (split; auto).
        apply SimpleSE.dbBlocks_cons with (S2:=SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 cs2 tmn1) lc1 als1) gl1 Mem1); 
          auto using dbTerminator__dbBlock.
  SCase "dbCmd".
    apply dbInsn__inv in d.
    destruct d as [_ [_ [_ [_ [EQ5 [EQ6 [EQ7 [EQ8 _]]]]]]]]; subst.
    destruct J' as [
                     [cs3 [cs4 [tr1 [tr2 [lc2 [als2 [gl2 [Mem2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 [EQ6 [J11 J12]]]]]]]]]]]]]]] | 
                     [cs3 [cs4 [tr1 [tr2 [tr3 [lc2 [als2 [gl2 [Mem2 [lc3 [als3 [gl3 [Mem3 [EQ1 [EQ2 [J21 [J22 J23]]]]]]]]]]]]]]]]]
                   ]; subst.
    SSCase "one block".
      left.
      apply dbCmd_dbSubblocks__dbCmd_or_dbSubblocks with (lc:=lc)(als:=als)(gl:=gl)(Mem0:=Mem0)(c:=c)(tr1:=t1) in J11; auto.
      destruct J11 as [[J11 [EQ [EQ' [EQ1 [EQ2 [EQ3 EQ4]]]]]] | J11]; subst.
        exists nil. exists (c::cs4).
        exists trace_nil. exists (trace_app t1 tr2).
        exists lc. exists als. exists gl. exists Mem0.
        rewrite nil_app_trace__eq__trace.
        rewrite nil_app_trace__eq__trace.
        repeat (split; eauto). 

        exists (c::cs3). exists cs4.
        exists (trace_app t1 tr1). exists tr2.
        exists lc2. exists als2. exists gl2. exists Mem2.
        rewrite trace_app_commute. simpl_env in *.
        repeat (split; auto).
    
    SSCase "multi block".
      apply dbCmd_dbBlocks__dbCmd_or_dbBlocks with (lc:=lc)(als:=als)(gl:=gl)(Mem0:=Mem0)(c:=c)(tr1:=t1) in J21; auto.
      destruct J21 as [[J21 [EQ [EQ' [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 [EQ6 EQ7]]]]]]]]] | J21]; subst.
        apply dbCmd_dbSubblocks__dbCmd_or_dbSubblocks with (lc:=lc)(als:=als)(gl:=gl)(Mem0:=Mem0)(c:=c)(tr1:=t1) in J22; auto.
        destruct J22 as [[J22 [EQ [EQ' [EQ1 [EQ2 [EQ3 EQ4]]]]]] | J22]; subst.
          left. 
          exists nil. exists (c::cs4).
          exists trace_nil. exists (trace_app t1 tr3).
          exists lc. exists als. exists gl. exists Mem0.
          rewrite nil_app_trace__eq__trace.
          rewrite nil_app_trace__eq__trace.
          repeat (split; eauto).
            admit. (*block*) 
      
          left.
          exists (c::cs3). exists cs4.
          exists (trace_app t1 tr2). exists tr3.
          exists lc3. exists als3. exists gl3. exists Mem3.
          rewrite nil_app_trace__eq__trace.
          rewrite trace_app_commute.
          repeat (split; eauto).
            admit. (*block*) 
        
        right.
        exists cs3. exists cs4.
        exists (trace_app t1 tr1). exists tr2. exists tr3.
        exists lc2. exists als2. exists gl2. exists Mem2.
        exists lc3. exists als3. exists gl3. exists Mem3.
        rewrite trace_app_commute.
        rewrite trace_app_commute.
        repeat (split; eauto).

  SCase "dbCall".
    assert (J:=J2).
    apply dbCall_isCallInst in J.
    apply dbCall__dbSubblock with (als:=als1) in J2.
    apply dbInsn_Call__inv in d; auto.
    destruct d as [_ [_ [_ [_ [EQ5 [EQ6 [EQ7 [EQ8 [_ EQ9]]]]]]]]]; subst.
    destruct J' as [
                     [cs3 [cs4 [tr1 [tr2 [lc2 [als2 [gl2 [Mem2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 [EQ6 [J11 J12]]]]]]]]]]]]]]] | 
                     [cs3 [cs4 [tr1 [tr2 [tr3 [lc2 [als2 [gl2 [Mem2 [lc3 [als3 [gl3 [Mem3 [EQ1 [EQ2 [J21 [J22 J23]]]]]]]]]]]]]]]]]
                   ]; subst.
    SSCase "one block".
      left.
      exists (c::cs3). exists cs4.
      exists (trace_app t1 tr1). exists tr2.
      exists lc2. exists als2. exists gl2. exists Mem2.
      rewrite trace_app_commute. simpl_env in *.
      repeat (split; eauto).

    SSCase "multi block".
      apply dbSubblock_dbBlocks__dbSubblock_or_dbBlocks with (lc:=lc)(als:=als1)(gl:=gl)(Mem0:=Mem0)(cs:=c::nil)(tr1:=t1) in J21; auto.
      destruct J21 as [[J21 [EQ [EQ' [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 [EQ6 EQ7]]]]]]]]] | J21]; subst.
        left. 
        exists (c::cs3). exists cs4.
        exists (trace_app t1 tr2). exists tr3.
        exists lc3. exists als3. exists gl3. exists Mem3.
        rewrite nil_app_trace__eq__trace.
        rewrite trace_app_commute. simpl_env in *.
        repeat (split; eauto).
          admit. (*block*) 
      
        right.
        exists cs3. exists cs4.
        exists (trace_app t1 tr1). exists tr2. exists tr3.
        exists lc2. exists als2. exists gl2. exists Mem2.
        exists lc3. exists als3. exists gl3. exists Mem3.
        rewrite trace_app_commute.
        rewrite trace_app_commute.
        repeat (split; eauto).     

Case "dbFdef_func".
  assert (mkState S TD Ps (mkEC (fdef_intro (fheader_intro rt fid la) lb) (block_intro l' ps' cs' tmn') cs' tmn' (initLocals la (params2GVs TD lp lc gl)) (params2GVs TD lp lc gl) nil::ECs) gl Mem0 =
          mkState S TD Ps (mkEC (fdef_intro (fheader_intro rt fid la) lb) (block_intro l' ps' cs' tmn') cs' tmn' (initLocals la (params2GVs TD lp lc gl)) (params2GVs TD lp lc gl) nil::ECs) gl Mem0) as J. auto.
  apply H with (l'0:=l'')(ps'0:=ps'')(cs'0:=nil)(tmn'0:=insn_return rid rt Result)(lc'0:=lc')(als'0:=als')(gl'0:=gl')(Mem'0:=Mem')(cs0':=cs'') in J; auto.
  clear H d.
  destruct J as [
                 [cs3 [cs4 [tr1 [tr2 [lc2 [als2 [gl2 [Mem2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 [EQ6 [J11 J12]]]]]]]]]]]]]]] | 
                 [cs3 [cs4 [tr1 [tr2 [tr3 [lc2 [als2 [gl2 [Mem2 [lc3 [als3 [gl3 [Mem3 [EQ1 [EQ2 [J21 [J22 J23]]]]]]]]]]]]]]]]]
                ]; subst.
  SCase "one block".
    simpl_env in EQ6. subst.
    rewrite <- nil_app_trace__eq__trace with (tr:=tr1).
    eapply SimpleSE.dbFdef_func; eauto.
      rewrite <- e. 
      admit. (*lookup*)
  
  SCase "multi block".
    simpl_env in *.
    eapply SimpleSE.dbFdef_func; eauto.
      rewrite <- e. 
      admit. (*lookup*)

Case "dbFdef_proc".
  assert (mkState S TD Ps (mkEC (fdef_intro (fheader_intro rt fid la) lb) (block_intro l' ps' cs' tmn') cs' tmn' (initLocals la (params2GVs TD lp lc gl)) (params2GVs TD lp lc gl) nil::ECs) gl Mem0 =
          mkState S TD Ps (mkEC (fdef_intro (fheader_intro rt fid la) lb) (block_intro l' ps' cs' tmn') cs' tmn' (initLocals la (params2GVs TD lp lc gl)) (params2GVs TD lp lc gl) nil::ECs) gl Mem0) as J. auto.
  apply H with (l'0:=l'')(ps'0:=ps'')(cs'0:=nil)(tmn'0:=insn_return_void rid)(lc'0:=lc')(als'0:=als')(gl'0:=gl')(Mem'0:=Mem')(cs0':=cs'') in J; auto.
  clear H d.
  destruct J as [
                 [cs3 [cs4 [tr1 [tr2 [lc2 [als2 [gl2 [Mem2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 [EQ6 [J11 J12]]]]]]]]]]]]]]] | 
                 [cs3 [cs4 [tr1 [tr2 [tr3 [lc2 [als2 [gl2 [Mem2 [lc3 [als3 [gl3 [Mem3 [EQ1 [EQ2 [J21 [J22 J23]]]]]]]]]]]]]]]]]
                ]; subst.
  SCase "one block".
    simpl_env in EQ6. subst.
    rewrite <- nil_app_trace__eq__trace with (tr:=tr1).
    eapply SimpleSE.dbFdef_proc; eauto.
      rewrite <- e. 
      admit. (*lookup*)
  
  SCase "multi block".
    simpl_env in *.
    eapply SimpleSE.dbFdef_proc; eauto.
      rewrite <- e. 
      admit. (*lookup*)
Qed.


Lemma llvmop_dbInsn__seop : forall state2 tr S TD Ps F l ps cs tmn lc arg als ECs gl Mem cs0,
  LLVMopsem.dbInsn 
    (mkState S TD Ps ((mkEC F (block_intro l ps cs0 tmn) cs tmn lc arg als)::ECs) gl Mem)  
    state2 
    tr ->
  exists l', exists ps', exists cs', exists tmn', 
  exists lc', exists als', exists gl', exists Mem', exists cs0',
  state2 = (mkState S TD Ps ((mkEC F (block_intro l' ps' cs0' tmn') cs' tmn' lc' arg als')::ECs) gl' Mem') /\
  ((cs = nil /\ Mem = Mem' /\ als = als' /\ gl = gl' /\ cs' = cs0' /\
              SimpleSE.dbTerminator TD F 
                 (block_intro l ps cs tmn) lc gl 
                 tmn 
                 (block_intro l' ps' cs' tmn') lc' 
                 tr ) \/ 
  (exists c, c::cs' = cs /\ SimpleSE.dbCmd TD lc als gl Mem c lc' als' gl' Mem' tr) \/
  (exists c, c::cs' = cs /\ SimpleSE.dbCall S TD Ps lc gl Mem c lc' gl' Mem' tr)).
Proof.
  intros.
  destruct llvmop__seop as [J _]. 
  unfold llvmop_dbInsn__seop_prop in J.
  eapply J; eauto.
Qed.

Lemma llvmop_dbop__seop : forall tr S TD Ps F l ps cs tmn lc arg als ECs gl Mem l' ps' cs' tmn' lc' als' gl' Mem' cs0 cs0',
  LLVMopsem.dbop 
    (mkState S TD Ps ((mkEC F (block_intro l ps cs0 tmn) cs tmn lc arg als)::ECs) gl Mem)
    (mkState S TD Ps ((mkEC F (block_intro l' ps' cs0' tmn') cs' tmn' lc' arg als')::ECs) gl' Mem')
    tr ->
  (exists cs1, exists cs2, 
  exists tr1, exists tr2,
  exists lc1, exists als1, exists gl1, exists Mem1,
    trace_app tr1 tr2 = tr /\  
    l = l' /\
    ps = ps' /\
    cs0 = cs0' /\
    tmn = tmn' /\
    cs = cs1++cs2++cs' /\
    SimpleSE.dbSubblocks S TD Ps
      lc als gl Mem
      cs1
      lc1 als1 gl1 Mem1
      tr1 /\
    SimpleSE.dbCmds TD
      lc1 als1 gl1 Mem1
      cs2
      lc' als' gl' Mem'
      tr2) \/
  (exists cs1, exists cs2, 
  exists tr1, exists tr2, exists tr3,
  exists lc1, exists als1, exists gl1, exists Mem1,
  exists lc2, exists als2, exists gl2, exists Mem2,
    cs1++cs2++cs'=cs0' /\
    (trace_app (trace_app tr1 tr2) tr3) = tr /\
    SimpleSE.dbBlocks S TD Ps F arg 
      (SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps cs tmn) lc als) gl Mem) 
      (SimpleSE.mkState (SimpleSE.mkEC (block_intro l' ps' cs0' tmn') lc1 als1) gl1 Mem1)
      tr1 /\
    SimpleSE.dbSubblocks S TD Ps
      lc1 als1 gl1 Mem1
      cs1
      lc2 als2 gl2 Mem2
      tr2 /\
    SimpleSE.dbCmds TD
      lc2 als2 gl2 Mem2
      cs2
      lc' als' gl' Mem'
      tr3).
Proof.
  intros.
  destruct llvmop__seop as [_ [J _]]. 
  unfold llvmop_dbop__seop_prop in J.
  eapply J; eauto.
Qed.

Lemma llvmop_dbFdef__seop_dbFdef : forall fid rt lp S TD Ps ECs lc gl Mem lc' gl' als' Mem' B' Rid oResult tr,
  LLVMopsem.dbFdef fid rt lp S TD Ps ECs lc gl Mem lc' gl' als' Mem' B' Rid oResult tr ->
  SimpleSE.dbFdef fid rt lp S TD Ps lc gl Mem lc' gl' als' Mem' B' Rid oResult tr.
Proof.
  intros.
  destruct llvmop__seop as [_ [_ J]]. 
  unfold llvmop_dbFdef__seop_dbFdef_prop in J.
  eapply J; eauto.
Qed.



