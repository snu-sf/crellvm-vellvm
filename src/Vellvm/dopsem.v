Require Import Metatheory.
Require Import alist.
Require Import monad.
Require Import targetdata.
Require Import genericvalues.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import syntax.
Require Import typings.
Require Import static.
Require Import opsem.
Require Import opsem_props.
Require Import opsem_wf.
Require Import vellvm_tactics.
Require Import infrastructure.
Require Import infrastructure_props.

Import LLVMsyntax.
Import LLVMgv.
Import LLVMtd.
Import LLVMtypings.
Import LLVMinfra.

(* This file defines the deterministic instance of Vellvm's operational 
   semantics. *)

Notation "vidxs @@ vidxss" := (Opsem.in_list_gvs vidxs vidxss)
  (at level 43, right associativity).

(* Properties of deterministic operational semantics. *)
Lemma dos_in_list_gvs_inv : forall gvs gvss, gvs @@ gvss -> gvs = gvss.
Proof.
  induction 1; subst; auto.
Qed.

Ltac dgvs_instantiate_inv :=
  match goal with
  | [ H : _ = _ |- _ ] => subst
  | [ H : _ @@ _ |- _ ] => apply dos_in_list_gvs_inv in H; subst
  end.

(*************************************)
Definition DGVMap := Opsem.GVsMap.

(*************************************)
(* Aux invariants of wf ECs *)

Definition wfEC_inv s m (EC: Opsem.ExecutionContext) : Prop :=
uniqFdef (Opsem.CurFunction EC) /\ 
blockInFdefB (Opsem.CurBB EC) (Opsem.CurFunction EC) = true /\
match Opsem.CurCmds EC with
| nil => wf_insn s m (Opsem.CurFunction EC) (Opsem.CurBB EC) 
           (insn_terminator (Opsem.Terminator EC))
| c::_ => wf_insn s m (Opsem.CurFunction EC) (Opsem.CurBB EC) 
           (insn_cmd c)
end /\
exists l0, exists ps0, exists cs0,
  Opsem.CurBB EC = (l0, stmts_intro ps0 (cs0 ++ Opsem.CurCmds EC)
    (Opsem.Terminator EC)).

Definition wfECs_inv s m (ECs: list Opsem.ExecutionContext) : Prop :=
List.Forall (wfEC_inv s m) ECs.

Lemma wf_EC__wfEC_inv: forall S los nts Ps EC
  (HwfS : wf_system S) 
  (HMinS : moduleInSystemB (module_intro los nts Ps) S = true)
  (Hwfec : OpsemPP.wf_ExecutionContext (los, nts) Ps EC),
  wfEC_inv S (module_intro los nts Ps) EC.
Proof.
  destruct EC; simpl.
  intros.
  destruct Hwfec as [J1 [J2 [J3 [J4 [J5 J6]]]]].
  unfold wfEC_inv. simpl.
  split; eauto 2 using wf_system__uniqFdef.
  split; auto.
  split; auto.
    destruct J6 as [l1 [ps1 [cs1 J6]]]; subst.
    destruct CurCmds.
      eapply wf_system__wf_tmn in J2; eauto.
      eapply wf_system__wf_cmd in J2; eauto using in_middle.
Qed.

Lemma wf_ECStack__wfECs_inv: forall S los nts Ps ECs
  (HwfS : wf_system S) 
  (HMinS : moduleInSystemB (module_intro los nts Ps) S = true)
  (Hwf : OpsemPP.wf_ECStack (los, nts) Ps ECs),
  wfECs_inv S (module_intro los nts Ps) ECs.
Proof.
  unfold wfECs_inv.
  induction ECs as [|]; simpl; intros; auto.
  destruct Hwf as [J1 [J2 J3]].
  constructor; eauto using wf_EC__wfEC_inv.
Qed.

Lemma wf_State__wfECs_inv: forall cfg St (Hwfc: OpsemPP.wf_Config cfg) 
  (Hwfst: OpsemPP.wf_State cfg St), 
  wfECs_inv (OpsemAux.CurSystem cfg) 
    (module_intro (fst (OpsemAux.CurTargetData cfg))
                  (snd (OpsemAux.CurTargetData cfg))
                  (OpsemAux.CurProducts cfg) )
    (Opsem.EC St :: 
    Opsem.ECS St).
Proof.
  intros.
  destruct cfg as [? [? ?] ? ?].
  destruct St.
  destruct Hwfc as [? [? [? ?]]].
  destruct Hwfst. simpl.
  eapply wf_ECStack__wfECs_inv; eauto.
  destruct H4; auto.
  simpl; split; auto.
Qed.

Definition uniqEC (EC: Opsem.ExecutionContext) : Prop :=
uniqFdef (Opsem.CurFunction EC) /\ 
blockInFdefB (Opsem.CurBB EC) (Opsem.CurFunction EC) = true /\
exists l0, exists ps0, exists cs0,
  Opsem.CurBB EC = (l0, stmts_intro ps0 (cs0 ++ Opsem.CurCmds EC)
    (Opsem.Terminator EC)).

Definition uniqECs (ECs: list Opsem.ExecutionContext) : Prop :=
List.Forall uniqEC ECs.

Lemma wfEC_inv__uniqEC: forall s m EC (Hwf: wfEC_inv s m EC), uniqEC EC.
Proof.
  intros.
  destruct Hwf as [J1 [J3 [_ J2]]]. split; auto.
Qed.

Lemma wfECs_inv__uniqECs: forall s m EC ECs (Hwf: wfECs_inv s m (EC::ECs)), uniqECs (EC::ECs).
Proof.
  unfold wfECs_inv, uniqECs.
  intros.
  induction Hwf; auto.
    constructor; auto.
      apply wfEC_inv__uniqEC in H; auto.
Qed.

Lemma wf_State__uniqECs: forall cfg St (Hwfc: OpsemPP.wf_Config cfg) 
  (Hwfst: OpsemPP.wf_State cfg St), uniqECs ((Opsem.EC St) :: (Opsem.ECS St)).
Proof.
  intros.
  destruct cfg as [? [? ?] ? ?].
  destruct St.
  destruct Hwfc as [? [? [? ?]]].
  destruct Hwfst as [? [? ?]]. simpl.
  assert(H6 : OpsemPP.wf_ECStack (l0, n) CurProducts (EC :: ECS)).
  simpl. split; auto.
  eapply wf_ECStack__wfECs_inv in H6; eauto.
  eapply wfECs_inv__uniqECs; eauto.
Qed.

Ltac find_uniqEC :=
repeat match goal with
| H: uniqECs (Opsem.ECS {|Opsem.ECS := _; Opsem.Mem := _ |}) |- uniqEC _ => 
  simpl in H
| H: uniqECs (?EC::_) |- uniqEC ?EC => inv H; auto
| H: uniqECs (_::?EC::_) |- uniqEC ?EC => inv H; auto
| H: Forall uniqEC (?EC::_) |- uniqEC ?EC => inv H; auto
| H: Forall uniqEC (_::?EC::_) |- uniqEC ?EC => inv H; auto
end.

(*************************************)
(* More dynamic properties *)

Lemma GEP_inv: forall TD t (mp1 : GenericValue) inbounds0 vidxs mp2 t'
  (H1 : Opsem.GEP TD t mp1 vidxs inbounds0 t' = ret mp2),
  gundef TD (typ_pointer t') = ret mp2 \/
  exists blk, exists ofs1, exists ofs2 : int32, exists m1, exists m2,
    mp1 = (Vptr blk ofs1, m1) :: nil /\ mp2 = (Vptr blk ofs2, m2) :: nil.
Proof.
  intros.
  unfold Opsem.GEP in H1.
  unfold gep in H1. unfold GEP in H1.
  remember (GV2ptr TD (getPointerSize TD) mp1) as R1.
  destruct R1; auto.
  destruct (GVs2Nats TD vidxs); auto.
  remember (mgep TD t v l0) as R2.
  destruct R2; auto.
  inv H1.
  unfold mgep in HeqR2.
  destruct v; tinv HeqR2.
  destruct l0; tinv HeqR2.
  destruct (mgetoffset TD (typ_array 0%nat t) (z :: l0)) as [[]|];
    inv HeqR2.
  unfold GV2ptr in HeqR1.
  destruct mp1 as [|[]]; tinv HeqR1.
  destruct v; tinv HeqR1.
  destruct mp1; inv HeqR1.
  unfold ptr2GV. unfold val2GV. right. exists b0. exists i1.
  exists (Int.add 31 i1 (Int.repr 31 z0)). exists m.
  exists (AST.Mint (Size.mul Size.Eight (getPointerSize TD) - 1)).
  eauto.
Qed.

Lemma wf__getTypeStoreSize_eq_sizeGenericValue: forall (gl2 : GVMap)
  (lc2 : Opsem.GVsMap) (S : system) (los : layouts) (nts : namedts)
  (Ps : list product) (v1 : value) (gv1 : GenericValue)
  (Hwfg : LLVMgv.wf_global (los, nts) S gl2) (n : nat) t
  (HeqR : ret n = getTypeStoreSize (los, nts) t) F
  (H24 : Opsem.getOperandValue (los, nts) v1 lc2 gl2 = ret gv1)
  (Hwflc1 : OpsemPP.wf_lc (los, nts) F lc2)
  (Hwfv : wf_value S (module_intro los nts Ps) F v1 t),
  n = sizeGenericValue gv1.
Proof.
  intros.
  eapply OpsemPP.getOperandValue__wf_gvs in Hwflc1; eauto.
  inv Hwflc1.
  unfold gv_chunks_match_typ in H1.
  clear - H1 HeqR Hwfv. inv_mbind.
  apply wf_value__wf_typ in Hwfv. destruct Hwfv as [J1 J2].
  symmetry in HeqR0.
  eapply flatten_typ__getTypeSizeInBits in HeqR0; eauto.
  destruct HeqR0 as [sz [al [A B]]].          
  unfold getTypeAllocSize, getTypeStoreSize, getABITypeAlignment,
         getTypeSizeInBits, getAlignment, 
         getTypeSizeInBits_and_Alignment in HeqR.
  rewrite A in HeqR.
  inv HeqR. rewrite B.
  eapply vm_matches_typ__sizeMC_eq_sizeGenericValue; eauto.
Qed.
