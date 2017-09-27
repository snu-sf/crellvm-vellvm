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

(* Properties of deterministic operational semantics. *)

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

Definition uniqEC (EC: Opsem.ExecutionContext) : Prop :=
uniqFdef (Opsem.CurFunction EC) /\ 
blockInFdefB (Opsem.CurBB EC) (Opsem.CurFunction EC) = true /\
exists l0, exists ps0, exists cs0,
  Opsem.CurBB EC = (l0, stmts_intro ps0 (cs0 ++ Opsem.CurCmds EC)
    (Opsem.Terminator EC)).

Definition uniqECs (ECs: list Opsem.ExecutionContext) : Prop :=
List.Forall uniqEC ECs.

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

