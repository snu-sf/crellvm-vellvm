(* Adapted from Compcert 1.9 *)

Require Import Coqlib.
Require Intv.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
(* Vellvm does not have a global env component. We will provide a mapping
   from atom to blk.of explicitly. We use atom instead of ident. *)
(*Require Import Globalenvs.*)
Require Import Metatheory. 
Require Import alist. 
Require Import genericvalues. 
Require Import targetdata. 
Require Import syntax. 
Require Import memory_sim.
Require Import genericvalues_inject.
Require Import vellvm_tactics.
Export LLVMgv.

Set Implicit Arguments.

Module Genv.

Section GENV.

Variable GV: Type.

Record t : Type := mkgenv {
  genv_vars: list (atom * GV);
  genv_find_symbol: atom -> option block;
  genv_find_var_info: block -> option GV;
  genv_vars_inj: forall id1 id2 b,
    genv_find_symbol id1 = Some b ->
    genv_find_symbol id2 = Some b ->
    id1 = id2
}.

Definition find_symbol (ge:t) (id:atom) : option block :=
ge.(genv_find_symbol) id.

Definition find_var_info (ge:t) (b:block) : option GV :=
ge.(genv_find_var_info) b.

End GENV.

End Genv.

Unset Implicit Arguments.

Inductive eventval: Type :=
  | EVint: forall (wz:nat), Int.int wz -> eventval
  | EVfloat: float -> eventval
  | EVsingle: float32 -> eventval
  | EVptr_global: atom -> int32 -> eventval.

Definition eventgv := list eventval.

Inductive event: Type :=
  | Event_syscall: atom -> list eventgv -> option eventgv -> event
  .

Definition trace := list event.

Definition E0 : trace := nil.

Definition Eapp (t1 t2: trace) : trace := t1 ++ t2.

CoInductive traceinf : Type :=
  | Econsinf: event -> traceinf -> traceinf.

Fixpoint Eappinf (t: trace) (T: traceinf) {struct t} : traceinf :=
  match t with
  | nil => T
  | ev :: t' => Econsinf ev (Eappinf t' T)
  end.

Lemma E0_left: forall t, Eapp E0 t = t. Proof. auto. Qed.

Lemma E0_right: forall t, Eapp t E0 = t.
 Proof. intros. unfold E0, Eapp. rewrite <- app_nil_end. auto. Qed.

Lemma Eapp_assoc: forall t1 t2 t3, Eapp (Eapp t1 t2) t3 = Eapp t1 (Eapp t2 t3).
Proof. intros. unfold Eapp, trace. apply app_ass. Qed.

Lemma Eappinf_assoc: forall t1 t2 T, Eappinf (Eapp t1 t2) T = Eappinf t1 (Eappinf t2 T).
Proof. induction t1; intros; simpl. auto. decEq; auto. Qed.

Lemma E0_left_inf: forall T, Eappinf E0 T = T.
Proof. auto. Qed.

Infix "**" := Eapp (at level 60, right associativity).
Infix "***" := Eappinf (at level 60, right associativity).
Set Implicit Arguments.

Section EVENTVAL.

Variable GV: Type.
Variable ge: Genv.t GV.

Inductive eventval_match: eventval -> typ -> val -> Prop :=
  | ev_match_int: forall wz i,
      eventval_match (EVint wz i) Tint (Vint wz i)
  | ev_match_float: forall f,
      eventval_match (EVfloat f) Tfloat (Vfloat f)
  | ev_match_single: forall f,
      eventval_match (EVsingle f) Tsingle (Vsingle f)
  | ev_match_ptr: forall id b ofs,
      Genv.find_symbol ge id = Some b ->
      eventval_match (EVptr_global id ofs) Tint (Vptr b ofs).

(** Compatibility with memory injections *)

Variable f: block -> option (block * Z).

Definition meminj_preserves_globals : Prop :=
     (forall id b, Genv.find_symbol ge id = Some b -> f b = Some(b, 0))
  /\ (forall b gv, Genv.find_var_info ge b = Some gv -> f b = Some(b, 0))
  /\ (forall b1 b2 delta gv, 
        Genv.find_var_info ge b2 = Some gv -> 
        f b1 = Some(b2, delta) -> b2 = b1).

Hypothesis glob_pres: meminj_preserves_globals.

(** Validity *)

End EVENTVAL.

Definition eventgv_match (TD:LLVMtd.TargetData) (ge: Genv.t GenericValue) 
  (egv: eventgv) (t:LLVMsyntax.typ) (gv:GenericValue) : Prop :=
match flatten_typ TD t with
| Some ms =>
    Forall3 (fun ev m g =>
             let '(v, m0) := g in
             eventval_match ge ev (AST.type_of_chunk m) v /\
             m = m0) egv ms gv
| None => False
end.

Definition eventgv_list_match (TD:LLVMtd.TargetData) (ge: Genv.t GenericValue) 
  (egvs: list eventgv) (ts:list LLVMsyntax.typ) (gvs: list GenericValue) : Prop :=
Forall3 (eventgv_match TD ge) egvs ts gvs.

