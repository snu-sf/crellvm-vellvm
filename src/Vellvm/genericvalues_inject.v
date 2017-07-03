Require Import syntax.
Require Import infrastructure.
Require Import Memory.
Require Import targetdata.
Require Import genericvalues.
Require Import alist.
Require Import Integers.
Require Import Values.
Require Import Coqlib.
Require Import monad.
Require Import Metatheory.
Require Import Znumtheory.
Require Import typings.
Require Import infrastructure_props.
Require Import targetdata_props.
Require Import typings_props.
Require Import genericvalues_props.
Require Import memory_sim.
Require Import sflib.

Import LLVMinfra.
Import LLVMgv.
Import LLVMtd.
Import LLVMtypings.


(* TODO: location *)
Lemma has_chunk__has_chunkb
      v chk
      (CHUNK: Val.has_chunk v chk)
  :
    <<CHUNK: Val.has_chunkb v chk = true>>
.
Proof.
  unfold Val.has_chunk in *.
  destruct v, chk; simpl; intros; try solve [auto | congruence];
    des; clarify.
  apply andb_true_iff.
  split.
  + apply andb_true_iff.
    destruct (eq_nat_dec n n); ss. split; ss.
    destruct (zle 0 (Int.unsigned n i0)); ss.
  + destruct (zlt (Int.unsigned n i0) (Int.modulus n)); ss.
Qed.


(* The file proves the injection between generic values in terms of memory
   injection. *)
Inductive gv_inject (mi: meminj) : GenericValue -> GenericValue -> Prop :=
| gv_inject_nil : gv_inject mi nil nil
| gv_inject_cons : forall
    v1 m v2 gv1 gv2
    (CHUNK: v1 = Vundef -> v2 <> Vundef -> Val.has_chunkb v2 m),
    MoreMem.val_inject mi v1 v2 -> gv_inject mi gv1 gv2 ->
    gv_inject mi ((v1,m)::gv1) ((v2,m)::gv2)
.

Hint Constructors gv_inject.
Hint Unfold MoreMem.meminj_no_overlap MoreMem.meminj_zero_delta.

Definition gv_list_inject (mi: meminj) (gvss1 gvss2: list GenericValue): Prop :=
List.Forall2 (gv_inject mi) gvss1 gvss2.

Fixpoint gvs_inject mi gvs1 gvs2 : Prop :=
match (gvs1, gvs2) with
| (nil, nil) => True
| (gv1::gvs1', gv2::gvs2') => gv_inject mi gv1 gv2 /\ gvs_inject mi gvs1' gvs2'
| _ => False
end.

(* The well-formedness of memory injection. *)
Record wf_sb_mi maxb mi Mem1 Mem2 := mk_wf_sb_mi {
  Hno_overlap : MoreMem.meminj_no_overlap mi;
  Hmap1 : forall b, (b >= Mem.nextblock Mem1)%positive -> mi b = None;
  Hmap2 : forall b1 b2 delta2, 
    mi b1 = Some (b2, delta2) -> (b2 < Mem.nextblock Mem2)%positive;
  mi_freeblocks: forall b, ~(Mem.valid_block Mem1 b) -> mi b = None;
  mi_mappedblocks: forall b b' delta, 
    mi b = Some(b', delta) -> Mem.valid_block Mem2 b';
  mi_range_block: MoreMem.meminj_zero_delta mi;
  mi_bounds: forall b b' delta, 
    mi b = Some(b', delta) -> Mem.bounds Mem1 b = Mem.bounds Mem2 b';
  mi_globals : forall b, (b <= maxb)%positive -> mi b = Some (b, 0)
  }.

(* Well-formed globals *)
Fixpoint wf_global (maxb:Values.block) (gv:GenericValue) 
  : Prop :=
match gv with
| nil => True
| (Vptr b _,_)::gv' => (b <= maxb)%positive /\ wf_global maxb gv'
| _::gv' => wf_global maxb gv'
end.

Fixpoint wf_globals maxb (gl:GVMap) : Prop :=
match gl with
| nil => True
| (_,gv)::gl' => wf_global maxb gv /\ wf_globals maxb gl'
end.

(* Properties of gv_inject *)
Lemma gv_inject_incr:
  forall f1 f2 v v',
  inject_incr f1 f2 ->
  gv_inject f1 v v' ->
  gv_inject f2 v v'.
Proof.
  intros.
  induction H0; eauto using val_list_inject_incr.
Qed.

Lemma gv_inject_app : forall mi gv1 gv1' gv2 gv2',
  gv_inject mi gv1 gv2 ->
  gv_inject mi gv1' gv2' ->
  gv_inject mi (gv1++gv1') (gv2++gv2').
Proof.
  intros.
  induction H; simpl; eauto.
Qed.

Ltac tinv H := try solve [inv H].
  
Lemma gv_inject__repeatGV : forall mi gv1 gv2 n,
  gv_inject mi gv1 gv2 -> 
  gv_inject mi (repeatGV gv1 n) (repeatGV gv2 n).
Proof.
  induction n; intros; simpl; eauto using gv_inject_app.
Qed.

Lemma gv_inject_uninits : forall mi n, gv_inject mi (uninits n) (uninits n).
Proof.
  unfold uninits.
  induction n; intros; simpl; eauto using gv_inject_app.
Qed.

Lemma gv_inject__val_inject : forall mi gv1 gv2 TD,
  gv_inject mi gv1 gv2 ->
  exists v1, exists v2,
    GV2val TD gv1 = Some v1 /\ GV2val TD gv2 = Some v2 /\ 
    MoreMem.val_inject mi v1 v2.
Proof.
  intros.
  unfold GV2val in *.
  destruct gv1; inv H; subst. eauto.
    destruct gv1; inv H4; subst; eauto.
Qed.

Lemma gv_inject_mc2undefs: forall mi mcs,
  gv_inject mi (mc2undefs mcs) (mc2undefs mcs).
Proof.
  unfold mc2undefs.
  induction mcs; simpl; auto.
Qed.

Lemma gv_inject_mc2undefs': forall mi mcs gvs',
  gv_chunks_match_typb_aux gvs' mcs = true ->
  gv_inject mi (mc2undefs mcs) gvs'.
Proof.
  unfold mc2undefs.
  induction mcs; ii; ss.
  - destruct gvs'; ss. des_ifs.
  - destruct gvs'; ss. des_ifs.
    apply andb_true_iff in H. des.
    apply andb_true_iff in H. des.
    apply memory_chunk_eq_prop in H. subst.
    econs; eauto.
Qed.

Lemma gv_inject_gundef : forall mi TD t gv, gundef TD t = Some gv -> gv_inject mi gv gv.
Proof.
  intros. unfold gundef in H. 
  inv_mbind. apply gv_inject_mc2undefs.
Qed.

Lemma gv_inject_gundef'
      mi TD t gv gv'
      (MATCH: gv_chunks_match_typb TD gv' t = true)
      (UNDEF: gundef TD t = Some gv)
  :
    gv_inject mi gv gv'
.
Proof.
  intros. unfold gundef in UNDEF. 
  inv_mbind. (* apply gv_inject_mc2undefs. *)
  unfold gv_chunks_match_typb in *. des_ifs.
  eapply gv_inject_mc2undefs'; eauto.
Qed.

Lemma gv_inject_gundef_val2GV
      TD gv0 mi ty
      (UNDEF: gundef TD ty = ret gv0)
      v mc
      (TY: flatten_typ TD ty = ret [mc])
      (CHUNK: Val.has_chunkb v mc)
  :
    gv_inject mi gv0 (val2GV TD v mc)
.
Proof.
  unfold gundef in *. des_ifs.
  unfold flatten_typ in *. des_ifs.
  unfold val2GV.
  econs; eauto.
Qed.

(* Lemma has_chunkb_int_zero_ext *)
(*       sz0 *)
(*       wz i0 *)
(*   : *)
(*     <<CHUNK: Val.has_chunkb *)
(*                (Vint (sz0 - 1) *)
(*                      (Int.zero_ext (sz0 - 1) (Z.of_nat wz) (Int.repr (sz0 - 1) (Int.unsigned wz i0)))) *)
(*                (AST.Mint (sz0 - 1))>> *)
(* . *)
(* Proof. *)
(*   eapply has_chunk__has_chunkb; eauto. *)
(*   exploit Val.zero_ext'_has_chunk; eauto. *)
(*   instantiate (1:= (sz0 - 1)%nat). unfold Val.zero_ext'. *)
(*   instantiate (1:= Vint wz i0). ss. *)
(* Qed. *)

(* Lemma has_chunkb_int_sign_ext *)
(*       sz0 (* tt *) *)
(*       wz i0 *)
(*   : *)
(*     <<CHUNK: Val.has_chunkb *)
(*                (Vint (sz0 - 1) *)
(*                      (Int.sign_ext (sz0 - 1) (Z.of_nat wz) (Int.repr (sz0 - 1) (Int.unsigned wz i0))) *)
(*                (* tt *) *)
(*                ) *)
(*                (AST.Mint (sz0 - 1))>> *)
(* . *)
(* Proof. *)
(*   red. ss. *)
(*   exploit Int.Z_mod_modulus_range; eauto. *)
(*   instantiate (1:= (sz0 - 1)%nat). *)
(*   instantiate (1:= (Int.Zsign_ext (Z.of_nat wz) (Int.Z_mod_modulus (sz0 - 1) (Int.unsigned wz i0)))). *)
(*   i. des. *)
(*   destruct (Nat.eq_dec _ _); ss; try omega. *)
(*   apply andb_true_iff. split. *)
(*   - destruct (zle _ _); ss; try omega. *)
(*   - destruct (zlt _ _); ss; try omega. *)
(* Qed. *)

Lemma has_chunkb_trunc_int
      sz0 wz i0
  :
    <<CHUNK: Val.has_chunkb (Val.trunc (Vint wz i0) (sz0 - 1)) (AST.Mint (sz0 - 1))>>
.
Proof.
  red. ss.
  exploit Int.Z_mod_modulus_range; eauto.
  instantiate (1:= (sz0 - 1)%nat).
  instantiate (1:= (Int.unsigned wz i0)).
  i. des.
  des_ifs. ss.
  destruct (Nat.eq_dec _ _); ss; try omega.
  apply andb_true_iff. split.
  - destruct (zle _ _); ss; try omega.
  - destruct (zlt _ _); ss; try omega.
Qed.

Lemma gv_inject_gundef_trunc_int
      TD sz0 gv0 wz i0 mi
      (UNDEF: gundef TD (typ_int sz0) = ret gv0)
  :
    gv_inject mi gv0 (val2GV TD (Val.trunc (Vint wz i0) (sz0 - 1)) (AST.Mint (sz0 - 1)))
.
Proof.
  dup UNDEF.
  unfold gundef in UNDEF. des_ifs.
  eapply gv_inject_gundef_val2GV; eauto.
  { compute. des_ifs. }
  { apply has_chunkb_trunc_int. }
Qed.

Lemma gv_inject_gundef_trunc_float
      TD gv0 mi
      fp f
      (UNDEF: gundef TD (typ_floatpoint fp) = ret gv0)
      (ORDER: floating_point_order fp fp_double = true)
  :
    gv_inject mi gv0 (val2GV TD (Vsingle (Floats.Float.to_single f)) AST.Mfloat32)
.
Proof.
  eapply gv_inject_gundef_val2GV; eauto. compute. des_ifs.
Qed.

Ltac chunk_simpl := i; clarify.
Ltac chunk_auto := econs; eauto; chunk_simpl.
Ltac chunk_auto_try := try (by chunk_auto).

Lemma gv_inject_nptr_val_refl : forall TD v mi m,
  (forall b ofs, v <> Vptr b ofs) ->
  gv_inject mi (val2GV TD v m) (val2GV TD v m).
Proof.
  intros. unfold val2GV.
  destruct v; chunk_auto.
  - assert (J:=@H b i0). contradict J; auto.
Qed.

Lemma gv_inject__same_size : forall mi gv1 gv2,
  gv_inject mi gv1 gv2 ->
  sizeGenericValue gv1 = sizeGenericValue gv2.
Proof.
  intros mi gv1 gv2 Hinj.
  induction Hinj; simpl; auto.
Qed.

Lemma gv_inject_length_eq : forall mi gv1 gv2,
  gv_inject mi gv1 gv2 -> length gv1 = length gv2.
Proof.
  induction 1; intros; simpl; auto.
Qed.

Require Import Classical.

(* TODO: move to memory_sim.v *)
Lemma val_inject__has_chunkb: forall mi v1 v2 m
  (H : MoreMem.val_inject mi v1 v2)
  (CHUNK: v1 = Vundef -> v2 <> Vundef -> Val.has_chunkb v2 m)
  ,
  Val.has_chunkb v1 m = Val.has_chunkb v2 m.
Proof.
  intros. inv H; auto.
  destruct (classic (v2 = Vundef)).
  - subst. ss.
  - exploit CHUNK; eauto.
Qed.

Lemma gv_inject__has_chunkb: forall mi gv1 gv2
  (H: gv_inject mi gv1 gv2),
  List.Forall2 (fun vm1 vm2 =>
                  Val.has_chunkb vm1.(fst) vm1.(snd) =
                  Val.has_chunkb vm2.(fst) vm2.(snd)) gv1 gv2
.
Proof.
  ii. ginduction H; ii; ss.
  econs; eauto.
  s.
  eapply val_inject__has_chunkb; eauto.
Qed.

Lemma simulation__gv_chunks_match_typb : forall mi TD gv gv' t,
  gv_inject mi gv gv' ->
  gv_chunks_match_typb TD gv t = gv_chunks_match_typb TD gv' t.
Proof.
  unfold gv_chunks_match_typb.
  intros.
  destruct (flatten_typ TD t); auto.
  generalize dependent l0.
  induction H; simpl; auto.
    destruct l0; auto.
    rewrite IHgv_inject; try eassumption. f_equal. f_equal.
    eapply val_inject__has_chunkb; eauto.
Qed.

(* Globals inject to themselves. *)
Lemma global_gv_inject_refl_aux : forall maxb mi Mem1 Mem2 gv,
  wf_sb_mi maxb mi Mem1 Mem2 ->
  wf_global maxb gv ->
  gv_inject mi gv gv.
Proof.
  induction gv; intros; simpl; auto.
    destruct a.
    destruct v; simpl in *; try solve 
        [assert (J:=@IHgv H H0); eauto]; chunk_auto_try.

        destruct H0 as [H1 H2].
        assert (J:=(@IHgv H H2)).
        inversion H.
        apply mi_globals0 in H1.
        apply gv_inject_cons; auto.
          { chunk_simpl. }
          apply MoreMem.val_inject_ptr with (delta:=0); auto.
            rewrite Int.add_zero; auto.
Qed.

Lemma wf_globals__wf_global : forall mgb gl gv i0,
  wf_globals mgb gl ->
  ret gv = lookupAL GenericValue gl i0 ->
  wf_global mgb gv.
Proof.
  induction gl; intros.
    inversion H0.

    destruct a. simpl in *.
    destruct H as [J1 J2].
    destruct (i0 == i1); subst; eauto.
      inv H0; auto.
Qed.      

Lemma global_gv_inject_refl : forall maxb mi Mem1 Mem2 gl i0 gv,
  wf_sb_mi maxb mi Mem1 Mem2 ->
  wf_globals maxb gl ->
  lookupAL _ gl i0 = Some gv ->
  gv_inject mi gv gv.
Proof.
  intros. 
  eapply global_gv_inject_refl_aux; eauto.
    eapply wf_globals__wf_global; eauto.
Qed.



(* TODO: location *)
Ltac des_ifs_safe_aux TAC :=
  TAC;
  repeat
    multimatch goal with
    | |- context[match ?x with _ => _ end] =>
      match (type of x) with
      | { _ } + { _ } => destruct x; TAC; []
      | _ => let Heq := fresh "Heq" in destruct x as [] eqn: Heq; TAC; []
      end
    | H: context[ match ?x with _ => _ end ] |- _ =>
      match (type of x) with
      | { _ } + { _ } => destruct x; TAC; []
      | _ => let Heq := fresh "Heq" in destruct x as [] eqn: Heq; TAC; []
      end
    end.
Tactic Notation "des_ifs_safe" := des_ifs_safe_aux clarify.
Tactic Notation "des_ifs_safe" tactic(TAC) := des_ifs_safe_aux TAC.



(* Generic-value operations preserve gv_inject. *)
Lemma simulation__mtrunc_aux : forall mi TD top t1 gv1 t2 gv1' gv2,
  gv_inject mi gv1 gv1' ->
  mtrunc TD top t1 t2 gv1 = Some gv2 ->
  (mtrunc TD top t1 t2 gv1 = mtrunc TD top t1 t2 gv1' /\
    gv_inject mi gv2 gv2) \/
  exists gv2',
    mtrunc TD top t1 t2 gv1' = Some gv2' /\
    gv_inject mi gv2 gv2'.  
Proof.
  intros.
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v2 [J1 [J2 J3]]]].
  unfold mtrunc in *.
  rewrite J1. rewrite J2. rewrite J1 in H0.
  inv J3; auto.
    destruct_typ t1; destruct_typ t2; inv H0; try solve [
      eauto using gv_inject_gundef |
      unfold val2GV; simpl; destruct (le_lt_dec wz (s1-1)); auto
    ].

    { unfold GV2val in *.
      des_ifs.
      - right. esplits; eauto.
        unfold val2GV. ss. econs; eauto. i.
        des_ifs. ss.
        omega.
      - left. split; ss. unfold val2GV.
        econs; eauto. chunk_simpl.
    }

    destruct_typ t1; destruct_typ t2; inv H0; eauto using gv_inject_gundef.
      match goal with
      | H: context [floating_point_order ?f1 ?f0] |- _ =>
        destruct (floating_point_order f1 f0); inv H;
           simpl; eauto using gv_inject_gundef;
        destruct f0; inv H0; unfold val2GV; simpl; eauto using gv_inject_gundef
      end.
    destruct_typ t1; destruct_typ t2; inv H0; eauto using gv_inject_gundef.
 
    inv H0. eauto using gv_inject_gundef.
    inv H0. eauto using gv_inject_gundef.

    { unfold GV2val in *. des_ifs_safe.
      des_ifs; try (by (right; esplits; eauto using gv_inject_gundef)).
      - right.
        esplits; eauto.
        eapply gv_inject_gundef_trunc_int; eauto.
      - right.
        esplits; eauto.
        eapply gv_inject_gundef_trunc_int; eauto.
      - right.
        esplits; eauto.
        eapply gv_inject_gundef_trunc_int; eauto.
      - right.
        esplits; eauto.
        eapply gv_inject_gundef_trunc_float; eauto.
      - right.
        esplits; eauto.
        eapply gv_inject_gundef_trunc_float; eauto.
      - right.
        esplits; eauto.
        eapply gv_inject_gundef_trunc_float; eauto.
    }
Qed.

Lemma simulation__mtrunc : forall mi TD top t1 gv1 t2 gv1' gv2,
  gv_inject mi gv1 gv1' ->
  mtrunc TD top t1 t2 gv1 = Some gv2 ->
  exists gv2',
    mtrunc TD top t1 t2 gv1' = Some gv2' /\
    gv_inject mi gv2 gv2'.
Proof.
  intros.
  assert (J:=H0).
  eapply simulation__mtrunc_aux in H0; eauto.
  destruct H0 as [[H1 H2] | H0]; eauto.
    rewrite <- H1.
    exists gv2. split; auto.
Qed.

Lemma simulation__mext_aux : forall mi TD eop t1 gv1 t2 gv1' gv2,
  gv_inject mi gv1 gv1' ->
  mext TD eop t1 t2 gv1 = Some gv2 ->
  (mext TD eop t1 t2 gv1 = mext TD eop t1 t2 gv1' /\
    gv_inject mi gv2 gv2) \/
  exists gv2',
    mext TD eop t1 t2 gv1' = Some gv2' /\
    gv_inject mi gv2 gv2'.  
Proof.
  intros. assert (J0:=H).
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v2 [J1 [J2 J3]]]].
  unfold mext in *.
  rewrite J1. rewrite J2. rewrite J1 in H0.
  inv J3; try solve [
    auto |
    destruct t1; destruct t2; inv H0; simpl; eauto using gv_inject_gundef;
      match goal with
      | H: context [floating_point_order ?f ?f0] |- _ =>
        destruct (floating_point_order f f0); inv H; eauto using gv_inject_gundef
      end
    ].

  {
    destruct t1; destruct t2; inv H0; simpl; eauto using gv_inject_gundef.
      destruct eop; inv H1;
        try solve [unfold val2GV; simpl; eauto using gv_inject_gundef].
      { left. split; ss. econs; eauto. chunk_simpl. }
      { left. split; ss. econs; eauto. chunk_simpl. }
      match goal with
      | H: context [floating_point_order ?f1 ?f0] |- _ =>
         destruct (floating_point_order f1 f0); inv H; eauto using gv_inject_gundef
      end.
  }

    destruct t1; destruct t2; inv H0; simpl; eauto using gv_inject_gundef.
      match goal with
      | H: context [floating_point_order ?f0 ?f1] |- _ =>
        destruct (floating_point_order f0 f1); inv H1; simpl;
          eauto using gv_inject_gundef;
        destruct eop; inv H0; simpl; eauto using gv_inject_gundef;
        destruct f1; inv H1; simpl; unfold val2GV; auto
      end; eauto using gv_inject_gundef.

  { Local Opaque Val.zero_ext' Val.sign_ext'.
    des_ifs; ss; try (by (right; esplits; eauto using gv_inject_gundef)).
    - right. esplits; eauto. eapply gv_inject_gundef_val2GV; eauto.
      { compute. des_ifs. }
      eapply has_chunk__has_chunkb; eauto.
      eapply Val.zero_ext'_has_chunk.
    - right. esplits; eauto. eapply gv_inject_gundef_val2GV; eauto.
      { compute. des_ifs. }
      eapply has_chunk__has_chunkb; eauto.
      eapply Val.sign_ext'_has_chunk.
    - right. esplits; eauto. compute in Heq. des_ifs.
      eapply gv_inject_gundef_val2GV; eauto.
      compute; des_ifs.
  }
Qed.

Lemma simulation__mext : forall mi TD eop t1 gv1 t2 gv1' gv2,
  gv_inject mi gv1 gv1' ->
  mext TD eop t1 t2 gv1 = Some gv2 ->
  exists gv2',
    mext TD eop t1 t2 gv1' = Some gv2' /\
    gv_inject mi gv2 gv2'.
Proof.
  intros.
  assert (J:=H0).
  eapply simulation__mext_aux in H0; eauto.
  destruct H0 as [[H1 H2] | H0]; eauto.
    rewrite <- H1.
    exists gv2. split; auto.
Qed.

Lemma simulation__mbop_aux : forall mi TD op bsz gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  mbop TD op bsz gv1 gv2 = Some gv3 ->
  (mbop TD op bsz gv1 gv2 = mbop TD op bsz gv1' gv2' /\
    gv_inject mi gv3 gv3) \/
  exists gv3',
    mbop TD op bsz gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.  
Proof.
  intros. assert (J0:=H0). assert (J:=H).
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v1' [J1 [J2 J3]]]].
  apply gv_inject__val_inject with (TD:=TD) in H0.
  destruct H0 as [v2 [v2' [J1' [J2' J3']]]].
  unfold mbop in *.
  rewrite J1. rewrite J2. rewrite J1'. rewrite J2'.
  rewrite J1 in H1. rewrite J1' in H1.
  inv J3; try solve [inv H1; eauto using gv_inject_gundef].
    inv J3'; try solve [auto | inv H1; eauto using gv_inject_gundef].
    destruct (eq_nat_dec (wz + 1) (Size.to_nat bsz));
       try solve [inv H1; eauto using gv_inject_gundef].
    destruct op;
    try match goal with
      | H0 : match ?s with
        | ret _ => _
        | merror => _
        end = _ |- _ => destruct s eqn:Heqn
    end;
    inv H1;
       try (left; split; auto; apply gv_inject_nptr_val_refl); eauto using gv_inject_gundef.
       apply add_isnt_ptr.
       apply sub_isnt_ptr.
       apply mul_isnt_ptr.
       intros; eapply divu_isnt_ptr; eauto.
       intros; eapply divs_isnt_ptr; eauto.
       intros; eapply modu_isnt_ptr; eauto.
       intros; eapply mods_isnt_ptr; eauto.
       apply shl_isnt_ptr.
       intros; eapply shrx_isnt_ptr; eauto.
       apply shr_isnt_ptr.
       apply and_isnt_ptr.
       apply or_isnt_ptr.
       apply xor_isnt_ptr.
  {
    des_ifs; try (by right; esplits; eauto using gv_inject_gundef);
      right; esplits; eauto; (eapply gv_inject_gundef_val2GV; eauto; [ by compute; des_ifs | ]);
        rewrite <- e; rewrite Nat.add_sub; eapply has_chunk__has_chunkb.
    - eapply Val.add_has_chunk1.
    - eapply Val.sub_has_chunk1.
    - eapply Val.mul_has_chunk1.
    - unfold Val.divu in *. des_ifs. econs; eauto using Int.unsigned_range; eauto.
    - unfold Val.divs in *. des_ifs. econs; eauto using Int.unsigned_range; eauto.
    - unfold Val.modu in *. des_ifs. econs; eauto using Int.unsigned_range; eauto.
    - unfold Val.mods in *. des_ifs. econs; eauto using Int.unsigned_range; eauto.
    - unfold Val.shl in *. des_ifs. econs; eauto using Int.unsigned_range; eauto.
    - unfold Val.shrx in *. des_ifs. econs; eauto using Int.unsigned_range; eauto.
    - unfold Val.shr in *. des_ifs. econs; eauto using Int.unsigned_range; eauto.
    - unfold Val.and in *. des_ifs. econs; eauto using Int.unsigned_range; eauto.
    - unfold Val.or in *. des_ifs. econs; eauto using Int.unsigned_range; eauto.
    - unfold Val.xor in *. des_ifs. econs; eauto using Int.unsigned_range; eauto.
  }
  {
    des_ifs; try (by right; esplits; eauto using gv_inject_gundef);
      right; esplits; eauto; (eapply gv_inject_gundef_val2GV; eauto; [ by compute; des_ifs | ]);
        rewrite <- e; rewrite Nat.add_sub; eapply has_chunk__has_chunkb.
    - eapply Val.add_has_chunk1.
    - eapply Val.sub_has_chunk1.
    - eapply Val.mul_has_chunk1.
    - unfold Val.divu in *. des_ifs. econs; eauto using Int.unsigned_range; eauto.
    - unfold Val.divs in *. des_ifs. econs; eauto using Int.unsigned_range; eauto.
    - unfold Val.modu in *. des_ifs. econs; eauto using Int.unsigned_range; eauto.
    - unfold Val.mods in *. des_ifs. econs; eauto using Int.unsigned_range; eauto.
    - unfold Val.shl in *. des_ifs. econs; eauto using Int.unsigned_range; eauto.
    - unfold Val.shrx in *. des_ifs. econs; eauto using Int.unsigned_range; eauto.
    - unfold Val.shr in *. des_ifs. econs; eauto using Int.unsigned_range; eauto.
    - unfold Val.and in *. des_ifs. econs; eauto using Int.unsigned_range; eauto.
    - unfold Val.or in *. des_ifs. econs; eauto using Int.unsigned_range; eauto.
    - unfold Val.xor in *. des_ifs. econs; eauto using Int.unsigned_range; eauto.
  }
Qed.

Lemma simulation__mbop : forall mi TD op bsz gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  mbop TD op bsz gv1 gv2 = Some gv3 ->
  exists gv3',
    mbop TD op bsz gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.
Proof.
  intros.
  assert (J:=H1).
  eapply simulation__mbop_aux in H1; eauto.
  destruct H1 as [[H1 H2] | H1]; eauto.
    rewrite <- H1.
    exists gv3. split; auto.
Qed.

Ltac solve_flatten_typ :=
  match goal with
  | [ |- flatten_typ ?a ?b = ?c ] => compute; des_ifs
  end.

Lemma simulation__mfbop_aux : forall mi TD op fp gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  mfbop TD op fp gv1 gv2 = Some gv3 ->
  (mfbop TD op fp gv1 gv2 = mfbop TD op fp gv1' gv2' /\
    gv_inject mi gv3 gv3) \/
  exists gv3',
    mfbop TD op fp gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.  
Proof.
  intros. assert (J0:=H0). assert (J:=H).
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v1' [J1 [J2 J3]]]].
  apply gv_inject__val_inject with (TD:=TD) in H0.
  destruct H0 as [v2 [v2' [J1' [J2' J3']]]].
  unfold mfbop in *.
  rewrite J1. rewrite J2. rewrite J1'. rewrite J2'.
  rewrite J1 in H1. rewrite J1' in H1.
  inv J3; try solve [inv H1; eauto using gv_inject_gundef].
  {
    - des_ifs; inv J3'; try (by left; split; ss; eauto using gv_inject_gundef);
        try (by right; esplits; eauto; eapply gv_inject_gundef_val2GV; eauto; solve_flatten_typ).
      + left. split; ss. unfold val2GV. econs; eauto.
      + left. split; ss. unfold val2GV. econs; eauto.
      + left. split; ss. unfold val2GV. econs; eauto.
      + left. split; ss. unfold val2GV. econs; eauto.
      + left. split; ss. unfold val2GV. econs; eauto.
  }
  {
    (* Float(64) *)
    inv J3'; try solve [auto | inv H1; eauto using gv_inject_gundef].
    destruct fp; inv H1; try solve [eauto using gv_inject_gundef].
       destruct op;
          try (left; split; auto; apply gv_inject_nptr_val_refl;
            try solve [auto | intro; simpl; congruence]).
    { des_ifs; try (by left; split; ss; eauto using gv_inject_gundef);
        try (by right; esplits; eauto; eapply gv_inject_gundef_val2GV; eauto; solve_flatten_typ).
    }
  }
  {
    (* Float(32) *)
    inv J3'; try rewrite H1; try (by des_ifs; right; esplits; eauto using gv_inject_gundef).
    - des_ifs; try (by left; split; ss; eauto using gv_inject_gundef);
        right; esplits; eauto; eapply gv_inject_gundef_val2GV; eauto; compute; des_ifs.
    - des_ifs; try (by left; split; ss; eauto using gv_inject_gundef);
        right; esplits; eauto; eapply gv_inject_gundef_val2GV; eauto; compute; des_ifs.
    - des_ifs; try (by left; split; ss; eauto using gv_inject_gundef);
        right; esplits; eauto; eapply gv_inject_gundef_val2GV; eauto; compute; des_ifs.
    (* inv J3'; try solve [auto | inv H1; eauto using gv_inject_gundef]. *)
    (* destruct fp; inv H1; try solve [eauto using gv_inject_gundef]. *)
    (* { right. rewrite H0. des_ifs; esplits; eauto using gv_inject_gundef. } *)
    (*   destruct op; *)
    (*     try (left; split; auto; apply gv_inject_nptr_val_refl; *)
    (*       try solve [auto | intro; congruence]). *)
  }
Qed.

Lemma simulation__mfbop : forall mi TD op fp gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  mfbop TD op fp gv1 gv2 = Some gv3 ->
  exists gv3',
    mfbop TD op fp gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.
Proof.
  intros.
  assert (J:=H1).
  eapply simulation__mfbop_aux in H1; eauto.
  destruct H1 as [[H1 H2] | H1]; eauto.
    rewrite <- H1.
    exists gv3. split; auto.
Qed.

Lemma simulation__mcast_aux_helper : forall TD gv1' wz i0 mi gv2
  (J2 : GV2val TD gv1' = ret Vint wz i0)
  (J : gv_inject mi gv2 gv1')
  (J1 : GV2val TD gv2 = ret Vint wz i0),
   ret gv2 = ret gv1' /\ gv_inject mi gv2 gv2 \/
   (exists gv2' : GenericValue, ret gv1' = ret gv2' /\ gv_inject mi gv2 gv2').
Proof. intros.
        unfold GV2val in *.
        destruct gv1'; tinv J2.
        destruct p; tinv J2.
        destruct gv1'; tinv J2.
        destruct gv2; tinv J1.
        destruct p; tinv J1.
        destruct gv2; inv J1.
        right. exists ((v, m) :: nil). 
        simpl. auto.
Qed.

Lemma simulation__mcast_aux : forall mi TD op t1 t2 gv1 gv1' gv2,
  gv_inject mi gv1 gv1' ->
  mcast TD op t1 t2 gv1 = Some gv2 ->
  (mcast TD op t1 t2 gv1 = mcast TD op t1 t2 gv1' /\
    gv_inject mi gv2 gv2) \/
  exists gv2',
    mcast TD op t1 t2 gv1' = Some gv2' /\
    gv_inject mi gv2 gv2'.  
Proof.
  intros.  assert (J:=H).
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v1' [J1 [J2 J3]]]].
  unfold mcast, mbitcast in *.
  inv J3; try solve [
    destruct op; try solve [
      abstract (destruct t1; try solve [
        inv H0 |
        destruct t2; inv H0; eauto using gv_inject_gundef |
        destruct t2; inv H0; eauto using simulation__mcast_aux_helper
      ])
    ]
  ].
Qed.

Lemma simulation__mcast : forall mi TD op t1 gv1 gv1' t2 gv2,
  gv_inject mi gv1 gv1' ->
  mcast TD op t1 t2 gv1 = Some gv2 ->
  exists gv2',
    mcast TD op t1 t2 gv1' = Some gv2' /\
    gv_inject mi gv2 gv2'.
Proof.
  intros.
  assert (J:=H0).
  eapply simulation__mcast_aux in H0; eauto.
  destruct H0 as [[H1 H2] | H1]; eauto.
    rewrite <- H1.
    exists gv2. split; auto.
Qed.

Lemma inject_val_cmp
      cmp mi v1 v2 mc
  :
    gv_inject mi [(Val.cmp cmp v1 v2, mc)] [(Val.cmp cmp v1 v2, mc)]
.
Proof.
  unfold Val.cmp. unfold Val.cmp_bool. unfold Val.of_optbool.
  destruct cmp; ss; des_ifs; econs; eauto; chunk_simpl.
  all: econs; eauto.
Qed.

Lemma inject_val_cmpu_int
      cmp mi v1 v2
  :
    gv_inject mi [(Val.cmpu_int cmp v1 v2, AST.Mint 0)] [(Val.cmpu_int cmp v1 v2, AST.Mint 0)]
.
Proof.
  exploit Val.cmpu_int_is_bool; eauto.
  instantiate (1:= v2).
  instantiate (1:= v1).
  instantiate (1:= cmp).
  intro BOOL. unfold Val.is_bool in *. des.
  - repeat rewrite BOOL. econs; eauto.
  - repeat rewrite BOOL. econs; eauto. econs; eauto.
  - repeat rewrite BOOL. econs; eauto. econs; eauto.
Qed.

Lemma simulation__micmp_aux : forall mi TD c t gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  micmp TD c t gv1 gv2 = Some gv3 ->
  (micmp TD c t gv1 gv2 = micmp TD c t gv1' gv2' /\
    gv_inject mi gv3 gv3) \/
  exists gv3',
    micmp TD c t gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.  
Proof.
  intros. assert (J0:=H0). assert (J:=H).
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v1' [J1 [J2 J3]]]].
  apply gv_inject__val_inject with (TD:=TD) in H0.
  destruct H0 as [v2 [v2' [J1' [J2' J3']]]].
  unfold micmp, micmp_int in *.
  rewrite J1. rewrite J2. rewrite J1'. rewrite J2'.
  rewrite J1 in H1. rewrite J1' in H1.
  {
    inv J3; inv J3';
      des_ifs; try (by left; split; ss; eauto using gv_inject_gundef; unfold val2GV in *;
                    try apply inject_val_cmp; try apply inject_val_cmpu_int);
        try (by right; esplits; eauto; eapply gv_inject_gundef_val2GV; eauto; try solve_flatten_typ;
             try eapply has_chunk__has_chunkb;
             try eapply Val.cmp_has_Mint0; try eapply Val.cmpu_int_has_Mint0).
  }
  (* inv J3; try solve [inv H1; eauto 3 using gv_inject_gundef]. *)
  (*   inv J3'; try solve [auto | inv H1; eauto using gv_inject_gundef]; *)
  (*   destruct t; try solve [inv H1; eauto using gv_inject_gundef]. *)
  (*     destruct c; inv H1; *)
  (*       try (left; split; auto; *)
  (*         apply gv_inject_nptr_val_refl; try solve *)
  (*           [auto | apply cmp_isnt_ptr | apply cmpu_isnt_ptr *)
  (*           | apply cmpu_int_isnt_ptr]). *)
  (*   destruct t; try solve [inv H1; eauto using gv_inject_gundef]. *)
  (*   destruct t; try solve [inv H1; eauto using gv_inject_gundef]. *)
  (*   destruct t; try solve [inv H1; eauto using gv_inject_gundef]. *)
  (*   destruct t; try solve [inv H1; eauto using gv_inject_gundef]. *)
  (*   destruct t; try solve [inv H1; eauto using gv_inject_gundef]. *)
Qed.

Lemma simulation__micmp : forall mi TD c t gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  micmp TD c t gv1 gv2 = Some gv3 ->
  exists gv3',
    micmp TD c t gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.
Proof.
  intros.
  assert (J:=H1).
  eapply simulation__micmp_aux in H1; eauto.
  destruct H1 as [[H1 H2] | H1]; eauto.
    rewrite <- H1.
    exists gv3. split; auto.
Qed.

Lemma inject_val_cmpf
      cmp mi v1 v2 mc
  :
    gv_inject mi [(Val.cmpf cmp v1 v2, mc)] [(Val.cmpf cmp v1 v2, mc)]
.
Proof.
  unfold Val.cmpf. unfold Val.cmpf_bool. unfold Val.of_optbool.
  destruct cmp; ss; des_ifs; econs; eauto; chunk_simpl.
  all: econs; eauto.
Qed.

Lemma simulation__mfcmp_aux : forall mi TD c t gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  mfcmp TD c t gv1 gv2 = Some gv3 ->
  (mfcmp TD c t gv1 gv2 = mfcmp TD c t gv1' gv2' /\
    gv_inject mi gv3 gv3) \/
  exists gv3',
    mfcmp TD c t gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.  
Proof.
  intros. assert (J0:=H0). assert (J:=H).
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v1' [J1 [J2 J3]]]].
  apply gv_inject__val_inject with (TD:=TD) in H0.
  destruct H0 as [v2 [v2' [J1' [J2' J3']]]].
  unfold mfcmp in *.
  rewrite J1. rewrite J2. rewrite J1'. rewrite J2'.
  rewrite J1 in H1. rewrite J1' in H1.
  {
    inv J3; inv J3';
      des_ifs;
      try (by left; split; ss; eauto using gv_inject_gundef; try unfold val2GV;
           try apply inject_val_cmpf; repeat (econs; eauto));
      try (by right; esplits; eauto; eapply gv_inject_gundef_val2GV; eauto; try solve_flatten_typ;
           try eapply has_chunk__has_chunkb; try eapply Val.cmpf_has_Mint0
          ).
  }
  (* inv J3; try solve [inv H1; eauto using gv_inject_gundef]. *)
  (*   inv J3'; try solve [auto | inv H1; eauto using gv_inject_gundef]; *)
  (*   destruct t; try solve [inv H1; eauto using gv_inject_gundef]. *)
  (*     destruct c; inv H1; *)
  (*       try solve [ *)
  (*         eauto using gv_inject_gundef | *)
  (*         (left; split; auto; *)
  (*         apply gv_inject_nptr_val_refl; try solve *)
  (*           [auto | apply val_of_bool_isnt_ptr | apply Vfalse_isnt_ptr | *)
  (*            apply Vtrue_isnt_ptr]) *)
  (*       ]. *)
  (*     destruct c; inv H1; *)
  (*       try solve [ *)
  (*         eauto using gv_inject_gundef | *)
  (*         (left; split; auto; *)
  (*         apply gv_inject_nptr_val_refl; try solve *)
  (*           [auto | apply val_of_bool_isnt_ptr | apply Vfalse_isnt_ptr | *)
  (*            apply Vtrue_isnt_ptr]) *)
  (*       ]. *)
Qed.

Lemma simulation__mfcmp : forall mi TD c t gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  mfcmp TD c t gv1 gv2 = Some gv3 ->
  exists gv3',
    mfcmp TD c t gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.
Proof.
  intros.
  assert (J:=H1).
  eapply simulation__mfcmp_aux in H1; eauto.
  destruct H1 as [[H1 H2] | H1]; eauto.
    rewrite <- H1.
    exists gv3. split; auto.
Qed.

Lemma simulation__GV2ptr : forall mi TD gv1 gv1' v,
  gv_inject mi gv1 gv1' ->
  GV2ptr TD (getPointerSize TD) gv1 = Some v ->
  exists v',
    GV2ptr TD (getPointerSize TD) gv1' = Some v' /\
    MoreMem.val_inject mi v v'.
Proof.
  intros.
  unfold GV2ptr in *.
  destruct gv1; tinv H0.
  destruct p; tinv H0.
  destruct v0; tinv H0.
  destruct gv1; inv H0.
  inv H. inv H5. inv H4. eauto.
Qed.

Lemma simulation__mgep : forall mi TD v v' v0 t0 l1,
  MoreMem.val_inject mi v v' ->
  mgep TD t0 v l1 = Some v0 ->
  exists v0',
    mgep TD t0 v' l1 = Some v0' /\
    MoreMem.val_inject mi v0 v0'.
Proof.
  intros.
  unfold mgep in *.
  destruct v; tinv H0.
  destruct l1; tinv H0.
  inv H.
  destruct (mgetoffset TD (typ_array 0%nat t0) (z :: l1)) as [[i1 ?]|] ; tinv H0.
  inv H0. 
  exists (Vptr b2 (Int.add 31 (Int.add 31 i0 (Int.repr 31 delta)) (Int.repr 31 i1))).
  split; auto.
    eapply MoreMem.val_inject_ptr; eauto.
      rewrite Int.add_assoc.
      assert (Int.add 31 (Int.repr 31 delta) (Int.repr 31 i1) = 
              Int.add 31 (Int.repr 31 i1) (Int.repr 31 delta)) as EQ.
        rewrite Int.add_commut. auto.
      rewrite EQ.
      rewrite Int.add_assoc. auto.
Qed.

Lemma simulation__splitGenericValue_some : forall mi gv gv' z gvl gvr,
  gv_inject mi gv gv' ->
  splitGenericValue gv z = Some (gvl, gvr) ->
  exists gvl', exists gvr', 
    splitGenericValue gv' z = Some (gvl', gvr') /\
    gv_inject mi gvl gvl' /\ gv_inject mi gvr gvr'.
Proof.
  induction gv; simpl; intros gv' z gvl gvr H H0.
    inv H.
    simpl.
    destruct (zeq z 0); inv H0. 
      exists nil. exists nil. auto.
      destruct (zlt z 0); inv H1.

    inv H.
    simpl.
    destruct (zeq z 0); inv H0. 
      exists nil. exists ((v2, m)::gv2). 
      split; auto.
    destruct (zlt z 0); inv H1.
    remember (splitGenericValue gv (z - size_chunk m)) as R.
    destruct R as [[gvl' gvr']|]; inv H0.
    symmetry in HeqR.
    eapply IHgv in HeqR; eauto.
    destruct HeqR as [gvl'0 [gvr' [J4 [J5 J6]]]].
    rewrite J4.     
    exists ((v2, m) :: gvl'0). exists gvr'. 
    split; auto.
Qed.
   
Lemma simulation__splitGenericValue_none : forall mi gv gv' z,
  gv_inject mi gv gv' ->
  splitGenericValue gv z = None ->
  splitGenericValue gv' z = None.
Proof.
  induction gv; simpl; intros gv' z H H0.
    inv H.
    simpl.
    destruct (zeq z 0); inv H0. 
    destruct (zlt z 0); inv H1; auto.

    inv H. 
    simpl.
    destruct (zeq z 0); inv H0. 
    destruct (zlt z 0); inv H1; auto.
    remember (splitGenericValue gv (z - size_chunk m)) as R.
    destruct R as [[gvl' gvr']|]; inv H0.
    symmetry in HeqR.
    eapply IHgv in HeqR; eauto.
    rewrite HeqR; auto.
Qed.

Lemma simulation__extractGenericValue : forall mi gv1 gv1' TD t1 l0 gv,
  gv_inject mi gv1 gv1' ->
  extractGenericValue TD t1 gv1 l0 = Some gv ->
  exists gv',
    extractGenericValue TD t1 gv1' l0 = Some gv' /\
    gv_inject mi gv gv'.
Proof.
  intros mi gv1 gv1' TD t1 l0 gv H H0.
  unfold extractGenericValue in *.
  destruct (intConsts2Nats TD l0); inv H0; 
    try solve [exists (uninits 1); auto using gv_inject_uninits].
  destruct (mgetoffset TD t1 l1) as [[o t']|]; inv H2;
    try solve [exists (uninits 1); auto using gv_inject_uninits].
  unfold mget in *. 
  destruct (getTypeStoreSize TD t'); inv H1; eauto using gv_inject_gundef.
  remember (splitGenericValue gv1 o) as R.
  destruct R as [[gvl gvr]|].
    symmetry in HeqR.
    eapply simulation__splitGenericValue_some in HeqR; eauto.      
    destruct HeqR as [gvl' [gvr' [J1 [J2 J3]]]].
    simpl. rewrite J1.
    remember (splitGenericValue gvr (Z_of_nat n)) as R1.
    destruct R1 as [[gvrl gvrr]|]; inv H2.
    {
      symmetry in HeqR1.
      eapply simulation__splitGenericValue_some in HeqR1; eauto.      
      destruct HeqR1 as [gvrl' [gvrr' [J1' [J2' J3']]]].
      simpl. rewrite J1'.
        erewrite <- simulation__gv_chunks_match_typb; eauto.
        destruct_if; eauto using gv_inject_gundef.
    }

      symmetry in HeqR1.
      eapply simulation__splitGenericValue_none in HeqR1; eauto.      
      rewrite HeqR1. rewrite H1. eauto using gv_inject_gundef.

    simpl.
    symmetry in HeqR.
    eapply simulation__splitGenericValue_none in HeqR; eauto.      
    rewrite HeqR. rewrite H2. eauto using gv_inject_gundef.
Qed.

(* TODO: move location *)
Lemma load_implies_has_chunkb
      mc Mem0 b0 ofs v0
      (LOAD: Mem.load mc Mem0 b0 ofs = ret v0)
  :
  <<CHUNK: Val.has_chunkb v0 mc>>
.
Proof.
  Transparent Mem.load.
  unfold Mem.load in *. des_ifs. red.
  eapply has_chunk__has_chunkb.
  eapply decode_val_chunk; eauto. 
Qed.

Lemma simulation__insertGenericValue: forall mi gv1 gv1' TD t1 l0 gv t2 gv2 gv2',
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  insertGenericValue TD t1 gv1 l0 t2 gv2 = Some gv ->
  exists gv',
    insertGenericValue TD t1 gv1' l0 t2 gv2' = Some gv' /\
    gv_inject mi gv gv'.
Proof.
  intros mi gv1 gv1' TD t1 l0 gv t2 gv2 gv2' H H0 H1.
  unfold insertGenericValue in *.
  destruct (intConsts2Nats TD l0); inv H1; eauto using gv_inject_gundef.
  destruct (mgetoffset TD t1 l1) as [[o ?]|]; inv H3; eauto using gv_inject_gundef.
  unfold mset in *. 
  destruct (getTypeStoreSize TD t2); inv H2; eauto using gv_inject_gundef.
  assert (J:=@gv_inject_length_eq mi gv2 gv2' H0). 
  rewrite <- J. simpl.
  destruct (n =n= length gv2); subst; inv H3; eauto using gv_inject_gundef.
  remember (splitGenericValue gv1 o) as R.
  destruct R as [[gvl gvr]|].
    symmetry in HeqR.
    eapply simulation__splitGenericValue_some in HeqR; eauto.      
    destruct HeqR as [gvl' [gvr' [J1 [J2 J3]]]].
    simpl. rewrite J1.
    remember (splitGenericValue gvr (Z_of_nat n)) as R1.
    destruct R1 as [[gvrl gvrr]|]; inv H2.
      symmetry in HeqR1.
      eapply simulation__splitGenericValue_some in HeqR1; eauto.      
      destruct HeqR1 as [gvrl' [gvrr' [J1' [J2' J3']]]].
      simpl. rewrite J1'. 
      erewrite <- simulation__gv_chunks_match_typb; eauto.
      destruct_if; eauto using gv_inject_gundef.
      exists (gvl' ++ gv2' ++ gvrr').
      split; auto.
        apply gv_inject_app; auto.
        apply gv_inject_app; auto.

      symmetry in HeqR1.
      eapply simulation__splitGenericValue_none in HeqR1; eauto.      
      rewrite HeqR1. eauto using gv_inject_gundef.
    symmetry in HeqR.
    eapply simulation__splitGenericValue_none in HeqR; eauto.      
    rewrite HeqR. rewrite H2. eauto using gv_inject_gundef.
Qed.

Lemma simulation__mtrunc_refl : forall mi TD top t1 gv1 t2 gv2,
  gv_inject mi gv1 gv1 ->
  mtrunc TD top t1 t2 gv1 = Some gv2 ->
  gv_inject mi gv2 gv2.
Proof.
  ii.
  unfold mtrunc in *.
  des_ifs; try (by eauto using gv_inject_gundef).
  - econs; eauto.
  - econs; eauto. chunk_simpl.
  - econs; eauto.
Qed.

Lemma simulation__mext_refl : forall mi TD eop t1 gv1 t2 gv2,
  gv_inject mi gv1 gv1 ->
  mext TD eop t1 t2 gv1 = Some gv2 ->
  gv_inject mi gv2 gv2.
Proof.
  ii.
  unfold mext in *.
  des_ifs; try (by eauto using gv_inject_gundef).
  - econs; eauto. chunk_simpl.
    Local Transparent Val.zero_ext'.
    unfold Val.zero_ext'. ss.
  - econs; eauto.
    + chunk_simpl.
    + Local Transparent Val.sign_ext'.
      unfold Val.zero_ext'. ss.
  - econs; eauto.
Qed.

Lemma simulation__mbop_refl : forall mi TD op bsz gv1 gv2 gv3,
  gv_inject mi gv1 gv1 ->
  gv_inject mi gv2 gv2 ->
  mbop TD op bsz gv1 gv2 = Some gv3 ->
  gv_inject mi gv3 gv3.
Proof.
  intros. assert (J0:=H0). assert (J:=H).
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v1' [J1 [J2 J3]]]].
  apply gv_inject__val_inject with (TD:=TD) in H0.
  destruct H0 as [v2 [v2' [J1' [J2' J3']]]].
  rewrite J1 in J2. inv J2.
  rewrite J1' in J2'. inv J2'.
  unfold mbop in *.
  rewrite J1 in H1. rewrite J1' in H1.
  destruct v1';
    try solve [inv H1; eauto using gv_inject_gundef].
  destruct v2';
    try solve [inv H1; eauto using gv_inject_gundef].
  destruct (eq_nat_dec (wz + 1) (Size.to_nat bsz));
     try solve [inv H1; eauto using gv_inject_gundef].
  destruct op;
  try match goal with
      | H0 : match ?s with
        | ret _ => _
        | merror => _
        end = _ |- _ => destruct s eqn:Heqn
  end;
  inv H1; try (apply gv_inject_nptr_val_refl; auto); eauto using gv_inject_gundef.
       apply add_isnt_ptr.
       apply sub_isnt_ptr.
       apply mul_isnt_ptr.
       intros; eapply divu_isnt_ptr; eauto.
       intros; eapply divs_isnt_ptr; eauto.
       intros; eapply modu_isnt_ptr; eauto.
       intros; eapply mods_isnt_ptr; eauto.
       apply shl_isnt_ptr.
       intros; eapply shrx_isnt_ptr; eauto.
       apply shr_isnt_ptr.
       apply and_isnt_ptr.
       apply or_isnt_ptr.
       apply xor_isnt_ptr.
Qed.

Lemma simulation__mfbop_refl : forall mi TD op fp gv1 gv2 gv3,
  gv_inject mi gv1 gv1 ->
  gv_inject mi gv2 gv2 ->
  mfbop TD op fp gv1 gv2 = Some gv3 ->
  gv_inject mi gv3 gv3.
Proof.
  intros. assert (J0:=H0). assert (J:=H).
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v1' [J1 [J2 J3]]]].
  apply gv_inject__val_inject with (TD:=TD) in H0.
  destruct H0 as [v2 [v2' [J1' [J2' J3']]]].
  rewrite J1 in J2. inv J2.
  rewrite J1' in J2'. inv J2'.
  unfold mfbop in *.
  rewrite J1 in H1. rewrite J1' in H1. 
  destruct v1';
    try solve [inv H1; eauto using gv_inject_gundef];
  destruct v2';
    try solve [inv H1; eauto using gv_inject_gundef];
  destruct fp; try solve [inv H1; eauto using gv_inject_gundef];
  destruct op; inv H1; 
    try (apply gv_inject_nptr_val_refl; try solve [auto | intro; congruence]).
Qed.

Lemma simulation__mcast_refl : forall mi TD op t1 t2 gv1 gv2,
  gv_inject mi gv1 gv1 ->
  mcast TD op t1 t2 gv1 = Some gv2 ->
  gv_inject mi gv2 gv2.
Proof.
  intros.  assert (J:=H).
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v1' [J1 [J2 J3]]]].
  rewrite J1 in J2. inv J2.
  unfold mcast, mbitcast in *.
  destruct op; 
    try solve [
      inv H0; eauto using gv_inject_gundef |
      destruct t1; destruct t2; inv H0; eauto using gv_inject_gundef
    ].
Qed.

Lemma simulation__micmp_refl : forall mi TD c t gv1 gv2 gv3,
  gv_inject mi gv1 gv1 ->
  gv_inject mi gv2 gv2 ->
  micmp TD c t gv1 gv2 = Some gv3 ->
  gv_inject mi gv3 gv3.
Proof.
  intros. assert (J0:=H0). assert (J:=H).
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v1' [J1 [J2 J3]]]].
  apply gv_inject__val_inject with (TD:=TD) in H0.
  destruct H0 as [v2 [v2' [J1' [J2' J3']]]].
  rewrite J1 in J2. inv J2.
  rewrite J1' in J2'. inv J2'.
  unfold micmp, micmp_int in *.
  rewrite J1 in H1. rewrite J1' in H1. 
  destruct t; try solve [inv H1; eauto using gv_inject_gundef].
  destruct v1'; try solve [inv H1; eauto using gv_inject_gundef].
  destruct v2'; try solve [inv H1; eauto using gv_inject_gundef].
  destruct c; inv H1; 
        try (apply gv_inject_nptr_val_refl; try solve 
            [auto | apply cmp_isnt_ptr | apply cmpu_isnt_ptr
            | apply cmpu_int_isnt_ptr]).
Qed.

Lemma simulation__mfcmp_refl : forall mi TD c t gv1 gv2 gv3,
  gv_inject mi gv1 gv1 ->
  gv_inject mi gv2 gv2 ->
  mfcmp TD c t gv1 gv2 = Some gv3 ->
  gv_inject mi gv3 gv3.
Proof.
  ii.
  unfold mfcmp in *.
  des_ifs; try (by (eauto using gv_inject_gundef));
    try (by eapply inject_val_cmpf; eauto);
    try (by econs; eauto; [econs; eauto]).
Qed.

Lemma simulation__mgep_refl : forall mi TD v v0 t0 l1,
  MoreMem.val_inject mi v v ->
  mgep TD t0 v l1 = Some v0 ->
  MoreMem.val_inject mi v0 v0.
Proof.
  intros.
  unfold mgep in *.
  destruct v; tinv H0.
  destruct l1; tinv H0.
  destruct (mgetoffset TD (typ_array 0%nat t0) (z :: l1)) as [[o ?]|]; tinv H0.
  inv H0.
  inversion H. subst i0 b ofs1 b1.
  eapply MoreMem.val_inject_ptr; eauto.
    assert (Int.add 31 ofs2 (Int.repr 31 delta) = 
            Int.add 31 (Int.repr 31 delta) ofs2) as EQ.
      rewrite <- Int.add_commut. auto. 
    symmetry.
    rewrite Int.add_commut. 
    rewrite <- Int.add_assoc.
    rewrite <- EQ.   
    rewrite <- H5.
    auto.
Qed.

Lemma GV2ptr_refl : forall mi TD gv v,
  gv_inject mi gv gv ->
  GV2ptr TD (getPointerSize TD) gv = Some v ->
  MoreMem.val_inject mi v v.
Proof.
  intros.
  unfold GV2ptr in H0.
  destruct gv; tinv H0.
  destruct p; tinv H0.
  destruct v0; tinv H0.
  destruct gv; tinv H0.
  inv H0. inv H; auto.
Qed.

Lemma simulation__splitGenericValue_refl : forall mi gv z gvl gvr,
  gv_inject mi gv gv ->
  splitGenericValue gv z = Some (gvl, gvr) ->
  gv_inject mi gvl gvl /\
  gv_inject mi gvr gvr.
Proof.
  induction gv; simpl; intros; inv H; simpl.
    destruct (zeq z 0); inv H0. 
      auto.
      destruct (zlt z 0); inv H1.

    destruct (zeq z 0); inv H0. 
      split; auto.

      destruct (zlt z 0); inv H1.
      remember (splitGenericValue gv (z - size_chunk m)) as R.
      destruct R as [[gvl' gvr']|]; inv H0.
      symmetry in HeqR. 
      eapply IHgv in HeqR; eauto.
      destruct HeqR as [J5 J6].
      split; auto.
Qed.

Lemma simulation__extractGenericValue_refl : forall mi gv1 TD t1 l0 gv,
  gv_inject mi gv1 gv1 ->
  extractGenericValue TD t1 gv1 l0 = Some gv ->
  gv_inject mi gv gv.
Proof.
  intros.
  unfold extractGenericValue in *.
  destruct (intConsts2Nats TD l0); inv H0;
    try solve [auto using gv_inject_uninits].
  destruct (mgetoffset TD t1 l1) as [[o t']|]; inv H2;
    try solve [auto using gv_inject_uninits].
  unfold mget in *. 
  destruct (getTypeStoreSize TD t'); inv H1; 
    try solve [eauto using gv_inject_gundef].
  remember (splitGenericValue gv1 o) as R.
  destruct R as [[gvl gvr]|]; inv H2;
    try solve [eauto using gv_inject_gundef].
  symmetry in HeqR.
  eapply simulation__splitGenericValue_refl in HeqR; eauto.      
  destruct HeqR as [J2 J3].
  remember (splitGenericValue gvr (Z_of_nat n)) as R1.
  destruct R1 as [[gvrl gvrr]|]; inv H1;
    try solve [eauto using gv_inject_gundef].
  symmetry in HeqR1.
  eapply simulation__splitGenericValue_refl in HeqR1; eauto.      
  destruct HeqR1; auto.
  destruct_if; eauto using gv_inject_gundef.
Qed.

Lemma simulation__insertGenericValue_refl : forall mi gv1 TD t1 l0 gv t2 gv2,
  gv_inject mi gv1 gv1 ->
  gv_inject mi gv2 gv2 ->
  insertGenericValue TD t1 gv1 l0 t2 gv2 = Some gv ->
  gv_inject mi gv gv.
Proof.
  intros.
  unfold insertGenericValue in *.
  destruct (intConsts2Nats TD l0); inv H1; 
    try solve [eauto using gv_inject_gundef].
  destruct (mgetoffset TD t1 l1) as [[o ?]|]; inv H3;
    try solve [eauto using gv_inject_gundef].
  unfold mset in *. 
  destruct (getTypeStoreSize TD t2); inv H2; 
    try solve [eauto using gv_inject_gundef].
  destruct (n =n= length gv2); subst;
    try solve [inv H3; eauto using gv_inject_gundef].
  remember (splitGenericValue gv1 o) as R.
  destruct R as [[gvl gvr]|]; inv H3;
    try solve [eauto using gv_inject_gundef].
  symmetry in HeqR.
  eapply simulation__splitGenericValue_refl in HeqR; eauto.      
  destruct HeqR as [J2 J3].
  remember (splitGenericValue gvr (Z_of_nat n)) as R1.
  destruct R1 as [[gvrl gvrr]|]; inv H2;
    try solve [eauto using gv_inject_gundef].
  symmetry in HeqR1.
  eapply simulation__splitGenericValue_refl in HeqR1; eauto.      
  destruct HeqR1.
  destruct_if; eauto using gv_inject_gundef.
  apply gv_inject_app; auto.
  apply gv_inject_app; auto.
Qed.

Lemma simulation__GV2int : forall mi gn gn' TD sz i,
  gv_inject mi gn gn' ->
  GV2int TD sz gn = Some i ->
  GV2int TD sz gn' = Some i.
Proof.
  ii.
  unfold GV2int in *.
  inv H; ss.
  inv H1; des_ifs; ss. inv H2; ss.
Qed.

Lemma simulation__GVs2Nats : forall mi TD vidxs vidxs' ns,
  gvs_inject mi vidxs vidxs' ->
  GVs2Nats TD vidxs = Some ns ->
  GVs2Nats TD vidxs' = Some ns.
Proof.
  i.
  ginduction vidxs; ii; ss; clarify.
  { des_ifs. }
  des_ifs. ss. des.
  erewrite simulation__GV2int; eauto.
  erewrite IHvidxs; eauto.
Qed.

Lemma simulation__mgep' : forall mi TD v v' t0 l1,
  MoreMem.val_inject mi v v' ->
  mgep TD t0 v l1 = None -> 
  mgep TD t0 v' l1 = None.
Proof.
(*   intros. *)
(*   unfold mgep in *. *)
(*   inv H; auto. *)
(*   destruct l1; auto. *)
(*   destruct (mgetoffset TD (typ_array 0%nat t0) (z :: l1)) as [[i1 ?]|];  *)
(*     try solve [inv H0 | auto]. *)
(* Qed. *)
Admitted.

Lemma simulation__GEP : forall maxb mi TD Mem Mem2 inbounds0 vidxs vidxs' gvp1 
    gvp gvp' t t',
  wf_sb_mi maxb mi Mem Mem2 ->
  gv_inject mi gvp gvp' ->
  gvs_inject mi vidxs vidxs' ->
  GEP TD t gvp vidxs inbounds0 t' = ret gvp1 ->
  exists gvp2,
    GEP TD t gvp' vidxs' inbounds0 t' = ret gvp2 /\
    gv_inject mi gvp1 gvp2.
Proof.
(*   intros maxb mi TD Mem Mem2 inbounds0 vidxs vidxs' gvp1 gvp gvp' t t' H H0 H1  *)
(*     H2. *)
(*   unfold GEP in *. *)
(*   remember (GV2ptr TD (getPointerSize TD) gvp) as R. *)
(*   destruct R; inv H2. *)
(*     symmetry in HeqR. *)
(*     eapply simulation__GV2ptr in HeqR; eauto. *)
(*     destruct HeqR as [v' [J1 J2]]. *)
(*     rewrite J1.  *)
(*     assert (GVs2Nats TD vidxs = GVs2Nats TD vidxs') as EQ. *)
(*       eapply simulation__GVs2Nats; eauto. *)
(*     rewrite <- EQ. *)
(*     destruct (GVs2Nats TD vidxs). *)
(*       remember (mgep TD t v l0) as R1. *)
(*       destruct R1; inv H4. *)
(*         symmetry in HeqR1. *)
(*         eapply simulation__mgep in HeqR1; eauto. *)
(*         destruct HeqR1 as [v0' [J11 J12]]. *)
(*         rewrite J11. exists (ptr2GV TD v0'). *)
(*         unfold ptr2GV, val2GV. *)
(*         simpl. eauto. *)

(*         symmetry in HeqR1. *)
(*         eapply simulation__mgep' in HeqR1; eauto. *)
(*         rewrite HeqR1. simpl.  *)
(*         unfold gundef. simpl. *)
(*         eauto using gv_inject_gundef. *)

(*       rewrite H4. eauto using gv_inject_gundef. *)

(*     erewrite simulation__GV2ptr'; eauto. *)
(*     unfold gundef. simpl. *)
(*     eauto using gv_inject_gundef. *)
(* Qed. *)
Admitted.

Lemma simulation_mload_aux : forall Mem0 Mem2 b b2 delta mi mgb
  (Hwfmi : wf_sb_mi mgb mi Mem0 Mem2)
  (Hmsim : MoreMem.mem_inj mi Mem0 Mem2)
  (H1 : mi b = ret (b2, delta)) mcs ofs gv
  (Hmloads : mload_aux Mem0 mcs b ofs = ret gv),
   exists gv2 : GenericValue,
     mload_aux Mem2 mcs b2 (ofs + delta) = ret gv2 /\ gv_inject mi gv gv2.
Proof.
  induction mcs; simpl; intros.
    inv Hmloads. eauto.

    remember (Mem.load a Mem0 b ofs) as R.
    destruct R as [v|]; tinv Hmloads.
    symmetry in HeqR.
    inv Hwfmi.
    eapply MoreMem.load_inj in HeqR; eauto.
    destruct HeqR as [v2 [Hmload Hinj]].
    rewrite Hmload.
    remember (mload_aux Mem0 mcs b (ofs + size_chunk a)) as R1.
    destruct R1; inv Hmloads.
    symmetry in HeqR1.
    apply IHmcs in HeqR1; auto.
    destruct HeqR1 as [gv2 [Hmloads Hinjs]].
    assert (ofs + delta + size_chunk a = ofs + size_chunk a + delta) as EQ. ring.
    rewrite EQ.
    rewrite Hmloads. eauto.
    { esplits; eauto. chunk_auto.
      eapply load_implies_has_chunkb; eauto. }
Qed.

Lemma simulation__fit_gv : forall maxb mi TD t Mem Mem2 gv1 gv1' gv2,
  wf_sb_mi maxb mi Mem Mem2 ->
  gv_inject mi gv1 gv2 ->
  fit_gv TD t gv1 = ret gv1' ->
  exists gv2',
    fit_gv TD t gv2 = ret gv2' /\ gv_inject mi gv1' gv2'.
Proof.
  intros maxb mi TD t Mem Mem2 gv1 gv1' gv2 Hwfmi Hinj Hfit.
  unfold fit_gv in *.
  destruct (getTypeSizeInBits TD t); tinv Hfit.
  erewrite <- gv_inject__same_size; eauto.
  erewrite <- simulation__gv_chunks_match_typb; eauto.
  destruct_if; eauto using gv_inject_gundef.
Qed.

(* The sb_ds_trans_lib.mem_simulation__free should use this lemma. *)
Lemma mem_inj__free : forall mi Mem0 M2 Mem' mgb hi lo
  (b2 : Values.block) (delta : Z) blk,
  wf_sb_mi mgb mi Mem0 M2 ->
  MoreMem.mem_inj mi Mem0 M2 ->
  Mem.free Mem0 blk lo hi = ret Mem' ->
  (lo, hi) = Mem.bounds Mem0 blk ->
  mi blk = ret (b2, delta) ->
  exists Mem2',
    Mem.free M2 b2 (lo+delta) (hi+delta) = ret Mem2' /\
    wf_sb_mi mgb mi Mem' Mem2' /\
    MoreMem.mem_inj mi Mem' Mem2'.
Proof.
  intros mi Mem0 M2 Mem' mgb hi lo b2 delta blk Hwfmi Hmsim1 H0 HeqR2 H4.
  assert ({ Mem2':Mem.mem | Mem.free M2 b2 (lo+delta) (hi+delta) = ret Mem2'})
    as J.
    apply Mem.range_perm_free.
    apply Mem.free_range_perm in H0.
    clear - H0 Hmsim1 H4.
    unfold Mem.range_perm in *.
    intros ofs J.
    assert (lo <= ofs - delta < hi) as J'.
      auto with zarith.
    apply H0 in J'.
    eapply MoreMem.perm_inj in J'; eauto.
    assert (ofs - delta + delta = ofs) as EQ. auto with zarith.
    rewrite EQ in J'. auto.
  destruct J as [Mem2' J].
  exists Mem2'. split; auto.
  split.
  SCase "wfmi".
    clear - Hwfmi H0 J H4.
    inversion_clear Hwfmi.
    split; eauto with mem.
    SSCase "Hmap3".
      intros. erewrite Mem.nextblock_free in H; eauto.
    SSCase "Hmap4".
      intros. erewrite Mem.nextblock_free; eauto.
    SSCase "bounds".
      intros. apply mi_bounds0 in H.
      erewrite Mem.bounds_free; eauto.
      erewrite Mem.bounds_free with (m2:=Mem2'); eauto.

  SCase "msim".
    clear - Hmsim1 Hwfmi H0 J H4.
    inv Hwfmi.
    eapply MoreMem.free_inj; eauto.
Qed.

(* The sb_ds_trans_lib.mem_simulation__free should use this lemma. *)
Lemma mem_inj__unchecked_free : forall mi Mem0 M2 Mem' mgb hi lo
  (b2 : Values.block) (delta : Z) blk,
  wf_sb_mi mgb mi Mem0 M2 ->
  MoreMem.mem_inj mi Mem0 M2 ->
  Mem.unchecked_free Mem0 blk lo hi = Mem' ->
  (lo, hi) = Mem.bounds Mem0 blk ->
  mi blk = ret (b2, delta) ->
  exists Mem2',
    Mem.unchecked_free M2 b2 (lo+delta) (hi+delta) = Mem2' /\
    wf_sb_mi mgb mi Mem' Mem2' /\
    MoreMem.mem_inj mi Mem' Mem2'.
Proof.
  ii.
  esplits; eauto.
  - inv H. econs; eauto.
  - eapply MoreMem.unchecked_free_inj; eauto.
    + inv H; ss.
    + inv H; ss.
Qed.

Lemma val_inject_has_chunk mi v1 v2 chk
  (Hinj: MoreMem.val_inject mi v1 v2)
  (UNDEF: v1 = Vundef -> v2 <> Vundef -> has_chunk_eq v2 chk)
  :
  has_chunk_eq v1 chk = has_chunk_eq v2 chk.
Proof.
  destruct v1, v2; inv Hinj; auto; try (by rewrite UNDEF; ss).
Qed.

Lemma has_chunkb_has_chunk_eq
      v m
      (CHUNK: Val.has_chunkb v m)
  :
    <<CHUNK: has_chunk_eq v m>>
.
Proof.
  destruct v; ss; des_ifs; ss;
    try (destruct (Nat.eq_dec _ _); ss; clarify);
    try (apply Nat.eqb_eq; ss).
Qed.

(* sb_ds_trans_lib.simulation_mstore_aux should use this *)
Lemma mem_inj_mstore_aux : forall b b2 delta mi mgb
  (H1 : mi b = ret (b2, delta)) mc gv ofs gv2 Mem0 Mem2 Mem0'
  (Hwfmi : wf_sb_mi mgb mi Mem0 Mem2)
  (Hmsim : MoreMem.mem_inj mi Mem0 Mem2)
  (Hinj : gv_inject mi gv gv2)
  (Hmstores : mstore_aux Mem0 mc gv b ofs = ret Mem0'),
   exists Mem2',
     mstore_aux Mem2 mc gv2 b2 (ofs + delta) = ret Mem2' /\
     wf_sb_mi mgb mi Mem0' Mem2' /\
     MoreMem.mem_inj mi Mem0' Mem2'.
Proof.
  induction mc; destruct gv; simpl; intros.
    inv Hinj; inv Hmstores; eauto.
    inv Hinj; inv Hmstores; eauto.
    inv Hinj; inv Hmstores; eauto.
    destruct p. inv Hinj.
    destruct (AST.memory_chunk_eq a m); simpl in *; tinv Hmstores.
    rewrite <- (val_inject_has_chunk mi v v2 m H4); cycle 1.
    { i. clarify.
      exploit CHUNK; ss; try eassumption. i.
      apply has_chunkb_has_chunk_eq; ss.
    }
    destruct (has_chunk_eq v m); simpl in *; tinv Hmstores.
    remember (Mem.store m Mem0 b ofs v) as R1.
    destruct R1 as [M|]; tinv Hmstores.
    symmetry in HeqR1.
    inv Hwfmi.
    assert (Hmstore0 := HeqR1).
    eapply MoreMem.store_mapped_inj with (f:=mi)(m2:=Mem2) in HeqR1;
      try solve [eauto | inversion Hwfmi; eauto].
    destruct HeqR1 as [Mem2' [Hmstore Hminj]].
    simpl. rewrite Hmstore.
    assert (ofs + delta + size_chunk m = ofs + size_chunk m + delta) as EQ. ring.
    rewrite EQ.
    apply IHmc with (Mem0:=M) (gv:=gv); auto.
    Case "wf_sb_mi".
      split; auto.
      SCase "Hnext1".
        erewrite <- Mem.nextblock_store with (m1:=Mem0) in Hmap3; eauto.
      SCase "Hnext2".
        intros b1 b0 delta2 J.
        apply Hmap4 in J.
        apply Mem.nextblock_store in Hmstore.
        rewrite Hmstore. auto.
      SCase "mi_freeblocks0".
        intros b0 J. apply mi_freeblocks0. intro J'. apply J.
        eapply Mem.store_valid_block_1; eauto.
      SCase "mi_mappedblocks0".
        intros b0 b' delta0 J.
        eapply Mem.store_valid_block_1; eauto.
      SCase "mi_bounds".
        intros b0 b' delta0 J.
        apply mi_bounds0 in J.
        apply Mem.bounds_store with (b':=b0) in Hmstore0; auto.
        rewrite Hmstore0. rewrite J.
        erewrite Mem.bounds_store with (m2:=Mem2'); eauto.
Qed.

