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

Lemma gv_inject_gundef_val2GV_int
      TD sz0 gv0 wz i0 mi
      (UNDEF: gundef TD (typ_int sz0) = ret gv0)
  :
    gv_inject mi gv0 (val2GV TD (Val.trunc (Vint wz i0) (sz0 - 1)) (AST.Mint (sz0 - 1)))
.
Proof.
  unfold gundef in *. des_ifs.
  unfold flatten_typ in *. des_ifs.
  ginduction l0; ii; ss; clarify; ss.
  - econs; eauto.
    i. des_ifs.
    ss.
    exploit Int.Z_mod_modulus_range; eauto.
    instantiate (1:= (sz0 - 1)%nat).
    instantiate (1:= (Int.unsigned wz i0)).
    i.
    repeat (apply andb_true_iff; split); try omega.
    + destruct (Nat.eq_dec _ _); ss.
    + destruct (zle _ _); ss. exfalso.
      omega.
    + destruct (zlt _ _); ss. exfalso.
      omega.
Qed.

Lemma gv_inject_gundef_val2GV_float
      TD gv0 mi
      fp f
      (UNDEF: gundef TD (typ_floatpoint fp) = ret gv0)
      (ORDER: floating_point_order fp fp_double = true)
  :
    gv_inject mi gv0 (val2GV TD (Vsingle (Floats.Float.to_single f)) AST.Mfloat32)
.
Proof.
  unfold gundef in *. des_ifs.
  unfold flatten_typ in *. des_ifs. ss.
  des_ifs.
  - econs; eauto.
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
        eapply gv_inject_gundef_val2GV_int; eauto.
      - right.
        esplits; eauto.
        eapply gv_inject_gundef_val2GV_int; eauto.
      - right.
        esplits; eauto.
        eapply gv_inject_gundef_val2GV_int; eauto.
      - right.
        esplits; eauto.
        eapply gv_inject_gundef_val2GV_float; eauto.
      - right.
        esplits; eauto.
        eapply gv_inject_gundef_val2GV_float; eauto.
      - right.
        esplits; eauto.
        eapply gv_inject_gundef_val2GV_float; eauto.
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
  (* intros. assert (J0:=H). *)
  (* apply gv_inject__val_inject with (TD:=TD) in H. *)
  (* destruct H as [v1 [v2 [J1 [J2 J3]]]]. *)
  (* unfold mext in *. *)
  (* rewrite J1. rewrite J2. rewrite J1 in H0. *)
  (* inv J3; try solve [ *)
  (*   auto | *)
  (*   destruct t1; destruct t2; inv H0; simpl; eauto using gv_inject_gundef; *)
  (*     match goal with *)
  (*     | H: context [floating_point_order ?f ?f0] |- _ =>  *)
  (*       destruct (floating_point_order f f0); inv H; eauto using gv_inject_gundef *)
  (*     end *)
  (*   ]. *)

  (*   destruct t1; destruct t2; inv H0; simpl; eauto using gv_inject_gundef. *)
  (*     destruct eop; inv H1;  *)
  (*       try solve [unfold val2GV; simpl; eauto using gv_inject_gundef]. *)
  (*     match goal with *)
  (*     | H: context [floating_point_order ?f1 ?f0] |- _ =>  *)
  (*        destruct (floating_point_order f1 f0); inv H; eauto using gv_inject_gundef *)
  (*     end. *)

  (*   destruct t1; destruct t2; inv H0; simpl; eauto using gv_inject_gundef. *)
  (*     match goal with *)
  (*     | H: context [floating_point_order ?f0 ?f1] |- _ =>  *)
  (*       destruct (floating_point_order f0 f1); inv H1; simpl;  *)
  (*         eauto using gv_inject_gundef; *)
  (*       destruct eop; inv H0; simpl; eauto using gv_inject_gundef; *)
  (*       destruct f1; inv H1; simpl; unfold val2GV; auto *)
  (*     end. *)
(* Qed. *)
Admitted.

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
(*   intros. assert (J0:=H0). assert (J:=H). *)
(*   apply gv_inject__val_inject with (TD:=TD) in H. *)
(*   destruct H as [v1 [v1' [J1 [J2 J3]]]]. *)
(*   apply gv_inject__val_inject with (TD:=TD) in H0. *)
(*   destruct H0 as [v2 [v2' [J1' [J2' J3']]]]. *)
(*   unfold mbop in *. *)
(*   rewrite J1. rewrite J2. rewrite J1'. rewrite J2'.   *)
(*   rewrite J1 in H1. rewrite J1' in H1.  *)
(*   inv J3; try solve [inv H1; eauto using gv_inject_gundef]. *)
(*     inv J3'; try solve [auto | inv H1; eauto using gv_inject_gundef]. *)
(*     destruct (eq_nat_dec (wz + 1) (Size.to_nat bsz));  *)
(*        try solve [inv H1; eauto using gv_inject_gundef]. *)
(*     destruct op;  *)
(*     try match goal with *)
(*       | H0 : match ?s with *)
(*         | ret _ => _ *)
(*         | merror => _ *)
(*         end = _ |- _ => destruct s eqn:Heqn *)
(*     end; *)
(*     inv H1;  *)
(*        try (left; split; auto; apply gv_inject_nptr_val_refl); eauto using gv_inject_gundef. *)
(*        apply add_isnt_ptr. *)
(*        apply sub_isnt_ptr. *)
(*        apply mul_isnt_ptr. *)
(*        intros; eapply divu_isnt_ptr; eauto. *)
(*        intros; eapply divs_isnt_ptr; eauto. *)
(*        intros; eapply modu_isnt_ptr; eauto. *)
(*        intros; eapply mods_isnt_ptr; eauto. *)
(*        apply shl_isnt_ptr. *)
(*        intros; eapply shrx_isnt_ptr; eauto. *)
(*        apply shr_isnt_ptr. *)
(*        apply and_isnt_ptr. *)
(*        apply or_isnt_ptr. *)
(*        apply xor_isnt_ptr. *)
(* Qed. *)
Admitted.

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
(*   intros. assert (J0:=H0). assert (J:=H). *)
(*   apply gv_inject__val_inject with (TD:=TD) in H. *)
(*   destruct H as [v1 [v1' [J1 [J2 J3]]]]. *)
(*   apply gv_inject__val_inject with (TD:=TD) in H0. *)
(*   destruct H0 as [v2 [v2' [J1' [J2' J3']]]]. *)
(*   unfold mfbop in *. *)
(*   rewrite J1. rewrite J2. rewrite J1'. rewrite J2'.   *)
(*   rewrite J1 in H1. rewrite J1' in H1.  *)
(*   inv J3; try solve [inv H1; eauto using gv_inject_gundef]. *)
(*     (* Float(64) *) *)
(*     inv J3'; try solve [auto | inv H1; eauto using gv_inject_gundef]. *)
(*     destruct fp; inv H1; try solve [eauto using gv_inject_gundef]. *)
(*        destruct op;  *)
(*           try (left; split; auto; apply gv_inject_nptr_val_refl;  *)
(*             try solve [auto | intro; simpl; congruence]). *)
(*     (* Float(32) *) *)
(*     inv J3'; try solve [auto | inv H1; eauto using gv_inject_gundef]. *)
(*     destruct fp; inv H1; try solve [eauto using gv_inject_gundef]. *)
(*       destruct op; *)
(*         try (left; split; auto; apply gv_inject_nptr_val_refl;  *)
(*           try solve [auto | intro; congruence]). *)
(* Qed. *)
Admitted.

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
(*   intros. assert (J0:=H0). assert (J:=H). *)
(*   apply gv_inject__val_inject with (TD:=TD) in H. *)
(*   destruct H as [v1 [v1' [J1 [J2 J3]]]]. *)
(*   apply gv_inject__val_inject with (TD:=TD) in H0. *)
(*   destruct H0 as [v2 [v2' [J1' [J2' J3']]]]. *)
(*   unfold micmp, micmp_int in *. *)
(*   rewrite J1. rewrite J2. rewrite J1'. rewrite J2'.   *)
(*   rewrite J1 in H1. rewrite J1' in H1. *)
(*   inv J3; try solve [inv H1; eauto 3 using gv_inject_gundef]. *)
(*     inv J3'; try solve [auto | inv H1; eauto using gv_inject_gundef]; *)
(*     destruct t; try solve [inv H1; eauto using gv_inject_gundef]. *)
(*       destruct c; inv H1;  *)
(*         try (left; split; auto;  *)
(*           apply gv_inject_nptr_val_refl; try solve  *)
(*             [auto | apply cmp_isnt_ptr | apply cmpu_isnt_ptr *)
(*             | apply cmpu_int_isnt_ptr]). *)
(*     destruct t; try solve [inv H1; eauto using gv_inject_gundef]. *)
(*     destruct t; try solve [inv H1; eauto using gv_inject_gundef]. *)
(*     destruct t; try solve [inv H1; eauto using gv_inject_gundef]. *)
(*     destruct t; try solve [inv H1; eauto using gv_inject_gundef]. *)
(*     destruct t; try solve [inv H1; eauto using gv_inject_gundef]. *)
(* Qed. *)
Admitted.

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
(*   intros. assert (J0:=H0). assert (J:=H). *)
(*   apply gv_inject__val_inject with (TD:=TD) in H. *)
(*   destruct H as [v1 [v1' [J1 [J2 J3]]]]. *)
(*   apply gv_inject__val_inject with (TD:=TD) in H0. *)
(*   destruct H0 as [v2 [v2' [J1' [J2' J3']]]]. *)
(*   unfold mfcmp in *. *)
(*   rewrite J1. rewrite J2. rewrite J1'. rewrite J2'.   *)
(*   rewrite J1 in H1. rewrite J1' in H1.  *)
(*   inv J3; try solve [inv H1; eauto using gv_inject_gundef]. *)
(*     inv J3'; try solve [auto | inv H1; eauto using gv_inject_gundef]; *)
(*     destruct t; try solve [inv H1; eauto using gv_inject_gundef]. *)
(*       destruct c; inv H1;  *)
(*         try solve [ *)
(*           eauto using gv_inject_gundef | *)
(*           (left; split; auto;  *)
(*           apply gv_inject_nptr_val_refl; try solve  *)
(*             [auto | apply val_of_bool_isnt_ptr | apply Vfalse_isnt_ptr |  *)
(*              apply Vtrue_isnt_ptr]) *)
(*         ]. *)
(*       destruct c; inv H1;  *)
(*         try solve [ *)
(*           eauto using gv_inject_gundef | *)
(*           (left; split; auto;  *)
(*           apply gv_inject_nptr_val_refl; try solve  *)
(*             [auto | apply val_of_bool_isnt_ptr | apply Vfalse_isnt_ptr |  *)
(*              apply Vtrue_isnt_ptr]) *)
(*         ]. *)
(* Qed. *)
Admitted.

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
        (* des_ifs; try (by esplits; eauto using gv_inject_gundef'). *)
        (* - rename gv into __gv__. *)
        (*   unfold gv_chunks_match_typb in *. unfold gundef. des_ifs. *)
        (*   esplits; eauto. *)
        (*   admit. *)
        (* - unfold gundef in *. unfold gv_chunks_match_typb in *. des_ifs. *)
        (*   esplits; eauto. *)
        (*   apply gv_inject_mc2undefs. *)
    }

      symmetry in HeqR1.
      eapply simulation__splitGenericValue_none in HeqR1; eauto.      
      rewrite HeqR1. rewrite H1. eauto using gv_inject_gundef.

    simpl.
    symmetry in HeqR.
    eapply simulation__splitGenericValue_none in HeqR; eauto.      
    rewrite HeqR. rewrite H2. eauto using gv_inject_gundef.
Qed.

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

(* TODO: move position *)
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

