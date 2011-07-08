Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../ssa/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../TV".
Require Import ssa_def.
Require Import ssa_lib.
Require Import ssa_dynamic.
Require Import trace.
Require Import Memory.
Require Import genericvalues.
Require Import alist.
Require Import Integers.
Require Import Values.
Require Import Coqlib.
Require Import monad.
Require Import Metatheory.
Require Import Znumtheory.
Require Import ssa_static.
Require Import ssa_props.
Require Import ssa_wf.

Definition gv_inject (mi: Values.meminj) (gv gv':GenericValue) : Prop :=
let '(vals,mks) := List.split gv in 
let '(vals',mks') := List.split gv' in 
val_list_inject mi vals vals'.

Definition meminj_no_overlap (f: meminj) (m: mem) : Prop :=
  forall b1 b1' delta1 b2 b2' delta2,
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2'.

Lemma meminj_no_overlap__implies : forall f m,
  meminj_no_overlap f m -> Mem.meminj_no_overlap f m.
Proof.
  intros f m J.
  unfold meminj_no_overlap in J.
  unfold Mem.meminj_no_overlap.
  eauto.
Qed.

Record wf_sb_mi maxb mi Mem1 Mem2 := mk_wf_sb_mi {
  Hno_overlap : meminj_no_overlap mi Mem1;
  Hnull : mi Mem.nullptr = Some (Mem.nullptr, 0);
  Hmap1 : forall b, b >= Mem.nextblock Mem1 -> mi b = None;
  Hmap2 : forall b1 b2 delta2, 
    mi b1 = Some (b2, delta2) -> b2 < Mem.nextblock Mem2;
  mi_freeblocks: forall b, ~(Mem.valid_block Mem1 b) -> mi b = None;
  mi_mappedblocks: forall b b' delta, 
    mi b = Some(b', delta) -> Mem.valid_block Mem2 b';
  mi_range_block: forall b b' delta, 
    mi b = Some(b', delta) -> delta = 0;
  mi_bounds: forall b b' delta, 
    mi b = Some(b', delta) -> Mem.bounds Mem1 b = Mem.bounds Mem2 b';
  mi_globals : forall b, b <= maxb -> mi b = Some (b, 0)
  }.

Fixpoint wf_global (maxb:Values.block) (gv:GenericValue) 
  : Prop :=
match gv with
| nil => True
| (Vptr b _,_)::gv' => b <= maxb /\ wf_global maxb gv'
| _::gv' => wf_global maxb gv'
end.

Fixpoint wf_globals maxb (gl:GVMap) : Prop :=
match gl with
| nil => True
| (_,gv)::gl' => wf_global maxb gv /\ wf_globals maxb gl'
end.

Lemma gv_inject_incr:
  forall f1 f2 v v',
  inject_incr f1 f2 ->
  gv_inject f1 v v' ->
  gv_inject f2 v v'.
Proof.
  intros. 
  unfold gv_inject in *.
  destruct (split v).
  destruct (split v').
  eauto using val_list_inject_incr.
Qed.

Lemma val_list_inject_app : forall mi vs1 vs1' vs2 vs2',
  val_list_inject mi vs1 vs2 ->
  val_list_inject mi vs1' vs2' ->
  val_list_inject mi (vs1++vs1') (vs2++vs2').
Proof.
  induction vs1; destruct vs2; simpl; intros; inv H; auto.
Qed.

Lemma gv_inject_app : forall mi gv1 gv1' gv2 gv2',
  gv_inject mi gv1 gv2 ->
  gv_inject mi gv1' gv2' ->
  gv_inject mi (gv1++gv1') (gv2++gv2').
Proof.
  unfold gv_inject.
  induction gv1; destruct gv2; simpl; intros; auto.  
    destruct p. destruct (split gv2). inv H.
    destruct a. destruct (split gv1). inv H.

    destruct a. remember (split gv1) as R3. destruct R3.
    destruct p. remember (split gv2) as R4. destruct R4. 
    inv H.
    remember (split (gv1 ++ gv1')) as R1. destruct R1.
    remember (split (gv2 ++ gv2')) as R2. destruct R2.
    apply val_cons_inject; auto.
      assert (J:=@IHgv1 gv1' gv2 gv2').
      rewrite <- HeqR4 in J.
      rewrite <- HeqR1 in J.
      rewrite <- HeqR2 in J.
      eapply J; eauto.
Qed.

Definition zeroconst2GV__gv_inject_refl_prop (t:typ) := 
  forall maxb mi Mem1 Mem2 gv TD, 
  wf_sb_mi maxb mi Mem1 Mem2 ->
  zeroconst2GV TD t = Some gv ->
  gv_inject mi gv gv.
  
Definition zeroconsts2GV__gv_inject_refl_prop (lt:list_typ) := 
  forall maxb mi Mem1 Mem2 gv TD n, 
  wf_sb_mi maxb mi Mem1 Mem2 ->
  zeroconsts2GV TD lt = Some (gv,n) ->
  gv_inject mi gv gv.

Ltac tinv H := try solve [inv H].
  
Lemma gv_inject__repeatGV : forall mi gv1 gv2 n,
  gv_inject mi gv1 gv2 -> 
  gv_inject mi (repeatGV gv1 n) (repeatGV gv2 n).
Proof.
  induction n; intros.
    unfold gv_inject. simpl. auto.
    simpl. eapply gv_inject_app; eauto.
Qed.

Lemma gv_inject_uninits : forall mi n, gv_inject mi (uninits n) (uninits n).
Proof.
  unfold uninits.
  induction n.
    unfold gv_inject. simpl; auto.
    simpl. simpl_env. apply gv_inject_app; auto.
      unfold gv_inject. simpl; auto.
Qed.

Lemma zeroconst2GV__gv_inject_refl_mutrec :
  (forall t, zeroconst2GV__gv_inject_refl_prop t) *
  (forall lt, zeroconsts2GV__gv_inject_refl_prop lt).
Proof.
  apply typ_mutrec; 
    unfold zeroconst2GV__gv_inject_refl_prop, 
           zeroconsts2GV__gv_inject_refl_prop; 
    intros; simpl in *; 
    try solve [unfold gv_inject; simpl in *; eauto | 
               inversion H0 | inversion H1 | inversion H2].

  unfold gv_inject.
  inv H0. simpl. 
  apply val_cons_inject; auto.

  unfold gv_inject.
  destruct f; inv H0; simpl; apply val_cons_inject; auto.

  remember (zeroconst2GV TD t) as R.
  destruct R; tinv H1.
  destruct (getTypeStoreSize TD t); tinv H1.
  destruct (getTypeAllocSize TD t); inv H1.
  simpl. symmetry in HeqR.
  eapply H in HeqR; eauto.
  apply gv_inject__repeatGV.
  apply gv_inject_app; auto.
    apply gv_inject_uninits.

  remember (zeroconsts2GV TD l0) as R.
  destruct R as [[gv0 tsz]|]; tinv H1.
  destruct (getTypeAllocSize TD (typ_struct l0)); inv H1.
  destruct l0; inv H3.
    apply gv_inject_uninits.
    symmetry in HeqR.
    eapply H in HeqR; eauto.
    apply gv_inject_app; auto.
      apply gv_inject_uninits.
 
  inv H1. unfold gv_inject. simpl.
  apply val_cons_inject; auto.
    inv H0. 
    eapply val_inject_ptr; eauto.

  inv H0. unfold gv_inject. simpl. auto.


  remember (zeroconsts2GV TD l0) as R.
  destruct R as [[gv1 tsz]|]; tinv H2.
  remember (zeroconst2GV TD t) as R1.
  destruct R1 as [gv2|]; tinv H2.
  destruct (getTypeStoreSize TD t); inv H2.
  destruct (getTypeAllocSize TD t); inv H4.
  symmetry in HeqR.
  eapply H0 in HeqR; eauto.
  symmetry in HeqR1.
  eapply H in HeqR1; eauto.
  apply gv_inject_app; auto.
  apply gv_inject_app; auto.
    apply gv_inject_uninits.
Qed.

Lemma zeroconst2GV__gv_inject_refl : forall maxb mi Mem1 Mem2 gv TD t, 
  wf_sb_mi maxb mi Mem1 Mem2 ->
  zeroconst2GV TD t = Some gv ->
  gv_inject mi gv gv.
Proof.
  intros.  
  destruct zeroconst2GV__gv_inject_refl_mutrec as [J _].
  unfold zeroconst2GV__gv_inject_refl_prop in J.
  eauto.
Qed. 

Lemma global_gv_inject_refl_aux : forall maxb mi Mem1 Mem2 gv,
  wf_sb_mi maxb mi Mem1 Mem2 ->
  wf_global maxb gv ->
  gv_inject mi gv gv.
Proof.
  unfold gv_inject.
  induction gv; intros; simpl; auto.
    destruct a.
    remember (split gv) as R.
    destruct R.
      destruct v; simpl in *; try solve 
        [assert (J:=@IHgv H H0); eauto].

        destruct H0 as [H1 H2].
        assert (J:=(@IHgv H H2)).
        inversion H.
        apply mi_globals0 in H1.
        apply val_cons_inject; auto.
          apply val_inject_ptr with (delta:=0); auto.
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
    
Lemma gv_inject_nil_inv : forall mi gv2,
  gv_inject mi nil gv2 -> gv2 = nil.
Proof.
  intros.   
  destruct gv2; eauto.
  unfold gv_inject in H. simpl in H. destruct p. destruct (split gv2). inv H.
Qed.    

Lemma gv_inject_nil_inv' : forall mi gv1,
  gv_inject mi gv1 nil -> gv1 = nil.
Proof.
  intros.   
  destruct gv1; eauto.
  unfold gv_inject in H. simpl in H. destruct p. destruct (split gv1). inv H.
Qed.    

Lemma gv_inject_cons_inv : forall mi g1 gv1 gv2,
  gv_inject mi (g1::gv1) gv2 -> 
  exists gv2', exists v1, exists m1, exists v2, exists m2, 
    gv2 = (v2,m2)::gv2' /\ gv_inject mi gv1 gv2' /\ val_inject mi v1 v2 /\
    g1 = (v1,m1).
Proof.
  intros.   
  destruct gv2; eauto.
    apply gv_inject_nil_inv' in H. inv H.
    unfold gv_inject in H. simpl in H. destruct g1. 
    remember (split gv1) as R1.  destruct R1. destruct p.
    remember (split gv2) as R2.  destruct R2. 
    inv H. exists gv2. exists v. exists m. exists v0. exists m0.
    unfold gv_inject. rewrite <- HeqR1. rewrite <- HeqR2.
    split; auto.
Qed.    

Lemma gv_inject__val_inject : forall mi gv1 gv2 TD,
  gv_inject mi gv1 gv2 ->
  exists v1, exists v2,
    GV2val TD gv1 = Some v1 /\ GV2val TD gv2 = Some v2 /\ val_inject mi v1 v2.
Proof.
  intros.
  unfold GV2val in *.
  destruct gv1.
    apply gv_inject_nil_inv in H. subst. eauto.

    apply gv_inject_cons_inv in H.
    destruct H as [gv2' [v1' [m1 [v2 [m2 [J1 [J2 [J3 J4]]]]]]]]; subst.
    destruct gv1.
      apply gv_inject_nil_inv in J2. subst. eauto.
  
      apply gv_inject_cons_inv in J2.
      destruct J2 as [gv3 [v2' [m2' [v3 [m3 [J1 [J2 [J5 J4]]]]]]]]; subst.
      eauto.
Qed.

Lemma gv_inject_nil_refl : forall mi, gv_inject mi nil nil.
Proof.
  intros. unfold gv_inject. simpl. auto.
Qed.

Lemma gv_inject_cons_intro : forall mi v1 m1 v2 m2 gv1 gv2,
  gv_inject mi gv1 gv2 ->
  val_inject mi v1 v2 ->
  gv_inject mi ((v1, m1) :: gv1) ((v2, m2) :: gv2).
Proof.
  intros.
  unfold gv_inject in *. simpl.
  remember (split gv1) as R1.
  remember (split gv2) as R2.
  destruct R1. destruct R2.
  eauto.
Qed.  

Lemma gv_inject_gundef : forall mi t, gv_inject mi (gundef t) (gundef t).
Proof.
  intros. unfold gundef. 
  destruct (typ2memory_chunk t); auto using gv_inject_uninits.
    apply gv_inject_cons_intro; auto using gv_inject_nil_refl.
Qed.

Lemma gv_inject_nptr_val_refl : forall TD v mi m,
  (forall b ofs, v <> Vptr b ofs) ->
  gv_inject mi (val2GV TD v m) (val2GV TD v m).
Proof.
  intros. unfold val2GV, gv_inject. simpl.
  destruct v; auto. 
    assert (J:=@H b i0). contradict J; auto.
Qed.

Lemma gv_inject_gundef_any_val : forall TD v mi t m,
  gv_inject mi (gundef t) (val2GV TD v m).
Proof.
  intros. unfold val2GV, gv_inject, gundef. 
  destruct (typ2memory_chunk t); simpl; auto.
Qed.

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
    destruct t1; destruct t2; inv H0; try solve [
      auto using gv_inject_gundef |
      unfold gv_inject; simpl; destruct (le_lt_dec wz s0); auto
    ].

    destruct t1; destruct t2; inv H0; auto using gv_inject_gundef.
      destruct (floating_point_order f1 f0); inv H1; 
        simpl; auto using gv_inject_gundef.
      destruct f1; inv H0; unfold gv_inject; simpl; auto using gv_inject_gundef.
 
    inv H0. auto using gv_inject_gundef.
    inv H0. auto using gv_inject_gundef.

    right. inv H0.
    destruct v2; try solve [exists (gundef t2); auto using gv_inject_gundef].
      destruct t1; try solve [exists (gundef t2); auto using gv_inject_gundef].
      remember t2 as t2'.
      destruct t2; try solve [exists (gundef t2'); subst; 
        auto using gv_inject_gundef].
        subst.
        exists (val2GV TD (Val.trunc (Vint wz i0) s0) (AST.Mint s0)).
        split; auto.  
          unfold val2GV, gv_inject. simpl.
          destruct (le_lt_dec wz s0); auto.

      destruct t1; try solve [exists (gundef t2); auto using gv_inject_gundef].
      remember t2 as t2'.
      destruct t2; try solve [exists (gundef t2'); subst; 
         auto using gv_inject_gundef].
      subst.
      destruct (floating_point_order f1 f0);
        try solve [exists (gundef (typ_floatpoint f1)); 
          simpl; auto using gv_inject_gundef].
      remember f1 as f1'.
      destruct f1; try solve [exists (gundef (typ_floatpoint f1')); subst;
          simpl; auto using gv_inject_gundef]; subst; unfold gv_inject.
        exists (val2GV TD (Val.ftrunc (Vfloat f)) AST.Mfloat32).
          simpl. auto.  
        exists (val2GV TD (Val.ftrunc (Vfloat f)) AST.Mfloat64).
          simpl. auto.  
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
  inv J3; auto.
    destruct t1; destruct t2; inv H0; simpl; auto using gv_inject_gundef.
      destruct eop; inv H1; try solve [unfold gv_inject; simpl; auto].
      destruct (floating_point_order f f0); inv H1; auto using gv_inject_gundef.

    destruct t1; destruct t2; inv H0; simpl; auto using gv_inject_gundef.
      destruct (floating_point_order f0 f1); inv H1; simpl; 
        auto using gv_inject_gundef.
      destruct eop; inv H0; simpl; auto using gv_inject_gundef.
      right. exists gv1'. split; auto.        

    destruct t1; destruct t2; inv H0; simpl; auto using gv_inject_gundef.
      destruct (floating_point_order f f0); inv H2; auto using gv_inject_gundef.

    destruct t1; destruct t2; inv H0; simpl; auto using gv_inject_gundef.
      destruct (floating_point_order f f0); inv H1; 
        simpl; auto using gv_inject_gundef.

    destruct t1; destruct t2; inv H0; simpl; auto using gv_inject_gundef.
      destruct v2; simpl; auto using gv_inject_gundef.
      destruct eop; auto using gv_inject_gundef.
        right. exists (val2GV TD (Vint wz (Int.zero_ext wz (Size.to_Z s0) i0))
           (AST.Mint (Size.to_nat s0 - 1))).
        unfold gv_inject. simpl. auto.
        right. exists (val2GV TD (Vint wz (Int.sign_ext wz (Size.to_Z s0) i0))
            (AST.Mint (Size.to_nat s0 - 1))).
        unfold gv_inject. simpl. auto.
      destruct (floating_point_order f f0); inv H1; 
        simpl; eauto using gv_inject_gundef.
        destruct v2; simpl; auto using gv_inject_gundef.
        destruct eop; simpl; auto using gv_inject_gundef.
          right. exists gv1'. split; auto.
          destruct gv1'; inv J2.
          destruct p.
          destruct gv1'; inv H0.
          unfold gv_inject. unfold gundef. simpl. 
          destruct f0; simpl; auto.
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

Lemma add_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.add (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_add; try congruence.
    unfold Val.add_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. congruence.
Qed.

Lemma sub_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.sub (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_sub; try congruence.
    unfold Val.sub_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. congruence.
Qed.

Lemma mul_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.mul (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_mul; try congruence.
    unfold Val.mul_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. congruence.
Qed.

Lemma divu_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.divu (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_divu; try congruence.
    unfold Val.divu_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. 
    destruct (Int.eq wz0 i1 (Int.zero wz0)); congruence.
Qed.

Lemma divs_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.divs (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_divs; try congruence.
    unfold Val.divs_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. 
    destruct (Int.eq wz0 i1 (Int.zero wz0)); congruence.
Qed.

Lemma modu_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.modu (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_modu; try congruence.
    unfold Val.modu_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. 
    destruct (Int.eq wz0 i1 (Int.zero wz0)); congruence.
Qed.

Lemma mods_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.mods (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_mods; try congruence.
    unfold Val.mods_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. 
    destruct (Int.eq wz0 i1 (Int.zero wz0)); congruence.
Qed.

Lemma shl_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.shl (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_shl; try congruence.
    unfold Val.shl_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. 
    destruct (Int.ltu wz0 i1 (Int.iwordsize wz0)); congruence.
Qed.

Lemma shrx_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.shrx (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_shrx; try congruence.
    unfold Val.shrx_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. 
    destruct (Int.ltu wz0 i1 (Int.iwordsize wz0)); congruence.
Qed.

Lemma shr_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.shr (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_shr; try congruence.
    unfold Val.shr_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. 
    destruct (Int.ltu wz0 i1 (Int.iwordsize wz0)); congruence.
Qed.

Lemma and_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.and (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_and; try congruence.
    unfold Val.and_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. 
    congruence.
Qed.

Lemma or_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.or (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_or; try congruence.
    unfold Val.or_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. 
    congruence.
Qed.

Lemma xor_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.xor (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_xor; try congruence.
    unfold Val.xor_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. 
    congruence.
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
  inv J3; try solve [inv H1; auto using gv_inject_gundef].
    inv J3'; try solve [auto | inv H1; auto using gv_inject_gundef].
    destruct (eq_nat_dec (wz + 1) (Size.to_nat bsz)); 
       try solve [inv H1; auto using gv_inject_gundef].
    destruct op; inv H1; 
       try (left; split; auto; apply gv_inject_nptr_val_refl; auto).
       apply add_isnt_ptr.
       apply sub_isnt_ptr.
       apply mul_isnt_ptr.
       apply divu_isnt_ptr.
       apply divs_isnt_ptr.
       apply modu_isnt_ptr.
       apply mods_isnt_ptr.
       apply shl_isnt_ptr.
       apply shrx_isnt_ptr.
       apply shr_isnt_ptr.
       apply and_isnt_ptr.
       apply or_isnt_ptr.
       apply xor_isnt_ptr.

    inv H1.
      destruct v2'; auto using gv_inject_gundef.
      destruct (eq_nat_dec (wz + 1) (Size.to_nat bsz)); 
        auto using gv_inject_gundef.
      destruct op; try solve [right; eauto using gv_inject_gundef_any_val].

    inv H1.
      destruct v1'; try solve [auto using gv_inject_gundef].
      destruct v2'; try solve [auto using gv_inject_gundef].
      destruct (eq_nat_dec (wz + 1) (Size.to_nat bsz)); 
        auto using gv_inject_gundef.
      destruct op; try solve [right; eauto using gv_inject_gundef_any_val].
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
  inv J3; try solve [inv H1; auto using gv_inject_gundef].
    inv J3'; try solve [auto | inv H1; auto using gv_inject_gundef].
    destruct fp; inv H1; try solve [auto using gv_inject_gundef].
       destruct op; 
          try (left; split; auto; apply gv_inject_nptr_val_refl; 
            try solve [auto | intro; congruence]).
       destruct op; 
          try (left; split; auto; apply gv_inject_nptr_val_refl; 
            try solve [auto | intro; congruence]).

   inv H1. 
   destruct v2'; auto using gv_inject_gundef.
   destruct fp; try solve [
     destruct op; try solve [right; eauto using gv_inject_gundef_any_val] |
     auto using gv_inject_gundef
     ].

   destruct v1'; auto using gv_inject_gundef.
      inv H1. auto using gv_inject_gundef.
      inv H1. auto using gv_inject_gundef.
      inv H1. auto using gv_inject_gundef.
      destruct v2'; auto using gv_inject_gundef.

   destruct fp; try solve [ 
      destruct op; try solve [right; eauto using gv_inject_gundef_any_val] |
      auto using gv_inject_gundef |
      inv H1; auto using gv_inject_gundef
     ].
   inv H1. auto using gv_inject_gundef.
   inv H1. auto using gv_inject_gundef.
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
        unfold gv_inject. simpl. auto.
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
      destruct t1; try solve [
        inv H0 |
        destruct t2; inv H0; eauto using gv_inject_gundef |
        destruct t2; inv H0; eauto using simulation__mcast_aux_helper
      ]
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

Lemma cmp_isnt_ptr : forall c wz i0 wz0 i1 b ofs,
  Val.cmp c (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_cmp; try congruence.
    unfold Val.cmp_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. 
    unfold Val.of_bool.
    destruct (Int.cmp wz0 c i0 i1).
      unfold Vtrue. unfold Vone. congruence.
      unfold Vfalse. unfold Vzero. congruence.
Qed.

Lemma cmpu_isnt_ptr : forall c wz i0 wz0 i1 b ofs,
  Val.cmpu c (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_cmpu; try congruence.
    unfold Val.cmpu_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. 
    unfold Val.of_bool.
    destruct (Int.cmpu wz0 c i0 i1).
      unfold Vtrue. unfold Vone. congruence.
      unfold Vfalse. unfold Vzero. congruence.
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
  inv J3; try solve [inv H1; auto using gv_inject_gundef].
    inv J3'; try solve [auto | inv H1; auto using gv_inject_gundef];
    destruct t; try solve [inv H1; auto using gv_inject_gundef].
      destruct c; inv H1; 
        try (left; split; auto; 
          apply gv_inject_nptr_val_refl; try solve 
            [auto | apply cmp_isnt_ptr | apply cmpu_isnt_ptr]).
    inv H1.
     destruct v2'; try solve [auto using gv_inject_gundef].
     destruct c; try solve [right; eauto using gv_inject_gundef_any_val].
    destruct t; try solve [inv H1; auto using gv_inject_gundef].
    destruct t; try solve [inv H1; auto using gv_inject_gundef].
    destruct t; try solve [inv H1; auto using gv_inject_gundef].
    destruct t; try solve [inv H1; auto using gv_inject_gundef].
    inv H1.
     destruct v1'; try solve [auto using gv_inject_gundef].
     destruct v2'; try solve [auto using gv_inject_gundef].
     destruct c; try solve [right; eauto using gv_inject_gundef_any_val].
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

Lemma val_of_bool_isnt_ptr : forall v b ofs,
  Val.of_bool v <> Vptr b ofs.
Proof.
  intros. unfold Val.of_bool. destruct v. 
    unfold Vtrue. unfold Vone. congruence.
    unfold Vfalse. unfold Vzero. congruence.
Qed.

Lemma Vfalse_isnt_ptr : forall b ofs,
  Vfalse <> Vptr b ofs.
Proof.
  intros. unfold Vfalse. unfold Vzero. congruence.
Qed.

Lemma Vtrue_isnt_ptr : forall b ofs,
  Vtrue <> Vptr b ofs.
Proof.
  intros. unfold Vtrue. unfold Vone. congruence.
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
  inv J3; try solve [inv H1; auto using gv_inject_gundef].
    inv J3'; try solve [auto | inv H1; auto using gv_inject_gundef];
    destruct t; try solve [inv H1; auto using gv_inject_gundef].
      destruct c; inv H1; 
        try solve [
          auto using gv_inject_gundef |
          (left; split; auto; 
          apply gv_inject_nptr_val_refl; try solve 
            [auto | apply val_of_bool_isnt_ptr | apply Vfalse_isnt_ptr | 
             apply Vtrue_isnt_ptr])
        ].
      destruct c; inv H1; 
        try solve [
          auto using gv_inject_gundef |
          (left; split; auto; 
          apply gv_inject_nptr_val_refl; try solve 
            [auto | apply val_of_bool_isnt_ptr | apply Vfalse_isnt_ptr | 
             apply Vtrue_isnt_ptr])
        ].


    inv H1.
     destruct v2'; try solve [auto using gv_inject_gundef].
     destruct c; try solve [
       right; eauto using gv_inject_gundef_any_val |
       auto using gv_inject_gundef
     ].
    inv H1.
     destruct v2'; try solve [auto using gv_inject_gundef].
     destruct c; try solve [
       right; eauto using gv_inject_gundef_any_val |
       auto using gv_inject_gundef
     ].
    inv H1. destruct v2'; try solve [auto using gv_inject_gundef].
    inv H1. destruct v2'; try solve [auto using gv_inject_gundef].
    inv H1. destruct v2'; try solve [auto using gv_inject_gundef].
    inv H1.
     destruct v1'; try solve [auto using gv_inject_gundef].
     destruct v2'; try solve [auto using gv_inject_gundef].
     destruct t; try solve [auto using gv_inject_gundef].
       destruct c; try solve [auto using gv_inject_gundef |
         right; eauto using gv_inject_gundef_any_val].
       destruct c; try solve [auto using gv_inject_gundef |
         right; eauto using gv_inject_gundef_any_val].
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
    Values.val_inject mi v v'.
Proof.
  intros.
  unfold GV2ptr in *.
  destruct gv1; tinv H0.
  destruct p; tinv H0.
  destruct v0; tinv H0.
  destruct gv1; inv H0.
  unfold gv_inject in H.
  destruct gv1'; tinv H.
  destruct p; tinv H.
  destruct gv1'; tinv H.
    destruct v; simpl in H; inv H; inv H3. eauto.
    destruct p. simpl in H. destruct (split gv1'). inv H. inv H5.
Qed.

Lemma simulation__mgep : forall mi TD v v' v0 t0 l1,
  Values.val_inject mi v v' ->
  mgep TD t0 v l1 = Some v0 ->
  exists v0',
    mgep TD t0 v' l1 = Some v0' /\
    Values.val_inject mi v0 v0'.
Proof.
  intros.
  unfold mgep in *.
  destruct v; tinv H0.
  destruct l1; tinv H0.
  inv H.
  destruct (mgetoffset TD (typ_array 0%nat t0) (z :: l1)) as [[i1 ?]|] ; tinv H0.
  inv H0. 
  exists (Vptr b2 (Int.add 31 (Int.add 31 i0 (Int.repr 31 delta)) i1)).
  split; auto.
    eapply val_inject_ptr; eauto.
      rewrite Int.add_assoc.
      assert (Int.add 31 (Int.repr 31 delta) i1 = 
              Int.add 31 i1 (Int.repr 31 delta)) as EQ.
        rewrite Int.add_commut. auto.
      rewrite EQ.
      rewrite Int.add_assoc. auto.
Qed.
   
Definition defined_gv (gv:GenericValue) : Prop :=
match gv with
| (v,_)::_ => v <> Vundef
| _ => True
end.

Fixpoint defined_gvs (gvs:list GenericValue) : Prop :=
match gvs with
| gv::gvs' => defined_gv gv /\ defined_gvs gvs'
| nil => True
end.

Definition chunk_matched (gv gv':GenericValue) : Prop :=
let '(_,ms):=split gv in
let '(_,ms'):=split gv' in
ms = ms'.

Lemma chunk_matched_nil_inv : forall gv2,
  chunk_matched nil gv2 -> gv2 = nil.
Proof.
  intros.   
  destruct gv2; eauto.
  unfold chunk_matched in H. simpl in H. destruct p. destruct (split gv2). inv H.
Qed.    

Lemma chunk_matched_nil_inv' : forall gv1,
  chunk_matched gv1 nil -> gv1 = nil.
Proof.
  intros.   
  destruct gv1; eauto.
  unfold chunk_matched in H. simpl in H. destruct p. destruct (split gv1). inv H.
Qed.    

Lemma chunk_matched_nil_refl : chunk_matched nil nil.
Proof.
  intros. unfold chunk_matched. simpl. auto.
Qed.

Lemma chunk_matched_cons_intro : forall v1 m v2 gv1 gv2,
  chunk_matched gv1 gv2 ->
  chunk_matched ((v1, m) :: gv1) ((v2, m) :: gv2).
Proof.
  intros.
  unfold chunk_matched in *. simpl.
  remember (split gv1) as R1.
  remember (split gv2) as R2.
  destruct R1. destruct R2.
  inv H. auto.
Qed.  

Lemma chunk_matched_cons_inv : forall g1 gv1 gv2,
  chunk_matched (g1::gv1) gv2 -> 
  exists gv2', exists v1, exists m1, exists v2,
    gv2 = (v2,m1)::gv2' /\ chunk_matched gv1 gv2' /\ g1 = (v1,m1).
Proof.
  intros.   
  destruct gv2; eauto.
    apply chunk_matched_nil_inv' in H. inv H.
    unfold chunk_matched in H. simpl in H. destruct g1. 
    remember (split gv1) as R1.  destruct R1. destruct p.
    remember (split gv2) as R2.  destruct R2. 
    inv H. exists gv2. exists v. exists m0. exists v0.
    unfold chunk_matched. rewrite <- HeqR1. rewrite <- HeqR2.
    split; auto.
Qed.    

Lemma simulation__splitGenericValue_some : forall mi gv gv' z gvl gvr,
  chunk_matched gv gv' ->
  gv_inject mi gv gv' ->
  splitGenericValue gv z = Some (gvl, gvr) ->
  exists gvl', exists gvr', 
    splitGenericValue gv' z = Some (gvl', gvr') /\
    gv_inject mi gvl gvl' /\ chunk_matched gvl gvl' /\
    gv_inject mi gvr gvr' /\ chunk_matched gvr gvr'.
Proof.
  induction gv; simpl; intros gv' z gvl gvr J H H0.
    apply gv_inject_nil_inv in H. subst.
    simpl.
    destruct (zeq z 0); inv H0. 
      exists nil. exists nil. split; auto using gv_inject_nil_refl.
      destruct (zlt z 0); inv H1.

    apply gv_inject_cons_inv in H. 
    destruct H as [gv2' [v1 [m1 [v2 [m2 [J1 [J2 [J3 J4]]]]]]]]; subst.
    simpl.
    destruct (zeq z 0); inv H0. 
      exists nil. exists ((v2, m2)::gv2'). 
      split; auto using gv_inject_nil_refl, gv_inject_cons_intro,
         chunk_matched_nil_refl, chunk_matched_cons_intro.
    destruct (zlt z 0); inv H1.
    remember (splitGenericValue gv (z - size_chunk m1)) as R.
    destruct R as [[gvl' gvr']|]; inv H0.
    apply chunk_matched_cons_inv in J.
    destruct J as [gv2 [v3 [m3 [v4 [J1 [J2' J3']]]]]]; subst.
    inv J1. inv J3'.
    symmetry in HeqR.
    eapply IHgv in HeqR; eauto.
    destruct HeqR as [gvl'0 [gvr' [J4 [J5 [J6 [J7 J8]]]]]].
    rewrite J4.     
    exists ((v4, m3) :: gvl'0). exists gvr'. 
    split; auto using gv_inject_cons_intro, chunk_matched_cons_intro.
Qed.
   
Lemma simulation__splitGenericValue_none : forall mi gv gv' z,
  chunk_matched gv gv' ->
  gv_inject mi gv gv' ->
  splitGenericValue gv z = None ->
  splitGenericValue gv' z = None.
Proof.
  induction gv; simpl; intros gv' z J H H0.
    apply gv_inject_nil_inv in H. subst.
    simpl.
    destruct (zeq z 0); inv H0. 
    destruct (zlt z 0); inv H1; auto.

    apply gv_inject_cons_inv in H. 
    destruct H as [gv2' [v1 [m1 [v2 [m2 [J1 [J2 [J3 J4]]]]]]]]; subst.
    simpl.
    destruct (zeq z 0); inv H0. 
    destruct (zlt z 0); inv H1; auto.
    remember (splitGenericValue gv (z - size_chunk m1)) as R.
    destruct R as [[gvl' gvr']|]; inv H0.
    apply chunk_matched_cons_inv in J.
    destruct J as [gv2 [v3 [m3 [v4 [J1 [J2' J3']]]]]]; subst.
    inv J1. inv J3'.
    symmetry in HeqR.
    eapply IHgv in HeqR; eauto.
    rewrite HeqR; auto.
Qed.

Lemma simulation__extractGenericValue : forall mi gv1 gv1' TD t1 l0 gv,
  chunk_matched gv1 gv1' ->
  gv_inject mi gv1 gv1' ->
  extractGenericValue TD t1 gv1 l0 = Some gv ->
  exists gv',
    extractGenericValue TD t1 gv1' l0 = Some gv' /\
    gv_inject mi gv gv'.
Proof.
  intros mi gv1 gv1' TD t1 l0 gv J H H0.
  unfold extractGenericValue in *.
  destruct (intConsts2Nats TD l0); inv H0; 
    try solve [exists (uninits 1); auto using gv_inject_uninits].
  destruct (mgetoffset TD t1 l1) as [[o t']|]; inv H2;
    try solve [exists (uninits 1); auto using gv_inject_uninits].
  unfold mget in *. 
  destruct (getTypeStoreSize TD t'); inv H1; 
    try solve [exists (gundef t'); auto using gv_inject_gundef].
  remember (splitGenericValue gv1 (Int.signed 31 o)) as R.
  destruct R as [[gvl gvr]|].
    symmetry in HeqR.
    eapply simulation__splitGenericValue_some in HeqR; eauto.      
    destruct HeqR as [gvl' [gvr' [J1 [J2 [J3 [J4 J5]]]]]].
    simpl. rewrite J1.
    remember (splitGenericValue gvr (Z_of_nat n)) as R1.
    destruct R1 as [[gvrl gvrr]|]; inv H2.
      symmetry in HeqR1.
      eapply simulation__splitGenericValue_some in HeqR1; eauto.      
      destruct HeqR1 as [gvrl' [gvrr' [J1' [J2' [J3' [J4' J5']]]]]].
      simpl. rewrite J1'. eauto.

      symmetry in HeqR1.
      eapply simulation__splitGenericValue_none in HeqR1; eauto.      
      rewrite HeqR1.     
      exists (gundef t'). auto using gv_inject_gundef.
    symmetry in HeqR.
    eapply simulation__splitGenericValue_none in HeqR; eauto.      
    rewrite HeqR. inv H2.    
    exists (gundef t'). auto using gv_inject_gundef.
Qed.

Lemma gv_inject_length_eq : forall mi gv1 gv2,
  gv_inject mi gv1 gv2 -> length gv1 = length gv2.
Proof.
  induction gv1; intros.
    apply gv_inject_nil_inv in H. subst.
    simpl. auto.

    apply gv_inject_cons_inv in H. 
    destruct H as [gv2' [v1 [m1 [v2 [m2 [J1 [J2 [J3 J4]]]]]]]]; subst.
    simpl. eauto.
Qed.

Lemma simulation__insertGenericValue: forall mi gv1 gv1' TD t1 l0 gv t2 gv2 gv2',
  chunk_matched gv1 gv1' ->
  chunk_matched gv2 gv2' ->
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  insertGenericValue TD t1 gv1 l0 t2 gv2 = Some gv ->
  exists gv',
    insertGenericValue TD t1 gv1' l0 t2 gv2' = Some gv' /\
    gv_inject mi gv gv'.
Proof.
  intros mi gv1 gv1' TD t1 l0 gv t2 gv2 gv2' JJ JJ' H H0 H1.
  unfold insertGenericValue in *.
  destruct (intConsts2Nats TD l0); inv H1; 
    try solve [exists (gundef t1); auto using gv_inject_gundef].
  destruct (mgetoffset TD t1 l1) as [[o ?]|]; inv H3;
    try solve [exists (gundef t1); auto using gv_inject_gundef].
  unfold mset in *. 
  destruct (getTypeStoreSize TD t2); inv H2; 
    try solve [exists (gundef t1); auto using gv_inject_gundef].
  assert (J:=@gv_inject_length_eq mi gv2 gv2' H0). 
  rewrite <- J. simpl.
  destruct (n =n= length gv2); subst;
    try solve [inv H3; exists (gundef t1); auto using gv_inject_gundef].
  remember (splitGenericValue gv1 (Int.signed 31 o)) as R.
  destruct R as [[gvl gvr]|].
    symmetry in HeqR.
    eapply simulation__splitGenericValue_some in HeqR; eauto.      
    destruct HeqR as [gvl' [gvr' [J1 [J2 [J3 [J4 J5]]]]]].
    simpl. rewrite J1.
    remember (splitGenericValue gvr (Z_of_nat n)) as R1.
    destruct R1 as [[gvrl gvrr]|]; inv H3.
      symmetry in HeqR1.
      eapply simulation__splitGenericValue_some in HeqR1; eauto.      
      destruct HeqR1 as [gvrl' [gvrr' [J1' [J2' [J3' [J4' J5']]]]]].
      simpl. rewrite J1'. 
      exists (gvl' ++ gv2' ++ gvrr').
      split; auto.
        apply gv_inject_app; auto.
        apply gv_inject_app; auto.

      symmetry in HeqR1.
      eapply simulation__splitGenericValue_none in HeqR1; eauto.      
      rewrite HeqR1.     
      exists (gundef t1). auto using gv_inject_gundef.
    symmetry in HeqR.
    eapply simulation__splitGenericValue_none in HeqR; eauto.      
    rewrite HeqR. inv H3.    
    exists (gundef t1). auto using gv_inject_gundef.
Qed.

Lemma simulation__eq__GV2int : forall mi gn gn' TD sz,
  defined_gv gn ->
  gv_inject mi gn gn' ->
  GV2int TD sz gn = GV2int TD sz gn'.
Proof.
  intros mi gn gn' TD sz Hdef Hinj.
  unfold GV2int.
  destruct gn.
    apply gv_inject_nil_inv in Hinj. subst. auto.

    apply gv_inject_cons_inv in Hinj.
    destruct Hinj as [gv2 [v1 [m1 [v2 [m2 [J1 [J2 [J3 J4]]]]]]]]; subst.
    inv J3; auto.
      destruct gn.   
        apply gv_inject_nil_inv in J2. subst. auto.
        apply gv_inject_cons_inv in J2.
        destruct J2 as [gv2' [v1' [m1' [v2' [m2' [J1' [J2' [J3' J4']]]]]]]]; 
          subst; auto.
        destruct v2; auto.
          destruct gv2; auto.
          simpl in Hdef. contradict Hdef; auto.
Qed.

Lemma simulation__isGVZero : forall mi c c' TD,
  defined_gv c ->
  gv_inject mi c c' ->
  isGVZero TD c = isGVZero TD c'.
Proof.
  intros mi c c' TD Hdef Hinj.
  unfold isGVZero.   
  erewrite simulation__eq__GV2int; eauto.
Qed.

Lemma simulation__mtrunc_refl : forall mi TD top t1 gv1 t2 gv2,
  gv_inject mi gv1 gv1 ->
  mtrunc TD top t1 t2 gv1 = Some gv2 ->
  gv_inject mi gv2 gv2.
Proof.
  intros.
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v2 [J1 [J2 J3]]]].
  unfold mtrunc in *.
  rewrite J1 in H0. 
  rewrite J1 in J2. inv J2.
  destruct v2; try (inv J3); try solve [inv H0; auto using gv_inject_gundef].
    destruct t1; try solve [
      inv H0; auto using gv_inject_gundef |
      destruct t2; try solve 
        [inv H0; auto using gv_inject_gundef | 
         inv H0; destruct (le_lt_dec wz s0); unfold gv_inject; simpl; auto]
    ].

    destruct t1; try solve [
      inv H0; auto using gv_inject_gundef |
      destruct t2; try solve [
        inv H0; auto using gv_inject_gundef |
        destruct (floating_point_order f1 f0); try solve [
          destruct f1; try solve [inv H0; unfold gv_inject; simpl; auto] |
          inv H0; auto using gv_inject_gundef
        ]
      ]
    ].
Qed.

Lemma simulation__mext_refl : forall mi TD eop t1 gv1 t2 gv2,
  gv_inject mi gv1 gv1 ->
  mext TD eop t1 t2 gv1 = Some gv2 ->
  gv_inject mi gv2 gv2.
Proof.
  intros. assert (J0:=H).
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v2 [J1 [J2 J3]]]].
  unfold mext in *.
  rewrite J1 in H0.
  rewrite J1 in J2. inv J2.
  destruct t1; destruct t2; inv H0; auto using gv_inject_gundef.
    destruct v2; inv H1; auto using gv_inject_gundef.
    destruct eop; inv H0; try solve [
      auto using gv_inject_gundef | unfold gv_inject; simpl; auto].
    destruct (floating_point_order f f0); inv H1; try solve [
      auto using gv_inject_gundef | unfold gv_inject; simpl; auto].
    destruct v2; inv H0; auto using gv_inject_gundef.
    destruct eop; inv H1; auto using gv_inject_gundef.
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
    try solve [inv H1; auto using gv_inject_gundef].
  destruct v2';
    try solve [inv H1; auto using gv_inject_gundef].
  destruct (eq_nat_dec (wz + 1) (Size.to_nat bsz)); 
     try solve [inv H1; auto using gv_inject_gundef].
  destruct op; inv H1; try (apply gv_inject_nptr_val_refl; auto).
       apply add_isnt_ptr.
       apply sub_isnt_ptr.
       apply mul_isnt_ptr.
       apply divu_isnt_ptr.
       apply divs_isnt_ptr.
       apply modu_isnt_ptr.
       apply mods_isnt_ptr.
       apply shl_isnt_ptr.
       apply shrx_isnt_ptr.
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
    try solve [inv H1; auto using gv_inject_gundef].
  destruct v2';
    try solve [inv H1; auto using gv_inject_gundef].
  destruct fp; try solve [inv H1; auto using gv_inject_gundef].
  destruct op; inv H1; 
    try (apply gv_inject_nptr_val_refl; try solve [auto | intro; congruence]).
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
      inv H0; auto using gv_inject_gundef |
      destruct t1; destruct t2; inv H0; auto using gv_inject_gundef
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
  destruct t; try solve [inv H1; auto using gv_inject_gundef].
  destruct v1'; try solve [inv H1; auto using gv_inject_gundef].
  destruct v2'; try solve [inv H1; auto using gv_inject_gundef].
  destruct c; inv H1; 
        try (apply gv_inject_nptr_val_refl; try solve 
            [auto | apply cmp_isnt_ptr | apply cmpu_isnt_ptr]).
Qed.

Lemma simulation__mfcmp_refl : forall mi TD c t gv1 gv2 gv3,
  gv_inject mi gv1 gv1 ->
  gv_inject mi gv2 gv2 ->
  mfcmp TD c t gv1 gv2 = Some gv3 ->
  gv_inject mi gv3 gv3.
Proof.
  intros. assert (J0:=H0). assert (J:=H).
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v1' [J1 [J2 J3]]]].
  apply gv_inject__val_inject with (TD:=TD) in H0.
  destruct H0 as [v2 [v2' [J1' [J2' J3']]]].
  rewrite J1 in J2. inv J2.
  rewrite J1' in J2'. inv J2'.
  unfold mfcmp in *.
  rewrite J1 in H1. rewrite J1' in H1. 
  destruct v1'; try solve [inv H1; auto using gv_inject_gundef].
  destruct v2'; try solve [inv H1; auto using gv_inject_gundef].
  destruct t; try solve [inv H1; auto using gv_inject_gundef].
  destruct c; inv H1; try (
    apply gv_inject_nptr_val_refl; try solve 
            [auto | apply val_of_bool_isnt_ptr | apply Vfalse_isnt_ptr | 
             apply Vtrue_isnt_ptr]
    ).
    auto using gv_inject_gundef.
    auto using gv_inject_gundef.
  destruct c; inv H1; try (
    apply gv_inject_nptr_val_refl; try solve 
            [auto | apply val_of_bool_isnt_ptr | apply Vfalse_isnt_ptr | 
             apply Vtrue_isnt_ptr]
    ).
    auto using gv_inject_gundef.
    auto using gv_inject_gundef.
Qed.

Lemma simulation__mgep_refl : forall mi TD v v0 t0 l1,
  Values.val_inject mi v v ->
  mgep TD t0 v l1 = Some v0 ->
  Values.val_inject mi v0 v0.
Proof.
  intros.
  unfold mgep in *.
  destruct v; tinv H0.
  destruct l1; tinv H0.
  destruct (mgetoffset TD (typ_array 0%nat t0) (z :: l1)) as [[o ?]|]; tinv H0.
  inv H0.
  inversion H. subst i0 b ofs1 b1.
  eapply val_inject_ptr; eauto.
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
  val_inject mi v v.
Proof.
  intros.
  unfold GV2ptr in H0.
  destruct gv; tinv H0.
  destruct p; tinv H0.
  destruct v0; tinv H0.
  destruct gv; tinv H0.
  inv H0.
  unfold gv_inject in H.
  simpl in H. inv H; auto.
Qed.

Lemma simulation__splitGenericValue_refl : forall mi gv z gvl gvr,
  gv_inject mi gv gv ->
  splitGenericValue gv z = Some (gvl, gvr) ->
  gv_inject mi gvl gvl /\
  gv_inject mi gvr gvr.
Proof.
  induction gv; simpl; intros.
    apply gv_inject_nil_inv in H. subst.
    simpl.
    destruct (zeq z 0); inv H0. 
      auto using gv_inject_nil_refl.
      destruct (zlt z 0); inv H2.

    apply gv_inject_cons_inv in H. 
    destruct H as [gv2' [v1 [m1 [v2 [m2 [J1 [J2 [J3 J4]]]]]]]]; subst.
    simpl.
    destruct (zeq z 0); inv H0. 
      inv J1.
      split; auto using gv_inject_nil_refl, gv_inject_cons_intro.
    destruct (zlt z 0); inv H1.
    remember (splitGenericValue gv (z - size_chunk m1)) as R.
    destruct R as [[gvl' gvr']|]; inv H0.
    symmetry in HeqR. inv J1.
    eapply IHgv in HeqR; eauto.
    destruct HeqR as [J5 J6].
    split; auto using gv_inject_cons_intro.
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
    try solve [auto using gv_inject_gundef].
  remember (splitGenericValue gv1 (Int.signed 31 o)) as R.
  destruct R as [[gvl gvr]|]; inv H2;
    try solve [auto using gv_inject_gundef].
  symmetry in HeqR.
  eapply simulation__splitGenericValue_refl in HeqR; eauto.      
  destruct HeqR as [J2 J3].
  remember (splitGenericValue gvr (Z_of_nat n)) as R1.
  destruct R1 as [[gvrl gvrr]|]; inv H1;
    try solve [auto using gv_inject_gundef].
  symmetry in HeqR1.
  eapply simulation__splitGenericValue_refl in HeqR1; eauto.      
  destruct HeqR1; auto.
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
    try solve [auto using gv_inject_gundef].
  destruct (mgetoffset TD t1 l1) as [[o ?]|]; inv H3;
    try solve [auto using gv_inject_gundef].
  unfold mset in *. 
  destruct (getTypeStoreSize TD t2); inv H2; 
    try solve [ auto using gv_inject_gundef].
  destruct (n =n= length gv2); subst;
    try solve [inv H3; auto using gv_inject_gundef].
  remember (splitGenericValue gv1 (Int.signed 31 o)) as R.
  destruct R as [[gvl gvr]|]; inv H3;
    try solve [auto using gv_inject_gundef].
  symmetry in HeqR.
  eapply simulation__splitGenericValue_refl in HeqR; eauto.      
  destruct HeqR as [J2 J3].
  remember (splitGenericValue gvr (Z_of_nat n)) as R1.
  destruct R1 as [[gvrl gvrr]|]; inv H2;
    try solve [auto using gv_inject_gundef].
  symmetry in HeqR1.
  eapply simulation__splitGenericValue_refl in HeqR1; eauto.      
  destruct HeqR1.
  apply gv_inject_app; auto.
  apply gv_inject_app; auto.
Qed.

Definition sb_mem_inj__const2GV_prop (c:const) := forall maxb mi Mem1 Mem2 TD gl 
    gv t,
  wf_sb_mi maxb mi Mem1 Mem2 ->
  wf_globals maxb gl -> 
  _const2GV TD gl c = Some (gv,t) ->
  gv_inject mi gv gv.

Definition sb_mem_inj__list_const2GV_prop (lc:list_const) := 
  forall maxb mi Mem1 Mem2 TD gl,
  wf_sb_mi maxb mi Mem1 Mem2 ->
  wf_globals maxb gl -> 
  (forall gv, 
    _list_const_arr2GV TD gl lc = Some gv ->
    gv_inject mi gv gv
  ) /\
  (forall gv t a, 
    _list_const_struct2GV TD gl lc = Some (gv,t,a) ->
    gv_inject mi gv gv
  ).

Lemma sb_mem_inj__const2GV_mutrec :
  (forall c, sb_mem_inj__const2GV_prop c) *
  (forall lc, sb_mem_inj__list_const2GV_prop lc).
Proof.
  apply const_mutrec; 
    unfold sb_mem_inj__const2GV_prop, sb_mem_inj__list_const2GV_prop;
    intros; simpl in *; eauto.
Case "zero".
  remember (zeroconst2GV TD t) as R.
  destruct R; inv H1.
  eauto using zeroconst2GV__gv_inject_refl.
Case "int".
  inv H1.
  unfold val2GV, gv_inject; simpl; auto.
Case "float".
  destruct f; inv H1; unfold val2GV, gv_inject; simpl; auto.
Case "undef".
  remember (getTypeSizeInBits TD t) as R.
  destruct R; inv H1. 
  apply gv_inject_gundef.
Case "null".
  inv H1. unfold val2GV, gv_inject; simpl; auto.
      apply val_cons_inject; auto.
      apply val_inject_ptr with (delta:=0); auto.
      destruct H. auto.
Case "arr". 
  eapply H with (TD:=TD)(gl:=gl) in H1; eauto.
  destruct H1; eauto.
  remember (_list_const_arr2GV TD gl l0) as R.
  destruct R; inv H2. eauto.
Case "struct". 
  eapply H with (TD:=TD)(gl:=gl) in H1; eauto.
  destruct H1 as [H00 H01].
  remember (_list_const_struct2GV TD gl l0) as R.
  destruct R as [[[gv1 t1] a1]|]; inv H2.
  destruct (getTypeAllocSize TD (typ_struct t1)); try solve [inv H3].
  destruct l0; inv H3.
    apply gv_inject_uninits.
    apply gv_inject_app; eauto.
      apply gv_inject_uninits.
Case "gid".
  remember (lookupAL GenericValue gl i0) as R.
  destruct R; inv H1.
  eauto using global_gv_inject_refl.
Case "trunc".
  remember (_const2GV TD gl c) as R.
  destruct R as [[gv1 t1']|]; try solve [inv H2].
  symmetry in HeqR.
  eapply H in HeqR; eauto.
  remember (mtrunc TD t t1' t0 gv1) as R1.
  destruct R1; inv H2.
  symmetry in HeqR1.
  eapply simulation__mtrunc_refl in HeqR1; eauto.
Case "ext".
  remember (_const2GV TD gl c) as R.
  destruct R as [[gv1 t1']|]; tinv H2.
  symmetry in HeqR.
  eapply H in HeqR; eauto.
  remember (mext TD e t1' t gv1) as R1.
  destruct R1; inv H2.
  symmetry in HeqR1.
  eapply simulation__mext_refl in HeqR1; eauto.
Case "cast".
  remember (_const2GV TD gl c0) as R.
  destruct R as [[gv1 t1']|]; tinv H2.
  symmetry in HeqR.
  eapply H in HeqR; eauto.
  remember (mcast TD c t1' t gv1) as R1.
  destruct R1; inv H2.
  symmetry in HeqR1.
  eapply simulation__mcast_refl in HeqR1; eauto.
Case "gep".
  remember (_const2GV TD gl c) as R1.
  destruct R1 as [[gv1 t1]|]; tinv H3.
  destruct t1; tinv H3.
  remember (getConstGEPTyp l0 (typ_pointer t1)) as R2.
  destruct R2; tinv H3.
  remember (GV2ptr TD (getPointerSize TD) gv1) as R3.
  destruct R3; tinv H3.
    remember (intConsts2Nats TD l0) as R4.
    destruct R4; tinv H3.
      remember (mgep TD t1 v l1) as R5.
      destruct R5; inv H3.
        symmetry in HeqR1.
        eapply H in HeqR1; eauto.
        symmetry in HeqR5.
        eapply simulation__mgep_refl with (mi:=mi) in HeqR5; 
          eauto using GV2ptr_refl.
        unfold ptr2GV, val2GV, gv_inject. simpl. auto.

        apply gv_inject_gundef.
      inv H3. apply gv_inject_gundef.
    inv H3. apply gv_inject_gundef.
Case "select".
  remember (_const2GV TD gl c) as R3.
  destruct R3 as [[gv3 t3]|]; tinv H4.
  remember (_const2GV TD gl c0) as R4.
  destruct R4 as [[gv4 t4]|]; tinv H4.
  remember (_const2GV TD gl c1) as R5.
  destruct R5; tinv H4.
  destruct (isGVZero TD gv3); inv H4; eauto.
Case "icmp".
  remember (_const2GV TD gl c0) as R3.
  destruct R3 as [[gv3 t3]|]; tinv H3.
  remember (_const2GV TD gl c1) as R4.
  destruct R4 as [[gv4 t4]|]; tinv H3.
  symmetry in HeqR3. 
  eapply H in HeqR3; eauto.
  symmetry in HeqR4. 
  eapply H0 in HeqR4; eauto.
  remember (micmp TD c t3 gv3 gv4) as R1.
  destruct R1; inv H3.
  symmetry in HeqR1.
  eapply simulation__micmp_refl in HeqR1; eauto.
Case "fcmp".
  remember (_const2GV TD gl c) as R3.
  destruct R3 as [[gv3 t3]|]; tinv H3.
  destruct t3; tinv H3.  
  remember (_const2GV TD gl c0) as R4.
  destruct R4 as [[gv4 t4]|]; tinv H3.
  symmetry in HeqR3. 
  eapply H in HeqR3; eauto.
  symmetry in HeqR4. 
  eapply H0 in HeqR4; eauto.
  remember (mfcmp TD f f0 gv3 gv4) as R1.
  destruct R1; inv H3.
  symmetry in HeqR1.
  eapply simulation__mfcmp_refl in HeqR1; eauto.
Case "extractValue". 
  remember (_const2GV TD gl c) as R.
  destruct R as [[gv1 t1]|]; tinv H3.
  remember (getSubTypFromConstIdxs l0 t1) as R2.
  destruct R2; tinv H3.   
  remember (extractGenericValue TD t1 gv1 l0) as R3.
  destruct R3; inv H3.   
  symmetry in HeqR3.
  eapply simulation__extractGenericValue_refl in HeqR3; eauto.
Case "insertValue". 
  remember (_const2GV TD gl c) as R.
  destruct R as [[gv1 t1]|]; tinv H4.
  remember (_const2GV TD gl c0) as R2.
  destruct R2 as [[gv2 t2]|]; tinv H4.
  remember (insertGenericValue TD t1 gv1 l0 t2 gv2) as R3.
  destruct R3; inv H4.   
  symmetry in HeqR3.
  eapply simulation__insertGenericValue_refl in HeqR3; eauto.
Case "bop".
  remember (_const2GV TD gl c) as R3.
  destruct R3 as [[gv3 t3]|]; tinv H3.
  destruct t3; tinv H3.
  remember (_const2GV TD gl c0) as R4.
  destruct R4 as [[gv4 t4]|]; tinv H3.
  remember (mbop TD b s gv3 gv4) as R1.
  destruct R1; inv H3.
  symmetry in HeqR1.
  eapply simulation__mbop_refl in HeqR1; eauto.
Case "fbop".
  remember (_const2GV TD gl c) as R3.
  destruct R3 as [[gv3 t3]|]; tinv H3.
  destruct t3; tinv H3.
  remember (_const2GV TD gl c0) as R4.
  destruct R4 as [[gv4 t4]|]; tinv H3.
  remember (mfbop TD f f0 gv3 gv4) as R1.
  destruct R1; inv H3.
  symmetry in HeqR1.
  eapply simulation__mfbop_refl in HeqR1; eauto.
Case "nil".
  split.
    intros gv J.
    inv J. apply gv_inject_nil_refl; auto.
    intros gv t a J.
    inv J. apply gv_inject_nil_refl; auto.
Case "cons".
  split; intros.
    remember (_list_const_arr2GV TD gl l0) as R3.
    destruct R3 as [gv3|]; tinv H3.
    remember (_const2GV TD gl c) as R4.
    destruct R4 as [[gv4 t4]|]; tinv H3.
    symmetry in HeqR4.
    eapply H in HeqR4; eauto.
    eapply H0 with (TD:=TD) in H1; eauto.
    destruct H1 as [J3 J4]; auto.
    destruct (getTypeStoreSize TD t4); tinv H3.
    destruct (getTypeAllocSize TD t4); inv H3.
      apply gv_inject_app.
        apply gv_inject_app; auto.
        apply gv_inject_uninits.

    remember (_list_const_struct2GV TD gl l0) as R3.
    destruct R3 as [[[gv3 t3] a3]|]; tinv H3.
    remember (_const2GV TD gl c) as R4.
    destruct R4 as [[gv4 t4]|]; tinv H3.
    symmetry in HeqR4.
    eapply H in HeqR4; eauto.
    eapply H0 with (TD:=TD) in H1; eauto.
    destruct H1 as [J3 J4]; auto.
    destruct (getTypeStoreSize TD t4); tinv H3.
    destruct (getTypeAllocSize TD t4); inv H3.
      apply gv_inject_app; eauto.
        apply gv_inject_app; auto.
        apply gv_inject_uninits.
Qed.

Lemma sb_mem_inj__cgv2gv : forall mi g, 
  gv_inject mi g g -> gv_inject mi (? g ?) (? g ?).
Proof.
  intros.  
  destruct g; auto.
  destruct p; auto.
  destruct v; auto.
  destruct g; auto.
  destruct m; apply gv_inject_cons_intro; auto using gv_inject_nil_refl.
Qed.

Lemma sb_mem_inj__const2GV : forall maxb mi Mem Mem' TD gl c gv,
  wf_sb_mi maxb mi Mem Mem' ->
  wf_globals maxb gl -> 
  const2GV TD gl c = Some gv ->
  gv_inject mi gv gv.
Proof.
  destruct sb_mem_inj__const2GV_mutrec as [J _].
  unfold sb_mem_inj__const2GV_prop in J. 
  intros.
  unfold const2GV in H1.
  remember (_const2GV TD gl c) as R.
  destruct R as [[? ?]|]; inv H1; auto.
  apply sb_mem_inj__cgv2gv; eauto.
Qed.

Fixpoint gvs_inject mi gvs1 gvs2 : Prop :=
match (gvs1, gvs2) with
| (nil, nil) => True
| (gv1::gvs1', gv2::gvs2') => gv_inject mi gv1 gv2 /\ gvs_inject mi gvs1' gvs2'
| _ => False
end.

Lemma simulation__GVs2Nats : forall mi TD vidxs vidxs',
  defined_gvs vidxs ->
  gvs_inject mi vidxs vidxs' ->
  GVs2Nats TD vidxs = GVs2Nats TD vidxs'.
Proof.
  induction vidxs; intros vidxs' Hdefs Hinj.
    destruct vidxs'; inv Hinj; simpl; auto.
    destruct vidxs'; simpl in *; inv Hinj; auto.
      destruct Hdefs as [J1 J2].
      erewrite simulation__eq__GV2int; eauto.      
      erewrite IHvidxs; eauto.
Qed.

Lemma gv_inject_ptr_inv : forall mi b ofs gv' cm,
  gv_inject mi ((Vptr b ofs,cm)::nil) gv' ->
  exists b', exists ofs', exists cm,
    gv' = (Vptr b' ofs', cm)::nil /\
    val_inject mi (Vptr b ofs) (Vptr b' ofs').
Proof.
  intros mi b ofs gv' cm J .
  unfold gv_inject in J.
  simpl in J.
  destruct gv'; simpl in J.
    inv J.

    destruct p; simpl in J. 
    destruct gv'; simpl in J.    
      inv J. 
      inv H2. exists b2. exists (Int.add 31 ofs (Int.repr 31 delta)). exists m.
      split; eauto.

      destruct p. destruct (split gv'). 
      inv J. inv H4.
Qed.

Lemma defined_gv_dec : forall gv, defined_gv gv \/ ~ defined_gv gv.
Proof.
  destruct gv; simpl; auto.
    destruct p; simpl; auto.
    destruct v; simpl; try solve [left; congruence].
      right. intro J. contradict J; auto.
Qed.      

Lemma defined_gvs_dec : forall gvs, defined_gvs gvs \/ ~ defined_gvs gvs.
Proof.
  induction gvs; simpl; auto.
    destruct IHgvs as [IHgvs | IHgvs].
      destruct (@defined_gv_dec a) as [J | J]; auto.
        right. intros [J1 J2]. congruence.
      right. intros [J1 J2]. congruence.
Qed.

Lemma memory_chuck_dec : forall (mc1 mc2:AST.memory_chunk), 
  mc1 = mc2 \/ mc1 <> mc2.
Proof.
  destruct mc1; destruct mc2; try solve [auto | right; congruence].
    destruct (eq_nat_dec n n0); auto.
      right. intros J. inv J. auto.
Qed.

Lemma chunk_matched_dec : forall gv1 gv2, 
  chunk_matched gv1 gv2 \/ ~ chunk_matched gv1 gv2.
Proof.
  induction gv1; destruct gv2.
    left. apply chunk_matched_nil_refl.
    right. intro J. apply chunk_matched_nil_inv in J. inv J.

    right. intro J. apply chunk_matched_nil_inv' in J. inv J.
    destruct a. destruct p.
    destruct (@memory_chuck_dec m m0) as [J | J]; subst.
      destruct (@IHgv1 gv2) as [J' | J'].
        left. apply chunk_matched_cons_intro; auto.
        right. intro J. apply chunk_matched_cons_inv in J.
          destruct J as [gv2' [v1 [m1 [v2 [J1 [J2 J3]]]]]].
          inv J3. inv J1. congruence.
      right. intro J1. apply chunk_matched_cons_inv in J1.
        destruct J1 as [gv2' [v1 [m1 [v2 [J1 [J2 J3]]]]]].
        inv J3. inv J1. congruence.
Qed.     

Lemma gv_inject_null_refl : forall mgb mi M1 M2,
  wf_sb_mi mgb mi M1 M2 -> gv_inject mi null null.
Proof.
  intros. inv H. unfold gv_inject. simpl. eauto.
Qed.

Lemma incl_cons : forall A l1 (x:A), incl l1 (x::l1).
Proof.
  intros. intros y J. simpl; auto.
Qed.



(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
