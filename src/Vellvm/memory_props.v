Require Import vellvm.
Require Import memory_sim.
Require Import sflib.

Ltac unfold_blk2GV := unfold blk2GV, ptr2GV, val2GV.

Lemma simpl_blk2GV: forall td mb,
  blk2GV td mb =
  ((Vptr mb (Int.repr 31 0),
    AST.Mint (Size.mul Size.Eight (getPointerSize td) - 1)) :: nil).
Proof.
  intros. unfold_blk2GV. auto.
Qed.

Module MemProps.

(*****************************************************************)
(* We assume blocks smaller than maxb are allocated for globals. *)
Fixpoint wf_global (maxb:Values.block) (gv:GenericValue) : Prop :=
match gv with
| nil => True
| (Vptr b _,_)::gv' => (b <= maxb)%positive /\ wf_global maxb gv'
| _::gv' => wf_global maxb gv'
end.

Fixpoint wf_global_list maxb (gl:GVMap) : Prop :=
match gl with
| nil => True
| (_,gv)::gl' => wf_global maxb gv /\ wf_global_list maxb gl'
end.

(* maxb must be non-negative. *)
Definition wf_globals maxb (gl:GVMap) : Prop :=
(xH <= maxb)%positive /\ wf_global_list maxb gl.

(*****************************************************************)
(* Two values are not aliased if they do not have pointers in the same block. *)
Fixpoint no_alias_with_blk (gvs:GenericValue) (blk:Values.block) : Prop :=
match gvs with
| nil => True
| (Vptr b _,_)::gvs' => b <> blk /\ no_alias_with_blk gvs' blk
| _::gvs' => no_alias_with_blk gvs' blk
end.

Fixpoint no_alias (gvs1 gvs2:GenericValue) : Prop :=
match gvs2 with
| nil => True
| (Vptr b _,_)::gvs2' => no_alias_with_blk gvs1 b /\ no_alias gvs1 gvs2'
| _::gvs2' => no_alias gvs1 gvs2'
end.

(*****************************************************************)
(* bound is the maximal block allocated so far. A pointer is valid if 
   it only uses blocks smaller than bound. *)
Fixpoint valid_ptrs (bound:Values.block) (gvs:GenericValue): Prop :=
match gvs with
| nil => True
| (Vptr blk _,_)::gvs' => (blk < bound)%positive /\ valid_ptrs bound gvs'
| _::gvs' => valid_ptrs bound gvs'
end.

(*****************************************************************)
(* pointers in locals, memory and allocation lists must be valid. *)
Definition wf_lc M lc : Prop :=
forall id0 gvs,
  lookupAL _ lc id0 = Some gvs -> valid_ptrs (Mem.nextblock M) gvs.

Definition wf_Mem maxb (td:targetdata) (M:mem) : Prop :=
(forall gptr ty al gvs,
  mload td M gptr ty al = Some gvs -> valid_ptrs (Mem.nextblock M) gvs) /\
(maxb < Mem.nextblock M)%positive.

(*****************************************************************)
(* Check if gv contains pointers *)
Fixpoint no_embedded_ptrs (gvs:GenericValue): Prop :=
match gvs with
| nil => True
| (Vptr _ _,_)::gvs' => False
| _::gvs' => no_embedded_ptrs gvs'
end.

(*****************************************************************)
Definition encode_decode_ident_prop
  (M:mem) (b:Values.block) (ofs:Z) (chunk:AST.memory_chunk) : Prop :=
forall bs, 
  bs = Mem.getN (size_chunk_nat chunk) ofs (Maps.PMap.get b (Mem.mem_contents M)) ->
  bs = encode_val chunk (decode_val chunk bs).

Fixpoint encode_decode_ident_aux (M:mem) (mc:list AST.memory_chunk) b ofs 
  : Prop :=
match mc with
| nil => True
| c::mc' => encode_decode_ident_prop M b ofs c /\
            encode_decode_ident_aux M mc' b (ofs+size_chunk c)%Z
end.

Definition encode_decode_ident 
  (TD:TargetData) (M:mem) (ptr:mptr) (t:typ) (a:align) : Prop :=
match GV2ptr TD (getPointerSize TD) ptr with
| Some (Vptr b ofs) =>
  match flatten_typ TD t with
  | Some mc => encode_decode_ident_aux M mc b (Int.signed 31 ofs)
  | _ => False
  end
| _ => False
end.

Axiom zeroconst2GV_no_ptr: forall
      TD t g
      (ZCGV: zeroconst2GV TD t = Some g)
  ,
    <<NOPTR: MemProps.no_embedded_ptrs g>>
.

(*****************************************************************)
(* Properties of no_embedded_ptrs. *)
Lemma mc2undefs__no_embedded_ptrs: forall l0, 
  no_embedded_ptrs (mc2undefs l0).
Proof.
  induction l0; simpl; auto.
Qed.

Lemma undef__no_embedded_ptrs: forall g td t1
  (Hc2g : ret g = gundef td t1), no_embedded_ptrs g.
Proof.
  unfold gundef. intros.
  inv_mbind'. simpl. apply mc2undefs__no_embedded_ptrs.
Qed.

Lemma no_embedded_ptrs__no_alias_with_blk: forall b2 gvs1,
  no_embedded_ptrs gvs1 -> no_alias_with_blk gvs1 b2.
Proof.
  induction gvs1 as [|[]]; simpl; intros; auto.
    destruct v; auto. inv H.
Qed.

Lemma no_embedded_ptrs__no_alias: forall gvs1 gvs2,
  no_embedded_ptrs gvs1 -> no_alias gvs1 gvs2.
Proof.
  induction gvs2 as [|[]]; simpl; intros; auto.
    destruct v; auto.
    split; auto using no_embedded_ptrs__no_alias_with_blk.
Qed.

Lemma no_embedded_ptrs__valid_ptrs: forall bd gvs,
  no_embedded_ptrs gvs -> valid_ptrs bd gvs.
Proof.
  induction gvs as [|[]]; simpl; intros; auto.
    destruct v; auto.
      inversion H.
Qed.

Lemma mtrunc_preserves_no_embedded_ptrs: forall td top t1 t2 gv gv',
  mtrunc td top t1 t2 gv = Some gv' -> no_embedded_ptrs gv'.
Proof.
  intros.
  unfold mtrunc in H.
  remember (GV2val td gv) as R.
  destruct R; eauto using undef__no_embedded_ptrs.
  destruct v; eauto using undef__no_embedded_ptrs.
    destruct_typ t1; eauto using undef__no_embedded_ptrs.
      destruct_typ t2; eauto using undef__no_embedded_ptrs.
        inv H. destruct (le_lt_dec wz (s1-1)); simpl; auto.

    destruct_typ t1; eauto using undef__no_embedded_ptrs.
      destruct_typ t2; eauto using undef__no_embedded_ptrs.
      destruct (floating_point_order f1 f0); tinv H.
      destruct f0; inv H; unfold val2GV; simpl; auto; eauto using undef__no_embedded_ptrs.
      eauto using undef__no_embedded_ptrs.

    destruct_typ t1; eauto using undef__no_embedded_ptrs.
      destruct_typ t2; eauto using undef__no_embedded_ptrs.
Qed.

Lemma mext_preserves_no_embedded_ptrs: forall td eop t1 t2 gv gv',
  mext td eop t1 t2 gv = Some gv' -> no_embedded_ptrs gv'.
Proof.
  {
    ii. unfold mext in *.
    des_ifs; eauto using undef__no_embedded_ptrs.
  }
  (* intros. *)
  (* unfold mext in H. *)
  (* remember (GV2val td gv) as R. *)
  (* destruct t1; tinv H. *)
  (*   destruct t2; tinv H. *)
  (*   destruct R; eauto using undef__no_embedded_ptrs. *)
  (*   destruct v; eauto using undef__no_embedded_ptrs. *)
  (*   destruct eop; inv H; simpl; auto. *)

  (*   destruct_typ t2; tinv H. *)
  (*   match goal with *)
  (*     | H : (if ?t then _ else _ ) = _ |- _ => destruct t; tinv H *)
  (*   end. *)
  (*   destruct R; eauto using undef__no_embedded_ptrs. *)
  (*   destruct v; eauto using undef__no_embedded_ptrs. *)
  (*   destruct eop; tinv H; simpl; auto. *)
  (*   destruct f; inv H; unfold val2GV; simpl; auto. *)
Qed.

Lemma nonptr_no_embedded_ptrs: forall v t td,
  (forall b ofs, v <> Vptr b ofs) -> no_embedded_ptrs (val2GV td v t).
Proof.
  intros.
  destruct v; simpl; auto.
    assert (H1:=@H b i0). congruence.
Qed.

Lemma micmp_int_preserves_no_embedded_ptrs: forall td cop gv1 gv2 gv',
  micmp_int td cop gv1 gv2 = Some gv' -> no_embedded_ptrs gv'.
Proof.
  intros.
  unfold micmp_int in H.
  destruct (GV2val td gv1); eauto using undef__no_embedded_ptrs.
  destruct v; eauto using undef__no_embedded_ptrs.
  destruct (GV2val td gv2); eauto using undef__no_embedded_ptrs.
  destruct v; eauto using undef__no_embedded_ptrs.
Opaque Val.cmp Val.cmpu.
  destruct cop; inv H;
    apply nonptr_no_embedded_ptrs;
      try solve [auto | apply cmp_isnt_ptr | apply cmpu_int_isnt_ptr].
Transparent Val.cmp Val.cmpu Val.cmpu_int.
Qed.

Lemma mbop_preserves_no_embedded_ptrs: forall td bop0 sz0 gv1 gv2 gv3,
  mbop td bop0 sz0 gv1 gv2 = Some gv3 -> no_embedded_ptrs gv3.
Proof.
  intros.
  unfold mbop in H.
  destruct (GV2val td gv1); eauto using undef__no_embedded_ptrs.
  destruct v; eauto using undef__no_embedded_ptrs.
  destruct (GV2val td gv2); eauto using undef__no_embedded_ptrs.
  destruct v; eauto using undef__no_embedded_ptrs.
  destruct (eq_nat_dec (wz + 1) (Size.to_nat sz0));
    eauto using undef__no_embedded_ptrs.
  destruct bop0; inv H;
    try apply nonptr_no_embedded_ptrs;
      try solve
        [apply add_isnt_ptr | apply sub_isnt_ptr | apply mul_isnt_ptr |
         apply shl_isnt_ptr | apply shr_isnt_ptr | apply and_isnt_ptr |
         apply or_isnt_ptr | apply xor_isnt_ptr |
         (destruct (eq_nat_dec _ _); subst; eauto using undef__no_embedded_ptrs;
           try match goal with
             | _: context[if ?s then _ else _] |- _ => destruct s end
           ; subst; inv H1; eauto using undef__no_embedded_ptrs
           ; apply nonptr_no_embedded_ptrs; congruence)].
Qed.

Lemma mfbop_preserves_no_embedded_ptrs: forall td fbop0 fp0 gv1 gv2 gv3,
  mfbop td fbop0 fp0 gv1 gv2 = Some gv3 -> no_embedded_ptrs gv3.
Proof.
  intros.
  unfold mfbop in H.
  destruct (GV2val td gv1); eauto using undef__no_embedded_ptrs.
  destruct v; eauto using undef__no_embedded_ptrs.
  destruct (GV2val td gv2); eauto using undef__no_embedded_ptrs.
  destruct v; eauto using undef__no_embedded_ptrs.
  destruct fp0; tinv H; destruct fbop0; inv H; simpl; eauto using undef__no_embedded_ptrs.
  destruct (GV2val td gv2); try destruct v; eauto using undef__no_embedded_ptrs.
  destruct fp0; tinv H; destruct fbop0; inv H; simpl; eauto using undef__no_embedded_ptrs.
Qed.

(*****************************************************************)
(* Inversion *)
Lemma mbitcast_inv: forall t1 t2 gv1 gv2,
  mbitcast t1 gv1 t2 = ret gv2 -> gv1 = gv2.
Proof.
  intros.
  unfold mbitcast in H.
  destruct t1; tinv H.
    destruct t2; inv H; auto.
    destruct t2; inv H; auto.
Qed.

Lemma mcast_inv: forall td cop t1 t2 gv1 gv2,
  mcast td cop t1 t2 gv1 = ret gv2 -> gv2 = gv1 \/ gundef td t2 = ret gv2.
Proof.
  intros.
  unfold mcast in H.
  destruct cop; auto;
    try
    match goal with
    | H : mbitcast _ _ _ = ret _ |- _ => apply mbitcast_inv in H; subst; auto
    end.
Qed.

Lemma GV2ptr_inv: forall g1 td v,
  ret v = GV2ptr td (getPointerSize td) g1 ->
  exists b, exists ofs, exists m, g1 = (Vptr b ofs, m)::nil /\ v = Vptr b ofs.
Proof.
  intros.
  unfold GV2ptr in H.
  destruct g1 as [|[]]; tinv H.
  destruct v0; tinv H.
  destruct g1 as [|[]]; inv H.
  unfold ptr2GV. unfold val2GV. eauto.
Qed.

Lemma mgep_inv: forall td v1 t1 l1 v2,
  ret v2 = mgep td t1 v1 l1 ->
  exists b, exists ofs1, exists ofs2, v1 = Vptr b ofs1 /\ v2 = Vptr b ofs2.
Proof.
  intros.
  unfold mgep in *.
  destruct v1; tinv H.
  destruct l1; tinv H.
  destruct (mgetoffset td (typ_array 0%nat t1) (z :: l1)) as [[]|]; inv H.
  eauto.
Qed.

(*****************************************************************)
(* Properties of no_alias. *)

Lemma no_alias_nil: forall g, no_alias nil g.
Proof.
  induction g; simpl; intros; auto.
    destruct a.
    destruct v; auto.
Qed.

Lemma no_alias_with_blk_split: forall g2 b g1,
  no_alias_with_blk (g1++g2) b ->
  no_alias_with_blk g1 b /\ no_alias_with_blk g2 b.
Proof.
  induction g1 as [|[]]; simpl; intros; auto.
    destruct v; auto.
    destruct H. apply IHg1 in H0. destruct H0. split; auto.
Qed.

Lemma no_alias_split: forall g2 g1 g,
  no_alias (g1++g2) g -> no_alias g1 g /\ no_alias g2 g.
Proof.
  induction g as [|[]]; simpl; intros; auto.
    destruct v; auto.

    destruct H. apply IHg in H0. destruct H0.
    apply no_alias_with_blk_split in H. destruct H.
    repeat split; auto.
Qed.

Lemma ptr_no_alias__no_alias_with_blk : forall b i0 m gvs2,
  no_alias [(Vptr b i0, m)] gvs2 -> no_alias_with_blk gvs2 b.
Proof.
  induction gvs2 as [|[]]; simpl; intros; auto.
    destruct v; auto.
    destruct H. destruct H.
    split; auto.
Qed.

Lemma no_alias_sym: forall gvs2 gvs1, no_alias gvs1 gvs2 -> no_alias gvs2 gvs1.
Proof.
  induction gvs1 as [|[]]; simpl; intros; auto.
    simpl_env in H.
    apply no_alias_split in H.
    destruct H as [H1 H2].
    destruct v; auto.
    split; auto.
      apply ptr_no_alias__no_alias_with_blk in H1; auto.
Qed.

(*****************************************************************)
Lemma uninits_valid_ptrs: forall bd n, valid_ptrs bd (uninits n).
Proof.
  intros.
  induction n; simpl; auto.
Qed.

Lemma valid_ptrs_app: forall bd g2 g1,
  valid_ptrs bd g1 -> valid_ptrs bd g2 -> valid_ptrs bd (g1++g2).
Proof.
  induction g1 as [|[]]; simpl; intros; auto.
    destruct v; auto.
    destruct H.
    split; auto.
Qed.

Lemma mtrunc_preserves_valid_ptrs: forall td top t1 t2 gv gv' bd,
  mtrunc td top t1 t2 gv = Some gv' -> valid_ptrs bd gv'.
Proof.
  intros.
  apply no_embedded_ptrs__valid_ptrs.
  apply mtrunc_preserves_no_embedded_ptrs in H; auto.
Qed.

Lemma mext_preserves_valid_ptrs: forall td eop t1 t2 gv gv' bd,
  mext td eop t1 t2 gv = Some gv' -> valid_ptrs bd gv'.
Proof.
  intros.
  apply no_embedded_ptrs__valid_ptrs.
  apply mext_preserves_no_embedded_ptrs in H; auto.
Qed.

Lemma mc2undefs_valid_ptrs: forall blk l0, valid_ptrs blk (mc2undefs l0).
Proof. induction l0; simpl; auto. Qed.

Lemma undef_valid_ptrs: forall g td t1 blk
  (Hc2g : ret g = gundef td t1), valid_ptrs blk g.
Proof.
  unfold gundef. intros.
  inv_mbind'. simpl. apply mc2undefs_valid_ptrs.
Qed.

Lemma mcast_preserves_valid_ptrs: forall td cop t1 t2 gv gv' bd,
  mcast td cop t1 t2 gv = Some gv' -> valid_ptrs bd gv -> valid_ptrs bd gv'.
Proof.
  intros.
  apply mcast_inv in H.
  destruct H as [H | H]; subst; eauto using undef_valid_ptrs.
Qed.

Lemma GV2ptr_preserves_valid_ptrs: forall bd g1 td v,
  valid_ptrs bd g1 ->
  ret v = GV2ptr td (getPointerSize td) g1 ->
  valid_ptrs bd (ptr2GV td v).
Proof.
  intros. apply GV2ptr_inv in H0. destruct H0 as [b [ofs [m [J1 J2]]]]; subst.
  unfold ptr2GV. unfold val2GV. simpl in *. auto.
Qed.

Lemma mgep_preserves_valid_ptrs: forall td v t1 l1 v0 bd,
  valid_ptrs bd (ptr2GV td v) ->
  ret v0 = mgep td t1 v l1 ->
  valid_ptrs bd (ptr2GV td v0).
Proof.
  intros.
  apply mgep_inv in H0. destruct H0 as [b [ofs1 [ofs2 [J1 J2]]]]; subst.
  simpl in *. auto.
Qed.

Lemma micmp_int_preserves_valid_ptrs: forall td cop gv1 gv2 bd gv',
  micmp_int td cop gv1 gv2 = Some gv' -> valid_ptrs bd gv'.
Proof.
  intros.
  apply no_embedded_ptrs__valid_ptrs.
  apply micmp_int_preserves_no_embedded_ptrs in H; auto.
Qed.

Lemma micmp_preserves_valid_ptrs: forall td cop t1 gv1 gv2 gv' bd,
  micmp td cop t1 gv1 gv2 = Some gv' -> valid_ptrs bd gv'.
Proof.
  intros.
  unfold micmp in H.
  destruct t1; tinv H; eauto using undef_valid_ptrs.
    eapply micmp_int_preserves_valid_ptrs; eauto.
Qed.

Lemma cmpf_non_ptr
      cmp v1 v2
  :
    forall b ofs, Val.cmpf cmp v1 v2 <> Vptr b ofs
.
Proof.
  i. compute; des_ifs.
Qed.

Lemma mfcmp_preserves_valid_ptrs: forall td fop fp gv1 gv2 gv' bd,
  mfcmp td fop fp gv1 gv2 = Some gv' -> valid_ptrs bd gv'.
Proof.
  intros.
  unfold mfcmp in H.
  destruct (GV2val td gv1); eauto using undef_valid_ptrs.
  destruct v; eauto using undef_valid_ptrs.
  destruct (GV2val td gv2); eauto using undef_valid_ptrs.
  destruct v; eauto using undef_valid_ptrs.
  apply no_embedded_ptrs__valid_ptrs.
  des_ifs; try (by (eapply nonptr_no_embedded_ptrs; eapply cmpf_non_ptr));
    try (by compute in H; des_ifs).
  (* destruct fp; tinv H; *)
  (*   destruct fop; inv H; apply nonptr_no_embedded_ptrs; *)
  (*     try solve [auto | apply Vfalse_isnt_ptr | apply Vtrue_isnt_ptr | *)
  (*                apply val_of_bool_isnt_ptr]. *)
Qed.

Lemma splitGenericValue_preserves_valid_ptrs: forall bd g0 z0 g1 g2,
  valid_ptrs bd g0 ->
  ret (g1, g2) = splitGenericValue g0 z0 ->
  valid_ptrs bd g1 /\ valid_ptrs bd g2.
Proof.
  induction g0 as [|[]]; simpl; intros.
    destruct (zeq z0 0).
      inv H0. auto.
      destruct (zlt z0 0); tinv H0.

    destruct (zeq z0 0).
      inv H0. simpl. auto.

      destruct (zlt z0 0); tinv H0.
      inv_mbind'. inv H2.
      simpl_env in H.
      assert (valid_ptrs bd [(v,m)] /\ valid_ptrs bd g0) as J.
        simpl.
        destruct v; auto.
          destruct H; auto.
      destruct J as [J1 J2].
      apply IHg0 in HeqR; auto.
      destruct HeqR.
      split; auto.
        simpl_env.
        apply valid_ptrs_app; auto.
Qed.

Lemma extractGenericValue_preserves_valid_ptrs: forall td g1 t1 g0 bd l0,
  valid_ptrs bd g0 -> ret g1 = extractGenericValue td t1 g0 l0 ->
  valid_ptrs bd g1.
Proof.
  intros.
  unfold extractGenericValue in *.
  inv_mbind'.
  remember (mget td g0 z t) as R.
  destruct R; eauto using undef_valid_ptrs.
  inv H1.
  unfold mget in HeqR1.
  destruct (getTypeStoreSize td t); tinv HeqR1.
  simpl in HeqR1.
  inv_mbind'. inv H2.
  eapply splitGenericValue_preserves_valid_ptrs in HeqR2; eauto.
  destruct HeqR2.
  eapply splitGenericValue_preserves_valid_ptrs in HeqR1; eauto.
  destruct HeqR1; auto.
  destruct_if; eauto.
Qed.

Lemma insertGenericValue_preserves_valid_ptrs: forall td t1 t2 g0 g1 g2 l0 bd,
  valid_ptrs bd g0 -> valid_ptrs bd g1 ->
  ret g2 = insertGenericValue td t1 g0 l0 t2 g1 -> valid_ptrs bd g2.
Proof.
  intros.
  unfold insertGenericValue in *.
  inv_mbind'.
  remember (mset td g0 z t2 g1) as R.
  destruct R; eauto using undef_valid_ptrs.
  inv H2.
  unfold mset in HeqR1.
  destruct (getTypeStoreSize td t2); tinv HeqR1.
  simpl in HeqR1.
  destruct (n =n= length g1); tinv HeqR1.
  inv_mbind'. inv H3.
  eapply splitGenericValue_preserves_valid_ptrs in HeqR2; eauto.
  destruct HeqR2.
  eapply splitGenericValue_preserves_valid_ptrs in HeqR1; eauto.
  destruct HeqR1.
  destruct_if; eauto.
  repeat apply valid_ptrs_app; auto.
Qed.

Lemma mbop_preserves_valid_ptrs: forall td bop0 sz0 gv1 gv2 gv3 bd,
  mbop td bop0 sz0 gv1 gv2 = Some gv3 ->
  valid_ptrs bd gv3.
Proof.
  intros.
  apply no_embedded_ptrs__valid_ptrs.
  apply mbop_preserves_no_embedded_ptrs in H; auto.
Qed.

Lemma mfbop_preserves_valid_ptrs: forall td fbop0 fp0 gv1 gv2 gv3 bd,
  mfbop td fbop0 fp0 gv1 gv2 = Some gv3 -> valid_ptrs bd gv3.
Proof.
  intros.
  apply no_embedded_ptrs__valid_ptrs.
  apply mfbop_preserves_no_embedded_ptrs in H; auto.
Qed.

Lemma valid_ptrs__trans: forall bound1 bound2 gv,
  valid_ptrs bound1 gv -> (bound1 <= bound2)%positive -> valid_ptrs bound2 gv.
Proof.
  induction gv as [|[]]; simpl; intros; auto.
    destruct v; auto.
      destruct H. split; auto. eapply Pos.lt_le_trans; eauto.
Qed.

Lemma in_valid_ptrs: forall bd m b ofs gvs,
  valid_ptrs bd gvs -> In (Vptr b ofs, m) gvs -> (b < bd)%positive.
Proof.
  induction gvs as [|[]]; simpl; intros.
    inv H0.

    destruct H0 as [H0 | H0].
      inv H0.
      destruct H; auto.

      destruct v; eauto.
      destruct H; eauto.
Qed.

Lemma valid_ptrs_overlap: forall gvs1 gvs2 bd gvs0,
  valid_ptrs bd gvs1 ->
  valid_ptrs bd gvs2 ->
  (forall (v : val) (m : AST.memory_chunk),
       In (v, m) gvs0 ->
       In (v, m) gvs2 \/
       (forall (b0 : Values.block) (ofs0 : int32),
        v = Vptr b0 ofs0 -> In (v, m) gvs1)) ->
  valid_ptrs bd gvs0.
Proof.
  induction gvs0 as [|[]]; simpl; intros; auto.
    destruct v; eauto.
    edestruct H1 as [J1 | J1]; eauto.
      split; eauto.
      eapply in_valid_ptrs in J1; eauto.

      split; eauto.
      eapply in_valid_ptrs in H; eauto.
Qed.

Lemma valid_ptrs__no_alias__fresh_ptr: forall bound TD mb (Hbd: (bound <= mb)%positive)
  gvs, valid_ptrs bound gvs ->
  no_alias gvs (blk2GV TD mb).
Proof.
Local Opaque no_alias.
  induction gvs as [|[]]; simpl; intros.
    apply no_alias_nil.

    destruct v; auto.
    destruct H.
    apply IHgvs in H0. rewrite simpl_blk2GV in *. simpl in *.
    destruct H0.
    repeat split; auto.
      intro J. subst. contradict H; apply Pos.le_nlt; auto.
Transparent no_alias.
Qed.

Lemma undefs_valid_ptrs: forall bd gvs1
  (Hc2g : forall v m, In (v, m) gvs1 -> v = Vundef),
  valid_ptrs bd gvs1.
Proof.
  induction gvs1 as [|[]]; simpl; intros; auto.
    destruct v; eauto.
    assert ((Vptr b i0, m) = (Vptr b i0, m) \/ In (Vptr b i0, m) gvs1) as J.
      auto.
    apply Hc2g in J. congruence.
Qed.

Lemma updateAddAL__wf_lc: forall gv3 Mem0 lc id0
  (Hwfgv: valid_ptrs (Mem.nextblock Mem0) gv3) (Hwflc: wf_lc Mem0 lc),
  wf_lc Mem0 (updateAddAL GenericValue lc id0 gv3).
Proof.
  intros. unfold wf_lc in *. intros.
  destruct (id_dec id0 id1); subst.
    rewrite lookupAL_updateAddAL_eq in H. inv H. eauto.

    rewrite <- lookupAL_updateAddAL_neq in H; auto.
    eapply Hwflc; eauto.
Qed.

(*****************************************************************)
(* Properties of free. *)
Lemma nextblock_free: forall TD M gv M',
  free TD M gv = ret M' -> Mem.nextblock M = Mem.nextblock M'.
Proof.
  intros.
  apply free_inv in H.
  destruct H as [blk' [ofs' [hi [lo [J4 [J5 [J6 J7]]]]]]].
  apply Mem.nextblock_free in J7. auto.
Qed.

Lemma free_preserves_mload_aux_inv: forall blk lo hi b Mem Mem'
  (Hfree:Mem.free Mem blk lo hi = ret Mem') mc ofs gvsa,
  mload_aux Mem' mc b ofs = ret gvsa ->
  mload_aux Mem mc b ofs = ret gvsa.
Proof.
  induction mc; simpl; intros; auto.
    inv_mbind'. symmetry in HeqR0.
    apply IHmc in HeqR0.
    rewrite HeqR0.
    erewrite <- Mem.load_free; eauto.
      rewrite <- HeqR. auto.
      eapply Mem.load_free'; eauto.
Qed.

Lemma free_preserves_mload_inv: forall TD Mem' gptr ty al gvsa Mem mptr0
  (H1 : mload TD Mem' gptr ty al = ret gvsa)
  (H2 : free TD Mem mptr0 = ret Mem'),
  mload TD Mem gptr ty al = ret gvsa.
Proof.
  intros.
  apply mload_inv in H1.
  destruct H1 as [b [ofs [m [mc [J1 [J2 J3]]]]]]; subst.
  unfold mload. simpl. rewrite J2.
  apply free_inv in H2.
  destruct H2 as [blk' [ofs' [hi [lo [J4 [J5 [J6 J7]]]]]]].
  eapply free_preserves_mload_aux_inv; eauto.
Qed.

Lemma free_preserves_wf_lc: forall TD Mem' Mem mptr0
  (H2 : free TD Mem mptr0 = ret Mem') lc
  (Hwf: wf_lc Mem lc),
  wf_lc Mem' lc.
Proof.
  unfold wf_lc.
  intros.
  apply Hwf in H.
  apply free_inv in H2.
  destruct H2 as [blk' [ofs' [hi [lo [J4 [J5 [J6 J7]]]]]]].
  erewrite Mem.nextblock_free; eauto.
Qed.

Lemma free_preserves_mload_aux: forall Mem blk lo hi Mem' b
  (Hfree: Mem.free Mem blk lo hi = ret Mem') (Hneq: blk <> b) mc ofs gv,
  mload_aux Mem mc b ofs = ret gv ->
  mload_aux Mem' mc b ofs = ret gv.
Proof.
  induction mc; simpl; intros; auto.
    inv_mbind'. symmetry in HeqR0.
    apply IHmc in HeqR0.
    rewrite HeqR0.
    erewrite Mem.load_free; eauto.
      rewrite <- HeqR. auto.
Qed.

Lemma free_preserves_mload: forall TD Mem Mem' t al gv gptr gvsa
  (H0 : no_alias gptr gvsa)
  (H1 : free TD Mem gptr = ret Mem')
  (H2 : mload TD Mem gvsa t al = ret gv),
  mload TD Mem' gvsa t al = ret gv.
Proof.
  intros.
  apply free_inv in H1.
  destruct H1 as [blk [ofs [hi [lo [J4 [J5 [J6 J7]]]]]]].
  apply mload_inv in H2.
  destruct H2 as [b [ofs' [m [mc [J1 [J2 J3]]]]]]; subst.
  unfold mload. simpl. rewrite J2.
  symmetry in J4.
  apply GV2ptr_inv in J4.
  destruct J4 as [b1 [ofs1 [m1 [J8 J9]]]]; subst.
  inv J9.
  simpl in H0. destruct H0. destruct H. clear H1 H0.
  eapply free_preserves_mload_aux in J3; eauto.
Qed.

Lemma free_preserves_wf_Mem : forall maxb TD M M' mptr0
  (Hfree: free TD M mptr0 = ret M')
  (Hwf: wf_Mem maxb TD M),
  wf_Mem maxb TD M'.
Proof.
  intros. destruct Hwf as [J1 J2].
  unfold wf_Mem.
  erewrite <- nextblock_free; eauto.
  split; auto.
    intros.
    eapply free_preserves_mload_inv in H; eauto.
Qed.


(*****************************************************************)
(* Properties of store. *)

Axiom mstore_mload_same: forall
      td Mem mp2 typ1 gv1 align1 Mem'
      (MSTORE: mstore td Mem mp2 typ1 gv1 align1 = ret Mem'),
    <<MLOAD: mload td Mem' mp2 typ1 align1 = ret gv1>>
.

Axiom mstore_aux_never_produce_new_ptr: forall
      TD mem0 mem1
      nptr ch val b o
      (MEM_NOALIAS: forall ptr ty a gv,
          mload TD mem0 ptr ty a = Some gv ->
          MemProps.no_alias nptr gv)
      (STORE_AUX: mstore_aux mem0 ch val b o = Some mem1)
      (NOALIAS: MemProps.no_alias nptr val)
  ,
    forall ptr ty a gv,
    mload TD mem1 ptr ty a = Some gv ->
    MemProps.no_alias nptr gv
.


Lemma store_preserves_mload_aux_inv: forall b1 b2 v2 m2 Mem' Mem ofs2
  (Hst: Mem.store m2 Mem b2 ofs2 v2 = ret Mem') mc ofs1 gvs0,
  mload_aux Mem' mc b1 ofs1 = ret gvs0 ->
  exists gvs2 : GenericValue,
     mload_aux Mem mc b1 ofs1 = ret gvs2 /\
     (forall v m,
      In (v, m) gvs0 -> In (v, m) gvs2 \/
      (forall b0 ofs0, v = Vptr b0 ofs0 -> v = v2 /\ m = m2)).
Proof.
  induction mc; simpl; intros.
    inv H.
    exists nil.
    split; auto.
      intros. inv H.

    inv_mbind'. symmetry in HeqR0.
    apply IHmc in HeqR0.
    destruct HeqR0 as [gvs2 [J1 J2]].
    rewrite J1.
    eapply Mem.store_preserves_load_inv in Hst; eauto.
    destruct Hst as [v1' [J3 J4]].
    rewrite J3.
    exists ((v1',a)::gvs2).
    split; auto.
      intros. simpl.
      simpl in H. destruct H as [H | H]; subst.
        inv H.
        destruct J4 as [J4 | J4]; subst; auto.

        apply J2 in H.
        destruct H as [H | H]; auto.
Qed.

Lemma mstore_aux_preserves_mload_aux_inv: forall mc b1 ofs1 gvs0 b2 mc' gvs1 Mem' Mem ofs2,
  mload_aux Mem' mc b1 ofs1 = ret gvs0 ->
  mstore_aux Mem mc' gvs1 b2 ofs2 = ret Mem' ->
  exists gvs2 : GenericValue,
     mload_aux Mem mc b1 ofs1 = ret gvs2 /\
     (forall v m,
      In (v, m) gvs0 -> In (v, m) gvs2 \/
      (forall b0 ofs0, v = Vptr b0 ofs0 -> In (v, m) gvs1)).
Proof.
  induction mc'; destruct gvs1; intros Mem' Mem ofs2 Hload Hstore; inv Hstore.
    exists gvs0. split; auto.

    inv_mbind'.
    destruct (AST.memory_chunk_eq a m); inv H0.
    destruct (has_chunk_eq v m); inv H1.
    inv_mbind'.
    apply IHmc' in H1; auto.
    destruct H1 as [gvs2 [J1 J2]].
    symmetry in HeqR.
    eapply store_preserves_mload_aux_inv in HeqR; eauto.
    destruct HeqR as [gvs3 [J3 J4]].
    exists gvs3.
    split; auto.
    intros.
    apply J2 in H.
    destruct H as [H | H]; subst;
      try solve [right; intros; subst; right; eauto].
    apply J4 in H.
    destruct H as [H | H]; subst; auto.
      right. intros. apply H in H0. destruct H0; subst; left; auto.
Qed.

Ltac destruct_ldst :=
match goal with
| H1 : mload _ _ _ _ _ = ret _,
  H2 : mstore _ _ _ _ _ _ = ret _ |- _ =>
  apply store_inv in H2;
  destruct H2 as [b [ofs [mc' [J6 [J5 J4]]]]];
  apply mload_inv in H1;
  destruct H1 as [b1 [ofs1 [m1 [mc [J1 [J2 J3]]]]]]; subst;
  unfold mload; simpl; rewrite J2;
  symmetry in J6; apply GV2ptr_inv in J6;
  destruct J6 as [b2 [ofs2 [m2 [J7 J8]]]]; subst; inv J8
end.

Lemma mstore_preserves_mload_inv: forall TD Mem' gptr ty al gvs0 Mem gvs1 t
  mp2 (H1 : mload TD Mem' gptr ty al = ret gvs0) align
  (H2 : mstore TD Mem mp2 t gvs1 align = Some Mem'),
  exists gvs2, mload TD Mem gptr ty al = ret gvs2 /\
     (forall v m,
      In (v, m) gvs0 -> In (v, m) gvs2 \/
      (forall b0 ofs0, v = Vptr b0 ofs0 -> In (v, m) gvs1)).
Proof.
  intros. destruct_ldst.
  eapply mstore_aux_preserves_mload_aux_inv; eauto.
Qed.

Lemma store_preserves_mload: forall b1 b2 v2 m2 Mem' Mem ofs2
  (Hneq: b1 <> b2) (Hst: Mem.store m2 Mem b2 ofs2 v2 = ret Mem') mc ofs1 gvs0,
  mload_aux Mem mc b1 ofs1 = ret gvs0 ->
  mload_aux Mem' mc b1 ofs1 = ret gvs0.
Proof.
  induction mc; simpl; intros; auto.
    inv_mbind'. symmetry in HeqR0.
    apply IHmc in HeqR0.
    rewrite HeqR0.
    erewrite Mem.load_store_other; eauto.
    rewrite <- HeqR. auto.
Qed.

Lemma mstore_aux_preserves_mload_aux: forall mc b1 ofs1 gvs0 b2
  (Hneq: b1 <> b2) mc' gvs1 Mem' Mem ofs2,
  mload_aux Mem mc b1 ofs1 = ret gvs0 ->
  mstore_aux Mem mc' gvs1 b2 ofs2 = ret Mem' ->
  mload_aux Mem' mc b1 ofs1 = ret gvs0.
Proof.
  induction mc'; destruct gvs1; intros Mem' Mem ofs2 Hload Hstore; inv Hstore; auto.
  inv_mbind'.
  destruct (AST.memory_chunk_eq a m); inv H0.
    destruct (has_chunk_eq v m); inv H1.
  inv_mbind'.
  apply IHmc' in H1; auto.
  eapply store_preserves_mload; eauto.
Qed.

Lemma mstore_preserves_mload: forall TD Mem' gptr ty al gvs0 Mem gv1 t
  mp2 (H1 : mload TD Mem gptr ty al = ret gvs0) align
  (H2 : mstore TD Mem mp2 t gv1 align = Some Mem')
  (Hna: no_alias mp2 gptr),
  mload TD Mem' gptr ty al = ret gvs0.
Proof.
  intros. destruct_ldst.
  simpl in Hna. destruct Hna as [[Hna _] _ ].
  eapply mstore_aux_preserves_mload_aux; eauto.
Qed.



Lemma nextblock_mstore_aux: forall b mc gvs M ofs M',
  mstore_aux M mc gvs b ofs = ret M' ->
  Mem.nextblock M = Mem.nextblock M'.
Proof.
  induction mc; destruct gvs; intros M ofs M' Hstore; inv Hstore; auto.
    inv_mbind'.
    destruct (AST.memory_chunk_eq a m); inv H0.
    destruct (has_chunk_eq v m); inv H1.
    inv_mbind'.
    apply IHmc in H1.
    symmetry in HeqR.
    apply Mem.nextblock_store in HeqR.
    rewrite <- HeqR. auto.
Qed.

Lemma nextblock_mstore: forall TD M gv1 M' mp2 t align0,
  mstore TD M mp2 t gv1 align0 = ret M' ->
  Mem.nextblock M = Mem.nextblock M'.
Proof.
  intros.
  apply store_inv in H.
  destruct H as [blk' [ofs' [mc [J1 [J2 J3]]]]].
  apply nextblock_mstore_aux in J3; auto.
Qed.

Lemma mstore_preserves_wf_lc: forall TD M' M mp2 t gv1 align
  (Hst: mstore TD M mp2 t gv1 align = Some M') lc
  (Hwf: wf_lc M lc),
  wf_lc M' lc.
Proof.
  unfold wf_lc.
  intros.
  apply Hwf in H.
  erewrite <- nextblock_mstore; eauto.
Qed.

Lemma store_preserves_mload_inv': forall b1 b2 v2 m2 Mem' Mem ofs2
  (Hneq: b1 <> b2) (Hst: Mem.store m2 Mem b2 ofs2 v2 = ret Mem') mc ofs1 gvs0,
  mload_aux Mem' mc b1 ofs1 = ret gvs0 ->
  mload_aux Mem mc b1 ofs1 = ret gvs0.
Proof.
  induction mc; simpl; intros; auto.
    inv_mbind'. symmetry in HeqR0.
    apply IHmc in HeqR0.
    rewrite HeqR0.
    erewrite <- Mem.load_store_other; eauto.
    rewrite <- HeqR. auto.
Qed.

Lemma mstore_aux_preserves_mload_inv_aux': forall mc b1 ofs1 gvs0 b2
  (Hneq: b1 <> b2) mc' gvs1 Mem' Mem ofs2,
  mload_aux Mem' mc b1 ofs1 = ret gvs0 ->
  mstore_aux Mem mc' gvs1 b2 ofs2 = ret Mem' ->
  mload_aux Mem mc b1 ofs1 = ret gvs0.
Proof.
  induction mc'; destruct gvs1; intros Mem' Mem ofs2 Hload Hstore; inv Hstore; auto.

    inv_mbind'.
    destruct (AST.memory_chunk_eq a m); inv H0.
    destruct (has_chunk_eq v m); inv H1.
    inv_mbind'.
    apply IHmc' in H1; auto.
    eapply store_preserves_mload_inv'; eauto.
Qed.

Lemma mstore_preserves_mload_inv': forall TD Mem' gptr ty al gvs0 Mem gv1 t
  mp2 (H1 : mload TD Mem' gptr ty al = ret gvs0) align
  (H2 : mstore TD Mem mp2 t gv1 align = Some Mem')
  (Hna: no_alias mp2 gptr),
  mload TD Mem gptr ty al = ret gvs0.
Proof.
  intros. destruct_ldst.
  simpl in Hna. destruct Hna as [[Hna _] _ ].
  eapply mstore_aux_preserves_mload_inv_aux'; eauto.
Qed.


Lemma bounds_mstore_aux: forall b mc gvs M ofs M',
  mstore_aux M mc gvs b ofs = ret M' ->
  forall b', Mem.bounds M b' = Mem.bounds M' b'.
Proof.
  induction mc; destruct gvs; intros M ofs M' Hstore b'; inv Hstore; auto.

    inv_mbind'.
    destruct (AST.memory_chunk_eq a m); inv H0.
    destruct (has_chunk_eq v m); inv H1.
    inv_mbind'.
    eapply IHmc in H1; eauto.
    symmetry in HeqR.
    eapply Mem.bounds_store in HeqR; eauto.
    rewrite <- HeqR. eauto.
Qed.

Lemma bounds_mstore: forall TD M gv1 M' mp2 t align0,
  mstore TD M mp2 t gv1 align0 = ret M' ->
  forall b', Mem.bounds M b' = Mem.bounds M' b'.
Proof.
  intros.
  apply store_inv in H.
  destruct H as [blk' [ofs' [mc' [J1 [J2 J3]]]]].
  eapply bounds_mstore_aux in J3; eauto.
Qed.



(*****************************************************************)
(* Properties of alloca. *)
Fixpoint mcs2uninits (mc:list AST.memory_chunk) : GenericValue :=
match mc with
| nil => nil
| c::mc => (Vundef, c)::mcs2uninits mc
end.

Lemma alloc_preserves_mload_aux_inv': forall M M' mb lo hi b
  (Hal : Mem.alloc M lo hi = (M', mb)) mc ofs gvs1
  (H : mload_aux M' mc b ofs = ret gvs1),
  mload_aux M mc b ofs = ret gvs1 /\ b <> mb \/
  gvs1 = mcs2uninits mc /\ b = mb.
Proof.
  induction mc; simpl; intros.
    inv H.
    destruct (peq b mb); subst; auto.

    inv_mbind'.
    symmetry in HeqR.
    assert (J:=HeqR).
    apply Mem.load_valid_access in J.
    eapply Mem.valid_access_alloc_inv in J; eauto.
    symmetry in HeqR0. apply IHmc in HeqR0.
    destruct (eq_block b mb); subst.
      destruct J as [J1 [J2 J3]].
      erewrite Mem.load_alloc_same' in HeqR; eauto.
      inv HeqR.
      destruct HeqR0 as [[J4 J5] | [J4 J5]]; subst;
        try solve [congruence | tauto].

      destruct HeqR0 as [[J4 J5] | [J4 J5]]; subst; try solve [congruence].
      left.
      rewrite J4.
      split; auto.
        apply Mem.valid_access_implies with (p2:=Nonempty) in J; try constructor.
        apply Mem.valid_access_valid_block in J.
        erewrite Mem.load_alloc_unchanged in HeqR; eauto.
        rewrite HeqR. auto.
Qed.

Lemma alloc_drop_preserves_mload_aux_inv': forall M M' mb lo hi b
  (Hal : Mem.alloc M lo hi = (M', mb)) mc ofs gvs1
  M''
  (DROP: Mem.drop_perm M' mb lo hi Writable = ret M'')
  (H : mload_aux M'' mc b ofs = ret gvs1),
  mload_aux M mc b ofs = ret gvs1 /\ b <> mb \/
  gvs1 = mcs2uninits mc /\ b = mb.
Proof.
  i.
  ginduction mc; ii; ss.
  - inv H.
    destruct (eq_block b mb).
    + right. split; ss.
    + left. split; ss.
  - destruct (Mem.load a M'' b ofs) eqn:T; ss.
    destruct (mload_aux M'' mc b (ofs + size_chunk a)) eqn:T2; ss.
    clarify.
    hexploit Mem.load_drop; try eassumption.
    { right. right. right. econs. }
    intro EQ.
    rewrite EQ in *.
    exploit Mem.load_valid_access; eauto; intro VALID; des.
    eapply Mem.valid_access_alloc_inv in VALID; eauto.
    eapply IHmc in T2; eauto.

    destruct (eq_block b mb).
    + clarify. right. split; ss.
      des_ifs. des; ss.
      erewrite Mem.load_alloc_same' in T; eauto. clarify.
    + left. split; ss.
      eapply Mem.valid_access_implies with (p2:=Nonempty) in VALID; eauto; [|econs].
      apply Mem.valid_access_valid_block in VALID.
      eapply Mem.load_alloc_unchanged in Hal; eauto.
      rewrite <- Hal. rewrite T.
      des; ss. rewrite T2. ss.
Qed.


Lemma mcs2uninits_spec: forall v m mc, In (v, m) (mcs2uninits mc) -> v = Vundef.
Proof.
  induction mc; simpl; intros.
    inv H.

    destruct H as [H | H]; auto.
      inv H; auto.
Qed.

Lemma alloc_preserves_mload_aux_inv: forall M M' mb lo hi b
  (Hal : Mem.alloc M lo hi = (M', mb)) mc ofs gvs1
  (H : mload_aux M' mc b ofs = ret gvs1),
  mload_aux M mc b ofs = ret gvs1 /\ b <> mb \/
  (forall v m, In (v, m) gvs1 -> v = Vundef) /\ b = mb.
Proof.
  intros.
  eapply alloc_preserves_mload_aux_inv' in H; eauto.
  destruct H as [H | H]; auto.
  right.
  destruct H; subst.
  split; auto.
    intros.
    eapply mcs2uninits_spec; eauto.
Qed.

Lemma alloc_drop_preserves_mload_aux_inv: forall M M' mb lo hi b
  (Hal : Mem.alloc M lo hi = (M', mb)) mc ofs gvs1
  M''
  (DROP: Mem.drop_perm M' mb lo hi Writable = ret M'')
  (H : mload_aux M'' mc b ofs = ret gvs1),
  mload_aux M mc b ofs = ret gvs1 /\ b <> mb \/
  (forall v m, In (v, m) gvs1 -> v = Vundef) /\ b = mb.
Proof.
  intros.
  eapply alloc_drop_preserves_mload_aux_inv' in H; eauto.
  destruct H as [H | H]; auto.
  right.
  destruct H; subst.
  split; auto.
    intros.
    eapply mcs2uninits_spec; eauto.
Qed.

Ltac destruct_allocld :=
match goal with
| Hal : malloc _ _ _ _ _ = ret _,
  H : mload _ _ _ _ _ = ret _ |- _ =>
  apply mload_inv in H;
  destruct H as [b [ofs [m [mc [J1 [J2 J3]]]]]]; subst;
  apply malloc_inv in Hal;
  unfold mload; simpl; rewrite J2
end.
(*   apply malloc_inv in Hal; *)
(*   destruct Hal as [n [J4 [J5 J6]]]; *)
(*   unfold mload; simpl; rewrite J2 *)

Lemma alloca_preserves_mload_inv: forall TD M M' mb align0 gn tsz
  (Hal : alloca TD M tsz gn align0 = ret (M', mb))
  gptr gvs1 ty al
  (H : mload TD M' gptr ty al = ret gvs1),
  mload TD M gptr ty al = ret gvs1 /\ no_alias_with_blk gptr mb \/
  (forall v m, In (v, m) gvs1 -> v = Vundef) /\ ~ no_alias_with_blk gptr mb.
Proof.
  ii. unfold alloca in *.
  remember (match GV2int TD Size.ThirtyTwo gn with
            | ret n => Size.to_Z tsz * n
            | merror => 0
            end) as hi. clear Heqhi.
  des_ifs. unfold Datatypes.option_map, flip in *.
  des_ifs.
  unfold mload in *. des_ifs.
  exploit alloc_drop_preserves_mload_aux_inv; try exact H; eauto; []; i.
  unfold GV2ptr in *. des_ifs.
  des.
  - left. split; ss.
  - right. split; ss.
    ii. des. ss.
Qed.

Lemma nextblock_malloc: forall TD M tsz gn M' align0 mb,
  malloc TD M tsz gn align0 = ret (M', mb) ->
  (Mem.nextblock M + 1)%positive = Mem.nextblock M'.
Proof.
  intros.
  apply malloc_inv in H.
  apply Mem.nextblock_alloc in H.
  rewrite H. rewrite Pplus_one_succ_r; auto.
Qed.

Lemma nextblock_alloca: forall TD M tsz gn M' align0 mb,
  alloca TD M tsz gn align0 = ret (M', mb) ->
  (Mem.nextblock M + 1)%positive = Mem.nextblock M'.
Proof.
  intros.
  apply alloca_inv in H.
  unfold Datatypes.option_map, flip in *. des.
  des_ifs; apply Mem.nextblock_alloc in Heq; apply Mem.nextblock_drop in Heq0;
    rewrite Heq0; rewrite Heq; rewrite Pplus_one_succ_r; auto.
Qed.

Lemma malloc_result: forall TD M tsz gn M' align0 mb,
  malloc TD M tsz gn align0 = ret (M', mb) ->
  mb = Mem.nextblock M.
Proof.
  intros.
  apply malloc_inv in H.
  apply Mem.alloc_result in H; auto.
  (* destruct H as [n [J1 [J2 J3]]]. *)
  (* apply Mem.alloc_result in J3; auto. *)
Qed.

Lemma alloca_result: forall TD M tsz gn M' align0 mb,
  alloca TD M tsz gn align0 = ret (M', mb) ->
  mb = Mem.nextblock M.
Proof.
  intros.
  apply alloca_inv in H.
  unfold Datatypes.option_map, flip in *. des.
  des_ifs; apply Mem.alloc_result in Heq; ss.
  (* destruct H as [n [J1 [J2 J3]]]. *)
  (* apply Mem.alloc_result in J3; auto. *)
Qed.


Lemma alloc_drop_preserves_mload_aux: forall M M' mb lo hi b
  (Hal : Mem.alloc M lo hi = (M', mb)) mc ofs gvs1
  M''
  (DROP: Mem.drop_perm M' mb lo hi Writable = ret M'')
  (H : mload_aux M mc b ofs = ret gvs1),
  mload_aux M'' mc b ofs = ret gvs1.
Proof.
  i. ginduction mc; ii; ss.
  destruct (Mem.load a M b ofs) eqn:LOAD; ss.
  destruct (mload_aux M mc b (ofs + size_chunk a)) eqn:LOAD_AUX; ss.
  clarify.
  exploit Mem.load_drop; try eassumption.
  { right. right. right. econs. }
  intro EQ. rewrite EQ in *.
  exploit Mem.load_alloc_other; eauto; []; intro LOAD1; des.
  rewrite LOAD1.
  exploit IHmc; eauto; []; intro MLOAD_AUX1; des.
  rewrite MLOAD_AUX1. ss.
Qed.

Ltac u_alloca := unfold alloca, Datatypes.option_map, flip in *.

Lemma alloca_preserves_wf_Mem : forall maxb TD M tsz gn align0 M' mb
  (Hmlc: alloca TD M tsz gn align0 = ret (M', mb))
  (Hwf: wf_Mem maxb TD M),
  wf_Mem maxb TD M'.
Proof.
  eauto.
  intros. destruct Hwf as [J1 J2].
  assert ((Mem.nextblock M + 1)%positive = Mem.nextblock M') as EQ.
    eapply nextblock_alloca; eauto.
  split.
    rewrite <- EQ.
    intros.
    eapply alloca_preserves_mload_inv in H; eauto.
    destruct H as [[G _]| [G _]]; subst; eauto.
      apply J1 in G. eapply valid_ptrs__trans; eauto. rewrite <- Pplus_one_succ_r; apply Ple_succ.
      eapply undefs_valid_ptrs; eauto.

    eapply Plt_trans; eauto. rewrite <- EQ. rewrite <- Pplus_one_succ_r; apply Plt_succ.
Qed.

Lemma alloca_preserves_wf_lc_in_tail: forall TD M M' tsz gn align0 mb lc
  (Halloca: alloca TD M tsz gn align0 = ret (M', mb))
  (Hwf: wf_lc M lc), wf_lc M' lc.
Proof.
  unfold wf_lc.
  intros. apply Hwf in H.
  eapply valid_ptrs__trans; eauto.
  erewrite <- nextblock_alloca with (M':=M'); eauto.
  rewrite <- Pplus_one_succ_r; apply Ple_succ.
Qed.

(* The current design of malloc does not check alignment! It must ensure that 
   mload is successful at the allocated address. To do so, malloc must ensure 
   all subcomponents in an aggregated object are well-aligned! *)
Axiom malloc_mload_aux_undef: forall TD t tsz mcs M gn align0 M' mb gvs gl
  (Hsz: getTypeAllocSize TD t = Some tsz)
  (Hflatten: flatten_typ TD t = Some mcs)
  (Hal : malloc TD M tsz gn align0 = ret (M', mb))
  (Hc2v : Opsem.const2GV TD gl (const_undef t) = ret gvs),
  mload_aux M' mcs mb (Int.signed 31 (Int.repr 31 0)) = ret gvs.

Axiom alloca_mload_aux_undef: forall TD t tsz mcs M gn align0 M' mb gvs gl
  (Hsz: getTypeAllocSize TD t = Some tsz)
  (Hflatten: flatten_typ TD t = Some mcs)
  (Hal : alloca TD M tsz gn align0 = ret (M', mb))
  (Hc2v : Opsem.const2GV TD gl (const_undef t) = ret gvs),
  mload_aux M' mcs mb (Int.signed 31 (Int.repr 31 0)) = ret gvs.

Lemma redundant__wf_globals: forall maxb gl, 
  wf_globals maxb gl ->
  genericvalues_inject.wf_globals maxb gl.
Proof.
  intros. destruct H.
  induction gl; auto.
Qed.

(**************************************************)
(* Properties of externals *)
Axiom callExternalOrIntrinsics_preserves_mload: forall Mem fid gvsa gvs gvsv
  Mem' TD oresult ty al dck gl tret targs tr,
  callExternalOrIntrinsics TD gl Mem fid tret targs dck gvs 
    = ret (oresult, tr, Mem') ->
  mload TD Mem gvsa ty al = ret gvsv ->
  mload TD Mem' gvsa ty al = ret gvsv.

(**************************************************)
(* Properties of inject_init *)
Definition inject_init (maxb:positive) : MoreMem.meminj :=
fun (b:Values.block) => 
if Pos.leb b maxb then Some (b, 0)
else None.

End MemProps.
