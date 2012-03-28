Require Import List.
Require Import Arith.
Require Import monad.
Require Import Metatheory.
Require Import alist.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import Kildall.
Require Import ListSet.

(**********************************)
(* Dom and Reaching analysis *)

Require Import syntax.
Require Import infrastructure.
Require Import infrastructure_props.
Import LLVMsyntax.
Import LLVMinfra.

Fixpoint successors_blocks (bs: blocks) : ATree.t ls :=
match bs with
| nil => ATree.empty ls
| block_intro l0 _ _ tmn :: bs' =>
    ATree.set l0 (successors_terminator tmn) (successors_blocks bs')
end.

Definition successors (f: fdef) : ATree.t ls :=
let '(fdef_intro _ bs) := f in
successors_blocks bs.

Definition transfer (bound: set atom) (lbl: l) (before: Dominators.t bound) :=
  Dominators.add _ before lbl.

(** The static analysis itself is then an instantiation of Kildall's
  generic solver for forward dataflow inequations. [analyze f]
  returns a mapping from program points to mappings of pseudo-registers
  to approximations.  It can fail to reach a fixpoint in a reasonable
  number of iterations, in which case [None] is returned. *)

Fixpoint bound_blocks (bs: blocks) : set atom :=
match bs with
| nil => empty_set _
| block_intro l0 _ _ tmn :: bs' => l0::(bound_blocks bs')
end.

Definition bound_fdef (f: fdef) : set atom :=
let '(fdef_intro _ bs) := f in
bound_blocks bs.

Lemma entry_dom : forall (bs:list block),
  {oresult : option (l * Dominators.BoundedSet (bound_blocks bs)) &
     match oresult with
     | None => bs = nil
     | Some (le, Dominators.mkBoundedSet nil _) => True
     | _ => False
     end
  }.
Proof.
  intros.
  destruct bs as [| b bs]; simpl in *.
    exists None. auto.

    destruct b as [l0 ps0 cs0 tmn0].
    assert (incl nil (l0 :: bound_blocks bs)) as J.
      intros a J. inv J.
    exists (Some (l0, Dominators.mkBoundedSet _ nil J)). auto.
Defined.

Module DomDS := Dataflow_Solver_Var_Top(AtomNodeSet).

Definition dom_analyze (f: fdef) : AMap.t (Dominators.t (bound_fdef f)) :=
  let '(fdef_intro _ bs) := f in
  let bound := bound_blocks bs in
  let top := Dominators.top bound in
  match entry_dom bs with
  | (existT (Some (le, start)) _) =>
      match DomDS.fixpoint bound (successors_blocks bs) (transfer bound)
        ((le, start) :: nil) with
      | None => (AMap.set le start (AMap.init top))
      | Some res => res
      end
  | (existT None _) => AMap.init top
  end.

Definition blockDominates (f: fdef) (b1 b2: block) : Prop :=
let '(block_intro l1 _ _ _) := b1 in
let '(block_intro l2 _ _ _) := b2 in
let 'dt := dom_analyze f in
let '(Dominators.mkBoundedSet els _) := AMap.get l2 dt in
set_In l1 els \/ l1 = l2.

Definition blockStrictDominates (f: fdef) (b1 b2: block) : Prop :=
let '(block_intro l1 _ _ _) := b1 in
let '(block_intro l2 _ _ _) := b2 in
let 'dt := dom_analyze f in
let '(Dominators.mkBoundedSet els _) := AMap.get l2 dt in
set_In l1 els.

Definition insnDominates (id1:id) (i2:insn) (b:block) : Prop :=
match b with
| (block_intro l5 ps cs tmn) =>
  match i2 with
  | insn_terminator tmn2 =>
      ((exists cs1, exists c1, exists cs2,
         cs = cs1++c1::cs2 /\ getCmdID c1 = Some id1) \/
       (exists ps1, exists p1, exists ps2,
         ps = ps1++p1::ps2 /\ getPhiNodeID p1 = id1)
       ) /\ tmn2 = tmn
  | insn_cmd c2 =>
      (exists ps1, exists p1, exists ps2,
         ps = ps1++p1::ps2 /\ getPhiNodeID p1 = id1) \/
      (exists cs1, exists c1, exists cs2, exists cs3,
         cs = cs1++c1::cs2 ++ c2 :: cs3 /\ getCmdID c1 = Some id1)
  | _ => False
  end
end.

Module ReachDS := Dataflow_Solver(LBoolean)(AtomNodeSet).

Definition areachable_aux (f: fdef) : option (AMap.t bool) :=
  match getEntryBlock f with
  | Some (block_intro le _ _ _) =>
     ReachDS.fixpoint (successors f) (fun pc r => r) ((le, true) :: nil)
  | None => None
  end.

Definition areachable (f: fdef) : AMap.t bool :=
  match areachable_aux f with
  | None => AMap.init true
  | Some rs => rs
  end.

Require Import Dipaths.

Definition vertexes_fdef (f:fdef) : V_set :=
fun (v:Vertex) => let '(index a) := v in In a (bound_fdef f).

Definition arcs_fdef (f:fdef) : A_set :=
fun (arc:Arc) =>
  let '(A_ends (index a2) (index a1)) := arc in
  In a2 ((successors f)!!!a1).

Definition reachable (f:fdef) (l0:l) : Prop :=
match getEntryBlock f with
| Some (block_intro entry _ _ _) =>
  let vertexes := vertexes_fdef f in
  let arcs := arcs_fdef f in
  exists vl: V_list, exists al: A_list,
    D_walk vertexes arcs (index l0) (index entry) vl al
| _ => false
end.

Definition isReachableFromEntry (f:fdef) (b1:block) : Prop :=
let '(block_intro l1 _ _ _) := b1 in
reachable f l1.

Definition isAReachableFromEntry (f:fdef) (b1:block) : Prop :=
let '(block_intro l1 _ _ _) := b1 in
AMap.get l1 (areachable f).

(********************************************)
(** * Properties of domination analysis *)

Import AtomSet.

Definition eq_dts bound1 bound2 (dts1:DomDS.dt1 bound1) (dts2:DomDS.dt2 bound2)
  :=
match dts1, dts2 with
| {| DomDS.L.bs_contents := els1 |}, {| DomDS.L.bs_contents := els2 |} =>
  set_eq _ els1 els2
end.

Lemma eq_dts_prop1 : forall bd,
  eq_dts bd bd (DomDS.L.bot bd) (DomDS.L.bot bd).
Proof.
  intros. simpl. auto using set_eq_refl.
Qed.

Lemma eq_dts_prop2 : forall bd x1 x2 y1 y2,
  eq_dts bd bd x1 x2 ->
  eq_dts bd bd y1 y2 ->
  eq_dts bd bd (DomDS.L.lub bd x1 y1) (DomDS.L.lub bd x2 y2).
Proof.
  intros.
  destruct x1. destruct x2. destruct y1. destruct y2. simpl in *.
  apply set_eq_inter; auto.
Qed.

Lemma eq_dts_prop3 : forall bd x1 x2 pc,
  eq_dts bd bd x1 x2 ->
  eq_dts bd bd (transfer bd pc x1) (transfer bd pc x2).
Proof.
  intros.
  unfold transfer. unfold Dominators.add.
  destruct x1, x2.
  destruct (in_dec eq_atom_dec pc bd); simpl in *; auto.
    simpl_env. apply set_eq_app; auto using set_eq_refl.
Qed.

Lemma eq_dts_prop4 : forall bd x1 x2 y1 y2,
  eq_dts bd bd x1 x2 ->
  eq_dts bd bd y1 y2 ->
  DomDS.L.beq bd y1 (DomDS.L.lub bd y1 x1) =
    DomDS.L.beq bd y2 (DomDS.L.lub bd y2 x2).
Proof.
  intros.
  destruct x1. destruct x2. destruct y1. destruct y2. simpl in *.
  assert (
    set_eq atom (ListSet.set_inter eq_atom_dec bs_contents1 bs_contents)
      (ListSet.set_inter eq_atom_dec bs_contents2 bs_contents0)
  ) as EQ.
    apply set_eq_inter; auto.
  unfold DomDS.L.beq.
  destruct (
    DomDS.L.eq_dec bd
         {|
         DomDS.L.bs_contents := bs_contents1;
         DomDS.L.bs_bound := bs_bound1 |}
         {|
         DomDS.L.bs_contents := ListSet.set_inter eq_atom_dec bs_contents1
                                  bs_contents;
         DomDS.L.bs_bound := DomDS.L.lub_obligation_1 bd
                              {|
                              DomDS.L.bs_contents := bs_contents1;
                              DomDS.L.bs_bound := bs_bound1 |}
                              {|
                              DomDS.L.bs_contents := bs_contents;
                              DomDS.L.bs_bound := bs_bound |} bs_contents1
                              bs_bound1 eq_refl bs_contents bs_bound eq_refl |});
    simpl in *.
    destruct (
      DomDS.L.eq_dec bd
         {|
         DomDS.L.bs_contents := bs_contents2;
         DomDS.L.bs_bound := bs_bound2 |}
         {|
         DomDS.L.bs_contents := ListSet.set_inter eq_atom_dec bs_contents2
                                  bs_contents0;
         DomDS.L.bs_bound := DomDS.L.lub_obligation_1 bd
                               {|
                               DomDS.L.bs_contents := bs_contents2;
                               DomDS.L.bs_bound := bs_bound2 |}
                               {|
                               DomDS.L.bs_contents := bs_contents0;
                               DomDS.L.bs_bound := bs_bound0 |} bs_contents2
                               bs_bound2 eq_refl bs_contents0 bs_bound0
                               eq_refl |});
      simpl in *; auto.
      contradict n; eauto using set_eq_trans, set_eq_sym.
    destruct (
      DomDS.L.eq_dec bd
         {|
         DomDS.L.bs_contents := bs_contents2;
         DomDS.L.bs_bound := bs_bound2 |}
         {|
         DomDS.L.bs_contents := ListSet.set_inter eq_atom_dec bs_contents2
                                  bs_contents0;
         DomDS.L.bs_bound := DomDS.L.lub_obligation_1 bd
                               {|
                               DomDS.L.bs_contents := bs_contents2;
                               DomDS.L.bs_bound := bs_bound2 |}
                               {|
                               DomDS.L.bs_contents := bs_contents0;
                               DomDS.L.bs_bound := bs_bound0 |} bs_contents2
                               bs_bound2 eq_refl bs_contents0 bs_bound0
                               eq_refl |});
      simpl in *; auto.
    contradict n; eauto using set_eq_trans, set_eq_sym.
Qed.

Hint Resolve eq_dts_prop1 eq_dts_prop2 eq_dts_prop3 eq_dts_prop4: eq_dts_db.

Lemma blockStrictDominates_iff : forall (l4 l1 l0 : l) (id' : id)
  bd1 bd2 succ (Heq : bd1 = bd2) cts
  (bs_bound1 : incl cts bd1)
  (bs_bound2 : incl cts bd2) init1 init2
  (Heq1 : init1 = {| DomDS.L.bs_contents := cts;
                   DomDS.L.bs_bound := bs_bound1 |})
  (Heq2 : init2 = {| DomDS.L.bs_contents := cts;
                   DomDS.L.bs_bound := bs_bound2 |}),
   (let '{| DomDS.L.bs_contents := els |} :=
         Maps.AMap.get l1
           match
             DomDS.fixpoint bd1 succ (transfer bd1) ((l4, init1) :: nil)
           with
           | ret res => res
           | merror =>
               Maps.AMap.set l4 init1 (Maps.AMap.init (Dominators.top bd1))
           end in ListSet.set_In l0 els) <->
   (let '{| DomDS.L.bs_contents := els |} :=
         Maps.AMap.get l1
           match
             DomDS.fixpoint bd2 succ (transfer bd2) ((l4, init2):: nil)
           with
           | ret res => res
           | merror =>
               Maps.AMap.set l4 init2 (Maps.AMap.init (Dominators.top bd2))
           end in ListSet.set_In l0 els).
Proof.
  intros.
  unfold l in *.
  case_eq (DomDS.fixpoint bd2 succ (transfer bd2) ((l4, init2) :: nil)).
      intros dom2 Hfix2.
      apply DomDS.fixpoint_some2_right with (pc:=l1) (P:=eq_dts bd1 bd2)
        (bound1:=bd1) (transf1:=transfer bd1)(entrypoints1:=((l4, init1):: nil))
        in Hfix2; subst;
        try solve [(auto with eq_dts_db) |
                   apply Forall2_cons; simpl; auto using set_eq_refl].
        destruct Hfix2 as [dom1 [Hfix1 Heq']].
        rewrite Hfix1.
        unfold DomDS.dt in *.
        destruct (Maps.AMap.get l1 dom1). destruct (Maps.AMap.get l1 dom2).
        simpl in *.
        destruct Heq' as [J1 J2].
        unfold ListSet.set_In.
        split; intro J; eauto.

      intros Hfix2.
      apply DomDS.fixpoint_none2_right with (bound1:=bd1) (P:=eq_dts bd1 bd2)
        (transf1:=transfer bd1) (entrypoints1:=((l4,init1) :: nil)) in Hfix2;
        subst; try solve [(auto with eq_dts_db) |
                           apply Forall2_cons; simpl; auto using set_eq_refl].
        rewrite Hfix2. clear Hfix2.
        repeat rewrite Maps.AMap.gsspec.
        destruct (eq_atom_dec l1 l4); subst.
          split; intro; auto.

          unfold Maps.AMap.init.
          unfold Maps.AMap.get. simpl.
          repeat rewrite Maps.ATree.gempty. simpl.
          split; intro; auto.
Qed.

Lemma blockDominates_iff : forall (l4 l1 l0 : l) (id' : id)
  bd1 bd2 succ (Heq : bd1 = bd2) cts
  (bs_bound1 : incl cts bd1)
  (bs_bound2 : incl cts bd2) init1 init2
  (Heq1 : init1 = {| DomDS.L.bs_contents := cts;
                   DomDS.L.bs_bound := bs_bound1 |})
  (Heq2 : init2 = {| DomDS.L.bs_contents := cts;
                   DomDS.L.bs_bound := bs_bound2 |}),
   (let '{| DomDS.L.bs_contents := els |} :=
         Maps.AMap.get l1
           match
             DomDS.fixpoint bd1 succ (transfer bd1) ((l4, init1) :: nil)
           with
           | ret res => res
           | merror =>
               Maps.AMap.set l4 init1 (Maps.AMap.init (Dominators.top bd1))
           end in ListSet.set_In l0 els \/ l0 = l1) <->
   (let '{| DomDS.L.bs_contents := els |} :=
         Maps.AMap.get l1
           match
             DomDS.fixpoint bd2 succ (transfer bd2) ((l4, init2):: nil)
           with
           | ret res => res
           | merror =>
               Maps.AMap.set l4 init2 (Maps.AMap.init (Dominators.top bd2))
           end in ListSet.set_In l0 els \/ l0 = l1).
Proof.
  intros.
  unfold l in *.
  case_eq (DomDS.fixpoint bd2 succ (transfer bd2) ((l4, init2) :: nil)).
      intros dom2 Hfix2.
      apply DomDS.fixpoint_some2_right with (pc:=l1) (P:=eq_dts bd1 bd2)
        (bound1:=bd1) (transf1:=transfer bd1)(entrypoints1:=((l4, init1):: nil))
        in Hfix2; subst;
        try solve [(auto with eq_dts_db) |
                   apply Forall2_cons; simpl; auto using set_eq_refl].
        destruct Hfix2 as [dom1 [Hfix1 Heq']].
        rewrite Hfix1.
        unfold DomDS.dt in *.
        destruct (Maps.AMap.get l1 dom1). destruct (Maps.AMap.get l1 dom2).
        simpl in *.
        destruct Heq' as [J1 J2].
        unfold ListSet.set_In.
        split; intro J; destruct J; auto.

      intros Hfix2.
      apply DomDS.fixpoint_none2_right with (bound1:=bd1) (P:=eq_dts bd1 bd2)
        (transf1:=transfer bd1) (entrypoints1:=((l4,init1) :: nil)) in Hfix2;
        subst; try solve [(auto with eq_dts_db) |
                           apply Forall2_cons; simpl; auto using set_eq_refl].
        rewrite Hfix2. clear Hfix2.
        repeat rewrite Maps.AMap.gsspec.
        destruct (eq_atom_dec l1 l4); subst.
          split; intro; auto.

          unfold Maps.AMap.init.
          unfold Maps.AMap.get. simpl.
          repeat rewrite Maps.ATree.gempty. simpl.
          split; intro; auto.
Qed.

(********************************************)
(** * Correctness of analysis *)

Lemma atomset_eq__proof_irr2 : forall (* proof irrelevence *)
  max
  (contents' : ListSet.set atom)
  (inbound' : incl contents' max)
  a
  (Heqdefs' : {|
             DomDS.L.bs_contents := contents';
             DomDS.L.bs_bound := inbound' |} = a),
  contents' = Dominators.bs_contents max a.
Proof. intros. subst. simpl. auto. Qed.

Lemma atomset_eq__proof_irr1 : forall
  (bs : blocks)
  (l' : l)
  (t : AMap.t (DomDS.dt (bound_blocks bs)))
  (contents' : ListSet.set atom)
  (inbound' : incl contents' (bound_blocks bs))
  (Heqdefs' : {|
             DomDS.L.bs_contents := contents';
             DomDS.L.bs_bound := inbound' |} = t !! l')
  (bs_contents : ListSet.set atom)
  (bs_bound0 : incl bs_contents (bound_blocks bs))
  (HeqR2 : {|
          DomDS.L.bs_contents := bs_contents;
          DomDS.L.bs_bound := bs_bound0 |} = t !! l'),
  contents' = bs_contents.
Proof.
  intros.
  apply atomset_eq__proof_irr2 in Heqdefs'; subst.
  apply atomset_eq__proof_irr2 in HeqR2; subst.
  auto.
Qed.

Lemma areachable_entrypoint:
  forall (f:fdef) l0 ps cs tmn,
    getEntryBlock f = Some (block_intro l0 ps cs tmn) ->
    (areachable f)!!l0 = true.
Proof.
  intros f l0 ps cs tmn Hentry. unfold areachable.
  caseEq (areachable_aux f).
    unfold areachable_aux; intros reach A.
    rewrite Hentry in A.
    assert (LBoolean.ge reach!!l0 true).
      eapply ReachDS.fixpoint_entry. eexact A. auto with coqlib.
    unfold LBoolean.ge in H. tauto.

    intros. apply AMap.gi.
Qed.

Lemma entry_in_vertexes : forall f l0 ps cs tmn
  (Hentry : getEntryBlock f = ret block_intro l0 ps cs tmn),
  vertexes_fdef f (index l0).
Proof.
  intros.
  unfold vertexes_fdef. unfold bound_fdef. destruct f as [f b].
  destruct b; simpl in *.
    congruence.
    inv Hentry. simpl. auto.
Qed.

Lemma reachable_dec: forall (f:fdef) (l1:l), reachable f l1 \/ ~ reachable f l1.
Proof. intros. tauto. Qed. (* classic logic *)

Lemma reachable_entrypoint:
  forall (f:fdef) l0 ps cs tmn,
    getEntryBlock f = Some (block_intro l0 ps cs tmn) ->
    reachable f l0.
Proof.
  intros f l0 ps cs tmn Hentry. unfold reachable.
  rewrite Hentry. exists V_nil. exists A_nil. apply DW_null.
  eapply entry_in_vertexes; eauto.
Qed.

Lemma successors_terminator__successors_blocks : forall
  (bs : blocks)
  (l0 : l)
  (cs : phinodes)
  (ps : cmds)
  (tmn : terminator)
  (l1 : l)
  (HuniqF : uniqBlocks bs)
  (HbInF : InBlocksB (block_intro l0 cs ps tmn) bs)
  (Hin : In l1 (successors_terminator tmn)),
  successors_terminator tmn = (successors_blocks bs) !!! l0.
Proof.
  intros.
  induction bs.
    inversion HbInF.

    assert (J:=HuniqF).
    simpl_env in J.
    apply uniqBlocks_inv in J.
    destruct J as [J1 J2].
    simpl in *.
    apply orb_prop in HbInF.
    destruct a.
    destruct HbInF as [HbInF | HbInF].
      unfold blockEqB in HbInF.
      apply sumbool2bool_true in HbInF. inv HbInF.
      unfold successors_list.
      rewrite ATree.gss. auto.

      apply IHbs in J2; auto.
      unfold successors_list in *.
      destruct HuniqF as [J _].
      inv J.
      rewrite ATree.gso; auto.
        clear - HbInF H1.
        eapply InBlocksB__NotIn; eauto.
Qed.

Lemma successors_predOfBlock : forall f l1 ps1 cs1 tmn1 l0 ps0 cs0 tmn0,
  uniqFdef f ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true ->
  In l0 (successors_terminator tmn1) ->
  In l1 (predOfBlock (block_intro l0 ps0 cs0 tmn0) (genBlockUseDef_fdef f)).
Proof.
  unfold predOfBlock.
  destruct f as [f b].
  destruct f as [fnattrs5 typ5 id5 args5 varg5].
  intros.
  destruct H as [H _].
  generalize dependent l1.
  generalize dependent ps1.
  generalize dependent cs1.
  generalize dependent tmn1.
  generalize dependent l0.
  generalize dependent ps0.
  generalize dependent cs0.
  generalize dependent tmn0.
  induction b as [|a0 b]; intros; simpl in *.
    inversion H0.

    assert (G:=H). simpl_env in G.
    apply uniqBlocks_inv in G.
    destruct G as [G1 G2].
    destruct a0 as [l5 p c t0]. simpl.
    apply orb_prop in H0.
    destruct H0 as [H0 | H0].
      apply blockEqB_inv in H0.
      inv H0.
      destruct t0 as [i0 t0 v0|i0|i0 v0 l2 l3|i0 l2|i0]; auto.
        apply IHb with (ps1:=p)(cs1:=c)(tmn1:=insn_return i0 t0 v0); auto.
        apply IHb with (ps1:=p)(cs1:=c)(tmn1:=insn_return_void i0); auto.

        simpl in H1.
        destruct H1 as [H1 | [H1 | H1]]; subst.
          assert (J:=@lookupAL_update_udb_eq (update_udb nil l5 l3) l5 l0).
          destruct J as [ls0 [J1 J2]].
          apply lookupAL_genBlockUseDef_blocks_spec with (bs:=b) in J1; auto.
          destruct J1 as [ls1 [J1 J3]].
          rewrite J1. apply J3; auto.

          assert (J:=@lookupAL_update_udb_eq nil l5 l0).
          destruct J as [ls0 [J J0]].
          apply lookupAL_update_udb_spec with (l1:=l5)(l2:=l2) in J; auto.
          destruct J as [ls1 [J J1]].
          apply lookupAL_genBlockUseDef_blocks_spec with (bs:=b) in J; auto.
          destruct J as [ls2 [J J2]].
          rewrite J. apply J2. apply J1. auto.

          inversion H1.
        simpl in H1.
        destruct H1 as [H1 | H1]; subst.
          assert (J:=@lookupAL_update_udb_eq nil l5 l0).
          destruct J as [ls0 [J J0]].
          apply lookupAL_genBlockUseDef_blocks_spec with (bs:=b) in J; auto.
          destruct J as [ls2 [J J2]].
          rewrite J. apply J2. auto.

          inversion H1.

        apply IHb with (ps1:=p)(cs1:=c)(tmn1:=insn_unreachable i0); auto.

      eapply IHb in H1; eauto.
        remember (lookupAL (list l) (genBlockUseDef_blocks b nil) l0) as R.
        destruct R as [l4|]; try solve [inversion H1].
        destruct H as [J1 J2].
        simpl in J1.
        inv J1.
        apply InBlocksB_In in H0.
        destruct (eq_atom_dec l1 l5); subst.
          contradict H0; auto.

          clear - HeqR H1.
          simpl.
          assert (usedef_block_inc nil
            (match t0 with
             | insn_return _ _ _ => nil
             | insn_return_void _ => nil
             | insn_br _ _ l2 l3 => update_udb (update_udb nil l5 l3) l5 l2
             | insn_br_uncond _ l2 => update_udb nil l5 l2
             | insn_unreachable _ => nil
             end)) as J.
            intros x A J. inversion J.
          apply genBlockUseDef_blocks_inc with (bs:=b) in J.
          symmetry in HeqR.
          apply J in HeqR.
          destruct HeqR as [l2 [J1 J2]].
          rewrite J1. apply J2 in H1; auto.
Qed.

Lemma areachable_successors:
  forall f l0 cs ps tmn l1,
  uniqFdef f ->
  blockInFdefB (block_intro l0 cs ps tmn) f ->
  In l1 (successors_terminator tmn) ->
  (areachable f)!!l0 = true ->
  (areachable f)!!l1 = true.
Proof.
  intros f l0 cs ps tmn l1 HuniqF HbInF Hin.
  unfold areachable.
  caseEq (areachable_aux f).
    unfold areachable_aux. intro reach; intros.
    remember (getEntryBlock f) as R.
    destruct R; inv H.
    destruct b as [le ? ? ?].
    assert (LBoolean.ge reach!!l1 reach!!l0) as J.
      change (reach!!l0) with ((fun pc r => r) l0 (reach!!l0)).
      eapply ReachDS.fixpoint_solution; eauto.
        destruct f as [[?] bs]. simpl in *.
        clear - HuniqF HbInF Hin. destruct HuniqF.
        assert ((successors_terminator tmn) = (successors_blocks bs) !!! l0)
          as EQ.
          eapply successors_terminator__successors_blocks; eauto.
        rewrite <- EQ; auto.
    elim J; intro. congruence. auto.

  intros. apply AMap.gi.
Qed.

Lemma blockInFdefB__successors : forall a ps0 cs0 tmn0 f (Huniq: uniqFdef f),
  blockInFdefB (block_intro a ps0 cs0 tmn0) f ->
  (successors f) ! a = Some (successors_terminator tmn0).
Proof.
  destruct f as [[] bs]. simpl.
  intros [J _].
  unfold uniqBlocks in J.
  destruct J as [J _].
  induction bs as [|a1 bs]; simpl; intros.
    congruence.

    destruct a1 as [l0 ps1 cs1 tmn1].
    apply orb_true_iff in H.
    destruct H as [H | H].
      apply blockEqB_inv in H. inv H.
      rewrite ATree.gss. auto.

      assert (J':=J). inv J'.
      simpl in J. simpl_env in J.
      apply IHbs in H3; auto.
      apply InBlocksB_In in H.
      apply infrastructure_props.NoDup_disjoint with (i0:=a) in J; auto.
      destruct (id_dec l0 a); subst.
        contradict J. simpl. auto.

        rewrite ATree.gso; auto.
Qed.

Lemma successors__blockInFdefB : forall l0 a f,
  In l0 (successors f) !!! a ->
  exists ps0, exists cs0, exists tmn0,
    blockInFdefB (block_intro a ps0 cs0 tmn0) f /\
    In l0 (successors_terminator tmn0).
Proof.
  destruct f as [fh bs]. simpl.
  unfold successors_list.
  induction bs as [|a0 bs]; simpl; intro.
    rewrite ATree.gempty in H. inv H.

    destruct a0 as [l1 p c t].
    destruct (id_dec l1 a); subst.
      rewrite ATree.gss in H.
      exists p. exists c. exists t.
      split; auto.
        eapply orb_true_iff. left. apply blockEqB_refl.

      rewrite ATree.gso in H; auto.
      apply IHbs in H; auto.
      destruct H as [ps0 [cs0 [tmn0 [J1 J2]]]].
      exists ps0. exists cs0. exists tmn0.
      split; auto.
        eapply orb_true_iff; eauto.
Qed.

Lemma successors_blocks__blockInFdefB : forall l0 a fh bs,
  In l0 (successors_blocks bs) !!! a ->
  exists ps0, exists cs0, exists tmn0,
    blockInFdefB (block_intro a ps0 cs0 tmn0) (fdef_intro fh bs) /\
    In l0 (successors_terminator tmn0).
Proof.
  intros.
  apply successors__blockInFdefB; auto.
Qed.

Lemma areachable_is_correct:
  forall f l0,
  uniqFdef f ->
  reachable f l0 ->
  (areachable f)!!l0.
Proof.
  unfold reachable.
  intros.
  remember (getEntryBlock f) as R.
  destruct R; tinv H0.
  destruct b as [l1 p c t]. destruct H0 as [vl [al H0]].
  remember (vertexes_fdef f) as Vs.
  remember (arcs_fdef f) as As.
  remember (index l0) as v0.
  remember (index l1) as v1.
  generalize dependent f.
  generalize dependent l0.
  generalize dependent l1.
  generalize dependent p.
  generalize dependent c.
  generalize dependent t.
  induction H0; intros; subst.
    inv Heqv0.
    symmetry in HeqR.
    apply areachable_entrypoint in HeqR; auto.

    destruct y as [a0].
    apply IHD_walk with (l0:=a0) in HeqR; auto.
    assert (exists ps0, exists cs0, exists tmn0,
      blockInFdefB (block_intro a0 ps0 cs0 tmn0) f /\
      In l0 (successors_terminator tmn0)) as J.
      eapply successors__blockInFdefB; eauto.
    destruct J as [ps0 [cs0 [tmn0 [HBinF' Hinsucc]]]].
    eapply areachable_successors; eauto.
Qed.

Lemma arcs_fdef_inv : forall f a1 a2,
  arcs_fdef f (A_ends (index a2) (index a1)) ->
  In a2 ((successors f)!!!a1).
Proof. auto. Qed.

Lemma blockInFdefB_in_vertexes : forall l0 cs ps tmn f
  (HbInF : blockInFdefB (block_intro l0 cs ps tmn) f),
  vertexes_fdef f (index l0).
Proof.
  intros.
  unfold vertexes_fdef, bound_fdef.
  destruct f as [f b].
  generalize dependent cs.
  generalize dependent ps.
  generalize dependent tmn.
  generalize dependent l0.
  induction b; simpl in *; intros.
    congruence.

    destruct a.
    apply orb_prop in HbInF.
    destruct HbInF as [HbInF | HbInF].
      unfold blockEqB in HbInF.
      apply sumbool2bool_true in HbInF. inv HbInF.
      simpl. auto.

      apply IHb in HbInF.
      simpl. auto.
Qed.

Lemma successor_in_arcs : forall l0 cs ps tmn f l1
  (HuniqF : uniqFdef f)
  (HbInF : blockInFdefB (block_intro l0 cs ps tmn) f)
  (Hin : In l1 (successors_terminator tmn)),
  arcs_fdef f (A_ends (index l1) (index l0)).
Proof.
  intros.
  unfold arcs_fdef.
  destruct f as [fh bs]. apply uniqF__uniqBlocks in HuniqF.
  simpl.
  erewrite <- successors_terminator__successors_blocks; eauto.
Qed.

Ltac tinv H := try solve [inv H].
Import AtomSet.

Lemma dom_entrypoint : forall f l0 ps cs tmn
  (Hentry : getEntryBlock f = Some (block_intro l0 ps cs tmn)),
  Dominators.bs_contents (bound_fdef f) ((dom_analyze f) !! l0) = nil.
Proof.
  intros.
  unfold dom_analyze.
  destruct f as [f b].
  remember (entry_dom b) as R.
  destruct R as [R Hp].
  destruct R as [[le start] | ].
  Case "entry is good".
    remember (DomDS.fixpoint (bound_blocks b) (successors_blocks b)
                (transfer (bound_blocks b)) ((le, start) :: nil)) as R1.
    destruct start.
    destruct bs_contents; tinv Hp.
    destruct b; try solve [inversion HeqR].
    destruct b as [l1 p c t]. simpl in HeqR. inversion HeqR. subst le.
    simpl in Hentry. inversion Hentry. subst l0 p c t.
    clear HeqR Hentry.
    destruct R1; subst.
    SCase "analysis is done".
      symmetry in HeqR1.
      apply DomDS.fixpoint_entry with (n:=l1)(v:={|
                DomDS.L.bs_contents := nil;
                DomDS.L.bs_bound := bs_bound |}) in HeqR1; simpl; eauto.
      unfold DomDS.L.ge in HeqR1.
      unfold DomDS.L.eq, DomDS.L.top, DomDS.L.bot, DomDS.L.sub in HeqR1.
      simpl in *.

      remember (t !! l1) as R.
      destruct R.
      change (Dominators.t) with (DomDS.dt).
      rewrite <- HeqR. simpl.
      destruct HeqR1 as [HeqR1 | [ HeqR1 | HeqR1 ]]; auto.
      SSCase "1".
        apply set_eq_empty_inv in HeqR1. subst. auto.
      SSCase "2".
        apply set_eq_sym in HeqR1.
        apply set_eq_empty_inv in HeqR1. inv HeqR1.
      SSCase "3".
        apply incl_empty_inv in HeqR1; auto.

    SCase "analysis fails".
      simpl.
      rewrite AMap.gss. simpl. auto.

  Case "entry is wrong".
    subst. inversion Hentry.
Qed.

Module EntryDomsOthers.

Section EntryDomsOthers.

Variable bs : blocks.
Definition bound := bound_blocks bs.
Definition predecessors := make_predecessors (successors_blocks bs).
Definition transf := transfer bound.
Definition top := Dominators.top bound.
Definition bot := Dominators.bot bound.
Definition dt := DomDS.dt bound.
Variable entry: l.
Variable entrypoints: list (atom * dt).

Hypothesis wf_entrypoints:
  predecessors!!!entry = nil /\
  match bs with
  | block_intro l0 _ _ _ :: _ => l0 = entry
  | _ => False
  end /\
  exists v, [(entry, v)] = entrypoints /\ Dominators.eq _ v top.

Lemma dom_entry_start_state_in:
  forall n v,
  In (n, v) entrypoints ->
  Dominators.eq _ (DomDS.start_state_in _ entrypoints)!!n v.
Proof.
  destruct wf_entrypoints as [_ [_ J]]. clear wf_entrypoints.
  destruct J as [v [Heq J]]; subst. simpl.
  intros.
  destruct H as [H | H]; inv H.
  rewrite AMap.gss. rewrite AMap.gi.
  apply Dominators.eq_trans with (y:=DomDS.L.lub bound v0 bot).
    apply Dominators.lub_commut.
    apply Dominators.lub_preserves_ge.
    apply Dominators.ge_compat with (x:=top)(y:=bot).
      apply Dominators.eq_sym; auto.
      apply Dominators.eq_refl.
      apply Dominators.ge_bot.
Qed.

Lemma dom_nonentry_start_state_in:
  forall n,
  n <> entry ->
  Dominators.eq _ (DomDS.start_state_in _ entrypoints)!!n bot.
Proof.
  destruct wf_entrypoints as [_ [_ J]]. clear wf_entrypoints.
  destruct J as [v [Heq J]]; subst. simpl.
  intros.
  rewrite AMap.gi. rewrite AMap.gso; auto. rewrite AMap.gi.
  apply Dominators.eq_refl.
Qed.

Lemma transf_mono: forall p x y,
  Dominators.ge bound x y -> Dominators.ge _ (transf p x) (transf p y).
Proof.
  unfold transf, transfer. intros.
  apply Dominators.add_mono; auto.
Qed.

Definition lub_of_preds (res: AMap.t dt) (n:atom) : dt :=
  Dominators.lubs _ (List.map (fun p => transf p res!!p)
    (predecessors!!!n)).

Definition entry_doms_others (res: AMap.t dt) : Prop :=
  forall l0, l0 <> entry -> Dominators.member _ entry res!!l0.

Lemma start_entry_doms_others:
  entry_doms_others
    (DomDS.st_in _ (DomDS.start_state _ (successors_blocks bs) entrypoints)).
Proof.
  intros l0 Hneq.
  apply dom_nonentry_start_state_in in Hneq.
  unfold DomDS.start_state. simpl.
  apply Dominators.member_eq with (x2:=bot); auto.
  destruct wf_entrypoints as [_ [J _]]. unfold bot. unfold bound.
  destruct bs; tinv J.
  destruct b; subst. simpl. auto.
Qed.

(** We show that the start state satisfies the invariant, and that
  the [step] function preserves it. *)

Lemma propagate_succ_entry_doms_others: forall st n out,
  Dominators.member _ entry out ->
  entry_doms_others st.(DomDS.st_in _) ->
  entry_doms_others (DomDS.propagate_succ _ st out n).(DomDS.st_in _).
Proof.
  unfold entry_doms_others.
  intros.
  destruct (@DomDS.propagate_succ_spec _ st out n) as [J1 J2].
  apply H0 in H1.
  destruct (eq_atom_dec n l0); subst.
    apply Dominators.member_eq with (a:=entry) in J1; auto.
    apply Dominators.member_lub; auto.

    rewrite J2; auto.
Qed.

Lemma propagate_succ_list_entry_doms_others:
  forall scs st out,
  Dominators.member _ entry out ->
  entry_doms_others st.(DomDS.st_in _) ->
  entry_doms_others (DomDS.propagate_succ_list _ st out scs).(DomDS.st_in _).
Proof.
  induction scs; simpl; intros; auto.
    apply IHscs; auto.
    apply propagate_succ_entry_doms_others; auto.
Qed.

Lemma step_entry_doms_others:
  forall st n rem,
  AtomNodeSet.pick st.(DomDS.st_wrk _) = Some(n, rem) ->
  entry_doms_others st.(DomDS.st_in _) ->
  entry_doms_others (DomDS.propagate_succ_list _
                                  (DomDS.mkstate _ st.(DomDS.st_in _) rem)
                                  (transf n st.(DomDS.st_in _)!!n)
                                  ((successors_blocks bs)!!!n)).(DomDS.st_in _).
Proof.
  intros st n rem WKL GOOD.
  destruct st. simpl.
  apply propagate_succ_list_entry_doms_others; auto.
    simpl in *.
    unfold transf, transfer.
    destruct (eq_atom_dec n entry); subst.
      apply Dominators.add_member1.
      destruct wf_entrypoints as [_ [J _]].
      unfold bound.
      destruct bs; tinv J.
      destruct b; subst. simpl. auto.

      apply GOOD in n0.
      apply Dominators.add_member2; auto.
Qed.

Theorem dom_entry_doms_others: forall res,
  DomDS.fixpoint _ (successors_blocks bs) transf entrypoints = Some res ->
  entry_doms_others res.
Proof.
  unfold DomDS.fixpoint. intros res PI. pattern res.
  eapply (PrimIter.iterate_prop _ _ (DomDS.step _ _ _)
    (fun st => entry_doms_others st.(DomDS.st_in _))); eauto.
  intros st GOOD. unfold DomDS.step.
  caseEq (AtomNodeSet.pick st.(DomDS.st_wrk _)); auto.
  intros [n rem] PICK.
  apply step_entry_doms_others; auto.
    apply start_entry_doms_others.
Qed.

Lemma dom_solution_ge: forall res,
  DomDS.fixpoint _ (successors_blocks bs) transf entrypoints = Some res ->
  forall n,
  Dominators.ge _ res!!n (lub_of_preds res n).
Proof.
  intros.
  apply Dominators.lubs_spec3.
  intros.
  apply in_map_iff in H0.
  destruct H0 as [x [J1 J2]]; subst.
  eapply DomDS.fixpoint_solution; eauto.
  apply make_predecessors_correct'; auto.
Qed.

End EntryDomsOthers.

End EntryDomsOthers.

(***************************)
(* domination prop *)

Fixpoint cmds_dominates_cmd (cs:cmds) (id0:id) : list atom :=
match cs with
| nil => nil
| c1::cs' =>
    let ctx := cmds_dominates_cmd cs' id0 in
    if eq_atom_dec (getCmdLoc c1) id0 then nil
    else
      match getCmdID c1 with
      | Some id1 => id1::ctx
      | None => ctx
      end
end.

Lemma NoDup__In_cmds_dominates_cmd : forall cs1 c cs2 id1,
  NoDup (getCmdsLocs (cs1 ++ c :: cs2)) ->
  In id1 (getCmdsIDs cs1) ->
  In id1 (cmds_dominates_cmd (cs1 ++ c :: cs2) (getCmdLoc c)).
Proof.
  induction cs1; intros; simpl in *.
    inversion H0.

    inv H.
    destruct (eq_atom_dec (getCmdLoc a) (getCmdLoc c)).
      assert (False) as F.
        apply H3.
        rewrite e.
        rewrite getCmdsLocs_app. simpl.
        apply in_or_app. right. simpl. auto.
      inversion F.

      destruct (getCmdID a); auto.
      simpl in *. destruct H0 as [H0 | H0]; auto.
Qed.

Definition inscope_of_block (f:fdef) (l1:l) (opt_ctx:option (list atom)) (lbl:l)
  :=
  match opt_ctx with
  | Some ctx =>
     match lookupBlockViaLabelFromFdef f lbl with
     | None => None
     | Some b =>
         if eq_atom_dec lbl l1 then Some ctx
         else Some (getBlockIDs b ++ ctx)
     end
  | None => None
  end.

Definition init_scope (f:fdef) (ps:phinodes) (cs:cmds) (id0:id) : list atom :=
if (in_dec id_dec id0 (getPhiNodesIDs ps)) then
  getArgsIDsOfFdef f
else 
  getPhiNodesIDs ps ++ cmds_dominates_cmd cs id0 ++ getArgsIDsOfFdef f.

Definition inscope_of_id (f:fdef) (b1:block) (id0:id) : option (list atom) :=
let '(block_intro l1 ps cs _) := b1 in
let 'dt := dom_analyze f in
let '(Dominators.mkBoundedSet els _) := AMap.get l1 dt in
fold_left (inscope_of_block f l1) els (Some (init_scope f ps cs id0))
.

Definition value_in_scope (v0:value) (ids0:ids) : Prop :=
match v0 with
| value_const _ => True
| value_id vid => In vid ids0
end.

Definition idDominates (f:fdef) (id1 id2: id) : Prop :=
match lookupBlockViaIDFromFdef f id2 with
| Some b2 =>
    match inscope_of_id f b2 id2 with
    | Some ids2 => In id1 ids2
    | None => False
    end
| None => False
end.

(* v1 >> v2 == id1 >> id2 \/ v1 is constant *)
Definition valueDominates (f:fdef) (v1 v2:value) : Prop :=
match v1, v2 with
| value_id id1, value_id id2 => idDominates f id1 id2
| value_const _, _ => True
| _, _ => False
end.

Definition inscope_of_cmd (f:fdef) (b1:block) (c:cmd) : option (list atom) :=
let id0 := getCmdLoc c in inscope_of_id f b1 id0.

Definition inscope_of_tmn (f:fdef) (b1:block) (tmn:terminator)
  : option (list atom) :=
let '(block_intro l1 ps cs _) := b1 in
let 'dt := dom_analyze f in
let '(Dominators.mkBoundedSet els _) := AMap.get l1 dt in
fold_left (inscope_of_block f l1) els
  (Some (getPhiNodesIDs ps ++ getCmdsIDs cs ++ getArgsIDsOfFdef f))
.

Definition defs_dominate (f:fdef) (curb incomingb:block) (i:insn)
  : option (list atom) :=
match i with
| insn_phinode p =>
    let '(block_intro _ _ _ tmn) := incomingb in
    inscope_of_tmn f incomingb tmn
| insn_cmd c => inscope_of_cmd f curb c
| insn_terminator tmn => inscope_of_tmn f curb tmn
end.

Lemma init_scope_spec1: forall f ps cs id0,
  ~ In id0 (getPhiNodesIDs ps) ->
  init_scope f ps cs id0 =
    getPhiNodesIDs ps ++ cmds_dominates_cmd cs id0 ++ getArgsIDsOfFdef f.
Proof.
  intros.
  unfold init_scope.
  destruct_if; try tauto.
Qed.

Lemma init_scope_spec2: forall f ps cs id2 id1
  (J1 : In id1 (init_scope f ps cs id2)) 
  (Hnotin2 : ~ In id1 (getArgsIDsOfFdef f)),
  In id1 (getPhiNodesIDs ps ++ cmds_dominates_cmd cs id2 ++ getArgsIDsOfFdef f).
Proof.
  unfold init_scope.
  intros.
  destruct_if; try tauto.
Qed.

Lemma getCmdsIDs__cmds_dominates_cmd : forall cs2' c',
  ~ In (getCmdLoc c') (getCmdsLocs cs2') ->
  set_eq _ (getCmdsIDs (cs2' ++ [c']))
  (cmds_dominates_cmd (cs2' ++ [c']) (getCmdLoc c') ++
    match getCmdID c' with
    | Some id1 => [id1]
    | None => nil
    end).
Proof.
  induction cs2'; intros c' Hnotin.
    simpl in *.
    destruct (eq_atom_dec (getCmdLoc c') (getCmdLoc c')) as [_ | n];
      try solve [contradict n; auto].
      remember (getCmdID c') as R.
      destruct R; simpl_env; apply set_eq_refl.

    simpl in *.
    assert (~ In (getCmdLoc c') (getCmdsLocs cs2')) as J.
      auto.
    apply IHcs2' in J.
    remember (getCmdID a) as R1.
    remember (getCmdID c') as R2.
    destruct (eq_atom_dec (getCmdLoc a) (getCmdLoc c'));
      try solve [contradict e; auto].
    destruct R1; auto.
      simpl_env.
      apply set_eq_app; auto using set_eq_refl.
Qed.

Definition opt_set_eq (ops1 ops2:option (list atom)) : Prop :=
match (ops1, ops2) with
| (None, None) => True
| (Some s1, Some s2) => set_eq _ s1 s2
| _ => False
end.

Lemma inscope_of_block__opt_set_eq : forall f l1 l' opr1 opr2,
  opt_set_eq opr1 opr2 ->
  opt_set_eq (inscope_of_block f l1 opr1 l') (inscope_of_block f l1 opr2 l').
Proof.
  unfold inscope_of_block.
  intros.
  destruct (lookupBlockViaLabelFromFdef f l').
    destruct (eq_atom_dec l' l1); subst.
      destruct opr1.
        destruct opr2; try solve [inversion H | auto].
        destruct opr2; try solve [inversion H | auto].
      unfold opt_set_eq in *.
      destruct opr1.
        destruct opr2; try solve [inversion H ].
          apply set_eq_app; auto using set_eq_refl.
        destruct opr2; try solve [inversion H | auto ].
    unfold opt_set_eq in *.
    destruct opr1.
      destruct opr2; try solve [inversion H | auto].
      destruct opr2; try solve [inversion H | auto].
Qed.

Lemma fold_left__opt_set_eq_aux : forall ls0 opr1 opr2 f l1,
  opt_set_eq opr1 opr2 ->
  opt_set_eq (fold_left (inscope_of_block f l1) ls0 opr1)
           (fold_left (inscope_of_block f l1) ls0 opr2).
Proof.
  induction ls0; intros opr1 opr2 f l1 Heq; simpl in *; auto.
    apply IHls0.
      apply inscope_of_block__opt_set_eq; auto.
Qed.

Lemma fold_left__opt_set_eq : forall (ls0:list atom) f l1 init1 init2 r1,
  set_eq _ init1 init2 ->
  fold_left (inscope_of_block f l1) ls0 (Some init1) = Some r1 ->
  exists r2, fold_left (inscope_of_block f l1) ls0 (Some init2) = Some r2 /\
    set_eq _ r1 r2.
Proof.
  intros.
  assert (opt_set_eq (Some init1) (Some init2)) as EQ. unfold opt_set_eq. auto.
  apply fold_left__opt_set_eq_aux with (ls0:=ls0)(f:=f)(l1:=l1) in EQ.
  remember (fold_left (inscope_of_block f l1) ls0 (ret init2)) as R.
  unfold opt_set_eq in EQ.
  rewrite H0 in EQ.
  destruct R; try solve [inversion EQ].
  exists l0. auto.
Qed.

Lemma inscope_of_block__opt_union : forall f l1 l' init1 init2 r1,
  inscope_of_block f l1 (Some init1) l' = Some r1 ->
  exists r2, inscope_of_block f l1 (Some (init1++init2)) l' = Some r2 /\
    set_eq _ (r1++init2) r2.
Proof.
  intros.
  unfold inscope_of_block in *.
  destruct (lookupBlockViaLabelFromFdef f l').
    destruct (eq_atom_dec l' l1); subst; inv H.
      exists (r1++init2). auto using set_eq_refl.
      exists (getBlockIDs b ++ init1 ++ init2).
        simpl_env. auto using set_eq_refl.
    inversion H.
Qed.

Lemma fold_left__none : forall (ls0:list atom) f l1,
  fold_left (inscope_of_block f l1) ls0 None = None.
Proof.
  induction ls0; intros f l1; simpl in *; auto.
Qed.

Lemma fold_left__opt_union : forall (ls0:list atom) f l1 init1 init2 r1,
  fold_left (inscope_of_block f l1) ls0 (Some init1) = Some r1 ->
  exists r2,
    fold_left (inscope_of_block f l1) ls0 (Some (init1++init2)) = Some r2
      /\ set_eq _ (r1++init2) r2.
Proof.
  induction ls0; intros f l1 init1 init2 r1 H; simpl in *; auto.
    inv H. exists (r1 ++ init2). split; auto using set_eq_refl.

    destruct (lookupBlockViaLabelFromFdef f a).
      destruct (eq_atom_dec a l1); subst; auto.
        apply IHls0 with (init2:=init2) in H; auto.
          simpl_env in H. auto.
      rewrite fold_left__none in H. inversion H.
Qed.

Lemma inscope_of_cmd_tmn : forall f l2 ps2 cs2' c' tmn' ids1
(Huniq: NoDup (getBlockLocs (block_intro l2 ps2 (cs2'++[c']) tmn'))),
Some ids1 = inscope_of_cmd f (block_intro l2 ps2 (cs2'++[c']) tmn') c' ->
exists ids2,
  Some ids2 = inscope_of_tmn f (block_intro l2 ps2 (cs2'++[c']) tmn') tmn' /\
  match getCmdID c' with
  | Some id1 => set_eq _ (id1::ids1) ids2
  | None => set_eq _ ids1 ids2
  end.
Proof.
  intros f l2 ps2 cs2' c' tmn' ids1 Huniq Hinscope.
  unfold inscope_of_cmd, inscope_of_id, init_scope in Hinscope.
  assert (~ In (getCmdLoc c') (getCmdsLocs cs2') /\
          ~ In (getCmdLoc c') (getPhiNodesIDs ps2)) as Hnotin.
    simpl in Huniq. 
    split.
      split_NoDup.
      solve_NoDup_notin.

      eapply NoDup_disjoint; eauto.
      apply in_or_app. left.
      solve_in_list.    
  destruct Hnotin as [Hnotin Hnotin'].
  destruct_if; try tauto.
  unfold inscope_of_tmn.
  destruct f as [[f t i0 la va] bs].
  remember ((dom_analyze (fdef_intro (fheader_intro f t i0 la va) bs)) !! l2) as R.
  destruct R as [R_contents R_bound]. simpl in *.
  apply getCmdsIDs__cmds_dominates_cmd in Hnotin.
  symmetry in H0.
  remember (getCmdID c') as R.
  destruct R.
    apply fold_left__opt_union with (init2:=[i1]) in H0.
    destruct H0 as [r2 [Hinscope Heq]].
    apply fold_left__opt_set_eq with (init2:=((getPhiNodesIDs ps2) ++
      ((getCmdsIDs (cs2' ++ [c'])) ++ (getArgsIDs la)))) in Hinscope.
      destruct Hinscope as [r3 [Hinscope Heq']].
      exists r3.
      split; auto.
        simpl_env.
        eapply set_eq_trans with (y:=r2); eauto.
        eapply set_eq_trans with (y:=ids1 ++ [i1]); eauto.
          apply set_eq_swap.
      simpl_env.
      apply set_eq_app; auto using set_eq_refl.
      apply set_eq_trans with (y:=(cmds_dominates_cmd (cs2' ++ [c'])
         (getCmdLoc c') ++ [i1]) ++ getArgsIDs la).
        simpl_env.
        apply set_eq_app; auto using set_eq_refl.
          apply set_eq_swap.

        apply set_eq_app; auto using set_eq_refl.
          apply set_eq_sym; auto.

    apply fold_left__opt_set_eq with (init2:=((getPhiNodesIDs ps2) ++
      ((getCmdsIDs (cs2' ++ [c'])) ++ (getArgsIDs la)))) in H0.
      destruct H0 as [r3 [Hinscope Heq']].
      exists r3.
      split; auto.
      apply set_eq_app; auto using set_eq_refl.
      apply set_eq_app; auto using set_eq_refl.
      simpl_env in Hnotin.
      apply set_eq_sym; auto.
Qed.

Lemma cmds_dominates_cmd__cmds_dominates_cmd : forall cs2' c' c cs',
  NoDup (getCmdsLocs (cs2'++[c']++[c]++cs')) ->
  set_eq _ (cmds_dominates_cmd (cs2' ++ c' :: c :: cs') (getCmdLoc c))
    (cmds_dominates_cmd (cs2' ++ c' :: c :: cs') (getCmdLoc c') ++
     match getCmdID c' with
     | Some id1 => [id1]
     | None => nil
     end).
Proof.
  induction cs2'; intros c' c cs' Hnodup.
    simpl in *.
    inv Hnodup. simpl in H1.
    remember (getCmdID c') as R.
    destruct (eq_atom_dec (getCmdLoc c') (getCmdLoc c)).
      contradict e; auto.

      destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [_|n1];
        try solve [contradict n1; auto].
      destruct (eq_atom_dec (getCmdLoc c') (getCmdLoc c')) as [_|n2];
        try solve [contradict n2; auto].
      destruct R; auto using set_eq_refl.

    simpl in *.
    inv Hnodup.
    rewrite getCmdsLocs_app in H1.
    apply NotIn_inv in H1.
    destruct H1 as [H11 H12].
    simpl in H12.
    destruct (eq_atom_dec (getCmdLoc a) (getCmdLoc c)) as [e1 | ];
      try solve [contradict e1; auto].
    destruct (eq_atom_dec (getCmdLoc a) (getCmdLoc c')) as [e1 | ];
      try solve [contradict e1; auto].
    destruct (getCmdID a); auto.
      apply IHcs2' in H2. clear IHcs2'.
      simpl_env.
       apply set_eq_app; auto using set_eq_refl.
Qed.

Lemma inscope_of_cmd_cmd : forall f l2 ps2 cs2' c' c cs' tmn' ids1
(Huniq: NoDup (getBlockLocs (block_intro l2 ps2 (cs2'++[c']++[c]++cs') tmn')))
(Hinscope: Some ids1 = 
           inscope_of_cmd f (block_intro l2 ps2 (cs2'++[c']++[c]++cs') tmn') c'),
exists ids2,
  Some ids2 =
    inscope_of_cmd f (block_intro l2 ps2 (cs2'++[c']++[c]++cs') tmn') c /\
  match getCmdID c' with
  | Some id1 => set_eq _ (id1::ids1) ids2
  | None => set_eq _ ids1 ids2
  end.
Proof.
  intros f l2 ps2 cs2' c' c cs' tmn' ids1 Huniq Hinscope.
  unfold inscope_of_cmd, inscope_of_id, init_scope in Hinscope.
  unfold inscope_of_cmd, inscope_of_id, init_scope.
  assert (NoDup (getCmdsLocs (cs2'++[c']++[c]++cs'))) as Hnodup.
    simpl in Huniq. split_NoDup. auto.
  assert (~ In (getCmdLoc c) (getPhiNodesIDs ps2) /\
          ~ In (getCmdLoc c') (getPhiNodesIDs ps2)) as Hnotin.
    simpl in Huniq. 
    split; eapply NoDup_disjoint; try solve 
             [eauto | apply in_or_app; left; solve_in_list].
  destruct_if; try tauto.
  destruct_if; try tauto. clear Hnotin.
  destruct f as [[f t i0 la va] bs].
  remember ((dom_analyze (fdef_intro (fheader_intro f t i0 la va) bs)) !! l2) as R.
  destruct R as [R_contents R_bound].
  apply cmds_dominates_cmd__cmds_dominates_cmd in Hnodup. simpl in *.
  symmetry in H0.
  remember (getCmdID c') as R.
  destruct R.
    apply fold_left__opt_union with (init2:=[i1]) in H0.
    destruct H0 as [r2 [Hinscope Heq]].
    apply fold_left__opt_set_eq with (init2:=((getPhiNodesIDs ps2) ++
      ((cmds_dominates_cmd (cs2' ++ c' :: c :: cs') (getCmdLoc c)) ++
      (getArgsIDs la)))) in Hinscope.
      destruct Hinscope as [r3 [Hinscope Heq']].
      exists r3.
      split; auto.
        simpl_env.
        eapply set_eq_trans with (y:=r2); eauto.
        eapply set_eq_trans with (y:=ids1 ++ [i1]); eauto.
          apply set_eq_swap.
      simpl_env.
      apply set_eq_app; auto using set_eq_refl.
      apply set_eq_trans with (y:=(cmds_dominates_cmd (cs2' ++ [c']++[c]++cs')
         (getCmdLoc c') ++ [i1]) ++ getArgsIDs la).
        simpl_env.
        apply set_eq_app; auto using set_eq_refl.
          apply set_eq_swap.

        apply set_eq_app; auto using set_eq_refl.
          apply set_eq_sym; auto.

    apply fold_left__opt_set_eq with (init2:=((getPhiNodesIDs ps2) ++
      ((cmds_dominates_cmd (cs2' ++ c' :: c :: cs') (getCmdLoc c)) ++
      (getArgsIDs la)))) in H0.
      destruct H0 as [r3 [Hinscope Heq']].
      exists r3.
      split; auto.
      apply set_eq_app; auto using set_eq_refl.
      apply set_eq_app; auto using set_eq_refl.
      simpl_env in Hnodup.
      apply set_eq_sym; auto.
Qed.

Lemma inc__getLabel2Block_blocks : forall a bs
  (Hinc : incl [a] (bound_blocks bs)),
  exists b : block, lookupAL block (genLabel2Block_blocks bs) a = Some b.
Proof.
  intros.
  induction bs as [|a0 bs]; simpl in *; auto.
    assert (J:=@Hinc a). simpl in J. destruct J; auto.
    destruct a0 as [l0 p c t]; simpl in *.
    destruct (a==l0); subst.
      exists (block_intro l0 p c t). auto.

      apply IHbs. intros x J.
      assert (x=a) as EQ.
        simpl in J. destruct J; auto. inversion H.
      subst.
      apply Hinc in J. simpl in J.
      destruct J as [J | J]; subst; auto.
      contradict n; auto.
Qed.

Lemma fold_left__bound_blocks : forall ls0 fh bs l0 init,
  incl ls0 (bound_blocks bs) ->
  exists r,
    fold_left (inscope_of_block (fdef_intro fh bs) l0) ls0 (Some init) = Some r.
Proof.
  induction ls0; intros fh bs l0 init Hinc; simpl in *.
    exists init. auto.

    assert (incl ls0 (bound_blocks bs)) as J.
      simpl_env in Hinc.
      eapply incl_app_invr; eauto.
    assert (exists b, lookupAL block (genLabel2Block_blocks bs) a = Some b)
      as Hlkup.
      clear - Hinc.
      simpl_env in Hinc.
      apply incl_app_invl in Hinc.
      apply inc__getLabel2Block_blocks; auto.

    destruct Hlkup as [b Hlkup].
    rewrite Hlkup.
    destruct (eq_atom_dec a l0); subst; auto.
Qed.

Lemma fold_left__spec : forall ls0 l0 init r f,
  fold_left (inscope_of_block f l0) ls0 (Some init) = Some r ->
    incl init r /\
    (forall l1 b1,
      In l1 (ListSet.set_diff eq_atom_dec ls0 [l0]) ->
      lookupBlockViaLabelFromFdef f l1 = Some b1 ->
      incl (getBlockIDs b1) r) /\
    (forall id1,
      In id1 r ->
      In id1 init \/
      exists b1, exists l1, In l1 (ListSet.set_diff eq_atom_dec ls0 [l0]) /\
        lookupBlockViaLabelFromFdef f l1 = Some b1 /\
        In id1 (getBlockIDs b1)
    ).
Proof.
  induction ls0; intros l0 init r f Hfold; simpl in *.
    inv Hfold.
    split. apply incl_refl.
    split; auto.
      intros ? ? Hfalse. inversion Hfalse.

    remember (lookupBlockViaLabelFromFdef f a) as R.
    destruct R.
      destruct (eq_atom_dec a l0); subst; auto.
      apply IHls0 in Hfold.
      destruct Hfold as [J1 [J2 J3]].
      split.
        eapply incl_app_invr; eauto.
      split.
        intros l1 b1 Hin Hlkup.
        apply ListSet.set_add_elim in Hin.
        destruct Hin as [Hin | Hin]; subst; eauto.
          rewrite Hlkup in HeqR. inv HeqR.
          eapply incl_app_invl; eauto.
        intros id1 Hin.
        apply J3 in Hin.
        destruct Hin as [Hin | [b1 [l1 [H1 [H2 H3]]]]].
          apply in_app_or in Hin.
          destruct Hin as [Hin | Hin]; auto.
          right.
          exists b. exists a.
          split; auto.
            apply ListSet.set_add_intro; auto.

          right.
          exists b1. exists l1.
          split; auto.
            apply ListSet.set_add_intro; auto.

      rewrite fold_left__none in Hfold. inversion Hfold.
Qed.

Lemma cmds_dominates_cmd_spec : forall id2 id0 cs,
  In id2 (cmds_dominates_cmd cs id0) -> In id2 (getCmdsIDs cs).
Proof.
  induction cs; simpl; intros; auto.
    destruct (eq_atom_dec (getCmdLoc a) id0); subst.
      inv H.

      remember (getCmdID a) as R.
      symmetry in HeqR.
      destruct R; auto.
        apply getCmdLoc_getCmdID in HeqR.
        simpl in *.
        destruct H; auto.
Qed.

Lemma cmds_dominates_cmd_spec' : forall ids1 id2 cs id0,
  In id2 (ids1 ++ cmds_dominates_cmd cs id0) ->
  In id2 (ids1 ++ getCmdsIDs cs).
Proof.
  intros.
  apply in_app_or in H.
  apply in_or_app.
  destruct H as [H | H]; auto.
  right. eapply cmds_dominates_cmd_spec; eauto.
Qed.

Lemma insnDominates_spec4 : forall b i0 insn2,
  insnDominates i0 insn2 b -> In i0 (getBlockIDs b).
Proof.
  unfold insnDominates.
  destruct b. intros.
  destruct insn2; tinv H.
    destruct H as [[ps1 [p1 [ps2 [J1 J2]]]] |
                   [cs1 [c1 [cs2 [cs3 [J1 J2]]]]]]; subst; simpl.
      solve_in_list.

      apply in_or_app.
      right. apply InGetCmdsIDs_middle'; auto.

    destruct H as [[[cs1 [c1 [cs2 [J1 J2]]]] |
                    [ps1 [p1 [ps2 [J1 J2]]]]] Heq]; subst; simpl.
      apply in_or_app.
      right. apply InGetCmdsIDs_middle'; auto.

      solve_in_list.
Qed.

Lemma insnDominates_spec3 : forall F b i0 insn2,
  uniqFdef F ->
  blockInFdefB b F = true ->
  insnDominates i0 insn2 b ->
  lookupBlockViaIDFromFdef F i0 = ret b.
Proof.
  intros.
  eapply inGetBlockIDs__lookupBlockViaIDFromFdef; eauto.
  apply insnDominates_spec4 in H1; auto.
Qed.

Lemma cmds_dominates_cmd_inv: forall id2 cs id1,
  In id1 (getCmdsLocs cs) ->
  In id2 (cmds_dominates_cmd cs id1) ->
  exists cs1, exists c, exists cs2,
    cs = cs1 ++ c :: cs2 /\
    In id2 (getCmdsLocs cs1) /\
    getCmdLoc c = id1.
Proof.
  induction cs; simpl; intros.
    inv H0.

    destruct (eq_atom_dec (getCmdLoc a) id1); subst.
      inv H0.

      destruct H as [H | H]; subst.
        congruence.

        remember (getCmdID a) as R.
        destruct R.
          symmetry in HeqR.

          simpl in H0.
          destruct H0 as [H0 | H0]; subst.
            apply in_getCmdsLocs_inv in H.
            destruct H as [cs1 [c [cs2 [J1 J2]]]]; subst.
            exists (a::cs1). exists c. exists cs2.
            simpl. erewrite getCmdLoc_getCmdID; eauto.

            apply IHcs in H0; auto.
            destruct H0 as [cs1 [c [cs2 [J1 [J2 J3]]]]]; subst.
            exists (a::cs1). exists c. exists cs2.
            simpl. eauto.

          apply IHcs in H0; auto.
          destruct H0 as [cs1 [c [cs2 [J1 [J2 J3]]]]]; subst.
          exists (a::cs1). exists c. exists cs2.
          simpl. eauto.
Qed.

Lemma cmds_dominates_cmd_spec3: forall cs1 c cs2 id1,
  NoDup (getCmdsLocs (cs1 ++ c :: cs2)) -> getCmdLoc c = id1 ->
  cmds_dominates_cmd (cs1++c::cs2) id1 = getCmdsIDs cs1.
Proof.
  induction cs1; simpl; intros; subst.
    destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)); auto.
      congruence.

    destruct (eq_atom_dec (getCmdLoc a) (getCmdLoc c)); subst.
      inv H.
      rewrite e in H2.
      contradict H2. rewrite getCmdsLocs_app.
      apply in_or_app. simpl. auto.

      inv H.
      destruct (getCmdID a).
        eapply IHcs1 in H3; eauto.
        rewrite H3. auto.

        eapply IHcs1 in H3; eauto.
Qed.

Lemma cmds_dominates_cmd_spec5: forall cs id1,
  ~ In id1 (getCmdsLocs cs) ->
  cmds_dominates_cmd cs id1 = getCmdsIDs cs.
Proof.
  induction cs; simpl; intros; auto.
    destruct (eq_atom_dec (getCmdLoc a) id1); subst.
      contradict H. auto.

      remember (getCmdID a) as R.
      destruct R; auto.
      rewrite IHcs; auto.
Qed.

Lemma insnDominates_spec1 : forall c1 block',
  NoDup (getBlockLocs block') -> insnInBlockB (insn_cmd c1) block' ->
  ~ insnDominates (getCmdLoc c1) (insn_cmd c1) block'.
Proof.
  intros. intro J.
  unfold insnDominates in J.
  destruct block'.
  destruct J as [[ps1 [p1 [ps2 [J1 J2]]]] | [cs1 [c2 [cs2 [cs3 [J1 J2]]]]]];
    subst; simpl in *.
    apply NoDup_disjoint with (i0:=getPhiNodeID p1) in H; auto.
      apply H. apply InGetPhiNodesIDs_middle.
      rewrite J2. apply getCmdLoc_in_getCmdsLocs'; auto.

    apply getCmdLoc_getCmdID in J2.
    apply NoDup_inv in H. destruct H as [_ H].
    apply NoDup_inv in H. destruct H as [H _].
    rewrite_env ((cs1 ++ c2 :: cs2) ++ c1 :: cs3) in H.
    rewrite getCmdsLocs_app in H.
    apply NoDup_disjoint with (i0:=getCmdLoc c2) in H; auto.
      apply H. apply InGetCmdsLocs_middle.
      rewrite J2. simpl. auto.
Qed.

Lemma insnDominates_spec2 : forall c1 c2 block',
  NoDup (getBlockLocs block') ->
  insnInBlockB (insn_cmd c1) block' ->
  insnInBlockB (insn_cmd c2) block' ->
  insnDominates (getCmdLoc c1) (insn_cmd c2) block' ->
  ~ insnDominates (getCmdLoc c2) (insn_cmd c1) block'.
Proof.
  unfold insnDominates. destruct block'. intros.
  destruct H2 as [[ps1 [p1 [ps2 [J1 J2]]]] | [cs1 [c2' [cs2 [cs3 [J1 J2]]]]]];
    subst; simpl in *.
    apply NoDup_disjoint with (i0:=getPhiNodeID p1) in H; auto.
      contradict H. apply InGetPhiNodesIDs_middle.
      rewrite J2. apply getCmdLoc_in_getCmdsLocs'; auto.

    intros J.
    destruct J as [[ps3 [p4 [ps5 [J3 J4]]]] | [cs3' [c3 [cs4 [cs5 [J3 J4]]]]]];
      subst.
      apply NoDup_disjoint with (i0:=getPhiNodeID p4) in H; auto.
        contradict H. apply InGetPhiNodesIDs_middle.
        rewrite J4. apply getCmdLoc_in_getCmdsLocs'; auto.

      apply getCmdLoc_getCmdID in J2.
      apply getCmdLoc_getCmdID in J4.
      apply NoDup_inv in H. destruct H as [_ H].
      apply NoDup_inv in H. destruct H as [H _].
      assert (H':=H).
      apply InCmdsB_in in H0.
      apply getCmdsLocs_uniq with (c1:=c1)(c2:=c2') in H; auto using in_middle.
      rewrite J3 in H'.
      assert (H'':=H').
      apply getCmdsLocs_uniq with (c1:=c2)(c2:=c3) in H'; auto using in_middle.
        subst.
        rewrite <- J3 in H''.
        rewrite_env ((cs1 ++ c2' :: cs2) ++ c3 :: cs3) in J3.
        rewrite_env ((cs1 ++ c2' :: cs2) ++ c3 :: cs3) in H''.
        apply in_middle_inv in J3; auto.
        destruct J3 as [Heq1 Heq2]; subst.
        rewrite getCmdsLocs_app in H''.
        apply NoDup_disjoint with (i0:=getCmdLoc c2') in H''; auto.
          contradict H''. apply InGetCmdsLocs_middle.
          rewrite_env ((c3 :: cs4) ++ c2' :: cs5). apply InGetCmdsLocs_middle.

        rewrite <- J3. rewrite_env ((cs1 ++ c2' :: cs2) ++ c2 :: cs3).
        auto using in_middle.
Qed.

Lemma insnDominates_spec5: forall F1 b c instr,
  uniqFdef F1 ->
  blockInFdefB b F1 ->
  insnDominates (getCmdLoc c) instr b ->
  lookupBlockViaIDFromFdef F1 (getCmdLoc c) = Some b.
Proof.
  intros. eapply insnDominates_spec3; eauto.
Qed.

Lemma cmds_dominates_cmd__insnDominates: forall F1 c1 l0 p c0 t c
  (Huniq : uniqFdef F1)
  (H : insnInFdefBlockB (insn_cmd c1) F1 (block_intro l0 p c0 t) = true)
  (Hin' : In c c0) (Hsome: getCmdID c1 <> None)
  (Hin : In (getCmdLoc c1)
          (getPhiNodesIDs p ++ cmds_dominates_cmd c0 (getCmdLoc c))),
  insnDominates (getCmdLoc c1) (insn_cmd c) (block_intro l0 p c0 t).
Proof.
  simpl. intros.
  apply in_app_or in Hin.
  apply andb_true_iff in H.
  destruct H as [J1 J2].
  apply uniqFdef__uniqBlockLocs in J2; auto.
  simpl in J2.
  destruct Hin as [Hin | Hin].
    apply NoDup_disjoint' with (i0:=getCmdLoc c1) in J2; auto.
    contradict J2. apply in_or_app.
    apply InCmdsB_InCmdsLocs in J1; auto.
    assert (J3:=Hin').
    apply getCmdLoc_in_getCmdsLocs in Hin'.
    apply cmds_dominates_cmd_inv in Hin; auto.
    destruct Hin as [cs1 [c2 [cs2 [Heq [Hin J]]]]]; subst.

    apply NoDup_inv in J2. destruct J2 as [_ J2].
    apply NoDup_inv in J2. destruct J2 as [J2 _].
    apply InCmdsB_in in J1.
    assert (J2':=J2).
    apply getCmdsLocs_uniq with (c1:=c)(c2:=c2) in J2'; auto using in_middle.
    subst.
    apply nodup_getCmdsLocs_in_first with (c1:=c1) in J2; auto.
    apply in_split in J2. destruct J2 as [cs3 [c0 cs4]]; subst.
    right.
    exists cs3. exists c1. exists c0. exists cs2.
    rewrite getCmdID_getCmdLoc; auto. simpl_env. split; auto.
Qed.

Lemma fold_left__init : forall f l1 r ls0 init,
  fold_left (inscope_of_block f l1) ls0 (Some init) = Some r ->
  incl init r.
Proof.
  induction ls0; simpl; intros.
    inv H. apply incl_refl; auto.

    destruct (lookupBlockViaLabelFromFdef f a).
      destruct (eq_atom_dec a l1); subst; auto.
        apply IHls0 in H.
        intros x J. apply H. apply in_or_app. auto.

      rewrite fold_left__none in H. inv H.
Qed.

Lemma fold_left__intro: forall f (Huniq: uniqFdef f) l1 bs_contents l2 B
  r init,
  In l2 (ListSet.set_diff eq_atom_dec bs_contents [l1]) ->
  lookupBlockViaLabelFromFdef f l2 = ret B ->
  fold_left (inscope_of_block f l1) bs_contents (Some init) = Some r ->
  incl (getBlockIDs B) r.
Proof.
  induction bs_contents; simpl; intros.
    inv H.

    destruct (eq_atom_dec a l1); subst.
      remember (lookupBlockViaLabelFromFdef f l1) as R.
      destruct R; eauto.
        rewrite fold_left__none in H1. inv H1.

      apply ListSet.set_add_elim in H.
      destruct H as [H | H]; subst.
        rewrite H0 in H1.
        apply fold_left__init in H1.
        intros x J. apply H1. apply in_or_app. auto.

        remember (lookupBlockViaLabelFromFdef f a) as R.
        destruct R.
          eapply IHbs_contents in H1; eauto.
          rewrite fold_left__none in H1. inv H1.
Qed.

Lemma cmds_dominates_cmd_spec2: forall cs cs' id1,
  In id1 (getCmdsIDs cs) ->
  cmds_dominates_cmd (cs++cs') id1 = cmds_dominates_cmd cs id1.
Proof.
  induction cs; simpl; intros.
    inv H.

    destruct (eq_atom_dec (getCmdLoc a) id1); subst; auto.
    remember (getCmdID a) as R.
    destruct R; eauto.
      symmetry in HeqR.
      apply getCmdLoc_getCmdID in HeqR. subst.
      simpl in H.
      destruct H as [H | H]; subst; try congruence.
      rewrite IHcs; auto.
Qed.

Lemma cmds_dominates_cmd_spec'' : forall ids1 id2 cs id0 tl1 
  (Hnin: ~ In id2 tl1),
  In id2 (ids1 ++ cmds_dominates_cmd cs id0 ++ tl1) ->
  In id2 (ids1 ++ getCmdsIDs cs).
Proof.
  intros.
  rewrite_env ((ids1 ++ cmds_dominates_cmd cs id0) ++ tl1) in H.
  apply in_app_or in H.
  destruct H as [H | H]; try congruence.
  apply cmds_dominates_cmd_spec' in H. auto.
Qed.

Lemma idDominates__lookupBlockViaIDFromFdef : forall f id1 id2
  (Huniq: uniqFdef f) (Hnotin: ~ In id1 (getArgsIDsOfFdef f)),
  idDominates f id1 id2 ->
  exists b1, lookupBlockViaIDFromFdef f id1 = ret b1.
Proof.
  intros.
  unfold idDominates in H.
  remember (lookupBlockViaIDFromFdef f id2) as R.
  destruct R; tinv H.
  remember (inscope_of_id f b id2) as R.
  destruct R; tinv H.
  unfold inscope_of_id in HeqR0.
  destruct b.
  remember (Maps.AMap.get l1 (dom_analyze f)) as R.
  destruct R. destruct f as [[fa ty fid la va] bs].
  symmetry in HeqR0.
  apply fold_left__spec in HeqR0.
  destruct HeqR0 as [J1 [J2 J3]].
  apply J3 in H.
  destruct H as [H | [b2 [l2 [H1 [H2 H3]]]]].
    unfold init_scope in H.
    simpl in H.
    destruct_if; try tauto.
    exists (block_intro l1 p c t).
    symmetry in HeqR.
    apply lookupBlockViaIDFromFdef__blockInFdefB in HeqR.
    apply inGetBlockIDs__lookupBlockViaIDFromFdef; auto.
    simpl. eapply cmds_dominates_cmd_spec''; eauto.
    
    exists b2.
    apply lookupBlockViaLabelFromFdef__blockInFdefB in H2; auto.
    apply inGetBlockIDs__lookupBlockViaIDFromFdef; auto.
Qed.

Lemma idDominates__blockDominates : forall f b1 b2 id1 id2
  (Hdom : idDominates f id1 id2) (HuniqF: uniqFdef f) 
  (Hnotin: ~ In id1 (getArgsIDsOfFdef f))
  (H : lookupBlockViaIDFromFdef f id2 = ret b2)
  (J : lookupBlockViaIDFromFdef f id1 = ret b1),
  blockDominates f b1 b2.
Proof.
  unfold idDominates, blockDominates in *. intros.
  rewrite H in Hdom.
  remember (inscope_of_id f b2 id2) as R2.
  destruct R2; tinv Hdom.
  unfold inscope_of_id in *.
  destruct b1. destruct b2.
  remember (Maps.AMap.get l2 (dom_analyze f)) as R.
  destruct R. destruct f as [[fa ty fid la va] bs].
  symmetry in HeqR2.
  apply fold_left__spec in HeqR2.
  destruct HeqR2 as [J1 [J2 J3]].
  apply J3 in Hdom.
  destruct Hdom as [Hdom | [b1 [l1' [H4 [H5 H6]]]]].
    unfold init_scope in Hdom.
    destruct_if; try tauto.
    right.
    apply lookupBlockViaIDFromFdef__blockInFdefB in H.
    apply block_eq1 with (b2:=block_intro l2 p0 c0 t0) in J; eauto.
      inv J; auto.
      simpl. eapply cmds_dominates_cmd_spec''; eauto.

    left.
    assert (block_intro l1 p c t = b1 /\ l1' = l1) as J'.
      destruct b1. apply lookupBlockViaLabelFromFdef_inv in H5; auto.
      destruct H5 as [Heq H5]; subst.
      clear - H6 J HuniqF H5.
      eapply block_eq1 in J; eauto. inv J; auto.
    destruct J' as [Heq1 Heq2]; subst.
    apply ListSet.set_diff_elim1 in H4; auto.
Qed.

Lemma idDominates__lookupTypViaIDFromFdef : forall f id1 id2 (Huniq: uniqFdef f),
  idDominates f id1 id2 ->
  exists t, lookupTypViaIDFromFdef f id1 = ret t.
Proof.
  unfold idDominates. intros.
  remember (lookupBlockViaIDFromFdef f id2) as R.
  destruct R; tinv H.
  remember (inscope_of_id f b id2) as R.
  destruct R; tinv H.
  unfold inscope_of_id in HeqR0.
  destruct b as [l1 ps cs tmn].
  destruct f as [[fa ty fid la va] bs].
  remember (Maps.AMap.get l1 
    (dom_analyze (fdef_intro (fheader_intro fa ty fid la va) bs))) as R.
  destruct R.
  symmetry in HeqR0.
  apply fold_left__spec in HeqR0.
  destruct HeqR0 as [J1 [J2 J3]].
  apply J3 in H.
  destruct H as [H | [b2 [l2 [H1 [H2 H3]]]]].
    unfold init_scope in H.
    destruct_if.
      eapply InArgsIDs_lookupTypViaIDFromFdef; eauto.

      symmetry in HeqR.
      apply lookupBlockViaIDFromFdef__blockInFdefB in HeqR.
      rewrite_env ((getPhiNodesIDs ps ++ cmds_dominates_cmd cs id2) 
                   ++ getArgsIDs la) in H.
      apply in_app_or in H.
      destruct H as [H | H].
        eapply inGetBlockLocs__lookupTypViaIDFromFdef in HeqR; eauto.
        simpl. 
        apply cmds_dominates_cmd_spec' in H.
          solve_in_list.

          eapply InArgsIDs_lookupTypViaIDFromFdef; eauto.

    apply lookupBlockViaLabelFromFdef__blockInFdefB in H2; auto.
    eapply inGetBlockLocs__lookupTypViaIDFromFdef in H2; eauto.
      solve_in_list.
Qed.

Lemma idDominates_insnDominates__blockDominates : forall f id1 id2 b1 b instr
  (Hnotin: ~ In id1 (getArgsIDsOfFdef f)),
  idDominates f id1 id2 ->
  lookupBlockViaIDFromFdef f id1 = ret b1 ->
  insnDominates id2 instr b ->
  blockInFdefB b f = true ->
  uniqFdef f ->
  blockDominates f b1 b.
Proof.
  intros. eapply idDominates__blockDominates; eauto.
  destruct b. eapply insnDominates_spec3 in H1; eauto.
Qed.

Lemma insnDominates_trans: forall id1 p c t id2 l1 instr f
  (G : ~ In id1 (getArgsIDsOfFdef f))
  (H : In id1 (init_scope f p c id2))
  (H3 : NoDup (getBlockLocs (block_intro l1 p c t)))
  (H1 : insnDominates id2 instr (block_intro l1 p c t)),
  insnDominates id1 instr (block_intro l1 p c t).
Proof.
  intros.
  unfold init_scope in H.
  destruct_if; try tauto.
  apply in_app_or in H.
  destruct H as [H | H]; simpl in *.
  Case "id1 in p".
    destruct instr; auto.
      left. apply in_getPhiNodesIDs_inv; auto.

      destruct H1 as [H1 Heq]; subst.
      split; auto.
      right. apply in_getPhiNodesIDs_inv; auto.

  apply in_app_or in H.
  destruct H as [H | H]; simpl in *; try tauto.
  Case "id1 in cs".
    destruct instr; auto.
    SCase "instr=cmd".
      right.
      destruct H1 as [[ps1 [p1 [ps2 [J1 J2]]]] |
                      [cs1 [c1 [cs2 [cs3 [J1 J2]]]]]]; subst; simpl.
      SSCase "p >> cmd".
        clear HeqR. contradict n. solve_in_list.
      SSCase "cmd >> cmd".
        split_NoDup.
        rewrite cmds_dominates_cmd_spec3 in H; eauto using getCmdID__getCmdLoc.
        apply in_getCmdsIDs_inv in H.
        destruct H as [cs6 [c3 [cs7 [J6 J7]]]]; subst.
        exists cs6. exists c3. exists (cs7 ++ c1 :: cs2). exists cs3.
        simpl_env. split; auto.

    SCase "instr=tmn".
      destruct H1 as [[[cs1 [c1 [cs2 [J1 J2]]]] |
                       [ps1 [p1 [ps2 [J1 J2]]]]] Heq]; subst; simpl.
      SSCase "cmd >> tmn".
        split_NoDup.
        rewrite cmds_dominates_cmd_spec3 in H; eauto using getCmdID__getCmdLoc.
        apply in_getCmdsIDs_inv in H.
        destruct H as [cs6 [c3 [cs7 [J6 J7]]]]; subst.
        split; auto. left.
        exists cs6. exists c3. exists (cs7 ++ c1 :: cs2).
        simpl_env. split; auto.
      SSCase "p >> tmn".
        clear HeqR. contradict n. solve_in_list.
Qed.

Lemma idDominates_insnDominates__insnDominates : forall f id1 id2 b instr
  (Hnotin: ~ In id1 (getArgsIDsOfFdef f))
  (H: idDominates f id1 id2)
  (H0: lookupBlockViaIDFromFdef f id1 = ret b)
  (H1: insnDominates id2 instr b)
  (H2: blockInFdefB b f = true)
  (H3: uniqFdef f),
  insnDominates id1 instr b.
Proof.
  intros.
  unfold idDominates in H.
  inv_mbind. symmetry_ctx.
  unfold inscope_of_id in *.
  destruct b0 as [l1 p c t].
  remember ( (dom_analyze f) !! l1) as R.
  destruct R.
  apply fold_left__spec in HeqR0.
  destruct HeqR0 as [J1 [J2 J3]].
  apply J3 in H.
  destruct H as [H | [b2 [l2 [H1' [H2' H3']]]]].
    assert (b = block_intro l1 p c t) as EQ.
      eapply block_eq1 with (id0:=id1); eauto 1.
        solve_blockInFdefB.

        unfold init_scope in H.
        destruct_if.
          clear HeqR0.
          contradict H. auto.
          
          simpl.
          eapply cmds_dominates_cmd_spec''; eauto.
    subst.  
    eapply insnDominates_trans; eauto.
      solve_NoDup.

    eapply insnDominates_spec3 in H1; eauto.
    uniq_result.
    destruct b2 as [l3 p0 c0 t0].
    apply lookupBlockViaLabelFromFdef_inv in H2'; auto.
    destruct H2' as [Heq H2']; subst.
    apply block_eq1 with (b2:=block_intro l3 p0 c0 t0) in H0; auto.
    inv H0.
    apply ListSet.set_diff_elim2 in H1'.
    contradict H1'; simpl; auto.
Qed.

Lemma idDominates_insnDominates__insnOrBlockStrictDominates :
forall f id1 id2 b1 b instr
  (Hnotin: ~ In id1 (getArgsIDsOfFdef f)),
  idDominates f id1 id2 ->
  lookupBlockViaIDFromFdef f id1 = ret b1 ->
  insnDominates id2 instr b ->
  blockInFdefB b f = true ->
  uniqFdef f ->
  insnDominates id1 instr b \/ blockStrictDominates f b1 b.
Proof.
  intros.
  assert (H1':=H1).
  eapply idDominates_insnDominates__blockDominates in H1; eauto.
  destruct b1, b.
  destruct (l_dec l0 l1); subst.
    left.
    assert (block_intro l1 p c t = block_intro l1 p0 c0 t0) as EQ.
      apply lookupBlockViaIDFromFdef__blockInFdefB in H0.
      eapply blockInFdefB_uniq with (ps1:=p) in H2; eauto.
      destruct H2 as [A [B C]]; subst; auto.
    inv EQ.
    eapply idDominates_insnDominates__insnDominates in H0; eauto.

    right.
    unfold blockStrictDominates.
    unfold blockDominates in H1.
    destruct (Maps.AMap.get l1 (dom_analyze f)).
    destruct H1; subst; auto.
      congruence.
Qed.

Lemma inscope_of_id__idDominates : forall l0 f b2 id2 i0
  (HeqR0 : ret l0 = inscope_of_id f b2 id2) (Hin: In i0 l0)
  (Hlk : lookupBlockViaIDFromFdef f id2 = ret b2),
  idDominates f i0 id2.
Proof.
  intros. unfold idDominates. rewrite Hlk. rewrite <- HeqR0. auto.
Qed.

Lemma cmd_in_scope__block_in_scope: forall (l' : l) (F : fdef) 
  (ids0' ids1 : list atom) (HuniqF : uniqFdef F) (contents' : ListSet.set atom)
  (inbound' : incl contents' (bound_fdef F))
  (Heqdefs' : {| DomDS.L.bs_contents := contents';
                 DomDS.L.bs_bound := inbound' |} = (dom_analyze F) !! l')
  (Hinscope : fold_left (inscope_of_block F l') contents' (ret ids1) = ret ids0')
  (id1 : atom) (Hid1 : In id1 ids0') (Hnotin' : ~ In id1 ids1) insn1
  (Hlkc1 : lookupInsnViaIDFromFdef F id1 = ret insn1)
  (l0 : l) (p : phinodes) (c : cmds) (t0 : terminator)
  (H : insnInFdefBlockB insn1 F (block_intro l0 p c t0) = true),
  In l0 contents'.
Proof.
  intros. 
  apply fold_left__spec in Hinscope.
  destruct Hinscope as [_ [_ Hinscope]].
  apply Hinscope in Hid1.
  destruct Hid1 as [Hid1 | [b1 [l1 [J1 [J2 J3]]]]]; try congruence.
  destruct b1.
  assert (l1 = l2) as EQ.
    apply lookupBlockViaLabelFromFdef_inv in J2; auto.
    destruct J2; auto.
  subst.
  eapply lookupBlockViaLabelFromFdef__lookupBlockViaIDFromFdef in J2;
    eauto.
  eapply lookupInsnViaIDFromFdef_lookupBlockViaIDFromFdef__getInsnID in Hlkc1;
    eauto.
  eapply insnInFdefBlockB__lookupBlockViaIDFromFdef in H; 
    try solve [eauto | congruence].
  erewrite getInsnID__getInsnLoc in H; eauto.
  uniq_result.
  apply ListSet.set_diff_elim1 in J1; auto.
Qed.

Lemma domination__block_in_scope: forall (l' : l) (ps' : phinodes) (cs' : cmds)
  (F : fdef) (tmn' : terminator) (HwfF : uniqFdef F) (c1 : cmd) (i0 : atom) 
  (l0 : l) (p : phinodes) (c : cmds) (t0 : terminator)
  (Hreachb1 : isReachableFromEntry F (block_intro l0 p c t0))
  (H5 : lookupBlockViaIDFromFdef F i0 = ret block_intro l' ps' cs' tmn')
  (H7 : insnDominates i0 (insn_cmd c1) (block_intro l0 p c t0) \/
        blockStrictDominates F (block_intro l' ps' cs' tmn')
          (block_intro l0 p c t0) \/
        ~ isReachableFromEntry F (block_intro l0 p c t0))
  (Hneq : l0 <> l')
  (HbInF0 : blockInFdefB (block_intro l0 p c t0) F = true),
  In l' (DomDS.L.bs_contents (bound_fdef F) (dom_analyze F) !! l0).
Proof.
  intros.
  destruct H7 as [H7 | [H7 | H7]]; try congruence.
    apply insnDominates_spec3 with (F:=F) in H7; auto.
    rewrite H7 in H5. inv H5. congruence.
  
    clear - H7.
    unfold blockStrictDominates in H7.
    destruct ((dom_analyze F) !! l0); simpl; auto.
Qed.

Lemma insnDominates_spec6: forall (l1 : l) (ps1 : phinodes) (cs1 : cmds)
  (tmn1 : terminator) (id1 : id) tl
  (J' : insnDominates id1 (insn_terminator tmn1) (block_intro l1 ps1 cs1 tmn1)),
  In id1 (getPhiNodesIDs ps1 ++ getCmdsIDs cs1 ++ tl).
Proof.
  intros.  
  destruct J' as [J' _].
  destruct J' as [[cs2 [c1' [cs3 [J1 J2]]]] | [ps2 [p1 [ps3 [J1 J2]]]]];
    subst.
    rewrite getCmdsIDs_app. simpl. rewrite J2.
    apply in_or_app. right.
    apply in_or_app. left.
    apply in_or_app. right. simpl. auto.
    
    rewrite getPhiNodesIDs_app. simpl.
    apply in_or_app. left.
    apply in_or_app. right. simpl. auto.
Qed.

Lemma inscope_of_tmn__inscope_of_cmd_at_beginning: forall f (l3 : l) 
  (ps : phinodes) (cs : cmds) 
  (tmn : terminator) (ids0 : list atom) (l' : l) (ps' : phinodes)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (contents3 : ListSet.set atom)
  init (Heq: init = getArgsIDsOfFdef f)
  (Hinscope : ret ids0 =
             fold_left (inscope_of_block f l3) contents3
               (ret (getPhiNodesIDs ps ++ getCmdsIDs cs ++ init)))
  (Huniq : uniqFdef f)
  (contents' : ListSet.set atom)
  (Hsub : incl contents' (l3 :: contents3))
  (r : list atom)
  (J1 : fold_left (inscope_of_block f l') contents'
         (ret (getPhiNodesIDs ps' ++ init)) = ret r),
  incl (ListSet.set_diff eq_atom_dec r (getPhiNodesIDs ps')) ids0.
Proof.
  intros.
  apply fold_left__spec in J1.
  symmetry in Hinscope.
  apply fold_left__spec in Hinscope.
  destruct J1 as [J1 [J2 J3]].
  destruct Hinscope as [J4 [J5 J6]].
  intros id1 J.
  assert (J':=J).
  apply ListSet.set_diff_elim1 in J.
  apply ListSet.set_diff_elim2 in J'.
  apply J3 in J.
  destruct J as [J | J].
  SCase "id1 in init and the current block".
    simpl in J.
    apply in_app_or in J.
    destruct J as [J | J]; try solve [contradict J; auto].
    apply J4.
    apply in_or_app. right.
    apply in_or_app; auto.
  SCase "id1 in strict dominating blocks".
    destruct J as [b1 [l1 [J8 [J9 J10]]]].
    assert (In l1 contents') as J8'.
      clear - J8.
      apply ListSet.set_diff_elim1 in J8. auto.
    apply Hsub in J8'.
      destruct (eq_atom_dec l1 l3); subst.
        simpl in J9.
        assert (b1=block_intro l3 ps cs tmn) as EQ.
          clear - J9 HBinF Huniq. 
          eapply blockInFdefB__lookupBlockViaLabelFromFdef; eauto.
        subst.
        simpl in J10.
        apply J4.
        rewrite_env
          ((getPhiNodesIDs ps ++ getCmdsIDs cs) ++ getArgsIDsOfFdef f).
        apply in_or_app; auto.
  
        apply J5 in J9; auto.
          simpl in J8'.
          destruct J8' as [J8' | J8']; try solve [contradict n; auto].
          apply ListSet.set_diff_intro; auto.
            intro J. simpl in J.
            destruct J as [J | J]; auto.
Qed.

Lemma cmds_dominates_cmd_trans : forall id1 id2 R1 R2 cs1 c cs
  (G: In id1 (getCmdsLocs (cs1 ++ c :: cs))),
  NoDup (R1 ++ getCmdsLocs (cs1 ++ c :: cs)) ->
  In id1 (R1 ++
          cmds_dominates_cmd (cs1 ++ c :: cs) (getCmdLoc c)) ->
  In id2 (R1 ++
          cmds_dominates_cmd (cs1 ++ c :: cs) id1 ++ R2) ->
  In id2 (R1 ++
          cmds_dominates_cmd (cs1 ++ c :: cs) (getCmdLoc c) ++ R2).
Proof.
  intros.
  solve_in_list.
  apply in_app_or in H0.
  destruct H0 as [H0 | H0].
    eapply NoDup_disjoint' in H; eauto.
    apply cmds_dominates_cmd_inv in H1; auto.
    destruct H1 as [cs2 [c0 [cs3 [J1 [J2 J3]]]]]; subst.
    rewrite J1 in H.
    contradict H. apply getCmdLoc_in_getCmdsLocs. apply in_middle.

    apply NoDup_inv in H. destruct H as [J1 J2].
    rewrite cmds_dominates_cmd_spec3 in H0; auto.
    rewrite cmds_dominates_cmd_spec2 with (cs:=cs1) in H1; auto.
    rewrite cmds_dominates_cmd_spec3; auto.
    apply cmds_dominates_cmd_spec in H1; auto.
Qed.

Lemma cmds_dominates_cmd_inscope_of_cmd__inscope_of_cmd: forall 
  (f : fdef) (t : list atom) (l1 : l) (ps1 : phinodes) (cs1 : cmds)
  (cs : cmds) (tmn1 : terminator) id1 (c : cmd) (id2 : id)
  (HwfF : uniqFdef f) (bs_contents : ListSet.set atom)
  (HbInF : blockInFdefB (block_intro l1 ps1 (cs1 ++ c :: cs) tmn1) f = true)
  (l2 : l) (p : phinodes) (c2 : cmds) (t0 : terminator)
  (HeqR1 : ret block_intro l2 p c2 t0 = lookupBlockViaIDFromFdef f id2)
  init (Heq: init = getArgsIDsOfFdef f)
  (J1:In id1 (init_scope f p c2 id2)) (Hnotin: ~ In id1 init)
  instr0 (HeqR0 : ret instr0 = lookupInsnViaIDFromFdef f id2)
  (J12 : In id2
          (getPhiNodesIDs ps1 ++
           cmds_dominates_cmd (cs1 ++ c :: cs) (getCmdLoc c)))
  (HeqR' : fold_left (inscope_of_block f l1) bs_contents
             (ret (getPhiNodesIDs ps1 ++
                   cmds_dominates_cmd (cs1 ++ c :: cs) (getCmdLoc c) ++ init)) =
           ret t),
  In id1 t.
Proof.
  intros.
  assert (block_intro l2 p c2 t0 =
          block_intro l1 ps1 (cs1 ++ c :: cs) tmn1) as EQ.
    eapply block_eq1 with (id0:=id2); eauto.
      simpl. eapply cmds_dominates_cmd_spec' with (id0:=getCmdLoc c); eauto.
  inv EQ.
  apply fold_left__init in HeqR'.
  apply HeqR'; auto.
    unfold init_scope in J1.
    destruct_if; try tauto.
    eapply cmds_dominates_cmd_trans; eauto.
      apply cmds_dominates_cmd_spec' in J12.
      solve_in_list.
  
      apply uniqFdef__uniqBlockLocs in HbInF; auto.
      simpl in HbInF.
      rewrite_env ((getPhiNodesIDs ps1 ++
         getCmdsLocs (cs1 ++ c :: cs)) ++ getTerminatorID tmn1 :: nil)
      in HbInF.
      apply NoDup_inv in HbInF. destruct HbInF; auto.
Qed.

Lemma cmds_dominates_cmd_inscope_of_block__inscope_of_block: forall 
  (f : fdef) (t : list atom) (l1 : l) (ps1 : phinodes) (cs1 : cmds)
  id1 (id2 : id) (HwfF : uniqFdef f)
  (bs_contents : ListSet.set atom)
  (l2 : l) (p : phinodes) (c2 : cmds) (t0 : terminator)
  (HeqR1 : ret block_intro l2 p c2 t0 = lookupBlockViaIDFromFdef f id2)
  (J1 : In id1 (getPhiNodesIDs p ++ cmds_dominates_cmd c2 id2))
  (b2 : block) (l2' : atom)
  (J13 : In l2' (ListSet.set_diff eq_atom_dec bs_contents [l1]))
  (J14 : lookupBlockViaLabelFromFdef f l2' = ret b2)
  (J15 : In id2 (getBlockIDs b2)) init
  (HeqR' : fold_left (inscope_of_block f l1) bs_contents (ret init) = ret t),
  In id1 t.
Proof.
  intros.
  assert (block_intro l2 p c2 t0 = b2) as EQ.
    clear - HwfF HeqR1 J14 J15.
    apply lookupBlockViaLabelFromFdef__blockInFdefB in J14; auto.
    eapply block_eq1 with (id0:=id2); eauto.
  subst.
  assert (In id1 (getBlockIDs (block_intro l2 p c2 t0))) as Hin'.
    clear - J1. simpl. eapply cmds_dominates_cmd_spec'; eauto.
  apply fold_left__intro with (l2:=l2')(B:=block_intro l2 p c2 t0) in HeqR';
    auto.
Qed.

Lemma inscope_of_block_cmds_dominates_cmd__inscope_of_cmd: forall
  (f : fdef) (t : list atom) (l1 : l) (ps1 : phinodes) (cs1 : cmds) (cs : cmds)
  (tmn1 : terminator) id1 (c : cmd) (id2 : id) (HwfF : uniqFdef f)
  (bs_contents : ListSet.set atom)
  (bs_bound : incl bs_contents (bound_fdef f))
  (HeqR3 : {| DomDS.L.bs_contents := bs_contents;
              DomDS.L.bs_bound := bs_bound |} = (dom_analyze f) !! l1)
  (HbInF : blockInFdefB (block_intro l1 ps1 (cs1 ++ c :: cs) tmn1) f = true)
  (l2 : l) (p : phinodes) (c2 : cmds) (t0 : terminator)
  (HeqR1 : ret block_intro l2 p c2 t0 = lookupBlockViaIDFromFdef f id2)
  (bs_contents0 : ListSet.set atom)
  (bs_bound0 : incl bs_contents0 (bound_fdef f))
  (HeqR4 : {| DomDS.L.bs_contents := bs_contents0;
              DomDS.L.bs_bound := bs_bound0 |} = (dom_analyze f) !! l2)
  (b1 : block) (l1' : atom)
  (J10 : In l1' (ListSet.set_diff eq_atom_dec bs_contents0 [l2]))
  (J11 : lookupBlockViaLabelFromFdef f l1' = ret b1)
  (J11' : In id1 (getBlockIDs b1)) init
  (J12 : In id2
          (getPhiNodesIDs ps1 ++
           cmds_dominates_cmd (cs1 ++ c :: cs) (getCmdLoc c)))
  (HeqR' : fold_left (inscope_of_block f l1) bs_contents
            (ret (getPhiNodesIDs ps1 ++
                  cmds_dominates_cmd (cs1 ++ c :: cs) (getCmdLoc c) ++ init)) = 
           ret t),
  In id1 t.
Proof.
  intros.
  assert (block_intro l2 p c2 t0 =
              block_intro l1 ps1 (cs1 ++ c :: cs) tmn1) as EQ.
    eapply block_eq1 with (id0:=id2); eauto.
      simpl. eapply cmds_dominates_cmd_spec'; eauto.
  inv EQ.
  rewrite <- HeqR3 in HeqR4. inv HeqR4.
  apply fold_left__intro with (l2:=l1')(B:=b1) in HeqR'; auto.
Qed.

Lemma cmds_dominates_cmd_inscope_of_tmn__inscope_of_tmn: forall
  (f : fdef) (t : list atom) (l1 : l) (ps1 : phinodes) (cs1 : cmds)
  (tmn1 : terminator) id1 (id2 : id) (HwfF : uniqFdef f)
  (bs_contents : ListSet.set atom)
  (HbInF : blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true)
  (l2 : l) (p : phinodes) (c0 : cmds) (t0 : terminator)
  (HeqR1 : ret block_intro l2 p c0 t0 = lookupBlockViaIDFromFdef f id2)
  (J1 : In id1 (getPhiNodesIDs p ++ cmds_dominates_cmd c0 id2))
  (J12 : In id2 (getPhiNodesIDs ps1 ++ getCmdsIDs cs1)) init
  (HeqR' : fold_left (inscope_of_block f l1) bs_contents
            (ret (getPhiNodesIDs ps1 ++ getCmdsIDs cs1 ++ init)) = 
           ret t),
  In id1 t.
Proof.
  intros.
  assert (block_intro l2 p c0 t0 = block_intro l1 ps1 cs1 tmn1) as EQ.
    eapply block_eq1 with (id0:=id2); eauto.
  inv EQ.
  apply fold_left__init in HeqR'.
  apply HeqR'; auto.
    eapply cmds_dominates_cmd_spec' in J1; eauto.
    solve_in_list.
Qed.  

Lemma inscope_of_block_cmds_dominates_cmd__inscope_of_tmn: forall
  (f : fdef) (t : list atom) (l1 : l) (ps1 : phinodes) (cs1 : cmds)
  (tmn1 : terminator) id1 (id2 : id) (HwfF : uniqFdef f)
  (bs_contents : ListSet.set atom)
  (bs_bound : incl bs_contents (bound_fdef f))
  (HeqR3 : {| DomDS.L.bs_contents := bs_contents;
              DomDS.L.bs_bound := bs_bound |} = (dom_analyze f) !! l1)
  (HbInF : blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true)
  (l2 : l) (p : phinodes) (c0 : cmds) (t0 : terminator)
  (HeqR1 : ret block_intro l2 p c0 t0 = lookupBlockViaIDFromFdef f id2)
  (bs_contents0 : ListSet.set atom)
  (bs_bound0 : incl bs_contents0 (bound_fdef f))
  (HeqR4 : {| DomDS.L.bs_contents := bs_contents0;
              DomDS.L.bs_bound := bs_bound0 |} = (dom_analyze f) !! l2)
  (b1 : block) (l1' : atom)
  (J10 : In l1' (ListSet.set_diff eq_atom_dec bs_contents0 [l2]))
  (J11 : lookupBlockViaLabelFromFdef f l1' = ret b1)
  (J11' : In id1 (getBlockIDs b1))
  (J12 : In id2 (getPhiNodesIDs ps1 ++ getCmdsIDs cs1)) init
  (HeqR' : fold_left (inscope_of_block f l1) bs_contents
            (ret (getPhiNodesIDs ps1 ++ getCmdsIDs cs1 ++ init)) = 
           ret t),
  In id1 t.
Proof.
  intros.
  assert (block_intro l2 p c0 t0 = block_intro l1 ps1 cs1 tmn1) as EQ.
    eapply block_eq1 with (id0:=id2); eauto.
  inv EQ.
  rewrite <- HeqR3 in HeqR4. inv HeqR4.
  apply fold_left__intro with (l2:=l1')(B:=b1) in HeqR'; auto.
Qed.

Lemma cmds_dominates_cmd_spec0 : forall ids1 id2 cs id0,
  In id2 (ids1 ++ cmds_dominates_cmd cs id0) ->
  In id2 (ids1 ++ getCmdsLocs cs).
Proof.
  intros.
  eapply cmds_dominates_cmd_spec' in H; eauto.
  solve_in_list.
Qed.

Lemma In_cmds_dominates_cmd_fdef__getCmdID_eq_getCmdLoc: forall
  (F1 : fdef) id0 (Huniq : uniqFdef F1)
  (c1 : cmd) (l0 : l) (p : phinodes) (c0 : cmds)
  (Hin : In (getCmdLoc c1)
          (getPhiNodesIDs p ++ cmds_dominates_cmd c0 id0))
  (t : terminator)
  (H : insnInFdefBlockB (insn_cmd c1) F1 (block_intro l0 p c0 t) = true),
  getCmdID c1 = Some (getCmdLoc c1).
Proof.
  intros.
  simpl in H.
  bdestruct H as G1 G2. assert (G:=G2).
  assert (NoDup (getBlockLocs (block_intro l0 p c0 t))) as Huniq'.
    eapply uniqFdef__uniqBlockLocs; eauto.
  apply InCmdsB_in in G1.
  apply IngetCmdsIDs__lookupCmdViaIDFromFdef with (c1:=c1) in G2; auto.
  apply lookupCmdViaIDFromFdef_spec with (id2:=getCmdLoc c1) in G; 
    eauto using cmds_dominates_cmd_spec0.
  assert (In (getCmdLoc c1) (cmds_dominates_cmd c0 id0)) as Hin'.
    apply in_app_or in Hin.
    destruct Hin as [Hin | Hin]; auto.
    simpl in Huniq'.
    eapply NoDup_disjoint' in Huniq'; eauto.
    contradict Huniq'. solve_in_list.
  apply cmds_dominates_cmd_spec in Hin'.
  apply In_getCmdsIDs__getCmdID_eq_getCmdLoc in Hin'; auto.
    simpl in Huniq'.
    apply NoDup_split in Huniq'.
    destruct Huniq' as [_ Huniq'].
    apply NoDup_split in Huniq'.
    destruct Huniq'. auto.
Qed.

Lemma inscope_of_id__total: forall f b id0, inscope_of_id f b id0 <> None.
Proof.
  unfold inscope_of_id. 
  destruct f as [fh bs]. destruct b.
  intros. 
  destruct ((dom_analyze (fdef_intro fh bs)) !! l0).
  eapply fold_left__bound_blocks 
    with (fh:=fh)(l0:=l0)(init:=init_scope (fdef_intro fh bs) p c id0) 
    in bs_bound; eauto.
  destruct bs_bound. simpl. congruence.
Qed.

Lemma inscope_of_cmd__idDominates : forall l0 f b c i0
  (HeqR0 : ret l0 = inscope_of_cmd f b c) (Hin: In i0 l0) 
  (Hsome: getCmdID c <> None) (Huniq: uniqFdef f)
  (HbInF: blockInFdefB b f = true) (HcInB: cmdInBlockB c b = true),
  idDominates f i0 (getCmdLoc c).
Proof.
  unfold inscope_of_cmd.
  intros. 
  eapply inscope_of_id__idDominates in HeqR0; eauto.
  apply inGetBlockIDs__lookupBlockViaIDFromFdef; auto.
    solve_in_list.
Qed.
          
Lemma cmds_dominates_cmd_acyclic: forall (id1 id2 : id) (cs3 : cmds)
  (Hnodup : NoDup (getCmdsLocs cs3))
  (Hin2 : In id2 (cmds_dominates_cmd cs3 id1))
  (Hin1 : In id1 (cmds_dominates_cmd cs3 id2))
  (Hin3 : In id1 (getCmdsLocs cs3)) (Hin4 : In id2 (getCmdsLocs cs3)),
  False.
Proof.
  intros.  
  apply cmds_dominates_cmd_inv in Hin2; auto.
  destruct Hin2 as [cs1 [c [cs2 [J1 [J2 J3]]]]]; subst.
  apply cmds_dominates_cmd_inv in Hin1; auto.
  destruct Hin1 as [cs1' [c' [cs2' [J1' [J2' J3']]]]]; subst.
  apply in_getCmdsLocs_inv in J2.
  destruct J2 as [cs4 [c1 [cs3 [G1 G2]]]]; subst.
  apply in_getCmdsLocs_inv in J2'.
  destruct J2' as [cs4' [c1' [cs3' [G1' G2']]]]; subst.
  simpl_env in J1'. simpl_env in Hnodup. simpl in *.
  assert (G:=Hnodup).
  apply NoDup_getCmdsLocs_prop with (c1:=c1)(c2:=c') in G; 
    try solve [auto | solve_in_list | rewrite J1'; solve_in_list].
  subst.
  assert (G:=Hnodup).
  apply NoDup_getCmdsLocs_prop with (c1:=c1')(c2:=c) in G; 
    try solve [auto | solve_in_list | rewrite J1'; solve_in_list].
  subst.
  rewrite_env ((cs4' ++ c :: cs3') ++ c' :: cs2') in J1'.
  apply NoDup_cmds_split_middle in J1'; auto.
  destruct J1'; subst.
  clear - Hnodup.
  simpl_env in Hnodup. 
  rewrite getCmdsLocs_app in Hnodup.
  apply NoDup_split in Hnodup. destruct Hnodup as [_ Hnodup].
  rewrite getCmdsLocs_app in Hnodup.
  simpl in Hnodup. inv Hnodup.
  apply H1. rewrite_env ((cs3' ++ c' :: cs3) ++ c :: cs2).
  solve_in_list.
Qed.

Inductive wf_phi_operands (f:fdef) (b:block) (id0:id) (t0:typ) :
    list_value_l -> Prop :=
| wf_phi_operands_nil : wf_phi_operands f b id0 t0 Nil_list_value_l
| wf_phi_operands_cons_vid : forall vid1 l1 vls b1,    
    lookupBlockViaLabelFromFdef f l1 = Some b1 ->
    ((exists vb, lookupBlockViaIDFromFdef f vid1 = Some vb /\ 
       (blockDominates f vb b1 \/ not (isReachableFromEntry f b))) \/ 
     In vid1 (getArgsIDsOfFdef f)) ->
    wf_phi_operands f b id0 t0 vls ->
    wf_phi_operands f b id0 t0 (Cons_list_value_l (value_id vid1) l1 vls)
| wf_phi_operands_cons_vc : forall c1 l1 vls,
    wf_phi_operands f b id0 t0 vls ->
    wf_phi_operands f b id0 t0 (Cons_list_value_l (value_const c1) l1 vls).

Definition check_list_value_l (f:fdef) (b:block) (vls:list_value_l) :=
  let ud := genBlockUseDef_fdef f in
  let vls1 := unmake_list_value_l vls in
  let '(vs1,ls1) := List.split vls1 in
  let ls2 := predOfBlock b ud in
  (length ls2 > 0)%nat /\
  AtomSet.set_eq _ ls1 ls2 /\
  NoDup ls1.

Definition wf_phinode (f:fdef) (b:block) (p:phinode) :=
let '(insn_phi id0 t0 vls0) := p in
wf_phi_operands f b id0 t0 vls0 /\ check_list_value_l f b vls0.

