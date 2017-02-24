Require Import ListSet.
Require Import vellvm_tactics.
Require Import Coq.Lists.List.
Require Import CoqListFacts.
Require Import Metatheory.
Require Import Coqlib.
Require Import alist.

(* In *)

Lemma In_weakening : forall A (l2 l3 l1:list A) a,
  In a (l1 ++ l3) -> In a (l1 ++ l2 ++ l3).
Proof.
  induction l1; simpl; intros.
    apply in_or_app; auto.
    destruct H as [H | H]; auto.
Qed.

Lemma In_middle : forall A (c:A) cs1 cs2, In c (cs1++c::cs2).
Proof.
  induction cs1; simpl; auto.
Qed.

Lemma notin_app_inv: forall A (l1 l2:list A) a,
  ~ In a (l1 ++ l2) -> ~ In a l1 /\ ~ In a l2.
Proof.
  intros.
  split; intro J; apply H; apply in_or_app; auto.
Qed.

Lemma notin_app: forall A (l1 l2:list A) a,
  ~ In a l1 -> ~ In a l2 ->
  ~ In a (l1 ++ l2).
Proof.
  intros. intro J.
  apply in_app_or in J.
  destruct J as [J | J].
    apply H; auto.
    apply H0; auto.
Qed.

Lemma in_middle : forall A (c:A) cs1 cs2, In c (cs1 ++ c :: cs2).
Proof.
  intros.
  apply in_app_iff; simpl; auto.
Qed.

Lemma in_first_chunk: forall X (a:X) A B C, In a A -> In a (A++B++C).
Proof.
  intros. apply in_or_app. auto.
Qed.

Lemma in_second_chunk: forall X (b:X) A B C, In b B -> In b (A++B++C).
Proof.
  intros. apply in_or_app. right. apply in_or_app. auto.
Qed.

Lemma in_third_chunk: forall X (c:X) A B C, In c C -> In c (A++B++C).
Proof.
  intros. apply in_or_app. right. apply in_or_app. auto.
Qed.

Ltac destruct_in H :=
match type of H with
| In _ [_] => simpl in H; destruct H as [H | H]; subst; try tauto
| In _ (_::_) => simpl in H; destruct H as [H | H]; subst; try tauto
| In _ (_++_) => apply in_app_or in H; destruct H as [H | H]
end.

(* map *) 
Lemma map_app_inv : forall A B l1 l2 l (f:A->B),
  List.map f l = l1 ++ l2 ->
  exists l1', exists l2',
    l = l1' ++ l2' /\ List.map f l1' = l1 /\ List.map f l2' = l2.
Proof.
  induction l1; simpl; intros.
    exists nil. exists l. auto.

    destruct l; inv H.
    apply IHl1 in H2. destruct H2 as [l1' [l2' [J1 [J2 J3]]]]; subst.
    exists (a0::l1'). exists l2'. auto.
Qed.

Lemma fst_split__map_fst: forall A B (l1:list (A*B)),
  fst (split l1) = List.map fst l1.
Proof.
  induction l1 as [|[]]; simpl; auto.
    destruct_let. simpl. rewrite <- IHl1. auto.
Qed.

Lemma snd_split__map_snd: forall A B (l1:list (A*B)),
  snd (split l1) = List.map snd l1.
Proof.
  induction l1 as [|[]]; simpl; auto.
    destruct_let. simpl. rewrite <- IHl1. auto.
Qed.

Lemma map_id_ext {A : Type} (f : A -> A) (l : list A) :
  (forall a : A, f a = a) -> List.map f l = l.
Proof.
  intros H. induction l as [|a l]. trivial.
  simpl. rewrite H. rewrite IHl. trivial.
Qed.

Lemma map_nil_inv: forall A B (f:A->B) l1 (Heq : nil = List.map f l1),
  l1 = nil.
Proof.
  intros.
  destruct l1 as [|a x]; inv Heq; auto.
Qed.

Lemma map_cons_inv: forall A B (x:list A) y2 (a':B) f 
  (Heq: List.map f x = a' :: y2),
  exists a, exists x2, x = a :: x2 /\ List.map f x2 = y2 /\ f a = a'.
Proof.
  intros.
  destruct x as [|a x]; inv Heq.
    eauto.
Qed.

Lemma In_fst__in_dom: forall X (A:list (atom*X)) i0,
  In i0 (List.map fst A) <-> i0 `in` dom A.
Proof.
  induction A as [|[] A]; simpl; intros; auto.
    split; intro J.
      inv J. fsetdec.

    split; intro J.
      destruct J as [J | J]; subst; auto.
        apply IHA in J; auto.

      apply AtomSetFacts.add_iff in J.
      destruct J as [J | J]; subst; auto.
        apply IHA in J; auto.
Qed.

Lemma eq_map_fst__eq_dom: forall A (acs1 acs2:list (atom*A))
  (Heq: List.map fst acs1 = List.map fst acs2),
  dom acs1 [=] dom acs2.
Proof.
  induction acs1 as [|[]]; destruct acs2 as [|[]]; intros; inv Heq.
    fsetdec. 
    simpl. apply IHacs1 in H1. fsetdec.
Qed.

Lemma map_fst_uniq: forall A (acs1:list (atom*A)) 
  (Huniq: uniq acs1) (acs2:list (atom*A)) 
  (Heq: List.map fst acs1 = List.map fst acs2),
  uniq acs2.
Proof.
  induction 1; intros; destruct acs2 as [|[]]; inv Heq; 
    simpl_env; constructor; auto.
    apply eq_map_fst__eq_dom in H2. fsetdec.
Qed. 

Lemma app__map_fst: forall A (acs1 acs2 acs3 acs4: list (atom*A))
  (Heq12: List.map fst acs1 = List.map fst acs2)
  (Heq34: List.map fst acs3 = List.map fst acs4),
  List.map fst (acs1++acs3) = List.map fst (acs2++acs4).
Proof.
  intros.
  repeat (rewrite List.map_app).
  congruence.
Qed.

Lemma map_fst__dom: forall A (l1:list (atom*A)) B (l2:list (atom*B))
  (Heq: List.map fst l1 = List.map fst l2),
  dom l1 [=] dom l2.
Proof.
  induction l1 as [|[]]; destruct l2 as [|[id2 ac2] l2]; simpl; intros.
    fsetdec.
    inv Heq.
    inv Heq.

    inv Heq. apply IHl1 in H1. fsetdec.
Qed.

Lemma map_fst__uniq: forall A (l1:list (atom*A)) (Huniq: uniq l1) 
  B (l2:list (atom*B))
  (Heq: List.map fst l1 = List.map fst l2),
  uniq l2.
Proof.
  induction 1; destruct l2 as [|[id2 ac2] l2]; simpl; intros; auto.
    inv Heq.

    inv Heq.
    simpl_env.
    constructor; auto.
      apply map_fst__dom in H2. fsetdec.
Qed.

(* incl *) 
Lemma incl_insert: forall A (l1 l2:list A) a, incl (l1++l2) (l1++a::l2).
Proof.
  induction l1; simpl; intros; intros x J; simpl; auto.
    simpl in J. destruct J as [J | J]; auto.
    right. apply IHl1; auto.
Qed.

Lemma incl_app: forall A (l0 l1 l2:list A),
  incl l1 l2 -> incl (l0++l1) (l0++l2).
Proof.
  intros. intros x J.
  apply in_or_app. apply in_app_or in J.
  destruct J as [J | J]; auto.
Qed.

Lemma incl_nil : forall A (d:list A), incl nil d.
Proof. intros. intros x J. inv J. Qed.

Lemma incl_cons : forall A l1 (x:A), incl l1 (x::l1).
Proof.
  intros. intros y J. simpl; auto.
Qed.

Lemma removelast_incl : forall A (l1:list A),
  incl (removelast l1) l1.
Proof.
  intros.
  destruct l1 as [|a l1].
    apply incl_nil.

    assert (a::l1 <> nil) as Hneq by congruence.
    apply exists_last in Hneq.
    destruct Hneq as [l' [a0 EQ]].
    rewrite EQ.
    rewrite removelast_app; try congruence.
    simpl. simpl_env.
    apply incl_appl. apply incl_refl.
Qed.

Lemma incl_split: forall A (l1 l2 l3:list A) (Hinc: incl (l1++l2) l3),
  incl l1 l3 /\ incl l2 l3.
Proof.
  intros.
  split; intros x Hin; apply Hinc; apply in_or_app; auto.
Qed.

Lemma incl_cons_split: forall A a (l2 l3:list A) (Hinc: incl (a::l2) l3),
  In a l3 /\ incl l2 l3.
Proof.
  intros.
  simpl_env in Hinc.
  apply incl_split in Hinc.
  destruct Hinc as [Hinc1 Hinc2].
  split; auto.
    apply Hinc1. simpl. auto.
Qed.

Lemma tl_incl: forall A (l1: list A), incl (tl l1) l1.
Proof.
  intros.
  unfold tl.
  destruct l1.
    apply incl_refl.
    apply incl_tl. apply incl_refl.
Qed.

Implicit Arguments tl_incl [A].

Lemma incl_notin: forall A (acs2 acs1 : list (atom * A)) (id5 : atom)
  (Hinc : incl acs2 acs1) (Hend : id5 `notin` dom acs1),
  id5 `notin` dom acs2.
Proof.
  induction acs2 as [|[]]; intros; simpl.
    fsetdec.

    destruct (eq_atom_dec id5 a); subst.
      contradict Hend.
      apply In_InDom with (v1:=a0).
      apply Hinc. simpl. auto.      

      simpl_env in Hinc.
      apply incl_split in Hinc.
      destruct Hinc as [_ Hinc].
      eapply IHacs2 in Hinc; eauto.
Qed.

(* list *) 
Lemma in_dom__iff__in_rev_dom: forall i0 X (A:list (atom*X)),
  i0 `in` dom A <-> i0 `in` dom (rev A).
Proof.
  induction A as [|[] A]; simpl.
    split; auto.

    rewrite dom_app. simpl.
    fsetdec.
Qed.

Lemma app_split: forall A (x y z u:list A) a (Heq: x ++ y = z ++ a :: u),
  (exists u1, exists u2, x = z ++ a :: u1 /\ y = u2 /\ u = u1 ++ u2) \/
  (exists z1, exists z2, x = z1 /\ y = z2 ++ a :: u /\ z = z1 ++ z2).
Proof.
  induction x as [|x1 x]; simpl; intros; subst.
    right. exists nil. eauto.

    destruct z as [|z1 z].
      inv Heq. simpl. left. exists x. eauto.

      inv Heq.
      apply_clear IHx in H1.
      destruct H1 as [[u1 [u2 [J1 [J2 J3]]]]|[z1' [z2 [J1 [J2 J3]]]]]; subst.
        left. exists u1. exists u2. eauto.
        right. exists (z1::z1'). eauto.
Qed.

Lemma rev_non_nil: forall A (ls1:list A),
  ls1 <> nil <-> rev ls1 <> nil.
Proof.
  induction ls1; simpl.
    split; auto.  
    split; intro J; auto with datatypes.      
Qed.

Lemma cons_last: forall A (hd:A) tl, 
  exists pre, exists last, hd::tl = pre++[last].
Proof.
  intros.
  assert (hd::tl <> nil) as Hnnil.
    congruence.
  apply exists_last in Hnnil.
  destruct Hnnil as [? [? ?]].
  eauto.
Qed.

Lemma app_cons_is_larger: forall A cs3 cs2 (c:A),
  cs2 = cs3 ++ c :: cs2 -> False.
Proof.
  intros.
  assert (J:=app_length cs3 (c::cs2)).
  rewrite <- H in J.
  simpl in J. omega.
Qed.

Lemma app_inv_tail_nil : forall A (l1 l2:list A),
  l1 ++ l2 = l2 -> l1 = nil.
Proof.
  intros.
  change l2 with (nil ++ l2) in H at 2.
  apply app_inv_tail in H; auto.
Qed.

Lemma head_tail_commut: forall A (a:A) cs,
  exists cs', exists a', [a] ++ cs = cs' ++ [a'].
Proof.
  induction cs.
    exists nil. exists a. auto.

    destruct IHcs as [cs' [a' IHcs]].
    destruct cs'.
      inv IHcs.
      exists [a']. exists a0. auto.

      inv IHcs.
      exists ([a1]++a0::cs'). exists a'. auto.
Qed.

Lemma app_middle_split: forall A (l1 l2 l3 l4:list A) a,
  l1++a::l2 = l3++l4 ->
  (exists l12, l1 = l3++l12 /\ l4 = l12++a::l2) \/
  (exists l21, l3 = l1++a::l21 /\ l2 = l21++l4).
Proof.
  induction l1; simpl; intros.
    destruct l3.
      destruct l4; inv H.
        left. exists nil. auto.
      inv H. right. exists l3. auto.

    destruct l3.
      destruct l4; inv H.
        left. exists (a1::l1). auto.
      inv H. apply IHl1 in H2.
      destruct H2 as [[l21 [J1 J2]]|[l21 [J1 J2]]]; subst; simpl; eauto.
Qed.

Lemma split_r_in : forall A B (l1:list (A*B))(b:B),
  In b (snd (split l1)) -> exists a, In (a,b) l1.
Proof.
  induction l1 as [|[]]; simpl; intros; try tauto.
    destruct_let. simpl in *.
    destruct H as [H | H]; subst; eauto.
      apply IHl1 in H. 
      destruct H as [a0 H]. eauto.
Qed.

Lemma split_l_in : forall A B (l1:list (A*B))(a:A),
  In a (fst (split l1)) -> exists b, In (a,b) l1.
Proof.
  induction l1 as [|[]]; simpl; intros; try tauto.
    destruct_let. simpl in *.
    destruct H as [H | H]; subst; eauto.
      apply IHl1 in H. 
      destruct H as [b0 H]. eauto.
Qed.

Ltac anti_simpl_env :=
simpl_env in *;
repeat match goal with
| H: ?A ++ _ = ?A ++ _ |- _ => apply app_inv_head in H
| H: ?A ++ ?B ++ ?C = _ |- _ => rewrite_env ((A++B)++C) in H
| H: ?A ++ ?B ++ ?C ++ ?D = _ |- _ => rewrite_env (((A++B)++C)++D) in H
| H: ?A ++ ?B ++ ?C ++ ?D ++ ?E = _ |- _ =>rewrite_env ((((A++B)++C)++D)++E) in H
| H: _ = ?A ++ ?B ++ ?C |- _ => rewrite_env ((A++B)++C) in H
| H: _ = ?A ++ ?B ++ ?C ++ ?D |- _ => rewrite_env (((A++B)++C)++D) in H
| H: _ = ?A ++ ?B ++ ?C ++ ?D ++ ?E |- _ =>rewrite_env ((((A++B)++C)++D)++E) in H
end;
repeat match goal with
| H: _ ++ ?A = _ ++ ?A |- _ => apply app_inv_tail in H
| H: _ ++ [?a] = _ ++ [?b] |- _ => apply app_inj_tail in H; destruct H; subst
| H: ?A = _ ++ ?A |- _ => symmetry in H; apply app_inv_tail_nil in H
| H: _ ++ ?A = ?A |- _ => apply app_inv_tail_nil in H
| H: (_++[_])++_ = nil |- _ => 
    contradict H; simpl_env; simpl; apply CoqListFacts.app_cons_not_nil
| H: _++[_]++_ = nil |- _ => contradict H; simpl; apply CoqListFacts.app_cons_not_nil
| H: ?A++[?a] = nil |- _ => 
       rewrite_env (A++[a]++nil) in H;
       contradict H; simpl; apply CoqListFacts.app_cons_not_nil
end.

Lemma list_prop1: forall A (l1 l3 l4:list A) a2 a5,
  l1 ++ [a2] ++ l3 = l4 ++ [a5] ->
  exists l6, [a2] ++ l3 = l6 ++ [a5].
Proof.
  induction l1; simpl; intros.
    exists l4. auto.

    destruct l4; inv H.
      anti_simpl_env.
      simpl in *. apply IHl1 in H2; auto.
Qed.

Lemma list_prop2: forall A (l2:list A) (H: (length l2 > 0)%nat),
  exists l1, exists b2, l2 = l1 ++ [b2].
Proof.
  induction l2; simpl; intros.
    contradict H. omega.

    destruct l2.
      exists nil. exists a. auto.

      destruct IHl2 as [l1 [b2 J]]; simpl; try omega.
      rewrite J.
      exists (a::l1). exists b2. simpl_env. auto.
Qed.
    
Lemma list_prop3: forall A (a1:A) l2,
  exists l1, exists b2, a1 :: l2 = l1 ++ [b2].
Proof.
  intros.
  apply list_prop2. simpl. omega.
Qed.

Lemma list_suffix_dec: forall A (Hdec: forall (x y : A), {x = y}+{x <> y})
  (l1 l2: list A), (exists l3, l1 = l3 ++ l2) \/ (~ exists l3, l1 = l3 ++ l2).
Proof.
  induction l2; simpl; eauto.
    destruct IHl2 as [IHl2 | IHl2].
      destruct IHl2 as [l3 IHl2]; subst.
      destruct l3.
        right.
        intro J. destruct J as [l3 J].
        anti_simpl_env.

        destruct (@list_prop3 _ a0 l3) as [l4 [b5 J]].
        rewrite J.
        destruct (@Hdec b5 a); subst.
          left. exists l4. simpl_env. auto.
          right. intro J'. destruct J' as [l6 J'].
          simpl_env in J'. anti_simpl_env. auto.


      right. intro J. apply IHl2.
      destruct J as [l3 J]; subst.
      exists (l3 ++ [a]). simpl_env. auto.
Qed.

Lemma cons_head: forall A pre (last:A), 
  exists hd, exists tl, hd::tl = pre++[last].
Proof.
  induction pre; intros.
    exists last. exists nil. auto.

    destruct (IHpre last) as [hd [tl EQ]].
    simpl_env. rewrite <- EQ. exists a. exists (hd::tl). auto.
Qed.

Lemma nnil_inv: forall A (l1:list A) (Hn: l1 <> nil), 
  exists pre, exists last, l1 = pre++[last].
Proof.
  intros.
  destruct l1; try congruence.
  apply cons_last; auto.
Qed.

Lemma app_cons_not_nil': forall A (x y:list A) (a:A) (H: x ++ a :: y = nil), 
  False.
Proof.
  intros.
  contradict H. apply app_cons_not_nil.
Qed.

Lemma tl_nonempty_inv: forall A (z0:A) vl vl1 vl2
  (Heq: tl vl = vl1 ++ z0 :: vl2),
  exists v0, vl = v0 :: vl1 ++ z0 :: vl2.
Proof.
  unfold tl.
  intros.
  destruct vl.
    symmetry in Heq. apply app_cons_not_nil' in Heq. tauto.
    subst. eauto.  
Qed.

Lemma in_middle_split: forall A (a b:A) l1 l2 (HIna: In b (l1++a::l2)),
  In b (l1++l2) \/ b = a.
Proof.
  intros.
  apply in_app_or in HIna.
  destruct HIna as [HIna | HIna].
    left. apply in_or_app; auto.
    simpl in HIna.
    destruct HIna as [HIna | HIna]; auto.
      left. apply in_or_app; auto.
Qed.

Lemma notin_tl: forall A (z0:A) vl1
  (H: ~ In z0 vl1), ~ In z0 (tl vl1).
Proof.
  intros. 
  assert (J:=tl_incl vl1). auto.
Qed.

Lemma cons_self__False: forall A (a:A) l1 (Heq: a::l1 = l1), False.
Proof.
  induction l1; intros; congruence.
Qed.

Ltac cons_self__False_tac :=
match goal with
| H: _ :: ?acs = ?acs |- _ => apply cons_self__False in H; inv H
end.

(* Forall *)
Lemma Forall_app: forall A P (x y:list A) (Hx: Forall P x) (Hy: Forall P y),
  Forall P (x++y).
Proof.
  induction 1; intros; auto.
    constructor; auto.
Qed.

Lemma Forall_inv' : forall A P (a:A) l, Forall P (a :: l) -> Forall P l.
Proof.
  intros. inv H; auto.
Qed.

Lemma Forall_tl : forall A P (l:list A), Forall P l -> Forall P (tl l).
Proof.
  induction 1; simpl; auto.
Qed.

Lemma Forall_split : forall A P (l1 l2:list A), Forall P (l1++l2) -> 
  Forall P l1 /\ Forall P l2.
Proof.
  induction l1; intros; auto.
    inv H.
    apply IHl1 in H3.
    destruct H3.
    split; auto.
Qed.

Lemma Forall_tl_first : forall A P (l1 l2:list A), 
  Forall P (l1 ++ l2) -> Forall P (tl l1++l2).
Proof.
  intros.
  apply Forall_split in H. destruct H.
  apply Forall_app; auto using Forall_tl.
Qed.

Lemma Forall_incl : forall A P (l1 l2:list A), 
  Forall P l2 -> incl l1 l2 -> Forall P l1.
Proof.
  intros.
  eapply Forall_forall.
  intros.
  apply H0 in H1.
  eapply Forall_forall in H; eauto.
Qed. 

Lemma Forall_removelast : forall A P (l1:list A), 
  Forall P l1 -> Forall P (removelast l1).
Proof.
  intros.
  eapply Forall_incl; eauto.
  apply removelast_incl.
Qed. 

(* filter *)
Lemma filter_ext: forall (A:Type) (f g:A->bool)
  (Heq: forall a, f a = g a) (l0:list A), List.filter f l0 = List.filter g l0.
Proof.
  induction l0; intros; simpl; auto.
    rewrite Heq. rewrite IHl0. auto.
Qed.

Lemma filter_true: forall (A:Type) (f:A->bool)
  (Heq: forall a, f a = true) (l0:list A), l0 = List.filter f l0.
Proof.
  induction l0; intros; simpl; auto.
    rewrite Heq. congruence.
Qed.

Lemma filter_app: forall A (check: A -> bool) (l1 l2:list A),
  filter check (l1++l2) = filter check l1 ++ filter check l2.
Proof.
  induction l1; simpl; intros; auto.
    destruct_if.
    rewrite IHl1. simpl_env. auto.
Qed.

(* fold *)
Lemma fold_left_eq : forall B f (J:forall a b, f a b = false -> a = false),
  forall (l1:list B) a, List.fold_left f l1 a = false -> a = false.
Proof.
  induction l1; simpl; intros; eauto.
Qed.

Lemma fold_left_congruence : forall B (f:Prop -> B -> Prop)
  (J:forall (a b:Prop) c, (a->b) -> (f a c -> f b c))
  (l1:list B) (a b:Prop),
  (a -> b) ->
  (List.fold_left f l1 a -> List.fold_left f l1 b).
Proof. induction l1; simpl; intros; eauto. Qed.

Lemma fold_left_prop : forall B (f:Prop -> B -> Prop),
  (forall (a:Prop) b, f a b -> a) ->
  (forall (a b:Prop) c, (a->b) -> (f a c -> f b c)) ->
  forall (l1:list B) (a:Prop),
  (List.fold_left f l1 a -> a).
Proof.
  induction l1; simpl; intros; auto.
    apply IHl1; auto.
    apply fold_left_congruence with (a:=f a0 a); auto.
    apply H.
Qed.

Lemma fold_left_or_false : forall B (f:bool -> B -> bool)
  (J:forall a b, f a b = false -> a = false),
  forall (l1:list B) init,
    List.fold_left f l1 init = false ->
    List.fold_left f l1 false = false /\ init = false.
Proof.
  induction l1; simpl; intros; eauto.
    assert (H':=H).
    apply IHl1 in H.
    destruct H as [H1 H2].
    apply J in H2. subst.
    split; auto.
Qed.

Lemma fold_left_and_true : forall B (f:bool -> B -> bool)
  (J:forall a b, f a b = true -> a = true),
  forall (l1:list B) init,
    List.fold_left f l1 init = true ->
    List.fold_left f l1 true = true /\ init = true.
Proof.
  induction l1; simpl; intros; eauto.
    assert (H':=H).
    apply IHl1 in H.
    destruct H as [H1 H2].
    apply J in H2. subst.
    split; auto.
Qed.

Lemma fold_left_or_spec : forall B (f:bool -> B -> bool)
  (J:forall a b, a = true -> f a b = true),
  forall (l1:list B), List.fold_left f l1 true = true.
Proof.
  induction l1; simpl; intros; eauto.
    rewrite J; auto.
Qed.

Lemma fold_left_or_false_elim : forall B (f: B -> bool)
  l0 init (H:fold_left (fun a b => a || f b) l0 init = false),
  forall x (Hin: In x l0), f x = false.
Proof.
  induction l0; simpl; intros. 
    tauto.

    apply fold_left_or_false in H.
      destruct H as [H1 H2].
      binvf H2 as H3 H4. 
      destruct Hin as [Hin | Hin]; subst; eauto.
      
      intros. binvf H0 as H3 H4. auto.
Qed.

Lemma fold_left_or_true_elim: forall B (f: B -> bool)
  l0 (H:fold_left (fun a b => a || f b) l0 false = true),
  exists x, In x l0 /\ f x = true.
Proof.
  induction l0; simpl; intros. 
    congruence.

    remember (f a) as R. 
    destruct R.
      eauto.
      apply IHl0 in H. destruct H as [x [J1 J2]]. eauto.
Qed.

(* index *)
Lemma firstn_nil : forall A n, firstn n (@nil A) = nil.
Proof. induction n; simpl; auto. Qed.

Lemma skipn_nil : forall A n, skipn n (@nil A) = nil.
Proof. induction n; simpl; auto. Qed.

(* NoDup *)

Lemma NotIn_inv : forall X (a:X) (lb1 lb2:list X),
  ~ In a (lb1++lb2) ->
  ~ In a lb1 /\ ~ In a lb2.
Proof.
  intros.
  split; intro J'; apply H; auto using in_or_app.
Qed.

Lemma NoDup_split : forall A (l1 l2:list A),
  NoDup (l1++l2) ->
  NoDup l1 /\ NoDup l2.
Proof.
  induction l1; intros.
    simpl in *.
    split; auto using NoDup_nil.

    inversion H; subst.
    apply IHl1 in H3.
    destruct H3 as [J1 J2].
    split; auto.
      apply NoDup_cons; auto.
        intro J. apply H2. apply in_or_app; auto.
Qed.

Lemma NoDup_last_inv : forall X (a:X) l0,
  NoDup (l0++a::nil) ->
  ~ In a l0.
Proof.
  induction l0; intros.
    intro J. inversion J.

    simpl in H.
    inversion H; subst.
    apply IHl0 in H3.
    intro J.
    simpl in J.
    inversion J; subst; auto.
      apply NotIn_inv in H2.
      destruct H2.
      apply H1; simpl; auto.
Qed.

Lemma NoDup_disjoint : forall X (l2 l1 : list X) (i0 : X),
  NoDup (l1 ++ l2) -> In i0 l2 -> ~ In i0 l1.
Proof.
  induction l1; simpl; intros; auto.
    inversion H; subst.
    intro J.
    destruct J as [J | J]; subst.
      apply H3. apply in_or_app. auto.
      eapply IHl1 in H4; eauto.
Qed.

Ltac solve_NoDup_disjoint :=
match goal with
| H: NoDup (?A++?B++?a::nil) |- ~ In ?a (?A++?B) =>
  rewrite_env ((A++B)++[a]) in H;
  apply NoDup_disjoint with (i0:=a); simpl; eauto
end.

Lemma NoDup_disjoint' : forall l1 l2 (i0:atom),
  NoDup (l1++l2) ->
  In i0 l1 ->
  ~ In i0 l2.
Proof.
  induction l1; intros.
    inversion H0.

    simpl. simpl_env in H.
    inv H. simpl in H0.
    destruct H0 as [H0 | H0]; subst; eauto.
      intro J. apply H3. apply in_or_app; auto.
Qed.

Hint Constructors NoDup.

Ltac split_NoDup :=
repeat match goal with
| Huniq: NoDup (_++_) |- _ =>
  let H1:=fresh "Huniq" in
  let H2:=fresh "Huniq" in
  apply NoDup_split in Huniq;
  destruct Huniq as [H1 H2]
end.

Lemma NoDup_strenthening : forall A (l2 l3 l1:list A),
  NoDup (l1 ++ l2 ++ l3) -> NoDup (l1 ++ l3).
Proof.
  induction l1; simpl; intros.
    apply NoDup_split in H. destruct H; auto.

    inv H. apply NoDup_cons; auto using In_weakening.
Qed.

Lemma NoDup_split': forall A (l1 l2:list A),
  NoDup (l1++l2) ->
  NoDup l1 /\ NoDup l2 /\ (forall (a:A), In a l1 -> ~ In a l2).
Proof.
  induction l1; simpl; intros; auto.
    inv H.
    apply IHl1 in H3. destruct H3 as [J1 [J2 J3]].
    split.
      constructor; auto.
        intro J. apply H2. apply in_or_app; auto.
    split; auto.
      intros.
      destruct H as [H | H]; subst; auto.
        intro J. apply H2. apply in_or_app; auto.
Qed.

Lemma NoDup_insert: forall A (l1 l2:list A) a,
  NoDup (l1++l2) ->
  ~ In a (l1 ++ l2) ->
  NoDup (l1++a::l2).
Proof.
  induction l1; simpl; intros.
    constructor; auto.

    inv H.
    apply IHl1 with (a:=a0) in H4; auto.
    constructor; auto.
      intro J. apply H3.
      apply in_app_or in J.
      apply in_or_app.
      destruct J as [J | J]; auto.
      simpl in J.
      destruct J as [J | J]; auto.
      subst. contradict H0; auto.
Qed.

Lemma NoDup_commut: forall A (l1 l2:list A),
  NoDup (l1++l2) -> NoDup (l2++l1).
Proof.
  induction l1; simpl; intros.
    simpl_env. auto.

    inv H.
    apply NoDup_insert; auto.
    intro J. apply in_app_or in J.
    apply H2. apply in_or_app.
    destruct J as [J | J]; auto.
Qed.

Lemma NoDup_rev: forall A (l1:list A) (Huniq: NoDup l1), NoDup (rev l1).
Proof.
  induction 1; simpl; auto.
    apply NoDup_commut. simpl.
    constructor; auto.
      intro J. apply H. apply in_rev; auto.
Qed.

Lemma NoDup_app: forall A (l1 l2:list A),
  NoDup l1 -> NoDup l2 ->
  (forall (a:A), In a l1 -> ~ In a l2) ->
  NoDup (l1++l2).
Proof.
  induction l1; simpl; intros; auto.
    inv H.
    constructor; auto.
      intro J. apply in_app_or in J.
      destruct J as [J | J]; auto.
      assert (a = a \/ In a l1) as Hin. auto.
      apply H1 in Hin. auto.
Qed.

Lemma NoDup_fst__uniq: forall X (A:list (atom*X)) (Huniq: NoDup (List.map fst A)), 
  uniq A.
Proof.
  induction A as [|[] A]; simpl; intros; auto.
    inv Huniq.
    apply uniq_cons; auto.
      intro J. apply H1. apply In_fst__in_dom; auto.
Qed.

(* sublist *) 
Lemma sublist__dom: forall A (l1 l2:list (atom*A)) 
  (Hinc : sublist (List.map fst l1) (List.map fst l2)),
  dom l1 [<=] dom l2.
Proof.
  intros.
  remember (List.map fst l1) as d1.
  remember (List.map fst l2) as d2.
  generalize dependent l1.
  generalize dependent l2.
  induction Hinc; intros; subst.
    apply map_nil_inv in Heqd1.
    subst.
    fsetdec.

    symmetry in Heqd1.
    apply map_cons_inv in Heqd1.
    destruct Heqd1 as [[] [x2 [EQ1 [EQ2 EQ3]]]]; subst.
    symmetry in Heqd2.
    apply map_cons_inv in Heqd2.
    destruct Heqd2 as [[] [x2' [EQ1' [EQ2' EQ3']]]]; subst.
    simpl in EQ3'. 
    inv EQ3'.
    simpl. 
    assert (dom x2 [<=] dom x2') as Hsub.
      eapply IHHinc; eauto.
    fsetdec.

    symmetry in Heqd2.
    apply map_cons_inv in Heqd2.
    destruct Heqd2 as [[] [x2' [EQ1' [EQ2' EQ3']]]]; subst.
    simpl. 
    assert (dom l3 [<=] dom x2') as Hsub.
      eapply IHHinc; eauto.
    fsetdec.
Qed.

(* uniq *) 
Lemma uniq__iff__uniq_rev: forall X (A:list (atom*X)),
  uniq A <-> uniq (rev A).
Proof.
  induction A as [|[] A]; simpl.
    split; auto.

    split; intro J.
      inv J. 
      apply uniq_app_iff.
      split. apply IHA; auto.
      split. apply uniq_cons; auto.
        apply disjoint_one_r. 
        intro J. apply H3.
        eapply in_dom__iff__in_rev_dom; eauto.

      apply uniq_app_iff in J.
      destruct J as [J1 [J2 J3]].
      apply uniq_cons; auto.
        apply IHA; auto.

        apply disjoint_one_r in J3. 
        intro J. apply J3.
        apply in_dom__iff__in_rev_dom in J; auto.
Qed.

Lemma In_uniq_eq: forall A (id0 : atom) (ac ac':A) acs1 acs2
  (Huniq : uniq (acs1 ++ (id0, ac) :: acs2))
  (Hin1 : In (id0, ac') (acs1 ++ (id0, ac) :: acs2)),
  ac' = ac.
Proof.
  intros.
  assert (J:=Hin1).
  apply In_lookupAL in Hin1; auto.
  rewrite In_lookupAL with (v1:=ac) in Hin1; auto.
    inv Hin1. auto.
    apply in_middle.
Qed.

Lemma uniq_split_middle: forall A (cs2:AssocList A) cs2' c cs1 cs1'
  (H: uniq (cs1 ++ c :: cs2)) (H0: cs1 ++ c :: cs2 = cs1' ++ c :: cs2'),
  cs1 = cs1' /\ cs2 = cs2'.
Proof.
  induction cs1; destruct cs1'; simpl; intros.
    inv H0. auto.

    inv H0.
    inv H.
    contradict H3. simpl_env. fsetdec.

    inv H0.
    inv H.
    contradict H3. simpl_env. fsetdec.

    inv H0.
    inv H.
    eapply IHcs1 in H2; eauto.
    destruct H2 as [J1 J2]; subst; auto.
Qed.

Lemma uniq__sublist: forall A (l1 l2:list (atom*A)) 
  (Hinc: sublist (List.map fst l1) (List.map fst l2)) (Huniq: uniq l2), 
  uniq l1.
Proof.
  intros.
  remember (List.map fst l1) as d1.
  remember (List.map fst l2) as d2.
  generalize dependent l1.
  generalize dependent l2.
  induction Hinc; intros; subst.
    apply map_nil_inv in Heqd1.
    subst.
    constructor.

    symmetry in Heqd1.
    apply map_cons_inv in Heqd1.
    destruct Heqd1 as [[] [x2 [EQ1 [EQ2 EQ3]]]]; subst.
    symmetry in Heqd2.
    apply map_cons_inv in Heqd2.
    destruct Heqd2 as [[] [x2' [EQ1' [EQ2' EQ3']]]]; subst.
    simpl in EQ3'. 
    inv EQ3'.
    simpl_env. 
    inv Huniq.
    constructor.
      eapply IHHinc; eauto.
      apply sublist__dom in Hinc. fsetdec.

    symmetry in Heqd2.
    apply map_cons_inv in Heqd2.
    destruct Heqd2 as [[] [x2' [EQ1' [EQ2' EQ3']]]]; subst.
    inv Huniq.
    eauto.
Qed.

(* nth_err *)

Lemma nil_nth_error_Some__False : forall X n (v:X),
  nth_error (@nil X) n = Some v -> False.
Proof.
  induction n; intros; simpl in *; inversion H.
Qed.

Lemma nth_error_cons__inv : forall X b lb n (b':X),
  nth_error (b::lb) n = Some b' ->
  b = b' \/ (exists n', S n' = n /\ nth_error lb n' = Some b').
Proof.
  destruct n; intros; simpl in *.
    inversion H; auto.

    right. exists n. split; auto.
Qed.

Lemma nth_error_cons__inv' : forall X b lb n (b':X),
  nth_error (b::lb) n = Some b' ->
  (n = O /\ b = b') \/ (exists n', S n' = n /\ nth_error lb n' = Some b').
Proof.
  destruct n; intros; simpl in *.
    inversion H; auto.

    right. exists n. split; auto.
Qed.

Lemma nth_error_In : forall A n (l1:list A) a,
  nth_error l1 n = Some a -> In a l1.
Proof.
  induction n; simpl; intros; destruct l1; inv H; simpl; auto.
Qed.

Lemma nth_error_in {A : Type} (l : list A) (a : A) :
  In a l <-> exists n, nth_error l n = Some a.
Proof.
  split; intros H; induction l as [|a' l]; simpl in *.

    tauto. destruct H as [H | H]. subst. exists O. trivial.
    destruct IHl as [n Hn]; trivial. exists (S n). trivial.

    destruct H as [[|n] Hn]; simpl in *; discriminate.
    destruct H as [[|n] Hn]; simpl in *; eauto.
    inversion Hn. subst. auto.
Qed.

(* length *)
Lemma length_le__length_lt: forall A 
  (eq_dec : forall x y : A, {x = y}+{x <> y})
  (a:A) (l2:list A) (l1:list A) 
  (Huniq: list_norepet l1) (Hinc: incl l1 l2)  
  (Hnotin: ~ In a l1) (Hin: In a l2), 
  (length l1 < length l2)%nat.
Proof.
  intros.
  assert (incl l1 (List.remove eq_dec a l2)) as Hinc'.
    apply remove_notin_incl; eauto with datatypes.
  apply incl__length_le in Hinc'; auto.
  assert (length (List.remove eq_dec a l2) < length l2)%nat as Hle.
    apply remove_in_length; auto with datatypes.
  omega.
Qed.

Lemma len_le_zero__nil: forall A (vl:@list A) (Hlen: (0 >= length vl)%nat),
  vl = nil.
Proof.
  intros.
  destruct vl; auto.
    simpl in *. contradict Hlen. omega.
Qed.

(* atom set *)
Section MoreAtomSet.

Variable A:Type.
Variable Hdec: forall x y : atom*A, {x = y} + {x <> y}.

Lemma set_remove_spec3 : forall n n' s (Huniq: uniq s),
  In n' (set_remove Hdec n s) -> n' <> n.
Proof.
  induction 1; intros; simpl in *; auto.
    destruct (Hdec n (x, a)) as [J1 | J2]; subst; simpl in *; auto.
      intro EQ. subst.
      apply binds_dom_contradiction in H0; auto.

      destruct H0 as [H0 | H0]; subst; eauto.
Qed.

Lemma set_remove_notin_doms : forall x n E (Hnotin: x `notin` dom E),
  x `notin` dom (set_remove Hdec n E).
Proof.
  induction E as [|[] E]; simpl; intros; auto.
    destruct_if. 
Qed.

Lemma set_remove_uniq: forall n s (Huniq: uniq s), 
  uniq (set_remove Hdec n s).
Proof.
  induction 1; simpl.
    constructor. 
  
    destruct_if. simpl_env.
    constructor; auto. 
      apply set_remove_notin_doms; auto.
Qed.

Lemma set_remove__seq_eq: forall actions2 actions1 (Huniq1 : uniq actions1)
  (x : AtomSetImpl.elt) (a : A) (H2 : x `notin` dom actions2)
  (Heq : AtomSet.set_eq actions1 ((x, a) :: actions2)),
  AtomSet.set_eq (set_remove Hdec (x, a) actions1) actions2.
Proof.
  intros.
  destruct Heq as [Hincl1 Hincl2].
  split.
    intros y Hiny.
    assert (y <> (x,a)) as Hneq.
      eapply set_remove_spec3 in Hiny; eauto.
    apply AtomSet.set_remove_spec2 in Hiny.
    apply Hincl1 in Hiny.
    destruct_in Hiny; try congruence.

    intros y Hiny.
    apply AtomSet.set_remove_spec1.
      apply Hincl2. simpl. auto.
      intro EQ. subst.
      apply binds_dom_contradiction in Hiny; auto.
Qed.

End MoreAtomSet.

(* disjoint *)
Lemma disj__disjoint: forall X (A2 B2:list (atom*X)) A1 B1
  (Hdisj1: forall i, In i A1 -> ~ In i B1)
  (Hinca: forall a, a `in` dom A2 -> In a A1)
  (Hincb: forall b, b `in` dom B2 -> In b B1),
  disjoint A2 B2.
Proof.
  intros. unfold disjoint.
  unfold AtomSetImpl.Subset. intros a Hina.
  apply AtomSetFacts.inter_iff in Hina.
  destruct Hina as [Hina1 Hina2].
  apply Hinca in Hina1.
  apply Hincb in Hina2.
  apply Hdisj1 in Hina1. tauto.
Qed.

(* misc *)
Lemma neq_symmetry: forall A (x y:A), x <> y -> y <> x.
Proof. auto. Qed.

Lemma eq_nil_dec: forall A (l1:list A),
  l1 = nil \/ l1 <> nil.
Proof.
  destruct l1; auto.
    right. congruence.
Qed.

(* node set *)

Require Import Iteration.
Require Import Maps.
Require Import maps_ext.
Require Import Lattice.

Module Type NODE_SET0.

  Variable t: Type.
  Variable add: atom -> t -> t.
  Variable pick: t -> option (atom * t).
  Variable initial: ATree.t (list atom) -> t.

  Variable In: atom -> t -> Prop.
  Hypothesis add_spec:
    forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
  Hypothesis pick_none:
    forall s n, pick s = None -> ~In n s.
  Hypothesis pick_some:
    forall s n s', pick s = Some(n, s') ->
    forall n', In n' s <-> n = n' \/ In n' s'.
  Hypothesis initial_spec:
    forall successors n s,
    successors!n = Some s -> In n (initial successors).

End NODE_SET0.

Module AtomNodeSet <: NODE_SET0.
  Definition t := set atom.
  Definition add (n: atom) (s: t) : t := set_add eq_atom_dec n s.
  Definition pick (s: t) :=
    match s with
    | n::s' => Some(n, set_remove eq_atom_dec n s')
    | nil => None
    end.
  Definition initial (successors: ATree.t (list atom)) :=
    ATree.fold (fun s pc scs => add pc s) successors (empty_set atom).
  Definition In := (@set_In atom).

  Lemma add_spec:
    forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
  Proof.
    intros.
    split; intro J.
      apply (@set_add_elim atom eq_atom_dec n' n s) in J.
      destruct J; auto.

      apply (@set_add_intro atom eq_atom_dec).
      destruct J; auto.
  Qed.

  Lemma pick_none:
    forall s n, pick s = None -> ~In n s.
  Proof.
    intros until n; unfold pick.
    destruct s; auto.
      intro J. inversion J.
  Qed.

  Lemma pick_some:
    forall s n s', pick s = Some(n, s') ->
    forall n', In n' s <-> n = n' \/ In n' s'.
  Proof.
    intros until s'; unfold pick.
    destruct s; intro H0; inv H0.
    intros n'.
    split; intros.
      simpl in H.
      inv H; auto.
        destruct (eq_atom_dec n n') as [J1 | J2]; subst; auto.
          right. apply AtomSet.set_remove_spec1; auto.

      destruct H as [H | H]; subst; simpl; auto.
          right. eapply AtomSet.set_remove_spec2; eauto.
  Qed.

  Lemma initial_spec:
    forall successors n s,
    successors!n = Some s -> In n (initial successors).
  Proof.
    intros successors.
    apply ATree_Properties.fold_rec with
      (P := fun succ set =>
              forall n s, succ!n = Some s -> In n set).
    (* extensionality *)
    intros. rewrite <- H in H1. eauto.
    (* base case *)
    intros. rewrite ATree.gempty in H. congruence.
    (* inductive case *)
    intros. rewrite ATree.gsspec in H2. rewrite add_spec.
    destruct (ATree.elt_eq n k). auto. eauto.
  Qed.

  Lemma pick_in:
    forall s n s', pick s = Some(n, s') -> In n s.
  Proof.
    intros until s'; unfold pick. 
    caseEq s; intros; try congruence.
    inv H0. simpl. auto.
  Qed.
  
  Lemma initial_spec':
    forall successors n,
    In n (initial successors) -> 
    exists s, successors ! n = Some s.
  Proof.
    intros successors.
    apply ATree_Properties.fold_rec with
      (P := fun succ set =>
              forall n, In n set -> exists s, succ ! n = Some s).
    (* extensionality *)
    intros. rewrite <- H. eauto.
    (* base case *)
    intros. inv H.
    (* inductive case *)
    intros. rewrite ATree.gsspec. apply add_spec in H2.
    destruct (ATree.elt_eq n k); eauto.
      destruct H2 as [H2 | H2]; subst.
        congruence.
        eauto.
  Qed.

  Lemma NoDup__initial: forall successors, NoDup (initial successors).
  Proof.
    intro successors.
    apply ATree_Properties.fold_rec with
      (P := fun succ set => NoDup set).
      (* extensionality *)
      intros. auto.
      (* base case *)
      constructor.
      (* inductive case *)
      intros. apply AtomSet.set_add_NoDup; auto.
  Qed.

End AtomNodeSet.

(* Lattice *)
Require Import FSets.
Module Type SEMILATTICE0.

  Variable t: Type.
  Variable eq: t -> t -> Prop.
  Hypothesis eq_refl: forall x, eq x x.
  Hypothesis eq_sym: forall x y, eq x y -> eq y x.
  Hypothesis eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Variable beq: t -> t -> bool.
  Hypothesis beq_correct: forall x y, beq x y = true -> eq x y.
  Variable ge: t -> t -> Prop.
  Hypothesis ge_refl: forall x y, eq x y -> ge x y.
  Hypothesis ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Hypothesis ge_compat: forall x x' y y', eq x x' -> eq y y' -> ge x y -> ge x' y'.
  Variable bot: t.
  Hypothesis ge_bot: forall x, ge x bot.
  Variable lub: t -> t -> t.
  Hypothesis lub_commut: forall x y, eq (lub x y) (lub y x).
  Hypothesis ge_lub_left: forall x y, ge (lub x y) x.

End SEMILATTICE0.

Module Type SEMILATTICE_WITH_TOP0.

  Include Type SEMILATTICE0.
  Variable top: t.
  Hypothesis ge_top: forall x, ge top x.

End SEMILATTICE_WITH_TOP0.

Module LBoolean <: SEMILATTICE_WITH_TOP0.

Definition t := bool.

Definition eq (x y: t) := (x = y).
Definition eq_refl: forall x, eq x x := (@refl_equal t).
Definition eq_sym: forall x y, eq x y -> eq y x := (@sym_equal t).
Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@trans_equal t).

Definition beq : t -> t -> bool := eqb.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof eqb_prop.

Definition ge (x y: t) : Prop := x = y \/ x = true.

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof. unfold ge; tauto. Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof. unfold ge; intuition congruence. Qed.

Lemma ge_compat: forall x x' y y', eq x x' -> eq y y' -> ge x y -> ge x' y'.
Proof.
  unfold eq; intros; congruence.
Qed.

Definition bot := false.

Lemma ge_bot: forall x, ge x bot.
Proof. destruct x; compute; tauto. Qed.

Definition top := true.

Lemma ge_top: forall x, ge top x.
Proof. unfold ge, top; tauto. Qed.

Definition lub (x y: t) := x || y.

Lemma lub_commut: forall x y, eq (lub x y) (lub y x).
Proof. intros; unfold eq, lub. apply orb_comm. Qed.

Lemma ge_lub_left: forall x y, ge (lub x y) x.
Proof. destruct x; destruct y; compute; tauto. Qed.

Lemma ge_lub: forall x y1 y2, ge y1 y2 -> ge (lub x y1) (lub x y2).
Proof. unfold ge. intros. destruct x, y1, y2; tauto. Qed.

End LBoolean.

(** * Semi-lattice over maps *)

(** Given a semi-lattice with top [L], the following functor implements
  a semi-lattice structure over finite maps from positive numbers to [L.t].
  The default value for these maps is either [L.top] or [L.bot]. *)

Module LPMap(L: SEMILATTICE_WITH_TOP0) <: SEMILATTICE_WITH_TOP0.

Inductive t_ : Type :=
  | Bot_except: ATree'.t L.t -> t_
  | Top_except: ATree'.t L.t -> t_.

Definition t: Type := t_.

Definition get (p: atom) (x: t) : L.t :=
  match x with
  | Bot_except m =>
      match ATree'.get p m with None => L.bot | Some x => x end
  | Top_except m =>
      match ATree'.get p m with None => L.top | Some x => x end
  end.

Definition set (p: atom) (v: L.t) (x: t) : t :=
  match x with
  | Bot_except m =>
      Bot_except (if L.beq v L.bot then ATree'.remove p m else ATree'.set p v m)
  | Top_except m =>
      Top_except (if L.beq v L.top then ATree'.remove p m else ATree'.set p v m)
  end.

Lemma gss:
  forall p v x,
  L.eq (get p (set p v x)) v.
Proof.
  intros. destruct x; simpl.
  case_eq (L.beq v L.bot); intros.
  rewrite ATree'.grs. apply L.eq_sym. apply L.beq_correct; auto.
  rewrite ATree'.gss. apply L.eq_refl.
  case_eq (L.beq v L.top); intros.
  rewrite ATree'.grs. apply L.eq_sym. apply L.beq_correct; auto.
  rewrite ATree'.gss. apply L.eq_refl.
Qed.

Lemma gso:
  forall p q v x,
  p <> q -> get p (set q v x) = get p x.
Proof.
  intros. destruct x; simpl.
  destruct (L.beq v L.bot). rewrite ATree'.gro; auto. rewrite ATree'.gso; auto.
  destruct (L.beq v L.top). rewrite ATree'.gro; auto. rewrite ATree'.gso; auto.
Qed.

Definition eq (x y: t) : Prop :=
  forall p, L.eq (get p x) (get p y).

Lemma eq_refl: forall x, eq x x.
Proof.
  unfold eq; intros. apply L.eq_refl.
Qed.

Lemma eq_sym: forall x y, eq x y -> eq y x.
Proof.
  unfold eq; intros. apply L.eq_sym; auto.
Qed.

Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
Proof.
  unfold eq; intros. eapply L.eq_trans; eauto.
Qed.

Definition beq (x y: t) : bool :=
  match x, y with
  | Bot_except m, Bot_except n => ATree'.beq L.beq m n
  | Top_except m, Top_except n => ATree'.beq L.beq m n
  | _, _ => false
  end.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof.
  destruct x; destruct y; simpl; intro; try congruence.
  red; intro; simpl.
  generalize (@ATree'.beq_correct _ L.eq L.beq L.beq_correct t0 t1 H p).
  destruct (ATree'.get p t0); destruct (ATree'.get p t1); intuition. apply L.eq_refl.
  red; intro; simpl.
  generalize (@ATree'.beq_correct _ L.eq L.beq L.beq_correct t0 t1 H p).
  destruct (ATree'.get p t0); destruct (ATree'.get p t1); intuition. apply L.eq_refl.
Qed.

Definition ge (x y: t) : Prop :=
  forall p, L.ge (get p x) (get p y).

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof.
  unfold ge, eq; intros. apply L.ge_refl. auto.
Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof.
  unfold ge; intros. apply L.ge_trans with (get p y); auto.
Qed.

Lemma ge_compat: forall x x' y y', eq x x' -> eq y y' -> ge x y -> ge x' y'.
Proof.
  unfold eq,ge; intros. eapply L.ge_compat; eauto.
Qed.

Definition bot := Bot_except (ATree'.empty L.t).

Lemma get_bot: forall p, get p bot = L.bot.
Proof.
  unfold bot; intros; simpl. rewrite ATree'.gempty. auto.
Qed.

Lemma ge_bot: forall x, ge x bot.
Proof.
  unfold ge; intros. rewrite get_bot. apply L.ge_bot.
Qed.

Definition top := Top_except (ATree'.empty L.t).

Lemma get_top: forall p, get p top = L.top.
Proof.
  unfold top; intros; simpl. rewrite ATree'.gempty. auto.
Qed.

Lemma ge_top: forall x, ge top x.
Proof.
  unfold ge; intros. rewrite get_top. apply L.ge_top.
Qed.

Definition opt_lub (x y: L.t) : option L.t :=
  let z := L.lub x y in
  if L.beq z L.top then None else Some z.

Definition lub (x y: t) : t :=
  match x, y with
  | Bot_except m, Bot_except n =>
      Bot_except
        (ATree'.combine
           (fun a b =>
              match a, b with
              | Some u, Some v => Some (L.lub u v)
              | None, _ => b
              | _, None => a
              end)
           m n)
  | Bot_except m, Top_except n =>
      Top_except
        (ATree'.combine
           (fun a b =>
              match a, b with
              | Some u, Some v => opt_lub u v
              | None, _ => b
              | _, None => None
              end)
        m n)
  | Top_except m, Bot_except n =>
      Top_except
        (ATree'.combine
           (fun a b =>
              match a, b with
              | Some u, Some v => opt_lub u v
              | None, _ => None
              | _, None => a
              end)
        m n)
  | Top_except m, Top_except n =>
      Top_except
        (ATree'.combine
           (fun a b =>
              match a, b with
              | Some u, Some v => opt_lub u v
              | _, _ => None
              end)
           m n)
  end.

Lemma lub_commut:
  forall x y, eq (lub x y) (lub y x).
Proof.
  intros x y p.
  assert (forall u v,
    L.eq (match opt_lub u v with
          | Some x => x
          | None => L.top end)
         (match opt_lub v u with
         | Some x => x
         | None => L.top
         end)).
  intros. unfold opt_lub.
  case_eq (L.beq (L.lub u v) L.top);
  case_eq (L.beq (L.lub v u) L.top); intros.
  apply L.eq_refl.
  eapply L.eq_trans. apply L.eq_sym. apply L.beq_correct; eauto. apply L.lub_commut.
  eapply L.eq_trans. apply L.lub_commut. apply L.beq_correct; auto.
  apply L.lub_commut.
  destruct x; destruct y; simpl;
  repeat rewrite ATree'.gcombine; auto;
  destruct (ATree'.get p t0); destruct (ATree'.get p t1);
  auto; apply L.eq_refl || apply L.lub_commut.
Qed.

Lemma ge_lub_left:
  forall x y, ge (lub x y) x.
Proof.
  assert (forall u v,
    L.ge (match opt_lub u v with Some x => x | None => L.top end) u).
  intros; unfold opt_lub.
  case_eq (L.beq (L.lub u v) L.top); intros. apply L.ge_top. apply L.ge_lub_left.

  unfold ge, get, lub; intros; destruct x; destruct y.

  rewrite ATree'.gcombine; auto.
  destruct (ATree'.get p t0); destruct (ATree'.get p t1).
  apply L.ge_lub_left.
  apply L.ge_refl. apply L.eq_refl.
  apply L.ge_bot.
  apply L.ge_refl. apply L.eq_refl.

  rewrite ATree'.gcombine; auto.
  destruct (ATree'.get p t0); destruct (ATree'.get p t1).
  auto.
  apply L.ge_top.
  apply L.ge_bot.
  apply L.ge_top.

  rewrite ATree'.gcombine; auto.
  destruct (ATree'.get p t0); destruct (ATree'.get p t1).
  auto.
  apply L.ge_refl. apply L.eq_refl.
  apply L.ge_top.
  apply L.ge_top.

  rewrite ATree'.gcombine; auto.
  destruct (ATree'.get p t0); destruct (ATree'.get p t1).
  auto.
  apply L.ge_top.
  apply L.ge_top.
  apply L.ge_top.
Qed.

End LPMap.

(** * Domination analysis *)

(** The type [Dominators] of compile-time approximations of domination. *)

(** We equip this type of approximations with a semi-lattice structure.
  The ordering is inclusion between the sets of values denoted by
  the approximations. *)

Module Dominators <: SEMILATTICE_WITH_TOP0.

  Require Import ListSet.
  Export AtomSet.

  Definition t := option (set atom).

  Definition eq (x y: t) :=
    match x, y with
    | Some cx, Some cy => set_eq cx cy
    | None, None => True
    | _, _ => False
    end.

  Definition eq_refl: forall x, eq x x.
  Proof.
    unfold eq. intro x. destruct x; auto with atomset.
  Qed.

  Definition eq_sym: forall x y, eq x y -> eq y x.
  Proof.
    unfold eq. intros x y J. destruct x; destruct y; auto with atomset.
  Qed.

  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    unfold eq. intros x y z J1 J2. 
    destruct x; destruct y; destruct z; eauto with atomset. tauto.
  Qed.

  Lemma eq_dec: forall (x y: t), {eq x y} + {~ eq x y}.
  Proof.
    unfold eq. destruct x; destruct y; auto.
    apply set_eq_dec. apply eq_atom_dec.
  Qed.

  Definition beq (x y: t) := if eq_dec x y then true else false.

  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    unfold beq; intros.  destruct (eq_dec x y). auto. congruence.
  Qed.

  Definition sub (x y: t) :=
    match x, y with
    | Some cx, Some cy => incl cx cy
    | _, None => True
    | _, _ => False
    end.

  Definition top : t := Some (empty_set atom).

  Definition bot : t := None.

  Definition ge (x y: t) : Prop := sub x y.

  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    unfold ge, eq. destruct x, y; simpl; auto. 
    intro J. destruct J; auto.
  Qed.

  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    unfold ge. 
    destruct x, y, z; simpl; eauto 2 with datatypes.
      tauto.
  Qed.

  Lemma ge_compat: forall x x' y y', eq x x' -> eq y y' -> ge x y -> ge x' y'.
  Proof.
    unfold ge, eq. 
    destruct x, x', y, y'; simpl; try solve [eauto 2 with atomset | tauto].
  Qed.

  Lemma ge_bot: forall x, ge x bot.
  Proof.
    unfold ge, eq, sub. destruct x; simpl; auto with atomset.
  Qed.

  Lemma ge_top: forall x, ge top x.
  Proof.
    unfold ge, eq, sub. destruct x; simpl; auto with atomset.
  Qed.

  Definition lub (x y: t) : t :=
    match x, y with
    | Some cx, Some cy => Some (set_inter eq_atom_dec cx cy)
    | None, _ => y
    | _, None => x
    end.

  Lemma lub_commut: forall x y, eq (lub x y) (lub y x).
  Proof.
    unfold lub, eq. destruct x, y; auto with atomset.
  Qed.

  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    unfold lub, ge, sub. destruct x, y; simpl; auto with datatypes.
    intros a J.
    apply set_inter_elim in J. destruct J. auto.
  Qed.

  Lemma ge_lub_right:
    forall x y, ge (lub x y) y.
  Proof.
    intros.
    apply ge_compat with (x:=lub y x)(y:=y).
      apply lub_commut.
      apply eq_refl.
      apply ge_lub_left.
  Qed.

  Lemma lub_preserves_ge : forall x y, ge x y -> eq (lub x y) x.
  Proof.
    unfold lub, ge, eq. destruct x, y; simpl; auto with atomset.
  Qed.

  Lemma lub_compat : forall x y x' y',
    ge x x' -> ge y y' -> ge (lub x y) (lub x' y').
  Proof.
    unfold lub, ge, eq. 
    destruct x, y, x', y'; simpl; try solve [
      tauto | eauto 2 with atomset | 
      intros; eapply incl_tran; eauto; eauto 2 with atomset
    ].
  Qed.

  Lemma lub_refl : forall x, eq x (lub x x).
  Proof.
    unfold eq, lub. destruct x; auto with atomset.
  Qed.

  Lemma ge_top_inv : forall x, ge x top -> eq x top.
  Proof.
    unfold ge, top. destruct x; simpl; auto.
    intros J.
    apply incl_empty_inv in J. subst. auto with atomset.
  Qed.

  Lemma ge_antisym : forall x y, ge x y -> ge y x -> eq x y.
  Proof.
    destruct x, y; simpl; auto.
    intros J1 J2. split; auto.
  Qed.

  Lemma lub_compat' : forall x y1 y2, ge x y1 -> ge x y2 -> ge x (lub y1 y2).
  Proof.
    intros.
    apply ge_trans with (y:=lub x x).
      apply ge_refl. apply lub_refl.
      apply lub_compat; auto.
  Qed.

  Lemma ge_lub_left' : forall a p1 p2, ge p2 p1 -> ge (lub p2 a) p1.
  Proof.
    intros.
    apply ge_trans with (y:=p2); auto.
    apply ge_lub_left.
  Qed.

  Lemma ge_refl' : forall x, ge x x.
  Proof.
    intros. apply ge_refl. apply eq_refl.
  Qed.

  Definition add (x:t) (a:atom) : t :=
    match x with
    | Some cx => Some (a::cx)
    | None => None
    end.

  Lemma add_mono: forall a x y, ge x y -> ge (add x a) (add y a).
  Proof.
    unfold ge, add, eq, sub. destruct x, y; simpl; auto.
    intros.
    intros x J. simpl in J.
    destruct J as [J | J]; subst; simpl; auto.
  Qed.

  Definition member (a:atom) (x: t) :=
    match x with
    | Some cx => In a cx
    | None => True
    end.

  Lemma add_member1: forall a x,
    member a (add x a).
  Proof.
    unfold member, add. destruct x; simpl; auto.
  Qed.

  Lemma add_member2: forall a b x,
    member a x -> member a (add x b).
  Proof.
    unfold member, add. destruct x; simpl; auto.
  Qed.

  Lemma member_eq : forall a x1 x2, eq x1 x2 -> member a x2 -> member a x1.
  Proof.
    unfold member, eq. destruct x1, x2; simpl; try solve [auto | tauto].
    intros H H1. destruct H. auto.
  Qed.

  Lemma member_lub : forall a x1 x2,
    member a x2 -> member a x1 -> member a (lub x1 x2).
  Proof.
    unfold member, lub. destruct x1, x2; simpl; auto.
    intros. apply set_inter_intro; auto.
  Qed.

  Lemma ge_elim : forall a x y, ge x y -> member a x -> member a y.
  Proof.
    unfold member, ge. destruct x, y; simpl; try solve [auto | tauto].
  Qed.

  Lemma member_dec: forall a x, member a x \/ ~ member a x.
  Proof.
    unfold member. destruct x; simpl; auto.
    destruct (in_dec eq_atom_dec a s); auto.
  Qed.

  Lemma lub_compat_eq : forall x y x' y',
    eq x x' -> eq y y' -> eq (lub x y) (lub x' y').
  Proof.
    unfold lub, eq. destruct x, y, x', y'; simpl; try solve [auto | tauto].
    intros J1 J2. auto with atomset.
  Qed.

  Lemma add_bot: forall a, eq (add bot a) bot.
  Proof.
    unfold eq, add, bot. intros. auto.
  Qed.

  Lemma add_eq: forall a x y, eq x y -> eq (add x a) (add y a).
  Proof.
    unfold eq, add. destruct x, y; simpl; auto.
    intros [H1 H2].
    split; intros x J; simpl in *; destruct J; subst; auto.
  Qed.

  Lemma lub_intro: forall a x y, member a x -> member a y -> member a (lub x y).
  Proof.
    unfold member, lub. destruct x, y; simpl; auto.
    intros. apply set_inter_intro; auto.
  Qed.

  Definition lubs (pds: list t) : t :=
    fold_left (fun acc => fun p => lub acc p) pds bot.

  Lemma lubs_spec1: forall pds p2 p1,
    ge p2 p1 -> ge (fold_left (fun acc => fun p => lub acc p) pds p2) p1.
  Proof.
    induction pds; simpl; intros; auto.
      apply IHpds. apply ge_lub_left'; auto.
  Qed.

  Lemma lubs_spec2_aux: forall pds p2 p1, In p1 pds ->
    ge (fold_left (fun acc => fun p => lub acc p) pds p2) p1.
  Proof.
    induction pds; simpl; intros.
      inversion H.
      destruct H as [H | H]; subst.
        apply lubs_spec1.
          apply ge_lub_right; auto.
        apply IHpds; auto.
  Qed.

  Lemma lubs_spec2: forall pds p1, In p1 pds ->
    ge (lubs pds) p1.
  Proof.
    unfold lubs. intros. apply lubs_spec2_aux; auto.
  Qed.

  Lemma lubs_spec3_aux: forall p0 pds p2,
    ge p0 p2 ->
    (forall p, In p pds -> ge p0 p) ->
    ge p0 (fold_left (fun acc => fun p => lub acc p) pds p2).
  Proof.
    induction pds; simpl; intros; auto.
      apply IHpds; auto.
        apply lub_compat'; auto.
  Qed.

  Lemma lubs_spec3: forall pds p1,
    (forall p, In p pds -> ge p1 p) -> ge p1 (lubs pds).
  Proof.
    unfold lubs. intros. apply lubs_spec3_aux; auto.
      apply ge_bot.
  Qed.

  Definition gt (x y: t) : Prop := 
  match x, y with
  | Some _, None => True
  | Some x', Some y' => incl x' y' /\ exists a, In a y' /\ ~ In a x'
  | _, _ => False
  end.

  Lemma beq_correct': forall x y, beq x y = false -> ~ eq x y.
  Proof.
    unfold beq; intros. 
    destruct (eq_dec x y). 
      congruence.
      auto. 
  Qed.

  Lemma ge__gt_or_eq: forall x y (Hge: ge x y), eq x y \/ gt x y.
  Proof.
    unfold ge, gt.
    intros.
    destruct x as [x|].
      destruct y as [y|]; auto.
        simpl in Hge. assert (J:=Hge). 
        apply incl__eq_or_exact in J; auto.
        destruct J as [EQ | [e [Hin Hnotin]]]; subst; auto.
          right. split; eauto.
      left.
      destruct y as [y|]; try tauto.
  Qed.

End Dominators.

Module Type DATAFLOW_SOLVER0.

  Declare Module L: SEMILATTICE0.

  Variable fixpoint:
    forall (successors: ATree.t (list atom))
           (transf: atom -> L.t -> L.t)
           (entrypoints: list (atom * L.t)),
    option (AMap.t L.t).

  (** [fixpoint successors transf entrypoints] is the solver.
    It returns either an error or a mapping from program points to
    values of type [L.t] representing the solution.  [successors]
    is a finite map returning the list of successors of the given program
    point. [transf] is the transfer function, and [entrypoints] the additional
    constraints imposed on the solution. *)

  Hypothesis fixpoint_solution:
    forall successors transf entrypoints res n s,
    fixpoint successors transf entrypoints = Some res ->
    In s successors!!!n ->
    L.ge res!!s (transf n res!!n).

  (** The [fixpoint_solution] theorem shows that the returned solution,
    if any, satisfies the dataflow inequations. *)

  Hypothesis fixpoint_entry:
    forall successors transf entrypoints res n v,
    fixpoint successors transf entrypoints = Some res ->
    In (n, v) entrypoints ->
    L.ge res!!n v.

  (** The [fixpoint_entry] theorem shows that the returned solution,
    if any, satisfies the additional constraints expressed
    by [entrypoints]. *)

  Hypothesis fixpoint_invariant:
    forall successors transf entrypoints
           (P: L.t -> Prop),
    P L.bot ->
    (forall x y, P x -> P y -> P (L.lub x y)) ->
    (forall pc x, P x -> P (transf pc x)) ->
    (forall n v, In (n, v) entrypoints -> P v) ->
    forall res pc,
    fixpoint successors transf entrypoints = Some res ->
    P res!!pc.

  (** Finally, any property that is preserved by [L.lub] and [transf]
      and that holds for [L.bot] also holds for the results of
      the analysis. *)

  Hypothesis fixpoint_inv:
    forall (successors: ATree.t (list atom)) (transf: atom -> L.t -> L.t)
           (entrypoints: list (atom * L.t)) (P: atom -> L.t -> Prop)
    (P_bot: forall n, P n L.bot)
    (P_lub: forall n x y, P n x -> P n y -> P n (L.lub x y))
    (P_transf: forall pc sc x y (Hin: In sc (successors!!!pc))
      (HPx: P pc x) (HPy: P sc y), P sc (L.lub y (transf pc x)))
    (P_entrypoints: forall n v, In (n, v) entrypoints -> P n v)
    (transf_mono: forall p x y,
       L.ge x y -> L.ge (transf p x) (transf p y))
    (ge_lub: forall x y1 y2, 
       L.ge y1 y2 -> L.ge (L.lub x y1) (L.lub x y2))
    (P_ge: forall n x y, L.ge x y -> P n x -> P n y),
    forall res,
    fixpoint successors transf entrypoints = Some res ->
    forall pc, P pc res!!pc.

  (** A variant of fixpoint_invariant *)

End DATAFLOW_SOLVER0.

(** We now define a generic solver that works over
    any semi-lattice structure. *)

Module Dataflow_Solver (LAT: SEMILATTICE0) (NS: NODE_SET0):
                          DATAFLOW_SOLVER0 with Module L := LAT.

Module L := LAT.

Section Kildall.

Variable successors: ATree.t (list atom).
Variable transf: atom -> L.t -> L.t.
Variable entrypoints: list (atom * L.t).

(** The state of the iteration has two components:
- A mapping from program points to values of type [L.t] representing
  the candidate solution found so far.
- A worklist of program points that remain to be considered.
*)

Record state : Type :=
  mkstate { st_in: AMap.t L.t; st_wrk: NS.t }.

(** Kildall's algorithm, in pseudo-code, is as follows:
<<
    while st_wrk is not empty, do
        extract a node n from st_wrk
        compute out = transf n st_in[n]
        for each successor s of n:
            compute in = lub st_in[s] out
            if in <> st_in[s]:
                st_in[s] := in
                st_wrk := st_wrk union {s}
            end if
        end for
    end while
    return st_in
>>

The initial state is built as follows:
- The initial mapping sets all program points to [L.bot], except
  those mentioned in the [entrypoints] list, for which we take
  the associated approximation as initial value.  Since a program
  point can be mentioned several times in [entrypoints], with different
  approximations, we actually take the l.u.b. of these approximations.
- The initial worklist contains all the program points. *)

Fixpoint start_state_in (ep: list (atom * L.t)) : AMap.t L.t :=
  match ep with
  | nil =>
      AMap.init L.bot
  | (n, v) :: rem =>
      let m := start_state_in rem in AMap.set n (L.lub m!!n v) m
  end.

Definition start_state :=
  mkstate (start_state_in entrypoints) (NS.initial successors).

(** [propagate_succ] corresponds, in the pseudocode,
  to the body of the [for] loop iterating over all successors. *)

Definition propagate_succ (s: state) (out: L.t) (n: atom) :=
  let oldl := s.(st_in)!!n in
  let newl := L.lub oldl out in
  if L.beq oldl newl
  then s
  else mkstate (AMap.set n newl s.(st_in)) (NS.add n s.(st_wrk)).

(** [propagate_succ_list] corresponds, in the pseudocode,
  to the [for] loop iterating over all successors. *)

Fixpoint propagate_succ_list (s: state) (out: L.t) (succs: list atom)
                             {struct succs} : state :=
  match succs with
  | nil => s
  | n :: rem => propagate_succ_list (propagate_succ s out n) out rem
  end.

(** [step] corresponds to the body of the outer [while] loop in the
  pseudocode. *)

Definition step (s: state) : AMap.t L.t + state :=
  match NS.pick s.(st_wrk) with
  | None =>
      inl _ s.(st_in)
  | Some(n, rem) =>
      inr _ (propagate_succ_list
              (mkstate s.(st_in) rem)
              (transf n s.(st_in)!!n)
              (successors!!!n))
  end.

(** The whole fixpoint computation is the iteration of [step] from
  the start state. *)

Definition fixpoint : option (AMap.t L.t) :=
  PrimIter.iterate _ _ step start_state.

(** ** Monotonicity properties *)

(** We first show that the [st_in] part of the state evolves monotonically:
  at each step, the values of the [st_in[n]] either remain the same or
  increase with respect to the [L.ge] ordering. *)

Definition in_incr (in1 in2: AMap.t L.t) : Prop :=
  forall n, L.ge in2!!n in1!!n.

Lemma in_incr_refl:
  forall in1, in_incr in1 in1.
Proof.
  unfold in_incr; intros. apply L.ge_refl. apply L.eq_refl.
Qed.

Lemma in_incr_trans:
  forall in1 in2 in3, in_incr in1 in2 -> in_incr in2 in3 -> in_incr in1 in3.
Proof.
  unfold in_incr; intros. apply L.ge_trans with in2!!n; auto.
Qed.

Lemma propagate_succ_incr:
  forall st out n,
  in_incr st.(st_in) (propagate_succ st out n).(st_in).
Proof.
  unfold in_incr, propagate_succ; simpl; intros.
  match goal with [|- context[if ?b then _ else _]] => 
      case b
  end.
  apply L.ge_refl. apply L.eq_refl.
  simpl. case (eq_atom_dec n n0); intro.
  subst n0. rewrite AMap.gss. apply L.ge_lub_left.
  rewrite AMap.gso; auto. apply L.ge_refl. apply L.eq_refl.
Qed.

Lemma propagate_succ_list_incr:
  forall out scs st,
  in_incr st.(st_in) (propagate_succ_list st out scs).(st_in).
Proof.
  induction scs; simpl; intros.
  apply in_incr_refl.
  apply in_incr_trans with (propagate_succ st out a).(st_in).
  apply propagate_succ_incr. auto.
Qed.

Lemma fixpoint_incr:
  forall res,
  fixpoint = Some res -> in_incr (start_state_in entrypoints) res.
Proof.
  unfold fixpoint; intros.
  change (start_state_in entrypoints) with start_state.(st_in).
  eapply (PrimIter.iterate_prop _ _ step
    (fun st => in_incr start_state.(st_in) st.(st_in))
    (fun res => in_incr start_state.(st_in) res)).

  intros st INCR. unfold step.
  destruct (NS.pick st.(st_wrk)) as [ [n rem] | ].
  apply in_incr_trans with st.(st_in). auto.
  change st.(st_in) with (mkstate st.(st_in) rem).(st_in).
  apply propagate_succ_list_incr.
  auto.

  eauto. apply in_incr_refl.
Qed.

(** ** Correctness invariant *)

(** The following invariant is preserved at each iteration of Kildall's
  algorithm: for all program points [n], either
  [n] is in the worklist, or the inequations associated with [n]
  ([st_in[s] >= transf n st_in[n]] for all successors [s] of [n])
  hold.  In other terms, the worklist contains all nodes that do not
  yet satisfy their inequations. *)

Definition good_state (st: state) : Prop :=
  forall n,
  NS.In n st.(st_wrk) \/
  (forall s, In s (successors!!!n) ->
             L.ge st.(st_in)!!s (transf n st.(st_in)!!n)).

(** We show that the start state satisfies the invariant, and that
  the [step] function preserves it. *)

Lemma start_state_good:
  good_state start_state.
Proof.
  unfold good_state, start_state; intros.
  case_eq (successors!n); intros.
  left; simpl. eapply NS.initial_spec. eauto.
  unfold XATree.successors_list. rewrite H. right; intros. contradiction.
Qed.

Lemma propagate_succ_charact:
  forall st out n,
  let st' := propagate_succ st out n in
  L.ge st'.(st_in)!!n out /\
  (forall s, n <> s -> st'.(st_in)!!s = st.(st_in)!!s).
Proof.
  unfold propagate_succ; intros; simpl.
  match goal with
    [|- context[if L.beq ?l1 ?l2 then _ else _]] =>
      predSpec L.beq L.beq_correct l1 l2
  end.
  split.
  eapply L.ge_trans. apply L.ge_refl. apply H; auto.
  eapply L.ge_compat. apply L.lub_commut. apply L.eq_refl.
  apply L.ge_lub_left.
  auto.

  simpl. split.
  rewrite AMap.gss.
  eapply L.ge_compat. apply L.lub_commut. apply L.eq_refl.
  apply L.ge_lub_left.
  intros. rewrite AMap.gso; auto.
Qed.

Lemma propagate_succ_list_charact:
  forall out scs st,
  let st' := propagate_succ_list st out scs in
  forall s,
  (In s scs -> L.ge st'.(st_in)!!s out) /\
  (~(In s scs) -> st'.(st_in)!!s = st.(st_in)!!s).
Proof.
  induction scs; simpl; intros.
  tauto.
  generalize (IHscs (propagate_succ st out a) s). intros [A B].
  generalize (propagate_succ_charact st out a). intros [C D].
  split; intros.
  elim H; intro.
  subst s.
  apply L.ge_trans with (propagate_succ st out a).(st_in)!!a.
  apply propagate_succ_list_incr. assumption.

  apply A. auto.
  transitivity (propagate_succ st out a).(st_in)!!s.
  apply B. tauto.
  apply D. tauto.
Qed.

Lemma propagate_succ_incr_worklist:
  forall st out n x,
  NS.In x st.(st_wrk) -> NS.In x (propagate_succ st out n).(st_wrk).
Proof.
  intros. unfold propagate_succ.
  match goal with
    [|- context[if ?c then _ else _]] =>
      case c
  end.
  auto.
  simpl. rewrite NS.add_spec. auto.
Qed.

Lemma propagate_succ_list_incr_worklist:
  forall out scs st x,
  NS.In x st.(st_wrk) -> NS.In x (propagate_succ_list st out scs).(st_wrk).
Proof.
  induction scs; simpl; intros.
  auto.
  apply IHscs. apply propagate_succ_incr_worklist. auto.
Qed.

Lemma propagate_succ_records_changes:
  forall st out n s,
  let st' := propagate_succ st out n in
  NS.In s st'.(st_wrk) \/ st'.(st_in)!!s = st.(st_in)!!s.
Proof.
  simpl. intros. unfold propagate_succ.
  case (L.beq (st_in st) !! n (L.lub (st_in st) !! n out)).
  right; auto.
  case (eq_atom_dec s n); intro.
  subst s. left. simpl. rewrite NS.add_spec. auto.
  right. simpl. apply AMap.gso. auto.
Qed.

Lemma propagate_succ_list_records_changes:
  forall out scs st s,
  let st' := propagate_succ_list st out scs in
  NS.In s st'.(st_wrk) \/ st'.(st_in)!!s = st.(st_in)!!s.
Proof.
  induction scs; simpl; intros.
  right; auto.
  elim (propagate_succ_records_changes st out a s); intro.
  left. apply propagate_succ_list_incr_worklist. auto.
  rewrite <- H. auto.
Qed.

Lemma step_state_good:
  forall st n rem,
  NS.pick st.(st_wrk) = Some(n, rem) ->
  good_state st ->
  good_state (propagate_succ_list (mkstate st.(st_in) rem)
                                  (transf n st.(st_in)!!n)
                                  (successors!!!n)).
Proof.
  unfold good_state. intros st n rem WKL GOOD x.
  generalize (NS.pick_some _ _ _ WKL); intro PICK.
  set (out := transf n st.(st_in)!!n).
  match goal with
    [|- context[propagate_succ_list _ _ ?k]] =>
      elim (propagate_succ_list_records_changes
          out k (mkstate st.(st_in) rem) x)
  end.
  (*elim (propagate_succ_list_records_changes
          out (successors!!!n) (mkstate st.(st_in) rem) x).*)
  intro; left; auto.
  simpl; intros EQ. rewrite EQ.
  case (eq_atom_dec x n); intro.
  (* Case 1: x = n *)
  subst x.
  right; intros.
  elim (propagate_succ_list_charact out (successors!!!n)
          (mkstate st.(st_in) rem) s); intros.
  auto.
  (* Case 2: x <> n *)
  elim (GOOD x); intro.
  (* Case 2.1: x was already in worklist, still is *)
  left. apply propagate_succ_list_incr_worklist.
  simpl. rewrite PICK in H. elim H; intro. congruence. auto.
  (* Case 2.2: x was not in worklist *)
  right; intros.
  case (In_dec eq_atom_dec s (successors!!!n)); intro.
  (* Case 2.2.1: s is a successor of n, it may have increased *)
  apply L.ge_trans with st.(st_in)!!s.
  change st.(st_in)!!s with (mkstate st.(st_in) rem).(st_in)!!s.
  apply propagate_succ_list_incr.
  auto.
  (* Case 2.2.2: s is not a successor of n, it did not change *)
  elim (propagate_succ_list_charact out (successors!!!n)
          (mkstate st.(st_in) rem) s); intros.
  rewrite H2. simpl. auto. auto.
Qed.

(** ** Correctness of the solution returned by [iterate]. *)

(** As a consequence of the [good_state] invariant, the result of
  [fixpoint], if defined, is a solution of the dataflow inequations,
  since [st_wrk] is empty when the iteration terminates. *)

Theorem fixpoint_solution:
  forall res n s,
  fixpoint = Some res ->
  In s (successors!!!n) ->
  L.ge res!!s (transf n res!!n).
Proof.
  assert (forall res, fixpoint = Some res ->
          forall n s,
          In s successors!!!n ->
          L.ge res!!s (transf n res!!n)).
  unfold fixpoint. intros res PI. pattern res.
  eapply (PrimIter.iterate_prop _ _ step good_state).

  intros st GOOD. unfold step.
  caseEq (NS.pick st.(st_wrk)).
  intros [n rem] PICK. apply step_state_good; auto.
  intros.
  elim (GOOD n); intro.
  elim (NS.pick_none _ n H). auto.
  auto.

  eauto. apply start_state_good. eauto.
Qed.

(** As a consequence of the monotonicity property, the result of
  [fixpoint], if defined, is pointwise greater than or equal the
  initial mapping.  Therefore, it satisfies the additional constraints
  stated in [entrypoints]. *)

Lemma start_state_in_entry:
  forall ep n v,
  In (n, v) ep ->
  L.ge (start_state_in ep)!!n v.
Proof.
  induction ep; simpl; intros.
  elim H.
  elim H; intros.
  subst a. rewrite AMap.gss.
  eapply L.ge_compat. apply L.lub_commut. apply L.eq_refl.
  apply L.ge_lub_left.
  destruct a. rewrite AMap.gsspec. case (eq_atom_dec n a); intro.
  subst a. apply L.ge_trans with (start_state_in ep)!!n.
  apply L.ge_lub_left. auto.
  auto.
Qed.

Theorem fixpoint_entry:
  forall res n v,
  fixpoint = Some res ->
  In (n, v) entrypoints ->
  L.ge res!!n v.
Proof.
  intros.
  apply L.ge_trans with (start_state_in entrypoints)!!n.
  apply fixpoint_incr. auto.
  apply start_state_in_entry. auto.
Qed.

(** ** Preservation of a property over solutions *)

Variable P: L.t -> Prop.
Hypothesis P_bot: P L.bot.
Hypothesis P_lub: forall x y, P x -> P y -> P (L.lub x y).
Hypothesis P_transf: forall pc x, P x -> P (transf pc x).
Hypothesis P_entrypoints: forall n v, In (n, v) entrypoints -> P v.

Theorem fixpoint_invariant:
  forall res pc,
  fixpoint = Some res ->
  P res!!pc.
Proof.
  assert (forall ep,
          (forall n v, In (n, v) ep -> P v) ->
          forall pc, P (start_state_in ep)!!pc).
    induction ep; intros; simpl.
    rewrite AMap.gi. auto.
    simpl in H.
    assert (P (start_state_in ep)!!pc). apply IHep. eauto.
    destruct a as [n v]. rewrite AMap.gsspec. destruct (eq_atom_dec pc n).
    apply P_lub. subst. auto. eapply H. left; reflexivity. auto.
  set (inv := fun st => forall pc, P (st.(st_in)!!pc)).
  assert (forall st v n, inv st -> P v -> inv (propagate_succ st v n)).
    unfold inv, propagate_succ. intros.
    destruct (LAT.beq (st_in st)!!n (LAT.lub (st_in st)!!n v)).
    auto. simpl. rewrite AMap.gsspec. destruct (eq_atom_dec pc n).
    apply P_lub. subst n; auto. auto.
    auto.
  assert (forall l st v, inv st -> P v -> inv (propagate_succ_list st v l)).
    induction l; intros; simpl. auto.
    apply IHl; auto.
  assert (forall res, fixpoint = Some res -> forall pc, P res!!pc).
    unfold fixpoint. intros res0 RES0. pattern res0.
    eapply (PrimIter.iterate_prop _ _ step inv).
    intros. unfold step. destruct (NS.pick (st_wrk a)) as [[n rem] | ].
    apply H1. auto. apply P_transf. apply H2.
    assumption.
    eauto.
    unfold inv, start_state; simpl. auto.
  intros. auto.
Qed.

End Kildall.

Section FixpointInv.

(* A variant of fixpoint_invariant *)

Variable successors: ATree.t (list atom).
Variable transf: atom -> L.t -> L.t.
Variable entrypoints: list (atom * L.t).

Variable P: atom -> L.t -> Prop.
Definition inv := fun st => forall pc, P pc (st.(st_in)!!pc).
Hypothesis P_bot: forall n, P n L.bot.
Hypothesis P_lub: forall n x y, P n x -> P n y -> P n (L.lub x y).
Hypothesis P_transf: 
  forall pc sc x y (Hin: In sc (successors!!!pc))
    (HPx: P pc x) (HPy: P sc y), P sc (L.lub y (transf pc x)).
Hypothesis P_entrypoints: forall n v, In (n, v) entrypoints -> P n v.
Hypothesis transf_mono: forall p x y,
  L.ge x y -> L.ge (transf p x) (transf p y).
Hypothesis ge_lub: forall x y1 y2, 
  L.ge y1 y2 -> L.ge (L.lub x y1) (L.lub x y2).
Hypothesis P_ge: forall n x y, L.ge x y -> P n x -> P n y.

Lemma propagate_succ_inv: forall st n sc out
  (Hin: In sc successors!!!n)
  (Hge: L.ge (transf n st.(st_in)!!n) out)
  (Hinv: inv st),
  inv (propagate_succ st out sc).
Proof.
  unfold inv.
  intros.
  destruct (eq_atom_dec sc pc) as [Heq | Hneq]; subst.
    unfold propagate_succ.
    destruct (L.beq (st_in st) !! pc (L.lub (st_in st) !! pc out)); auto.
    simpl.
    rewrite AMap.gss. 
    eapply P_transf in Hin; eauto.

    destruct (propagate_succ_charact st out sc) as [J1 J2].
    rewrite J2; auto.
Qed.

Lemma propagate_succ_list_inv_aux: forall n scs st out,
  (forall s, In s scs -> In s successors!!!n) ->
  L.ge (transf n st.(st_in)!!n) out ->
  inv st ->
  inv (propagate_succ_list st out scs).
Proof.
  induction scs; simpl; intros; auto.
    apply IHscs; auto.
      apply L.ge_trans with (y:=(transf n (st_in st) !! n)); auto.
        apply transf_mono.
        apply propagate_succ_incr.
      eapply propagate_succ_inv; eauto.
Qed.

Lemma propagate_succ_list_inv: forall n scs st,
  (forall s, In s scs -> In s successors!!!n) ->
  inv st ->
  inv (propagate_succ_list st (transf n st.(st_in)!!n) scs).
Proof.
  intros.
  eapply propagate_succ_list_inv_aux; eauto.
    apply L.ge_refl. apply L.eq_refl.
Qed.

Lemma step_inv: forall st n rem,
  NS.pick st.(st_wrk) = Some(n, rem) ->
  inv st ->
  inv (propagate_succ_list (mkstate st.(st_in) rem)
                           (transf n st.(st_in)!!n)
                           (successors!!!n)).
Proof.
  intros st n rem WKL GOOD.
  destruct st. simpl.
  apply propagate_succ_list_inv; auto.
Qed.

Lemma entry_inv: inv (start_state successors entrypoints).
Proof.
  unfold inv.
  unfold start_state. simpl.
  induction entrypoints as [|[n v] ep]; intros; simpl.
    rewrite AMap.gi. auto.

    simpl in P_entrypoints.
    assert (P pc (start_state_in ep)!!pc) as J. 
      apply IHep. eauto.
    rewrite AMap.gsspec.
    destruct (eq_atom_dec pc n); subst.
      apply P_lub. auto. 
        eapply P_entrypoints. left; reflexivity. 
      auto.
Qed.

Theorem fixpoint_inv:
  forall res,
  fixpoint successors transf entrypoints = Some res ->
  forall pc, P pc res!!pc.
Proof.
  unfold fixpoint. intros res PI. pattern res.
  eapply (PrimIter.iterate_prop _ _ (step _ _) inv); eauto.
    intros st GOOD. unfold step.
    caseEq (NS.pick st.(st_wrk)); auto. 
    intros [n rem] PICK. 
    apply step_inv; auto.

    apply entry_inv; auto.
Qed.

End FixpointInv.

End Dataflow_Solver.

Module Dataflow_Solver_Var_Top (NS: NODE_SET0).

Module L := Dominators.

Section Kildall.

Variable successors: ATree.t (list atom).
Variable transf: atom -> L.t -> L.t.
Variable entrypoints: list (atom * L.t).

(** The state of the iteration has two components:
- A mapping from program points to values of type [L.t] representing
  the candidate solution found so far.
- A worklist of program points that remain to be considered.
*)

Record state : Type :=
  mkstate { st_in: AMap.t L.t; st_wrk: NS.t }.

(** Kildall's algorithm, in pseudo-code, is as follows:
<<
    while st_wrk is not empty, do
        extract a node n from st_wrk
        compute out = transf n st_in[n]
        for each successor s of n:
            compute in = lub st_in[s] out
            if in <> st_in[s]:
                st_in[s] := in
                st_wrk := st_wrk union {s}
            end if
        end for
    end while
    return st_in
>>

The initial state is built as follows:
- The initial mapping sets all program points to [L.bot], except
  those mentioned in the [entrypoints] list, for which we take
  the associated approximation as initial value.  Since a program
  point can be mentioned several times in [entrypoints], with different
  approximations, we actually take the l.u.b. of these approximations.
- The initial worklist contains all the program points. *)

Fixpoint start_state_in (ep: list (atom * L.t)) : AMap.t L.t :=
  match ep with
  | nil =>
      AMap.init L.bot
  | (n, v) :: rem =>
      let m := start_state_in rem in AMap.set n (L.lub m!!n v) m
  end.

Definition start_state :=
  mkstate (start_state_in entrypoints) (NS.initial successors).

(** [propagate_succ] corresponds, in the pseudocode,
  to the body of the [for] loop iterating over all successors. *)

Definition propagate_succ (s: state) (out: L.t) (n: atom) :=
  let oldl := s.(st_in)!!n in
  let newl := L.lub oldl out in
  if L.beq oldl newl
  then s
  else mkstate (AMap.set n newl s.(st_in)) (NS.add n s.(st_wrk)).

(** [propagate_succ_list] corresponds, in the pseudocode,
  to the [for] loop iterating over all successors. *)

Fixpoint propagate_succ_list (s: state) (out: L.t) (succs: set atom)
                             {struct succs} : state :=
  match succs with
  | nil => s
  | n :: rem => propagate_succ_list (propagate_succ s out n) out rem
  end.

(** [step] corresponds to the body of the outer [while] loop in the
  pseudocode. *)

Definition step (s: state) : AMap.t L.t + state :=
  match NS.pick s.(st_wrk) with
  | None =>
      inl _ s.(st_in)
  | Some(n, rem) =>
      inr _ (propagate_succ_list
              (mkstate s.(st_in) rem)
              (transf n s.(st_in)!!n)
              (successors!!!n))
  end.

(** The whole fixpoint computation is the iteration of [step] from
  the start state. *)

Definition fixpoint num_iterations : option (AMap.t L.t) :=
  PrimIter.iter _ _ step num_iterations start_state.

(** ** Monotonicity properties *)

(** We first show that the [st_in] part of the state evolves monotonically:
  at each step, the values of the [st_in[n]] either remain the same or
  increase with respect to the [L.ge] ordering. *)

Definition in_incr (in1 in2: AMap.t L.t) : Prop :=
  forall n, L.ge in2!!n in1!!n.

Lemma in_incr_refl:
  forall in1, in_incr in1 in1.
Proof.
  unfold in_incr; intros. apply L.ge_refl. apply L.eq_refl.
Qed.

Lemma in_incr_trans:
  forall in1 in2 in3, in_incr in1 in2 -> in_incr in2 in3 -> in_incr in1 in3.
Proof.
  unfold in_incr; intros. apply L.ge_trans with in2!!n; auto.
Qed.

Lemma propagate_succ_incr:
  forall st out n,
  in_incr st.(st_in) (propagate_succ st out n).(st_in).
Proof.
  unfold in_incr, propagate_succ; simpl; intros.
  case (L.beq st.(st_in)!!n (L.lub st.(st_in)!!n out)).
  apply L.ge_refl. apply L.eq_refl.
  simpl. case (eq_atom_dec n n0); intro.
  subst n0. rewrite AMap.gss. apply L.ge_lub_left.
  rewrite AMap.gso; auto. apply L.ge_refl. apply L.eq_refl.
Qed.

Lemma propagate_succ_list_incr:
  forall out scs st,
  in_incr st.(st_in) (propagate_succ_list st out scs).(st_in).
Proof.
  induction scs; simpl; intros.
  apply in_incr_refl.
  apply in_incr_trans with (propagate_succ st out a).(st_in).
  apply propagate_succ_incr. auto.
Qed.

Lemma step_incr: forall st st' 
  (Hstep: step st = inr st'),
  in_incr (st_in st) (st_in st').
Proof.
  unfold step.
  intros.
  remember (NS.pick (st_wrk st)) as R.
  destruct R as [ [n rem] | ]; inv Hstep.
  change st.(st_in) with (mkstate st.(st_in) rem).(st_in).
  apply propagate_succ_list_incr; auto.
Qed.

Lemma fixpoint_incr:
  forall res ni,
  fixpoint ni = Some res -> in_incr (start_state_in entrypoints) res.
Proof.
  unfold fixpoint; intros.
  change (start_state_in entrypoints) with start_state.(st_in).
  eapply (PrimIter.iter_prop _ _ step
    (fun st => in_incr start_state.(st_in) st.(st_in))
    (fun res => in_incr start_state.(st_in) res)) in H; eauto.

  intros st INCR. unfold step.
  destruct (NS.pick st.(st_wrk)) as [ [n rem] | ].
  apply in_incr_trans with st.(st_in). auto.
  change st.(st_in) with (mkstate st.(st_in) rem).(st_in).
  apply propagate_succ_list_incr.
  auto.

  eauto. apply in_incr_refl.
Qed.

(** ** Correctness invariant *)

(** The following invariant is preserved at each iteration of Kildall's
  algorithm: for all program points [n], either
  [n] is in the worklist, or the inequations associated with [n]
  ([st_in[s] >= transf n st_in[n]] for all successors [s] of [n])
  hold.  In other terms, the worklist contains all nodes that do not
  yet satisfy their inequations. *)

Definition good_state (st: state) : Prop :=
  forall n,
  NS.In n st.(st_wrk) \/
  (forall s, In s (successors!!!n) ->
             L.ge st.(st_in)!!s (transf n st.(st_in)!!n)).

(** We show that the start state satisfies the invariant, and that
  the [step] function preserves it. *)

Lemma start_state_good:
  good_state start_state.
Proof.
  unfold good_state, start_state; intros.
  case_eq (successors!n); intros.
  left; simpl. eapply NS.initial_spec. eauto.
  unfold XATree.successors_list. rewrite H. right; intros. contradiction.
Qed.

Lemma propagate_succ_spec:
  forall st out n,
  let st' := propagate_succ st out n in
  (L.eq st'.(st_in)!!n (L.lub st.(st_in)!!n out)) /\
  (forall s, n <> s -> st'.(st_in)!!s = st.(st_in)!!s).
Proof.
  unfold propagate_succ; intros; simpl.
  predSpec L.beq L.beq_correct
           ((st_in st) !! n) (L.lub (st_in st) !! n out).
  split; auto.

  simpl. split.
    rewrite AMap.gss. apply L.eq_refl.
    intros. rewrite AMap.gso; auto.
Qed.

Lemma propagate_succ_charact:
  forall st out n,
  let st' := propagate_succ st out n in
  L.ge st'.(st_in)!!n out /\
  (forall s, n <> s -> st'.(st_in)!!s = st.(st_in)!!s).
Proof.
  unfold propagate_succ; intros; simpl.
  predSpec L.beq L.beq_correct
           ((st_in st) !! n) (L.lub (st_in st) !! n out).
  split.
  eapply L.ge_trans. apply L.ge_refl. apply H; auto.
  eapply L.ge_compat. apply L.lub_commut. apply L.eq_refl.
  apply L.ge_lub_left.
  auto.

  simpl. split.
  rewrite AMap.gss.
  eapply L.ge_compat. apply L.lub_commut. apply L.eq_refl.
  apply L.ge_lub_left.
  intros. rewrite AMap.gso; auto.
Qed.

Lemma propagate_succ_list_charact:
  forall out scs st,
  let st' := propagate_succ_list st out scs in
  forall s,
  (In s scs -> L.ge st'.(st_in)!!s out) /\
  (~(In s scs) -> st'.(st_in)!!s = st.(st_in)!!s).
Proof.
  induction scs; simpl; intros.
  tauto.
  generalize (IHscs (propagate_succ st out a) s). intros [A B].
  generalize (propagate_succ_charact st out a). intros [C D].
  split; intros.
  elim H; intro.
  subst s.
  apply L.ge_trans with (propagate_succ st out a).(st_in)!!a.
  apply propagate_succ_list_incr. assumption.
  apply A. auto.
  transitivity (propagate_succ st out a).(st_in)!!s.
  apply B. tauto.
  apply D. tauto.
Qed.

Lemma propagate_succ_incr_worklist:
  forall st out n x,
  NS.In x st.(st_wrk) -> NS.In x (propagate_succ st out n).(st_wrk).
Proof.
  intros. unfold propagate_succ.
  case (L.beq (st_in st) !! n (L.lub (st_in st) !! n out)).
  auto.
  simpl. rewrite NS.add_spec. auto.
Qed.

Lemma propagate_succ_list_incr_worklist:
  forall out scs st x,
  NS.In x st.(st_wrk) -> NS.In x (propagate_succ_list st out scs).(st_wrk).
Proof.
  induction scs; simpl; intros.
  auto.
  apply IHscs. apply propagate_succ_incr_worklist. auto.
Qed.

Lemma propagate_succ_records_changes:
  forall st out n s,
  let st' := propagate_succ st out n in
  NS.In s st'.(st_wrk) \/ st'.(st_in)!!s = st.(st_in)!!s.
Proof.
  simpl. intros. unfold propagate_succ.
  case (L.beq (st_in st) !! n (L.lub (st_in st) !! n out)).
  right; auto.
  case (eq_atom_dec s n); intro.
  subst s. left. simpl. rewrite NS.add_spec. auto.
  right. simpl. apply AMap.gso. auto.
Qed.

Lemma propagate_succ_list_records_changes:
  forall out scs st s,
  let st' := propagate_succ_list st out scs in
  NS.In s st'.(st_wrk) \/ st'.(st_in)!!s = st.(st_in)!!s.
Proof.
  induction scs; simpl; intros.
  right; auto.
  elim (propagate_succ_records_changes st out a s); intro.
  left. apply propagate_succ_list_incr_worklist. auto.
  rewrite <- H. auto.
Qed.

Lemma step_state_good:
  forall st n rem,
  NS.pick st.(st_wrk) = Some(n, rem) ->
  good_state st ->
  good_state (propagate_succ_list (mkstate st.(st_in) rem)
                                  (transf n st.(st_in)!!n)
                                  (successors!!!n)).
Proof.
  unfold good_state. intros st n rem WKL GOOD x.
  generalize (NS.pick_some _ _ _ WKL); intro PICK.
  set (out := transf n st.(st_in)!!n).
  elim (propagate_succ_list_records_changes
          out (successors!!!n) (mkstate st.(st_in) rem) x).
  intro; left; auto.
  simpl; intros EQ. rewrite EQ.
  (* Case 1: x = n *)
  case (eq_atom_dec x n); intro.
  subst x.
  right; intros.
  elim (propagate_succ_list_charact out (successors!!!n)
          (mkstate st.(st_in) rem) s); intros.
  auto.
  (* Case 2: x <> n *)
  elim (GOOD x); intro.
  (* Case 2.1: x was already in worklist, still is *)
  left. apply propagate_succ_list_incr_worklist.
  simpl. rewrite PICK in H. elim H; intro. congruence. auto.
  (* Case 2.2: x was not in worklist *)
  right; intros.
  case (In_dec eq_atom_dec s (successors!!!n)); intro.
  (* Case 2.2.1: s is a successor of n, it may have increased *)
  apply L.ge_trans with st.(st_in)!!s.
  change st.(st_in)!!s with (mkstate st.(st_in) rem).(st_in)!!s.
  apply propagate_succ_list_incr.
  auto.
  (* Case 2.2.2: s is not a successor of n, it did not change *)
  elim (propagate_succ_list_charact out (successors!!!n)
          (mkstate st.(st_in) rem) s); intros.
  rewrite H2. simpl. auto. auto.
Qed.

(** ** Correctness of the solution returned by [iterate]. *)

(** As a consequence of the [good_state] invariant, the result of
  [fixpoint], if defined, is a solution of the dataflow inequations,
  since [st_wrk] is empty when the iteration terminates. *)

Theorem fixpoint_solution:
  forall res ni n s,
  fixpoint ni = Some res ->
  In s (successors!!!n) ->
  L.ge res!!s (transf n res!!n).
Proof.
  assert (forall res ni, fixpoint ni = Some res ->
          forall n s,
          In s successors!!!n ->
          L.ge res!!s (transf n res!!n)).
    unfold fixpoint. intros res ni PI. pattern res.
    eapply (PrimIter.iter_prop _ _ step good_state) in PI; eauto.
      intros st GOOD. unfold step.
      caseEq (NS.pick st.(st_wrk)); auto.
        intros [n rem] PICK. apply step_state_good; auto.

        intros.  
        elim (GOOD n); intro; auto.
        elim (NS.pick_none _ n H); auto.
      eauto. apply start_state_good. 
  eauto.
Qed.

(** As a consequence of the monotonicity property, the result of
  [fixpoint], if defined, is pointwise greater than or equal the
  initial mapping.  Therefore, it satisfies the additional constraints
  stated in [entrypoints]. *)

Lemma start_state_in_entry:
  forall ep n v,
  In (n, v) ep ->
  L.ge (start_state_in ep)!!n v.
Proof.
  induction ep; simpl; intros.
  elim H.
  elim H; intros.
  subst a. rewrite AMap.gss.
  eapply L.ge_compat. apply L.lub_commut. apply L.eq_refl.
  apply L.ge_lub_left.
  destruct a. rewrite AMap.gsspec. case (eq_atom_dec n a); intro.
  subst a. apply L.ge_trans with (start_state_in ep)!!n.
  apply L.ge_lub_left. auto.
  auto.
Qed.

Theorem fixpoint_entry:
  forall res ni n v,
  fixpoint ni = Some res ->
  In (n, v) entrypoints ->
  L.ge res!!n v.
Proof.
  intros.
  apply L.ge_trans with (start_state_in entrypoints)!!n.
    eapply fixpoint_incr. eauto.
    apply start_state_in_entry. auto.
Qed.

(** ** Preservation of a property over solutions *)

Variable P: L.t -> Prop.
Hypothesis P_bot: P L.bot.
Hypothesis P_lub: forall x y, P x -> P y -> P (L.lub x y).
Hypothesis P_transf: forall pc x, P x -> P (transf pc x).
Hypothesis P_entrypoints: forall n v, In (n, v) entrypoints -> P v.

Theorem fixpoint_invariant:
  forall res ni pc,
  fixpoint ni = Some res ->
  P res!!pc.
Proof.
  assert (forall ep,
          (forall n v, In (n, v) ep -> P v) ->
          forall pc, P (start_state_in ep)!!pc).
    induction ep; intros; simpl.
    rewrite AMap.gi. auto.
    simpl in H.
    assert (P (start_state_in ep)!!pc). apply IHep. eauto.
    destruct a as [n v]. rewrite AMap.gsspec. destruct (eq_atom_dec pc n).
    apply P_lub. subst. auto. eapply H. left; reflexivity. auto.
  set (inv := fun st => forall pc, P (st.(st_in)!!pc)).
  assert (forall st v n, inv st -> P v -> inv (propagate_succ st v n)).
    unfold inv, propagate_succ. intros.
    destruct (L.beq (st_in st)!!n (L.lub (st_in st)!!n v)).
    auto. simpl. rewrite AMap.gsspec. destruct (eq_atom_dec pc n).
    apply P_lub. subst n; auto. auto.
    auto.
  assert (forall l0 st v, inv st -> P v -> inv (propagate_succ_list st v l0)).
    induction l0; intros; simpl. auto.
    apply IHl0; auto.
  assert (forall res ni, fixpoint ni = Some res -> forall pc, P res!!pc).
    unfold fixpoint. intros res0 ni0 RES0. pattern res0.
    eapply (PrimIter.iter_prop _ _ step inv); eauto.
      intros. unfold step. 
      destruct (NS.pick (st_wrk a)) as [[n rem] | ].
        apply H1. auto. apply P_transf. apply H2.
        assumption.
      unfold inv, start_state; simpl. auto.
  intros. eauto.
Qed.

(** ** Another invariant for unreachable nodes *)

Definition good_unreach (res: AMap.t L.t) : Prop :=
  forall n,
  ((XATree.make_predecessors successors)!!!n = nil ->
    res!!n = (start_state_in entrypoints)!!n).

(** We show that the start state satisfies the invariant, and that
  the [step] function preserves it. *)

Lemma propagate_succ_good_unreach: forall st n out,
  (XATree.make_predecessors successors)!!!n <> nil ->
  good_unreach st.(st_in) -> good_unreach (propagate_succ st out n).(st_in).
Proof.
  unfold good_unreach.
  intros.
  destruct (@propagate_succ_spec st out n) as [J1 J2].
  destruct (eq_atom_dec n n0); subst.
    contradict H; auto.
    apply H0 in H1. rewrite <- H1. auto.
Qed.

Lemma propagate_succ_list_good_unreach:
  forall scs st out,
  (forall s, In s scs -> (XATree.make_predecessors successors)!!!s <> nil) ->
  good_unreach st.(st_in) ->
  good_unreach (propagate_succ_list st out scs).(st_in).
Proof.
  induction scs; simpl; intros; auto.
    apply IHscs; auto.
      eapply propagate_succ_good_unreach; eauto.
Qed.

Lemma step_unreach_good:
  forall st n rem,
  NS.pick st.(st_wrk) = Some(n, rem) ->
  good_unreach st.(st_in) ->
  good_unreach (propagate_succ_list (mkstate st.(st_in) rem)
                                    (transf n st.(st_in)!!n)
                                    (successors!!!n)).(st_in).
Proof.
  intros st n rem WKL GOOD.
  destruct st. simpl.
  apply propagate_succ_list_good_unreach; auto.
  intros.
  apply XATree.make_predecessors_correct in H. intro J. rewrite J in H. inv H.
Qed.

Theorem fixpoint_good_unreach: forall res ni,
  fixpoint ni = Some res -> good_unreach res.
Proof.
  unfold fixpoint. intros res ni PI. pattern res.
  eapply (PrimIter.iter_prop _ _ step
    (fun st => good_unreach st.(st_in))); eauto.
  intros st GOOD. unfold step.
  caseEq (NS.pick st.(st_wrk)); auto.
  intros [n rem] PICK. apply step_unreach_good; auto.
  intros x J. unfold start_state. simpl. auto.
Qed.

End Kildall.

Section FixpointInvariant2.

Variable successors: ATree.t (list atom).
Variable transf1: atom -> L.t -> L.t.
Variable transf2: atom -> L.t -> L.t.
Variable entrypoints1: list (atom * L.t).
Variable entrypoints2: list (atom * L.t).

Variable P: L.t -> L.t -> Prop.
Hypothesis P_bot: P L.bot L.bot.
Hypothesis P_lub: forall x1 x2 y1 y2,
  P x1 x2 -> P y1 y2 -> P (L.lub x1 y1) (L.lub x2 y2).
Hypothesis P_transf: forall pc x1 x2,
  P x1 x2 -> P (transf1 pc x1) (transf2 pc x2).
Definition P_entrypoints_aux (ep1: list (atom * L.t)) (ep2: list (atom * L.t))
  := Forall2 (fun el1 el2 =>
           match el1, el2 with
           | (n1,v1), (n2,v2) => n1 = n2 /\ P v1 v2
           end) ep1 ep2.
Hypothesis P_entrypoints: P_entrypoints_aux entrypoints1 entrypoints2.
Hypothesis P_beq : forall x1 x2 y1 y2,
  P x1 x2 -> P y1 y2 ->
  L.beq y1 (L.lub y1 x1) =
  L.beq y2 (L.lub y2 x2).

Lemma start_state_in_invariant2 : forall ep1 ep2
  (H:P_entrypoints_aux ep1 ep2) pc,
  P (start_state_in ep1)!!pc (start_state_in ep2)!!pc.
Proof.
  induction ep1; destruct ep2; intros; simpl; inv H.
    repeat rewrite AMap.gi. auto.

    destruct a as [n1 v1]. destruct p as [n2 v2].
    destruct H3 as [Heq H3]; subst.
    assert (P (start_state_in ep1)!!pc
              (start_state_in ep2)!!pc).
      apply IHep1. eauto.
    repeat rewrite AMap.gsspec.
    destruct (eq_atom_dec pc n2); subst; auto.
Qed.

Hint Resolve start_state_in_invariant2.

Definition invariant2 := fun st1 st2 =>
    st1.(st_wrk) = st2.(st_wrk) /\
    forall pc, P (st1.(st_in)!!pc) (st2.(st_in)!!pc).

Lemma propagate_succ_invariant2 : forall st1 st2 v1 v2 n
  (H:invariant2 st1 st2) (H0:P v1 v2),
  invariant2 (propagate_succ st1 v1 n) (propagate_succ st2 v2 n).
Proof.
  unfold invariant2, propagate_succ. intros.
  destruct H as [J1 J2].
  case_eq (L.beq (st_in st1)!!n (L.lub (st_in st1)!!n v1)).
    intros Hbeq.
    erewrite P_beq in Hbeq; eauto. rewrite Hbeq. auto.

    intros Hbeq.
    erewrite P_beq in Hbeq; eauto. rewrite Hbeq.
    simpl. rewrite J1. split; auto.
    intro pc. repeat rewrite AMap.gsspec.
    destruct (eq_atom_dec pc n); subst; auto.
Qed.

Hint Resolve propagate_succ_invariant2.

Lemma propagate_succ_list_invariant2 : forall l0 st1 st2 v1 v2,
  invariant2 st1 st2 -> P v1 v2 ->
  invariant2 (propagate_succ_list st1 v1 l0)
             (propagate_succ_list st2 v2 l0).
Proof.
  induction l0; intros; simpl. auto.
  apply IHl0; auto.
Qed.

Hint Resolve propagate_succ_list_invariant2.

Theorem fixpoint_some2:
  forall res1 res2 ni pc,
  fixpoint successors transf1 entrypoints1 ni = Some res1 ->
  fixpoint successors transf2 entrypoints2 ni = Some res2 ->
  P res1!!pc res2!!pc.
Proof.
  intros res1 res2 ni pc Hinter1 Hinter2.
  revert pc.
  unfold fixpoint. pattern res1, res2.
  eapply (PrimIter.iter_some2 _ _ _ _
    (step successors transf1)
    (step successors transf2) invariant2); eauto.
    intros a1 a2 H2. unfold step.
    destruct H2 as [J1 J2]. rewrite J1.
    destruct (NS.pick (st_wrk a2))
      as [[n rem] | ]; eauto.
      apply propagate_succ_list_invariant2; auto.
        split; auto.
    unfold invariant2, start_state; simpl. auto.
Qed.

Theorem fixpoint_none2_right: forall ni,
  fixpoint successors transf2 entrypoints2 ni = None ->
  fixpoint successors transf1 entrypoints1 ni = None.
Proof.
  unfold fixpoint.
  intros Hinter2.
  eapply (PrimIter.iter_none2_right _ _ _ _
    (step successors transf1)
    (step successors transf2) invariant2); eauto.
    intros a1 a2 H2. unfold step.
    destruct H2 as [J1 J2]. rewrite J1.
    destruct (NS.pick (st_wrk a2))
      as [[n rem] | ]; eauto.
      apply propagate_succ_list_invariant2; auto.
        split; auto.
    unfold invariant2, start_state; simpl. auto.
Qed.

Theorem fixpoint_none2_left: forall ni,
  fixpoint successors transf1 entrypoints1 ni = None ->
  fixpoint successors transf2 entrypoints2 ni = None.
Proof.
  unfold fixpoint.
  intros Hinter1.
  eapply (PrimIter.iter_none2_left _ _ _ _
    (step successors transf1)
    (step successors transf2) invariant2); eauto.
    intros a1 a2 H2. unfold step.
    destruct H2 as [J1 J2]. rewrite J1.
    destruct (NS.pick (st_wrk a2))
      as [[n rem] | ]; eauto.
      apply propagate_succ_list_invariant2; auto.
        split; auto.
    unfold invariant2, start_state; simpl. auto.
Qed.

Theorem fixpoint_some2_right:
  forall res2 ni pc,
  fixpoint successors transf2 entrypoints2 ni = Some res2 ->
  exists res1,
    fixpoint successors transf1 entrypoints1 ni = Some res1 /\
    P res1!!pc res2!!pc.
Proof.
  intros res2 ni pc Hfix2.
  case_eq (fixpoint successors transf1 entrypoints1 ni).
    intros res1 Hfix1.
    exists res1. split; eauto using fixpoint_some2.

    intros Hfix1.
    eapply fixpoint_none2_left in Hfix1; eauto.
    rewrite Hfix1 in Hfix2. congruence.
Qed.

Theorem fixpoint_some2_left:
  forall res1 ni pc,
  fixpoint successors transf1 entrypoints1 ni = Some res1 ->
  exists res2,
    fixpoint successors transf2 entrypoints2 ni = Some res2 /\
    P res1!!pc res2!!pc.
Proof.
  intros res1 ni pc Hfix1.
  case_eq (fixpoint successors transf2 entrypoints2 ni).
    intros res2 Hfix2.
    exists res2. split; eauto using fixpoint_some2.

    intros Hfix2.
    eapply fixpoint_none2_right in Hfix2; eauto.
    rewrite Hfix2 in Hfix1. congruence.
Qed.

End FixpointInvariant2.

End Dataflow_Solver_Var_Top.
