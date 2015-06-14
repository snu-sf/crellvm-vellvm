(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Applicative finite maps are the main data structure used in this
  project.  A finite map associates data to keys.  The two main operations
  are [set k d m], which returns a map identical to [m] except that [d]
  is associated to [k], and [get k m] which returns the data associated
  to key [k] in map [m].  In this library, we distinguish two kinds of maps:
- Trees: the [get] operation returns an option type, either [None]
  if no data is associated to the key, or [Some d] otherwise.
- Maps: the [get] operation always returns a data.  If no data was explicitly
  associated with the key, a default data provided at map initialization time
  is returned.

  In this library, we provide efficient implementations of trees and
  maps whose keys range over the type [positive] of binary positive
  integers or any type that can be injected into [positive].  The
  implementation is based on radix-2 search trees (uncompressed
  Patricia trees) and guarantees logarithmic-time operations.  An
  inefficient implementation of maps as functions is also provided.
*)

Require Import Coqlib.
Require Import Metatheory.

Lemma in_fst_map__in_dom: forall A x (E : list (atom * A))
  (Hin: In x (List.map fst E)), x `in` dom E.
Proof.
  induction E as [|[]]; simpl; intros.
    tauto.
    destruct Hin as [Hin | Hin]; subst; auto.
Qed.

Lemma uniq__list_norepet: forall A (l1:list (atom*A)) (Huniq: uniq l1), 
  list_norepet (List.map fst l1).
Proof.
  induction 1; simpl; intros.
    constructor.
    constructor; auto using in_fst_map__in_dom.
Qed.

(*************************************************)

Module InsertSort. Section InsertSort.

Variable atom:Type.
Variable atom_lt: atom -> atom -> bool.
Hypothesis eq_atom_dec: forall (x y:atom), {x = y} + {x <> y}.
Hypothesis tom_lt_irrefl: forall a0, atom_lt a0 a0 = false.
Hypothesis atom_lt_trans: forall a1 a2 a3, 
  atom_lt a1 a2 = true -> atom_lt a2 a3 = true -> atom_lt a1 a3 = true.
Hypothesis atom_lt_gt: forall a1 a2, 
  atom_lt a1 a2 = false -> a1 <> a2 -> atom_lt a2 a1 = true.

Fixpoint insert_sort_aux (l0:atom)(prefix suffix:list atom) 
  : list atom :=
match suffix with
| nil => List.rev (l0 :: prefix)
| l1::suffix' =>
    if atom_lt l0 l1 then (List.rev (l0 :: prefix) ++ suffix)
    else if eq_atom_dec l0 l1 then (List.rev prefix) ++ suffix
    else insert_sort_aux l0 (l1::prefix) suffix'
end.

Definition insert_sort (l0:atom)(ls2:list atom) : list atom :=
insert_sort_aux l0 nil ls2.

Lemma insert_sort_aux_safe: forall l0 suffix l1 prefix,
  (In l0 (prefix ++ suffix) \/ l0 = l1) <->
  In l0 (insert_sort_aux l1 prefix suffix).
Proof.
  induction suffix; simpl; intros.
  (*1*)
    split; intro J.
      apply in_or_app.
      destruct J as [J | J]; subst.
        left. simpl_env in J. apply in_rev in J; auto.
        right. simpl. auto.

      apply in_app_or in J. simpl in J. simpl_env.
      destruct J as [J | [J | J]]; subst; auto.
        left. apply in_rev in J; auto.
        tauto.
  (*2*)
    simpl_env. simpl.
    split; intro J.
    (*2.1*)
      destruct (atom_lt l1 a).
      (*2.1.1*)
        destruct J as [J | J]; subst.
          apply in_app_or in J. simpl in J.
          apply in_or_app. simpl.
          destruct J as [J | [J | J]]; subst; auto.
            apply in_rev in J; auto.

          apply in_or_app. simpl. auto.

      (*2.1.2*)
        destruct (eq_atom_dec l1 a); subst.
        (*2.1.2.1*)
          destruct J as [J | J]; subst.
            apply in_or_app. 
            apply in_app_or in J. simpl in J. 
            destruct J as [J | [J | J]]; subst; simpl; auto.
              left. apply in_rev in J; auto.
  
            apply in_or_app. simpl. auto.

        (*2.1.2.2*)
          apply IHsuffix.
            destruct J as [J | J]; auto.
            left. simpl.
            apply in_app_or in J. simpl in J.
            destruct J as [J | [J | J]]; subst; auto.
              right. apply in_or_app; auto.
              right. apply in_or_app; auto.

    (*2.2*)
      destruct (atom_lt l1 a).
      (*2.2.1*)
        apply in_app_or in J. simpl in J.
        destruct J as [J | [J | [J | J]]]; subst; auto.
          left. apply in_or_app. simpl.
          apply in_rev in J; auto.

          left. apply in_or_app. simpl. auto.
          left. apply in_or_app. simpl. auto.
      (*2.2.2*)
      destruct (eq_atom_dec l1 a); subst.
        (*2.2.2.1*)
          left. 
          apply in_or_app. simpl. 
          apply in_app_or in J. simpl in J. 
          destruct J as [J | [J | J]]; subst; simpl; auto.
            apply in_rev in J; auto.
        (*2.2.2.2*)
        apply IHsuffix in J.
          destruct J as [J | J]; auto.
          left. apply in_or_app. simpl.
          apply in_app_or in J. simpl in J.
          destruct J as [[J | J] | J]; subst; auto.
Qed.

Lemma insert_sort_safe: forall l0 l1 ls2,
  (In l0 ls2 \/ l0 = l1) <-> In l0 (insert_sort l1 ls2).
Proof.
  intros.
  unfold insert_sort.  
  assert (J:=insert_sort_aux_safe l0 ls2 l1 nil).
  simpl in J. auto.
Qed.

Definition atom_lt_prop (a1 a2:atom) : Prop := atom_lt a1 a2 = true.

Lemma insert_sort_aux_sorted: forall l0 suffix prefix,
  Sorted atom_lt_prop (List.rev prefix ++ suffix) ->
  (forall l1 prefix', prefix = l1 :: prefix' -> atom_lt_prop l1 l0) ->
  Sorted atom_lt_prop (insert_sort_aux l0 prefix suffix).
Proof.
  induction suffix; simpl; intros.
  Case "1".
    simpl_env in *.
    apply sorted_append; auto.
      intros.
      apply H0 with (prefix':=rev l1'); auto.
        rewrite <- rev_involutive at 1.
        rewrite H1. rewrite rev_unit. auto.
  Case "2".
    remember (atom_lt l0 a) as R.
    destruct R.
    SCase "2.1".
      simpl_env. simpl.
      apply sorted_insert; auto.
        intros.
        apply H0 with (prefix':=rev l1'); auto.
          rewrite <- rev_involutive at 1.
          rewrite H1. rewrite rev_unit. auto.

        intros.
        inv H1.
        unfold atom_lt_prop. auto.

    SCase "2.2".
      destruct (eq_atom_dec l0 a); subst; auto.
      apply IHsuffix.
        simpl. simpl_env. simpl. auto.

        intros. inv H1.
        apply atom_lt_gt; auto.
Qed.

Lemma insert_sort_sorted: forall l0 ls1,
  Sorted atom_lt_prop ls1 ->
  Sorted atom_lt_prop (insert_sort l0 ls1).
Proof.
  unfold insert_sort.
  intros.
  apply insert_sort_aux_sorted; auto.
    congruence.
Qed.

Lemma insert_sort_strongly_sorted: forall l0 ls1
  (Hsort: StronglySorted atom_lt_prop ls1),
  StronglySorted atom_lt_prop (insert_sort l0 ls1).
Proof.
  intros.
  apply StronglySorted_Sorted in Hsort.
  apply insert_sort_sorted with (l0:=l0) in Hsort.
  apply Sorted_StronglySorted; auto.
Qed.

End InsertSort. End InsertSort.

(*************************************************)

Set Implicit Arguments.

(** * The abstract signatures of trees *)

Module Type TREE.
  Variable elt: Set.
  Variable elt_eq: forall (a b: elt), {a = b} + {a <> b}.
  Variable t: Type -> Type.
  Variable empty: forall (A: Type), t A.
  Variable get: forall (A: Type), elt -> t A -> option A.
  Variable set: forall (A: Type), elt -> A -> t A -> t A.
  Variable remove: forall (A: Type), elt -> t A -> t A.

  (** The ``good variables'' properties for trees, expressing
    commutations between [get], [set] and [remove]. *)
  Hypothesis gempty:
    forall (A: Type) (i: elt), get i (empty A) = None.
  Hypothesis gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = Some x.
  Hypothesis gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Hypothesis gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then Some x else get i m.
  (* We could implement the following, but it's not needed for the moment.
    Hypothesis grident:
      forall (A: Type) (i: elt) (m: t A) (v: A),
      get i m = None -> remove i m = m.
  *)
  Hypothesis grs:
    forall (A: Type) (i: elt) (m: t A), get i (remove i m) = None.
  Hypothesis gro:
    forall (A: Type) (i j: elt) (m: t A),
    i <> j -> get i (remove j m) = get i m.
  Hypothesis grspec:
    forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.

  (** Applying a function to all data of a tree. *)
  Variable map:
    forall (A B: Type), (elt -> A -> B) -> t A -> t B.
  Hypothesis gmap:
    forall (A B: Type) (f: elt -> A -> B) (i: elt) (m: t A),
    get i (map f m) = option_map (f i) (get i m).

  (** Enumerating the bindings of a tree. *)
  Variable elements:
    forall (A: Type), t A -> list (elt * A).
  Hypothesis elements_correct:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    get i m = Some v -> In (i, v) (elements m).
  Hypothesis elements_complete:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    In (i, v) (elements m) -> get i m = Some v.
  Hypothesis elements_keys_norepet:
    forall (A: Type) (m: t A),
    list_norepet (List.map (@fst elt A) (elements m)).

  (** Folding a function over all bindings of a tree. *)
  Variable fold:
    forall (A B: Type), (B -> elt -> A -> B) -> t A -> B -> B.
  Hypothesis fold_spec:
    forall (A B: Type) (f: B -> elt -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
End TREE.

Module Type TREE'.
  Include Type TREE.
  Variable eq: forall (A: Type), (forall (x y: A), {x=y} + {x<>y}) ->
                forall (a b: t A), {a = b} + {a <> b}.
  Hypothesis gsident:
    forall (A: Type) (i: elt) (m: t A) (v: A),
    get i m = Some v -> set i v m = m.

  (** Extensional equality between trees. *)
  Variable beq: forall (A: Type), (A -> A -> bool) -> t A -> t A -> bool.
  Hypothesis beq_correct:
    forall (A: Type) (P: A -> A -> Prop) (cmp: A -> A -> bool),
    (forall (x y: A), cmp x y = true -> P x y) ->
    forall (t1 t2: t A), beq cmp t1 t2 = true ->
    forall (x: elt),
    match get x t1, get x t2 with
    | None, None => True
    | Some y1, Some y2 => P y1 y2
    | _, _ => False
    end.

  (** Applying a function pairwise to all data of two trees. *)
  Variable combine:
    forall (A: Type), (option A -> option A -> option A) -> t A -> t A -> t A.
  Hypothesis gcombine:
    forall (A: Type) (f: option A -> option A -> option A),
    f None None = None ->
    forall (m1 m2: t A) (i: elt),
    get i (combine f m1 m2) = f (get i m1) (get i m2).
End TREE'.

Module Type SORTED_TREE.
  Include Type TREE'.
  Hypothesis combine_commut:
    forall (A: Type) (f g: option A -> option A -> option A),
    (forall (i j: option A), f i j = g j i) ->
    forall (m1 m2: t A),
    combine f m1 m2 = combine g m2 m1.
  Hypothesis elements_canonical_order:
    forall (A B: Type) (R: A -> B -> Prop) (m: t A) (n: t B),
    (forall i x, get i m = Some x -> exists y, get i n = Some y /\ R x y) ->
    (forall i y, get i n = Some y -> exists x, get i m = Some x /\ R x y) ->
    list_forall2
      (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
      (elements m) (elements n).
  Hypothesis elements_extensional:
    forall (A: Type) (m n: t A),
    (forall i, get i m = get i n) ->
    elements m = elements n.
End SORTED_TREE.

(** * The abstract signatures of maps *)

Module Type MAP.
  Variable elt: Type.
  Variable elt_eq: forall (a b: elt), {a = b} + {a <> b}.
  Variable t: Type -> Type.
  Variable init: forall (A: Type), A -> t A.
  Variable get: forall (A: Type), elt -> t A -> A.
  Variable set: forall (A: Type), elt -> A -> t A -> t A.
  Hypothesis gi:
    forall (A: Type) (i: elt) (x: A), get i (init x) = x.
  Hypothesis gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = x.
  Hypothesis gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Hypothesis gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then x else get i m.
  Hypothesis gsident:
    forall (A: Type) (i j: elt) (m: t A), get j (set i (get i m) m) = get j m.
  Variable map: forall (A B: Type), (A -> B) -> t A -> t B.
  Hypothesis gmap:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map f m) = f(get i m).
End MAP.

(** * An implementation of trees over type [positive] *)

Module PTree <: SORTED_TREE.
  Definition elt := positive.
  Definition elt_eq := peq.

  Inductive tree (A : Type) : Type :=
    | Leaf : tree A
    | Node : tree A -> option A -> tree A -> tree A
  .
  Implicit Arguments Leaf [A].
  Implicit Arguments Node [A].

  Definition t := tree.

  Theorem eq : forall (A : Type),
    (forall (x y: A), {x=y} + {x<>y}) ->
    forall (a b : t A), {a = b} + {a <> b}.
  Proof.
    intros A eqA.
    decide equality.
    generalize o o0; decide equality.
  Qed.

  Definition empty (A : Type) := (Leaf : t A).

  Fixpoint get (A : Type) (i : positive) (m : t A) {struct i} : option A :=
    match m with
    | Leaf => None
    | Node l o r =>
        match i with
        | xH => o
        | xO ii => get ii l
        | xI ii => get ii r
        end
    end.

  Fixpoint set (A : Type) (i : positive) (v : A) (m : t A) {struct i} : t A :=
    match m with
    | Leaf =>
        match i with
        | xH => Node Leaf (Some v) Leaf
        | xO ii => Node (set ii v Leaf) None Leaf
        | xI ii => Node Leaf None (set ii v Leaf)
        end
    | Node l o r =>
        match i with
        | xH => Node l (Some v) r
        | xO ii => Node (set ii v l) o r
        | xI ii => Node l o (set ii v r)
        end
    end.

  Fixpoint remove (A : Type) (i : positive) (m : t A) {struct i} : t A :=
    match i with
    | xH =>
        match m with
        | Leaf => Leaf
        | Node Leaf o Leaf => Leaf
        | Node l o r => Node l None r
        end
    | xO ii =>
        match m with
        | Leaf => Leaf
        | Node l None Leaf =>
            match remove ii l with
            | Leaf => Leaf
            | mm => Node mm None Leaf
            end
        | Node l o r => Node (remove ii l) o r
        end
    | xI ii =>
        match m with
        | Leaf => Leaf
        | Node Leaf None r =>
            match remove ii r with
            | Leaf => Leaf
            | mm => Node Leaf None mm
            end
        | Node l o r => Node l o (remove ii r)
        end
    end.

  Theorem gempty:
    forall (A: Type) (i: positive), get i (empty A) = None.
  Proof.
    induction i; simpl; auto.
  Qed.

  Theorem gss:
    forall (A: Type) (i: positive) (x: A) (m: t A), get i (set i x m) = Some x.
  Proof.
    induction i; destruct m; simpl; auto.
  Qed.

    Lemma gleaf : forall (A : Type) (i : positive), get i (Leaf : t A) = None.
    Proof. exact gempty. Qed.

  Theorem gso:
    forall (A: Type) (i j: positive) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    induction i; intros; destruct j; destruct m; simpl;
       try rewrite <- (gleaf A i); auto; try apply IHi; congruence.
  Qed.

  Theorem gsspec:
    forall (A: Type) (i j: positive) (x: A) (m: t A),
    get i (set j x m) = if peq i j then Some x else get i m.
  Proof.
    intros.
    destruct (peq i j); [ rewrite e; apply gss | apply gso; auto ].
  Qed.

  Theorem gsident:
    forall (A: Type) (i: positive) (m: t A) (v: A),
    get i m = Some v -> set i v m = m.
  Proof.
    induction i; intros; destruct m; simpl; simpl in H; try congruence.
     rewrite (IHi m2 v H); congruence.
     rewrite (IHi m1 v H); congruence.
  Qed.

    Lemma rleaf : forall (A : Type) (i : positive), remove i (Leaf : t A) = Leaf.
    Proof. destruct i; simpl; auto. Qed.

  Theorem grs:
    forall (A: Type) (i: positive) (m: t A), get i (remove i m) = None.
  Proof.
    induction i; destruct m.
     simpl; auto.
     destruct m1; destruct o; destruct m2 as [ | ll oo rr]; simpl; auto.
      rewrite (rleaf A i); auto.
      cut (get i (remove i (Node ll oo rr)) = None).
        destruct (remove i (Node ll oo rr)); auto; apply IHi.
        apply IHi.
     simpl; auto.
     destruct m1 as [ | ll oo rr]; destruct o; destruct m2; simpl; auto.
      rewrite (rleaf A i); auto.
      cut (get i (remove i (Node ll oo rr)) = None).
        destruct (remove i (Node ll oo rr)); auto; apply IHi.
        apply IHi.
     simpl; auto.
     destruct m1; destruct m2; simpl; auto.
  Qed.

  Theorem gro:
    forall (A: Type) (i j: positive) (m: t A),
    i <> j -> get i (remove j m) = get i m.
  Proof.
    induction i; intros; destruct j; destruct m;
        try rewrite (rleaf A (xI j));
        try rewrite (rleaf A (xO j));
        try rewrite (rleaf A 1); auto;
        destruct m1; destruct o; destruct m2;
        simpl;
        try apply IHi; try congruence;
        try rewrite (rleaf A j); auto;
        try rewrite (gleaf A i); auto.
     cut (get i (remove j (Node m2_1 o m2_2)) = get i (Node m2_1 o m2_2));
        [ destruct (remove j (Node m2_1 o m2_2)); try rewrite (gleaf A i); auto
        | apply IHi; congruence ].
     destruct (remove j (Node m1_1 o0 m1_2)); simpl; try rewrite (gleaf A i);
        auto.
     destruct (remove j (Node m2_1 o m2_2)); simpl; try rewrite (gleaf A i);
        auto.
     cut (get i (remove j (Node m1_1 o0 m1_2)) = get i (Node m1_1 o0 m1_2));
        [ destruct (remove j (Node m1_1 o0 m1_2)); try rewrite (gleaf A i); auto
        | apply IHi; congruence ].
     destruct (remove j (Node m2_1 o m2_2)); simpl; try rewrite (gleaf A i);
        auto.
     destruct (remove j (Node m1_1 o0 m1_2)); simpl; try rewrite (gleaf A i);
        auto.
  Qed.

  Theorem grspec:
    forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.
  Proof.
    intros. destruct (elt_eq i j). subst j. apply grs. apply gro; auto.
  Qed.

  Section EXTENSIONAL_EQUALITY.

    Variable A: Type.
    Variable eqA: A -> A -> Prop.
    Variable beqA: A -> A -> bool.
    Hypothesis beqA_correct: forall x y, beqA x y = true -> eqA x y.

    Definition exteq (m1 m2: t A) : Prop :=
      forall (x: elt),
      match get x m1, get x m2 with
      | None, None => True
      | Some y1, Some y2 => eqA y1 y2
      | _, _ => False
      end.

    Fixpoint bempty (m: t A) : bool :=
      match m with
      | Leaf => true
      | Node l None r => bempty l && bempty r
      | Node l (Some _) r => false
      end.

    Lemma bempty_correct:
      forall m, bempty m = true -> forall x, get x m = None.
    Proof.
      induction m; simpl; intros.
      change (@Leaf A) with (empty A). apply gempty.
      destruct o. congruence. destruct (andb_prop _ _ H).
      destruct x; simpl; auto.
    Qed.

    Fixpoint beq (m1 m2: t A) {struct m1} : bool :=
      match m1, m2 with
      | Leaf, _ => bempty m2
      | _, Leaf => bempty m1
      | Node l1 o1 r1, Node l2 o2 r2 =>
          match o1, o2 with
          | None, None => true
          | Some y1, Some y2 => beqA y1 y2
          | _, _ => false
          end
          && beq l1 l2 && beq r1 r2
      end.

    Lemma beq_correct:
      forall m1 m2, beq m1 m2 = true -> exteq m1 m2.
    Proof.
      induction m1; destruct m2; simpl.
      intros; red; intros. change (@Leaf A) with (empty A).
      repeat rewrite gempty. auto.
      destruct o; intro. congruence.
      red; intros. change (@Leaf A) with (empty A). rewrite gempty.
      rewrite bempty_correct. auto. assumption.
      destruct o; intro. congruence.
      red; intros. change (@Leaf A) with (empty A). rewrite gempty.
      rewrite bempty_correct. auto. assumption.
      destruct o; destruct o0; simpl; intro; try congruence.
      destruct (andb_prop _ _ H). destruct (andb_prop _ _ H0).
      red; intros. destruct x; simpl.
      apply IHm1_2; auto. apply IHm1_1; auto.
      apply beqA_correct; auto.
      destruct (andb_prop _ _ H).
      red; intros. destruct x; simpl.
      apply IHm1_2; auto. apply IHm1_1; auto.
      auto.
    Qed.

  End EXTENSIONAL_EQUALITY.

    Fixpoint append (i j : positive) {struct i} : positive :=
      match i with
      | xH => j
      | xI ii => xI (append ii j)
      | xO ii => xO (append ii j)
      end.

    Lemma append_assoc_0 : forall (i j : positive),
                           append i (xO j) = append (append i (xO xH)) j.
    Proof.
      induction i; intros; destruct j; simpl;
      try rewrite (IHi (xI j));
      try rewrite (IHi (xO j));
      try rewrite <- (IHi xH);
      auto.
    Qed.

    Lemma append_assoc_1 : forall (i j : positive),
                           append i (xI j) = append (append i (xI xH)) j.
    Proof.
      induction i; intros; destruct j; simpl;
      try rewrite (IHi (xI j));
      try rewrite (IHi (xO j));
      try rewrite <- (IHi xH);
      auto.
    Qed.

    Lemma append_neutral_r : forall (i : positive), append i xH = i.
    Proof.
      induction i; simpl; congruence.
    Qed.

    Lemma append_neutral_l : forall (i : positive), append xH i = i.
    Proof.
      simpl; auto.
    Qed.

    Fixpoint xmap (A B : Type) (f : positive -> A -> B) (m : t A) (i : positive)
             {struct m} : t B :=
      match m with
      | Leaf => Leaf
      | Node l o r => Node (xmap f l (append i (xO xH)))
                           (option_map (f i) o)
                           (xmap f r (append i (xI xH)))
      end.

  Definition map (A B : Type) (f : positive -> A -> B) m := xmap f m xH.

    Lemma xgmap:
      forall (A B: Type) (f: positive -> A -> B) (i j : positive) (m: t A),
      get i (xmap f m j) = option_map (f (append j i)) (get i m).
    Proof.
      induction i; intros; destruct m; simpl; auto.
      rewrite (append_assoc_1 j i); apply IHi.
      rewrite (append_assoc_0 j i); apply IHi.
      rewrite (append_neutral_r j); auto.
    Qed.

  Theorem gmap:
    forall (A B: Type) (f: positive -> A -> B) (i: positive) (m: t A),
    get i (map f m) = option_map (f i) (get i m).
  Proof.
    intros.
    unfold map.
    replace (f i) with (f (append xH i)).
    apply xgmap.
    rewrite append_neutral_l; auto.
  Qed.

  Definition Node' (A: Type) (l: t A) (x: option A) (r: t A): t A :=
    match l, x, r with
    | Leaf, None, Leaf => Leaf
    | _, _, _ => Node l x r
    end.

  Lemma gnode':
    forall (A: Type) (l r: t A) (x: option A) (i: positive),
    get i (Node' l x r) = get i (Node l x r).
  Proof.
    intros. unfold Node'.
    destruct l; destruct x; destruct r; auto.
    destruct i; simpl; auto; rewrite gleaf; auto.
  Qed.

  Section COMBINE.

  Variable A: Type.
  Variable f: option A -> option A -> option A.
  Hypothesis f_none_none: f None None = None.

  Fixpoint xcombine_l (m : t A) {struct m} : t A :=
      match m with
      | Leaf => Leaf
      | Node l o r => Node' (xcombine_l l) (f o None) (xcombine_l r)
      end.

  Lemma xgcombine_l :
          forall (m: t A) (i : positive),
          get i (xcombine_l m) = f (get i m) None.
    Proof.
      induction m; intros; simpl.
      repeat rewrite gleaf. auto.
      rewrite gnode'. destruct i; simpl; auto.
    Qed.

  Fixpoint xcombine_r (m : t A) {struct m} : t A :=
      match m with
      | Leaf => Leaf
      | Node l o r => Node' (xcombine_r l) (f None o) (xcombine_r r)
      end.

  Lemma xgcombine_r :
          forall (m: t A) (i : positive),
          get i (xcombine_r m) = f None (get i m).
    Proof.
      induction m; intros; simpl.
      repeat rewrite gleaf. auto.
      rewrite gnode'. destruct i; simpl; auto.
    Qed.

  Fixpoint combine (m1 m2 : t A) {struct m1} : t A :=
    match m1 with
    | Leaf => xcombine_r m2
    | Node l1 o1 r1 =>
        match m2 with
        | Leaf => xcombine_l m1
        | Node l2 o2 r2 => Node' (combine l1 l2) (f o1 o2) (combine r1 r2)
        end
    end.

  Theorem gcombine:
      forall (m1 m2: t A) (i: positive),
      get i (combine m1 m2) = f (get i m1) (get i m2).
  Proof.
    induction m1; intros; simpl.
    rewrite gleaf. apply xgcombine_r.
    destruct m2; simpl.
    rewrite gleaf. rewrite <- xgcombine_l. auto.
    repeat rewrite gnode'. destruct i; simpl; auto.
  Qed.

  End COMBINE.

  Lemma xcombine_lr :
    forall (A : Type) (f g : option A -> option A -> option A) (m : t A),
    (forall (i j : option A), f i j = g j i) ->
    xcombine_l f m = xcombine_r g m.
    Proof.
      induction m; intros; simpl; auto.
      rewrite IHm1; auto.
      rewrite IHm2; auto.
      rewrite H; auto.
    Qed.

  Theorem combine_commut:
    forall (A: Type) (f g: option A -> option A -> option A),
    (forall (i j: option A), f i j = g j i) ->
    forall (m1 m2: t A),
    combine f m1 m2 = combine g m2 m1.
  Proof.
    intros A f g EQ1.
    assert (EQ2: forall (i j: option A), g i j = f j i).
      intros; auto.
    induction m1; intros; destruct m2; simpl;
      try rewrite EQ1;
      repeat rewrite (xcombine_lr f g);
      repeat rewrite (xcombine_lr g f);
      auto.
     rewrite IHm1_1.
     rewrite IHm1_2.
     auto.
  Qed.

    Fixpoint xelements (A : Type) (m : t A) (i : positive) {struct m}
             : list (positive * A) :=
      match m with
      | Leaf => nil
      | Node l None r =>
          (xelements l (append i (xO xH))) ++ (xelements r (append i (xI xH)))
      | Node l (Some x) r =>
          (xelements l (append i (xO xH)))
          ++ ((i, x) :: xelements r (append i (xI xH)))
      end.

  (* Note: function [xelements] above is inefficient.  We should apply
     deforestation to it, but that makes the proofs even harder. *)

  Definition elements A (m : t A) := xelements m xH.

    Lemma xelements_correct:
      forall (A: Type) (m: t A) (i j : positive) (v: A),
      get i m = Some v -> In (append j i, v) (xelements m j).
    Proof.
      induction m; intros.
       rewrite (gleaf A i) in H; congruence.
       destruct o; destruct i; simpl; simpl in H.
        rewrite append_assoc_1; apply in_or_app; right; apply in_cons;
          apply IHm2; auto.
        rewrite append_assoc_0; apply in_or_app; left; apply IHm1; auto.
        rewrite append_neutral_r; apply in_or_app; injection H;
          intro EQ; rewrite EQ; right; apply in_eq.
        rewrite append_assoc_1; apply in_or_app; right; apply IHm2; auto.
        rewrite append_assoc_0; apply in_or_app; left; apply IHm1; auto.
        congruence.
    Qed.

  Theorem elements_correct:
    forall (A: Type) (m: t A) (i: positive) (v: A),
    get i m = Some v -> In (i, v) (elements m).
  Proof.
    intros A m i v H.
    exact (xelements_correct m i xH H).
  Qed.

    Fixpoint xget (A : Type) (i j : positive) (m : t A) {struct j} : option A :=
      match i, j with
      | _, xH => get i m
      | xO ii, xO jj => xget ii jj m
      | xI ii, xI jj => xget ii jj m
      | _, _ => None
      end.

    Lemma xget_left :
      forall (A : Type) (j i : positive) (m1 m2 : t A) (o : option A) (v : A),
      xget i (append j (xO xH)) m1 = Some v -> xget i j (Node m1 o m2) = Some v.
    Proof.
      induction j; intros; destruct i; simpl; simpl in H; auto; try congruence.
      destruct i; congruence.
    Qed.

    Lemma xelements_ii :
      forall (A: Type) (m: t A) (i j : positive) (v: A),
      In (xI i, v) (xelements m (xI j)) -> In (i, v) (xelements m j).
    Proof.
      induction m.
       simpl; auto.
       intros; destruct o; simpl; simpl in H; destruct (in_app_or _ _ _ H);
         apply in_or_app.
        left; apply IHm1; auto.
        right; destruct (in_inv H0).
         injection H1; intros EQ1 EQ2; rewrite EQ1; rewrite EQ2; apply in_eq.
         apply in_cons; apply IHm2; auto.
        left; apply IHm1; auto.
        right; apply IHm2; auto.
    Qed.

    Lemma xelements_io :
      forall (A: Type) (m: t A) (i j : positive) (v: A),
      ~In (xI i, v) (xelements m (xO j)).
    Proof.
      induction m.
       simpl; auto.
       intros; destruct o; simpl; intro H; destruct (in_app_or _ _ _ H).
        apply (IHm1 _ _ _ H0).
        destruct (in_inv H0).
         congruence.
         apply (IHm2 _ _ _ H1).
        apply (IHm1 _ _ _ H0).
        apply (IHm2 _ _ _ H0).
    Qed.

    Lemma xelements_oo :
      forall (A: Type) (m: t A) (i j : positive) (v: A),
      In (xO i, v) (xelements m (xO j)) -> In (i, v) (xelements m j).
    Proof.
      induction m.
       simpl; auto.
       intros; destruct o; simpl; simpl in H; destruct (in_app_or _ _ _ H);
         apply in_or_app.
        left; apply IHm1; auto.
        right; destruct (in_inv H0).
         injection H1; intros EQ1 EQ2; rewrite EQ1; rewrite EQ2; apply in_eq.
         apply in_cons; apply IHm2; auto.
        left; apply IHm1; auto.
        right; apply IHm2; auto.
    Qed.

    Lemma xelements_oi :
      forall (A: Type) (m: t A) (i j : positive) (v: A),
      ~In (xO i, v) (xelements m (xI j)).
    Proof.
      induction m.
       simpl; auto.
       intros; destruct o; simpl; intro H; destruct (in_app_or _ _ _ H).
        apply (IHm1 _ _ _ H0).
        destruct (in_inv H0).
         congruence.
         apply (IHm2 _ _ _ H1).
        apply (IHm1 _ _ _ H0).
        apply (IHm2 _ _ _ H0).
    Qed.

    Lemma xelements_ih :
      forall (A: Type) (m1 m2: t A) (o: option A) (i : positive) (v: A),
      In (xI i, v) (xelements (Node m1 o m2) xH) -> In (i, v) (xelements m2 xH).
    Proof.
      destruct o; simpl; intros; destruct (in_app_or _ _ _ H).
        absurd (In (xI i, v) (xelements m1 2)); auto; apply xelements_io; auto.
        destruct (in_inv H0).
         congruence.
         apply xelements_ii; auto.
        absurd (In (xI i, v) (xelements m1 2)); auto; apply xelements_io; auto.
        apply xelements_ii; auto.
    Qed.

    Lemma xelements_oh :
      forall (A: Type) (m1 m2: t A) (o: option A) (i : positive) (v: A),
      In (xO i, v) (xelements (Node m1 o m2) xH) -> In (i, v) (xelements m1 xH).
    Proof.
      destruct o; simpl; intros; destruct (in_app_or _ _ _ H).
        apply xelements_oo; auto.
        destruct (in_inv H0).
         congruence.
         absurd (In (xO i, v) (xelements m2 3)); auto; apply xelements_oi; auto.
        apply xelements_oo; auto.
        absurd (In (xO i, v) (xelements m2 3)); auto; apply xelements_oi; auto.
    Qed.

    Lemma xelements_hi :
      forall (A: Type) (m: t A) (i : positive) (v: A),
      ~In (xH, v) (xelements m (xI i)).
    Proof.
      induction m; intros.
       simpl; auto.
       destruct o; simpl; intro H; destruct (in_app_or _ _ _ H).
        generalize H0; apply IHm1; auto.
        destruct (in_inv H0).
         congruence.
         generalize H1; apply IHm2; auto.
        generalize H0; apply IHm1; auto.
        generalize H0; apply IHm2; auto.
    Qed.

    Lemma xelements_ho :
      forall (A: Type) (m: t A) (i : positive) (v: A),
      ~In (xH, v) (xelements m (xO i)).
    Proof.
      induction m; intros.
       simpl; auto.
       destruct o; simpl; intro H; destruct (in_app_or _ _ _ H).
        generalize H0; apply IHm1; auto.
        destruct (in_inv H0).
         congruence.
         generalize H1; apply IHm2; auto.
        generalize H0; apply IHm1; auto.
        generalize H0; apply IHm2; auto.
    Qed.

    Lemma get_xget_h :
      forall (A: Type) (m: t A) (i: positive), get i m = xget i xH m.
    Proof.
      destruct i; simpl; auto.
    Qed.

    Lemma xelements_complete:
      forall (A: Type) (i j : positive) (m: t A) (v: A),
      In (i, v) (xelements m j) -> xget i j m = Some v.
    Proof.
      induction i; simpl; intros; destruct j; simpl.
       apply IHi; apply xelements_ii; auto.
       absurd (In (xI i, v) (xelements m (xO j))); auto; apply xelements_io.
       destruct m.
        simpl in H; tauto.
        rewrite get_xget_h. apply IHi. apply (xelements_ih _ _ _ _ _ H).
       absurd (In (xO i, v) (xelements m (xI j))); auto; apply xelements_oi.
       apply IHi; apply xelements_oo; auto.
       destruct m.
        simpl in H; tauto.
        rewrite get_xget_h. apply IHi. apply (xelements_oh _ _ _ _ _ H).
       absurd (In (xH, v) (xelements m (xI j))); auto; apply xelements_hi.
       absurd (In (xH, v) (xelements m (xO j))); auto; apply xelements_ho.
       destruct m.
        simpl in H; tauto.
        destruct o; simpl in H; destruct (in_app_or _ _ _ H).
         absurd (In (xH, v) (xelements m1 (xO xH))); auto; apply xelements_ho.
         destruct (in_inv H0).
          congruence.
          absurd (In (xH, v) (xelements m2 (xI xH))); auto; apply xelements_hi.
         absurd (In (xH, v) (xelements m1 (xO xH))); auto; apply xelements_ho.
         absurd (In (xH, v) (xelements m2 (xI xH))); auto; apply xelements_hi.
    Qed.

  Theorem elements_complete:
    forall (A: Type) (m: t A) (i: positive) (v: A),
    In (i, v) (elements m) -> get i m = Some v.
  Proof.
    intros A m i v H.
    unfold elements in H.
    rewrite get_xget_h.
    exact (xelements_complete i xH m v H).
  Qed.

  Lemma in_xelements:
    forall (A: Type) (m: t A) (i k: positive) (v: A),
    In (k, v) (xelements m i) ->
    exists j, k = append i j.
  Proof.
    induction m; simpl; intros.
    tauto.
    assert (k = i \/ In (k, v) (xelements m1 (append i 2))
                  \/ In (k, v) (xelements m2 (append i 3))).
      destruct o.
      elim (in_app_or _ _ _ H); simpl; intuition.
      replace k with i. tauto. congruence.
      elim (in_app_or _ _ _ H); simpl; intuition.
    elim H0; intro.
    exists xH. rewrite append_neutral_r. auto.
    elim H1; intro.
    elim (IHm1 _ _ _ H2). intros k1 EQ. rewrite EQ.
    rewrite <- append_assoc_0. exists (xO k1); auto.
    elim (IHm2 _ _ _ H2). intros k1 EQ. rewrite EQ.
    rewrite <- append_assoc_1. exists (xI k1); auto.
  Qed.

  Definition xkeys (A: Type) (m: t A) (i: positive) :=
    List.map (@fst positive A) (xelements m i).

  Lemma in_xkeys:
    forall (A: Type) (m: t A) (i k: positive),
    In k (xkeys m i) ->
    exists j, k = append i j.
  Proof.
    unfold xkeys; intros.
    elim (list_in_map_inv _ _ _ H). intros [k1 v1] [EQ IN].
    simpl in EQ; subst k1. apply in_xelements with A m v1. auto.
  Qed.

  Remark list_append_cons_norepet:
    forall (A: Type) (l1 l2: list A) (x: A),
    list_norepet l1 -> list_norepet l2 -> list_disjoint l1 l2 ->
    ~In x l1 -> ~In x l2 ->
    list_norepet (l1 ++ x :: l2).
  Proof.
    intros. apply list_norepet_append_commut. simpl; constructor.
    red; intros. elim (in_app_or _ _ _ H4); intro; tauto.
    apply list_norepet_append; auto.
    apply list_disjoint_sym; auto.
  Qed.

  Lemma append_injective:
    forall i j1 j2, append i j1 = append i j2 -> j1 = j2.
  Proof.
    induction i; simpl; intros.
    apply IHi. congruence.
    apply IHi. congruence.
    auto.
  Qed.

  Lemma xelements_keys_norepet:
    forall (A: Type) (m: t A) (i: positive),
    list_norepet (xkeys m i).
  Proof.
    induction m; unfold xkeys; simpl; fold xkeys; intros.
    constructor.
    assert (list_disjoint (xkeys m1 (append i 2)) (xkeys m2 (append i 3))).
      red; intros; red; intro. subst y.
      elim (in_xkeys _ _ _ H); intros j1 EQ1.
      elim (in_xkeys _ _ _ H0); intros j2 EQ2.
      rewrite EQ1 in EQ2.
      rewrite <- append_assoc_0 in EQ2.
      rewrite <- append_assoc_1 in EQ2.
      generalize (append_injective _ _ _ EQ2). congruence.
    assert (forall (m: t A) j,
            j = 2%positive \/ j = 3%positive ->
            ~In i (xkeys m (append i j))).
      intros; red; intros.
      elim (in_xkeys _ _ _ H1); intros k EQ.
      assert (EQ1: append i xH = append (append i j) k).
        rewrite append_neutral_r. auto.
      elim H0; intro; subst j;
      try (rewrite <- append_assoc_0 in EQ1);
      try (rewrite <- append_assoc_1 in EQ1);
      generalize (append_injective _ _ _ EQ1); congruence.
    destruct o; rewrite list_append_map; simpl;
    change (List.map (@fst positive A) (xelements m1 (append i 2)))
      with (xkeys m1 (append i 2));
    change (List.map (@fst positive A) (xelements m2 (append i 3)))
      with (xkeys m2 (append i 3)).
    apply list_append_cons_norepet; auto.
    apply list_norepet_append; auto.
  Qed.

  Theorem elements_keys_norepet:
    forall (A: Type) (m: t A),
    list_norepet (List.map (@fst elt A) (elements m)).
  Proof.
    intros. change (list_norepet (xkeys m 1)). apply xelements_keys_norepet.
  Qed.

  Theorem elements_canonical_order:
    forall (A B: Type) (R: A -> B -> Prop) (m: t A) (n: t B),
    (forall i x, get i m = Some x -> exists y, get i n = Some y /\ R x y) ->
    (forall i y, get i n = Some y -> exists x, get i m = Some x /\ R x y) ->
    list_forall2
      (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
      (elements m) (elements n).
  Proof.
    intros until R.
    assert (forall m n j,
    (forall i x, get i m = Some x -> exists y, get i n = Some y /\ R x y) ->
    (forall i y, get i n = Some y -> exists x, get i m = Some x /\ R x y) ->
    list_forall2
      (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
      (xelements m j) (xelements n j)).
    induction m; induction n; intros; simpl.
    constructor.
    destruct o. exploit (H0 xH). simpl. reflexivity. simpl. intros [x [P Q]]. congruence.
    change (@nil (positive*A)) with ((@nil (positive * A))++nil).
    apply list_forall2_app.
    apply IHn1.
    intros. rewrite gleaf in H1. congruence.
    intros. exploit (H0 (xO i)). simpl; eauto. rewrite gleaf. intros [x [P Q]]. congruence.
    apply IHn2.
    intros. rewrite gleaf in H1. congruence.
    intros. exploit (H0 (xI i)). simpl; eauto. rewrite gleaf. intros [x [P Q]]. congruence.
    destruct o. exploit (H xH). simpl. reflexivity. simpl. intros [x [P Q]]. congruence.
    change (@nil (positive*B)) with (xelements (@Leaf B) (append j 2) ++ (xelements (@Leaf B) (append j 3))).
    apply list_forall2_app.
    apply IHm1.
    intros. exploit (H (xO i)). simpl; eauto. rewrite gleaf. intros [y [P Q]]. congruence.
    intros. rewrite gleaf in H1. congruence.
    apply IHm2.
    intros. exploit (H (xI i)). simpl; eauto. rewrite gleaf. intros [y [P Q]]. congruence.
    intros. rewrite gleaf in H1. congruence.
    exploit (IHm1 n1 (append j 2)).
    intros. exploit (H (xO i)). simpl; eauto. simpl. auto.
    intros. exploit (H0 (xO i)). simpl; eauto. simpl; auto.
    intro REC1.
    exploit (IHm2 n2 (append j 3)).
    intros. exploit (H (xI i)). simpl; eauto. simpl. auto.
    intros. exploit (H0 (xI i)). simpl; eauto. simpl; auto.
    intro REC2.
    destruct o; destruct o0.
    apply list_forall2_app; auto. constructor; auto.
    simpl; split; auto. exploit (H xH). simpl; eauto. simpl. intros [y [P Q]]. congruence.
    exploit (H xH). simpl; eauto. simpl. intros [y [P Q]]; congruence.
    exploit (H0 xH). simpl; eauto. simpl. intros [x [P Q]]; congruence.
    apply list_forall2_app; auto.

    unfold elements; auto.
  Qed.

  Theorem elements_extensional:
    forall (A: Type) (m n: t A),
    (forall i, get i m = get i n) ->
    elements m = elements n.
  Proof.
    intros.
    exploit (elements_canonical_order (fun (x y: A) => x = y) m n).
    intros. rewrite H in H0. exists x; auto.
    intros. rewrite <- H in H0. exists y; auto.
    induction 1. auto. destruct a1 as [a2 a3]; destruct b1 as [b2 b3]; simpl in *.
    destruct H0. congruence.
  Qed.

(*
  Definition fold (A B : Type) (f: B -> positive -> A -> B) (tr: t A) (v: B) :=
     List.fold_left (fun a p => f a (fst p) (snd p)) (elements tr) v.
*)

  Fixpoint xfold (A B: Type) (f: B -> positive -> A -> B)
                 (i: positive) (m: t A) (v: B) {struct m} : B :=
    match m with
    | Leaf => v
    | Node l None r =>
        let v1 := xfold f (append i (xO xH)) l v in
        xfold f (append i (xI xH)) r v1
    | Node l (Some x) r =>
        let v1 := xfold f (append i (xO xH)) l v in
        let v2 := f v1 i x in
        xfold f (append i (xI xH)) r v2
    end.

  Definition fold (A B : Type) (f: B -> positive -> A -> B) (m: t A) (v: B) :=
    xfold f xH m v.

  Lemma xfold_xelements:
    forall (A B: Type) (f: B -> positive -> A -> B) m i v,
    xfold f i m v =
    List.fold_left (fun a p => f a (fst p) (snd p))
                   (xelements m i)
                   v.
  Proof.
    induction m; intros.
    simpl. auto.
    simpl. destruct o.
    rewrite fold_left_app. simpl.
    rewrite IHm1. apply IHm2.
    rewrite fold_left_app. simpl.
    rewrite IHm1. apply IHm2.
  Qed.

  Theorem fold_spec:
    forall (A B: Type) (f: B -> positive -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
  Proof.
    intros. unfold fold, elements. apply xfold_xelements.
  Qed.

End PTree.

(** * An implementation of trees over type [atom] using list *)

Require Import alist.

Module ATree' <: TREE'.
  Definition elt := atom.
  Definition elt_eq := eq_atom_dec.

  Definition tree (A : Type) : Type := list (atom*A).

  Definition t := tree.

  Theorem eq: forall (A: Type), (forall (x y: A), {x=y} + {x<>y}) ->
                forall (a b: t A), {a = b} + {a <> b}.
  Proof.
    intros A eqA.
    decide equality.
    destruct a0, p. decide equality.
  Qed.

  Definition empty (A: Type) : t A := nil.

  Definition get (A: Type) (i: atom) (m: t A) : option A :=
    lookupAL _ m i.

  Definition set (A: Type) (i: atom) (v: A) (m: t A) : t A :=
    updateAddAL _ m i v.

  Definition remove (A: Type) (i: atom) (m: t A) : t A :=
    deleteAL _ m i.

  (** The ``good variables'' properties for trees, expressing
    commutations between [get], [set] and [remove]. *)
  Theorem gempty:
    forall (A: Type) (i: elt), get i (empty A) = None.
  Proof. auto. Qed.

  Theorem gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = Some x.
  Proof. intros. apply lookupAL_updateAddAL_eq; auto. Qed.

  Theorem gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros. unfold get, set.
    rewrite <- lookupAL_updateAddAL_neq; auto.
  Qed.

  Theorem gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then Some x else get i m.
  Proof.
    intros.
    destruct (elt_eq i j); [ rewrite e; apply gss | apply gso; auto ].
  Qed.

  Theorem gsident:
    forall (A: Type) (i: elt) (m: t A) (v: A),
    get i m = Some v -> set i v m = m.
  Proof. intros. apply lookupAL_updateAddAL_ident; auto. Qed.

  Theorem grs:
    forall (A: Type) (i: elt) (m: t A), get i (remove i m) = None.
  Proof. intros. apply lookupAL_deleteAL_eq; auto. Qed.

  Theorem gro:
    forall (A: Type) (i j: elt) (m: t A),
    i <> j -> get i (remove j m) = get i m.
  Proof. intros. apply lookupAL_deleteAL_neq; auto. Qed.

  Theorem grspec:
    forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.
  Proof.
    intros. destruct (elt_eq i j). subst j. apply grs. apply gro; auto.
  Qed.

  (** Extensional equality between trees. *)
  Fixpoint beq (A: Type) (cmp: A -> A -> bool) (m1 m2: t A): bool :=
  match m1, m2 with
  | nil, nil => true
  | (id1,gv1)::m1', (id2,gv2)::m2' =>
      if (elt_eq id1 id2) then cmp gv1 gv2 && beq cmp m1' m2' else false
  | _, _ => false
  end.

  Theorem beq_correct:
    forall (A: Type) (P: A -> A -> Prop) (cmp: A -> A -> bool),
    (forall (x y: A), cmp x y = true -> P x y) ->
    forall (t1 t2: t A), beq cmp t1 t2 = true ->
    forall (x: elt),
    match get x t1, get x t2 with
    | None, None => True
    | Some y1, Some y2 => P y1 y2
    | _, _ => False
    end.
  Proof.
    induction t1; destruct t2; simpl; intros; auto.
      congruence.
      destruct a. congruence.
      destruct a, p.
      destruct (elt_eq a a1); subst.
        apply andb_true_iff in H0. destruct H0 as [J1 J2].
        destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) x a1);
          subst; auto.
          apply IHt1; auto.
        congruence.
  Qed.

  (** Applying a function to all data of a tree. *)
  Fixpoint map (A B: Type) (f: elt -> A -> B) (m: t A) : t B :=
  match m with
  | nil => nil
  | (id0, gv0) :: m' => (id0, (f id0 gv0)) :: map f m'
  end.

  Theorem gmap:
    forall (A B: Type) (f: elt -> A -> B) (i: elt) (m: t A),
    get i (map f m) = option_map (f i) (get i m).
  Proof.
    induction m; simpl; intros; auto.
     destruct a. simpl.
     destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) i a); subst;
       auto.
  Qed.

  (** Enumerating the bindings of a tree. *)
  Fixpoint elements_aux (A: Type) (m acc: t A) : list (elt * A) := 
  match m with
  | nil => acc
  | (k,v)::m' => 
       let acc' := 
         match lookupAL _ acc k with
         | None => [(k,v)] ++ acc
         | _ => acc
         end in
       elements_aux m' acc'
  end.

  Lemma elements_aux_uniq:
    forall (A: Type) (m: t A) acc (Huniq: uniq acc), 
    uniq (elements_aux m acc).
  Proof.
    induction m as [|[k1 v1]]; simpl; intros; auto.
      apply IHm.
        case_eq (lookupAL A acc k1); auto.
          intros Hgeta. 
          simpl_env.
          constructor; eauto using lookupAL_None_notindom.
  Qed.        

  Lemma in_acc__in_elements_aux:
    forall (A: Type) (i: elt) (v: A) (m: t A) acc (Huniq: uniq acc)
    (Hget: get i acc = Some v), 
    In (i, v) (elements_aux m acc).
  Proof.
    induction m as [|[k1 v1]]; simpl; intros.
      auto using lookupAL_in.

      apply IHm.
        case_eq (lookupAL A acc k1); auto.
          intros Hgeta. 
          simpl_env.
          constructor; eauto using lookupAL_None_notindom.

        case_eq (lookupAL A acc k1); auto.
          intros Hgeta. 
          simpl. 
          destruct_if; auto.
            apply lookupAL_Some_indom in Hget.
            apply lookupAL_None_notindom in Hgeta.
            tauto.
  Qed.        

  Lemma elements_aux_correct:
    forall (A: Type) (i: elt) (v: A) (m: t A) acc (Huniq: uniq acc)
    (Hget: get i m = Some v), 
    In (i, v) (elements_aux m acc) \/ i `in` dom acc.
  Proof.
    induction m as [|[k1 v1]]; simpl; intros.
      congruence.

      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) i k1); subst.
      Case "1".
        inv Hget.
        case_eq (lookupAL A acc k1).
        SCase "1.1".
          intros a Hgeta.
          right. 
          apply lookupAL_Some_indom in Hgeta; auto.
        SCase "1.2".
          intros Hgeta. 
          left.
          apply in_acc__in_elements_aux; auto.
          SSCase "1.2.1".
            simpl_env. 
            constructor; eauto using lookupAL_None_notindom.
          SSCase "1.2.2".
            simpl. destruct_if. congruence.
      Case "2".
        case_eq (lookupAL A acc k1).
        SCase "2.1".
          intros a Hgeta.
          apply IHm; auto.
        SCase "2.2".
          intros Hgeta.
          apply IHm with (acc:=(k1, v1) :: acc) in Hget; auto. 
          SSCase "2.2.1".
            destruct Hget as [Hget | Hget]; auto.
              right. simpl in Hget. fsetdec.
          SSCase "2.2.2".
            simpl_env. 
            constructor; eauto using lookupAL_None_notindom.
  Qed.        

  Definition elements (A: Type) (m: t A) : list (elt * A) := 
    elements_aux m nil.

  Theorem elements_correct:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    get i m = Some v -> In (i, v) (elements m).
  Proof.
    intros.
    unfold elements.
    apply elements_aux_correct with (m:=m)(acc:=nil) in H; auto.
    destruct H as [H | H]; auto.
       fsetdec.
  Qed.

  Lemma elements_aux_complete:
    forall (A: Type) (m: t A) (i: elt) (v: A) acc (Huniq: uniq acc)
    (Hin: In (i, v) (elements_aux m acc)),
    get i m = Some v \/ i `in` dom acc.
  Proof.
    induction m as [|[k1 v1]]; simpl; intros.
    Case "base".
      right. 
      apply In_lookupAL in Hin; auto.
      apply lookupAL_Some_indom in Hin; auto.
    Case "ind".
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) i k1); subst.
      SCase "1.1".
        case_eq (lookupAL A acc k1).
        SSCase "1.1.1".
          intros a Hgeta.
          rewrite Hgeta in Hin. 
          right. 
          eapply lookupAL_Some_indom; eauto.
        SSCase "1.1.2".
          intros Hgeta.         
          rewrite Hgeta in Hin. 
          assert (Hget: get k1 ((k1,v1)::acc) = Some v1).
            simpl. 
            destruct_if. 
              congruence.
          assert (uniq ((k1, v1) :: acc)) as Huniq'.
            simpl_env. 
            constructor; eauto using lookupAL_None_notindom.
          apply in_acc__in_elements_aux with (m:=m) in Hget; auto.
          apply In_lookupAL in Hin; auto using elements_aux_uniq.
          apply In_lookupAL in Hget; auto using elements_aux_uniq.
          rewrite Hin in Hget. auto.
      SCase "1.2".
        case_eq (lookupAL A acc k1).
        SSCase "1.1.1".
          intros a Hgeta.
          rewrite Hgeta in Hin. auto.
        SSCase "1.1.2".
          intros Hgeta.         
          rewrite Hgeta in Hin. 
          apply IHm in Hin.
          SSSCase "1.1.2.1".
            destruct Hin as [Hin | Hin]; auto.
              right. simpl in Hin. fsetdec.
          SSSCase "1.1.2.2".
            simpl_env. 
            constructor; eauto using lookupAL_None_notindom.
  Qed.

  Lemma elements_complete:
    forall (A: Type) (m: t A) (i: elt) (v: A)
    (Hin: In (i, v) (elements m)), get i m = Some v.
  Proof.
    unfold elements.
    intros.
    apply elements_aux_complete in Hin; auto.
    destruct Hin as [Hin | Hin]; auto.
       fsetdec.
  Qed.

  Lemma elements_uniq:
    forall (A: Type) (m: t A), uniq (elements m).
  Proof.
    intros.
    unfold elements.
    apply elements_aux_uniq; auto.
  Qed.

  Lemma elements_keys_norepet:
    forall (A: Type) (m: t A),
    list_norepet (List.map (@fst elt A) (elements m)).
  Proof.
    intros.
    apply uniq__list_norepet.
    apply elements_uniq; auto.
  Qed.

  Lemma get__eq__get_elements: forall (A:Type) (i:atom) (m:t A),
    get i m = get i (elements m).
  Proof.
    intros.
    case_eq (get i m).
      intros a Hget.
      apply elements_correct in Hget.
      apply In_lookupAL in Hget; auto using elements_uniq.

      intros Hget.
      case_eq (get i (elements m)); auto.
      intros b Hget'.
      apply lookupAL_in in Hget'.
      apply elements_complete in Hget'.
      congruence.
  Qed.

(* FIXME: We need a non-duplicated AL to implement elements. 
  Hypothesis elements_canonical_order:
    forall (A B: Type) (R: A -> B -> Prop) (m: t A) (n: t B),
    (forall i x, get i m = Some x -> exists y, get i n = Some y /\ R x y) ->
    (forall i y, get i n = Some y -> exists x, get i m = Some x /\ R x y) ->
    list_forall2
      (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
      (elements m) (elements n).
  Hypothesis elements_extensional:
    forall (A: Type) (m n: t A),
    (forall i, get i m = get i n) ->
    elements m = elements n.
*)

  Section Combine.

  Variable (A:Type) (f:option A -> option A -> option A).

  Fixpoint combiner (m1 m2: t A)
    :t A :=
  match m2 with
  | nil => nil
  | (k, v2)::m2' => 
      let acc := combiner m1 m2' in
      match get k m1 with
      | None => 
          match f None (Some v2) with
          | Some r => (k, r)::acc
          | _ => acc
          end
      | Some _ => acc
      end
  end.

  Fixpoint combinel (m1 m2 init: t A) :t A :=
  match m1 with
  | nil => init
  | (k, v1)::m1' => 
      let acc := combinel m1' m2 init in
      match f (Some v1) (get k m2) with
      | Some r => (k, r)::acc
      | _ => acc
      end
  end.

  Definition combine (m1 m2: t A) :t A :=
  let m1' := elements m1 in
  let m2' := elements m2 in
  combinel m1' m2' (combiner m1' m2').

  Lemma notin_m2__notin_combiner: forall k m1 m2 (Hnotin : k `notin` dom m2),
    get k (combiner m1 m2) = None.
  Proof.
    induction m2 as [|[k2 v2]]; simpl; intros; auto.
      destruct (get k2 m1); auto.
      destruct (f None (Some v2)); auto.
        simpl. 
        destruct_if.
          fsetdec.
  Qed.

  Lemma notin_m1__notin_combinel: forall k m2 init m1 
    (Hnotin : k `notin` dom m1),
    get k (combinel m1 m2 init) = get k init.
  Proof.
    induction m1 as [|[k1 v1]]; simpl; intros; auto.
      destruct (f (Some v1) (get k1 m2)); auto.
        simpl. 
        destruct_if.
          fsetdec.
  Qed.

  Hypothesis (Hnone: f None None = None).

  Lemma gcombiner:
    forall (i: elt) (m1 m2: t A) (Huniq: uniq m2),
    (forall (Hget: get i m1 = None), 
       get i (combiner m1 m2) = f None (get i m2)) /\
    (forall (Hget: get i m1 <> None), get i (combiner m1 m2) = None).
  Proof.
    induction m2 as [|[k v2]]; simpl; intros; auto.
      inv Huniq.
      split; intros.   
      Case "1".
        destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) i k); subst.
        SCase "1.1".
          rewrite Hget.
          destruct (f None (Some v2)).
            simpl. destruct_if. congruence.
            apply notin_m2__notin_combiner; auto.
        SCase "1.2".
          case_eq (get k m1).
          SSCase "1.2.1".
            intros a Hgeta. 
            apply IHm2; auto.
          SSCase "1.2.2".
            intros Hgeta. 
            destruct (f None (Some v2)).
            SSSCase "1.2.2.1".
              simpl. 
              destruct_if. 
                congruence.
                apply IHm2; auto.
            SSSCase "1.2.2.2".
              apply IHm2; auto.
      Case "2".
          case_eq (get k m1).
          SSCase "1.2.1".
            intros a Hgeta. 
            apply IHm2; auto.
          SSCase "1.2.2".
            intros Hgeta. 
            destruct (f None (Some v2)).
            SSSCase "1.2.2.1".
              simpl. 
              destruct_if. 
                congruence.
                apply IHm2; auto.
            SSSCase "1.2.2.2".
              apply IHm2; auto.
  Qed.

  Lemma gcombinel:
    forall init (i: elt) (m2 m1: t A) (Huniq: uniq m1)
    (Hinit: forall i, get i m1 <> None -> get i init = None),
    (forall (Hget: get i m1 = None), get i (combinel m1 m2 init) = get i init) /\
    (forall (Hget: get i m1 <> None), 
       get i (combinel m1 m2 init) = f (get i m1) (get i m2)).
  Proof.
    induction m1 as [|[k v1]]; simpl; intros.
      split; auto.
        congruence.

      inv Huniq.
      assert (forall i0 : atom, get i0 m1 <> None -> get i0 init = None) 
        as Hinit'.
        intros. apply Hinit. destruct_if. congruence.
      split; intros.   
      Case "1".
        destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) i k); subst;
          try congruence.
        destruct (f (Some v1) (get k m2)).
        SCase "1.1".
          simpl. 
          destruct_if. 
            congruence.
            apply IHm1; auto.
        SCase "1.2.2.2".
          apply IHm1; auto.
      Case "2".
        destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) i k); subst.
        SCase "2.1".
          destruct (f (Some v1) (get k m2)).
          SSCase "2.1.1".
            simpl. 
            destruct_if. 
              congruence.
          SSCase "2.1.2".
            transitivity (get k init).
              apply notin_m1__notin_combinel; auto.
              apply Hinit.
              destruct_if. 
        SCase "2.2".
          destruct (f (Some v1) (get k m2)).
          SSCase "2.1.1".
            simpl. 
            destruct_if. 
              congruence.
              apply IHm1; auto.
          SSCase "2.1.2".
            apply IHm1; auto.
  Qed.

  Lemma gcombine:
    forall (m1 m2: t A) (i: elt),
    get i (combine m1 m2) = f (get i m1) (get i m2).
  Proof.
    unfold combine.
    intros.
    assert (get i m1 = get i (elements m1)) as EQ1.
      apply get__eq__get_elements.
    assert (get i m2 = get i (elements m2)) as EQ2.
      apply get__eq__get_elements.
    rewrite EQ1. rewrite EQ2.
    assert (forall i0 : atom,
            get i0 (elements m1) <> None ->
            get i0 (combiner (elements m1) (elements m2)) = None) as J.
      intros. apply gcombiner; auto using elements_uniq.
    case_eq (get i (elements m1)).
      intros a Hget. rewrite <- Hget.
      apply gcombinel; try solve [auto using elements_uniq | congruence].

      intros Hget.
      transitivity (get i (combiner (elements m1) (elements m2))).
        apply gcombinel; auto using elements_uniq.
        apply gcombiner; auto using elements_uniq.
  Qed.

(* 
  FIXME: We need a sorted AL to prove this.
  Hypothesis combine_commut:
    forall (A: Type) (f g: option A -> option A -> option A),
    (forall (i j: option A), f i j = g j i) ->
    forall (m1 m2: t A),
    combine f m1 m2 = combine g m2 m1.
*)

  End Combine.

  (** Folding a function over all bindings of a tree. *)
  Fixpoint xfold (A B: Type) (f: B -> elt -> A -> B) (m: t A) (v: B) : B :=
  match m with
  | nil => v
  | (id0, gv0)::m' => xfold f m' (f v id0 gv0)
  end.

  Definition fold (A B: Type) (f: B -> elt -> A -> B) (m: t A) (v: B) : B :=
  xfold f (elements m) v.

  Theorem fold_spec:
    forall (A B: Type) (f: B -> elt -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
  Proof.
    unfold fold.
    intros. generalize dependent v.
    generalize (elements m) as m'.
    induction m' as [|[k v]]; simpl; intros; auto.
  Qed.

  Global Opaque empty.

End ATree'.

(** * An implementation of trees over type [atom] using AVL *)

Module AtomOT <: OrderedType with Definition t := atom.

  Definition t := atom.

  Definition eq := @eq t.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.

  Definition eq_dec := eq_atom_dec.

  Parameter lt : t -> t -> Prop.
  
  Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.

  Parameter compare : forall x y : t, Compare lt eq x y.

End AtomOT.

Require Import FMapAVL.
Require Import FMapFacts.
Module AtomFMapAVL := FMapAVL.Make (AtomOT).
Module AVLFacts := WFacts_fun (AtomOT) (AtomFMapAVL).

Module ATree <: TREE.

  Definition elt := atom.
  Definition elt_eq := AtomOT.eq_dec .

  Definition tree (A : Type) : Type := AtomFMapAVL.t A.

  Definition t := tree.

  Definition empty (A: Type) : t A := AtomFMapAVL.empty A.

  Definition get (A: Type) (i: atom) (m: t A) : option A :=
    AtomFMapAVL.find i m.

  Definition set (A: Type) (i: atom) (v: A) (m: t A) : t A :=
    AtomFMapAVL.add i v m.

  Definition remove (A: Type) (i: atom) (m: t A) : t A :=
    AtomFMapAVL.remove i m.

  (** The ``good variables'' properties for trees, expressing
    commutations between [get], [set] and [remove]. *)
  Theorem gempty:
    forall (A: Type) (i: elt), get i (empty A) = None.
  Proof. auto. Qed.

  Theorem gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = Some x.
  Proof. intros. apply AVLFacts.add_eq_o; auto. Qed.

  Theorem gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof. intros. apply AVLFacts.add_neq_o; auto. Qed.

  Theorem gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then Some x else get i m.
  Proof.
    intros. rewrite AVLFacts.add_o; auto.
    unfold elt_eq. 
    destruct (AtomOT.eq_dec i j); subst; auto. 
      destruct (AtomOT.eq_dec j j); subst; congruence.
      destruct (AtomOT.eq_dec j i); subst; auto. congruence.
  Qed.

  Theorem grs:
    forall (A: Type) (i: elt) (m: t A), get i (remove i m) = None.
  Proof. intros. apply AVLFacts.remove_eq_o; auto. Qed.

  Theorem gro:
    forall (A: Type) (i j: elt) (m: t A),
    i <> j -> get i (remove j m) = get i m.
  Proof. intros. apply AVLFacts.remove_neq_o; auto. Qed.

  Theorem grspec:
    forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.
  Proof.
    intros. rewrite AVLFacts.remove_o; auto.
    unfold elt_eq. 
    destruct (AtomOT.eq_dec i j); subst; auto. 
      destruct (AtomOT.eq_dec j j); subst; congruence.
      destruct (AtomOT.eq_dec j i); subst; auto. congruence.
  Qed.

  (** Applying a function to all data of a tree. *)
  Definition map (A B: Type) (f: elt -> A -> B) (m: t A) : t B :=
    AtomFMapAVL.mapi f m.

  Theorem gmap:
    forall (A B: Type) (f: elt -> A -> B) (i: elt) (m: t A),
    get i (map f m) = option_map (f i) (get i m).
  Proof.
    intros.
    apply AVLFacts.mapi_o; congruence.
  Qed.

  (** Enumerating the bindings of a tree. *)
  Definition elements (A: Type) (m: t A) : list (elt * A) := 
    AtomFMapAVL.elements m.

  Theorem elements_correct:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    get i m = Some v -> In (i, v) (elements m).
  Proof.
    intros.
    apply AVLFacts.find_mapsto_iff in H.
    apply AVLFacts.elements_mapsto_iff in H.
    apply InA_alt in H.
    destruct H as [[i' v'] [[EQ1 EQ2] Hin]]; simpl in *; subst. auto.
  Qed.

  Lemma elements_complete:
    forall (A: Type) (m: t A) (i: elt) (v: A)
    (Hin: In (i, v) (elements m)), get i m = Some v.
  Proof.
    intros.
    apply AVLFacts.find_mapsto_iff.
    apply AVLFacts.elements_mapsto_iff.
    apply InA_alt.
    exists (i, v). 
    repeat split; auto.
  Qed.

  Lemma NoDupA_keys_norepet:
    forall (A: Type) (m: list (elt * A)) 
    (Huniq: NoDupA (@AtomFMapAVL.eq_key A) m),
    list_norepet (List.map (@fst elt A) m).
  Proof.
    induction 1; simpl.
      constructor.

      constructor; auto.
        intro Hin. apply H. apply InA_alt.
        apply list_in_map_inv in Hin.
        destruct Hin as [[i0 v0] [EQ Hin]].
        destruct x as [i v].
        simpl in EQ; inv EQ.
        exists (i0, v0).
        repeat split; auto.
  Qed.

  Lemma elements_keys_norepet:
    forall (A: Type) (m: t A),
    list_norepet (List.map (@fst elt A) (elements m)).
  Proof.
    intros.
    apply NoDupA_keys_norepet.
      apply AtomFMapAVL.elements_3w.
  Qed.

  Definition fold (A B: Type) (f: B -> elt -> A -> B) (m: t A) (v: B) : B :=
    AtomFMapAVL.fold (fun key v acc => f acc key v) m v.

  Theorem fold_spec:
    forall (A B: Type) (f: B -> elt -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
  Proof.
    intros. apply AtomFMapAVL.fold_1; auto.
  Qed.

  Global Opaque empty.

End ATree.

(** * An implementation of maps over type [positive] *)

Module PMap <: MAP.
  Definition elt := positive.
  Definition elt_eq := peq.

  Definition t (A : Type) : Type := (A * PTree.t A)%type.

  Definition eq: forall (A: Type), (forall (x y: A), {x=y} + {x<>y}) ->
                 forall (a b: t A), {a = b} + {a <> b}.
  Proof.
    intros A H.
    generalize (PTree.eq H). intros.
    decide equality.
  Qed.

  Definition init (A : Type) (x : A) :=
    (x, PTree.empty A).

  Definition get (A : Type) (i : positive) (m : t A) :=
    match PTree.get i (snd m) with
    | Some x => x
    | None => fst m
    end.

  Definition set (A : Type) (i : positive) (x : A) (m : t A) :=
    (fst m, PTree.set i x (snd m)).

  Theorem gi:
    forall (A: Type) (i: positive) (x: A), get i (init x) = x.
  Proof.
    intros. unfold init. unfold get. simpl. rewrite PTree.gempty. auto.
  Qed.

  Theorem gss:
    forall (A: Type) (i: positive) (x: A) (m: t A), get i (set i x m) = x.
  Proof.
    intros. unfold get. unfold set. simpl. rewrite PTree.gss. auto.
  Qed.

  Theorem gso:
    forall (A: Type) (i j: positive) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros. unfold get. unfold set. simpl. rewrite PTree.gso; auto.
  Qed.

  Theorem gsspec:
    forall (A: Type) (i j: positive) (x: A) (m: t A),
    get i (set j x m) = if peq i j then x else get i m.
  Proof.
    intros. destruct (peq i j).
     rewrite e. apply gss. auto.
     apply gso. auto.
  Qed.

  Theorem gsident:
    forall (A: Type) (i j: positive) (m: t A),
    get j (set i (get i m) m) = get j m.
  Proof.
    intros. destruct (peq i j).
     rewrite e. rewrite gss. auto.
     rewrite gso; auto.
  Qed.

  Definition map (A B : Type) (f : A -> B) (m : t A) : t B :=
    (f (fst m), PTree.map (fun _ => f) (snd m)).

  Theorem gmap:
    forall (A B: Type) (f: A -> B) (i: positive) (m: t A),
    get i (map f m) = f(get i m).
  Proof.
    intros. unfold map. unfold get. simpl. rewrite PTree.gmap.
    unfold option_map. destruct (PTree.get i (snd m)); auto.
  Qed.

End PMap.

(** * An implementation of maps over type [atom] using list *)

Module AMap' <: MAP.
  Definition elt := atom.
  Definition elt_eq := eq_atom_dec.

  Definition t (A : Type) : Type := (A * ATree'.t A)%type.

  Definition eq: forall (A: Type), (forall (x y: A), {x=y} + {x<>y}) ->
                 forall (a b: t A), {a = b} + {a <> b}.
  Proof.
    intros A H.
    generalize (ATree'.eq H). intros.
    decide equality.
  Qed.

  Definition init (A : Type) (x : A) :=
    (x, ATree'.empty A).

  Definition get (A : Type) (i : atom) (m : t A) :=
    match ATree'.get i (snd m) with
    | Some x => x
    | None => fst m
    end.

  Definition set (A : Type) (i : atom) (x : A) (m : t A) :=
    (fst m, ATree'.set i x (snd m)).

  Theorem gi:
    forall (A: Type) (i: atom) (x: A), get i (init x) = x.
  Proof.
    intros. unfold init. unfold get. simpl. rewrite ATree'.gempty. auto.
  Qed.

  Theorem gss:
    forall (A: Type) (i: atom) (x: A) (m: t A), get i (set i x m) = x.
  Proof.
    intros. unfold get. unfold set. simpl. rewrite ATree'.gss. auto.
  Qed.

  Theorem gso:
    forall (A: Type) (i j:atom) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros. unfold get. unfold set. simpl. rewrite ATree'.gso; auto.
  Qed.

  Theorem gsspec:
    forall (A: Type) (i j: atom) (x: A) (m: t A),
    get i (set j x m) = if eq_atom_dec i j then x else get i m.
  Proof.
    intros. destruct (eq_atom_dec i j).
     rewrite e. apply gss. auto.
     apply gso. auto.
  Qed.

  Theorem gsident:
    forall (A: Type) (i j: atom) (m: t A),
    get j (set i (get i m) m) = get j m.
  Proof.
    intros. destruct (eq_atom_dec i j).
     rewrite e. rewrite gss. auto.
     rewrite gso; auto.
  Qed.

  Definition map (A B : Type) (f : A -> B) (m : t A) : t B :=
    (f (fst m), ATree'.map (fun _ => f) (snd m)).

  Theorem gmap:
    forall (A B: Type) (f: A -> B) (i: atom) (m: t A),
    get i (map f m) = f(get i m).
  Proof.
    intros. unfold map. unfold get. simpl. rewrite ATree'.gmap.
    unfold option_map. destruct (ATree'.get i (snd m)); auto.
  Qed.

End AMap'.

(** * An implementation of maps over type [atom] using AVL *)

Module AMap <: MAP.

  Definition elt := atom.
  Definition elt_eq := AtomOT.eq_dec .

  Definition t (A : Type) : Type := (A * ATree.t A)%type.

  Definition init (A : Type) (x : A) :=
    (x, ATree.empty A).

  Definition get (A : Type) (i : atom) (m : t A) :=
    match ATree.get i (snd m) with
    | Some x => x
    | None => fst m
    end.

  Definition set (A : Type) (i : atom) (x : A) (m : t A) :=
    (fst m, ATree.set i x (snd m)).

  Theorem gi:
    forall (A: Type) (i: atom) (x: A), get i (init x) = x.
  Proof.
    intros. unfold init. unfold get. simpl. rewrite ATree.gempty. auto.
  Qed.

  Theorem gss:
    forall (A: Type) (i: atom) (x: A) (m: t A), get i (set i x m) = x.
  Proof.
    intros. unfold get. unfold set. simpl. rewrite ATree.gss. auto.
  Qed.

  Theorem gso:
    forall (A: Type) (i j:atom) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros. unfold get. unfold set. simpl. rewrite ATree.gso; auto.
  Qed.

  Theorem gsspec:
    forall (A: Type) (i j: atom) (x: A) (m: t A),
    get i (set j x m) = if eq_atom_dec i j then x else get i m.
  Proof.
    intros. destruct (eq_atom_dec i j).
     rewrite e. apply gss. auto.
     apply gso. auto.
  Qed.

  Theorem gsident:
    forall (A: Type) (i j: atom) (m: t A),
    get j (set i (get i m) m) = get j m.
  Proof.
    intros. destruct (eq_atom_dec i j).
     rewrite e. rewrite gss. auto.
     rewrite gso; auto.
  Qed.

  Definition map (A B : Type) (f : A -> B) (m : t A) : t B :=
    (f (fst m), ATree.map (fun _ => f) (snd m)).

  Theorem gmap:
    forall (A B: Type) (f: A -> B) (i: atom) (m: t A),
    get i (map f m) = f(get i m).
  Proof.
    intros. unfold map. unfold get. simpl. rewrite ATree.gmap.
    unfold option_map. destruct (ATree.get i (snd m)); auto.
  Qed.

End AMap.

(** * An implementation of maps over any type that injects into type [positive] *)

Module Type INDEXED_TYPE.
  Variable t: Type.
  Variable index: t -> positive.
  Hypothesis index_inj: forall (x y: t), index x = index y -> x = y.
  Variable eq: forall (x y: t), {x = y} + {x <> y}.
End INDEXED_TYPE.

Module IMap(X: INDEXED_TYPE).

  Definition elt := X.t.
  Definition elt_eq := X.eq.
  Definition t : Type -> Type := PMap.t.
  Definition eq: forall (A: Type), (forall (x y: A), {x=y} + {x<>y}) ->
                 forall (a b: t A), {a = b} + {a <> b} := PMap.eq.
  Definition init (A: Type) (x: A) := PMap.init x.
  Definition get (A: Type) (i: X.t) (m: t A) := PMap.get (X.index i) m.
  Definition set (A: Type) (i: X.t) (v: A) (m: t A) := PMap.set (X.index i) v m.
  Definition map (A B: Type) (f: A -> B) (m: t A) : t B := PMap.map f m.

  Lemma gi:
    forall (A: Type) (x: A) (i: X.t), get i (init x) = x.
  Proof.
    intros. unfold get, init. apply PMap.gi.
  Qed.

  Lemma gss:
    forall (A: Type) (i: X.t) (x: A) (m: t A), get i (set i x m) = x.
  Proof.
    intros. unfold get, set. apply PMap.gss.
  Qed.

  Lemma gso:
    forall (A: Type) (i j: X.t) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros. unfold get, set. apply PMap.gso.
    red. intro. apply H. apply X.index_inj; auto.
  Qed.

  Lemma gsspec:
    forall (A: Type) (i j: X.t) (x: A) (m: t A),
    get i (set j x m) = if X.eq i j then x else get i m.
  Proof.
    intros. unfold get, set.
    rewrite PMap.gsspec.
    case (X.eq i j); intro.
    subst j. rewrite peq_true. reflexivity.
    rewrite peq_false. reflexivity.
    red; intro. elim n. apply X.index_inj; auto.
  Qed.

  Lemma gmap:
    forall (A B: Type) (f: A -> B) (i: X.t) (m: t A),
    get i (map f m) = f(get i m).
  Proof.
    intros. unfold map, get. apply PMap.gmap.
  Qed.

End IMap.

Module ZIndexed.
  Definition t := Z.
  Definition index (z: Z): positive :=
    match z with
    | Z0 => xH
    | Zpos p => xO p
    | Zneg p => xI p
    end.
  Lemma index_inj: forall (x y: Z), index x = index y -> x = y.
  Proof.
    unfold index; destruct x; destruct y; intros;
    try discriminate; try reflexivity.
    congruence.
    congruence.
  Qed.
  Definition eq := zeq.
End ZIndexed.

Module ZMap := IMap(ZIndexed).

Module NIndexed.
  Definition t := N.
  Definition index (n: N): positive :=
    match n with
    | N0 => xH
    | Npos p => xO p
    end.
  Lemma index_inj: forall (x y: N), index x = index y -> x = y.
  Proof.
    unfold index; destruct x; destruct y; intros;
    try discriminate; try reflexivity.
    congruence.
  Qed.
  Lemma eq: forall (x y: N), {x = y} + {x <> y}.
  Proof.
    decide equality. apply peq.
  Qed.
End NIndexed.

Module NMap := IMap(NIndexed).

(** * An implementation of maps over any type with decidable equality *)

Module Type EQUALITY_TYPE.
  Variable t: Type.
  Variable eq: forall (x y: t), {x = y} + {x <> y}.
End EQUALITY_TYPE.

Module EMap(X: EQUALITY_TYPE) <: MAP.

  Definition elt := X.t.
  Definition elt_eq := X.eq.
  Definition t (A: Type) := X.t -> A.
  Definition init (A: Type) (v: A) := fun (_: X.t) => v.
  Definition get (A: Type) (x: X.t) (m: t A) := m x.
  Definition set (A: Type) (x: X.t) (v: A) (m: t A) :=
    fun (y: X.t) => if X.eq y x then v else m y.
  Lemma gi:
    forall (A: Type) (i: elt) (x: A), init x i = x.
  Proof.
    intros. reflexivity.
  Qed.
  Lemma gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), (set i x m) i = x.
  Proof.
    intros. unfold set. case (X.eq i i); intro.
    reflexivity. tauto.
  Qed.
  Lemma gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> (set j x m) i = m i.
  Proof.
    intros. unfold set. case (X.eq i j); intro.
    congruence. reflexivity.
  Qed.
  Lemma gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then x else get i m.
  Proof.
    intros. unfold get, set, elt_eq. reflexivity.
  Qed.
  Lemma gsident:
    forall (A: Type) (i j: elt) (m: t A), get j (set i (get i m) m) = get j m.
  Proof.
    intros. unfold get, set. case (X.eq j i); intro.
    congruence. reflexivity.
  Qed.
  Definition map (A B: Type) (f: A -> B) (m: t A) :=
    fun (x: X.t) => f(m x).
  Lemma gmap:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map f m) = f(get i m).
  Proof.
    intros. unfold get, map. reflexivity.
  Qed.
End EMap.

(** * Additional properties over trees *)

Module Tree_Properties(T: TREE).

(** An induction principle over [fold]. *)

Section TREE_FOLD_IND.

Variables V A: Type.
Variable f: A -> T.elt -> V -> A.
Variable P: T.t V -> A -> Prop.
Variable init: A.
Variable m_final: T.t V.

Hypothesis P_compat:
  forall m m' a,
  (forall x, T.get x m = T.get x m') ->
  P m a -> P m' a.

Hypothesis H_base:
  P (T.empty _) init.

Hypothesis H_rec:
  forall m a k v,
  T.get k m = None -> T.get k m_final = Some v -> P m a -> P (T.set k v m) (f a k v).

Definition f' (a: A) (p : T.elt * V) := f a (fst p) (snd p).

Definition P' (l: list (T.elt * V)) (a: A) : Prop :=
  forall m, list_equiv l (T.elements m) -> P m a.

Remark H_base':
  P' nil init.
Proof.
  red; intros. apply P_compat with (T.empty _); auto.
  intros. rewrite T.gempty. symmetry. case_eq (T.get x m); intros; auto.
  assert (In (x, v) nil). rewrite (H (x, v)). apply T.elements_correct. auto.
  contradiction.
Qed.

Remark H_rec':
  forall k v l a,
  ~In k (List.map (@fst T.elt V) l) ->
  In (k, v) (T.elements m_final) ->
  P' l a ->
  P' (l ++ (k, v) :: nil) (f a k v).
Proof.
  unfold P'; intros.
  set (m0 := T.remove k m).
  apply P_compat with (T.set k v m0).
    intros. unfold m0. rewrite T.gsspec. destruct (T.elt_eq x k).
    symmetry. apply T.elements_complete. rewrite <- (H2 (x, v)).
    apply in_or_app. simpl. intuition congruence.
    apply T.gro. auto.
  apply H_rec. unfold m0. apply T.grs. apply T.elements_complete. auto.
  apply H1. red. intros [k' v'].
  split; intros.
  apply T.elements_correct. unfold m0. rewrite T.gro. apply T.elements_complete.
  rewrite <- (H2 (k', v')). apply in_or_app. auto.
  red; intro; subst k'. elim H. change k with (fst (k, v')). apply in_map. auto.
  assert (T.get k' m0 = Some v'). apply T.elements_complete. auto.
  unfold m0 in H4. rewrite T.grspec in H4. destruct (T.elt_eq k' k). congruence.
  assert (In (k', v') (T.elements m)). apply T.elements_correct; auto.
  rewrite <- (H2 (k', v')) in H5. destruct (in_app_or _ _ _ H5). auto.
  simpl in H6. intuition congruence.
Qed.

Lemma fold_rec_aux:
  forall l1 l2 a,
  list_equiv (l2 ++ l1) (T.elements m_final) ->
  list_disjoint (List.map (@fst T.elt V) l1) (List.map (@fst T.elt V) l2) ->
  list_norepet (List.map (@fst T.elt V) l1) ->
  P' l2 a -> P' (l2 ++ l1) (List.fold_left f' l1 a).
Proof.
  induction l1; intros; simpl.
  rewrite <- List.app_nil_end. auto.
  destruct a as [k v]; simpl in *. inv H1.
  change ((k, v) :: l1) with (((k, v) :: nil) ++ l1). rewrite <- List.app_ass. apply IHl1.
  rewrite app_ass. auto.
  red; intros. rewrite List.map_app in H3. destruct (in_app_or _ _ _ H3). apply H0; auto with coqlib.
  simpl in H4. intuition congruence.
  auto.
  unfold f'. simpl. apply H_rec'; auto. eapply list_disjoint_notin; eauto with coqlib.
  rewrite <- (H (k, v)). apply in_or_app. simpl. auto.
Qed.

Theorem fold_rec:
  P m_final (T.fold f m_final init).
Proof.
  intros. rewrite T.fold_spec. fold f'.
  assert (P' (nil ++ T.elements m_final) (List.fold_left f' (T.elements m_final) init)).
    apply fold_rec_aux.
    simpl. red; intros; tauto.
    simpl. red; intros. elim H0.
    apply T.elements_keys_norepet.
    apply H_base'.
  simpl in H. red in H. apply H. red; intros. tauto.
Qed.

End TREE_FOLD_IND.

End Tree_Properties.

Module More_Tree_Properties(T: TREE).

Module TProp := Tree_Properties(T).

Notation "a ! b" := (T.get b a) (at level 1).
Notation "a !! b" := (T.get b a) (at level 1).

Definition successors_list A (successors: T.t (list A)) (pc: T.elt) 
  : list A :=
  match successors!pc with None => nil | Some l => l end.

Implicit Arguments successors_list [A].

Notation "a !!! b" := (successors_list a b) (at level 1).

Lemma successors_list_spec: forall A (a:A) scss l0,
  In a (scss!!!l0) -> exists scs, scss!l0 = Some scs /\ In a scs.
Proof.
  unfold successors_list.
  intros.
  destruct (scss!l0); [eauto | inv H].
Qed.

Section Predecessor. 

Variable successors: T.t (list T.elt).

Fixpoint add_successors (pred: T.t (list T.elt))
                        (from: T.elt) (tolist: list T.elt)
                        {struct tolist} : T.t (list T.elt) :=
  match tolist with
  | nil => pred
  | to :: rem => add_successors (T.set to (from :: pred!!!to) pred) from rem
  end.

Lemma add_successors_correct:
  forall tolist from pred n s,
  In n pred!!!s \/ (n = from /\ In s tolist) ->
  In n (add_successors pred from tolist)!!!s.
Proof.
  induction tolist; simpl; intros.
  tauto.
  apply IHtolist.
  unfold successors_list at 1. rewrite T.gsspec.
  destruct (T.elt_eq s a).
    subst a. 
    destruct H. 
      auto with coqlib.
      destruct H.
        subst n. auto with coqlib.
    fold (successors_list pred s). intuition congruence.
Qed.

Lemma add_successors_correct':
  forall tolist from pred n s,
  In n (add_successors pred from tolist)!!!s ->
  In n pred!!!s \/ (n = from /\ In s tolist).
Proof.
  induction tolist; simpl; intros.
  tauto.
  apply IHtolist in H.
  unfold successors_list at 1 in H.
  rewrite T.gsspec in H.
  destruct (T.elt_eq s a); subst.
    simpl in H.
    destruct H.
      destruct H; subst; auto.
      destruct H as [H1 H2]; subst; auto.

      fold (successors_list pred s) in H. intuition congruence.
Qed.

Lemma add_successors_correct'': forall (m a : T.t (list T.elt)) 
  (k : T.elt) (v : list T.elt)
  (Herr : m ! k = None) (l1 l2 : T.elt)
  (Hinc: In l1 a !!! l2 -> In l2 m !!! l1)
  (Hin: In l1 (add_successors a k v) !!! l2), In l2 (T.set k v m) !!! l1.
Proof.
  intros.
  apply add_successors_correct' in Hin. 
  unfold successors_list.
  rewrite T.gsspec.
  destruct (T.elt_eq l1 k).
    destruct Hin as [Hin | [EQ Hin]]; subst; auto.
      apply Hinc in Hin.
      unfold successors_list in Hin.
      rewrite Herr in Hin. inv Hin.
 
    destruct Hin as [Hin | [EQ Hin]]; subst; try congruence.
      apply Hinc in Hin. 
      unfold successors_list in Hin.
      auto.    
Qed.

Definition make_predecessors : T.t (list T.elt) :=
  T.fold add_successors successors (T.empty (list T.elt)).

Lemma make_predecessors_correct:
  forall n s,
  In s successors!!!n ->
  In n make_predecessors!!!s.
Proof.
  set (P := fun succ pred =>
          forall n s, In s succ!!!n -> In n pred!!!s).
  unfold make_predecessors.
  apply TProp.fold_rec with (P := P).
(* extensionality *)
  unfold P; unfold successors_list; intros.
  rewrite <- H in H1. auto.
(* base case *)
  red; unfold successors_list. intros n s. repeat rewrite T.gempty. auto.
(* inductive case *)
  unfold P; intros. apply add_successors_correct.
  unfold successors_list in H2. rewrite T.gsspec in H2.
  destruct (T.elt_eq n k).
  subst k. auto.
  fold (successors_list m n) in H2. auto.
Qed.

Lemma make_predecessors_correct':
  forall n s,
  In n make_predecessors!!!s ->
  In s successors!!!n.
Proof.
  set (P := fun succ pred =>
          forall n s, In n pred!!!s -> In s succ!!!n).
  unfold make_predecessors.
  apply TProp.fold_rec with (P := P).
(* extensionality *)
  unfold P; unfold successors_list; intros.
  rewrite <- H. auto.
(* base case *)
  red; unfold successors_list. intros n s. repeat rewrite T.gempty. auto.
(* inductive case *)
  unfold P; intros. apply add_successors_correct' in H2.
  unfold successors_list in *. rewrite T.gsspec.
  destruct H2 as [H2 | [Heq H2]]; subst.
    destruct (T.elt_eq n k); subst; auto.
      apply H1 in H2. unfold successors_list in H2. rewrite H in H2. inv H2.
    destruct (T.elt_eq k k); subst; auto.
      congruence.
Qed.

Lemma eq_eli__eq_successors_list: forall (m m':T.t (list T.elt)) x
  (Heq: m ! x = m' ! x), m !!! x = m' !!! x.
Proof.
  intros.
  unfold successors_list.
  erewrite Heq. auto.
Qed.

End Predecessor.

Definition children_of_tree A (tree: T.t (list A)) :=
  flat_map snd (T.elements tree).

Definition parents_of_tree A (tree: T.t A) :=
  List.map fst (T.elements tree).

Implicit Arguments children_of_tree [A].
Implicit Arguments parents_of_tree [A].

Require Import Program.Tactics.

Lemma children_in_children_of_tree: forall A (succs:T.t (list A)) l0,
  incl (succs !!! l0) (children_of_tree succs).
Proof.
  intros.
  intros x Hin.
  apply in_flat_map.
  apply successors_list_spec in Hin.
  destruct_conjs.
  eauto using T.elements_correct.
Qed.

Lemma parents_of_tree_spec: forall A l0 (tr: T.t A),
  In l0 (parents_of_tree tr) <-> exists a, In (l0, a) (T.elements tr).
Proof.
  unfold parents_of_tree.
  intros.
  split; intro J.
    apply in_map_iff in J.
    destruct J as [[x1 x2] [J1 J2]]. subst. eauto.

    apply in_map_iff.
    destruct J as [y J]. exists (l0, y). auto.
Qed.

Lemma notin_tree__notin_parents_of_tree: forall (visited : T.t unit)
  l0 (H0 : visited ! l0 = None),
  ~ In l0 (parents_of_tree visited).
Proof.
  intros.
  intros Hin'. apply parents_of_tree_spec in Hin'.
  destruct Hin' as [a Hin'].
  apply T.elements_complete in Hin'. 
  congruence.
Qed.

Lemma in_tree__in_parents_of_tree: forall (visited : T.t unit) a
  l0 (H0 : visited ! l0 = Some a),
  In l0 (parents_of_tree visited).
Proof.
  intros.
  apply parents_of_tree_spec. 
  apply T.elements_correct in H0.  eauto.
Qed.

Lemma parents_children_of_tree__inc__length_le: forall 
  (eq_dec : forall x y : T.elt, {x = y}+{x <> y}) (visited:T.t T.elt)
  succs (Hinc: incl (parents_of_tree visited) (children_of_tree succs)),
  (length (parents_of_tree visited) <= length (children_of_tree succs))%nat.
Proof.
  intros. 
  apply incl__length_le; auto.
    apply T.elements_keys_norepet.
Qed.

Ltac destruct_if :=
match goal with
| H: context [(if ?lk then _ else _)] |- _ =>
   remember lk as R; destruct R; try inv H
| H: context [if ?lk then _ else _] |- _ =>
   remember lk as R; destruct R; try inv H
| |- context [(if ?lk then _ else _)] =>
   remember lk as R; destruct R; subst; auto
| |- context [if ?lk then _ else _] => remember lk as R; destruct R; subst; auto
end.

Lemma parents_of_tree_succ_len: forall (visited : T.t unit)
  l0 (H0 : visited ! l0 = None),
  length (parents_of_tree (T.set l0 tt visited)) =
    (length (parents_of_tree visited) + 1)%nat.
Proof.
  intros.
  unfold parents_of_tree.
  apply norepet_equiv__length_cons_eq with (a:=l0); 
    auto using T.elements_keys_norepet.
    apply notin_tree__notin_parents_of_tree; auto.

    intro x; split; intro Hin.
      apply parents_of_tree_spec in Hin.
      destruct_conjs.
      apply T.elements_complete in H. 
      rewrite T.gsspec in H.
      destruct_if.
        auto with datatypes v62.

        apply in_tree__in_parents_of_tree in H2.
        auto with datatypes v62.

      apply parents_of_tree_spec.
      destruct_in Hin.
        exists tt.
        apply T.elements_correct.
        rewrite T.gsspec.
        destruct_if. 
          congruence.

        apply parents_of_tree_spec in Hin.
        destruct_conjs.
        exists Hin. 
        apply T.elements_correct.
        rewrite T.gsspec.
        destruct_if. 
          apply T.elements_complete in H.  
          congruence.

          apply T.elements_complete in H. auto.
Qed.

Lemma parents_of_empty_tree: forall A,
  parents_of_tree (T.empty A) = nil.
Proof. 
  unfold parents_of_tree. 
  intros.
  remember (List.map fst (T.elements (T.empty A))) as R.
  destruct R as [|e]; auto. 
  assert (In e (List.map fst (T.elements (T.empty A)))) as Hin.
    rewrite <- HeqR. auto with coqlib.
  apply in_map_iff in Hin.
  destruct_conjs.
  apply T.elements_complete in H0.
  rewrite T.gempty in H0.
  congruence.
Qed.

Definition in_cfg successors n : Prop :=
  In n (parents_of_tree successors) \/ 
  In n (children_of_tree successors).

Lemma in_parents_of_tree__in_cfg: forall scs n,
  In n (parents_of_tree scs) -> in_cfg scs n.
Proof. unfold in_cfg. auto. Qed.

Lemma in_succ__in_cfg: forall p scs sc
  (Hinscs : In sc scs !!! p),
  in_cfg scs sc.
Proof.
  intros. right.
  apply children_in_children_of_tree in Hinscs. auto.
Qed.

Lemma parents_of_tree__in_successors: forall A p (successors:T.t A),
  In p (parents_of_tree successors) <-> exists s, successors ! p = Some s.
Proof.
  intros.
  split; intro J.
    apply parents_of_tree_spec in J.
    destruct J as [? J].
    apply T.elements_complete in J. eauto.

    apply parents_of_tree_spec.
    destruct J as [? J].
    apply T.elements_correct in J. eauto.
Qed.

Lemma in_pred__in_parents: forall p scs n
  (Hinprds : In p (make_predecessors scs) !!! n),
  In p (parents_of_tree scs).
Proof.
  intros.
  apply make_predecessors_correct' in Hinprds.
  apply parents_of_tree_spec.
  apply successors_list_spec in Hinprds.
  destruct Hinprds as [scs0 [J1 J2]].
  apply T.elements_correct in J1. eauto.
Qed.

Lemma nonleaf_is_parent: forall A succs x (Hnnil : succs !!! x <> @nil A),
  In x (parents_of_tree succs).
Proof.
  intros.
  apply parents_of_tree_spec.
  assert (exists a, In a (succs!!!x)) as Hin.
    destruct (succs!!!x) as [|a].
      congruence.
      exists a. simpl. auto.
  destruct Hin as [a Hin].
  apply successors_list_spec in Hin.
  destruct Hin as [scs [J1 J2]].
  apply T.elements_correct in J1.
  eauto.
Qed.

Lemma children_of_tree_spec: forall A (l0:A) tr,
  In l0 (children_of_tree tr) <-> 
  exists a, exists scs, In (a, scs) (T.elements tr) /\ In l0 scs.
Proof.
  unfold children_of_tree.
  intros.
  split; intro J.
    apply in_flat_map in J.
    destruct J as [[x1 x2] [J1 J2]]. simpl in *. eauto.

    apply in_flat_map.
    destruct J as [y [xs J]]. exists (y, xs). auto.
Qed.

Lemma children_of_tree__in_successors: forall A (s:A) successors,
  In s (children_of_tree successors) <-> 
     exists p, exists scs, successors ! p = Some scs /\ In s scs.
Proof.
  intros.
  split; intro J.
    apply children_of_tree_spec in J.
    destruct J as [? [? [J Hin]]].
    apply T.elements_complete in J. eauto.

    apply children_of_tree_spec.
    destruct J as [? [? [J Hin]]].
    apply T.elements_correct in J. eauto.
Qed.

Lemma successors_list_intro: forall (scss:T.t (list T.elt)) l0 scs 
  (Hget: scss ! l0 = Some scs),
  scss!!!l0 = scs.
Proof.
  unfold successors_list.
  intros. rewrite Hget. auto.
Qed.

Lemma in_successors_list_intro: forall (scss:T.t (list T.elt)) l0 
  sc scs (Hget: scss ! l0 = Some scs) (Hin: In sc scs),
  In sc (scss!!!l0).
Proof.
  unfold successors_list.
  intros. rewrite Hget. auto.
Qed.

Lemma has_succ__in_cfg: forall succs n sc 
  (Hin: In sc (successors_list succs n)),
  in_cfg succs n.
Proof.
  intros.
  eapply in_parents_of_tree__in_cfg; eauto.
  apply parents_of_tree__in_successors.
  apply successors_list_spec in Hin.
  destruct_conjs. eauto.
Qed.

Lemma in_cfg_dec: forall (Hdec: forall x y : T.elt, {x = y} + {x <> y})
  successors n,  
  in_cfg successors n \/ ~ in_cfg successors n.
Proof.
  unfold in_cfg.
  intros.
  destruct (In_dec Hdec n (parents_of_tree successors)) as [J1 | J1]; auto.
  destruct (In_dec Hdec n (children_of_tree successors)) as [J2 | J2]; auto.
  right. intro J. tauto.
Qed.

Lemma no_preds__notin_succs: forall successors entrypoint
  (Hnopred: (make_predecessors successors) !!! entrypoint = nil),
  forall a0
    (Hin: In entrypoint (successors_list successors a0)), False.
Proof.
  intros. apply make_predecessors_correct in Hin. 
  rewrite Hnopred in Hin. tauto.
Qed.

Section ElementsOfCfg.

Variable successors: T.t (list T.elt).
Hypothesis Hdec: forall x y : T.elt, {x = y} + {x <> y}.

Definition elements_of_cfg: list T.elt :=
  remove_redundancy Hdec nil 
    (parents_of_tree successors ++ children_of_tree successors).

Lemma in_elements_of_cfg__in_cfg: forall l0,
  (In l0 (elements_of_cfg) <-> in_cfg successors l0).
Proof.
  intros.
  split; intro J.
    unfold elements_of_cfg in J.
    apply remove_redundancy_in in J; auto.
    unfold in_cfg.
    destruct_in J; auto.

    apply remove_redundancy_in; auto.
    apply in_or_app.
    destruct J; auto.  
Qed.

Lemma succs_in_elements_of_cfg: forall n, 
  incl (successors_list successors n) elements_of_cfg.
Proof.
  intros.
  unfold elements_of_cfg.
  intros x Hin.
  apply remove_redundancy_in; auto.
    apply children_in_children_of_tree in Hin.
    auto with datatypes v62.
Qed.

End ElementsOfCfg.

End More_Tree_Properties.

Module XATree := More_Tree_Properties(ATree).
Module XPTree := More_Tree_Properties(PTree).
Module ATree_Properties := Tree_Properties(ATree).
Module PTree_Properties := Tree_Properties(PTree).

(** * Useful notations *)

Notation "a ! b" := (ATree.get b a) (at level 1).
Notation "a !! b" := (AMap.get b a) (at level 1).
Notation "a !!! b" := (XATree.successors_list a b) (at level 1).

Notation "a ? b" := (PTree.get b a) (at level 1).
Notation "a ?? b" := (PMap.get b a) (at level 1).
Notation "a ??? b" := (XPTree.successors_list a b) (at level 1).

(* $Id: Maps.v,v 1.12.4.4 2006/01/07 11:46:55 xleroy Exp $ *)
