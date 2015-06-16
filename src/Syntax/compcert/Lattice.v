(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Constructions of semi-lattices. *)

Require Import Coqlib.
Require Import Maps.
Require Import FSets.
Require Import Metatheory.

(** * Signatures of semi-lattices *)

(** A semi-lattice is a type [t] equipped with an equivalence relation [eq],
  a boolean equivalence test [beq], a partial order [ge], a smallest element
  [bot], and an upper bound operation [lub].
  Note that we do not demand that [lub] computes the least upper bound. *)

Module Type SEMILATTICE.

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

End SEMILATTICE.

(** A semi-lattice ``with top'' is similar, but also has a greatest
  element [top]. *)

Module Type SEMILATTICE_WITH_TOP.

  Include Type SEMILATTICE.
  Variable top: t.
  Hypothesis ge_top: forall x, ge top x.

End SEMILATTICE_WITH_TOP.

(** * Semi-lattice over maps *)

(** Given a semi-lattice with top [L], the following functor implements
  a semi-lattice structure over finite maps from positive numbers to [L.t].
  The default value for these maps is either [L.top] or [L.bot]. *)

Module LPMap(L: SEMILATTICE_WITH_TOP) <: SEMILATTICE_WITH_TOP.

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

(** * Semi-lattice over a set. *)

(** Given a set [S: FSetInterface.S], the following functor
    implements a semi-lattice over these sets, ordered by inclusion. *)

Module LFSet (S: FSetInterface.S) <: SEMILATTICE.

  Definition t := S.t.

  Definition eq (x y: t) := S.Equal x y.
  Definition eq_refl: forall x, eq x x := S.eq_refl.
  Definition eq_sym: forall x y, eq x y -> eq y x := S.eq_sym.
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := S.eq_trans.
  Definition beq: t -> t -> bool := S.equal.
  Definition beq_correct: forall x y, beq x y = true -> eq x y := S.equal_2.

  Definition ge (x y: t) := S.Subset y x.
  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    unfold eq, ge, S.Equal, S.Subset; intros. firstorder.
  Qed.
  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    unfold ge, S.Subset; intros. eauto.
  Qed.
  Lemma ge_compat: forall x x' y y', eq x x' -> eq y y' -> ge x y -> ge x' y'.
  Proof.
    unfold ge, eq, S.Subset, S.Equal; intros. firstorder.
  Qed.

  Definition  bot: t := S.empty.
  Lemma ge_bot: forall x, ge x bot.
  Proof.
    unfold ge, bot, S.Subset; intros. elim (S.empty_1 H).
  Qed.

  Definition lub: t -> t -> t := S.union.
  Lemma lub_commut: forall x y, eq (lub x y) (lub y x).
  Proof.
    unfold lub, eq, S.Equal; intros. split; intro.
    destruct (S.union_1 H). apply S.union_3; auto. apply S.union_2; auto.
    destruct (S.union_1 H). apply S.union_3; auto. apply S.union_2; auto.
  Qed.

  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    unfold lub, ge, S.Subset; intros. apply S.union_2; auto.
  Qed.

End LFSet.

(** * Flat semi-lattice *)

(** Given a type with decidable equality [X], the following functor
  returns a semi-lattice structure over [X.t] complemented with
  a top and a bottom element.  The ordering is the flat ordering
  [Bot < Inj x < Top]. *)

Module LFlat(X: EQUALITY_TYPE) <: SEMILATTICE_WITH_TOP.

Inductive t_ : Type :=
  | Bot: t_
  | Inj: X.t -> t_
  | Top: t_.

Definition t : Type := t_.

Definition eq (x y: t) := (x = y).
Definition eq_refl: forall x, eq x x := (@refl_equal t).
Definition eq_sym: forall x y, eq x y -> eq y x := (@sym_equal t).
Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@trans_equal t).

Definition beq (x y: t) : bool :=
  match x, y with
  | Bot, Bot => true
  | Inj u, Inj v => if X.eq u v then true else false
  | Top, Top => true
  | _, _ => false
  end.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof.
  unfold eq; destruct x; destruct y; simpl; try congruence; intro.
  destruct (X.eq t0 t1); congruence.
Qed.

Definition ge (x y: t) : Prop :=
  match x, y with
  | Top, _ => True
  | _, Bot => True
  | Inj a, Inj b => a = b
  | _, _ => False
  end.

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof.
  unfold eq, ge; intros; subst y; destruct x; auto.
Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof.
  unfold ge; destruct x; destruct y; try destruct z; intuition.
  transitivity t1; auto.
Qed.

Lemma ge_compat: forall x x' y y', eq x x' -> eq y y' -> ge x y -> ge x' y'.
Proof.
  unfold eq; intros; congruence.
Qed.

Definition bot: t := Bot.

Lemma ge_bot: forall x, ge x bot.
Proof.
  destruct x; simpl; auto.
Qed.

Definition top: t := Top.

Lemma ge_top: forall x, ge top x.
Proof.
  destruct x; simpl; auto.
Qed.

Definition lub (x y: t) : t :=
  match x, y with
  | Bot, _ => y
  | _, Bot => x
  | Top, _ => Top
  | _, Top => Top
  | Inj a, Inj b => if X.eq a b then Inj a else Top
  end.

Lemma lub_commut: forall x y, eq (lub x y) (lub y x).
Proof.
  unfold eq; destruct x; destruct y; simpl; auto.
  case (X.eq t0 t1); case (X.eq t1 t0); intros; congruence.
Qed.

Lemma ge_lub_left: forall x y, ge (lub x y) x.
Proof.
  destruct x; destruct y; simpl; auto.
  case (X.eq t0 t1); simpl; auto.
Qed.

End LFlat.

(** * Boolean semi-lattice *)

(** This semi-lattice has only two elements, [bot] and [top], trivially
  ordered. *)

Module LBoolean <: SEMILATTICE_WITH_TOP.

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
(** * Domination analysis *)

(** The type [Dominators] of compile-time approximations of domination. *)

(** We equip this type of approximations with a semi-lattice structure.
  The ordering is inclusion between the sets of values denoted by
  the approximations. *)

Module Dominators <: SEMILATTICE_WITH_TOP.

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
    destruct x, y, z; simpl; eauto 2 with datatypes v62.
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
    unfold lub, ge, sub. destruct x, y; simpl; auto with datatypes v62.
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


