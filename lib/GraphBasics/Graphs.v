(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)



(* Like digraph, a graph is a type dependant of a set of vertices and   *)
(* a set of arcs. A graph is inhabited, when the construction is        *)
(* possible.Inversion lemmas are proved.                                *)

(* The following notion are defined :                                   *)
(*      - (Graph v a): dependant of a set of vertices and a set of arcs *)
(*              constructors : G_empty, G_vertex, G_edge, G_eq;         *)
(*      - GV_list : list of vertices in order of construction;          *)
(*      - GA_list : list of arcs containing (xy) and (yx);              *)
(*      - GE_list : list of edge containing (xy) or (yx);               *)
(*      - G_order : number of vertices;                                 *)
(*      - G_size : number of edges.                                     *)

Require Export Digraphs.
Require Export Edges.

Section GRAPH.

Variable A:Type.
Variable eq_a_dec: forall x y : A, {x = y} + {x <> y}.

Inductive Graph : @V_set A -> @A_set A -> Type :=
  | G_empty : Graph (@V_empty _) (@A_empty _)
  | G_vertex :
      forall (v : V_set) (a : A_set) (d : Graph v a) (x : Vertex),
      ~ v x -> Graph (V_union (V_single x) v) a
  | G_edge :
      forall (v : V_set) (a : A_set) (d : Graph v a) (x y : Vertex),
      v x ->
      v y ->
      x <> y ->
      ~ a (A_ends x y) -> ~ a (A_ends y x) -> Graph v (A_union (E_set x y) a)
  | G_eq :
      forall (v v' : V_set) (a a' : A_set),
      v = v' -> a = a' -> Graph v a -> Graph v' a'.

Fixpoint GV_list (v : V_set) (a : A_set) (g : Graph v a) {struct g} :
 V_list :=
  match g with
  | G_empty => V_nil
  | G_vertex v' a' g' x _ => x :: GV_list v' a' g'
  | G_edge v' a' g' x y _ _ _ _ _ => GV_list v' a' g'
  | G_eq v' _ a' _ _ _ g' => GV_list v' a' g'
  end.

Fixpoint GA_list (v : V_set) (a : A_set) (g : Graph v a) {struct g} :
 A_list :=
  match g with
  | G_empty => A_nil
  | G_vertex v' a' g' x _ => GA_list v' a' g'
  | G_edge v' a' g' x y _ _ _ _ _ =>
      A_ends x y :: A_ends y x :: GA_list v' a' g'
  | G_eq v' _ a' _ _ _ g' => GA_list v' a' g'
  end.

Fixpoint GE_list (v : V_set) (a : A_set) (g : Graph v a) {struct g} :
 E_list :=
  match g with
  | G_empty => E_nil
  | G_vertex v' a' g' x _ => GE_list v' a' g'
  | G_edge v' a' g' x y _ _ _ _ _ => E_ends x y :: GE_list v' a' g'
  | G_eq v' _ a' _ _ _ g' => GE_list v' a' g'
  end.

Definition G_order (v : V_set) (a : A_set) (g : Graph v a) :=
  length (GV_list v a g).

Definition G_size (v : V_set) (a : A_set) (g : Graph v a) :=
  length (GE_list v a g).

Lemma G_v_dec :
 forall (v : V_set) (a : A_set) (g : Graph v a) (x : Vertex), {v x} + {~ v x}.
Proof.
        intros v a g; elim g; intros.
        right; apply V_empty_nothing.

        case (X x0); intros.
        left; apply V_in_right; trivial.

        case (V_eq_dec eq_a_dec x x0); intros.
        left; apply V_in_left; rewrite e; apply V_in_single.

        right; red in |- *; intros; inversion H.
        elim n1; inversion H0; trivial.

        elim n0; trivial.

        auto.

        case (X x); intros.
        left; elim e; trivial.

        right; elim e; trivial.
Qed.

Lemma G_a_dec :
 forall (v : V_set) (a : A_set) (g : Graph v a) (x : Arc), {a x} + {~ a x}.
Proof.
        intros v a g; elim g; intros.
        right; apply A_empty_nothing.

        auto.

        case (X x0); intros.
        left; apply A_in_right; trivial.

        case (A_eq_dec eq_a_dec (A_ends x y) x0); intros.
        left; apply A_in_left; rewrite <- e; apply E_right; trivial.

        case (A_eq_dec eq_a_dec (A_ends y x) x0); intros.
        left; apply A_in_left; rewrite <- e; apply E_left; trivial.

        right; red in |- *; intros; inversion H.
        inversion H0.
        elim n3; trivial.

        elim n4; trivial.

        elim n2; trivial.

        case (X x); intros.
        left; elim e0; trivial.

        right; elim e0; trivial.
Qed.

Lemma G_non_directed :
 forall (v : V_set) (a : A_set) (g : Graph v a) (x y : Vertex),
 a (A_ends x y) -> a (A_ends y x).
Proof.
        intros v a g; elim g; intros.
        inversion H.

        auto.

        inversion H0.
        apply A_in_left.
        inversion H1.
        apply E_left.

        apply E_right.

        apply A_in_right; auto.
        apply H. auto.

        generalize H0; elim e0; auto.
Qed.

Lemma G_ina_inv1 :
 forall (v : V_set) (a : A_set) (g : Graph v a) (x y : Vertex),
 a (A_ends x y) -> v x.
Proof.
        intros v a g; elim g; intros.
        inversion H.

        apply V_in_right; apply (H x0 y); trivial.

        inversion H0.
        inversion H1; rewrite <- H4; trivial.

        apply (H x0 y0); trivial.

        rewrite <- e; apply (H x y); rewrite e0; trivial.
Qed.

Lemma G_ina_inv2 :
 forall (v : V_set) (a : A_set) (g : Graph v a) (x y : Vertex),
 a (A_ends x y) -> v y.
Proof.
        intros v a g; elim g; intros.
        inversion H.

        apply V_in_right; apply (H x0 y); trivial.

        inversion H0.
        inversion H1; rewrite <- H5; trivial.

        apply (H x0 y0); trivial.

        rewrite <- e; apply (H x y); rewrite e0; trivial.
Qed.

End GRAPH.

Implicit Arguments Graph [A].

Section GRAPH_TO_DIGRAPH.

Variable A:Type.
Variable eq_a_dec: forall x y : A, {x = y} + {x <> y}.

Lemma graph_isa_digraph :
 forall (v : V_set) (a : @A_set A) (d : Graph v a), Digraph v a.
Proof.
        intros v a d; elim d; intros.
        exact D_empty.

        apply D_vertex; auto.

        apply
         (D_eq v0 v0
            (A_union (A_single (A_ends x y))
               (A_union (A_single (A_ends y x)) a0))
            (A_union (E_set x y) a0)).
        trivial.

        symmetry  in |- *; apply E_add_edge.

        apply D_arc.
        apply D_arc; auto.

        trivial.

        trivial.

        red in |- *; intros; inversion_clear H.
        inversion H0.
        elim n; auto.

        elim n0; auto.

        apply (D_eq v0 v' a0 a'); auto.
Defined.

End GRAPH_TO_DIGRAPH.

Implicit Arguments G_v_dec [A].
Implicit Arguments G_a_dec [A].
Implicit Arguments G_non_directed [A].
Implicit Arguments G_ina_inv2 [A].
Implicit Arguments G_ina_inv1 [A].

Section UNION_GRAPHS.

Variable A:Type.
Variable eq_a_dec: forall x y : A, {x = y} + {x <> y}.

Lemma G_union :
 forall (v1 v2 : V_set) (a1 a2 : @A_set A),
 Graph v1 a1 -> Graph v2 a2 -> Graph (V_union v1 v2) (A_union a1 a2).
Proof.
        intros; elim X; intros.
        apply G_eq with (v := v2) (a := a2).
        symmetry  in |- *; apply V_union_neutral.

        symmetry  in |- *; apply A_union_neutral.

        trivial.

        case (G_v_dec eq_a_dec v2 a2 X0 x); intros.
        apply G_eq with (v := V_union v v2) (a := A_union a a2).
        autounfold.
        rewrite V_union_assoc; rewrite (V_union_absorb (V_single x)); trivial.
        apply V_included_single; apply V_in_right; trivial.

        trivial.

        trivial.

        apply
         G_eq
          with (v := V_union (V_single x) (V_union v v2)) (a := A_union a a2).
        symmetry  in |- *; apply V_union_assoc.

        trivial.

        apply G_vertex.
        trivial.

        apply V_not_union; trivial.

        case (G_a_dec eq_a_dec v2 a2 X0 (A_ends x y)); intros.
        apply G_eq with (v := V_union v v2) (a := A_union a a2).
        trivial.

        repeat autounfold.
        rewrite A_union_assoc; rewrite (A_union_absorb (E_set x y)); trivial.
        apply E_inclusion.
        apply A_in_right; trivial.

        apply A_in_right; apply (G_non_directed v2 a2 X0); auto.

        trivial.

        apply
         G_eq
          with (v := V_union v v2) (a := A_union (E_set x y) (A_union a a2)).
        trivial.

        symmetry  in |- *; apply A_union_assoc.

        apply G_edge.
        trivial.

        apply V_in_left; trivial.

        apply V_in_left; trivial.

        trivial.

        apply A_not_union; trivial.

        apply A_not_union.
        trivial.

        red in |- *; intro; elim n2; apply (G_non_directed v2 a2 X0); trivial.

        apply G_eq with (v := V_union v v2) (a := A_union a a2).
        elim e; trivial.

        elim e0; trivial.

        trivial.
Qed.

End UNION_GRAPHS.

Section INVERSION_GRAPH.

Variable A:Type.
Variable eq_a_dec: forall x y : A, {x = y} + {x <> y}.

Lemma G_empty_empty :
 forall (v : V_set) (a : A_set), Graph v a -> v = (@V_empty A) -> a = (@A_empty _).
Proof.
        intros v a g; elim g; intros.
        trivial.
     
        autounfold in *.
        elim (V_empty_nothing x); fold V_empty in |- *; rewrite <- H0;
         apply V_in_left; apply V_in_single.

        autounfold in *.
        elim (V_empty_nothing x); fold V_empty in |- *; rewrite <- H0;
         trivial.

        rewrite <- e0; apply H; rewrite e; trivial.
Qed.

Lemma V_union_single_inter :
 forall (x y : Vertex) (v v' : @V_set A),
 ~ v x ->
 x <> y ->
 V_union (V_single x) v = V_union (V_single y) v' ->
 V_union (V_single x) (V_inter v v') = v'.
Proof.
        intros; autounfold; rewrite V_distributivity_union_inter.
        fold (Union (@Vertex A)) (@V_inter A) (@V_union A) in |- *; rewrite H1;
         autounfold;
         rewrite (V_union_commut (V_single x));
         rewrite (V_union_commut (V_single y));
         rewrite <- V_distributivity_union_inter.
        fold (Union (@Vertex A)) V_union in |- *. unfold V_single.
        rewrite V_single_single_disjoint.
        autounfold.
        rewrite V_union_commut; apply V_union_neutral.

        auto.
Qed.

Lemma G_minus_vertex :
 forall (v : V_set) (a : A_set) (g : Graph v a) (x : Vertex),
 v x ->
 (forall y : @Vertex A, ~ a (A_ends x y)) ->
 forall v' : V_set, ~ v' x -> v = V_union (V_single x) v' -> Graph v' a.
Proof.
intros v a g; elim g; intros.
elim (V_empty_nothing x); trivial.

case (V_union_single_dec eq_a_dec x x0 v0 n H); intros.
apply G_eq with (v := v0) (a := a0).
apply V_union_inversion with (E := V_single x).
apply V_single_disjoint; trivial.

apply V_single_disjoint; rewrite e; trivial.

pattern x at 2 in |- *; rewrite e; trivial.

trivial.

trivial.

generalize (X x0 v1 H0); intros.
apply G_eq with (v := V_union (V_single x) (V_inter v0 v')) (a := a0).
apply (V_union_single_inter x x0).
trivial.

red in |- *; intros Heq; elim n; rewrite Heq; trivial.

trivial.

trivial.

apply G_vertex.
apply X0.
unfold V_inter in |- *.
rewrite (V_inter_commut v0 v'); apply V_not_inter; trivial.

autounfold.
rewrite V_inter_commut; symmetry  in |- *; apply (V_union_single_inter x0 x).
trivial.

red in |- *; intros Heq; elim n; rewrite <- Heq; trivial.

auto.

apply V_not_inter; trivial.

apply G_edge.
apply (X x0).
trivial.

red in |- *; intros; elim (H0 y0).
apply A_in_right; trivial.

trivial.

trivial.

rewrite H2 in v1; inversion v1.
elim (H0 y); inversion H3; apply A_in_left; apply E_right.

trivial.

rewrite H2 in v2; inversion v2.
elim (H0 x); inversion H3; apply A_in_left; apply E_left.

trivial.

trivial.

trivial.

trivial.

apply G_eq with (v := v'0) (a := a0).
trivial.

trivial.

apply (X x).
rewrite e; rewrite H2; apply V_in_left; apply V_in_single.

rewrite e0; trivial.

trivial.

rewrite e; trivial.
Qed.

Lemma A_union_single_inter :
 forall (x y x' y' : Vertex) (a a' : @A_set A),
 ~ a (A_ends x y) ->
 ~ a (A_ends y x) ->
 E_set x y <> E_set x' y' ->
 A_union (E_set x y) a = A_union (E_set x' y') a' ->
 A_union (E_set x y) (A_inter a a') = a'.
Proof.
        intros; repeat autounfold; rewrite A_distributivity_union_inter.
        fold (Union (@Arc A)) (@A_union A) (@A_inter A) in |- *; rewrite H2;
         repeat autounfold;
         rewrite (A_union_commut (E_set x y));
         rewrite (A_union_commut (E_set x' y'));
         rewrite <- A_distributivity_union_inter.
        fold (Union (@Arc A)) (@A_inter A). rewrite E_inter_empty.
        repeat autounfold; 
        rewrite A_union_commut; apply A_union_neutral.

        auto.
Qed.

Lemma G_minus_edge :
 forall (v : V_set) (a : A_set) (g : Graph v a) (x y : @Vertex A),
 a (A_ends x y) ->
 forall a' : A_set,
 ~ a' (A_ends x y) ->
 ~ a' (A_ends y x) -> a = A_union (E_set x y) a' -> Graph v a'.
Proof.
intros v a g; elim g.
unfold A_empty, Empty in |- *; tauto.

intros; apply G_vertex; eauto 2.

intros; case (E_set_eq_dec eq_a_dec x x0 y y0); intros.
apply G_eq with (v := v0) (a := a0).
trivial.

apply (A_union_inversion (E_set x y) a0 a').
apply E_set_disjoint; trivial.

rewrite e; apply E_set_disjoint; trivial.

rewrite <- e in H2; trivial.

trivial.

apply G_eq with (v := v0) (a := A_union (E_set x y) (A_inter a0 a')).
trivial.

apply A_union_single_inter with (x' := x0) (y' := y0); trivial.

apply G_edge.
apply (X x0 y0).
inversion H.
absurd (E_set x y = E_set x0 y0).
trivial.

inversion H3.
trivial.

apply E_set_eq.

trivial.

red in |- *; intros Ha; inversion Ha; elim H0; trivial.

red in |- *; intros Ha; inversion Ha; elim H1; trivial.

repeat autounfold.
rewrite A_inter_commut; symmetry  in |- *;
 apply A_union_single_inter with (x' := x) (y' := y).
trivial.

trivial.

auto.

auto.

trivial.

trivial.

trivial.

red in |- *; intros Ha; inversion Ha; elim n0; trivial.

red in |- *; intros Ha; inversion Ha; elim n1; trivial.

intros.
apply G_eq with (v := v0) (a := a'0).
trivial.

trivial.

apply (X x y).
rewrite e0; trivial.

trivial.

trivial.

rewrite e0; trivial.
Qed.

End INVERSION_GRAPH.

Implicit Arguments V_union_single_inter [A].
Implicit Arguments A_union_single_inter [A].
