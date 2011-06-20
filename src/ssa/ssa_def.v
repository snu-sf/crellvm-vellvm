(* generated by Ott 0.20.1 from: ssa_def.ott *)

Require Import Arith.
Require Import Bool.
Require Import List.
Require Import ListSet.
Require Import Logic_Type.
Require Import monad.
Require Import Metatheory.
Require Import ZArith.
Require Import Coqlib.
Require Import Floats.
Require Import alist.

Module LLVMsyntax.

Section Lists.

  Variable A : Type.

  Fixpoint last_opt (l:list A) {struct l} : option A := 
  match l with 
    | nil => None 
    | a :: nil => Some a 
    | a :: l' => last_opt l'
  end.

End Lists.

Require Import ZArith.

Module Size.

Definition t := nat.
Definition dec : forall x y : t, {x=y} + {x<>y} := eq_nat_dec.
Definition Zero : t := 0%nat.
Definition One : t := 1%nat.
Definition Two : t := 2%nat.
Definition Four : t := 4%nat.
Definition Eight : t := 8%nat.
Definition Sixteen : t := 16%nat.
Definition ThirtyTwo : t := 32%nat.
Definition SixtyFour : t := 64%nat.
Definition from_nat (i:nat) : t := i.
Definition to_nat (i:t) : nat := i.
Definition to_Z (i:t) : Z := Z_of_nat i.
Definition from_Z (i:Z) : t := nat_of_Z i.
Definition add (a b:t) : t := (a + b)%nat.
Definition sub (a b:t) : t := (a - b)%nat.
Definition mul (a b:t) : t := (a * b)%nat.
Definition div (a b:t) : t := nat_of_Z ((Z_of_nat a) / (Z_of_nat b)).
Definition gt (a b:t) : Prop := (a > b)%nat.
Definition lt (a b:t) : Prop := (a < b)%nat.

End Size.

Module Align.

Definition t := nat.
Definition dec : forall x y : t, {x=y} + {x<>y} := eq_nat_dec.
Definition Zero : t := 0%nat.
Definition One : t := 1%nat.
Definition Two : t := 2%nat.
Definition Four : t := 4%nat.
Definition Eight : t := 8%nat.
Definition Sixteen : t := 16%nat.
Definition ThirtyTwo : t := 32%nat.
Definition SixtyFour : t := 64%nat.
Definition from_nat (i:nat) : t := i.
Definition to_nat (i:t) : nat := i.
Definition to_Z (i:t) : Z := Z_of_nat i.
Definition from_Z (i:Z) : t := nat_of_Z i.
Definition add (a b:t) : t := (a + b)%nat.
Definition sub (a b:t) : t := (a - b)%nat.
Definition mul (a b:t) : t := (a * b)%nat.
Definition div (a b:t) : t := nat_of_Z ((Z_of_nat a) / (Z_of_nat b)).
Definition gt (a b:t) : Prop := (a > b)%nat.
Definition lt (a b:t) : Prop := (a < b)%nat.

End Align.

Module INTEGER.

Definition t := Z.
Definition dec : forall x y : t, {x=y} + {x<>y} := zeq.
Definition to_nat (i:t) : nat := nat_of_Z i.
Definition to_Z (i:t) : Z := i.
Definition of_Z (bitwidth:Z) (v:Z) (is_signed:bool) : t := v.

End INTEGER.

Module FLOAT.

Definition t := float.
Definition dec : forall x y : t, {x=y} + {x<>y} := Float.eq_dec.
(* Definition Zero : t := Float.zero. *)

End FLOAT.



Definition INT := INTEGER.t.

Definition Float := FLOAT.t.

Definition sz := Size.t.

Definition id := atom.

Definition l := atom.

Definition align := Align.t.

Definition i := nat.


Inductive floating_point : Set := 
 | fp_float : floating_point
 | fp_double : floating_point
 | fp_fp128 : floating_point
 | fp_x86_fp80 : floating_point
 | fp_ppc_fp128 : floating_point.

Definition varg : Set := bool.

Inductive typ : Set := 
 | typ_int : sz -> typ
 | typ_floatpoint : floating_point -> typ
 | typ_void : typ
 | typ_label : typ
 | typ_metadata : typ
 | typ_array : sz -> typ -> typ
 | typ_function : typ -> list_typ -> varg -> typ
 | typ_struct : list_typ -> typ
 | typ_pointer : typ -> typ
 | typ_opaque : typ
 | typ_namedt : id -> typ
with list_typ : Set := 
 | Nil_list_typ : list_typ
 | Cons_list_typ : typ -> list_typ -> list_typ.

Inductive cond : Set := 
 | cond_eq : cond
 | cond_ne : cond
 | cond_ugt : cond
 | cond_uge : cond
 | cond_ult : cond
 | cond_ule : cond
 | cond_sgt : cond
 | cond_sge : cond
 | cond_slt : cond
 | cond_sle : cond.

Inductive fcond : Set := 
 | fcond_false : fcond
 | fcond_oeq : fcond
 | fcond_ogt : fcond
 | fcond_oge : fcond
 | fcond_olt : fcond
 | fcond_ole : fcond
 | fcond_one : fcond
 | fcond_ord : fcond
 | fcond_ueq : fcond
 | fcond_ugt : fcond
 | fcond_uge : fcond
 | fcond_ult : fcond
 | fcond_ule : fcond
 | fcond_une : fcond
 | fcond_uno : fcond
 | fcond_true : fcond.

Inductive bop : Set := 
 | bop_add : bop
 | bop_sub : bop
 | bop_mul : bop
 | bop_udiv : bop
 | bop_sdiv : bop
 | bop_urem : bop
 | bop_srem : bop
 | bop_shl : bop
 | bop_lshr : bop
 | bop_ashr : bop
 | bop_and : bop
 | bop_or : bop
 | bop_xor : bop.

Inductive fbop : Set := 
 | fbop_fadd : fbop
 | fbop_fsub : fbop
 | fbop_fmul : fbop
 | fbop_fdiv : fbop
 | fbop_frem : fbop.

Inductive extop : Set := 
 | extop_z : extop
 | extop_s : extop
 | extop_fp : extop.

Inductive castop : Set := 
 | castop_fptoui : castop
 | castop_fptosi : castop
 | castop_uitofp : castop
 | castop_sitofp : castop
 | castop_ptrtoint : castop
 | castop_inttoptr : castop
 | castop_bitcast : castop.

Definition inbounds : Set := bool.

Inductive truncop : Set := 
 | truncop_int : truncop
 | truncop_fp : truncop.

Inductive const : Set := 
 | const_zeroinitializer : typ -> const
 | const_int : sz -> INT -> const
 | const_floatpoint : floating_point -> Float -> const
 | const_undef : typ -> const
 | const_null : typ -> const
 | const_arr : typ -> list_const -> const
 | const_struct : list_const -> const
 | const_gid : typ -> id -> const
 | const_truncop : truncop -> const -> typ -> const
 | const_extop : extop -> const -> typ -> const
 | const_castop : castop -> const -> typ -> const
 | const_gep : inbounds -> const -> list_const -> const
 | const_select : const -> const -> const -> const
 | const_icmp : cond -> const -> const -> const
 | const_fcmp : fcond -> const -> const -> const
 | const_extractvalue : const -> list_const -> const
 | const_insertvalue : const -> const -> list_const -> const
 | const_bop : bop -> const -> const -> const
 | const_fbop : fbop -> const -> const -> const
with list_const : Set := 
 | Nil_list_const : list_const
 | Cons_list_const : const -> list_const -> list_const.

Inductive value : Type := 
 | value_id : id -> value
 | value_const : const -> value.

Inductive attribute : Set := 
 | attribute_zext : attribute
 | attribute_sext : attribute
 | attribute_noreturn : attribute
 | attribute_inreg : attribute
 | attribute_structret : attribute
 | attribute_nounwind : attribute
 | attribute_noalias : attribute
 | attribute_byval : attribute
 | attribute_nest : attribute
 | attribute_readnone : attribute
 | attribute_readonly : attribute
 | attribute_noinline : attribute
 | attribute_alwaysinline : attribute
 | attribute_optforsize : attribute
 | attribute_stackprotect : attribute
 | attribute_stackprotectreq : attribute
 | attribute_nocapture : attribute
 | attribute_noredzone : attribute
 | attribute_implicitfloat : attribute
 | attribute_naked : attribute.

Definition param : Set := (prod typ value).

Definition tailc : Set := bool.

Definition attributes : Set := (list attribute).

Inductive callconv : Set := 
 | callconv_ccc : callconv
 | callconv_fast : callconv
 | callconv_cold : callconv
 | callconv_x86_stdcall : callconv
 | callconv_x86_fastcall : callconv.

Definition noret : Set := bool.

Definition params : Set := (list (typ*value)).

Inductive clattrs : Set := 
 | clattrs_intro : tailc -> callconv -> attributes -> attributes -> clattrs.

Inductive list_value : Set := 
 | Nil_list_value : list_value
 | Cons_list_value : value -> list_value -> list_value.

Inductive list_value_l : Set := 
 | Nil_list_value_l : list_value_l
 | Cons_list_value_l : value -> l -> list_value_l -> list_value_l.

Inductive cmd : Set := 
 | insn_bop : id -> bop -> sz -> value -> value -> cmd
 | insn_fbop : id -> fbop -> floating_point -> value -> value -> cmd
 | insn_extractvalue : id -> typ -> value -> list_const -> cmd
 | insn_insertvalue : id -> typ -> value -> typ -> value -> list_const -> cmd
 | insn_malloc : id -> typ -> value -> align -> cmd
 | insn_free : id -> typ -> value -> cmd
 | insn_alloca : id -> typ -> value -> align -> cmd
 | insn_load : id -> typ -> value -> align -> cmd
 | insn_store : id -> typ -> value -> value -> align -> cmd
 | insn_gep : id -> inbounds -> typ -> value -> list_value -> cmd
 | insn_trunc : id -> truncop -> typ -> value -> typ -> cmd
 | insn_ext : id -> extop -> typ -> value -> typ -> cmd
 | insn_cast : id -> castop -> typ -> value -> typ -> cmd
 | insn_icmp : id -> cond -> typ -> value -> value -> cmd
 | insn_fcmp : id -> fcond -> floating_point -> value -> value -> cmd
 | insn_select : id -> value -> typ -> value -> value -> cmd
 | insn_call : id -> noret -> clattrs -> typ -> value -> params -> cmd.

Inductive phinode : Set := 
 | insn_phi : id -> typ -> list_value_l -> phinode.

Definition arg : Set := (typ * attributes * id)%type.

Inductive visibility : Set := 
 | visibility_default : visibility
 | visibility_hidden : visibility
 | visibility_protected : visibility.

Inductive linkage : Set := 
 | linkage_external : linkage
 | linkage_available_externally : linkage
 | linkage_link_once : linkage
 | linkage_link_once_odr : linkage
 | linkage_weak : linkage
 | linkage_weak_odr : linkage
 | linkage_appending : linkage
 | linkage_internal : linkage
 | linkage_private : linkage
 | linkage_linker_private : linkage
 | linkage_dllimport : linkage
 | linkage_dllexport : linkage
 | linkage_external_weak : linkage
 | linkage_ghost : linkage
 | linkage_common : linkage.

Inductive terminator : Set := 
 | insn_return : id -> typ -> value -> terminator
 | insn_return_void : id -> terminator
 | insn_br : id -> value -> l -> l -> terminator
 | insn_br_uncond : id -> l -> terminator
 | insn_unreachable : id -> terminator.

Definition cmds : Set := (list cmd).

Definition phinodes : Set := (list phinode).

Definition args : Set := (list (typ*attributes*id)).

Inductive fnattrs : Set := 
 | fnattrs_intro : linkage -> visibility -> callconv -> attributes -> attributes -> fnattrs.

Inductive block : Set := 
 | block_intro : l -> phinodes -> cmds -> terminator -> block.

Inductive fheader : Set := 
 | fheader_intro : fnattrs -> typ -> id -> args -> varg -> fheader.

Definition blocks : Set := (list block).

Inductive gvar_spec : Set := 
 | gvar_spec_global : gvar_spec
 | gvar_spec_constant : gvar_spec.

Inductive fdec : Set := 
 | fdec_intro : fheader -> fdec.

Inductive fdef : Set := 
 | fdef_intro : fheader -> blocks -> fdef.

Inductive gvar : Set := 
 | gvar_intro : id -> linkage -> gvar_spec -> typ -> const -> align -> gvar
 | gvar_external : id -> gvar_spec -> typ -> gvar.

Inductive layout : Set := 
 | layout_be : layout
 | layout_le : layout
 | layout_ptr : sz -> align -> align -> layout
 | layout_int : sz -> align -> align -> layout
 | layout_float : sz -> align -> align -> layout
 | layout_aggr : sz -> align -> align -> layout
 | layout_stack : sz -> align -> align -> layout.

Inductive namedt : Set := 
 | namedt_intro : id -> typ -> namedt.

Inductive product : Set := 
 | product_gvar : gvar -> product
 | product_fdec : fdec -> product
 | product_fdef : fdef -> product.

Definition layouts : Set := (list layout).

Definition namedts : Set := (list namedt).

Definition products : Set := (list product).

Inductive module : Set := 
 | module_intro : layouts -> namedts -> products -> module.

Inductive insn : Set := 
 | insn_phinode : phinode -> insn
 | insn_cmd : cmd -> insn
 | insn_terminator : terminator -> insn.

Definition modules : Set := (list module).

Definition ids : Set := (list id).

Definition opt_INT : Set := option INT.

Definition opt_l : Set := option l.

Definition opt_id : Set := option id.

Definition opt_typ : Set := option typ.

Definition opt_value : Set := option value.

Definition ls : Set := (list l).

Definition insns : Set := (list insn).

Definition opt_block : Set := option block.

Definition opt_fdec : Set := option fdec.

Definition opt_fdef : Set := option fdef.

Inductive id_binding : Set := 
 | id_binding_none : id_binding
 | id_binding_cmd : cmd -> id_binding
 | id_binding_phinode : phinode -> id_binding
 | id_binding_terminator : terminator -> id_binding
 | id_binding_gvar : gvar -> id_binding
 | id_binding_fdec : fdec -> id_binding
 | id_binding_arg : arg -> id_binding.

Definition targetdata : Set := (prod (list layout) (list namedt)).

Definition system : Set := modules.

Definition usedef_block : Type := AssocList (list l).

Definition intrinsic_funs : Set := ids.

Fixpoint map_list_value_l (A:Set) (f:value->l->A) (l0:list_value_l) {struct l0} : list A :=
  match l0 with
  | Nil_list_value_l => nil
  | Cons_list_value_l h0 h1 tl_ => cons (f h0 h1) (map_list_value_l A f tl_)
  end.
Implicit Arguments map_list_value_l.

Fixpoint make_list_value_l (l0:list (value*l)) : list_value_l :=
  match l0 with
  | nil  => Nil_list_value_l
  | cons (h0,h1) tl_ => Cons_list_value_l h0 h1 (make_list_value_l tl_)
  end.

Fixpoint unmake_list_value_l (l0:list_value_l) :  list (value*l) :=
  match l0 with
  | Nil_list_value_l => nil
  | Cons_list_value_l h0 h1 tl_ =>  cons (h0,h1) (unmake_list_value_l tl_)
  end.

Fixpoint nth_list_value_l (n:nat) (l0:list_value_l) {struct n} : option (value*l) :=
  match n,l0 with
  | O, Cons_list_value_l h0 h1 tl_ => Some (h0,h1) 
  | O, other => None
  | S m, Nil_list_value_l => None
  | S m, Cons_list_value_l h0 h1 tl_ => nth_list_value_l m tl_
  end.
Implicit Arguments nth_list_value_l.

Fixpoint app_list_value_l (l0 m:list_value_l) {struct l0} : list_value_l :=
  match l0 with
  | Nil_list_value_l => m
  | Cons_list_value_l h0 h1 tl_ => Cons_list_value_l h0 h1 (app_list_value_l tl_ m)
  end.


Fixpoint map_list_value (A:Set) (f:value->A) (l0:list_value) {struct l0} : list A :=
  match l0 with
  | Nil_list_value => nil
  | Cons_list_value h tl_ => cons (f h) (map_list_value A f tl_)
  end.
Implicit Arguments map_list_value.

Fixpoint make_list_value (l0:list value) : list_value :=
  match l0 with
  | nil  => Nil_list_value
  | cons h tl_ => Cons_list_value h (make_list_value tl_)
  end.

Fixpoint unmake_list_value (l0:list_value) :  list value :=
  match l0 with
  | Nil_list_value => nil
  | Cons_list_value h tl_ =>  cons h (unmake_list_value tl_)
  end.

Fixpoint nth_list_value (n:nat) (l0:list_value) {struct n} : option value :=
  match n,l0 with
  | O, Cons_list_value h tl_ => Some h 
  | O, other => None
  | S m, Nil_list_value => None
  | S m, Cons_list_value h tl_ => nth_list_value m tl_
  end.
Implicit Arguments nth_list_value.

Fixpoint app_list_value (l0 m:list_value) {struct l0} : list_value :=
  match l0 with
  | Nil_list_value => m
  | Cons_list_value h tl_ => Cons_list_value h (app_list_value tl_ m)
  end.


Fixpoint map_list_const (A:Set) (f:const->A) (l0:list_const) {struct l0} : list A :=
  match l0 with
  | Nil_list_const => nil
  | Cons_list_const h tl_ => cons (f h) (map_list_const A f tl_)
  end.
Implicit Arguments map_list_const.

Fixpoint make_list_const (l0:list const) : list_const :=
  match l0 with
  | nil  => Nil_list_const
  | cons h tl_ => Cons_list_const h (make_list_const tl_)
  end.

Fixpoint unmake_list_const (l0:list_const) :  list const :=
  match l0 with
  | Nil_list_const => nil
  | Cons_list_const h tl_ =>  cons h (unmake_list_const tl_)
  end.

Fixpoint nth_list_const (n:nat) (l0:list_const) {struct n} : option const :=
  match n,l0 with
  | O, Cons_list_const h tl_ => Some h 
  | O, other => None
  | S m, Nil_list_const => None
  | S m, Cons_list_const h tl_ => nth_list_const m tl_
  end.
Implicit Arguments nth_list_const.

Fixpoint app_list_const (l0 m:list_const) {struct l0} : list_const :=
  match l0 with
  | Nil_list_const => m
  | Cons_list_const h tl_ => Cons_list_const h (app_list_const tl_ m)
  end.


Fixpoint map_list_typ (A:Set) (f:typ->A) (l0:list_typ) {struct l0} : list A :=
  match l0 with
  | Nil_list_typ => nil
  | Cons_list_typ h tl_ => cons (f h) (map_list_typ A f tl_)
  end.
Implicit Arguments map_list_typ.

Fixpoint make_list_typ (l0:list typ) : list_typ :=
  match l0 with
  | nil  => Nil_list_typ
  | cons h tl_ => Cons_list_typ h (make_list_typ tl_)
  end.

Fixpoint unmake_list_typ (l0:list_typ) :  list typ :=
  match l0 with
  | Nil_list_typ => nil
  | Cons_list_typ h tl_ =>  cons h (unmake_list_typ tl_)
  end.

Fixpoint nth_list_typ (n:nat) (l0:list_typ) {struct n} : option typ :=
  match n,l0 with
  | O, Cons_list_typ h tl_ => Some h 
  | O, other => None
  | S m, Nil_list_typ => None
  | S m, Cons_list_typ h tl_ => nth_list_typ m tl_
  end.
Implicit Arguments nth_list_typ.

Fixpoint app_list_typ (l0 m:list_typ) {struct l0} : list_typ :=
  match l0 with
  | Nil_list_typ => m
  | Cons_list_typ h tl_ => Cons_list_typ h (app_list_typ tl_ m)
  end.




Tactic Notation "cmd_cases" tactic(first) tactic(c) :=
  first;
  [ c "insn_bop" | c "insn_fbop" |
    c "insn_extractvalue" | c "insn_insertvalue" |
    c "insn_malloc" | c "insn_free" |
    c "insn_alloca" | c "insn_load" | c "insn_store" | c "insn_gep" |
    c "insn_trunc" | c "insn_ext" | c "insn_cast" | 
    c "insn_icmp" | c "insn_fcmp" | c "insn_select" |
    c "insn_call" ].

Tactic Notation "product_cases" tactic(first) tactic(c) :=
  first;
  [ c "product_gvar" | c "product_fdec" | c "product_fdef" ].

Scheme const_rec2 := Induction for const Sort Set
  with list_const_rec2 := Induction for list_const Sort Set.

Definition const_mutrec P P' :=
  fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21=>
      (pair (@const_rec2 P P' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21)
            (@list_const_rec2 P P' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21)).

Scheme typ_rec2 := Induction for typ Sort Set
  with list_typ_rec2 := Induction for list_typ Sort Set.

Definition typ_mutrec P P' :=
  fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 =>
      (pair (@typ_rec2 P P' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13)
            (@list_typ_rec2 P P' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13)).

Scheme const_ind2 := Induction for const Sort Prop
  with list_const_ind2 := Induction for list_const Sort Prop.

Combined Scheme const_mutind from const_ind2, list_const_ind2.

Scheme typ_ind2 := Induction for typ Sort Prop
  with list_typ_ind2 := Induction for list_typ Sort Prop.

Combined Scheme typ_mutind from typ_ind2, list_typ_ind2.


End LLVMsyntax.



(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)


