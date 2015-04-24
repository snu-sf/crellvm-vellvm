Require Import Ensembles.
Require Import syntax.
Require Import infrastructure.
Require Import List.
Require Import Arith.
Require Import monad.
Require Import Metatheory.
Require Import genericvalues.
Require Import alist.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import targetdata.
Require Import infrastructure_props.
Require Import typings.
Require Import events.
Require Import external_intrinsics.
Require Import genericvalues_inject.

(*************************************************************)
(* The operational semantics of Vellvm                       *)

Import LLVMsyntax.
Import LLVMtd.
Import LLVMinfra.
Import LLVMgv.
Import LLVMtypings.

(* GenericValues represent dynamic values at runtime. We provide
   different styles of semantics that have different definitions of
   dynamic values. The following defines their signatures. *)
Structure GenericValues := mkGVs {
(* The type of GenericValues *)
GVsT : Type;
(* instantiate_gvs gv gvs ensures that gvs includes gv. *) 
instantiate_gvs : GenericValue -> GVsT -> Prop;
(* inhabited gvs ensures that gvs is not empty. *)
inhabited : GVsT -> Prop;
(* cgv2gvs cgv t converts the constant cgv to GenericValues w.r.t type t. *)
cgv2gvs : GenericValue -> typ -> GVsT;
(* gv2gvs gv t converts gv to GenericValues in terms of type t. *)
gv2gvs : GenericValue -> typ -> GVsT;
(* f is a unary operation of gv, lift_op1 f returns a unary operation of 
   GenericValues. *)
lift_op1 : (GenericValue -> option GenericValue) -> GVsT -> typ -> option GVsT;
(* f is a binary operation of gv, lift_op2 f returns a binary operation of 
   GenericValues. *)
lift_op2 : (GenericValue -> GenericValue -> option GenericValue) ->
  GVsT -> GVsT -> typ -> option GVsT;
(* All values in (cgv2gvs cgv t) are of type size t, match type t, and non-empty.
 *)
cgv2gvs__getTypeSizeInBits : forall S los nts gv t sz al gv',
  wf_typ S (los,nts) t ->
  _getTypeSizeInBits_and_Alignment los
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t =
      Some (sz, al) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv ->
  instantiate_gvs gv' (cgv2gvs gv t) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) =
    sizeGenericValue gv';

cgv2gvs__matches_chunks : forall S los nts gv t gv',
  wf_typ S (los,nts) t ->
  gv_chunks_match_typ (los, nts) gv t ->
  instantiate_gvs gv' (cgv2gvs gv t) ->
  gv_chunks_match_typ (los, nts) gv' t;

cgv2gvs__inhabited : forall gv t, inhabited (cgv2gvs gv t);
(* All values in (gv2gvs gv t) are of type size t, match type t, and non-empty.
 *)
gv2gvs__getTypeSizeInBits : forall S los nts gv t sz al,
  wf_typ S (los,nts) t ->
  _getTypeSizeInBits_and_Alignment los
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t =
      Some (sz, al) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv ->
  forall gv', instantiate_gvs gv' (gv2gvs gv t) ->
  sizeGenericValue gv' = Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8);

gv2gvs__matches_chunks : forall S los nts gv t,
  wf_typ S (los,nts) t ->
  gv_chunks_match_typ (los, nts) gv t ->
  forall gv', instantiate_gvs gv' (gv2gvs gv t) ->
  gv_chunks_match_typ (los, nts) gv' t;

gv2gvs__inhabited : forall gv t, inhabited (gv2gvs gv t);
(* lift_op1 and lift_op2 preserve inhabitedness, totalness, type size, and 
   chunks. *)
lift_op1__inhabited : forall f gvs1 t gvs2
  (H:forall x, exists z, f x = Some z),
  inhabited gvs1 ->
  lift_op1 f gvs1 t = Some gvs2 ->
  inhabited gvs2;

lift_op2__inhabited : forall f gvs1 gvs2 t gvs3
  (H:forall x y, exists z, f x y = Some z),
  inhabited gvs1 -> inhabited gvs2 ->
  lift_op2 f gvs1 gvs2 t = Some gvs3 ->
  inhabited gvs3;

lift_op1__isnt_stuck : forall f gvs1 t
  (H:forall x, exists z, f x = Some z),
  exists gvs2, lift_op1 f gvs1 t = Some gvs2;

lift_op2__isnt_stuck : forall f gvs1 gvs2 t
  (H:forall x y, exists z, f x y = Some z),
  exists gvs3, lift_op2 f gvs1 gvs2 t = Some gvs3;

lift_op1__getTypeSizeInBits : forall S los nts f g t sz al gvs,
  wf_typ S (los,nts) t ->
  _getTypeSizeInBits_and_Alignment los
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t =
      Some (sz, al) ->
  (forall x y, instantiate_gvs x g -> f x = Some y ->
   sizeGenericValue y = nat_of_Z (ZRdiv (Z_of_nat sz) 8)) ->
  lift_op1 f g t = Some gvs ->
  forall gv : GenericValue,
  instantiate_gvs gv gvs ->
  sizeGenericValue gv = nat_of_Z (ZRdiv (Z_of_nat sz) 8);

lift_op2__getTypeSizeInBits : forall S los nts f g1 g2 t sz al gvs,
  wf_typ S (los,nts) t ->
  _getTypeSizeInBits_and_Alignment los
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t =
      Some (sz, al) ->
  (forall x y z,
   instantiate_gvs x g1 -> instantiate_gvs y g2 -> f x y = Some z ->
   sizeGenericValue z = nat_of_Z (ZRdiv (Z_of_nat sz) 8)) ->
  lift_op2 f g1 g2 t = Some gvs ->
  forall gv : GenericValue,
  instantiate_gvs gv gvs ->
  sizeGenericValue gv = nat_of_Z (ZRdiv (Z_of_nat sz) 8);

lift_op1__matches_chunks : forall S los nts f g t gvs,
  wf_typ S (los,nts) t ->
  (forall x y, instantiate_gvs x g -> f x = Some y ->
   gv_chunks_match_typ (los, nts) y t) ->
  lift_op1 f g t = Some gvs ->
  forall gv : GenericValue,
  instantiate_gvs gv gvs ->
  gv_chunks_match_typ (los, nts) gv t;

lift_op2__matches_chunks : forall S los nts f g1 g2 t gvs,
  wf_typ S (los,nts) t ->
  (forall x y z,
   instantiate_gvs x g1 -> instantiate_gvs y g2 -> f x y = Some z ->
   gv_chunks_match_typ (los, nts) z t) ->
  lift_op2 f g1 g2 t = Some gvs ->
  forall gv : GenericValue,
  instantiate_gvs gv gvs ->
  gv_chunks_match_typ (los, nts) gv t;
(* Inhabited values are not empty. *)
inhabited_inv : forall gvs, inhabited gvs -> exists gv, instantiate_gvs gv gvs;
(* gv is in (gv2gvs gv t). *)
instantiate_gv__gv2gvs : forall gv t, instantiate_gvs gv (gv2gvs gv t);
(* If gv's is not undefined, (gv2gvs gv' t) only includes gv'. *)
none_undef2gvs_inv : forall gv gv' t,
  instantiate_gvs gv (gv2gvs gv' t) -> (forall mc, (Vundef, mc)::nil <> gv') ->
  gv = gv'
}.

Global Opaque GVsT gv2gvs instantiate_gvs inhabited cgv2gvs lift_op1 lift_op2.

Module OpsemAux.

(**************************************)
(* This module defines configuration of semantics. A configuration includes
   the invariants and parameters of semantics. *)

(* The configuration for small-step semantics. *)
Record Config : Type := mkCfg {
CurSystem          : system;        (* programs *)
CurTargetData      : TargetData;    (* data layouts of the current program *)
CurProducts        : list product;  (* the currenr program *)
Globals            : GVMap;         (* globals *)
(* FunTable maps function names to their addresses that are taken as function
   pointers. When we are calling a function via an id, we first search in Globals
   via the value id to get its address, and then search in FunTable to get its
   name, via the name, we search in CurProducts to get its definition.

   We assume that there is an 'initFunTable' that returns function addresses to
   initialize FunTable
*)
FunTable           : GVMap 
}.

(* The configuration for big-step semantics. *)
Record bConfig : Type := mkbCfg {
bCurSystem          : system;
bCurTargetData      : TargetData;
bCurProducts        : list product;
bGlobals            : GVMap;
bFunTable           : GVMap;
bCurFunction        : fdef
}.

(* Find the name mapped to fptr from the function table fs. 

   To realize it in LLVM, we can try to dynamically cast fptr to Function*,
   if failed, return None
   if successeful, we can return this function's name *)
Fixpoint lookupFdefViaGVFromFunTable (fs:GVMap)(fptr:GenericValue): option id :=
match fs with
| nil => None
| (id0,gv0)::fs' =>
  if eq_gv gv0 fptr
  then Some id0
  else lookupFdefViaGVFromFunTable fs' fptr
end.

(* Find the function definition. *)
Definition lookupFdefViaPtr (Ps:products) (fs:GVMap) fptr : option fdef :=
  do fn <- lookupFdefViaGVFromFunTable fs fptr;
     lookupFdefViaIDFromProducts Ps fn.

(* Find the function declaration of external functions. *)
Definition lookupExFdecViaPtr (Ps:products) (fs:GVMap) fptr : option fdec :=
do fn <- lookupFdefViaGVFromFunTable fs fptr;
    match lookupFdefViaIDFromProducts Ps fn with
    | Some _ => None
    | None => lookupFdecViaIDFromProducts Ps fn
    end
.

(* Initalize a global with name id0, type t, initial value c, and alignment 
   align0. *)
Definition initGlobal (TD:TargetData)(gl:GVMap)(Mem:mem)(id0:id)(t:typ)(c:const)
  (align0:align) : option (GenericValue*mem) :=
  do tsz <- getTypeAllocSize TD t;
  do gv <- LLVMgv.const2GV TD gl c;
     match (malloc_one TD Mem (Size.from_nat tsz) align0) with
     | Some (Mem', mb) =>
       do Mem'' <- mstore TD Mem' (blk2GV TD mb) t gv align0;
       ret (blk2GV TD mb,  Mem'')
     | None => None
     end.

(* Initialize targetdata. Mem is used when extraction. *)
Definition initTargetData (los:layouts)(nts:namedts)(Mem:mem) : TargetData :=
  (los, nts).

(* Return the memory location of external functions. *)
Axiom getExternalGlobal : mem -> id -> option GenericValue.

(* For each function id, the runtime emits an address as a function pointer.
   It can be realized by taking Function* in LLVM as the address. *)
Axiom initFunTable : mem -> id -> option GenericValue.

(* Initialized globals and function tables in terms of the definitions in the 
   program Ps. *)
Fixpoint genGlobalAndInitMem (TD:TargetData)(Ps:list product)(gl:GVMap)(fs:GVMap)
  (Mem:mem) : option (GVMap*GVMap*mem) :=
match Ps with
| nil => Some (gl, fs, Mem)
| (product_gvar (gvar_intro id0 _ spec t c align))::Ps' =>
  match (initGlobal TD gl Mem id0 t c align) with
  | Some (gv, Mem') =>
      genGlobalAndInitMem TD Ps' (updateAddAL _ gl id0 gv) fs Mem'
  | None => None
  end
| (product_gvar (gvar_external id0 spec t))::Ps' =>
  match (getExternalGlobal Mem id0) with
  | Some gv => genGlobalAndInitMem TD Ps' (updateAddAL _ gl id0 gv) fs Mem
  | None => None
  end
| (product_fdef (fdef_intro (fheader_intro _ _ id0 _ _) _))::Ps' =>
  match initFunTable Mem id0 with
  | Some gv => genGlobalAndInitMem TD Ps' (updateAddAL _ gl id0 gv)
      (updateAddAL _ fs id0 gv) Mem
  | None => None
  end
| (product_fdec (fdec_intro (fheader_intro _ _ id0 _ _) _))::Ps' =>
  match initFunTable Mem id0 with
  | Some gv => genGlobalAndInitMem TD Ps' (updateAddAL _ gl id0 gv)
      (updateAddAL _ fs id0 gv) Mem
  | None => None
  end
end.

(* Properties of lookupFdefViaPtr. *)
Lemma lookupFdefViaPtr_inversion : forall Ps fs fptr f,
  lookupFdefViaPtr Ps fs fptr = Some f ->
  exists fn,
    lookupFdefViaGVFromFunTable fs fptr = Some fn /\
    lookupFdefViaIDFromProducts Ps fn = Some f.
Proof.
  intros.
  unfold lookupFdefViaPtr in H.
  destruct (lookupFdefViaGVFromFunTable fs fptr); tinv H.
  simpl in H. exists i0. eauto.
Qed.

Lemma lookupFdefViaPtr_inv : forall Ps fs fv F,
  lookupFdefViaPtr Ps fs fv = Some F ->
  InProductsB (product_fdef F) Ps.
Proof.
  intros.
  unfold lookupFdefViaPtr in H.
  destruct (lookupFdefViaGVFromFunTable fs fv); try solve [inversion H].
  apply lookupFdefViaIDFromProducts_inv in H; auto.
Qed.

Lemma lookupFdefViaPtr_uniq : forall los nts Ps fs S fptr F,
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  lookupFdefViaPtr Ps fs fptr = Some F ->
  uniqFdef F.
Proof.
  intros.
  apply lookupFdefViaPtr_inversion in H1.
  destruct H1 as [fn [J1 J2]].
  apply lookupFdefViaIDFromProducts_inv in J2; auto.
  apply uniqSystem__uniqProducts in H0; auto.
  eapply uniqProducts__uniqFdef; simpl; eauto.
Qed.

Lemma lookupFdefViaPtrInSystem : forall los nts Ps fs S fv F,
  moduleInSystem (module_intro los nts Ps) S ->
  lookupFdefViaPtr Ps fs fv = Some F ->
  productInSystemModuleB (product_fdef F) S (module_intro los nts Ps).
Proof.
  intros.
  apply lookupFdefViaPtr_inversion in H0.
  destruct H0 as [fn [J1 J2]].
  apply lookupFdefViaIDFromProducts_inv in J2.
  apply productInSystemModuleB_intro; auto.
Qed.

Lemma entryBlockInSystemBlockFdef'' : forall los nts Ps fs fv F S B,
  moduleInSystem (module_intro los nts Ps) S ->
  lookupFdefViaPtr Ps fs fv = Some F ->
  getEntryBlock F = Some B ->
  blockInSystemModuleFdef B S (module_intro los nts Ps) F.
Proof.
  intros.
  apply lookupFdefViaPtr_inversion in H0.
  destruct H0 as [fn [J1 J2]].
  apply lookupFdefViaIDFromProducts_inv in J2.
  apply entryBlockInFdef in H1.
  apply blockInSystemModuleFdef_intro; auto.
Qed.

(* Properties of lookupExFdecViaPtr. *)
Lemma lookupExFdecViaPtr_inversion : forall Ps fs fptr f,
  lookupExFdecViaPtr Ps fs fptr = Some f ->
  exists fn,
    lookupFdefViaGVFromFunTable fs fptr = Some fn /\
    lookupFdefViaIDFromProducts Ps fn = None /\
    lookupFdecViaIDFromProducts Ps fn = Some f.
Proof.
  intros.
  unfold lookupExFdecViaPtr in H.
  destruct (lookupFdefViaGVFromFunTable fs fptr); tinv H.
  simpl in H. exists i0.
  destruct (lookupFdefViaIDFromProducts Ps i0); inv H; auto.
Qed.

(* Simulation of function tables. *)
Definition ftable_simulation mi fs1 fs2 : Prop :=
  forall fv1 fv2, gv_inject mi fv1 fv2 ->
    lookupFdefViaGVFromFunTable fs1 fv1 =
    lookupFdefViaGVFromFunTable fs2 fv2.

(* Assume memory extension preserves function table simulation. *)
Axiom inject_incr__preserves__ftable_simulation: forall mi mi' fs1 fs2,
  ftable_simulation mi fs1 fs2 ->
  inject_incr mi mi' ->
  ftable_simulation mi' fs1 fs2.

End OpsemAux.

(************** Operational semantics *************************************** ***)

Module Opsem.

Export LLVMsyntax.
Export LLVMtd.
Export LLVMinfra.
Export LLVMgv.
Export LLVMtypings.
Export OpsemAux.

Section Opsem.

Context `{GVsSig : GenericValues}.

Notation GVs := GVsSig.(GVsT).
Definition GVsMap := list (id * GVs).
Notation "gv @ gvs" :=
  (GVsSig.(instantiate_gvs) gv gvs) (at level 43, right associativity).
Notation "$ gv # t $" := (GVsSig.(gv2gvs) gv t) (at level 41).

Definition in_list_gvs (l1 : list GenericValue) (l2 : list GVs) : Prop :=
List.Forall2 GVsSig.(instantiate_gvs) l1 l2.

Notation "vidxs @@ vidxss" := (in_list_gvs vidxs vidxss)
  (at level 43, right associativity).

(* Compute the semantic value of a constant. *)
Definition const2GV (TD:TargetData) (gl:GVMap) (c:const) : option GVs :=
match (_const2GV TD gl c) with
| None => None
| Some (gv, ty) => Some (GVsSig.(cgv2gvs) gv ty)
end.

(* Compute the semantic value of a program value. *)
Definition getOperandValue (TD:TargetData) (v:value) (locals:GVsMap)
  (globals:GVMap) : option GVs :=
match v with
| value_id id => lookupAL _ locals id
| value_const c => const2GV TD globals c
end.

(**************************************)
(** Execution contexts *)

(* Frames *)
Record ExecutionContext : Type := mkEC {
CurFunction : fdef;                  (* the current function *)
CurBB       : block;                 (* the current block in CurFunction *)
CurCmds     : cmds;                  (* cmds to run within CurBB *)
Terminator  : terminator;            (* the terminator of CurBB *)
Locals      : GVsMap;                (* LLVM values used in this invocation *)
Allocas     : list mblock            (* Track memory allocated by alloca *)
}.
(* Stacks *)
Definition ECStack := list ExecutionContext.
(* Program states *)
Record State : Type := mkState {
EC                 : ExecutionContext;
ECS                : ECStack;
Mem                : mem
}.

(* When a program jumps from the block b to a block with phinodes PNs, the
  function computes the definitions of PNs. *)
Fixpoint getIncomingValuesForBlockFromPHINodes (TD:TargetData)
  (PNs:list phinode) (b:block) (globals:GVMap) (locals:GVsMap) :
  option (list (id*GVs)) :=
match PNs with
| nil => Some nil
| (insn_phi id0 t vls)::PNs =>
  match (getValueViaBlockFromPHINode (insn_phi id0 t vls) b) with
  | None => None
  | Some v =>
      match (getOperandValue TD v locals globals,
             getIncomingValuesForBlockFromPHINodes TD PNs b globals locals)
      with
      | (Some gv1, Some idgvs) => Some ((id0,gv1)::idgvs)
      | _ => None
      end
  end
end.

(* Update locals in terms of the mapping ResultValues. *)
Fixpoint updateValuesForNewBlock (ResultValues:list (id*GVs)) (locals:GVsMap)
  : GVsMap :=
match ResultValues with
| nil => locals
| (id, v)::ResultValues' =>
    updateAddAL _ (updateValuesForNewBlock ResultValues' locals) id v
end.

(* When a program jumps from the block PrevBB to the block Dest, the function 
   updates locals. *)
Definition switchToNewBasicBlock (TD:TargetData) (Dest:block)
  (PrevBB:block) (globals: GVMap) (locals:GVsMap): option GVsMap :=
  let PNs := getPHINodesFromBlock Dest in
  match getIncomingValuesForBlockFromPHINodes TD PNs PrevBB globals locals with
  | Some ResultValues => Some (updateValuesForNewBlock ResultValues locals)
  | None => None
  end.

(* When a program calls a function with parameters lp, the following computes the
   runtime values of lp. *)
Fixpoint params2GVs (TD:TargetData) (lp:params) (locals:GVsMap) (globals:GVMap) :
 option (list GVs) :=
match lp with
| nil => Some nil
| (_, v)::lp' =>
    match (getOperandValue TD v locals globals,
           params2GVs TD lp' locals globals) with
    | (Some gv, Some gvs) => Some (gv::gvs)
    | _ => None
    end
end.

(* oResult is the value returned by a external function. rid is the variable
   that stores the return value. The following updates locals in terms of the
   type rt of the return value, and noret (whether the function returns). *)
Definition exCallUpdateLocals TD (rt:typ) (noret:bool) (rid:id)
  (oResult:option GenericValue) (lc :GVsMap) : option GVsMap :=
  match noret with
  | false =>
      match oResult with
      | None => None
      | Some Result =>
            match fit_gv TD rt Result with
            | Some gr => Some (updateAddAL _ lc rid ($ gr # rt $))
            | _ => None
            end
      end
  | true => Some lc
  end.

(* c' must be a call of a function that returns Result.
   lc is the local of the callee's function, and lc' is the local of
   the caller's function. The following updates lc'. *)
Definition returnUpdateLocals (TD:TargetData) (c':cmd) (Result:value)
  (lc lc':GVsMap) (gl:GVMap) : option GVsMap :=
  match (getOperandValue TD Result lc gl) with
  | Some gr =>
      match c' with
      | insn_call id0 false _ ct _ _ _ =>
           match (GVsSig.(lift_op1) (fit_gv TD ct) gr ct) with
           | Some gr' => Some (updateAddAL _ lc' id0 gr')
           | _ => None
           end
      | insn_call _ _ _ _ _ _ _ => Some lc'
      | _=> None
      end
  | None => None
  end.

(* Convert the list of values of GEP into runtime values. *)
Fixpoint values2GVs (TD:TargetData) (lv:list (sz * value)) (locals:GVsMap)
  (globals:GVMap) : option (list GVs):=
match lv with
| nil => Some nil
| (_, v) :: lv' =>
  match (getOperandValue TD v locals globals) with
  | Some GV =>
    match (values2GVs TD lv' locals globals) with
    | Some GVs => Some (GV::GVs)
    | None => None
    end
  | None => None
  end
end.

(* When a program calls a function with arguments la and the correponding runtime
   values lg, the following computes the initial locals of the function. 
   When la and lg do not match, for example, calling a function with the wrong
   signature, it returns none.
*)
Fixpoint _initializeFrameValues TD (la:args) (lg:list GVs) (locals:GVsMap)
  : option GVsMap :=
match (la, lg) with
| (((t, _), id)::la', g::lg') =>
  match _initializeFrameValues TD la' lg' locals,
        GVsSig.(lift_op1) (fit_gv TD t) g t with
  | Some lc', Some gv => Some (updateAddAL _ lc' id gv)
  | _, _ => None
  end
| (((t, _), id)::la', nil) =>
  (* FIXME: We should initalize them w.r.t their type size. *)
  match _initializeFrameValues TD la' nil locals, gundef TD t with
  | Some lc', Some gv => Some (updateAddAL _ lc' id ($ gv # t $))
  | _, _ => None
  end
| _ => Some locals
end.

Definition initLocals TD (la:args) (lg:list GVs): option GVsMap :=
_initializeFrameValues TD la lg nil.

(* Operations *)
Definition BOP (TD:TargetData) (lc:GVsMap) (gl:GVMap) (op:bop) (bsz:sz)
  (v1 v2:value) : option GVs :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gvs1, Some gvs2) =>
    GVsSig.(lift_op2) (mbop TD op bsz) gvs1 gvs2 (typ_int bsz)
| _ => None
end
.

Definition FBOP (TD:TargetData) (lc:GVsMap) (gl:GVMap) (op:fbop) fp
  (v1 v2:value) : option GVs :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gvs1, Some gvs2) =>
    GVsSig.(lift_op2) (mfbop TD op fp) gvs1 gvs2 (typ_floatpoint fp)
| _ => None
end
.

Definition ICMP (TD:TargetData) (lc:GVsMap) (gl:GVMap) c t (v1 v2:value)
  : option GVs :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gvs1, Some gvs2) =>
    GVsSig.(lift_op2) (micmp TD c t) gvs1 gvs2 (typ_int Size.One)
| _ => None
end
.

Definition FCMP (TD:TargetData) (lc:GVsMap) (gl:GVMap) c fp (v1 v2:value)
  : option GVs :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gvs1, Some gvs2) =>
    GVsSig.(lift_op2) (mfcmp TD c fp) gvs1 gvs2 (typ_int Size.One)
| _ => None
end
.

Definition CAST (TD:TargetData) (lc:GVsMap) (gl:GVMap) (op:castop)
  (t1:typ) (v1:value) (t2:typ) : option GVs:=
match (getOperandValue TD v1 lc gl) with
| (Some gvs1) => GVsSig.(lift_op1) (mcast TD op t1 t2) gvs1 t2
| _ => None
end
.

Definition TRUNC (TD:TargetData) (lc:GVsMap) (gl:GVMap) (op:truncop)
  (t1:typ) (v1:value) (t2:typ) : option GVs:=
match (getOperandValue TD v1 lc gl) with
| (Some gvs1) => GVsSig.(lift_op1) (mtrunc TD op t1 t2) gvs1 t2
| _ => None
end
.

Definition EXT (TD:TargetData) (lc:GVsMap) (gl:GVMap) (op:extop)
  (t1:typ) (v1:value) (t2:typ) : option GVs:=
match (getOperandValue TD v1 lc gl) with
| (Some gvs1) => GVsSig.(lift_op1) (mext TD op t1 t2) gvs1 t2
| _ => None
end
.

Definition GEP (TD:TargetData) (ty:typ) (mas:GVs) (vidxs:list GenericValue)
  (inbounds:bool) ty' : option GVs :=
GVsSig.(lift_op1) (gep TD ty vidxs inbounds ty') mas (typ_pointer ty').

Definition extractGenericValue (TD:TargetData) (t:typ) (gvs : GVs)
  (cidxs : list const) : option GVs :=
match (intConsts2Nats TD cidxs) with
| None => None
| Some idxs =>
  match (mgetoffset TD t idxs) with
  | Some (o, t') => GVsSig.(lift_op1) (mget' TD o t') gvs t'
  | None => None
  end
end.

Definition insertGenericValue (TD:TargetData) (t:typ) (gvs:GVs)
  (cidxs:list const) (t0:typ) (gvs0:GVs) : option GVs :=
match (intConsts2Nats TD cidxs) with
| None => None
| Some idxs =>
  match (mgetoffset TD t idxs) with
  | Some (o, _) => GVsSig.(lift_op2) (mset' TD o t t0) gvs gvs0 t
  | None => None
  end
end.

(***************************************************************)
(* small-step *)

Inductive sInsn : Config -> State -> State -> trace -> Prop :=
| sReturn : forall S TD Ps F B rid RetTy Result lc gl fs
                            F' B' c' cs' tmn' lc' ECS
                            Mem Mem' als als' lc'',
  Instruction.isCallInst c' = true ->
  (* FIXME: we should get Result before free?! *)
  free_allocas TD Mem als = Some Mem' ->
  returnUpdateLocals TD c' Result lc lc' gl = Some lc'' ->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState (mkEC F B nil (insn_return rid RetTy Result) lc als)
              ((mkEC F' B' (c'::cs') tmn' lc' als')::ECS) Mem)
    (mkState (mkEC F' B' cs' tmn' lc'' als') (ECS) Mem')
    E0

| sReturnVoid : forall S TD Ps F B rid lc gl fs
                            F' B' c' tmn' lc' ECS 
                            cs' Mem Mem' als als',
  Instruction.isCallInst c' = true ->
  free_allocas TD Mem als = Some Mem' ->
  getCallerReturnID c' = None ->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState (mkEC F B nil (insn_return_void rid) lc als)
              ((mkEC F' B' (c'::cs') tmn' lc' als')::ECS) Mem)
    (mkState (mkEC F' B' cs' tmn' lc' als') (ECS) Mem')
    E0 

| sBranch : forall S TD Ps F B lc gl fs bid Cond l1 l2 conds c
                              ps' cs' tmn' lc' ECS Mem als,
  getOperandValue TD Cond lc gl = Some conds ->
  c @ conds ->
  Some (stmts_intro ps' cs' tmn') = (if isGVZero TD c
               then lookupBlockViaLabelFromFdef F l2
               else lookupBlockViaLabelFromFdef F l1) ->
  switchToNewBasicBlock TD (if isGVZero TD c then l2 else l1, 
                            stmts_intro ps' cs' tmn') B gl lc = Some lc'->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState (mkEC F B nil (insn_br bid Cond l1 l2) lc als) (ECS) Mem)
    (mkState (mkEC F (if isGVZero TD c then l2 else l1, 
                       stmts_intro ps' cs' tmn') cs' tmn' lc' als) (ECS) Mem)
    E0 

| sBranch_uncond : forall S TD Ps F B lc gl fs bid l
                           ps' cs' tmn' lc' ECS Mem als,
  Some (stmts_intro ps' cs' tmn') = (lookupBlockViaLabelFromFdef F l) ->
  switchToNewBasicBlock TD (l, stmts_intro ps' cs' tmn') B gl lc = Some lc'->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState (mkEC F B nil (insn_br_uncond bid l) lc als) (ECS) Mem)
    (mkState (mkEC F (l, stmts_intro ps' cs' tmn') cs' tmn' lc' als) (ECS) Mem)
    E0 

| sBop: forall S TD Ps F B lc gl fs id bop sz v1 v2 gvs3 ECS cs tmn Mem als,
  BOP TD lc gl bop sz v1 v2 = Some gvs3 ->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState (mkEC F B ((insn_bop id bop sz v1 v2)::cs) tmn lc als) (ECS) Mem)
    (mkState (mkEC F B cs tmn (updateAddAL _ lc id gvs3) als) (ECS) Mem)
    E0 

| sFBop: forall S TD Ps F B lc gl fs id fbop fp v1 v2 gvs3 ECS cs tmn Mem als,
  FBOP TD lc gl fbop fp v1 v2 = Some gvs3 ->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState (mkEC F B ((insn_fbop id fbop fp v1 v2)::cs) tmn lc als) (ECS) Mem)
    (mkState (mkEC F B cs tmn (updateAddAL _ lc id gvs3) als) (ECS) Mem)
    E0 

| sExtractValue : forall S TD Ps F B lc gl fs id t v gvs gvs' idxs ECS cs tmn
                          Mem als t',
  getOperandValue TD v lc gl = Some gvs ->
  extractGenericValue TD t gvs idxs = Some gvs' ->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState (mkEC F B ((insn_extractvalue id t v idxs t')::cs) tmn lc als) (ECS)
               Mem)
    (mkState (mkEC F B cs tmn (updateAddAL _ lc id gvs') als) (ECS) Mem)
    E0

| sInsertValue : forall S TD Ps F B lc gl fs id t v t' v' gvs gvs' gvs'' idxs
                         ECS cs tmn Mem als,
  getOperandValue TD v lc gl = Some gvs ->
  getOperandValue TD v' lc gl = Some gvs' ->
  insertGenericValue TD t gvs idxs t' gvs' = Some gvs'' ->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState (mkEC F B ((insn_insertvalue id t v t' v' idxs)::cs) tmn
                    lc als) (ECS) Mem)
    (mkState (mkEC F B cs tmn (updateAddAL _ lc id gvs'') als) (ECS) Mem)
    E0 

| sMalloc : forall S TD Ps F B lc gl fs id t v gns gn align ECS cs tmn Mem als
                    Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gns ->
  gn @ gns ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState (mkEC F B ((insn_malloc id t v align)::cs) tmn lc als)  (ECS) Mem)
    (mkState (mkEC F B cs tmn
                (updateAddAL _ lc id ($ (blk2GV TD mb) # (typ_pointer t) $))
                als) (ECS) Mem')
    E0

| sFree : forall S TD Ps F B lc gl fs fid t v ECS cs tmn Mem als Mem' mptrs mptr,
  getOperandValue TD v lc gl = Some mptrs ->
  mptr @ mptrs ->
  free TD Mem mptr = Some Mem'->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState (mkEC F B ((insn_free fid t v)::cs) tmn lc als) (ECS) Mem)
    (mkState (mkEC F B cs tmn lc als) (ECS) Mem')
    E0

| sAlloca : forall S TD Ps F B lc gl fs id t v gns gn align ECS cs tmn Mem als
                    Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gns ->
  gn @ gns ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState (mkEC F B ((insn_alloca id t v align)::cs) tmn lc als) (ECS) Mem)
    (mkState (mkEC F B cs tmn
                   (updateAddAL _ lc id ($ (blk2GV TD mb) # (typ_pointer t) $))
                   (mb::als)) (ECS) Mem')
    E0

| sLoad : forall S TD Ps F B lc gl fs id t align v ECS cs tmn Mem als mps mp gv,
  getOperandValue TD v lc gl = Some mps ->
  mp @ mps ->
  mload TD Mem mp t align = Some gv ->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState (mkEC F B ((insn_load id t v align)::cs) tmn lc als) (ECS) Mem)
    (mkState (mkEC F B cs tmn (updateAddAL _ lc id ($ gv # t $)) als) (ECS) Mem)
    E0

| sStore : forall S TD Ps F B lc gl fs sid t align v1 v2 ECS cs tmn Mem als
                   mp2 gv1 Mem' gvs1 mps2,
  getOperandValue TD v1 lc gl = Some gvs1 ->
  getOperandValue TD v2 lc gl = Some mps2 ->
  gv1 @ gvs1 -> mp2 @ mps2 ->
  mstore TD Mem mp2 t gv1 align = Some Mem' ->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState (mkEC F B ((insn_store sid t v1 v2 align)::cs) tmn lc als) (ECS)
               Mem)
    (mkState (mkEC F B cs tmn lc als) (ECS) Mem')
    E0

| sGEP : forall S TD Ps F B lc gl fs id inbounds t v idxs vidxs vidxss ECS mp mp'
                 cs tmn Mem als t',
  getOperandValue TD v lc gl = Some mp ->
  values2GVs TD idxs lc gl = Some vidxss ->
  vidxs @@ vidxss ->
  GEP TD t mp vidxs inbounds t' = Some mp' ->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState (mkEC F B ((insn_gep id inbounds t v idxs t')::cs) 
                 tmn lc als) (ECS) Mem)
    (mkState (mkEC F B cs tmn (updateAddAL _ lc id mp') als) (ECS) Mem)
    E0 

| sTrunc : forall S TD Ps F B lc gl fs id truncop t1 v1 t2 gvs2 ECS cs tmn
                   Mem als,
  TRUNC TD lc gl truncop t1 v1 t2 = Some gvs2 ->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState (mkEC F B ((insn_trunc id truncop t1 v1 t2)::cs) tmn lc als) (ECS)
               Mem)
    (mkState (mkEC F B cs tmn (updateAddAL _ lc id gvs2) als) (ECS) Mem)
    E0

| sExt : forall S TD Ps F B lc gl fs id extop t1 v1 t2 gvs2 ECS cs tmn Mem
                 als,
  EXT TD lc gl extop t1 v1 t2 = Some gvs2 ->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState (mkEC F B ((insn_ext id extop t1 v1 t2)::cs) tmn lc als) (ECS) Mem)
    (mkState (mkEC F B cs tmn (updateAddAL _ lc id gvs2) als) (ECS) Mem)
    E0

| sCast : forall S TD Ps F B lc gl fs id castop t1 v1 t2 gvs2 ECS cs tmn Mem
                  als,
  CAST TD lc gl castop t1 v1 t2 = Some gvs2 ->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState (mkEC F B ((insn_cast id castop t1 v1 t2)::cs) tmn lc als) (ECS)
               Mem)
    (mkState (mkEC F B cs tmn (updateAddAL _ lc id gvs2) als) (ECS) Mem)
    E0

| sIcmp : forall S TD Ps F B lc gl fs id cond t v1 v2 gvs3 ECS cs tmn Mem als,
  ICMP TD lc gl cond t v1 v2 = Some gvs3 ->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState (mkEC F B ((insn_icmp id cond t v1 v2)::cs) tmn lc als) (ECS) Mem)
    (mkState (mkEC F B cs tmn (updateAddAL _ lc id gvs3) als) (ECS) Mem)
    E0

| sFcmp : forall S TD Ps F B lc gl fs id fcond fp v1 v2 gvs3 ECS cs tmn Mem
                  als,
  FCMP TD lc gl fcond fp v1 v2 = Some gvs3 ->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState (mkEC F B ((insn_fcmp id fcond fp v1 v2)::cs) tmn lc als) (ECS) Mem)
    (mkState (mkEC F B cs tmn (updateAddAL _ lc id gvs3) als) (ECS) Mem)
    E0

| sSelect : forall S TD Ps F B lc gl fs id v0 t v1 v2 cond c ECS cs tmn Mem als
                    gvs1 gvs2,
  getOperandValue TD v0 lc gl = Some cond ->
  getOperandValue TD v1 lc gl = Some gvs1 ->
  getOperandValue TD v2 lc gl = Some gvs2 ->
  c @ cond ->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState (mkEC F B ((insn_select id v0 t v1 v2)::cs) tmn lc als) (ECS) Mem)
    (mkState (mkEC F B cs tmn (if isGVZero TD c
                                then updateAddAL _ lc id gvs2
                                else updateAddAL _ lc id gvs1) als) (ECS) Mem)
    E0

| sCall : forall S TD Ps F B lc gl fs rid noret ca fid fv lp cs tmn fptrs fptr
                 lc' l' ps' cs' tmn' ECS rt la va lb Mem als rt1 va1 fa gvs,
  (* only look up the current module for the time being,
     do not support linkage. *)
  getOperandValue TD fv lc gl = Some fptrs ->
  fptr @ fptrs ->
  lookupFdefViaPtr Ps fs fptr =
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) =
    Some (l', stmts_intro ps' cs' tmn') ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc' ->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState (mkEC F B ((insn_call rid noret ca rt1 va1 fv lp)::cs) tmn
                       lc als) ECS Mem)
    (mkState (mkEC (fdef_intro (fheader_intro fa rt fid la va) lb)
                       (l', stmts_intro ps' cs' tmn') cs' tmn' lc' nil)
              ((mkEC F B ((insn_call rid noret ca rt1 va1 fv lp)::cs) tmn
                       lc als)::ECS) Mem)
    E0 

| sExCall : forall S TD Ps F B lc gl fs rid noret ca fid fv lp cs tmn ECS dck
       rt la Mem als oresult Mem' lc' va rt1 va1 fa gvs fptr fptrs gvss tr,
  (* only look up the current module for the time being,
     do not support linkage.
     FIXME: should add excall to trace
  *)
  getOperandValue TD fv lc gl = Some fptrs ->
  fptr @ fptrs ->
  lookupExFdecViaPtr Ps fs fptr =
    Some (fdec_intro (fheader_intro fa rt fid la va) dck) ->
  params2GVs TD lp lc gl = Some gvss ->
  gvs @@ gvss ->
  callExternalOrIntrinsics TD gl Mem fid rt (args2Typs la) dck gvs = 
    Some (oresult, tr, Mem') ->
  exCallUpdateLocals TD rt1 noret rid oresult lc = Some lc' ->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState (mkEC F B ((insn_call rid noret ca rt1 va1 fv lp)::cs) tmn
                       lc als) (ECS) Mem)
    (mkState (mkEC F B cs tmn lc' als) (ECS) Mem')
    tr
.

(* Given the entry of main with input Args, the following initializes the 
   program S. *)
Definition s_genInitState (S:system) (main:id) (Args:list GVs) (initmem:mem)
  : option (Config * State) :=
match (lookupFdefViaIDFromSystem S main) with
| None => None
| Some CurFunction =>
  match (getParentOfFdefFromSystem CurFunction S) with
  | None => None
  | Some (module_intro CurLayouts CurNamedts CurProducts) =>
    let initargetdata :=
      initTargetData CurLayouts CurNamedts initmem in
    match (genGlobalAndInitMem initargetdata CurProducts nil nil
      initmem) with
    | None => None
    | Some (initGlobal, initFunTable, initMem) =>
      match (getEntryBlock CurFunction) with
      | None => None
      | Some (l, stmts_intro ps cs tmn) =>
          match CurFunction with
          | fdef_intro (fheader_intro _ rt _ la _) _ =>
            match initLocals initargetdata la Args with
            | Some Values =>
              Some
              (mkCfg
                S
                initargetdata
                CurProducts
                initGlobal
                initFunTable,
               mkState
                (mkEC
                  CurFunction
                  (l, stmts_intro ps cs tmn)
                  cs
                  tmn
                  Values
                  nil
                )
                nil 
                initMem
              )
            | None => None
            end
        end
      end
    end
  end
end.

(* Return the final result if state is a final state. *)
Definition s_isFinialState (cfg:Config) (state:State) : option GVs :=
match state with
| (mkState (mkEC _ _ nil (insn_return_void _) _ _) nil _ ) => 
    (* This case cannot be None at any context. *)
    const2GV (OpsemAux.CurTargetData cfg) (OpsemAux.Globals cfg) 
      (const_int Size.One (INTEGER.of_Z 1%Z 1%Z false))
| (mkState (mkEC _ _ nil (insn_return _ _ v) lc _) nil _ ) => 
    (* This case cannot be None at well-formed context. 
       In other words, if a program reaches here, but returns None, 
       the program is stuck. *)
    getOperandValue (OpsemAux.CurTargetData cfg) v lc 
       (OpsemAux.Globals cfg)
| _ => None
end.

(* >=0 small steps *)
Inductive sop_star (cfg:Config) : State -> State -> trace -> Prop :=
| sop_star_nil : forall state, sop_star cfg state state E0
| sop_star_cons : forall state1 state2 state3 tr1 tr2,
    sInsn cfg state1 state2 tr1 ->
    sop_star cfg state2 state3 tr2 ->
    sop_star cfg state1 state3 (Eapp tr1 tr2)
.

(* >=1 small steps *)
Inductive sop_plus (cfg:Config) : State -> State -> trace -> Prop :=
| sop_plus_cons : forall state1 state2 state3 tr1 tr2,
    sInsn cfg state1 state2 tr1 ->
    sop_star cfg state2 state3 tr2 ->
    sop_plus cfg state1 state3 (Eapp tr1 tr2)
.

(* Three definitions of divergence. They are used for different proofs.
   We prove that they are equivalent. *)
CoInductive sop_diverges (cfg:Config) : State -> traceinf -> Prop :=
| sop_diverges_intro : forall state1 state2 tr1 tr2,
    sop_plus cfg state1 state2 tr1 ->
    sop_diverges cfg state2 tr2 ->
    sop_diverges cfg state1 (Eappinf tr1 tr2)
.

CoInductive sop_diverges' (cfg:Config): State -> traceinf -> Prop :=
| sop_diverges_intro' : forall state1 state2 tr1 tr2,
    Opsem.sInsn cfg state1 state2 tr1 ->
    sop_diverges' cfg state2 tr2 ->
    sop_diverges' cfg state1 (Eappinf tr1 tr2).

Section SOP_WF_DIVERGES.

Variable Measure: Type.
Variable R:Measure -> Measure -> Prop.
Hypothesis Hwf_founded_R: well_founded R.

CoInductive sop_wf_diverges (cfg:Config): Measure -> State -> traceinf -> Prop:=
| sop_wf_diverges_plus : forall m1 m2 state1 state2 tr1 tr2,
    Opsem.sop_plus cfg state1 state2 tr1 ->
    sop_wf_diverges cfg m2 state2 tr2 ->
    sop_wf_diverges cfg m1 state1 (Eappinf tr1 tr2)
| sop_wf_diverges_star : forall m1 m2 state1 state2 tr1 tr2,
    R m2 m1 ->
    Opsem.sop_star cfg state1 state2 tr1 ->
    sop_wf_diverges cfg m2 state2 tr2 ->
    sop_wf_diverges cfg m1 state1 (Eappinf tr1 tr2)
.

End SOP_WF_DIVERGES.

(* A program terminates if its initial state reaches a final state. *)
Inductive s_converges : system -> id -> list GVs -> trace -> GVs -> Prop :=
| s_converges_intro : forall (s:system) (main:id) (VarArgs:list GVs)    
                              cfg (IS FS:Opsem.State) r tr,
  s_genInitState s main VarArgs Mem.empty = Some (cfg, IS) ->
  sop_star cfg IS FS tr ->
  s_isFinialState cfg FS = Some r ->
  s_converges s main VarArgs tr r
.

(* A program non-terminates if its initial state diverges. *)
Inductive s_diverges : system -> id -> list GVs -> traceinf -> Prop :=
| s_diverges_intro : forall (s:system) (main:id) (VarArgs:list GVs)
                             cfg (IS:State) tr,
  s_genInitState s main VarArgs Mem.empty = Some (cfg, IS) ->
  sop_diverges cfg IS tr ->
  s_diverges s main VarArgs tr
.

(* A state is stuck if it cannot step. *)
Definition stuck_state (cfg:OpsemAux.Config) (st:State) : Prop :=
~ exists st', exists tr, sInsn cfg st st' tr.

(* A program terminates if its initial state reaches a non-final stuck state. *)
Inductive s_goeswrong : system -> id -> list GVs -> trace -> State -> Prop :=
| s_goeswrong_intro : forall (s:system) (main:id) (VarArgs:list GVs)
                              cfg (IS FS:State) tr,
  s_genInitState s main VarArgs Mem.empty = Some (cfg, IS) ->
  sop_star cfg IS FS tr ->
  stuck_state cfg FS ->
  s_isFinialState cfg FS = None ->
  s_goeswrong s main VarArgs tr FS
.

(***************************************************************)
(* big-step *)

Definition callUpdateLocals (TD:TargetData) rt (noret:bool) (rid:id)
  (oResult:option value) (lc lc':GVsMap) (gl:GVMap) : option GVsMap :=
    match noret with
    | false =>
        match oResult with
        | None => None
        | Some Result =>
          match getOperandValue TD Result lc' gl with
          | Some gr =>
              match (GVsSig.(lift_op1) (fit_gv TD rt) gr rt) with
              | Some gr' => Some (updateAddAL _ lc rid gr')
              | None => None
              end
          | None => None
          end
        end
    | true =>
        match oResult with
        | None => Some lc
        | Some Result =>
          match (getOperandValue TD Result lc' gl) with
          | Some gr => Some lc
          | None => None
          end
        end
    end.

(* Execution contexts for big-step *)
Record bExecutionContext : Type := mkbEC {
bCurBB       : block;                 (* the current block *)
bCurCmds     : cmds;                  (* cmds to run within CurBB *)
bTerminator  : terminator;            (* the terminator of CurBB *)
bLocals      : GVsMap;                (* LLVM values used in this invocation *)
bAllocas     : list mblock;           (* Track memory allocated by alloca *)
bMem         : mem
}.

(* The big-step semantics takes a function call as a single step by bFdef and
   bops. *)
Inductive bInsn :
    bConfig -> bExecutionContext -> bExecutionContext -> trace ->  Prop :=
| bBranch : forall S TD Ps F B lc gl fs bid Cond l1 l2 conds c
                              ps' cs' tmn' Mem als lc',
  getOperandValue TD Cond lc gl = Some conds ->
  c @ conds ->
  Some (stmts_intro ps' cs' tmn') = (if isGVZero TD c
               then lookupBlockViaLabelFromFdef F l2
               else lookupBlockViaLabelFromFdef F l1) ->
  switchToNewBasicBlock TD (if isGVZero TD c then l2 else l1,
                            stmts_intro ps' cs' tmn') B gl lc = Some lc'->
  bInsn (mkbCfg S TD Ps gl fs F)
    (mkbEC B nil (insn_br bid Cond l1 l2) lc als Mem)
    (mkbEC (if isGVZero TD c then l2 else l1, stmts_intro ps' cs' tmn') 
      cs' tmn' lc' als Mem)
    E0

| bBranch_uncond : forall S TD Ps F B lc gl fs l bid
                              ps' cs' tmn' Mem als lc',
  Some (stmts_intro ps' cs' tmn') = (lookupBlockViaLabelFromFdef F l) ->
  switchToNewBasicBlock TD (l, stmts_intro ps' cs' tmn') B gl lc = Some lc'->
  bInsn (mkbCfg S TD Ps gl fs F)
    (mkbEC B nil (insn_br_uncond bid l) lc als Mem)
    (mkbEC (l, stmts_intro ps' cs' tmn') cs' tmn' lc' als Mem)
    E0

| bBop : forall S TD Ps F B lc gl fs id bop sz v1 v2 gv3 cs tmn Mem als,
  BOP TD lc gl bop sz v1 v2 = Some gv3 ->
  bInsn (mkbCfg S TD Ps gl fs F)
    (mkbEC B ((insn_bop id bop sz v1 v2)::cs) tmn lc als Mem)
    (mkbEC B cs tmn (updateAddAL _ lc id gv3) als Mem)
    E0 

| bFBop : forall S TD Ps F B lc gl fs id fbop fp v1 v2 gv3 cs tmn Mem
                  als,
  FBOP TD lc gl fbop fp v1 v2 = Some gv3 ->
  bInsn (mkbCfg S TD Ps gl fs F)
    (mkbEC B ((insn_fbop id fbop fp v1 v2)::cs) tmn lc als Mem)
    (mkbEC B cs tmn (updateAddAL _ lc id gv3) als Mem)
    E0 

| bExtractValue : forall S TD Ps F B lc gl fs id t v gv gv' idxs cs tmn
                          Mem als t',
  getOperandValue TD v lc gl = Some gv ->
  extractGenericValue TD t gv idxs = Some gv' ->
  bInsn (mkbCfg S TD Ps gl fs F)
    (mkbEC B ((insn_extractvalue id t v idxs t')::cs) tmn lc als Mem)
    (mkbEC B cs tmn (updateAddAL _ lc id gv') als Mem)
    E0 

| bInsertValue : forall S TD Ps F B lc gl fs id t v t' v' gv gv' gv'' idxs
                         cs tmn Mem als,
  getOperandValue TD v lc gl = Some gv ->
  getOperandValue TD v' lc gl = Some gv' ->
  insertGenericValue TD t gv idxs t' gv' = Some gv'' ->
  bInsn (mkbCfg S TD Ps gl fs F)
    (mkbEC B ((insn_insertvalue id t v t' v' idxs)::cs) tmn lc als Mem)
    (mkbEC B cs tmn (updateAddAL _ lc id gv'') als Mem)
    E0

| bMalloc : forall S TD Ps F B lc gl fs id t v gns gn align cs tmn Mem als
                    Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gns ->
  gn @ gns ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  bInsn (mkbCfg S TD Ps gl fs F)
    (mkbEC B ((insn_malloc id t v align)::cs) tmn lc als Mem)
    (mkbEC B cs tmn  (updateAddAL _ lc id ($ (blk2GV TD mb) # (typ_pointer t) $))
          als Mem')
    E0

| bFree : forall S TD Ps F B lc gl fs fid t v cs tmn Mem als Mem' mptrs mptr,
  getOperandValue TD v lc gl = Some mptrs ->
  mptr @ mptrs ->
  free TD Mem mptr = Some Mem'->
  bInsn (mkbCfg S TD Ps gl fs F)
    (mkbEC B ((insn_free fid t v)::cs) tmn lc als Mem)
    (mkbEC B cs tmn lc als Mem')
    E0

| bAlloca : forall S TD Ps F B lc gl fs id t v gns gn align cs tmn Mem als
                    Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gns ->
  gn @ gns ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  bInsn (mkbCfg S TD Ps gl fs F)
    (mkbEC B ((insn_alloca id t v align)::cs) tmn lc als Mem)
    (mkbEC B cs tmn (updateAddAL _ lc id ($ (blk2GV TD mb) # (typ_pointer t) $))
                    (mb::als) Mem')
    E0

| bLoad : forall S TD Ps F B lc gl fs id t v align cs tmn Mem als mps mp gv,
  getOperandValue TD v lc gl = Some mps ->
  mp @ mps ->
  mload TD Mem mp t align = Some gv ->
  bInsn (mkbCfg S TD Ps gl fs F)
    (mkbEC B ((insn_load id t v align)::cs) tmn lc als Mem)
    (mkbEC B cs tmn (updateAddAL _ lc id ($ gv # t $)) als Mem)
    E0

| bStore : forall S TD Ps F B lc gl fs sid t v1 v2 align cs tmn Mem als
                   mp2 gv1 Mem' gvs1 mps2,
  getOperandValue TD v1 lc gl = Some gvs1 ->
  getOperandValue TD v2 lc gl = Some mps2 ->
  gv1 @ gvs1 -> mp2 @ mps2 ->
  mstore TD Mem mp2 t gv1 align = Some Mem' ->
  bInsn (mkbCfg S TD Ps gl fs  F)
    (mkbEC B ((insn_store sid t v1 v2 align)::cs) tmn lc als Mem)
    (mkbEC B cs tmn lc als Mem')
    E0

| bGEP : forall S TD Ps F B lc gl fs id inbounds t v idxs vidxs vidxss mp mp'
                 cs tmn Mem als t',
  getOperandValue TD v lc gl = Some mp ->
  values2GVs TD idxs lc gl = Some vidxss ->
  vidxs @@ vidxss ->
  GEP TD t mp vidxs inbounds t' = Some mp' ->
  bInsn (mkbCfg S TD Ps gl fs F)
    (mkbEC B ((insn_gep id inbounds t v idxs t')::cs) tmn lc als Mem)
    (mkbEC B cs tmn (updateAddAL _ lc id mp') als Mem)
    E0 

| bTrunc : forall S TD Ps F B lc gl fs id truncop t1 v1 t2 gv2 cs tmn Mem als,
  TRUNC TD lc gl truncop t1 v1 t2 = Some gv2 ->
  bInsn (mkbCfg S TD Ps gl fs F)
    (mkbEC B ((insn_trunc id truncop t1 v1 t2)::cs) tmn lc als Mem)
    (mkbEC B cs tmn (updateAddAL _ lc id gv2) als Mem)
    E0

| bExt : forall S TD Ps F B lc gl fs id extop t1 v1 t2 gv2 cs tmn Mem als,
  EXT TD lc gl extop t1 v1 t2 = Some gv2 ->
  bInsn (mkbCfg S TD Ps gl fs F)
    (mkbEC B ((insn_ext id extop t1 v1 t2)::cs) tmn lc als Mem)
    (mkbEC B cs tmn (updateAddAL _ lc id gv2) als Mem)
    E0

| bCast : forall S TD Ps F B lc gl fs id castop t1 v1 t2 gv2 cs tmn Mem als,
  CAST TD lc gl castop t1 v1 t2 = Some gv2 ->
  bInsn (mkbCfg S TD Ps gl fs F)
    (mkbEC B ((insn_cast id castop t1 v1 t2)::cs) tmn lc als Mem)
    (mkbEC B cs tmn (updateAddAL _ lc id gv2) als Mem)
    E0

| bIcmp : forall S TD Ps F B lc gl fs id cond t v1 v2 gv3 cs tmn Mem als,
  ICMP TD lc gl cond t v1 v2 = Some gv3 ->
  bInsn (mkbCfg S TD Ps gl fs F)
    (mkbEC B ((insn_icmp id cond t v1 v2)::cs) tmn lc als Mem)
    (mkbEC B cs tmn (updateAddAL _ lc id gv3) als Mem)
    E0

| bFcmp : forall S TD Ps F B lc gl fs id fcond fp v1 v2 gv3 cs tmn Mem als,
  FCMP TD lc gl fcond fp v1 v2 = Some gv3 ->
  bInsn (mkbCfg S TD Ps gl fs F)
    (mkbEC B ((insn_fcmp id fcond fp v1 v2)::cs) tmn lc als Mem)
    (mkbEC B cs tmn (updateAddAL _ lc id gv3) als Mem)
    E0

| bSelect : forall S TD Ps F B lc gl fs id v0 t v1 v2 cond c cs tmn Mem als
                    gv1 gv2,
  getOperandValue TD v0 lc gl = Some cond ->
  getOperandValue TD v1 lc gl = Some gv1 ->
  getOperandValue TD v2 lc gl = Some gv2 ->
  c @ cond ->
  bInsn (mkbCfg S TD Ps gl fs F)
    (mkbEC B ((insn_select id v0 t v1 v2)::cs) tmn lc als Mem)
    (mkbEC B cs tmn (if isGVZero TD c
                     then updateAddAL _ lc id gv2
                     else updateAddAL _ lc id gv1) als Mem)
    E0

| bCall : forall S TD Ps F B lc gl fs rid noret ca rt fv lp cs tmn
            Rid oResult tr B' lc' Mem Mem' als' als Mem'' lc'' rt1 va1,
  bFdef fv rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr ->
  free_allocas TD Mem' als' = Some Mem'' ->
  callUpdateLocals TD rt1 noret rid oResult lc lc' gl = Some lc'' ->
  bInsn (mkbCfg S TD Ps gl fs F)
    (mkbEC B ((insn_call rid noret ca rt1 va1 fv lp)::cs) tmn lc als Mem)
    (mkbEC B cs tmn lc'' als Mem'')
    tr

| bExCall : forall S TD Ps F B lc gl fs rid noret fv fid lp cs tmn dck
    rt la va Mem als oresult Mem' lc' rt1 va1 fa ca gvs fptr fptrs gvss tr,
  (* only look up the current module for the time being,
     do not support linkage.
     FIXME: should add excall to trace
  *)
  getOperandValue TD fv lc gl = Some fptrs ->
  fptr @ fptrs ->
  lookupExFdecViaPtr Ps fs fptr =
    Some (fdec_intro (fheader_intro fa rt fid la va) dck) ->
  params2GVs TD lp lc gl = Some gvss ->
  gvs @@ gvss ->
  callExternalOrIntrinsics TD gl Mem fid rt (args2Typs la) dck gvs = 
    Some (oresult, tr, Mem') ->
  exCallUpdateLocals TD rt1 noret rid oresult lc = Some lc' ->
  bInsn (mkbCfg S TD Ps gl fs F)
    (mkbEC B ((insn_call rid noret ca rt1 va1 fv lp)::cs) tmn lc als Mem)
    (mkbEC B cs tmn lc' als Mem')
    tr

with bops: bConfig -> bExecutionContext -> bExecutionContext -> trace -> Prop :=
| bops_nil : forall cfg S, bops cfg S S E0
| bops_cons : forall cfg S1 S2 S3 t1 t2,
    bInsn cfg S1 S2 t1 ->
    bops cfg S2 S3 t2 ->
    bops cfg S1 S3 (Eapp t1 t2)

with bFdef : value -> typ -> params -> system -> TargetData -> products ->
            GVsMap -> GVMap -> GVMap -> mem -> GVsMap ->
            list mblock -> mem -> block -> id -> option value -> trace -> Prop :=
| bFdef_func : forall S TD Ps gl fs fv fid lp lc rid fa lc0 fptrs fptr
   l' ps' cs' tmn' rt la lb l'' ps'' cs'' Result lc' tr Mem Mem' als' va gvs,
  getOperandValue TD fv lc gl = Some fptrs ->
  fptr @ fptrs ->
  lookupFdefViaPtr Ps fs fptr =
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) =
    Some (l', stmts_intro ps' cs' tmn') ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc0 ->
  bops (mkbCfg S TD Ps gl fs (fdef_intro (fheader_intro fa rt fid la va) lb))
    (mkbEC (l', stmts_intro ps' cs' tmn') cs' tmn' lc0 nil Mem)
    (mkbEC (l'', stmts_intro ps'' cs'' (insn_return rid rt Result)) nil
                             (insn_return rid rt Result) lc' als' Mem')
    tr ->
  bFdef fv rt lp S TD Ps lc gl fs Mem lc' als' Mem'
    (l'', stmts_intro ps'' cs'' (insn_return rid rt Result)) rid (Some Result) tr

| bFdef_proc : forall S TD Ps gl fs fv fid lp lc rid fa lc0 fptrs fptr
       l' ps' cs' tmn' rt la lb l'' ps'' cs'' lc' tr Mem Mem' als' va gvs,
  getOperandValue TD fv lc gl = Some fptrs ->
  fptr @ fptrs ->
  lookupFdefViaPtr Ps fs fptr =
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) =
    Some (l', stmts_intro ps' cs' tmn') ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc0 ->
  bops (mkbCfg S TD Ps gl fs (fdef_intro (fheader_intro fa rt fid la va) lb) )
    (mkbEC (l', stmts_intro ps' cs' tmn') cs' tmn' lc0 nil Mem)
    (mkbEC (l'', stmts_intro ps'' cs'' (insn_return_void rid)) nil
                            (insn_return_void rid) lc' als' Mem')
    tr ->
  bFdef fv rt lp S TD Ps lc gl fs Mem lc' als' Mem'
    (l'', stmts_intro ps'' cs'' (insn_return_void rid)) rid None tr
.

(* big-step divergence. *)
CoInductive bInsnInf : bConfig -> bExecutionContext -> traceinf -> Prop :=
| bCallInsnInf : forall S TD Ps F B lc gl fs rid noret ca rt fv lp cs tmn
                       tr Mem als rt1 va1,
  bFdefInf fv rt lp S TD Ps lc gl fs Mem tr ->
  bInsnInf (mkbCfg S TD Ps gl fs F)
    (mkbEC B ((insn_call rid noret ca rt1 va1 fv lp)::cs) tmn lc als Mem) tr

with bopInf : bConfig -> bExecutionContext -> traceinf -> Prop :=
| bopInf_insn : forall cfg state1 t1,
    bInsnInf cfg state1 t1 ->
    bopInf cfg state1 t1
| bopInf_cons : forall cfg state1 state2 t1 t2,
    bInsn cfg state1 state2 t1 ->
    bopInf cfg state2 t2 ->
    bopInf cfg state1 (Eappinf t1 t2)

with bFdefInf : value -> typ -> params -> system -> TargetData -> products ->
    GVsMap -> GVMap  -> GVMap -> mem -> traceinf -> Prop :=
| bFdefInf_intro : forall S TD Ps lc gl fs fv fid lp fa lc0
                          l' ps' cs' tmn' rt la va lb tr Mem gvs fptrs fptr,
  getOperandValue TD fv lc gl = Some fptrs ->
  fptr @ fptrs ->
  lookupFdefViaPtr Ps fs fptr =
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) =
    Some (l', stmts_intro ps' cs' tmn') ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc0 ->
  bopInf (mkbCfg S TD Ps gl fs (fdef_intro (fheader_intro fa rt fid la va) lb))
    (mkbEC (l', stmts_intro ps' cs' tmn') cs' tmn' lc0 nil Mem)
    tr ->
  bFdefInf fv rt lp S TD Ps lc gl fs Mem tr
.

(* Initial states *)
Definition b_genInitState (S:system) (main:id) (Args:list GVs) (initmem:mem)
  : option (bConfig * bExecutionContext) :=
match s_genInitState S main Args initmem with
| Some (mkCfg S0 TD Ps gl fs, mkState (mkEC F B cs tmn lc als) nil M) =>
    Some (mkbCfg S0 TD Ps gl fs F, mkbEC B cs tmn lc als M)
| _ => None
end.

(* Final states *)
Definition b_isFinialState (cfg:bConfig) (ec:bExecutionContext) : option GVs :=
match ec with
| (mkbEC _ nil (insn_return_void _) _ _ _ ) =>
    const2GV (OpsemAux.bCurTargetData cfg) (OpsemAux.bGlobals cfg) 
      (const_int Size.One (INTEGER.of_Z 1%Z 1%Z false))
| (mkbEC _ nil (insn_return _ _ v) lc _ _ ) =>
    getOperandValue (OpsemAux.bCurTargetData cfg) v lc 
      (OpsemAux.bGlobals cfg)
| _ => None
end.

(* Termination *)
Inductive b_converges : system -> id -> list GVs -> trace -> GVs -> Prop :=
| b_converges_intro : forall (s:system) (main:id) (VarArgs:list GVs)
                       cfg (IS FS:bExecutionContext) tr r,
  b_genInitState s main VarArgs Mem.empty = Some (cfg, IS) ->
  bops cfg IS FS tr ->
  b_isFinialState cfg FS = Some r ->
  b_converges s main VarArgs tr r
.

(* None-termination *)
Inductive b_diverges : system -> id -> list GVs -> traceinf -> Prop :=
| b_diverges_intro : forall (s:system) (main:id) (VarArgs:list GVs)
                             cfg (IS S:bExecutionContext) tr,
  b_genInitState s main VarArgs Mem.empty = Some (cfg, IS) ->
  bopInf cfg IS tr ->
  b_diverges s main VarArgs tr
.

(* Wrong programs *)
Definition stuck_bstate (cfg:OpsemAux.bConfig) (st:bExecutionContext) : Prop :=
~ exists st', exists tr, bInsn cfg st st' tr.

Inductive b_goeswrong : 
    system -> id -> list GVs -> trace -> bExecutionContext -> Prop :=
| b_goeswrong_intro : forall (s:system) (main:id) (VarArgs:list GVs)
                              cfg (IS FS:bExecutionContext) tr,
  b_genInitState s main VarArgs Mem.empty = Some (cfg, IS) ->
  bops cfg IS FS tr ->
  stuck_bstate cfg FS ->
  b_isFinialState cfg FS = None ->
  b_goeswrong s main VarArgs tr FS
.

Scheme bInsn_ind2 := Induction for bInsn Sort Prop
  with bops_ind2 := Induction for bops Sort Prop
  with bFdef_ind2 := Induction for bFdef Sort Prop.

Combined Scheme b_mutind from bInsn_ind2, bops_ind2, bFdef_ind2.

End Opsem.

Hint Unfold in_list_gvs.
Hint Constructors bInsn bops bFdef sInsn sop_star sop_diverges sop_plus.

End Opsem.

Tactic Notation "sInsn_cases" tactic(first) tactic(c) :=
  first;
  [ c "sReturn" | c "sReturnVoid" | c "sBranch" | c "sBranch_uncond" |
    c "sBop" | c "sFBop" | c "sExtractValue" | c "sInsertValue" |
    c "sMalloc" | c "sFree" |
    c "sAlloca" | c "sLoad" | c "sStore" | c "sGEP" |
    c "sTrunc" | c "sExt" |
    c "sCast" |
    c "sIcmp" | c "sFcmp" | c "sSelect" |
    c "sCall" | c "sExCall" ].

Tactic Notation "b_mutind_cases" tactic(first) tactic(c) :=
  first;
  [ c "bBranch" | c "bBranch_uncond" |
    c "bBop" | c "bFBop" | c "bExtractValue" | c "bInsertValue" |
    c "bMalloc" | c "bFree" |
    c "bAlloca" | c "bLoad" | c "bStore" | c "bGEP" |
    c "bTrunc" | c "bExt" | c "bCast" | c "bIcmp" | c "bFcmp" |  c "bSelect" |
    c "bCall" | c "bExCall" |
    c "bops_nil" | c "bops_cons" | c "bFdef_func" | c "bFdef_proc" ].

Tactic Notation "sop_star_cases" tactic(first) tactic(c) :=
  first;
  [ c "sop_star_nil" | c "sop_star_cons" ].

Ltac simpl_s_genInitState :=
  match goal with
  | Hinit: Opsem.s_genInitState _ _ _ _ = _ |- _ =>
    unfold Opsem.s_genInitState in Hinit;
    inv_mbind'
  end;
  match goal with
  | m : module |- _ =>
    destruct m as [CurLayouts CurNamedts CurProducts];
    inv_mbind'
  end;
  match goal with
  | H: ret (_, ?s0) = getEntryBlock ?f |- _ =>
    destruct s0 as [ps0 cs0 tmn0];
    destruct f as [[f t i0 a v] b];
    inv_mbind'
  end;
  try repeat match goal with
  | H: ret _ = ret _ |- _ => inv H
  end;
  symmetry_ctx.

