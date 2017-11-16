Require Import syntax_base.
Require Import syntax.
Require Import infrastructure.
Require Import Metatheory.
Require Import genericvalues.
Require Import targetdata.
Require Import Memory.
Require Import Integers.
Require Import Floats.
Require Import opsem.
(* Require Import interpreter. *)
Require Import Maps.
Require Import maps_ext.
Require Import Iteration.

Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive option => "option"  [ "Some" "None" ].
Extract Constant Iteration.GenIter.iterate =>
  "let rec iter f a =
    match f a with Coq_inl b -> Some b | Coq_inr a' -> iter f a'
   in iter".
(*
Extract Constant Iteration.dependent_description' => "fun x -> assert false".
TODO: check 
*)

(* Cutting the dependency to R. *)
Extract Inlined Constant Fcore_defs.F2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.FF2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.B2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.round_mode => "fun _ -> assert false".
Extract Inlined Constant Fcalc_bracket.inbetween_loc => "fun _ -> assert false".

Extract Constant AtomImpl.atom => "String.t".
Extract Constant AtomImpl.eq_atom_dec => "fun a b -> a = b".
Extract Constant AtomImpl.atom_fresh_for_list => "Camlcoq.atom_fresh_for_list".
Extract Constant AtomImpl.atom_compare => "fun x y ->
    let comp = String.compare x y in
    if(comp < 0) then Lt
    else if (comp > 0) then Gt
    else Eq".

Extract Constant LLVMsyntax_base.id => "String.t".
Extract Constant LLVMsyntax_base.l => "String.t".
Extract Constant LLVMsyntax_base.inbounds => "bool".
Extract Constant LLVMsyntax_base.tailc => "bool".
Extract Constant LLVMsyntax_base.noret => "bool".

Extract Constant Size.t => "int".
Extract Constant Size.Zero => "0".
Extract Constant Size.One => "1".
Extract Constant Size.Two => "2".
Extract Constant Size.Four => "4".
Extract Constant Size.Eight => "8".
Extract Constant Size.Sixteen => "16".
Extract Constant Size.ThirtyTwo => "32".
Extract Constant Size.SixtyFour => "64".
Extract Constant Size.from_nat => "Camlcoq.camlint_of_nat".
Extract Constant Size.to_nat =>
  "fun x -> Camlcoq.nat_of_camlint(Int32.of_int x)".
Extract Constant Size.to_Z =>
  "fun x -> Camlcoq.z_of_camlint (Int32.of_int x)".
Extract Constant Size.from_Z =>
  "fun x -> Int32.to_int (Camlcoq.camlint_of_z x)".
Extract Constant Size.add => "( + )".
Extract Constant Size.sub => "( - )".
Extract Constant Size.mul => "( * )".
Extract Constant Size.div => "( / )".
Extract Constant Size.dec => "( = )".

Extract Constant Align.t => "int".
Extract Constant Align.Zero => "0".
Extract Constant Align.One => "1".
Extract Constant Align.Two => "2".
Extract Constant Align.Four => "4".
Extract Constant Align.Eight => "8".
Extract Constant Align.Sixteen => "16".
Extract Constant Align.ThirtyTwo => "32".
Extract Constant Align.SixtyFour => "64".
Extract Constant Align.from_nat => "Camlcoq.camlint_of_nat".
Extract Constant Align.to_nat =>
  "fun x -> Camlcoq.nat_of_camlint(Int32.of_int x)".
Extract Constant Align.to_Z =>
  "fun x -> Camlcoq.z_of_camlint (Int32.of_int x)".
Extract Constant Align.from_Z =>
  "fun x -> Int32.to_int (Camlcoq.camlint_of_z x)".
Extract Constant Align.add => "( + )".
Extract Constant Align.sub => "( - )".
Extract Constant Align.mul => "( * )".
Extract Constant Align.div => "( / )".
Extract Constant Align.dec => "( = )".

Extract Constant INTEGER.t => "Llvm.APInt.t".
Extract Constant INTEGER.to_nat => "Camlcoq.llapint2nat".
Extract Constant INTEGER.to_Z => "Camlcoq.llapint2z".
Extract Constant INTEGER.dec => "Llvm.APInt.compare".
Extract Constant INTEGER.of_Z => "Camlcoq.z2llapint".

Extract Constant FLOAT.t => "Llvm.APFloat.t".
Extract Constant FLOAT.dec => "Llvm.APFloat.bcompare".
Extract Constant FLOAT.compare =>
"fun x y -> match Llvm.APFloat.compare_ord x y with Llvm.APFloat.CmpResult.LessThan -> Lt | Llvm.APFloat.CmpResult.GreaterThan -> Gt | Llvm.APFloat.CmpResult.Equal -> Eq | _ -> failwith ""Unreachable: Float.compare""".

Extract Constant LLVMinfra.inbounds_dec => "(=)".
Extract Constant LLVMinfra.tailc_dec => "(=)".
Extract Constant LLVMinfra.noret_dec => "(=)".
Extract Constant LLVMinfra.mgetoffset_aux =>
  "Llvmcaml.TargetData.mgetoffset_aux".
Extract Constant LLVMinfra.mgetoffset =>
  "Llvmcaml.TargetData.mgetoffset".
Extract Constant LLVMinfra.intConsts2Nats =>
  "Llvmcaml.TargetData.intConsts2Nats".

Extract Constant LLVMgv.mblock => "Llvmcaml.GenericValue.t".
Extract Constant LLVMgv.mptr => "Llvmcaml.GenericValue.t".
Extract Constant LLVMgv.null => "Llvmcaml.GenericValue.null".
Extract Constant LLVMgv.GenericValue => "Llvmcaml.GenericValue.t".
Extract Constant LLVMgv.uninits => "Llvmcaml.GenericValue.uninits".
Extract Constant LLVMgv.gundef => "Llvmcaml.GenericValue.gundef".
Extract Constant LLVMgv.mc2undefs => "fun x -> assert false".
Extract Constant LLVMgv.gv_chunks_match_typb_aux => "fun x y -> assert false".
Extract Constant LLVMgv.gv_has_chunkb => "fun x -> assert false".
Extract Constant LLVMgv.fit_gv => "Llvmcaml.GenericValue.fit_gv".
Extract Constant LLVMgv.GV2val => "Llvmcaml.GenericValue.gv2val".
Extract Constant LLVMgv.GV2int => "Llvmcaml.GenericValue.gv2int".
Extract Constant LLVMgv.GV2ptr => "Llvmcaml.GenericValue.gv2ptr".
Extract Constant LLVMgv.val2GV => "Llvmcaml.GenericValue.val2gv".
Extract Constant LLVMgv.ptr2GV => "Llvmcaml.GenericValue.ptr2gv".
Extract Constant LLVMgv.blk2GV => "Llvmcaml.GenericValue.blk2gv".
Extract Constant LLVMgv.isGVZero => "Llvmcaml.GenericValue.isZero".
Extract Constant LLVMgv.repeatGV => "Llvmcaml.GenericValue.repeatGV".
Extract Constant LLVMgv.sizeGenericValue =>
  "Llvmcaml.GenericValue.sizeGenericValue".
Extract Constant LLVMgv.splitGenericValue =>
  "Llvmcaml.GenericValue.splitGenericValue".
Extract Constant LLVMgv.zeroconst2GV => "Llvmcaml.GenericValue._zeroconst2GV".
Extract Constant LLVMgv.zeroconsts2GV =>
  "Llvmcaml.GenericValue._list_typ_zerostruct2GV".
Extract Constant LLVMgv.zeroconst2GV_aux => "fun x y z -> assert false".
Extract Constant LLVMgv.zeroconsts2GV_aux => "fun x y z -> assert false".
Extract Constant LLVMgv.zeroconsts2GV_aux_ => "fun x y z -> assert false".
Extract Constant LLVMgv.zeroconst2GV_for_namedts => "fun x y z -> assert false".
Extract Constant LLVMgv._list_const_arr2GV_ => "fun x y z w -> assert false".
Extract Constant LLVMgv._list_const_struct2GV_ => "fun x y z w -> assert false".
Extract Constant LLVMgv._const2GV =>
  "Llvmcaml.GenericValue._const2GV".
Extract Constant LLVMgv._list_const_arr2GV =>
  "Llvmcaml.GenericValue._list_const_arr2GV".
Extract Constant LLVMgv._list_const_struct2GV =>
  "Llvmcaml.GenericValue._list_const_struct2GV".
Extract Constant LLVMgv.extractGenericValue =>
  "Llvmcaml.GenericValue.extractGenericValue".
Extract Constant LLVMgv.insertGenericValue =>
  "Llvmcaml.GenericValue.insertGenericValue".
Extract Constant LLVMgv.GEP => "Llvmcaml.GenericValue.gep".
Extract Constant LLVMgv.mbop => "Llvmcaml.GenericValue.mbop".
Extract Constant LLVMgv.mfbop => "Llvmcaml.GenericValue.mfbop".
Extract Constant LLVMgv.mtrunc => "Llvmcaml.GenericValue.mtrunc".
Extract Constant LLVMgv.mcast => "Llvmcaml.GenericValue.mcast".
(*Extract Constant LLVMgv.mptrtoint => "Llvmcaml.GenericValue.mptrtoint". TODO: check *)
(*Extract Constant LLVMgv.minttoptr => "Llvmcaml.GenericValue.minttoptr". TODO: check *)
Extract Constant LLVMgv.mext => "Llvmcaml.GenericValue.mext".
Extract Constant LLVMgv.micmp => "Llvmcaml.GenericValue.micmp".
Extract Constant LLVMgv.micmp_int => "Llvmcaml.GenericValue.micmp_int".
(*Extract Constant LLVMgv.micmp_ptr => "Llvmcaml.GenericValue.micmp_ptr". TODO: check *)
Extract Constant LLVMgv.mfcmp => "Llvmcaml.GenericValue.mfcmp".
Extract Constant LLVMgv.eq_gv => "Llvmcaml.GenericValue.eq_gv".
Extract Constant LLVMgv.cgv2gv => "Llvmcaml.GenericValue.cgv2gv".
Extract Constant LLVMgv.cundef_gv => "Llvmcaml.GenericValue.cundef_gv".
Extract Constant LLVMgv.mgep => "Llvmcaml.GenericValue.mgep".
Extract Constant LLVMgv.mget => "Llvmcaml.GenericValue.mget".
Extract Constant LLVMgv.mset => "Llvmcaml.GenericValue.mset".
Extract Constant LLVMgv.const2GV => "Llvmcaml.GenericValue.const2GV".
Extract Constant LLVMgv.getOperandValue =>
  "Llvmcaml.GenericValue.getOperandValue".

Extract Constant LLVMgv.mem =>  "Llvmcaml.GenericValue.mem".
(*Extract Constant LLVMmem.initmem =>  "Llvmcaml.Mem.initmem".*)
Extract Constant LLVMgv.malloc =>  "Llvmcaml.GenericValue.malloc".
Extract Constant LLVMgv.malloc_one =>  "Llvmcaml.GenericValue.malloc_one".
Extract Constant LLVMgv.free =>  "Llvmcaml.GenericValue.free".
Extract Constant LLVMgv.mload =>  "Llvmcaml.GenericValue.mload".
Extract Constant LLVMgv.mstore =>  "Llvmcaml.GenericValue.mstore".
Extract Constant LLVMgv.mload_aux =>  "Llvmcaml.GenericValue.mload_aux".
Extract Constant LLVMgv.mstore_aux =>  "Llvmcaml.GenericValue.mstore_aux".
Extract Constant LLVMgv.flatten_typ =>  "Llvmcaml.GenericValue.flatten_typ".
Extract Constant LLVMgv.flatten_typs =>  "Llvmcaml.GenericValue.flatten_typs".
Extract Constant LLVMgv.flatten_typ_aux =>  "fun x y z -> assert false".
Extract Constant LLVMgv.flatten_typs_aux =>  "fun x y z -> assert false".
Extract Constant LLVMgv.flatten_typs_aux_ =>  "fun x y z -> assert false".
Extract Constant LLVMgv.flatten_typ_for_namedts =>  "fun x y z -> assert false".

Extract Constant OpsemAux.initGlobal => "Llvmcaml.GenericValue.initGlobal".
Extract Constant OpsemAux.getExternalGlobal =>
  "Llvmcaml.GenericValue.getExternalGlobal".
Extract Constant OpsemAux.initTargetData =>
  "Llvmcaml.GenericValue.initTargetData".
Extract Constant OpsemAux.lookupFdefViaGVFromFunTable =>
  "Llvmcaml.GenericValue.lookupFdefViaGVFromFunTable".
Extract Constant OpsemAux.initFunTable => "Llvmcaml.GenericValue.initFunTable".

Extract Constant external_intrinsics.callExternalOrIntrinsics => 
  "Llvmcaml2.callExternalFunction".
Extract Constant external_intrinsics.callExternalFunction =>
  "fun x y z a b c d -> assert false".
Extract Constant external_intrinsics.callIntrinsics =>
  "fun x y z a b c d -> assert false".
Extract Constant external_intrinsics.callIOFunction =>
  "fun x y z a b c d -> assert false".

Extract Constant LLVMtd.TargetData =>  
  "Llvmcaml.TargetData.t".
Extract Constant LLVMtd.getTypeAllocSize =>
  "Llvmcaml.TargetData.getTypeAllocSize".
Extract Constant LLVMtd.getTypeAllocSizeInBits =>
  "Llvmcaml.TargetData.getTypeAllocSizeInBits".
Extract Constant LLVMtd._getStructElementOffset =>
  "Llvmcaml.TargetData._getStructElementOffset".
Extract Constant LLVMtd.getStructElementOffset =>
  "Llvmcaml.TargetData.getStructElementOffset".
Extract Constant LLVMtd.getStructElementOffsetInBits =>
  "Llvmcaml.TargetData.getStructElementOffsetInBits".
Extract Constant LLVMtd._getStructElementContainingOffset =>
  "Llvmcaml.TargetData._getStructElementContainingOffset".
Extract Constant LLVMtd.getStructElementContainingOffset =>
  "Llvmcaml.TargetData.getStructElementContainingOffset".
Extract Constant LLVMtd._getIntAlignmentInfo =>
  "Llvmcaml.TargetData._getIntAlignmentInfo".
Extract Constant LLVMtd.getIntAlignmentInfo =>
  "Llvmcaml.TargetData.getIntAlignmentInfo".
Extract Constant LLVMtd._getPointerAlignmentInfo =>
  "Llvmcaml.TargetData._getPointerAlignmentInfo".
Extract Constant LLVMtd.getPointerAlignmentInfo =>
  "Llvmcaml.TargetData.getPointerAlignmentInfo".
Extract Constant LLVMtd._getStructAlignmentInfo =>
  "Llvmcaml.TargetData._getStructAlignmentInfo".
Extract Constant LLVMtd.getStructAlignmentInfo =>
  "Llvmcaml.TargetData.getStructAlignmentInfo".
Extract Constant LLVMtd._getPointerSize =>
  "Llvmcaml.TargetData._getPointerSize".
Extract Constant LLVMtd.getPointerSize0 =>
  "Llvmcaml.TargetData.getPointerSize0".
Extract Constant LLVMtd.getPointerSize =>
  "Llvmcaml.TargetData.getPointerSize".
Extract Constant LLVMtd.getPointerSizeInBits =>
  "Llvmcaml.TargetData.getPointerSizeInBits".
Extract Constant LLVMtd._getTypeSizeInBits_and_Alignment =>
  "Llvmcaml.TargetData._getTypeSizeInBits_and_Alignment".
Extract Constant LLVMtd._getListTypeSizeInBits_and_Alignment_aux =>
  "fun x y z w -> assert false".
Extract Constant LLVMtd._getListTypeSizeInBits_and_Alignment =>
  "Llvmcaml.TargetData._getListTypeSizeInBits_and_Alignment".
Extract Constant LLVMtd._getTypeSizeInBits_and_Alignment_for_namedts =>
  "Llvmcaml.TargetData._getTypeSizeInBits_and_Alignment_for_namedts".
Extract Constant LLVMtd.getTypeSizeInBits_and_Alignment_for_namedts =>
  "Llvmcaml.TargetData.getTypeSizeInBits_and_Alignment_for_namedts".
Extract Constant LLVMtd.getTypeSizeInBits_and_Alignment =>
  "Llvmcaml.TargetData.getTypeSizeInBits_and_Alignment".
Extract Constant LLVMtd.getListTypeSizeInBits_and_Alignment =>
  "Llvmcaml.TargetData.getListTypeSizeInBits_and_Alignment".
Extract Constant LLVMtd.getAlignment =>
  "Llvmcaml.TargetData.getAlignment".
Extract Constant LLVMtd.getABITypeAlignment =>
  "Llvmcaml.TargetData.getABITypeAlignment".
Extract Constant LLVMtd.getPrefTypeAlignment =>
  "Llvmcaml.TargetData.getPrefTypeAlignment".
Extract Constant LLVMtd.getTypeSizeInBits =>
  "Llvmcaml.TargetData.getTypeSizeInBits".
Extract Constant LLVMtd.getTypeStoreSize =>
  "Llvmcaml.TargetData.getTypeStoreSize".
Extract Constant LLVMtd.getTypeStoreSizeInBits =>
  "Llvmcaml.TargetData.getTypeStoreSizeInBits".
Extract Constant LLVMtd.getStructSizeInBytes =>
  "Llvmcaml.TargetData.getStructSizeInBytes".
Extract Constant LLVMtd.getStructSizeInBits =>
  "Llvmcaml.TargetData.getStructSizeInBits".
Extract Constant LLVMtd.getStructAlignment =>
  "Llvmcaml.TargetData.getStructAlignment".
Extract Constant LLVMtd.getFloatAlignmentInfo =>
  "Llvmcaml.TargetData.getFloatAlignmentInfo".

(* AST *)
Extract Constant AST.ident_of_string =>
  "fun s -> Camlcoq.intern_string (Camlcoq.camlstring_of_coqstring s)".

(* Float *)
Extract Inlined Constant Floats.float => "float".
Extract Constant Floats.Float.zero   => "0.".
(*Extract Constant Floats.Float.one   => "1.".*)
Extract Constant Floats.Float.neg => "( ~-. )".
Extract Constant Floats.Float.abs => "abs_float".
Extract Constant Floats.Float.to_single => "Floataux.singleoffloat". (* TODO: check *)
Extract Constant Floats.Float.of_single => "Floataux.floatofsingle". (* TODO: check *)
Extract Constant Floats.Float.to_int => "Floataux.intoffloat". (* TODO: check *)
Extract Constant Floats.Float.to_intu => "Floataux.intuoffloat". (* TODO: check *)
Extract Constant Floats.Float.to_long => "Floataux.longoffloat". (* TODO: check *)
Extract Constant Floats.Float.to_longu => "Floataux.longoffloat". (* TODO: check, not exact *)
Extract Constant Floats.Float.of_int => "Floataux.floatofint". (* TODO: check *)
Extract Constant Floats.Float.of_intu => "Floataux.floatofintu". (* TODO: check *)
Extract Constant Floats.Float.of_long => "Floataux.floatoflong". (* TODO: check *)
Extract Constant Floats.Float.of_longu => "Floataux.floatofintu". (* TODO: check *)
Extract Constant Floats.Float.add => "( +. )".
Extract Constant Floats.Float.sub => "( -. )".
Extract Constant Floats.Float.mul => "( *. )".
Extract Constant Floats.Float.div => "( /. )".
Extract Constant Floats.Float.rem => "mod_float".
Extract Constant Floats.Float.cmp => "Floataux.cmp". (* TODO: check *)
Extract Constant Floats.Float.eq_dec => "fun (x: float) (y: float) -> x = y".
Extract Constant Floats.Float.to_bits => "Floataux.bits_of_double". (* TODO: check *)
Extract Constant Floats.Float.of_bits => "Floataux.double_of_bits". (* TODO: check *)

(* TODO: check *)
Extract Inlined Constant Floats.float32 => "float".
Extract Constant Floats.Float32.zero   => "0.".
Extract Constant Floats.Float32.neg => "( ~-. )".
Extract Constant Floats.Float32.abs => "abs_float".
Extract Constant Floats.Float32.to_double => "Floataux.floatofsingle". (* TODO: check *)
Extract Constant Floats.Float32.of_double => "Floataux.singleoffloat". (* TODO: check *)
Extract Constant Floats.Float32.to_int => "Floataux.intoffloat". (* TODO: check *)
Extract Constant Floats.Float32.to_intu => "Floataux.intuoffloat". (* TODO: check *)
Extract Constant Floats.Float32.to_long => "Floataux.longoffloat". (* TODO: check *)
Extract Constant Floats.Float32.to_longu => "Floataux.longoffloat". (* TODO: check, not exact *)
Extract Constant Floats.Float32.of_int => "Floataux.floatofint". (* TODO: check *)
Extract Constant Floats.Float32.of_intu => "Floataux.floatofintu". (* TODO: check *)
Extract Constant Floats.Float32.of_long => "fun l -> Floataux.singleoffloat (Floataux.floatoflong l)". (* TODO: check *)
Extract Constant Floats.Float32.of_longu => "fun l -> Floataux.singleoffloat (Floataux.floatofintu l)". (* TODO: check *)
Extract Constant Floats.Float32.add => "( +. )".
Extract Constant Floats.Float32.sub => "( -. )".
Extract Constant Floats.Float32.mul => "( *. )".
Extract Constant Floats.Float32.div => "( /. )".
Extract Constant Floats.Float32.rem => "mod_float".
Extract Constant Floats.Float32.cmp => "Floataux.cmp". (* TODO: check *)
Extract Constant Floats.Float32.eq_dec => "fun (x: float) (y: float) -> x = y".
Extract Constant Floats.Float32.to_bits => "Floataux.bits_of_single". (* TODO: check *)
Extract Constant Floats.Float32.of_bits => "Floataux.single_of_bits". (* TODO: check *)

(* Memdata *)
Extract Constant Archi.big_endian => "false". (* TODO: check *)
(*Extract Constant Memdata.encode_float => "Memdataaux.encode_float". TODO: check *)
(*Extract Constant Memdata.decode_float => "Memdataaux.decode_float". TODO: check *)

(* Dominators *)
Extract Constant cfg.Pcubeplus => "Camlcoq.pcubeplus".

(* Memory - work around an extraction bug. *)
Extraction NoInline Memory.Mem.valid_pointer.

(* AVL Tree/Map *)
Extract Constant AtomOT.compare => "Camlcoq.string_compare".

Extraction Blacklist List String Int.

Recursive Extraction Library Metatheory.
Recursive Extraction Library analysis.
(* Recursive Extraction Library interpreter. *)
