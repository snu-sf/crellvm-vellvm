Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
(*Add LoadPath "../../../theory/metatheory".*)
Require Import symexe_correct.
Require Import ssa_def.
Require Import ssa_lib.
Require Import Metatheory.
Require Import genericvalues.
Require Import ssa_mem.
Require Import ssa_dynamic.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive option => "option"  [ "Some" "None" ].

Extract Constant AtomImpl.atom => "String.t".
Extract Constant AtomImpl.eq_atom_dec => "fun a b -> a = b".
Extract Constant AtomImpl.atom_fresh_for_list => "Camlcoq.atom_fresh_for_list".

Extract Constant LLVMsyntax.id => "String.t".
Extract Constant LLVMsyntax.l => "String.t".
Extract Constant LLVMsyntax.inbounds => "bool".
Extract Constant LLVMsyntax.tailc => "bool".
Extract Constant LLVMsyntax.noret => "bool".

Extract Constant LLVMsyntax.Size.t => "int".
Extract Constant LLVMsyntax.Size.Zero => "0".
Extract Constant LLVMsyntax.Size.One => "1".
Extract Constant LLVMsyntax.Size.Two => "2".
Extract Constant LLVMsyntax.Size.Four => "4".
Extract Constant LLVMsyntax.Size.Eight => "8".
Extract Constant LLVMsyntax.Size.Sixteen => "16".
Extract Constant LLVMsyntax.Size.ThirtyTwo => "32".
Extract Constant LLVMsyntax.Size.SixtyFour => "64".
Extract Constant LLVMsyntax.Size.from_nat => "Camlcoq.camlint_of_nat".
Extract Constant LLVMsyntax.Size.to_nat => "fun x -> Camlcoq.nat_of_camlint(Int32.of_int x)".
Extract Constant LLVMsyntax.Size.to_Z => "fun x -> Camlcoq.z_of_camlint (Int32.of_int x)".
Extract Constant LLVMsyntax.Size.from_Z => "fun x -> Int32.to_int (Camlcoq.camlint_of_z x)".
Extract Constant LLVMsyntax.Size.add => "( + )".
Extract Constant LLVMsyntax.Size.sub => "( - )".
Extract Constant LLVMsyntax.Size.mul => "( * )".
Extract Constant LLVMsyntax.Size.div => "( / )".
Extract Constant LLVMsyntax.Size.dec => "( == )".

Extract Constant LLVMsyntax.Align.t => "int".
Extract Constant LLVMsyntax.Align.Zero => "0".
Extract Constant LLVMsyntax.Align.One => "1".
Extract Constant LLVMsyntax.Align.Two => "2".
Extract Constant LLVMsyntax.Align.Four => "4".
Extract Constant LLVMsyntax.Align.Eight => "8".
Extract Constant LLVMsyntax.Align.Sixteen => "16".
Extract Constant LLVMsyntax.Align.ThirtyTwo => "32".
Extract Constant LLVMsyntax.Align.SixtyFour => "64".
Extract Constant LLVMsyntax.Align.from_nat => "Camlcoq.camlint_of_nat".
Extract Constant LLVMsyntax.Align.to_nat => "fun x -> Camlcoq.nat_of_camlint(Int32.of_int x)".
Extract Constant LLVMsyntax.Align.to_Z => "fun x -> Camlcoq.z_of_camlint (Int32.of_int x)".
Extract Constant LLVMsyntax.Align.from_Z => "fun x -> Int32.to_int (Camlcoq.camlint_of_z x)".
Extract Constant LLVMsyntax.Align.add => "( + )".
Extract Constant LLVMsyntax.Align.sub => "( - )".
Extract Constant LLVMsyntax.Align.mul => "( * )".
Extract Constant LLVMsyntax.Align.div => "( / )".
Extract Constant LLVMsyntax.Align.dec => "( == )".

Extract Constant LLVMsyntax.INTEGER.t => "Llvm.APInt.t".
Extract Constant LLVMsyntax.INTEGER.to_nat => "Camlcoq.llapint2nat".
Extract Constant LLVMsyntax.INTEGER.to_Z => "Camlcoq.llapint2z".
Extract Constant LLVMsyntax.INTEGER.dec => "Llvm.APInt.compare".

Extract Constant LLVMsyntax.FLOAT.t => "Llvm.APFloat.t".
Extract Constant LLVMsyntax.FLOAT.dec => "Llvm.APFloat.bcompare".

Extract Constant LLVMlib.inbounds_dec => "(==)".
Extract Constant LLVMlib.tailc_dec => "(==)".
Extract Constant LLVMlib.noret_dec => "(==)".

Extract Constant LLVMgv.mblock => "Llvmcaml.GenericValue.t".
Extract Constant LLVMgv.mptr => "Llvmcaml.GenericValue.t".
Extract Constant LLVMgv.null => "Llvmcaml.GenericValue.null".
Extract Constant LLVMgv.GenericValue => "Llvmcaml.GenericValue.t".
Extract Constant LLVMgv.sizeGenericValue => "Llvmcaml.GenericValue.sizeGenericValue".
Extract Constant LLVMgv.uninits => "Llvmcaml.GenericValue.uninits".
Extract Constant LLVMgv.GV2val => "Llvmcaml.GenericValue.gv2val".
Extract Constant LLVMgv.GV2int => "Llvmcaml.GenericValue.gv2int".
Extract Constant LLVMgv.GV2ptr => "Llvmcaml.GenericValue.gv2ptr".
Extract Constant LLVMgv.val2GV => "Llvmcaml.GenericValue.val2gv".
Extract Constant LLVMgv.ptr2GV => "Llvmcaml.GenericValue.ptr2gv".
Extract Constant LLVMgv.blk2GV => "Llvmcaml.GenericValue.blk2gv".
Extract Constant LLVMgv.isGVZero => "Llvmcaml.GenericValue.isZero".
Extract Constant LLVMgv.repeatGV => "Llvmcaml.GenericValue.repeatGV".
Extract Constant LLVMgv._zeroconst2GV => "Llvmcaml.GenericValue._zeroconst2GV".
Extract Constant LLVMgv._list_typ_zerostruct2GV => "Llvmcaml.GenericValue._list_typ_zerostruct2GV".
Extract Constant LLVMgv._const2GV => "Llvmcaml.GenericValue._const2GV".
Extract Constant LLVMgv._list_const_arr2GV => "Llvmcaml.GenericValue._list_const_arr2GV".
Extract Constant LLVMgv._list_const_struct2GV => "Llvmcaml.GenericValue._list_const_struct2GV".
Extract Constant LLVMgv.const2GV => "Llvmcaml.GenericValue.const2GV".
Extract Constant LLVMgv.extractGenericValue => "Llvmcaml.GenericValue.extractGenericValue".
Extract Constant LLVMgv.insertGenericValue => "Llvmcaml.GenericValue.insertGenericValue".
Extract Constant LLVMgv.GEP => "Llvmcaml.GenericValue.mgep".
Extract Constant LLVMgv.mbop => "Llvmcaml.GenericValue.mbop".
Extract Constant LLVMgv.mfbop => "Llvmcaml.GenericValue.mfbop".
Extract Constant LLVMgv.mtrunc => "Llvmcaml.GenericValue.mtrunc".
Extract Constant LLVMgv.mcast => "Llvmcaml.GenericValue.mcast".
Extract Constant LLVMgv.mext => "Llvmcaml.GenericValue.mext".
Extract Constant LLVMgv.micmp => "Llvmcaml.GenericValue.micmp".
Extract Constant LLVMgv.mfcmp => "Llvmcaml.GenericValue.mfcmp".
Extract Constant LLVMgv.eq_gv => "Llvmcaml.GenericValue.eq_gv".

Extract Constant LLVMmem.mem =>  "Llvmcaml.Mem.t".
(*Extract Constant LLVMmem.initmem =>  "Llvmcaml.Mem.initmem".*)
Extract Constant LLVMmem.malloc =>  "Llvmcaml.Mem.malloc".
Extract Constant LLVMmem.free =>  "Llvmcaml.Mem.free".
Extract Constant LLVMmem.mload =>  "Llvmcaml.Mem.mload".
Extract Constant LLVMmem.mstore =>  "Llvmcaml.Mem.mstore".

Extract Constant LLVMopsem.initGlobal => "Llvmcaml.Mem.initGlobal".
Extract Constant LLVMopsem.getExternalGlobal => "Llvmcaml.Mem.getExternalGlobal".
Extract Constant LLVMopsem.initTargetData => "Llvmcaml.Mem.initTargetData".
Extract Constant LLVMopsem.callExternalFunction => "Llvmcaml.Mem.callExternalFunction".
Extract Constant LLVMopsem.lookupFdefViaGVFromFunTable => "Llvmcaml.GenericValue.lookupFdefViaGVFromFunTable".
Extract Constant LLVMopsem.initFunTable => "Llvmcaml.Mem.initFunTable".

Extract Constant LLVMtd.TargetData =>  "Llvmcaml.TargetData.t".
Extract Constant LLVMtd.getTypeAllocSize => "Llvmcaml.TargetData.getTypeAllocSize".
Extract Constant LLVMtd.getTypeAllocSizeInBits => "Llvmcaml.TargetData.getTypeAllocSizeInBits".
Extract Constant LLVMtd._getStructElementOffset => "Llvmcaml.TargetData._getStructElementOffset".
Extract Constant LLVMtd.getStructElementOffset => "Llvmcaml.TargetData.getStructElementOffset".
Extract Constant LLVMtd.getStructElementOffsetInBits => "Llvmcaml.TargetData.getStructElementOffsetInBits".
Extract Constant LLVMtd._getStructElementContainingOffset => "Llvmcaml.TargetData._getStructElementContainingOffset".
Extract Constant LLVMtd.getStructElementContainingOffset => "Llvmcaml.TargetData.getStructElementContainingOffset".
Extract Constant LLVMtd._getIntAlignmentInfo => "Llvmcaml.TargetData._getIntAlignmentInfo".
Extract Constant LLVMtd.getIntAlignmentInfo => "Llvmcaml.TargetData.getIntAlignmentInfo".
Extract Constant LLVMtd._getPointerAlignmentInfo => "Llvmcaml.TargetData._getPointerAlignmentInfo".
Extract Constant LLVMtd.getPointerAlignmentInfo => "Llvmcaml.TargetData.getPointerAlignmentInfo".
Extract Constant LLVMtd._getStructAlignmentInfo => "Llvmcaml.TargetData._getStructAlignmentInfo".
Extract Constant LLVMtd.getStructAlignmentInfo => "Llvmcaml.TargetData.getStructAlignmentInfo".
Extract Constant LLVMtd._getPointerSize => "Llvmcaml.TargetData._getPointerSize".
Extract Constant LLVMtd.getPointerSize => "Llvmcaml.TargetData.getPointerSize".
Extract Constant LLVMtd.getPointerSizeInBits => "Llvmcaml.TargetData.getPointerSizeInBits".
Extract Constant LLVMtd.getTypeSizeInBits_and_Alignment => "Llvmcaml.TargetData.getTypeSizeInBits_and_Alignment".
Extract Constant LLVMtd.getListTypeSizeInBits_and_Alignment => "Llvmcaml.TargetData.getListTypeSizeInBits_and_Alignment".
Extract Constant LLVMtd.getAlignment => "Llvmcaml.TargetData.getAlignment".
Extract Constant LLVMtd.getABITypeAlignment => "Llvmcaml.TargetData.getABITypeAlignment".
Extract Constant LLVMtd.getPrefTypeAlignment => "Llvmcaml.TargetData.getPrefTypeAlignment".
Extract Constant LLVMtd.getTypeSizeInBits => "Llvmcaml.TargetData.getTypeSizeInBits".
Extract Constant LLVMtd.getTypeStoreSize => "Llvmcaml.TargetData.getTypeStoreSize".
Extract Constant LLVMtd.getTypeStoreSizeInBits => "Llvmcaml.TargetData.getTypeStoreSizeInBits".
Extract Constant LLVMtd.getStructSizeInBytes => "Llvmcaml.TargetData.getStructSizeInBytes".
Extract Constant LLVMtd.getStructSizeInBits => "Llvmcaml.TargetData.getStructSizeInBits".
Extract Constant LLVMtd.getStructAlignment => "Llvmcaml.TargetData.getStructAlignment".
Extract Constant LLVMtd.getFloatAlignmentInfo => "Llvmcaml.TargetData.getFloatAlignmentInfo". 

(* Float *)
Extract Inlined Constant Floats.float => "float".
Extract Constant Floats.Float.zero   => "0.".
(* Extract Constant Floats.Float.one   => "1.". *)
Extract Constant Floats.Float.neg => "( ~-. )".
Extract Constant Floats.Float.abs => "abs_float".
Extract Constant Floats.Float.singleoffloat => "Floataux.singleoffloat".
Extract Constant Floats.Float.intoffloat => "Floataux.intoffloat".
Extract Constant Floats.Float.intuoffloat => "Floataux.intuoffloat".
Extract Constant Floats.Float.floatofint => "Floataux.floatofint".
Extract Constant Floats.Float.floatofintu => "Floataux.floatofintu".
Extract Constant Floats.Float.add => "( +. )".
Extract Constant Floats.Float.sub => "( -. )".
Extract Constant Floats.Float.mul => "( *. )".
Extract Constant Floats.Float.div => "( /. )".
Extract Constant Floats.Float.cmp => "Floataux.cmp".
Extract Constant Floats.Float.eq_dec => "fun (x: float) (y: float) -> x = y".
Extract Constant Floats.Float.bits_of_double => "Floataux.bits_of_double".
Extract Constant Floats.Float.double_of_bits => "Floataux.double_of_bits".
Extract Constant Floats.Float.bits_of_single => "Floataux.bits_of_single".
Extract Constant Floats.Float.single_of_bits => "Floataux.single_of_bits".

(* Memdata *)
Extract Constant Memdata.big_endian => "Memdataaux.big_endian".
Extract Constant Memdata.encode_float => "Memdataaux.encode_float".
Extract Constant Memdata.decode_float => "Memdataaux.decode_float".

(* Memory - work around an extraction bug. *)
Extraction NoInline Memory.Mem.valid_pointer.

(*
Extract Constant LLVMsyntax.nth_list_typ => "Symexe_aux.nth_list_typ".

Extract Constant LLVMlib.getCmdTyp => "Symexe_aux.getCmdTyp".
Extract Constant LLVMlib.Constant.getTyp => "Symexe_aux.getTyp".
Extract Constant LLVMlib.GlobalValue.getTyp => "Symexe_aux.getTyp".
Extract Constant LLVMlib.Function.getTyp => "Symexe_aux.getTyp".
Extract Constant LLVMlib.Typ.getPrimitiveSizeInBits => "Symexe_aux.getPrimitiveSizeInBits".
Extract Constant LLVMlib.DerivedType.getPrimitiveSizeInBits => "Symexe_aux.getPrimitiveSizeInBits".
Extract Constant LLVMlib.FunctionType.getPrimitiveSizeInBits => "Symexe_aux.getPrimitiveSizeInBits".
Extract Constant LLVMlib.CompositeType.getPrimitiveSizeInBits => "Symexe_aux.getPrimitiveSizeInBits".
Extract Constant LLVMlib.SequentialType.getPrimitiveSizeInBits => "Symexe_aux.getPrimitiveSizeInBits".
Extract Constant LLVMlib.ArrayType.getPrimitiveSizeInBits => "Symexe_aux.getPrimitiveSizeInBits".
Extract Constant LLVMlib.ArrayType.getNumElements => "Symexe_aux.getNumElements".
*)

Extraction Blacklist List String Int.

(*Extraction "symexe" tv_system.*)

Cd "extraction".
Recursive Extraction Library symexe_correct.
Cd "../".

