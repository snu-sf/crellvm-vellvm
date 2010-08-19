open Printf
open Llvm
open Symexe

let string_of_value v = "value"

let travel_instr i =
	match (classify_instr i) with
	| InstrOpcode.Alloca ->
		  eprintf "%s = alloc %s, i32 %s, align %n\n"
			        (value_name i) 
			        (string_of_lltype (AllocationInst.get_allocated_type i)) 
							(string_of_value (AllocationInst.get_array_size i)) 
							(AllocationInst.get_alignment i);
      flush_all ()				
	| _ -> dump_value i	 

let travel_block b =
	prerr_string "label: ";
	prerr_endline (value_name (value_of_block b));
	iter_instrs travel_instr b

let travel_function f =
	prerr_string "fname: ";
	prerr_endline (value_name f);
	prerr_string "ftyp: ";
	prerr_endline (string_of_lltype (type_of f));
	Array.iter dump_value (params f);
	iter_blocks travel_block f
	
let travel_module m = 
	prerr_string "layouts: ";
	prerr_endline (data_layout m);
	iter_globals dump_value m;
	iter_functions travel_function m

let main in_filename out_filename =
  let c = create_context () in
  let mbuf = MemoryBuffer.of_file in_filename in
  let m = Llvm_bitreader.parse_bitcode c mbuf in

  (* I use prerr but not print, because dump_ outputs to stderr. *)
  dump_module m;

  prerr_endline "Travel me:";
  travel_module m;
	
  (* write the module to a file *)
  if not (Llvm_bitwriter.write_bitcode_file m out_filename) then exit 1;
  dispose_module m

let () = match Sys.argv with
  | [|_; in_filename; out_filename|] -> main in_filename out_filename
  | _ -> main "Input.bc" "Output.bc"
