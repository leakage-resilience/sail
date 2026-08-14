(****************************************************************************)
(*     Sail                                                                 *)
(*                                                                          *)
(*  Sail and the Sail architecture models here, comprising all files and    *)
(*  directories except the ASL-derived Sail code in the aarch64 directory,  *)
(*  are subject to the BSD two-clause licence below.                        *)
(*                                                                          *)
(*  The ASL derived parts of the ARMv8.3 specification in                   *)
(*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               *)
(*                                                                          *)
(*  Copyright (c) 2013-2021                                                 *)
(*    Kathyrn Gray                                                          *)
(*    Shaked Flur                                                           *)
(*    Stephen Kell                                                          *)
(*    Gabriel Kerneis                                                       *)
(*    Robert Norton-Wright                                                  *)
(*    Christopher Pulte                                                     *)
(*    Peter Sewell                                                          *)
(*    Alasdair Armstrong                                                    *)
(*    Brian Campbell                                                        *)
(*    Thomas Bauereiss                                                      *)
(*    Anthony Fox                                                           *)
(*    Jon French                                                            *)
(*    Dominic Mulligan                                                      *)
(*    Stephen Kell                                                          *)
(*    Mark Wassell                                                          *)
(*    Alastair Reid (Arm Ltd)                                               *)
(*                                                                          *)
(*  All rights reserved.                                                    *)
(*                                                                          *)
(*  This work was partially supported by EPSRC grant EP/K008528/1 <a        *)
(*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          *)
(*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   *)
(*  KTF funding, and donations from Arm.  This project has received         *)
(*  funding from the European Research Council (ERC) under the European     *)
(*  Union’s Horizon 2020 research and innovation programme (grant           *)
(*  agreement No 789108, ELVER).                                            *)
(*                                                                          *)
(*  This software was developed by SRI International and the University of  *)
(*  Cambridge Computer Laboratory (Department of Computer Science and       *)
(*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        *)
(*  and FA8750-10-C-0237 ("CTSRD").                                         *)
(*                                                                          *)
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(****************************************************************************)

open Libsail

open Ast
open Jib_smt
open Interactive.State
open Ast_compare

let opt_smt_auto = ref false
let opt_smt_auto_solver = ref Smt_exp.Cvc5
let opt_smt_includes : string list ref = ref []
let opt_smt_ignore_overflow = ref false
let opt_smt_specialize = ref true
let opt_smt_unknown_integer_width = ref 128
let opt_smt_unknown_bitvector_width = ref 64
let opt_smt_unknown_generic_vector_width = ref 32
let opt_smt_transition : string option ref = ref None

let rec source_argument_name (P_aux (pattern, _)) =
  match pattern with
  | P_id id -> Some (Ast_util.string_of_id id)
  | P_as (pattern, id) -> (
      match source_argument_name pattern with
      | Some _ as name -> name
      | None when not (Reporting.is_unknown_loc (Ast_util.id_loc id)) -> Some (Ast_util.string_of_id id)
      | None -> None
    )
  | P_typ (_, pattern) | P_var (pattern, _) -> source_argument_name pattern
  | _ -> None

let function_clause_argument_names (FCL_aux (FCL_funcl (_, pexp), _)) =
  let pattern, _, _, _ = Ast_util.destruct_pexp pexp in
  match pattern with
  | P_aux (P_tuple patterns, _) -> List.map source_argument_name patterns
  | pattern -> [source_argument_name pattern]

let same_source_name name1 name2 =
  match (name1, name2) with Some name1, Some name2 -> String.equal name1 name2 | None, None -> true | _ -> false

let merge_clause_argument_names = function
  | [] -> []
  | names :: remaining ->
      List.mapi
        (fun index name ->
          if
            List.for_all
              (fun other_names ->
                match List.nth_opt other_names index with
                | Some other_name -> same_source_name name other_name
                | None -> false
              )
              remaining
          then name
          else None
        )
        names

let transition_argument_names function_id (ast : Type_check.typed_ast) =
  List.find_map
    (function
      | DEF_aux (DEF_fundef (FD_aux (FD_function (_, _, clauses), _) as fundef), _)
        when Id.compare (Ast_util.id_of_fundef fundef) function_id = 0 ->
          Some (merge_clause_argument_names (List.map function_clause_argument_names clauses))
      | _ -> None
      )
    ast.defs

let set_smt_auto_solver arg =
  let open Smt_exp in
  match counterexample_solver_from_name arg with Some solver -> opt_smt_auto_solver := solver | None -> ()

let smt_options =
  [
    ( Flag.create ~prefix:["smt"] "auto",
      Arg.Tuple [Arg.Set opt_smt_auto],
      "automatically call the smt solver on generated SMT"
    );
    ( Flag.create ~prefix:["smt"] ~arg:"cvc4/cvc5/z3" "auto_solver",
      Arg.Tuple [Arg.Set opt_smt_auto; Arg.String set_smt_auto_solver],
      "set the solver to use for counterexample checks (default cvc5)"
    );
    ( Flag.create ~prefix:["smt"] "ignore_overflow",
      Arg.Set opt_smt_ignore_overflow,
      "ignore integer overflow in generated SMT"
    );
    ( Flag.create ~prefix:["smt"] ~arg:"n" "int_size",
      Arg.String (fun n -> opt_smt_unknown_integer_width := int_of_string n),
      "set a bound of n on the maximum integer bitwidth for generated SMT (default 128)"
    );
    ( Flag.create ~prefix:["smt"] "propagate_vars",
      Arg.Unit (fun () -> ()),
      "(deprecated) propgate variables through generated SMT"
    );
    ( Flag.create ~prefix:["smt"] ~arg:"n" "bits_size",
      Arg.String (fun n -> opt_smt_unknown_bitvector_width := int_of_string n),
      "set a size bound of n for unknown-length bitvectors in generated SMT (default 64)"
    );
    ( Flag.create ~prefix:["smt"] ~arg:"n" "vector_size",
      Arg.String (fun n -> opt_smt_unknown_generic_vector_width := int_of_string n),
      "set a bound of 2 ^ n for generic vectors in generated SMT (default 5)"
    );
    ( Flag.create ~prefix:["smt"] ~arg:"filename" "include",
      Arg.String (fun i -> opt_smt_includes := i :: !opt_smt_includes),
      "insert additional file in SMT output"
    );
    ( Flag.create ~prefix:["smt"] "disable_specialization",
      Arg.Clear opt_smt_specialize,
      "Disable generic specialization when generating SMT"
    );
    ( Flag.create ~prefix:["smt"] ~arg:"fn" "transition",
      Arg.String (fun fn -> opt_smt_transition := Some fn),
      "emit the given function's SMT transition relation, as a single quantifier-free define-fun with pre-state, \
       arguments, post-state, result, and side conditions as its parameters, plus a machine-readable interface \
       embedded with standard SMT-LIB set-info commands. Mutually exclusive with $property/$counterexample."
    );
  ]

let smt_rewrites =
  let open Rewrites in
  [
    ("instantiate_outcomes", [String_arg "c"]);
    ("realize_mappings", []);
    ("remove_vector_subrange_pats", []);
    ("toplevel_string_append", []);
    ("pat_string_append", []);
    ("mapping_patterns", []);
    ("truncate_hex_literals", []);
    ("mono_rewrites", [If_flag opt_mono_rewrites]);
    ("recheck_defs", [If_flag opt_mono_rewrites]);
    ("toplevel_nexps", [If_mono_arg]);
    ("monomorphise", [String_arg "c"; If_mono_arg]);
    ("atoms_to_singletons", [String_arg "c"; If_mono_arg]);
    ("recheck_defs", [If_mono_arg]);
    ("undefined", [Bool_arg false]);
    ("remove_not_pats", []);
    ("pattern_literals_typed", [Literal_arg "all"]);
    ("tuple_assignments", []);
    ("vector_concat_assignments", []);
    ("simple_struct_assignments", []);
    ("exp_lift_assign", []);
    ("merge_function_clauses", []);
    ("recheck_defs", []);
    ("constant_fold", [String_arg "c"]);
    ("properties", []);
  ]

(* Slice to root_ids, specialize, and compile to Jib - the part of the smt
   target's pipeline shared between the $property path and the
   -smt_transition path, which otherwise differ in what they slice to and
   how they turn the resulting cdefs into SMT. *)
let compile_for_smt out_file orig_env effect_info ast root_ids =
  let ast = Callgraph.filter_ast_ids root_ids IdSet.empty ast in
  Specialize.add_initial_calls root_ids;
  let ast_smt, env, effect_info =
    if !opt_smt_specialize then (
      let ast_smt, env, effect_info = Specialize.(specialize typ_specialization orig_env ast effect_info) in
      Specialize.(specialize_passes 2 int_specialization_with_externs env ast_smt effect_info)
    )
    else (ast, orig_env, effect_info)
  in
  let name_file =
    match out_file with Some f -> fun str -> f ^ "_" ^ str ^ ".smt2" | None -> fun str -> str ^ ".smt2"
  in
  Reporting.opt_warnings := true;
  let cdefs, ctx, register_map = Jib_smt.compile ~unroll_limit:10 env effect_info ast_smt in
  (ctx, cdefs, register_map, name_file)

let resolve_transition_id ast name =
  let id = Ast_util.mk_id name in
  if IdSet.mem id (Ast_util.val_spec_ids ast.Ast_defs.defs) then id
  else raise (Reporting.err_general Parse_ast.Unknown ("Could not find function " ^ name ^ " for -smt_transition"))

let smt_target out_file { ast; effect_info; env = orig_env; _ } =
  match !opt_smt_transition with
  | None ->
      let properties = Property.find_properties ast in
      let prop_ids = Bindings.bindings properties |> List.map fst |> IdSet.of_list in
      let ctx, cdefs, register_map, name_file = compile_for_smt out_file orig_env effect_info ast prop_ids in
      let module SMTGen = Jib_smt.Make (struct
        let max_unknown_integer_width = !opt_smt_unknown_integer_width
        let max_unknown_bitvector_width = !opt_smt_unknown_bitvector_width
        let max_unknown_generic_vector_length = !opt_smt_unknown_generic_vector_width
        let register_map = register_map
        let ignore_overflow = !opt_smt_ignore_overflow
      end) in
      let module Counterexample = Smt_exp.Counterexample (struct
        let max_unknown_integer_width = !opt_smt_unknown_integer_width
      end) in
      let t = Profile.start () in
      let generated_smt = SMTGen.generate_smt ~properties ~name_file ~smt_includes:!opt_smt_includes ctx cdefs in
      Profile.finish "Generating SMT" t;
      if !opt_smt_auto then (
        let unsats =
          List.map
            (fun ({ loc; file_name; function_id; args; arg_ctyps; arg_smt_names } : SMTGen.generated_smt_info) ->
              ( Counterexample.check ~loc ~ctx ~env:orig_env ~ast ~solver:!opt_smt_auto_solver ~file_name ~function_id
                  ~args ~arg_ctyps ~arg_smt_names,
                function_id
              )
            )
            generated_smt
        in
        List.iter
          (fun (u, fid) ->
            if u = false then (
              let l, tf = (Ast_util.id_loc fid, Ast_util.string_of_id fid) in
              raise (Reporting.err_general l ("Property check failure for " ^ tf ^ "."))
            )
          )
          unsats
      )
  | Some name ->
      let id = resolve_transition_id ast name in
      let arg_source_names =
        match transition_argument_names id ast with
        | Some names -> names
        | None ->
            raise
              (Reporting.err_general (Ast_util.id_loc id)
                 ("Could not recover source argument names for transition " ^ name)
              )
      in
      let ctx, cdefs, register_map, name_file =
        compile_for_smt out_file orig_env effect_info ast (IdSet.singleton id)
      in
      let module SMTGen = Jib_smt.Make (struct
        let max_unknown_integer_width = !opt_smt_unknown_integer_width
        let max_unknown_bitvector_width = !opt_smt_unknown_bitvector_width
        let max_unknown_generic_vector_length = !opt_smt_unknown_generic_vector_width
        let register_map = register_map
        let ignore_overflow = !opt_smt_ignore_overflow
      end) in
      ignore (SMTGen.generate_transition ~name_file ~arg_source_names ctx cdefs name)

let _ = Target.register ~name:"smt" ~options:smt_options ~rewrites:smt_rewrites smt_target
