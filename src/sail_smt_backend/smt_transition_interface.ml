(****************************************************************************)
(*     Sail                                                                 *)
(*                                                                          *)
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(****************************************************************************)

(** Machine-readable interface for an SMT transition relation. The SMT parameter name is an implementation detail;
    [source_name] and [role] provide the stable meaning consumed by verification tools. *)
type role = State_pre | Input | Nondet_input | State_post | Result | Side_condition

type parameter = { position : int; source_name : string option; smt_name : string; smt_sort : string; role : role }

let manifest_file_name smt_file = smt_file ^ ".interface.json"

let string_of_role = function
  | State_pre -> "state_pre"
  | Input -> "input"
  | Nondet_input -> "nondet_input"
  | State_post -> "state_post"
  | Result -> "result"
  | Side_condition -> "side_condition"

let json_of_parameter { position; source_name; smt_name; smt_sort; role } =
  `Assoc
    [
      ("position", `Int position);
      ("source_name", match source_name with Some name -> `String name | None -> `Null);
      ("smt_name", `String smt_name);
      ("smt_sort", `String smt_sort);
      ("role", `String (string_of_role role));
    ]

let to_json ~smt_file ~transition parameters =
  `Assoc
    [
      ("schema", `String "sail_smt_transition_interface");
      ("schema_version", `Int 1);
      ("transition", `String transition);
      ("smt_file", `String (Filename.basename smt_file));
      ("parameters", `List (List.map json_of_parameter parameters));
    ]

let write ~smt_file ~transition parameters =
  let file_name = manifest_file_name smt_file in
  let channel = open_out_bin file_name in
  Fun.protect
    ~finally:(fun () -> close_out_noerr channel)
    (fun () ->
      Yojson.Safe.pretty_to_channel ~std:true channel (to_json ~smt_file ~transition parameters);
      output_char channel '\n'
    )
