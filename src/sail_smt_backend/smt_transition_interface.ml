(****************************************************************************)
(*     Sail                                                                 *)
(*                                                                          *)
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(****************************************************************************)

(** Machine-readable interface metadata embedded in an SMT transition artifact. Formal names and sorts remain
    authoritative in the adjacent [define-fun]; [source_name] and [role] provide the stable source-level meaning. *)
type role = State_pre | Input | Nondet_input | State_post | Result | Side_condition

type parameter = { position : int; source_name : string option; role : role }

let string_of_role = function
  | State_pre -> "state-pre"
  | Input -> "input"
  | Nondet_input -> "nondet-input"
  | State_post -> "state-post"
  | Result -> "result"
  | Side_condition -> "side-condition"

(* SMT-LIB strings escape a quote by doubling it. Source-level Sail names do
   not normally contain quotes, but doing this here keeps the format complete. *)
let quote_string value = "\"" ^ String.concat "\"\"" (String.split_on_char '"' value) ^ "\""

let write channel ~transition parameters =
  output_string channel "; Sail transition interface; metadata order matches the define-fun parameters below.\n";
  output_string channel "(set-info :sail-transition-interface-version 1)\n";
  Printf.fprintf channel "(set-info :sail-transition %s)\n" (quote_string transition);
  List.iter
    (fun { position; source_name; role } ->
      Printf.fprintf channel "(set-info :sail-transition-parameter-%d-%s %s)\n" position (string_of_role role)
        (quote_string (Option.value ~default:"" source_name))
    )
    parameters
