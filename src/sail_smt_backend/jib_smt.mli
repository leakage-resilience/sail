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
open Ast_compare
open Ast_defs
open Ast_util
open Jib
open Jib_util

val opt_debug_graphs : bool ref

module type CONFIG = sig
  val max_unknown_integer_width : int
  val max_unknown_bitvector_width : int
  val max_unknown_generic_vector_length : int
  val register_map : name list CTMap.t
  val ignore_overflow : bool
end

module Make (Config : CONFIG) : sig
  type generated_smt_info = {
    loc : Ast.l;
    file_name : string;
    function_id : id;
    args : name list;
    arg_ctyps : ctyp list;
    arg_smt_names : (name * string option) list;
  }

  (** Generate SMT for all the $property and $counterexample pragmas provided, and write the generated SMT to
      appropriately named files. *)
  val generate_smt :
    properties:(string * string * l * 'a val_spec) Bindings.t (** See Property.find_properties *) ->
    name_file:(string -> string) (** Applied to each function name to generate the file name for the smtlib file *) ->
    smt_includes:string list (** Extra files to include in each generated SMT problem *) ->
    Jib_compile.ctx ->
    cdef list ->
    generated_smt_info list

  (** Generate the SMT transition relation for a single named function, as one quantifier-free [define-fun] of type
      [Bool] named after the function. Its parameters are, in order:
      - each architectural register's pre-state value, named after the register (zencoded, e.g. [zR1]),
      - each function argument, named after its Sail-level parameter name,
      - each additional nondeterministic input needed by the transition,
      - each architectural register's post-state value, named [<register>_next],
      - the function result, named [return_value], unless the function returns [unit],
      - a [Bool] parameter per side condition that can actually occur - [overflow], [assertion_failure], [match_failure]
        \- omitted entirely when it cannot occur.

      The body is a flat conjunction of equalities, one per post-state/result/side-condition parameter, each pinning it
      to its computed value (every intermediate value from the underlying SSA walk is inlined by substitution, since
      Smt_exp has no let-binding node). The z-encoded formal names, their order, and their sorts form the transition's
      complete interface. *)
  val generate_transition :
    name_file:(string -> string) (** Applied to the function name to generate the file name for the smtlib file *) ->
    Jib_compile.ctx ->
    cdef list ->
    string ->
    unit
end

val compile :
  unroll_limit:int ->
  Type_check.Env.t ->
  Effects.side_effect_info ->
  Type_check.typed_ast ->
  cdef list * Jib_compile.ctx * name list CTMap.t
