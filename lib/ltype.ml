open! Base
open Printf
open Loc
open Syntax
open Gtype
open Err

type t =
  | RecvL of message * name * t
  | SendL of message * name * t
  | ChoiceL of name * t list
  | TVarL of name
  | MuL of name * t
  | EndL
[@@deriving sexp_of]

let show =
  let indent_here indent = String.make (indent * 2) ' ' in
  let rec show_local_type_internal indent =
    let current_indent = indent_here indent in
    function
    | RecvL (m, r, l) ->
        sprintf "%s%s from %s;\n%s" current_indent (show_message m) r.value
          (show_local_type_internal indent l)
    | SendL (m, r, l) ->
        sprintf "%s%s to %s;\n%s" current_indent (show_message m) r.value
          (show_local_type_internal indent l)
    | MuL (n, l) ->
        sprintf "%srec %s {\n%s%s}\n" current_indent n.value
          (show_local_type_internal (indent + 1) l)
          current_indent
    | TVarL n -> sprintf "%s%s\n" current_indent n.value
    | EndL -> sprintf "%send\n" current_indent
    | ChoiceL (r, ls) ->
        let pre = sprintf "%schoice at %s {\n" current_indent r.value in
        let intermission = sprintf "%s} or {\n" current_indent in
        let post = sprintf "%s}\n" current_indent in
        let choices =
          List.map ~f:(show_local_type_internal (indent + 1)) ls
        in
        let ls = String.concat ~sep:intermission choices in
        pre ^ ls ^ post
  in
  show_local_type_internal 0

exception Unmergable of t * t [@@deriving sexp_of]

let rec merge projected_role lty1 lty2 =
  try
    let fail () = raise (Unmergable (lty1, lty2)) in
    let merge_recv r recvs =
      let rec aux (acc : (string * t) list) = function
        | RecvL (m, _, lty) as l -> (
            let label = message_label m in
            match List.Assoc.find acc ~equal:String.equal label with
            | None -> (label, l) :: acc
            | Some (RecvL (m_, r, l_))
              when Poly.equal (message_payload_ty m) (message_payload_ty m_)
              ->
                List.Assoc.add acc ~equal:String.equal label
                  (RecvL (m, r, merge projected_role lty l_))
            | Some (RecvL _) -> fail ()
            | _ -> failwith "Impossible" )
        | l -> failwith ("Impossible " ^ show l ^ " r " ^ r.value)
      in
      let conts = List.fold ~f:aux ~init:[] recvs in
      match conts with
      | [] -> EndL
      | [(_, lty)] -> lty
      | conts -> ChoiceL (r, List.map ~f:snd conts)
    in
    match (lty1, lty2) with
    | RecvL (_, r1, _), RecvL (_, r2, _) ->
        if not @@ name_equal r1 r2 then fail () ;
        merge_recv r1 [lty1; lty2]
    | ChoiceL (r1, ltys1), RecvL (_, r2, _) when name_equal r1 r2 ->
        (* Choice is a set of receive *)
        merge_recv r1 (lty2 :: ltys1)
    | RecvL (_, r2, _), ChoiceL (r1, ltys2) when name_equal r1 r2 ->
        merge_recv r1 (lty1 :: ltys2)
    | ChoiceL (r1, ltys1), ChoiceL (r2, ltys2)
      when name_equal r1 r2 && not (name_equal r1 projected_role) ->
        merge_recv r1 (ltys1 @ ltys2)
    | _ -> if Poly.equal lty1 lty2 then lty1 else fail ()
  with Unmergable (l1, l2) ->
    let s1 = Sexp.to_string (sexp_of_t l1) in
    let s2 = Sexp.to_string (sexp_of_t l2) in
    let error = s1 ^ " " ^ s2 in
    Err.UserError (Err.UnableToMerge error) |> raise

(* Check whether the first message in a g choice is from choice_r to recv_r,
   if recv_r is Some; return receive role *)
let check_consistent_gchoice choice_r recv_r =
  let err () = unimpl "Error message for inconsistent choice" in
  function
  | MessageG (_, send_r, recv_r_, _) -> (
      if not @@ name_equal send_r choice_r then err () ;
      match recv_r with
      | None -> Some recv_r_
      | Some recv_r ->
          if not @@ name_equal recv_r recv_r then err () ;
          Some recv_r )
  | _ -> err ()

let rec project (projected_role : name) = function
  | EndG -> EndL
  | TVarG name -> TVarL name
  | MuG (name, g_type) -> (
    match project projected_role g_type with
    | TVarL _ | EndL -> EndL
    | lType -> MuL (name, lType) )
  | MessageG (m, send_r, recv_r, g_type) -> (
      let next = project projected_role g_type in
      match projected_role with
      | _ when name_equal projected_role send_r -> SendL (m, recv_r, next)
      | _ when name_equal projected_role recv_r -> RecvL (m, send_r, next)
      | _ -> next )
  | ChoiceG (choice_r, g_types) -> (
      let recv_r =
        List.fold ~f:(check_consistent_gchoice choice_r) ~init:None g_types
      in
      let recv_r = Option.value_exn recv_r in
      let l_types = List.map ~f:(project projected_role) g_types in
      let l_types =
        List.filter ~f:(function EndL -> false | _ -> true) l_types
      in
      match projected_role with
      | _
        when name_equal projected_role choice_r
             || name_equal projected_role recv_r ->
          ChoiceL (choice_r, l_types)
      | _ -> (
        match List.reduce ~f:(merge projected_role) l_types with
        | Some l -> l
        | None -> EndL ) )
