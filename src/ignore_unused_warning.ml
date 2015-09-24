open StdLabels
open Ppx_core.Std
open Ast_builder.Default
open Asttypes
open Parsetree

[@@@metaloc loc]

let underscore_binding exp =
  let loc = exp.pexp_loc in
  value_binding ~loc ~pat:(ppat_any ~loc) ~expr:exp

let unit_binding exp =
  let loc = exp.pexp_loc in
  value_binding ~loc ~pat:(punit ~loc) ~expr:exp

let value_user ~loc exp =
  pstr_value ~loc Nonrecursive [underscore_binding exp]

let unit_value_user ~loc exp =
  pstr_value ~loc Nonrecursive [unit_binding exp]

let add_ignore (vars : Longident.t Located.t list) (acc : structure) : structure =
  List.fold_left (List.rev vars) ~init:acc ~f:(fun acc var ->
    value_user ~loc:var.loc (pexp_ident ~loc:var.loc var)
    :: acc)

let vars_of = object
  inherit [Longident.t Located.t list] Ast_traverse.fold as super
  method! pattern patt acc =
    match patt.ppat_desc with
    | Ppat_var v -> Located.map (fun var -> Longident.Lident var) v :: acc
    | _ -> super#pattern patt acc
end

(* For every [let x = ...] structure item, add a [let _ = x] *)
let add_dummy_user_for_values = object
  inherit Ast_traverse.map as super
  method! structure st =
    let rec loop st acc =
      match st with
      | [] -> List.rev acc
      | { pstr_desc = Pstr_value (_, vbs); pstr_loc = loc } as item :: rest ->
        let vars =
          List.fold_left vbs ~init:[] ~f:(fun acc vb -> vars_of#pattern vb.pvb_pat acc)
        in
        let ign =
          pstr_value ~loc Nonrecursive
            (List.rev_map vars ~f:(fun v ->
               underscore_binding (pexp_ident ~loc:v.loc v)))
        in
        loop rest (ign :: item :: acc)
      | item :: rest ->
        loop rest (item :: acc)
    in
    loop (super#structure st) []
end

let to_ignore_mark = "__type_conv_ignore_unused_warning__"
let to_ignore_mark_attr =
  ({ txt = to_ignore_mark; loc = Location.none }, PStr [])
;;

let has_mark vb =
  List.exists vb.pval_attributes ~f:(fun ({ txt; _ }, _) ->
    txt = to_ignore_mark)
;;

let remove_mark vb =
  let attrs =
    List.filter vb.pval_attributes ~f:(fun ({ txt; _ }, _) ->
      txt <> to_ignore_mark)
  in
  { vb with pval_attributes = attrs }
;;

let mark_values = object
  inherit Ast_traverse.map
  method! value_description x =
    { x with pval_attributes = to_ignore_mark_attr :: x.pval_attributes }
end

let wrap_functor_expression ~(arg : string loc) (structure : structure) : structure_item =
  let {txt = name; loc} = arg in
  let locate x = Location.mkloc x loc in
  let e_true = pexp_construct ~loc (locate (Longident.Lident "true")) None in
  let e_unit = pexp_construct ~loc (locate (Longident.Lident "()")) None in
  unit_value_user ~loc
    (pexp_ifthenelse ~loc e_true e_unit (Some (
       pexp_letmodule ~loc (locate "M") (
         pmod_functor ~loc (locate name)
           (Some (pmty_ident ~loc (locate (Longident.Lident name))))
           (pmod_structure ~loc structure))
         e_unit)))
;;

let rec prefix_longident (prefix : Longident.t) (lid : Longident.t) : Longident.t =
  match lid with
  | Lident s -> Ldot (prefix, s)
  | Ldot (id, x) -> Ldot (prefix_longident prefix id, x)
  | _ -> assert false
;;

let prefix_idents name vars =
  List.map vars ~f:(fun v -> { v with txt = prefix_longident name v.txt })
;;

let add_dummy_user_for_marked_values = object(self)
  inherit Ast_traverse.map as super

  method! expression e =
    match e.pexp_desc with
    | Pexp_letmodule (name, ({ pmod_desc = Pmod_constraint (me, mt); _ } as m), body) ->
      let me = self#module_expr me in
      let mt, vars = self#collect_marks_in_module_type mt in
      let vars = prefix_idents (lident name.txt) vars in
      let body = self#expression body in
      let body =
        List.fold_left vars ~init:body ~f:(fun acc var ->
          pexp_let ~loc:var.loc Nonrecursive
            [underscore_binding (pexp_ident ~loc:var.loc var)]
            acc)
      in
      let m = { m with pmod_desc = Pmod_constraint (me, mt) } in
      { e with pexp_desc = Pexp_letmodule (name, m, body) }
    | _ ->
      super#expression e

  method! structure st =
    let rec loop st =
      match st with
      | [] -> []
      | item :: rest ->
        match item.pstr_desc with
        | Pstr_modtype ({ pmtd_type = Some mt; _ } as mtd) ->
          let mod_name = mtd.pmtd_name in
          let mt, idents = self#collect_marks_in_module_type mt in
          let warnings_removal =
            add_ignore (prefix_idents (lident mod_name.txt) idents) []
          in
          let item =
            { item with
              pstr_desc = Pstr_modtype { mtd with pmtd_type = Some mt }
            }
          in
          if idents = [] then
            item :: loop rest
          else
            item
            :: wrap_functor_expression ~arg:mod_name warnings_removal
            :: loop rest

        | Pstr_module ({ pmb_expr = { pmod_desc = Pmod_constraint (me, mt); _ } as m
                       ; _ } as mb) ->
          let me = self#module_expr me in
          let mt, idents = self#collect_marks_in_module_type mt in
          let warnings_removal =
            add_ignore (prefix_idents (lident mb.pmb_name.txt) idents) []
          in
          let m = { m with pmod_desc = Pmod_constraint (me, mt) } in
          let mb = { mb with pmb_expr = m } in
          { item with pstr_desc = Pstr_module mb }
          :: warnings_removal
          @ loop rest

        | Pstr_include ({ pincl_mod = { pmod_desc = Pmod_constraint (me, mt); _ } as m
                        ; _ } as incl) ->
          let me = self#module_expr me in
          let mt, idents = self#collect_marks_in_module_type mt in
          let warnings_removal = add_ignore idents [] in
          let m = { m with pmod_desc = Pmod_constraint (me, mt) } in
          let incl = { incl with pincl_mod = m } in
          { item with pstr_desc = Pstr_include incl }
          :: warnings_removal
          @ loop rest

        | _ ->
          self#structure_item item :: loop rest
    in
    loop st

  method private fold_map_on_functor_arg warnings_removal me =
    match me.pmod_desc with
    | Pmod_functor (name, mt, me) ->
      (* wouldn't be quite right if you have a functor that takes several arguments with
         the same name, but who would do that anyway? *)
      let mt, idents =
        match mt with
        | None -> (None, [])
        | Some mt ->
          let mt, idents = self#collect_marks_in_module_type mt in
          (Some mt, idents)
      in
      let warnings_removal =
        warnings_removal @ add_ignore (prefix_idents (lident name.txt) idents) []
      in
      let me = self#fold_map_on_functor_arg warnings_removal me in
      { me with pmod_desc = Pmod_functor (name, mt, me) }
    | _ ->
      let me = super#module_expr me in
      match me.pmod_desc with
      | Pmod_structure str ->
        { me with pmod_desc = Pmod_structure (warnings_removal @ str) }
      | Pmod_constraint ({ pmod_desc = Pmod_structure str; _ } as me', mt) ->
        let me' = { me' with pmod_desc = Pmod_structure (warnings_removal @ str) } in
        { me with pmod_desc = Pmod_constraint (me', mt) }
      | _ ->
        (* not ignoring the warnings in this case because we don't even know if [me] is a
           functor or not, which makes it impossible to find a way of inserting
           [warnings_removal] *)
        me

  method! module_expr me =
    match me.pmod_desc with
    | Pmod_functor _ -> self#fold_map_on_functor_arg [] me
    | _ -> super#module_expr me

  (* Strip all the 'markers' that have not been handled *)
  method! value_description vb =
    if has_mark vb then
      remove_mark vb
    else
      vb

  method private collect_marks_in_module_type mt =
    match mt.pmty_desc with
    | Pmty_ident _
    | Pmty_typeof _
    | Pmty_extension _
    | Pmty_alias _
    | Pmty_functor _ ->
      (mt, [])
    | Pmty_signature sg ->
      let sg, vars = self#collect_marks_in_signature sg in
      ({ mt with pmty_desc = Pmty_signature sg }, vars)
    | Pmty_with (mt, wc) ->
      let mt, vars = self#collect_marks_in_module_type mt in
      ({ mt with pmty_desc = Pmty_with (mt, wc) }, vars)

  method private collect_marks_in_signature sg =
    let rec loop sg vars =
      match sg with
      | [] -> ([], vars)
      | item :: rest ->
        match item.psig_desc with
        | Psig_value vb when has_mark vb ->
          let rest, vars = loop rest vars in
          let item =
            { psig_desc = Psig_value (remove_mark vb)
            ; psig_loc  = item.psig_loc
            }
          in
          (item :: rest, Located.map lident vb.pval_name :: vars)
        | Psig_module md ->
          let mt, sub_vars = self#collect_marks_in_module_type md.pmd_type in
          let rest, vars = loop rest vars in
          let item =
            { psig_desc = Psig_module { md with pmd_type = mt }
            ; psig_loc  = item.psig_loc
            }
          in
          (item :: rest, vars @ prefix_idents (lident md.pmd_name.txt) sub_vars)
        | _ ->
          let rest, vars = loop rest vars in
          (item :: rest, vars)
    in
    loop sg []
end

let strip = object
  inherit Ast_traverse.map

  method! value_description vb =
    if has_mark vb then
      remove_mark vb
    else
      vb
end
