(* Pa_type_conv: Preprocessing Module for Registering Type Conversions *)

open StdLabels
open MoreLabels
open Ppx_core.Std
open Ast_builder.Default
open Asttypes
open Parsetree

module Spellcheck = Ppx_core.Spellcheck
module String_set = Set.Make (String)

module List = struct
  include List
  let concat_map xs ~f = concat (map xs ~f)
end

[@@@metaloc loc]

module Args = struct
  include (Ast_pattern : module type of struct include Ast_pattern end
           with type ('a, 'b, 'c) t := ('a, 'b, 'c) Ast_pattern.t)

  type 'a param =
    { name    : string
    ; pattern : (expression, 'a) Ast_pattern.Packed.t
    ; default : 'a
    }

  let arg name pattern =
    { name
    ; default = None
    ; pattern = Ast_pattern.Packed.create pattern (fun x -> Some x)
    }
  ;;

  let flag name =
    let pattern = pexp_ident (lident (string name)) in
    { name
    ; default = false
    ; pattern = Ast_pattern.Packed.create pattern true
    }
  ;;

  type (_, _) t =
    | Nil  : ('m, 'm) t
    | Cons : ('m1, 'a -> 'm2) t * 'a param -> ('m1, 'm2) t

  let empty = Nil
  let ( +> ) a b = Cons (a, b)

  let rec names : type a b. (a, b) t -> string list = function
    | Nil -> []
    | Cons (t, p) -> p.name :: names t
  ;;

  module Instance = struct
    type (_, _) instance =
      | I_nil  : ('m, 'm) instance
      | I_cons : ('m1, 'a -> 'm2) instance * 'a -> ('m1, 'm2) instance

    let rec create
      : type a b. (a, b) t -> (string * expression) list -> (a, b) instance
      = fun spec args ->
        match spec with
        | Nil -> I_nil
        | Cons (t, p) ->
          let value =
            match List.assoc p.name args with
            | exception Not_found -> p.default
            | expr -> Ast_pattern.Packed.parse p.pattern expr.pexp_loc expr
          in
          I_cons (create t args, value)
    ;;

    let rec apply : type a b. (a, b) instance -> a -> b = fun t f ->
      match t with
      | I_nil -> f
      | I_cons (t, x) -> apply t f x
    ;;
  end

  let apply t args f = Instance.apply (Instance.create t args) f
end

(* +-----------------------------------------------------------------+
   | Generators                                                      |
   +-----------------------------------------------------------------+ *)

module Export_intf = struct
  type ('output_ast, 'input_ast) ppx_deriving_generator
    =  options:(string * expression) list
    -> path:string list
    -> 'input_ast
    -> 'output_ast

  module type Ppx_deriving = sig
    type deriver
    val create
      : string
      -> ?core_type    :(core_type -> expression)
      -> ?type_ext_str :(structure, type_extension       ) ppx_deriving_generator
      -> ?type_ext_sig :(signature, type_extension       ) ppx_deriving_generator
      -> ?type_decl_str:(structure, type_declaration list) ppx_deriving_generator
      -> ?type_decl_sig:(signature, type_declaration list) ppx_deriving_generator
      -> unit
      -> deriver
    val register : deriver -> unit
  end
end

module Generator = struct
  type ('a, 'b, 'c) unpacked =
    { spec           : ('c, 'a) Args.t
    ; gen            : loc:Location.t -> path:string -> 'b -> 'c
    ; arg_names      : String_set.t
    ; attributes     : Attribute.packed list
    }

  type ('a, 'b) t = T : ('a, 'b, _) unpacked -> ('a, 'b) t

  let make ?(attributes=[]) spec gen =
    let arg_names =
      List.fold_left (Args.names spec) ~init:String_set.empty
        ~f:(fun set name -> String_set.add name set)
    in
    T { spec
      ; gen
      ; arg_names
      ; attributes
      }
  ;;

  let make_noarg ?attributes gen = make ?attributes Args.empty gen

  let check_arguments t name (args : (string * expression) list) =
    List.iter args ~f:(fun (label, e) ->
      if label = "" then
        Location.raise_errorf ~loc:e.pexp_loc
          "ppx_type_conv: generator arguments must be labelled");
    ignore (
      List.fold_left args ~init:String_set.empty ~f:(fun set (label, e) ->
        if String_set.mem label set then
          Location.raise_errorf ~loc:e.pexp_loc
            "ppx_type_conv: argument labelled '%s' appears more than once" label;
        String_set.add label set)
      : String_set.t
    );
    List.iter args ~f:(fun (label, e) ->
      if not (String_set.mem label t.arg_names) then
        let spellcheck_msg =
          match Spellcheck.spellcheck (String_set.elements t.arg_names) label with
          | None -> ""
          | Some s -> ".\n" ^ s
        in
        Location.raise_errorf ~loc:e.pexp_loc
          "ppx_type_conv: generator '%s' doesn't accept argument '%s'%s"
          name label spellcheck_msg);
  ;;

  let apply (T t) ~name ~loc ~path x args =
    check_arguments t name args;
    Args.apply t.spec args (t.gen ~loc ~path x)
  ;;

  let apply_all ?(rev=false) ~loc ~path entry (name, generators, args) =
    let results =
      if rev
      then
        (* Map actual_generators right->left so side effects (gensym) match camlp4 *)
        List.rev generators
        |> List.map ~f:(fun t -> apply t ~name:name.txt ~loc ~path entry args)
        |> List.rev
      else
        generators
        |> List.map ~f:(fun t -> apply t ~name:name.txt ~loc ~path entry args)
    in
    List.concat results
  ;;

  let apply_all ?rev ~loc ~path entry generators =
    let generators = List.rev generators in
    List.concat_map generators ~f:(apply_all ?rev ~loc ~path entry)
  ;;
end

type t = string
let ignore (_ : t) = ()

module Deriver = struct
  module Actual_deriver = struct
    type t =
      { name          : string
      ; str_type_decl : (structure, rec_flag * type_declaration list) Generator.t option
      ; str_type_ext  : (structure, type_extension                  ) Generator.t option
      ; str_exception : (structure, extension_constructor           ) Generator.t option
      ; sig_type_decl : (signature, rec_flag * type_declaration list) Generator.t option
      ; sig_type_ext  : (signature, type_extension                  ) Generator.t option
      ; sig_exception : (signature, extension_constructor           ) Generator.t option
      ; extension     : (loc:Location.t -> path:string -> core_type -> expression) option
      }
  end

  module Alias = struct
    type t =
      { str_type_decl : string list
      ; str_type_ext  : string list
      ; str_exception : string list
      ; sig_type_decl : string list
      ; sig_type_ext  : string list
      ; sig_exception : string list
      }
  end

  module Field = struct
    type kind = Str | Sig

    type ('a, 'b) t =
      { name    : string
      ; kind    : kind
      ; get     : Actual_deriver.t -> ('a, 'b) Generator.t option
      ; get_set : Alias.t -> string list
      }

    let str_type_decl = { kind = Str; name = "type"
                        ; get     = (fun t -> t.str_type_decl)
                        ; get_set = (fun t -> t.str_type_decl) }
    let str_type_ext  = { kind = Str; name = "type extension"
                        ; get     = (fun t -> t.str_type_ext)
                        ; get_set = (fun t -> t.str_type_ext ) }
    let str_exception = { kind = Str; name = "exception"
                        ; get     = (fun t -> t.str_exception)
                        ; get_set = (fun t -> t.str_exception) }
    let sig_type_decl = { kind = Sig; name = "signature type"
                        ; get     = (fun t -> t.sig_type_decl)
                        ; get_set = (fun t -> t.sig_type_decl) }
    let sig_type_ext  = { kind = Sig; name = "signature type extension"
                        ; get     = (fun t -> t.sig_type_ext)
                        ; get_set = (fun t -> t.sig_type_ext ) }
    let sig_exception = { kind = Sig; name = "signature exception"
                        ; get     = (fun t -> t.sig_exception)
                        ; get_set = (fun t -> t.sig_exception) }
  end

  type t =
    | Actual_deriver of Actual_deriver.t
    | Alias of Alias.t

  let all : (string, t) Hashtbl.t = Hashtbl.create 42

  let map_expression path e =
    match e with
    | { pexp_desc = Pexp_extension (name, PTyp typ); _ } ->
      begin match Hashtbl.find all name.txt with
      | exception Not_found -> e
      | Alias _ -> e
      | Actual_deriver drv ->
        match drv.extension with
        | None -> e
        | Some f ->
          let e' = f ~loc:e.pexp_loc ~path typ in
          { e' with pexp_attributes = e'.pexp_attributes @ e.pexp_attributes }
      end
    | _ -> e
  ;;

  exception Not_supported of string

  let resolve_internal (field : (_, _) Field.t) name =
    let rec loop name collected =
      if List.exists collected ~f:(fun (d : Actual_deriver.t) -> d.name = name) then
        collected
      else
        match Hashtbl.find all name with
        | Actual_deriver drv -> drv :: collected
        | Alias alias ->
          let set = field.get_set alias in
          List.fold_right set ~init:collected ~f:loop
        | exception Not_found -> raise (Not_supported name)
    in
    let actual_derivers_rev = loop name [] in
    List.rev_map actual_derivers_rev ~f:(fun drv ->
      match field.get drv with
      | None -> raise (Not_supported name)
      | Some g -> g)
  ;;

  let supported_for field =
    Hashtbl.fold all ~init:String_set.empty
      ~f:(fun ~key ~data:_ acc ->
        match resolve_internal field key with
        | _ -> String_set.add key acc
        | exception Not_supported _ -> acc)
    |> String_set.elements
  ;;

  let not_supported (field : (_, _) Field.t) ?(spellcheck=true) name =
    let spellcheck_msg =
      if spellcheck then
        match Spellcheck.spellcheck (supported_for field) name.txt with
        | None -> ""
        | Some s -> ".\n" ^ s
      else
        ""
    in
    Location.raise_errorf ~loc:name.loc
      "ppx_type_conv: '%s' is not a supported %s type-conv generator%s"
      name.txt field.name spellcheck_msg
  ;;

  let resolve field name =
    try
      resolve_internal field name.txt
    with Not_supported name' ->
      not_supported field ~spellcheck:(name.txt = name') name
  ;;

  let resolve_all field derivers =
    List.map derivers ~f:(fun (name, args) ->
      (name, resolve field name, args))
  ;;

  let export (module Ppx_deriving : Export_intf.Ppx_deriving) name =
    let resolve_opt field =
      match resolve_internal field name with
      | generators                  -> Some generators
      | exception (Not_supported _) -> None
    in
    let str_type_decl = resolve_opt Field.str_type_decl in
    let str_type_ext  = resolve_opt Field.str_type_ext  in
    let sig_type_decl = resolve_opt Field.sig_type_decl in
    let sig_type_ext  = resolve_opt Field.sig_type_ext  in
    let map_option o ~f =
      match o with
      | None -> None
      | Some x -> Some (f x)
    in
    let core_type =
      match Hashtbl.find all name with
      | Alias _ -> None
      | Actual_deriver drv ->
        map_option drv.extension ~f:(fun f ->
          fun ty -> f ty ~loc:ty.ptyp_loc ~path:"")
    in
    let import_path l = String.concat l ~sep:"." in
    let make_type_decl gens =
      map_option gens ~f:(fun gens ->
        fun ~options ~path tds ->
          let path = import_path path in
          List.concat_map gens ~f:(fun gen ->
            Generator.apply gen ~name ~loc:Location.none ~path (Recursive, tds) options))
    in
    let make_type_ext gens =
      map_option gens ~f:(fun gens ->
        fun ~options ~path te ->
          let path = import_path path in
          List.concat_map gens ~f:(fun gen ->
            Generator.apply gen ~name ~loc:Location.none ~path te options))
    in
    let type_decl_str = make_type_decl str_type_decl in
    let type_decl_sig = make_type_decl sig_type_decl in
    let type_ext_str  = make_type_ext  str_type_ext  in
    let type_ext_sig  = make_type_ext  sig_type_ext  in
    Ppx_deriving.register
      (Ppx_deriving.create name
         ?core_type
         ?type_ext_str
         ?type_ext_sig
         ?type_decl_str
         ?type_decl_sig
         ())
  ;;

  let ppx_deriving_implementation = ref None

  let set_ppx_deriving_implementation impl =
    ppx_deriving_implementation := Some impl;
    Hashtbl.iter all ~f:(fun ~key ~data:_ -> export impl key)
  ;;

  let safe_add id t =
    if Hashtbl.mem all id then
      failwith ("ppx_type_conv: generator '" ^ id ^ "' defined multiple times")
    else
      Hashtbl.add all ~key:id ~data:t;
    match !ppx_deriving_implementation with
    | None -> ()
    | Some impl -> export impl id
  ;;

  let add
        ?str_type_decl
        ?str_type_ext
        ?str_exception
        ?sig_type_decl
        ?sig_type_ext
        ?sig_exception
        ?extension
        name
    =
    let actual_deriver : Actual_deriver.t =
      { name
      ; str_type_decl
      ; str_type_ext
      ; str_exception
      ; sig_type_decl
      ; sig_type_ext
      ; sig_exception
      ; extension
      }
    in
    safe_add name (Actual_deriver actual_deriver);
    (match extension with
     | None -> ()
     | Some _ ->
       (* For the spellcheck *)
       let _ : _ Extension.Expert.t =
         Extension.Expert.declare name Extension.Context.expression
           Ast_pattern.(ptyp __) (fun _ -> assert false)
       in
       ());
    name
  ;;

  let add_alias
        name
        ?str_type_decl
        ?str_type_ext
        ?str_exception
        ?sig_type_decl
        ?sig_type_ext
        ?sig_exception
        set
    =
    let alias : Alias.t =
      let get = function
        | None     -> set
        | Some set -> set
      in
      { str_type_decl = get str_type_decl
      ; str_type_ext  = get str_type_ext
      ; str_exception = get str_exception
      ; sig_type_decl = get sig_type_decl
      ; sig_type_ext  = get sig_type_ext
      ; sig_exception = get sig_exception
      }
    in
    safe_add name (Alias alias);
    name
  ;;
end

let add       = Deriver.add
let add_alias = Deriver.add_alias

(* +-----------------------------------------------------------------+
   | [@@deriving ] parsing                                           |
   +-----------------------------------------------------------------+ *)

let invalid_with ~loc = Location.raise_errorf ~loc "invalid [@@deriving ] attribute syntax"

let generator_name_of_id loc id =
  match Longident.flatten id with
  | l -> { loc; txt = String.concat ~sep:"." l }
  | exception _ -> invalid_with ~loc:loc
;;

let mk_deriving_attr context =
  Attribute.declare
    "type_conv.deriving"
    context
    Ast_pattern.(
      let label =
        map' __ ~f:(fun loc f label ->
          if label = "" || label.[0] = '?' then
            Location.raise_errorf ~loc "non-optional labeled argument expected"
          else
            f label)
      in
      let generator_name () =
        map' (pexp_ident __) ~f:(fun loc f id -> f (generator_name_of_id loc id))
      in
      let arg = pack2 (label ** __) in
      let generator () =
        map (generator_name ()) ~f:(fun f x -> f (x, [])) |||
        pack2 (pexp_apply (generator_name ()) (many arg))
      in
      let generators =
        pexp_tuple (many (generator ())) |||
        map (generator ()) ~f:(fun f x -> f [x])
      in
      pstr (pstr_eval generators nil ^:: nil)
    )
    (fun x -> x)
;;

let deriving_attr_td = mk_deriving_attr Attribute.Context.type_declaration
let deriving_attr_te = mk_deriving_attr Attribute.Context.type_extension
let deriving_attr_ec = mk_deriving_attr Attribute.Context.extension_constructor

let get_derivers_tds field tds =
  let rec loop tds =
    match tds with
    | [] -> ([], [])
    | td :: tds ->
      let td, gens =
        match Attribute.consume deriving_attr_td td with
        | None -> (td, [])
        | Some x -> x
      in
      let tds, gens' = loop tds in
      (td :: tds, gens @ gens')
  in
  match loop tds with
  | _  , []   -> None
  | tds, gens -> Some (tds, Deriver.resolve_all field gens)
;;

let get_str_type_decl_derivers = get_derivers_tds Deriver.Field.str_type_decl
let get_sig_type_decl_derivers = get_derivers_tds Deriver.Field.sig_type_decl

let get_derivers attr field x =
  match Attribute.consume attr x with
  | None           -> None
  | Some (x, drvs) -> Some (x, Deriver.resolve_all field drvs)
;;

let get_str_type_ext_derivers  = get_derivers deriving_attr_te Deriver.Field.str_type_ext
let get_sig_type_ext_derivers  = get_derivers deriving_attr_te Deriver.Field.sig_type_ext
let get_str_exception_derivers = get_derivers deriving_attr_ec Deriver.Field.str_exception
let get_sig_exception_derivers = get_derivers deriving_attr_ec Deriver.Field.sig_exception

let get_rec_flag tds =
  let has_nonrec td =
    List.exists td.ptype_attributes ~f:(fun (name, _) -> name.txt = "nonrec")
  in
  if List.exists tds ~f:has_nonrec then
    Nonrecursive
  else
    Recursive
;;

(* +-----------------------------------------------------------------+
   | Unused warning stuff                                            |
   +-----------------------------------------------------------------+ *)

(* [do_insert_unused_warning_attribute] -- If true, generated code contains compiler
   attribute to disable unused warnings, instead of inserting [let _ = ... ].
   We wont enable this yet, otherwise it will make it much harder to compare the code
   generated by ppx with that of the pa version *)
let do_insert_unused_warning_attribute = false

let disable_unused_warning_attribute ~loc =
  ({ txt = "ocaml.warning"; loc }, PStr [%str "-32"])
;;

let disable_unused_warning_str ~loc st =
  if not do_insert_unused_warning_attribute then
    Ignore_unused_warning.add_dummy_user_for_values#structure st
  else
    [pstr_include ~loc
       (include_infos ~loc
          (pmod_structure ~loc
             (pstr_attribute ~loc (disable_unused_warning_attribute ~loc)
              :: st)))]
;;

let disable_unused_warning_sig ~loc sg =
  [psig_include ~loc
     (include_infos ~loc
        (pmty_signature ~loc
           (psig_attribute ~loc (disable_unused_warning_attribute ~loc)
            :: sg)))]
;;

(* +-----------------------------------------------------------------+
   | Remove attributes used by syntax extensions                     |
   +-----------------------------------------------------------------+ *)

let remove generators =
  let attributes =
    List.concat_map generators ~f:(fun (_, actual_generators, _) ->
      List.concat_map actual_generators ~f:(fun (Generator.T g) -> g.attributes))
  in
  object
    inherit Ast_traverse.map

    (* Don't recurse through attributes and extensions *)
    method! attribute x = x
    method! extension x = x

    method! label_declaration ld =
      Attribute.remove_seen Attribute.Context.label_declaration attributes ld

    method! constructor_declaration cd =
      Attribute.remove_seen Attribute.Context.constructor_declaration attributes cd
  end

(* +-----------------------------------------------------------------+
   | Main expansion                                                  |
   +-----------------------------------------------------------------+ *)

let types_used_by_type_conv (tds : type_declaration list)
    : structure_item list =
  List.map tds ~f:(fun td ->
    let typ = core_type_of_type_declaration td in
    let loc = td.ptype_loc in
    [%stri let _ = fun (_ : [%t typ]) -> () ]
  )

let expand_with_defs = object
  inherit Ast_traverse.map_with_path as super

  method! module_expr_desc path me =
    match me with
    | Pmod_constraint (me, mt) ->
      let mt = super#module_type path mt in
      let me = super#module_expr path me in
      Pmod_constraint (me, mt)
    | _ -> super#module_expr_desc path me

  method! expression path e =
    Deriver.map_expression path (super#expression path e)

  method! structure path st =
    List.concat_map st ~f:(fun item ->
      let item = super#structure_item path item in
      let loc = item.pstr_loc in
      match item.pstr_desc with
      | Pstr_type tds ->
        begin match get_str_type_decl_derivers tds with
        | None -> [item]
        | Some (tds, generators) ->
          let rec_flag = get_rec_flag tds in
          let generated =
            types_used_by_type_conv tds
            @ Generator.apply_all ~rev:true ~loc ~path (rec_flag, tds) generators;
          in
          let tds = List.map tds ~f:(remove generators)#type_declaration in
          let item = { item with pstr_desc = Pstr_type tds } in
          item :: disable_unused_warning_str ~loc generated
        end

      | Pstr_exception ec ->
        begin match get_str_exception_derivers ec with
        | None -> [item]
        | Some (ec, generators) ->
          let generated = Generator.apply_all ~rev:true ~loc ~path ec generators in
          let ec = (remove generators)#extension_constructor ec in
          let item = { item with pstr_desc = Pstr_exception ec } in
          item :: disable_unused_warning_str ~loc generated
        end

      | Pstr_typext te ->
        begin match get_str_type_ext_derivers te with
        | None -> [item]
        | Some (te, generators) ->
          let generated = Generator.apply_all ~rev:true ~loc ~path te generators in
          let te = (remove generators)#type_extension te in
          let item = { item with pstr_desc = Pstr_typext te } in
          item :: disable_unused_warning_str ~loc generated
        end

      | _ ->
        [item]
    )

  method! signature path sg =
    List.concat_map sg ~f:(fun item ->
      let item = super#signature_item path item in
      let loc = item.psig_loc in
      match item.psig_desc with
      | Psig_type tds ->
        begin match get_sig_type_decl_derivers tds with
        | None -> [item]
        | Some (tds, generators) ->
          let rec_flag = get_rec_flag tds in
          let generated = Generator.apply_all ~loc ~path (rec_flag, tds) generators in
          let tds = List.map tds ~f:(remove generators)#type_declaration in
          let item = { item with psig_desc = Psig_type tds } in
          item :: disable_unused_warning_sig ~loc generated
        end

      | Psig_exception ec ->
        begin match get_sig_exception_derivers ec with
        | None -> [item]
        | Some (ec, generators) ->
          let generated = Generator.apply_all ~loc ~path ec generators in
          let ec = (remove generators)#extension_constructor ec in
          let item = { item with psig_desc = Psig_exception ec } in
          item :: disable_unused_warning_sig ~loc generated
        end

      | Psig_typext te ->
        begin match get_sig_type_ext_derivers te with
        | None -> [item]
        | Some (te, generators) ->
          let generated = Generator.apply_all ~loc ~path te generators in
          let te = (remove generators)#type_extension te in
          let item = { item with psig_desc = Psig_typext te } in
          item :: disable_unused_warning_sig ~loc generated
        end

      | _ ->
        [item]
    )
end

let main_mapper_str st =
  let path = File_path.get_default_path_str st in
  expand_with_defs #structure path st
;;

let main_mapper_sig sg =
  let path = File_path.get_default_path_sig sg in
  expand_with_defs #signature path sg
;;

let () =
  Ppx_driver.register_transformation "type_conv"
    ~impl:main_mapper_str
    ~intf:main_mapper_sig
;;

module Ppx_deriving_exporter = struct
  include Export_intf
  let set = Deriver.set_ppx_deriving_implementation
end
