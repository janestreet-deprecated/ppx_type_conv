Ppx_type_conv.Std.Type_conv.Ppx_deriving_exporter.set
  (module struct
    type deriver = Ppx_deriving.deriver

    let create
          name
          ?core_type
          ?type_ext_str
          ?type_ext_sig
          ?type_decl_str
          ?type_decl_sig
          ()
      =
      Ppx_deriving.create
        name
        ?core_type
        ?type_ext_str
        ?type_ext_sig
        ?type_decl_str
        ?type_decl_sig
        ()
    ;;

    let register deriver = Ppx_deriving.register deriver
  end)
