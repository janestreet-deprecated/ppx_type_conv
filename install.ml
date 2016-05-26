#use "topfind";;
#require "js-build-tools.oasis2opam_install";;

open Oasis2opam_install;;

generate ~package:"ppx_type_conv"
  [ oasis_lib "ppx_type_conv"
  ; oasis_lib "ppx_type_conv_deriving"
  ; file "META" ~section:"lib"
  ]
