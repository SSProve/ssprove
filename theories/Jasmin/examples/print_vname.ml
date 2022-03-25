open Format

let print_vname (fmt : formatter) (t : Obj.t) =
  let t = Obj.magic t in
  ignore (List.map (pp_print_char fmt) t)
