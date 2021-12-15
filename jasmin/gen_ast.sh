#!/bin/bash

echo "open Format

let print_vname (fmt : formatter) (t : Obj.t) =
  let t = Obj.magic t in
  ignore (List.map (pp_print_char fmt) t)" > print_vname.ml

ocamlc -c print_vname.ml

name=$(basename "${1}" .jazz)
echo $name

mkdir $name

echo -n "Require Import List.
From Jasmin Require Import expr.
From Jasmin Require Import x86_extra.

Import ListNotations.
Local Open Scope string.

Definition ${name} :=" > $name/$name.v

(ocamldebug $(which jasminc.byte) <<EOF
load_printer "print_vname.cmo"
install_printer Print_vname.print_vname
set arguments $name.jazz
set print_length 10000
set print_depth 10000
break @Jasmin.Main_compiler 179
run
print cprog
EOF
) > $name/$name.cprog

sed -i '9,$!d;$d' $name/$name.cprog

sed 's/Jasmin\.[[:graph:]]*\.//g; s/Coq_//g ; s/=/:=/g ; s/{/{| /g ; s/}/ |}/g ; s/[[:graph:]]*\.[[:graph:]]*/"&"/g ; s/()/tt/g ;/./{H;$!d}; x ; :rename_balanced ; s/(\([^(),@]*\))/<<\1>>/g ; t rename_balanced ; :rename_pairs1 ; s/\([{([|,;][ \t\n]*([^(),]*\),/\1%/g; t rename_pairs1 ; :rename_pairs ; s/\([{([|,;][ \t\n]*\)(\([^(),]*\))/\1<<\2>>/g; t rename_balanced ; :rename_curries1 ; s/\([^{([|,;][ \t\n]*([^()]*\),/\1@/g; t rename_curries1; :rename_curries ; s/\([^{([|,;][ \t\n]*\)(\([^(),]*\))/\1++\2##/g; t rename_balanced; :uncurry ; s/\([^{([|,;][ \t\n]*++[^(),]*\)@\([ \t\n]*\)/\1##\2++/g ; t uncurry s/\([^{([|][ \t\n]*++[^(),]*\)@\([ \t\n]*\)/\1##\2++/g ; t uncurry ; s/<</(/g ; s/>>/)/g ; s/##/)/g ; s/++/(/g ; s/%/,/g ; s/@/,/g' $name/$name.cprog >> $name/$name.v

echo -n "." >> $name/$name.v

mv $name.jazz $name
