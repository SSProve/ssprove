#!/bin/bash

# you might have install the perl module Regexp::Common via cpan

# set path to jasminc.byte on command line by invoking the script with
# JASMINC=... ./gen_ast.sh foo.jazz
# JASMINC=${JASMINC:-$(which jasminc.byte)}

# use this variable to e.g. include paths
# e.g.: ./gen_ast.sh aes '-I AES:../examples'
OPTS=${2}
echo $OPTS
echo "open Format

let print_vname (fmt : formatter) (t : Obj.t) =
  let t = Obj.magic t in
  ignore (List.map (pp_print_char fmt) t)" > print_vname.ml

ocamlc -c print_vname.ml

name=$(basename "${1}" .jazz)
echo $name

echo -n "Require Import List.
From Jasmin Require Import expr.
From Jasmin Require Import x86_extra.

Import ListNotations.
Local Open Scope string.

Definition ${name} :=" > $name.v

(ocamldebug $JASMINC <<EOF
load_printer "print_vname.cmo"
install_printer Print_vname.print_vname
set arguments $name.jazz $OPTS
set print_length 100000
set print_depth 100000
break @Jasmin.Main_compiler 246
run
print cprog
EOF
) > $name.cprog

# delete all but the 12 first lines and then delete the last line
sed -i '12,$!d;$d' $name.cprog

perl -0777 deextract.pl $name.cprog >> $name.v

echo -n "." >> $name.v
