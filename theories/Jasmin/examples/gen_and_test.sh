#!/bin/bash
# test deextraction of all .jazz in this folder, note that their corresponding .v will be overwritten

JASMINC=${JASMINC:-$(which jasminc)}

# assuming jasmin is in home directory
for f in *.jazz
do
    echo $f
    $JASMINC -I AES:../examples -coq $f > $(basename $f .jazz).v
    # JASMINC=~/jasmin/compiler/jasminc.byte ./gen_ast.sh $f
    cd ../../..
    coqc -Q theories/Mon Mon \
	 -Q theories/Relational Relational \
	 -Q theories/Crypt Crypt \
	 -Q theories/Jasmin JasminSSProve \
	 theories/Jasmin/examples/"$(basename $f .jazz)".v
    cd -
done
