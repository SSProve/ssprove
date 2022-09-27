#!/bin/bash
# test deextraction of all .jazz in this folder, note that their corresponding .v will be overwritten

# assuming jasmin is in home directory
for f in *.jazz
do
if [ $f != "aes.jazz" ]
then
    JASMINC=~/jasmin/compiler/jasminc.byte ./gen_ast.sh $f
    coqc $(basename $f .jazz).v
fi
done

JASMINC=~/jasmin/compiler/jasminc.byte ./gen_ast.sh aes '-I AES:../examples'
coqc aes.v
