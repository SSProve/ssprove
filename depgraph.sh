#!/usr/bin/env bash

# Adapt to macOS (brew install gsed)
SED=`which gsed 2>/dev/null || which sed`

fn_project=_CoqProject
fn_out="dependencies"
base_style="rounded,filled"
# Some categorical color schemes recognised by dot: pastel19, set312
# http://www.graphviz.org/doc/info/colors.html#brewer
color_scheme=pastel19

function help_msg() {
    echo "`basename $0`: Print dependency graph for \"$fn_project\" according to coqdep."
    echo "Requires graphviz, coqdep, bash, and sed."
}
if ! [ -z $@ ] ; then
    help_msg ; exit 1
fi

( echo "digraph interval_deps {" ;
  echo 'node [shape=box, style="'$base_style'", URL="html/\N.html", colorscheme='$color_scheme'];';
  coqdep -vos -dyndep var -f $fn_project |
      # drop prefix, turn '/' into '.' ,
      $SED -n -e 's,theories/,,g' -e 's,/,.,g' \
          `# keep lines with [src].vo : [x].v [dst]* , drop [x].v` \
          -e 's/[.]vo.*: [^ ]*[.]v//p' |
      while read src dst; do
          # pick a color number based on the src node name
          color=$(echo "$src" | $SED -r \
                                    -e 's,Crypt[.]only_prob.*,2,' \
                                    -e 's,Crypt[.]package[.].*,3,' \
                                    -e 's,Crypt[.]state[.].*,4,' \
                                    -e 's,Crypt[.].*,5,' \
                                    -e 's,Mon[.].*,6,' \
                                    -e 's,Relational[.].*,7,' \
                                    -e 's,.*\..*,1,') # default
          echo "\"$src\" [fillcolor=$color];"
          for d in $dst; do
              echo "\"$src\" -> \"${d%.vo*}\" ;"
          done
      done;
  echo "}" ) |
    # transitively reduce graph
    tred |
    # double border around modules without further prerequisites
    gvpr -c 'N[outdegree == 0]{shape="doubleoctagon"}' |
    # fat border around modules without clients
    gvpr -c 'N[indegree == 0]{penwidth=3}' > $fn_out.dot

dot -T svg $fn_out.dot > $fn_out.svg
# dot -T png $fn_out.dot > $fn_out.png
# dot -T cmap $fn_out.dot | $SED -e 's,>$,/>,' > $fn_out.map
