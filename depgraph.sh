# Script adapted from https://discourse.rocq-prover.org/t/tool-for-drawing-coq-project-dependency-graph/653/16
( echo "digraph interval_deps {" ;
  echo "node [shape=ellipse, style=filled, URL=\"html/ITree.html\"];";
  ( coqdep $(cat _CoqProject.itree) ) |
    sed -n -e 's,theories/,,g;s,[^ ]*worker,,g;s,/,.,g;s/[.]vo.*: [^ ]*[.]v//p' |
    while read src dst; do
      color=$(echo "$src" | sed -e 's,Eq.*,turquoise,;s,Basics[.].*,plum,;s,Handler.*,lightcoral,;s,Core.*,yellow,;s,Indexed.*,cornflowerblue,;s,Interp.*,green,;s,Events.*,orange,;s,Props.*,olive,;s,[A-Z].*,white,')
      echo "\"$src\" [fillcolor=$color];"
      for d in $dst; do
        echo "\"$src\" -> \"${d%.vo}\" ;"
      done
    done;
  echo "}" ) | tred > deps.dot
dot -T png deps.dot > deps.png
# dot -T cmap deps.dot | sed -e 's,>$,/>,' > deps.map
