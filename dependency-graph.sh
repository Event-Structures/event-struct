#!/bin/sh

# The source code of this script was adapted from the snippet by Guillaume Melquiond:
# https://coq.discourse.group/t/tool-for-drawing-coq-project-dependency-graph/653/16
#
# This script generates a dependency graph file for the project.
# This is done via the following chain of transformations:
#                              coqdep                 dot
# _CoqProject (and .v files) ----------> .dot file ----------> .png file
#
# - `coqdep` is a standard utility distributed with Coq system
# - `dot` utility is distributed with `graphviz` utility collection
#    One can usually install it using a package manager like homebrew on macOS:
#    `brew install graphviz`

project_file=_CoqProject
name=dependency_graph

( echo "digraph interval_deps {" ;
  echo "node [shape=ellipse, style=filled, color=black];";
  ( coqdep -f ${project_file} ) |
    sed -n -e 's,/,.,g;s/[.]vo.*: [^ ]*[.]v//p' |
    while read src dst; do
      color=$(echo "$src" | sed -e 's,[a-zA-Z].*,white,')
      echo "\"$src\" [fillcolor=$color];"
      for d in $dst; do
        echo "\"$src\" -> \"${d%.vo}\" ;"
      done
    done;
  echo "}" ) | tred > ${name}.dot

dot -Gdpi=300 -T png ${name}.dot -o ${name}.png

# to generate pdf file simply do
# dot -T pdf ${dot_file} -o ${name}.pdf
