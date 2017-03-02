#!/bin/sh

set -e
mosmlc -c -toplevel basis2002.sml
mosmlc -c basis2002.ui Systeml.sig
mosmlc -c basis2002.ui Systeml.sml
mosmlc -c basis2002.ui Holdep_tokens.sig
mosmlc -c basis2002.ui Holdep_tokens.sml
mosmlc -c basis2002.ui holdeptool.sml
mosmlc -c basis2002.ui mosml_holdeptool.sml
mosmlc -c Holdep.sig
mosmlc -c basis2002.ui Holdep.sml
mosmlc -c regexpMatch.sig
mosmlc -c basis2002.ui regexpMatch.sml
mosmlc -c parse_glob.sig
mosmlc -c basis2002.ui parse_glob.sml
mosmlc -c internal_functions.sig
mosmlc -c basis2002.ui internal_functions.sml
mosmlc -c basis2002.ui Holmake_types.sig
mosmlc -c basis2002.ui Holmake_types.sml
mosmlc -o holdeptool.exe mosml_holdeptool.uo
mosmlc -c basis2002.ui Holmake_tools.sig
mosmlc -c basis2002.ui Holmake_tools.sml
mosmlc -c ReadHMF.sig
mosmlc -c basis2002.ui ReadHMF.sml
mosmlc -c basis2002.ui Holmake.sml
mosmlc -o Holmake Holmake.uo
cp Holmake ../../bin
