#!/bin/sh
mkdir -p rmns
cp -f bin1.obf obf.scm README run.sh rmns/
tar cvf rmns.tar rmns/
