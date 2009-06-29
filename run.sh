#!/bin/sh

echo "Ctrl-C to stop gnuplot after finishing"

ypsilon obf.scm | gnuplot
