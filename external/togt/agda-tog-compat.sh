#!/bin/sh

set -e

stack exec --rts-options "-s" agda -- -iexamples -iagda-prelude --type-in-type --without-K --no-termination-check --ignore-interfaces --no-positivity-check $@
