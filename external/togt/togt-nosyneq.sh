#!/bin/sh

set -e

stack exec --rts-options "-s" tog -- --synEquality 0 --solver W --noCheckElaborated --fastElaborate --termType HC4 $@
