#!/bin/sh

set -e

stack exec --rts-options "-s" tog -- --synEquality 2 --physicalEquality --solver W --noCheckElaborated --fastElaborate --termType HC4 $@
