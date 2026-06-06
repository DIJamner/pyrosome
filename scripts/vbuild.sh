#!/usr/bin/env bash
# Compile a single OTT .v file directly with rocq (bypasses make staleness).
set -e
rocq compile \
  -R /root/pyrosome-ai-2/coqutil/src/coqutil coqutil \
  -R /root/pyrosome-ai-2/canonical-binary-tries/ Tries \
  -R /root/pyrosome-ai-2/src/Utils Utils \
  -R /root/pyrosome-ai-2/src/Pyrosome Pyrosome \
  "$1"
