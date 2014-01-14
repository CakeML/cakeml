#!/bin/sh
set -e
if [ -f compileReplDecsCheat.sml ]; then
  mv compileReplDecsCheat.sml compileReplDecsScript.sml
  echo "now cheating (do not commit)"
else
  git checkout -- compileReplDecsScript.sml
  git checkout -- compileReplDecsCheat.sml
  echo "now not cheating"
fi
