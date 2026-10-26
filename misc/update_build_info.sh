#!/bin/sh
## Generates build_info.txt, which records version information for CakeML
## and HOL4.
## It only updates build_info.txt if necessary; updates can be disabled by
## setting the environment variable CML_FREEZE_BUILD_INFO.

## This script is called from the Holmakefile with HOLDIR as its argument.
## In addition to maintaining build_info.txt, it prints its name on success
## (and nothing on failure), determining whether Holmake sees it as a
## dependency.

# On failure, nothing will be printed => Holmake will not see build_info.txt
cd "$(dirname "$0")" || exit 0

out=build_info.txt

if [ -n "$CML_FREEZE_BUILD_INFO" ] && [ -f "$out" ]; then
  echo "CML_FREEZE_BUILD_INFO is set, so misc/$out is not updated" >&2
  echo "$out"
  exit 0
fi

# git_info PREFIX DIR prints the commit, tag, commit date and whether the
# worktree is dirty as key=value lines for the checkout at DIR.
# Values that cannot be determined are left empty.
git_info () {
  prefix="$1"
  dir="$2"
  commit=
  tag=
  date=
  dirty=
  if [ -n "$dir" ] &&
     commit=$(git -C "$dir" rev-parse --verify -q HEAD 2>/dev/null)
  then
    tag=$(git -C "$dir" describe --tags --exact-match HEAD 2>/dev/null) || tag=
    date=$(TZ=UTC git -C "$dir" show -s --format=%cd \
             --date=format-local:'%Y-%m-%d %H:%M:%S UTC' HEAD 2>/dev/null) ||
      date=
    if status=$(git -C "$dir" --no-optional-locks status --porcelain \
                  --untracked-files=normal 2>/dev/null)
    then
      if [ -n "$status" ]; then dirty=1; else dirty=0; fi
    fi
  fi
  printf '%s_commit=%s\n%s_tag=%s\n%s_date=%s\n%s_dirty=%s\n' \
    "$prefix" "$commit" "$prefix" "$tag" "$prefix" "$date" "$prefix" "$dirty"
}

info=$(git_info cakeml . ; git_info hol "$1")
tmp=$(mktemp "$out.tmp.XXXXXX") || exit 0
printf '%s\n' "$info" > "$tmp"
chmod 644 "$tmp"
if cmp -s "$tmp" "$out"; then
  rm -f "$tmp"
else
  mv -f "$tmp" "$out"
fi
echo "$out"
exit 0
