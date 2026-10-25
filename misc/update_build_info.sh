#!/bin/sh
## Records the CakeML and HOL4 commits, their tags (if a tag points at the
## commit), their commit dates in UTC, and whether their worktrees have
## uncommitted or untracked changes in build_info.txt, which buildInfoLib
## reads. The file is only replaced when its contents change, so that Holmake
## rebuilds dependents of buildInfoLib only when this information changes.
## Setting CML_FREEZE_BUILD_INFO to a non-empty value keeps an existing
## build_info.txt unchanged, so that commits and edits cause no rebuilds (the
## build info then goes stale). Called from the Holmakefile with HOLDIR as
## its argument; prints the name of the file it maintains.

cd "$(dirname "$0")" || exit 0

out=build_info.txt
tmp=$out.tmp.$$

if [ -n "$CML_FREEZE_BUILD_INFO" ] && [ -f "$out" ]; then
  echo "CML_FREEZE_BUILD_INFO is set, so misc/$out is not updated" >&2
  echo "$out"
  exit 0
fi

# git_info PREFIX DIR prints the key=value lines for the checkout at DIR.
# Values that cannot be determined are left empty (dirty is then "unknown");
# a failed git command must never be mistaken for a clean worktree. The tag
# is empty unless one points exactly at the commit.
git_info () {
  commit=
  tag=
  date=
  dirty=unknown
  if [ -n "$2" ] &&
     commit=$(git -C "$2" rev-parse --verify -q HEAD 2>/dev/null)
  then
    tag=$(git -C "$2" describe --tags --exact-match HEAD 2>/dev/null) || tag=
    date=$(TZ=UTC git -C "$2" show -s --format=%cd \
             --date=format-local:'%Y-%m-%d %H:%M:%S UTC' HEAD 2>/dev/null) ||
      date=
    if status=$(git -C "$2" --no-optional-locks status --porcelain \
                  --untracked-files=normal 2>/dev/null)
    then
      if [ -n "$status" ]; then dirty=1; else dirty=0; fi
    fi
  fi
  printf '%s_commit=%s\n%s_tag=%s\n%s_date=%s\n%s_dirty=%s\n' \
    "$1" "$commit" "$1" "$tag" "$1" "$date" "$1" "$dirty"
}

info=$(git_info cakeml . ; git_info hol "$1")
printf '%s\n' "$info" > "$tmp"
if cmp -s "$tmp" "$out"; then
  rm -f "$tmp"
else
  mv -f "$tmp" "$out"
fi
echo "$out"
exit 0
