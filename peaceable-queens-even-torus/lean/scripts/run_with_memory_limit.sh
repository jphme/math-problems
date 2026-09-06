#!/bin/zsh

# Run one proof command at a time and terminate its complete descendant tree
# at a conservative RSS threshold below the user's 20 GB budget. This is a
# sampled watchdog, not a kernel-enforced limit; system pressure is checked too.

set -u

limit_gib="${LEAN_MEMORY_LIMIT_GIB:-12}"
if [[ "$limit_gib" != <-> ]] || (( limit_gib < 1 || limit_gib > 16 )); then
  print -u2 "LEAN_MEMORY_LIMIT_GIB must be an integer from 1 through 16"
  exit 2
fi
readonly limit_gib
readonly limit_kib=$((limit_gib * 1024 * 1024))
readonly poll_seconds=0.1
readonly minimum_free_percent=20

if (( $# == 0 )); then
  print -u2 "usage: run_with_memory_limit.sh COMMAND [ARG ...]"
  exit 2
fi

# Fail before launching anything if the sandbox prevents process inspection.
probe_rss="$(ps -o rss= -p $$ 2>/dev/null | tr -d ' ')"
if [[ "$probe_rss" != <-> ]]; then
  print -u2 "MEMORY_MONITOR_UNAVAILABLE: process inspection is required"
  exit 2
fi

system_memory_ok() {
  local report
  local free_percent
  report="$(/usr/bin/memory_pressure 2>/dev/null)" || return 1
  free_percent="$(print -r -- "$report" | sed -n 's/^System-wide memory free percentage: \([0-9][0-9]*\)%$/\1/p')"
  if [[ "$free_percent" != <-> ]]; then
    print -u2 "SYSTEM_MEMORY_MONITOR_UNAVAILABLE"
    return 1
  fi
  if (( free_percent < minimum_free_percent )); then
    print -u2 "SYSTEM_MEMORY_PRESSURE free_percent=$free_percent minimum=$minimum_free_percent"
    return 1
  fi
}

system_memory_ok || exit 2

collect_descendants() {
  local parent="$1"
  local child
  local children
  children="$(pgrep -P "$parent" 2>/dev/null || true)"
  for child in ${(f)children}; do
    [[ -n "$child" ]] || continue
    print -r -- "$child"
    collect_descendants "$child"
  done
}

process_tree() {
  local root="$1"
  local descendants
  descendants="$(collect_descendants "$root")"
  print -r -- "$root"
  [[ -z "$descendants" ]] || print -r -- "$descendants"
}

terminate_tree() {
  local root="$1"
  local tree
  tree=(${(f)"$(process_tree "$root")"})
  (( ${#tree} == 0 )) && return
  kill -TERM $tree 2>/dev/null || true
  sleep 1
  # Keep the captured descendants: once the root exits, pgrep -P can no longer
  # find children that have been reparented to launchd.
  (( ${#tree} == 0 )) || kill -KILL $tree 2>/dev/null || true
}

"$@" &
root_pid=$!
peak_kib=0
memory_exceeded=0
pressure_ticks=0

trap 'terminate_tree "$root_pid"; exit 130' INT TERM

while kill -0 "$root_pid" 2>/dev/null; do
  tree=(${(f)"$(process_tree "$root_pid")"})
  total_kib=0
  for pid in $tree; do
    rss="$(ps -o rss= -p "$pid" 2>/dev/null | tr -d ' ' || true)"
    [[ "$rss" == <-> ]] || continue
    total_kib=$((total_kib + rss))
  done
  (( total_kib > peak_kib )) && peak_kib=$total_kib
  (( pressure_ticks += 1 ))
  if (( pressure_ticks >= 100 )); then
    pressure_ticks=0
    if ! system_memory_ok; then
      memory_exceeded=1
      terminate_tree "$root_pid"
      break
    fi
  fi
  if (( total_kib >= limit_kib )); then
    print -u2 "MEMORY_LIMIT_EXCEEDED rss_kib=$total_kib limit_kib=$limit_kib"
    for pid in $tree; do
      ps -o pid=,ppid=,rss=,command= -p "$pid" 2>/dev/null || true
    done
    memory_exceeded=1
    terminate_tree "$root_pid"
    break
  fi
  sleep "$poll_seconds"
done

wait "$root_pid" 2>/dev/null
exit_status=$?

if (( memory_exceeded )); then
  exit 137
fi

print -u2 "MEMORY_LIMIT_OK peak_rss_kib=$peak_kib limit_kib=$limit_kib"
exit "$exit_status"
