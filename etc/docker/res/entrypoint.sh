#!/usr/bin/env sh
set -e

if [ -t 0 ]; then
  # interactive shell
  if [ "$#" -lt 1 ]; then
    # no arguments given, probably looking for help
    cat README
  else
    # just run whatever the user wanted
    exec "$@"
  fi
else
  cat <<'ENDOFINFO'
--------- The Tamarin Prover Docker Image ---------

It looks like you want to run Tamarin as a service.
If you want to use it as a commandline tool, use
`docker run --tty --interactive` for more info.

---------------------------------------------------
ENDOFINFO
  exec /usr/local/bin/tamarin-prover \
    interactive \
    --port=3001 \
    --interface='*4' \
    "."
fi