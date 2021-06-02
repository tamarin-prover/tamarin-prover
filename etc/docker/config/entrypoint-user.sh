#!/usr/bin/env bash

echo "  -> GoSU user: ${USER} [${USER_ID}] (currently: $(whoami) [$(id)])"
echo ""
# exec /usr/local/bin/gosu ${USER_ID} "$@"
exec gosu ${USER_ID} "$@"
