#!/usr/bin/env bash

export USER_ID=${LOCAL_USER_ID:-${USER_ID_DEFAULT}}
export GROUP_ID=${LOCAL_GROUP_ID:-${GROUP_ID_DEFAULT}}

# Either use the LOCAL_USER_ID if passed in at runtime or fallback
echo ""
echo "- Starting with UID: ${USER_ID} USER: ${USER} GID: ${GROUP_ID}"
usermod ${USER} -u ${USER_ID}
groupmod ${USER} -g ${GROUP_ID}
# useradd --shell /bin/bash -u $USER_ID -o -c "" -m ${USER}

export HOME=/home/${USER}
chown -R ${USER_ID}:${GROUP_ID} ${HOME}
chown ${USER_ID}:${GROUP_ID} ${WORKDIR}
# chown ${USER_ID}:${GROUP_ID} ${PYTHON_ENV}
ls ${WORKDIR} | xargs chown ${USER_ID}:${GROUP_ID}

echo "  -> GoSU user: ${USER} [${USER_ID}] (currently: $(whoami) [$(id)])"
echo ""
# exec /usr/local/bin/gosu ${USER_ID} "$@"
exec gosu ${USER_ID} "$@"
