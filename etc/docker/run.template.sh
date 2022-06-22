#!/usr/bin/env bash
HOSTNAME="ProtoMachine"
HOST_PATH_1="/Users/robert/lab/teaching/2018-WS-Hands-On-Protocol-Verification/handsonws18/projects"
DOCKER_PATH_1="/workspace"
# VIRTUAL_ENV="/PATH/TO/LOCAL/VIRTUALENV/"

docker run -ti \
    --hostname ${HOSTNAME} \
    --volume ${HOST_PATH_1}:${DOCKER_PATH_1} \
    -e LOCAL_USER_ID=`id -u $USER` \
    -e LOCAL_GROUP_ID=`id -g $USER` \
    protocolplatform-user:latest

    # --volume ${VIRTUAL_ENV}:"/env/external" \
