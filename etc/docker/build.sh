#!/usr/bin/env bash
docker build -t protocolplatform:latest -f Dockerfile .
docker build \
    -f Dockerfile-user \
    --build-arg LOCAL_USER_ID=`id -u $USER` \
    --build-arg LOCAL_GROUP_ID=`id -g $USER` \
    --build-arg OCAML_VERSION=4.10.0    \
    -t protocolplatform-user:latest .
