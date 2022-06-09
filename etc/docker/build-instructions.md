# Pull and Run (and Build)

These instructions define how to run the docker image.

## Install docker:

- Linux/MacOS: Follow [instructions](https://docs.docker.com/get-docker/)
- In MacOS, there is a binary docker for Mac, which can be installed as
  a [package](https://docs.docker.com/docker-for-mac/),
  or, if you have homebrew, via `brew cask install docker`.


## Docker images

There are three docker images:

etc/docker/Dockerfile -> builds a docker with tamarin in it
etc/docker/Dockerfile-platform -> builds a docker with tamarin, proverif, gsverif and deepsec in it
etc/docker/Dockerfile-benchmark -> performs some benchmarks for the tamarin-platform docker

## Pull instructions

(For Dockerfile-platform)

```
docker pull protocolplatform/protocolplatform:latest
```

## Run instructions

1. Execute
```
docker run protocolplatform/protocolplatform:latest
```

2. Follow instructions.

## Build instructions

This is only needed for regenerating the image when we update the software.

1. run `./build.sh`

