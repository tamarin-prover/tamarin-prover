# Build and Run

Thse instructions define how to build a Docker from this repository.

## preparation 

1. Go to tamarin repository

2. Run the following command with the correct dir to update the .zip in res

git archive --format zip --output ~/research/protocol-platform/docker/res/protocolplatform.zip feature-proverif-output

## Build instructions

1. install docker:
    - In MacOS, there is a binary docker for Mac, which can be installed as
      a [package](https://docs.docker.com/docker-for-mac/),
      or, if you have homebrew, via `brew cask install docker`.
    - Linux/Windows: please add info, but I know it is possible. 
2. run `./build.sh`

## Run instructions

1. Copy `run.template.sh` into `run.myname.sh`, and modify the latter so that
   `HOST_PATH_1` points to whatever directory your projects reside in.
2. Run `./run.myname.sh`.
3. Edit the files on your computer and run `prover` or `tamarin-prover` in the docker console.


## More details:

The build script `build.sh` first creates the image
`protocolplatform:latest` from `Dockerfile`. Docker is crazy enough not to
automatically translate the uid of the docker user to the user within th
docker, which is the reason why the home directory belong to whoever has
uid=1000. Which might correct for a single-user debian, I guess.

For everyone else, you'd need docker to translate your host uid (500 for me) to
whatver the dockerfile created the home with (1000). Docker does not translate
this and does not have facilities for doing this, so it is recommended to chown
all files in home to the id of the outside user when running the file. This
takes ages because the ocaml and haskell stack are locally installed (and there
is no easy way to install this stuff in the newest version system-wide).

Hence the image `protocolplatform-user:latest` is created from the other
image by doing this chmod on all of home once and for all. Downside: you need
to create the image. Upside: you need to do this step only once, instead of
every time.

