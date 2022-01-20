FROM ocaml/opam as build-ocaml
# MAINTAINER Protocol Platform <protocolplatform@protonmail.com>
USER root
RUN opam install -y ocamlfind ocamlbuild

WORKDIR /opt/build
ENV RES="etc/docker/res"
ENV CONFIG="etc/docker/config"
ENV PROVERIF_URL="https://prosecco.gforge.inria.fr/personal/bblanche/proverif/proverif2.04.tar.gz"
ENV PROVERIF_DIR_NAME="proverif2.04"
ENV GSVERIF_TGZ="gsverif2.0.zip"
ENV GSVERIF_DIR_NAME="gsverif"
ENV DEEPSEC_URL="https://github.com/DeepSec-prover/deepsec.git"
ENV DEEPSEC_DIR_NAME="deepsec"
# Install ProVerif from source
# Note: need to install ProVerif before switching to 4.05.0, because that one doesn't have ocamlyacc
RUN curl -SL ${PROVERIF_URL} | tar -xzC .

# Note: installation will fail because of lacking libgtk, but still produce the binary :D
# Note: need to run bash so the .bashrc sets the environment variables and ocamlfind can be found
# CharlieNote: running the eval is the minimal lightweight setup to build
RUN eval `opam config env` && cd ${PROVERIF_DIR_NAME} && ./build; test -x proverif

RUN git clone --depth 1 ${DEEPSEC_URL} ${DEEPSEC_DIR_NAME} && cd ${DEEPSEC_DIR_NAME} &&  eval `opam config env` && make

# Install our custom gsverif
COPY ${RES}/${GSVERIF_TGZ} ${GSVERIF_DIR_NAME}/
RUN cd ${GSVERIF_DIR_NAME} && unzip ${GSVERIF_TGZ} && rm ${GSVERIF_TGZ}
RUN cd ${GSVERIF_DIR_NAME} &&  eval `opam config env` && ./build

FROM fpco/stack-build:lts-16.12 as deps-tamarin
RUN mkdir /opt/build
WORKDIR /opt/build
ENV DEBIAN_FRONTEND=noninteractive
#RUN apt-get update && apt-get install -y --no-install-recommends \
#    #general stuff
#    curl \
#    # gnupg \
#    m4 \
#    && rm -rf /var/lib/apt/lists/*

COPY stack.yaml stack.yaml.lock tamarin-prover.cabal /opt/build/
RUN mkdir lib lib/export lib/theory lib/sapic lib/tools lib/term
COPY lib/sapic/tamarin-prover-sapic.cabal lib/sapic/
COPY lib/term/tamarin-prover-term.cabal lib/term/
COPY lib/theory/tamarin-prover-theory.cabal lib/theory/
COPY lib/utils/tamarin-prover-utils.cabal lib/utils/
COPY lib/export/tamarin-prover-export.cabal lib/export/
RUN stack build --system-ghc --dependencies-only --ghc-options="+RTS -M600M" -j1

FROM fpco/stack-build:lts-16.12 as build-tamarin
# Copy compiled dependencies from previous stage
COPY --from=deps-tamarin /root/.stack /root/.stack
# copy all files except `etc`, because we don't want this stage to be rebuilt
# anytime the dockerfiles change
# docker is braindead: it copies the content of a directory, even if it is in a list
# so we need to list them one by one
COPY stack.yaml stack.yaml.lock tamarin-prover.cabal LICENSE /opt/build/
COPY src  /opt/build/src
COPY lib /opt/build/lib
COPY data /opt/build/data
COPY images /opt/build/images
WORKDIR /opt/build
RUN stack build --system-ghc
RUN mv "$(stack path --local-install-root --system-ghc)/bin" /opt/build/bin

# Base image for stack build so compiled artifact from previous
# stage should run
FROM debian:buster-slim as protocolplatform
RUN mkdir -p /opt/protocolplatform
WORKDIR /opt/protocolplatform

RUN apt-get update && apt-get install -y --no-install-recommends \
    #general stuff
    graphviz \
    libncurses5 \
    bc \
    locales \
    && rm -rf /var/lib/apt/lists/*

# set locales so haskell can do it's thing
# https://stackoverflow.com/questions/28405902/how-to-set-the-locale-inside-a-debian-ubuntu-docker-container
# The following does NOT work -> locale-gen --no-purge en_US.UTF-8
RUN sed -i '/en_US.UTF-8/s/^# //g' /etc/locale.gen && locale-gen
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8

# TODO turn variables above into ARGS ..
# https://stackoverflow.com/questions/52904847/how-do-i-copy-variables-between-stages-of-multi-stage-docker-build
ENV PROVERIF_DIR_NAME="proverif2.02pl1"
ENV GSVERIF_DIR_NAME="gsverif"
ENV DEEPSEC_DIR_NAME="deepsec"
ENV RES="etc/docker/res"
ENV CONFIG="etc/docker/config"

# Install third party tools
COPY --from=build-ocaml /opt/build/${PROVERIF_DIR_NAME}/proverif /opt/build/bin/
COPY --from=build-ocaml /opt/build/${GSVERIF_DIR_NAME}/gsverif /opt/build/bin/
COPY --from=build-ocaml /opt/build/${DEEPSEC_DIR_NAME}/deepsec /opt/build/bin/
COPY --from=build-ocaml /opt/build/${DEEPSEC_DIR_NAME}/deepsec_worker /opt/build/bin/

# Install built app
COPY --from=build-tamarin /opt/build/bin .

# Install new maude maude version
ENV PRELUDE_MAUDE="${RES}/prelude.maude"
ENV MAUDE="${RES}/maude"
COPY ${MAUDE} /opt/build/bin/
COPY ${PRELUDE_MAUDE} /opt/build/bin/

COPY ${RES}/proverif-tamarin .
COPY ${RES}/progsverif-tamarin .
COPY ${RES}/deepsec-tamarin .
COPY ${RES}/proverif-tamarin-diff .
COPY examples/sapic/export examples
# ENV EXPORT=examples/sapic/export/ExistingSapicModels
# COPY ${EXPORT}/AC.spthy ${EXPORT}/AC_counter_with_attack.spthy ${EXPORT}/AC_sid_with_attack.spthy ${EXPORT}/AKE.spthy ${EXPORT}/OTP.spthy ${EXPORT}/nsl-no_as-untagged.spthy examples/ExistingSapicModels/
# COPY examples/sapic/fast examples/fast
# COPY examples/sapic/slow examples/slow
# COPY ${RES}/README ${RES}/README-long ${RES}/.bashrc ./
COPY ${RES}/README ${RES}/.bashrc ./

ENV PATH=${PATH}:/opt/build/bin:/opt/protocolplatform
# TODO Do we need this???
# ENV DEEPSEC_DIR=$DEEPSEC_DIR_IMAGE/deepsec

EXPOSE 3001
CMD ["cat", "/opt/protocolplatform/README"]
