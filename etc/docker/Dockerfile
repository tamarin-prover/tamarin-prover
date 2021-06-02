# ===========================================================================================
# Dockerfile for building AOSP [Android Open Source Project]
#
# References:
#       http://source.android.com/source/index.html
# ===========================================================================================
# FROM python:3.6.6-slim-stretch
FROM debian:buster-slim

MAINTAINER Protocol Platform <protocolplatform@protonmail.com>

# ENV USER=handson
# ENV USER_ID_DEFAULT=1000
# ENV GROUP_ID_DEFAULT=1000

# ENV WORKDIR=/workspace
ENV SRC=/src
ENV PROVERIF_TGZ="res/proverif2.02pl1.tar.gz"
ENV PROVERIF_DIR_NAME="proverif2.02pl1"
ENV PROVERIF_DIR_IMAGE="${SRC}/${PROVERIF_DIR_NAME}"
# GSVerif
ENV GSVERIF_TGZ="res/gsverif2.0.zip"
ENV GSVERIF_DIR_IMAGE="${SRC}/gsverif"
# use accountability tamarin...
ENV TAMARIN_TGZ="res/protocolplatform.zip"
# ENV TAMARIN_DIR_BUILDER="/Users/robert/src/tamarin-prover-rkunnema"
ENV TAMARIN_DIR_IMAGE="${SRC}/protocol-platform"
ENV MAUDE="res/maude"
ENV DEEPSEC_URL="https://github.com/DeepSec-prover/deepsec.git"
ENV DEEPSEC_DIR_IMAGE="${SRC}/deepsec"
# ENV PYTHON_ENV=/env
# ENV PYTHON_ENV_NAME="default3.6"
# ENV PYTHON_ENV_NAME_EXTERNAL="external"
# ENV VIRTUALENV_PATH="${PYTHON_ENV}/${PYTHON_ENV_NAME}"
# ENV VIRTUALENV_PATH_EXTERNAL="${PYTHON_ENV}/${PYTHON_ENV_NAME_EXTERNAL}"
ARG OCAML_VERSION
ENV OCAML_VERSION 4.10.0

# See https://github.com/docker/docker/issues/4032
#ENV DEBIAN_FRONTEND noninteractive

# Install dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    #general stuff
    curl \
    gnupg \
    m4 \
    opam \
#    ocaml \
    # libgtk2.0-dev \
    # tamarin
    haskell-stack \
    graphviz \
    maude \
    git \
    netbase \
    zlib1g-dev \
    && rm -rf /var/lib/apt/lists/*

RUN mkdir ${WORKDIR}; \
    mkdir ${SRC}; \
    mkdir ${GSVERIF_DIR_IMAGE};

COPY config/.bashrc /root/.bashrc
COPY config/entrypoint.sh /usr/local/bin/entrypoint.sh


RUN sed -i \
        -e 's/VAR_DEEPSEC_DIR_IMAGE/${DEEPSEC_DIR_IMAGE}/g'\
        -e 's/VAR_PROVERIF_DIR_IMAGE/${PROVERIF_DIR_IMAGE}/g'\
        -e 's/VAR_GSVERIF_DIR_IMAGE/${GSVERIF_DIR_IMAGE}/g'\
        /root/.bashrc

RUN opam init -a -y --comp $OCAML_VERSION --disable-sandboxing && \
    \
    find /root/.opam -regex '.*\.\(cmt\|cmti\|annot\|byte\)' -delete && \
    rm -rf /root/.opam/archives \
           /root/.opam/repo/default/archives \
           /root/.opam/$OCAML_VERSION/man \
           /root/.opam/$OCAML_VERSION/build

# Install need version of ocaml for deepsec
RUN opam install -y ocamlfind ocamlbuild

# Install ProVerif from source
# Note: need to install ProVerif before switching to 4.05.0, because that one doesn't have ocamlyacc
COPY ${PROVERIF_TGZ} ${SRC}/${PROVERIF_TGZ}
RUN cd ${SRC} && tar -xzf ${PROVERIF_TGZ} && rm ${PROVERIF_TGZ}
# Note: installation will fail because of lacking libgtk, but still produce the binary :D
# Note: need to run bash so the .bashrc sets the environment variables and ocamlfind can be found
# CharlieNote: running the eval is the minimal lightweight setup to build
RUN eval `opam config env` && cd ${PROVERIF_DIR_IMAGE} && ./build; test -x proverif

RUN git clone --depth 1 ${DEEPSEC_URL} ${DEEPSEC_DIR_IMAGE} && cd ${DEEPSEC_DIR_IMAGE} &&  eval `opam config env` && make

# Install our custom gsverif
COPY ${GSVERIF_TGZ} ${GSVERIF_DIR_IMAGE}/${GSVERIF_TGZ}
RUN cd ${GSVERIF_DIR_IMAGE} && unzip ${GSVERIF_TGZ} && rm ${GSVERIF_TGZ}
RUN  cd ${GSVERIF_DIR_IMAGE} &&  eval `opam config env` && ./build


# Note: Stack in avaible package is outdated
RUN stack upgrade
# RUN apt-get update && apt-get install -y --no-install-recommends locales
# Set the locale
# RUN locale-gen en_US.UTF-8
# Note : We need to set the locale so that the stack install of  language-javascript-0.7.1.0 goes through...
ENV LANG C.UTF-8
ENV LC_ALL C.UTF-8

# # Install tamarin
RUN  mkdir ${TAMARIN_DIR_IMAGE}
RUN mkdir /test
COPY ${TAMARIN_TGZ} ${TAMARIN_DIR_IMAGE}/${TAMARIN_TGZ}
RUN cd ${TAMARIN_DIR_IMAGE} && unzip ${TAMARIN_TGZ} && rm ${TAMARIN_TGZ}
# COPY res/stack /usr/bin/stack
# RUN chmod +x /usr/bin/stack
RUN cd ${TAMARIN_DIR_IMAGE} && make


ENV PRELUDE_MAUDE="res/prelude.maude"

# Note: We fix the maude version binary
COPY ${MAUDE} /usr/local/bin/
COPY ${PRELUDE_MAUDE} /usr/local/bin/


# @ Robert, this bellow duplicates the path export we are making in bashrc, not sure which is best
# Note: Install the binaries
RUN cp ${GSVERIF_DIR_IMAGE}/gsverif /root/.local/bin/tamarin-prover ${PROVERIF_DIR_IMAGE}/proverif  ${DEEPSEC_DIR_IMAGE}/deepsec ${DEEPSEC_DIR_IMAGE}/deepsec_worker /usr/local/bin

# @ Robert, i'm putting this here to avoid recompiling everything, to put in the main apt later
RUN apt-get update && apt-get install -y --no-install-recommends libncurses5

# @Robert clean up stack stuff ? (rm -rf /root/.stack )
# @Robert  clean up opam stuff ?  (rm -rf /root/.opam ) in which case remove the opam init line from bashrc


COPY res/proverif-tamarin /usr/local/bin/
COPY res/progsverif-tamarin /usr/local/bin/
COPY res/deepsec-tamarin /usr/local/bin/


# EXPOSE ###############################################################################################################
# VOLUME [ \
#     "${WORKDIR}", \
#     ]
# WORKDIR ${WORKDIR}

# ENTRYPOINT ["/usr/local/bin/entrypoint.sh"]
ENV PATH="/usr/local/bin:${PATH}"
CMD ["/bin/bash"]
