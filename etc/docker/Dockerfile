FROM fpco/stack-build:lts-16.12 as deps-tamarin
RUN mkdir /opt/build
WORKDIR /opt/build
ENV DEBIAN_FRONTEND=noninteractive

COPY stack.yaml stack.yaml.lock tamarin-prover.cabal /opt/build/
RUN mkdir lib lib/export lib/theory lib/sapic lib/tools lib/term
COPY lib/sapic/tamarin-prover-sapic.cabal lib/sapic/
COPY lib/term/tamarin-prover-term.cabal lib/term/
COPY lib/theory/tamarin-prover-theory.cabal lib/theory/
COPY lib/utils/tamarin-prover-utils.cabal lib/utils/
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
FROM debian:buster-slim as tamarin-prover
RUN mkdir -p /opt/tamarin
WORKDIR /opt/tamarin

RUN apt-get update && apt-get install -y --no-install-recommends \
    #general stuff
    graphviz \
    libncurses5 \
    bc \
    locales \
    curl \
    ca-certificates \
    unzip \
    && rm -rf /var/lib/apt/lists/*

# set locales so haskell can do it's thing
# https://stackoverflow.com/questions/28405902/how-to-set-the-locale-inside-a-debian-ubuntu-docker-container
# The following does NOT work -> locale-gen --no-purge en_US.UTF-8
RUN sed -i '/en_US.UTF-8/s/^# //g' /etc/locale.gen && locale-gen
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8

# Install built app
COPY --from=build-tamarin /opt/build/bin .

ENV MAUDEURL="http://maude.cs.illinois.edu/w/images/5/5d/Maude-2.7.1-linux.zip"
ENV MAUDEZIP="Maude-2.7.1-linux.zip"
ENV MAUDEFILES="prelude.maude maude.linux64"

# Install new maude maude version
RUN cd /tmp && curl  -O ${MAUDEURL} \
&& unzip ${MAUDEZIP} ${MAUDEFILES} -d /opt/tamarin \
&& rm  ${MAUDEZIP}
RUN mv maude.linux64 maude && chmod +x maude

ENV RES="etc/docker/res"

COPY ${RES}/README .

ENV PATH=${PATH}:/opt/build/bin:/opt/tamarin
# ENTRYPOINT ["/opt/tamarin/tamarin-prover"]
CMD ["cat", "README" ]
