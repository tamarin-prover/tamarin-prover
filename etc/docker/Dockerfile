# Build image
# based on bullseye, since system-ghc is too old in buster
FROM debian:bullseye-slim AS tamarin-build
# install build dependencies
RUN apt-get update && \
    DEBIAN_FRONTEND=noninteractive \
    apt-get -y --no-install-recommends install \
        haskell-stack \
        ca-certificates \
        build-essential \
        netbase \
        locales \
        ghc \
        zlib1g \
        zlib1g-dev
WORKDIR /workspace
# copy dependency specifications first (need stack.yaml for resolver spec)
RUN mkdir -p lib/export lib/theory lib/sapic lib/tools lib/term
COPY stack.yaml tamarin-prover.cabal ./
COPY lib/sapic/tamarin-prover-sapic.cabal lib/sapic/
COPY lib/term/tamarin-prover-term.cabal lib/term/
COPY lib/theory/tamarin-prover-theory.cabal lib/theory/
COPY lib/utils/tamarin-prover-utils.cabal lib/utils/
# cache stack package index
RUN stack update
# > Compiling language-javascript requires a UTF-8 locale.
# (https://github.com/erikd/language-javascript/issues/86)
# thankfully we're only in a temporary build container, so let's change that real quick
RUN sed -i '/en_US.UTF-8/s/^# //g' /etc/locale.gen && locale-gen
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8
# build dependencies first, for caching
RUN stack build --system-ghc --dependencies-only --ghc-options="+RTS -M600M"
# now copy rest of source code
COPY LICENSE ./
# lib needs special handling since it already exists
COPY lib/. ./lib/
COPY src ./src
COPY data ./data
COPY images ./images
# build the entire thing
RUN stack build --system-ghc
RUN stack install --system-ghc --local-bin-path /usr/local/bin

# Assemble final image
# again, based on buillseye, since our build linked to bullseye libs
FROM debian:bullseye-slim
# Metadata
LABEL version="1.0" \
      description="The Tamarin prover for security protocol verification" \
      org.opencontainers.image.authors="The Tamarin prover authors"
# install runtime dependencies
RUN apt-get update && \
    DEBIAN_FRONTEND=noninteractive \
    apt-get -y --no-install-recommends install \
        maude \
        graphviz
COPY --from=tamarin-build /usr/local/bin /usr/local/bin
COPY etc/docker/res/entrypoint.sh /usr/local/bin/
RUN chmod 755 /usr/local/bin/entrypoint.sh
RUN useradd -ms /bin/bash tamarin
USER tamarin
WORKDIR /home/tamarin
EXPOSE 3001
COPY etc/docker/res/README .
ENTRYPOINT ["/usr/local/bin/entrypoint.sh"]
