# Use ARGs for versions for easier updates
ARG GHC_VERSION=9.6.6
ARG MAUDE_VERSION=Maude3.5

#----------------------------------------------------
# Stage 1: Build Maude from source
#----------------------------------------------------
FROM debian:bookworm-slim AS maude-build
ARG MAUDE_VERSION

# install Maude’s build dependencies (including static libraries)
RUN apt-get update && apt-get install -y --no-install-recommends \
      build-essential \
      bison \
      flex \
      autoconf \
      automake \
      libtool \
      libtool-bin \
      dh-autoreconf \
      libsigsegv-dev \
      libgmp-dev \
      libtecla-dev \
      libbdd-dev \
      pkg-config \
      git \
      ca-certificates \
  && rm -rf /var/lib/apt/lists/*

# bring the static GMP .a’s into /usr/lib so configure’s GMP_LIBS can see them
RUN mkdir -p /usr/lib && \
    ln -s /usr/lib/*-linux-gnu/libgmp.a      /usr/lib/libgmp.a     && \
    ln -s /usr/lib/*-linux-gnu/libgmpxx.a    /usr/lib/libgmpxx.a

WORKDIR /opt/maude-src
RUN git clone --depth 1 --branch ${MAUDE_VERSION} https://github.com/maude-lang/Maude.git . \
 && autoreconf -i

RUN mkdir build && cd build && \
    ../configure \
      --with-yices2=no \
      --with-cvc4=no \
      --enable-compiler \
      CXXFLAGS="-g -Wall -O3 -fno-stack-protector" \
      CPPFLAGS="-I/usr/include" \
      LDFLAGS="-L/usr/lib" \
      GMP_LIBS="/usr/lib/libgmpxx.a /usr/lib/libgmp.a" && \
    make -j$(nproc) && \
    make check && \
    make install

#----------------------------------------------------
# Stage 2: Build Haskell Dependencies
#----------------------------------------------------
FROM haskell:${GHC_VERSION} AS tamarin-dependencies

WORKDIR /opt/build

RUN apt-get update && apt-get install -y --no-install-recommends \
    libncurses-dev \
    zlib1g-dev \
    pkg-config \
 && rm -rf /var/lib/apt/lists/*

# copy only the files & folders that stack needs to figure out its deps
COPY stack.yaml tamarin-prover.cabal ./
COPY LICENSE ./
COPY lib/. ./lib/
COPY src ./src
COPY data ./data
COPY images ./images

RUN stack build --system-ghc --dependencies-only

#---------------------------------------------------
# Stage 3: Build the Application
#---------------------------------------------------
FROM haskell:${GHC_VERSION} AS tamarin-build

COPY --from=tamarin-dependencies /root/.stack /root/.stack
COPY --from=tamarin-dependencies /opt/build /opt/build

WORKDIR /opt/build

RUN stack install --system-ghc --local-bin-path /opt/build/bin

# Install binutils, strip the tamarin binary, and clean up in one layer
RUN apt-get update && \
    apt-get install -y --no-install-recommends binutils && \
    strip /opt/build/bin/tamarin-prover && \
    apt-get purge -y --auto-remove binutils && \
    rm -rf /var/lib/apt/lists/*

#---------------------------------------------------
# Stage 4: Final Image
#---------------------------------------------------
FROM debian:bookworm-slim AS tamarin

LABEL version="1.0" \
      description="The Tamarin prover for security protocol verification" \
      org.opencontainers.image.authors="The Tamarin prover authors"

ENV MAUDE_LIB=/usr/local/share \
    PATH="/usr/local/bin:$PATH" \
    LANG=C.UTF-8 \
    LC_ALL=C.UTF-8

RUN apt-get update \
 && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
    python3 \
    graphviz \
    libbdd0c2 \
    libtecla1 \
    libsigsegv2 \
 && rm -rf /var/lib/apt/lists/* \
 && useradd -ms /bin/bash tamarin

COPY --from=maude-build /usr/local/share/prelude.maude /usr/local/share/
COPY --from=maude-build /usr/local/bin/maude /usr/local/bin/maude

COPY --from=tamarin-build --chown=tamarin:tamarin /opt/build/bin /usr/local/bin
COPY --chown=tamarin:tamarin --chmod=755 etc/docker/res/entrypoint.sh /usr/local/bin/entrypoint.sh

USER tamarin
WORKDIR /home/tamarin
COPY --chown=tamarin:tamarin etc/docker/res/README .

EXPOSE 3001
ENTRYPOINT ["/usr/local/bin/entrypoint.sh"]
