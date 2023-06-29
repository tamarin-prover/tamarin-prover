FROM fpco/stack-build-small:lts-19.19 as dependencies
RUN mkdir /opt/build
WORKDIR /opt/build

RUN git clone https://github.com/tamarin-prover/tamarin-prover . && git checkout eebd77fddf06223fa52d866d8fc0eff2c78e462d

RUN stack build --system-ghc --dependencies-only
#---------------------------------------------------
FROM fpco/stack-build-small:lts-19.19 as build

COPY --from=dependencies /root/.stack /root/.stack
COPY --from=dependencies /opt/build /opt/build

WORKDIR /opt/build

RUN stack install --system-ghc --local-bin-path /opt/build/bin
#----------------------------------------------------
FROM debian:bullseye-slim as artifact
WORKDIR /opt

RUN apt-get update \
 && apt-get -y --no-install-recommends install \
    curl unzip ca-certificates

RUN curl -SL 'https://figshare.com/ndownloader/files/38371403' --output usenix23-ens.zip
RUN unzip usenix23-ens.zip
#----------------------------------------------------
FROM debian:bullseye-slim as tamarin

ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8

RUN apt-get update \
 && apt-get -y --no-install-recommends install \
    maude graphviz python3

COPY --from=build /opt/build/bin /usr/local/bin
COPY --from=artifact /opt/usenix23-ens/ /opt/usenix23-ens

WORKDIR /opt/usenix23-ens

EXPOSE 3001

CMD ["cat", "README.md"]
