FROM ubuntu:18.04

ARG POLY_GIT="F"
ARG POLY_ROOT="T"
ARG POLY_VERSION="v5.7.1"

RUN apt-get update && \
    apt-get install -y \
        wget git build-essential graphviz \
    && \
    rm -rf /var/lib/apt/lists/*

# NOTE: We might just install PolyML as Ubuntu package, but
# that strengthens the dependency on the base image.
COPY developers/install-poly.sh .
RUN  ./install-poly.sh && rm install-poly.sh

WORKDIR /HOL

COPY . .

RUN poly < tools/smart-configure.sml && ./bin/build

ENV PATH=/HOL/bin:$PATH

ENTRYPOINT ["/HOL/bin/hol"]
