# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), base image
#
# e.g. docker build --push -t binghelisp/hol-dev .

# GitHub Action recommends Debian-based systems as base images
FROM debian:stable

WORKDIR /ML
VOLUME /ML

# Use this mode when you need zero interaction while installing or upgrading the system via apt
ENV DEBIAN_FRONTEND=noninteractive
ENV LD_LIBRARY_PATH=/usr/local/lib

# necessary packages
RUN apt-get update -qy
RUN apt-get install -qy build-essential graphviz git libgmp-dev curl wget

# optional packages (IDE)
RUN apt-get install -qy emacs-nox vim automake
RUN apt-get clean

# install MLton (https://github.com/MLton/mlton.git)
RUN wget -q https://github.com/MLton/mlton/releases/download/on-20210117-release/mlton-20210117-1.amd64-linux-glibc2.31.tgz
RUN tar xzf mlton-20210117-1.amd64-linux-glibc2.31.tgz
RUN make -C mlton-20210117-1.amd64-linux-glibc2.31
RUN rm -rf mlton-20210117-1.amd64-linux-glibc2.31*

# install polyml (https://github.com/polyml/polyml.git)
RUN wget -q -O polyml-5.9.tar.gz https://github.com/polyml/polyml/archive/refs/tags/v5.9.tar.gz
RUN tar xzf polyml-5.9.tar.gz
RUN cd polyml-5.9 && ./configure --enable-intinf-as-int
RUN make -C polyml-5.9 -j4
RUN make -C polyml-5.9 install

# install mosml (https://github.com/kfl/mosml.git)
RUN wget -q -O mosml-ver-2.10.1.tar.gz https://github.com/kfl/mosml/archive/refs/tags/ver-2.10.1.tar.gz
RUN tar xzf mosml-ver-2.10.1.tar.gz
RUN make -C mosml-ver-2.10.1/src world
RUN make -C mosml-ver-2.10.1/src install

# install OpenTheory
RUN wget -q -O /root/opentheory-local.tar.gz https://github.com/binghe/opentheory/releases/download/v1.5/opentheory-local.tar.gz
RUN cd /root && tar xzf opentheory-local.tar.gz
RUN wget -q -O opentheory-1.5.tar.gz https://github.com/binghe/opentheory/archive/refs/tags/v1.5.tar.gz
RUN tar xzf opentheory-1.5.tar.gz
RUN make -C opentheory-1.5 mlton
RUN cp opentheory-1.5/bin/mlton/opentheory /usr/local/bin

# for Emacs
COPY .emacs /root

# [optional] delete building directories for smaller image sizes
RUN rm -rf polyml-5.9*
RUN rm -rf mosml-ver-2.10.1*
RUN rm -rf opentheory-1.5*
