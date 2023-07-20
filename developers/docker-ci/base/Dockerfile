# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), base image
#
# e.g. docker buildx build --platform linux/386,linux/amd64,linux/arm64 .

# GitHub Actions recommends Debian-based systems as base images
FROM --platform=$TARGETPLATFORM debian:stable

# The following two arguments are supported by "docker buildx"
ARG TARGETPLATFORM
ARG BUILDPLATFORM

RUN echo "I was running on $BUILDPLATFORM, building for $TARGETPLATFORM" > /tmp/log

WORKDIR /ML
VOLUME /ML

# Use this mode when you need zero interaction while installing or upgrading the system via apt
ENV DEBIAN_FRONTEND=noninteractive
ENV LD_LIBRARY_PATH=/usr/local/lib
ENV PATH=/ML/HOL/bin:$PATH

# some necessary Debian packages
RUN apt-get update -qy
RUN apt-get install -qy build-essential graphviz git libgmp-dev wget curl procps file unzip

# for Unicode display, learnt from Magnus Myreen
RUN apt-get install -qy locales-all terminfo man aptitude
RUN apt-get clean

# IDE
RUN apt-get install -qy emacs-nox

# 1. install Moscow ML (https://github.com/kfl/mosml.git)
RUN wget -q -O - https://github.com/kfl/mosml/archive/refs/tags/ver-2.10.1.tar.gz | tar xzf -
RUN make -C mosml-ver-2.10.1/src world install
RUN rm -rf mosml-ver-2.10.1

# 2. install polyml (https://github.com/polyml/polyml.git)
RUN wget -q -O polyml-master.zip https://github.com/polyml/polyml/archive/refs/heads/master.zip
RUN unzip polyml-master.zip
RUN if [ "linux/386" = "$TARGETPLATFORM" ]; then \
       cd polyml-master && ./configure --build=i686-pc-linux-gnu --enable-intinf-as-int; \
    else \
       cd polyml-master && ./configure --enable-intinf-as-int; \
    fi
RUN make -C polyml-master -j4
RUN make -C polyml-master compiler install
RUN rm -rf polyml-master polyml-master.zip

# 3. install MLton binary (https://github.com/MLton/mlton.git) for linux/amd64 only
RUN if [ "linux/amd64" = "$TARGETPLATFORM" ]; then \
    wget -q -O - https://github.com/MLton/mlton/releases/download/on-20210117-release/mlton-20210117-1.amd64-linux-glibc2.31.tgz | tar xzf -; fi
RUN if [ "linux/amd64" = "$TARGETPLATFORM" ]; then make -C mlton-20210117-1.amd64-linux-glibc2.31; fi
RUN rm -rf mlton-20210117-1.amd64-linux-glibc2.31

# 4. install OpenTheory with local packages
RUN wget -q -O - https://github.com/binghe/opentheory/archive/refs/tags/v1.5.tar.gz | tar xzf -
RUN if [ "linux/amd64" = "$TARGETPLATFORM" ]; then \
        make -C opentheory-1.5 mlton; \
    else \
        make -C opentheory-1.5 polyml; \
    fi
RUN if [ "linux/amd64" = "$TARGETPLATFORM" ]; then \
        cp opentheory-1.5/bin/mlton/opentheory /usr/local/bin; \
    else \
        cp opentheory-1.5/bin/polyml/opentheory /usr/local/bin; \
    fi
RUN rm -rf opentheory-1.5
RUN wget -q -O /root/opentheory-local.tar.gz \
    https://github.com/binghe/opentheory/releases/download/v1.5/opentheory-local.tar.gz
RUN cd /root && tar xzf opentheory-local.tar.gz && rm opentheory-local.tar.gz

# for HOL Emacs mode (Emacs is not installed by default, however)
COPY .emacs /root

ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8
