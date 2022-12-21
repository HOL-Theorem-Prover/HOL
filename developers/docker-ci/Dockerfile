# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), the CI image
#

# This "base" image is described in "base/Dockerfile"
FROM binghelisp/hol-dev:latest

# GitHub Actions' hardware specification for Linux virtual machines: 2-core CPU (x86_64)
ARG SML=poly
ARG BUILDOPTS="--expk -j2"

WORKDIR /ML/HOL

# fast copy all files to the docker image
COPY --link . .

# build HOL
RUN ${SML} < tools/smart-configure.sml 
RUN bin/build ${BUILDOPTS}

ENV PATH=/ML/HOL/bin:$PATH

# default entrypoint
ENTRYPOINT /ML/HOL/bin/hol
