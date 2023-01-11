# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), the CI image
#

# This "base" image is described in "base/Dockerfile"
FROM --platform=$TARGETPLATFORM binghelisp/hol-dev:latest

# The following two arguments are supported by "docker buildx" commands
ARG TARGETPLATFORM
ARG BUILDPLATFORM

# GitHub Actions' hardware specification for Linux virtual machines: 2-core CPU (x86_64)
# By default we use 4 cores in other building environments (e.g. Docker Hub autobuilds)
ARG BUILDOPTS="--expk -j4"
ARG SML=poly

WORKDIR /ML/HOL

# fast copy all files to the docker image
COPY --link . .

# building HOL
RUN ${SML} < tools/smart-configure.sml 
RUN bin/build ${BUILDOPTS}

# This can be overrided by "docker run <command>"
CMD ["/ML/HOL/bin/hol"]
