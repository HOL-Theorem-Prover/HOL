# NOTE: If you meet "ERROR: failed to solve: no match for platform in manifest",
#       your error should be related to this open issue [1] that enter into
#       Docker Desktop 4.20.  As a workaround, you should disable the flag
#      'Use containerd' for pulling and storing images within the feature of
#       Docker Desktop to solve it [2].  -- Chun Tian (binghe), July 17, 2023
#
# [1] https://github.com/moby/moby/issues/44578
# [2] https://stackoverflow.com/questions/76355896

DOCKER_IMAGE=binghelisp/hol-dev

build:
	docker buildx build --platform linux/386 .
	docker buildx build --platform linux/amd64 .
	docker buildx build --platform linux/arm64 .
	docker buildx build --platform linux/386,linux/amd64,linux/arm64 \
		-t $(DOCKER_IMAGE) .

# This will reuse the images built locally by the "build" target
push:
	docker buildx build --platform linux/386,linux/amd64,linux/arm64 \
		-t $(DOCKER_IMAGE) --push .

# This runs the docker image in your native platform
run:
	docker run -ti --rm $(DOCKER_IMAGE)
