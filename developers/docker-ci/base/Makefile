DOCKER_IMAGE=binghelisp/hol-dev:base

build:
	docker buildx build --platform linux/386 .
	docker buildx build --platform linux/amd64 .
	docker buildx build --platform linux/arm64 .
	docker buildx build --platform linux/386,linux/amd64,linux/arm64 -t $(DOCKER_IMAGE) .

push:
	docker push $(DOCKER_IMAGE)

# This runs the docker image in your native platform
run:
	docker run -ti -v ML --rm $(DOCKER_IMAGE)
