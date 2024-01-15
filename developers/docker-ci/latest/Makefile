DOCKER_IMAGE=binghelisp/hol-dev:latest

build:
	docker buildx build --platform linux/386 .
	docker buildx build --platform linux/amd64 .
	docker buildx build --platform linux/arm64 .
	docker buildx build --platform linux/386,linux/amd64,linux/arm64 -t $(DOCKER_IMAGE) .

push: build
	docker push $(DOCKER_IMAGE)

# This runs the docker image in your native platform
run:
	docker run -ti --rm $(DOCKER_IMAGE)
