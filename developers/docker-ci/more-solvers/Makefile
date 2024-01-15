DOCKER_IMAGE=binghelisp/hol-dev:more-solvers

build:
	docker buildx build --platform linux/amd64 -t $(DOCKER_IMAGE) .

push: build
	docker push $(DOCKER_IMAGE)

# This runs the docker image in your native platform
run:
	docker run -ti --rm $(DOCKER_IMAGE)
