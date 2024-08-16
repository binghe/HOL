DOCKER_IMAGE=binghelisp/hol-dev:riscv64

build:
	docker buildx build --platform linux/riscv64 --push -t $(DOCKER_IMAGE) .

# This runs the docker image in your native platform
run:
	docker run -ti -v ML --rm $(DOCKER_IMAGE)
