build:
	docker buildx build --platform linux/386 .
	docker buildx build --platform linux/amd64 .
	docker buildx build --platform linux/arm64 .
	docker buildx build --platform linux/386,linux/amd64,linux/arm64 -t binghelisp/hol-dev .

push:
	docker push binghelisp/hol-dev

run:
	docker run -ti --rm binghelisp/hol-dev
