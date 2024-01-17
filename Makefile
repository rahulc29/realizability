HTML_DIR=docs
build:
	agda --html --html-dir=${HTML_DIR} src/index.agda
pipe: build
	git add .
	git commit -m "Complete render"
	git push origin master
