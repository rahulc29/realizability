check:
	cd src
	agda --html --html-dir=docs ./index.agda

commit_message = Commit [Automated by Make]
commit:
	git add . && git commit -m '${commit_message}'

push : commit
	git push origin master
