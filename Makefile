all: build 

build:
	dune build src/expert_system.exe
	mv _build/default/src/expert_system.exe .

fclean:
	rm -rf ./_build
	rm -rf expert_system.exe
	rm -rf dune-project

test: build
	ruby ./tests/test.rb

re: fclean all