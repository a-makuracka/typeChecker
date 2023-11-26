SRC=src/
ROOT=.


all: bnfc typeCheck

bnfc: $(SRC)/Latte.cf
	cd $(SRC) && bnfc -m -haskell --functor Latte.cf && make && cd ..

typeCheck: $(SRC)/TypeChecker.hs
	cd $(SRC) && ghc TypeChecker.hs -o typeCheck && cd ..
	mv $(SRC)/typeCheck $(ROOT)/typeCheck

clean:
	rm typeCheck && cd $(SRC) && make distclean