SRC=src/
ROOT=.


all: bnfc insc

bnfc: $(SRC)/Latte.cf
	cd $(SRC) && bnfc -m -haskell --functor Latte.cf && make && cd ..

insc: $(SRC)/TypeChecker.hs
	cd $(SRC) && ghc TypeChecker.hs -o insc && cd ..
	mv $(SRC)/insc $(ROOT)/insc

clean:
	rm insc && cd $(SRC) && make distclean