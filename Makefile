all:
	cd repl/proof; Holmake
	cd translator/repl; Holmake
	cd bootstrap; Holmake
	cd compiler/tests; Holmake && ./selftest.exe

clean:
	cd semantics; Holmake cleanAll
	cd metatheory; Holmake cleanAll
	cd parsing; Holmake cleanAll
	cd parsing/testing; Holmake cleanAll
	cd inference; Holmake cleanAll
	cd inference/proofs; Holmake cleanAll
	cd bytecode; Holmake cleanAll
	cd compiler; Holmake cleanAll
	cd compiler/tests; Holmake cleanAll
	cd compiler/proofs; Holmake cleanAll
	cd repl; Holmake cleanAll
	cd repl/proofs; Holmake cleanAll
	cd translator; Holmake cleanAll
	cd translator/repl; Holmake cleanAll
	cd translator/simulator; Holmake cleanAll
	cd translator/okasaki-examples; Holmake cleanAll
	cd translator/other-examples; Holmake cleanAll
	cd bootstrap; Holmake cleanAll
	cd x86-64; Holmake cleanAll
	cd hol-light; Holmake cleanAll
	make -C unverified/interp clean
	make -C unverified/bytecode clean
