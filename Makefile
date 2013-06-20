test:
	cd semantics; Holmake
	cd parsing; Holmake
	cd implementation; Holmake
	cd metatheory; Holmake
	cd impl_proofs; Holmake
	cd translator; Holmake
	cd hol-light; Holmake
	cd compiler/tests; Holmake && ./selftest.exe
	cd compiler/proofs; Holmake

clean:
	cd metatheory; Holmake cleanAll
	cd semantics; Holmake cleanAll
	cd parsing; Holmake cleanAll
	cd implementation; Holmake cleanAll
	cd impl_proofs; Holmake cleanAll
	cd translator; Holmake cleanAll
	cd hol-light; Holmake cleanAll
	cd compiler; Holmake cleanAll
	cd compiler/tests; Holmake cleanAll
	cd compiler/proofs; Holmake cleanAll

all_lem:
	make -C semantics
	make -C metatheory
	make -C translator

clean_lem:
	make -C semantics clean
	make -C metatheory clean
	make -C translator clean
