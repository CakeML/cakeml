test:
	cd metatheory; Holmake
	cd compiler/emit; Holmake && ./selftest.exe
	cd compiler/correctness; Holmake
	cd hol-light; Holmake
	cd type_check; Holmake

clean:
	cd metatheory; Holmake cleanAll
	cd semantics; Holmake cleanAll
	cd implementation; Holmake cleanAll
	cd translator; Holmake cleanAll

all_lem:
	make -C semantics
	make -C metatheory
	make -C translator

clean_lem:
	make -C semantics clean
	make -C metatheory clean
	make -C translator clean
