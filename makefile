all: CoqMakefile
	make -f CoqMakefile

clean: CoqMakefile
	make -f CoqMakefile cleanall

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile
