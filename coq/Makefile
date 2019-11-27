all: coq

coq:
	coqc -Q . excomp Exp.v CoreDefs.v Core.v Named.v
	coqc -Q ./langs langs langs/Subst.v


.PHONY: coq
