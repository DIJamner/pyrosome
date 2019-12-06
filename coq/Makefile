all: coq

coq:
	coqc -Q . excomp Utils.v Exp.v Rule.v CoreDefs.v Core.v Named.v
	coqc -Q ./langs langs langs/Subst.v


.PHONY: coq
