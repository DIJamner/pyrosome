all: coq

coq:
	coqc -Q . excomp Utils.v Exp.v Rule.v CoreDefs.v Core.v EasyWF.v Named.v
	coqc -Q ./langs langs langs/Subst.v

clean:
	@rm *.vo *.vok *.vos *.glob


.PHONY: coq clean
