.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Pset10Sig.v
	$(COQC) Pset10.v

clean:
	rm -f *.vo *.vok *.vos *.glob
