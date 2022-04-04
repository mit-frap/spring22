.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Pset9Sig.v
	$(COQC) Pset9.v

clean:
	rm -f *.vo *.vok *.vos *.glob
