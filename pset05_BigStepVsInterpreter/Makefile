.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Pset5Sig.v
	$(COQC) Pset5.v

clean:
	rm -f *.vo *.glob *.aux .*.aux .*.cache *.vok *.vos
