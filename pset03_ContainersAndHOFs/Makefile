.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Pset3Sig.v
	$(COQC) Pset3.v

clean:
	rm -f *.vo *.glob .*.aux *.aux .lia.cache .nia.cache *.vok *.vos
