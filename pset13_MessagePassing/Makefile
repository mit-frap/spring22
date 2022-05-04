.PHONY: coq clean

COQC=coqc -q -R ../frap Frap 

coq:
	$(COQC) Pset13Sig.v
	$(COQC) Pset13.v

clean:
	rm -f *.vo *.vok *.vos *.glob
