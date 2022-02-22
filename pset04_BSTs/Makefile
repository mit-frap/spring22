.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Pset4Sig.v
	$(COQC) Pset4.v

clean:
	rm -f *.vo* .*.aux *.cache *.glob
