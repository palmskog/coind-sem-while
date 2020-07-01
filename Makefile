COQC=ssrcoq  -compile
COQDEP=coqdep 
FILES=Trace.v Language.v BigRel.v SmallRel.v BigFunct.v SmallFunct.v Alternatives.v

all: $(FILES:.v=.vo)
	@echo "done"

clean:
	-rm $(FILES:.v=.vo)

.SUFFIXES: .v .vo

.v.vo:
	$(COQC) $*

Trace.vo: Trace.v
Language.vo: Language.v Trace.vo
BigRel.vo: BigRel.v Trace.vo Language.vo
SmallRel.vo: SmallRel.v Trace.vo Language.vo BigRel.vo
BigFunct.vo: BigFunct.v Trace.vo Language.vo BigRel.vo
SmallFunct.vo: SmallFunct.v Trace.vo Language.vo SmallRel.vo BigRel.vo BigFunct.vo
Alternatives.vo: Alternatives.v Trace.vo Language.vo BigRel.vo

