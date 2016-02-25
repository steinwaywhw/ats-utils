PATSCC=$(PATSHOME)/bin/patscc -DATS_MEMALLOC_LIBC
PATSOPT=$(PATSHOME)/bin/patsopt 
PATSOLVE=$(PATSHOME)/bin/patsolve_z3
RMF=rm -f

all:: intset
intset:: intset.dats; $(PATSOPT) -tc --constraint-export -d $< | $(PATSOLVE) -i
intset:: intset.dats; $(PATSCC) --constraint-ignore -o $@ $<
regress:: intset; ./intset 
cleanall:: ; $(RMF) intset


testall:: all
testall:: regress
testall:: cleanall

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.c

cleanall:: clean

