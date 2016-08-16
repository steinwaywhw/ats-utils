

AR=ar -rcs
PATSOPT=patsopt 
CC=gcc -DATS_MEMALLOC_LIBC -I$(PATSHOME) -I$(PATSHOME)/ccomp/runtime -g
CCFLAGS=-fPIC -O2
PATSCC=patscc -DATS_MEMALLOC_LIBC -L$(PWD) -latsutils -g --tlcalopt-disable
RMF=rm -rf

# all:: intset
# intset:: intset.dats; $(PATSOPT) -tc --constraint-export -d $< | $(PATSOLVE) -i
# intset:: intset.dats; $(PATSCC) --constraint-ignore -o $@ $<
# regress:: intset; ./intset 
# cleanall:: ; $(RMF) intset


# testall:: all
# testall:: regress
# testall:: cleanall

# clean:: ; $(RMF) *~
# clean:: ; $(RMF) *_?ats.c

# cleanall:: clean


# tc: mset_tc

# mset_tc: mset.dats
# 	$(PATSOPT) -tc --constraint-export -d $< | $(PATSOLVE) -i | tee ./test | z3 -smt2 -in


all: libatsutils.a

%_sats.c: %.sats 
	$(PATSOPT) -o $@ -s $^

%_dats.c: %.dats
	$(PATSOPT) -o $@ -d $^

%.o: %.c 
	$(CC) $(CCFLAGS) -c $^ -o $@

libatsutils.a: list_dats.o maybe_dats.o stream_dats.o set_dats.o map_dats.o avl_dats.o linstream_dats.o string_dats.o order_dats.o show_dats.o unit_dats.o
	$(AR) $@ $^

clean: 
	$(RMF) *ats.c *.o

cleanall:
	$(RMF) *ats.c *.o *.a *.out *.out.dSYM

test: libatsutils.a testall.dats 
	$(PATSCC) testall.dats 