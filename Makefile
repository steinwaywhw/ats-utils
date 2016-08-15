# PATSCC=$(PATSHOME)/bin/patscc -DATS_MEMALLOC_LIBC
# PATSOPT=$(PATSHOME)/bin/patsopt 
# PATSOLVE=$(PATSHOME)/bin/patsolve_smt
# RMF=rm -f

AR=ar -rcs
PATSOPT=patsopt 
CC=gcc -DATS_MEMALLOC_LIBC -I$(PATSHOME) -I$(PATSHOME)/ccomp/runtime -g
# CCFLAGS=-fPIC 
CCFLAGS=
PATSCC=patscc -DATS_MEMALLOC_LIBC -L$(PWD) -latsutils -g
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


list_dats.c: list.dats 
list_dats.o: list_dats.c 

maybe_dats.c: maybe.dats 
maybe_dats.o: maybe_dats.c

stream_dats.c: stream.dats
stream_dats.o: stream_dats.c

set_dats.c: set.dats
set_dats.o: set_dats.c

map_dats.c: map.dats
map_dats.o: map_dats.c

avl_dats.c: avl.dats
avl_dats.o: avl_dats.c

linstream_dats.c: linstream.dats
linstream_dats.o: linstream_dats.c

string_dats.c: string.dats
string_dats.o: string_dats.c

order_dats.c: order.dats 
order_dats.o: order_dats.c

show_dats.c: show.dats 
show_dats.o: show_dats.c

unit_dats.c: unit.dats 
unit_dats.o: unit_dats.c

# libatsutils.a: maybe_dats.o order_dats.o show_dats.o
libatsutils.a: list_dats.o maybe_dats.o stream_dats.o set_dats.o map_dats.o avl_dats.o linstream_dats.o string_dats.o order_dats.o show_dats.o unit_dats.o
	$(AR) $@ $^

clean: 
	$(RMF) *ats.c *.o

cleanall:
	$(RMF) *ats.c *.o *.a *.out *.out.dSYM

test: libatsutils.a testall.dats 
	$(PATSCC) testall.dats 