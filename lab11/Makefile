NAME=list

agda: agda.agda
	agda --compile agda.agda

agda2: agda2.agda
	agda --compile agda2.agda

ats: ats.dats
	patscc -DATS_MEMALLOC_LIBC -o ats ats.dats

ats-z3: ats.dats
	patsopt -tc --constraint-export -d ats.dats | patsolve_z3 -i -
	patscc -DATS_MEMALLOC_LIBC --constraint-ignore -o ats-z3 ats.dats

.PHONY: clean
clean:
	rm -rf MAlonzo/ agda agda.agdai "#agda#" agda2 agda2.agdai "#agda2#" ats ats_dats.c ats-z3 ats-z3_dats.c *~
