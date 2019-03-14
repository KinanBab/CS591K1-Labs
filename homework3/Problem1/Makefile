NAME = logic

build: $(NAME).dats
	patscc -o $(NAME) $(NAME).dats

z3: $(NAME).dats
	patsopt -tc --constraint-export -d $(NAME).dats | patsolve_z3 -i -
	patscc --constraint-ignore -o $(NAME) $(NAME).dats

.PHONY: clean
clean:
	rm *.c
	rm $(NAME)
