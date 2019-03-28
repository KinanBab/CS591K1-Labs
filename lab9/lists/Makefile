NAME=list

$(NAME): $(NAME).agda
	agda --compile $(NAME).agda

.PHONY: clean
clean:
	rm -rf MAlonzo/ $(NAME) $(NAME).agdai "#$(NAME)#" *~
