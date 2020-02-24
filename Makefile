.PHONY: all clean fclean re

NAME = expert_system

PKG = core

CC = ocamlfind ocamlopt
CC_INT = ocamlfind ocamlc -opaque

SIDE_DIR = ./_build/

CFLAGS += -linkpkg -thread -package $(PKG)

# **************************************************************************** #
#                                  MODULES                                     #
# **************************************************************************** #

OBJ_DIR = $(SIDE_DIR)obj/

SRC_DIR = ./src/

SRC_ = \
		Library.ml \
		Operation.ml \
		Btree.ml \
		Lexer.ml \
		ReadFile.ml \
		Checker.ml 

# **************************************************************************** #
#                                  INTERFACES                                  #
# **************************************************************************** #

CMI_DIR = $(SIDE_DIR)cmi/

INC_CMI = -I $(CMI_DIR)

INT_DIR = ./src/

INT_ = \
		Library.mli \
		Operation.mli \
		Btree.mli \
		Lexer.mli \
		ReadFile.mli \
		Checker.mli

CMI = $(INT_:%.mli=$(CMI_DIR)%.cmi)

INT = $(addprefix $(INT_DIR), $(INT_))

# **************************************************************************** #
#                                  SOURCES                                     #
# **************************************************************************** #

OBJ_DIR = $(SIDE_DIR)obj/

SRC_DIR = ./src/

SRC_ += \
		parser.ml 

OBJ = $(SRC_:%.ml=$(OBJ_DIR)%.cmx)

SRC = $(addprefix $(SRC_DIR), $(SRC_))

# **************************************************************************** #
#                                    RULES                                     #
# **************************************************************************** #


all: $(NAME)

install:
	@brew install opam
	@eval $(opam config env)
	@opam install $(PKG)

$(NAME): $(CMI_DIR) $(CMI) $(OBJ_DIR) $(OBJ)
	@printf "== \x1b[35m$(NAME)\x1b[0m ========================================================\n"
	$(CC) $(CFLAGS) $(OBJ) -o $(NAME)

$(OBJ_DIR):
	@mkdir -p $@

$(CMI_DIR):
	@mkdir -p $@

printsrc:
	@printf "== \x1b[34mSources\x1b[0m ========================================================\n"

printint:
	@printf "== \x1b[34mInterfaces\x1b[0m =====================================================\n"

$(OBJ_DIR)%.cmx: $(SRC_DIR)%.ml | printsrc 
	@printf "$< -> $@\n"
	@$(CC) $(CFLAGS) -c -I $(CMI_DIR) -o $@ $<

$(CMI_DIR)%.cmi: $(INT_DIR)%.mli | printint
	@printf "$< -> $@\n"
	@$(CC_INT) -c -o $@ $<

clean:
	rm -rf $(SIDE_DIR)

fclean: clean
	rm -rf $(NAME)

re: fclean all
