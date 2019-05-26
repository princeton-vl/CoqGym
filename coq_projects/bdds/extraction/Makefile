CC= $(CAMLBIN)ocamlopt
FLAGS = -cclib -lunix
LIB= unix.cmxa

LEX= $(CAMLBIN)ocamllex
YACC= $(CAMLBIN)ocamlyacc

OBJ_I = dyade.cmi \
	parser.cmi

OBJ= 	dyade.cmx \
	lexer.cmx \
	parser.cmx \
	main.cmx \

PROG= dyade


all : 	$(PROG)

$(PROG) :  $(OBJ_I) $(OBJ)	
	$(CC) $(FLAGS) -o $(PROG) $(LIB) $(OBJ) 

parser.ml parser.mli : parser.mly
	$(YACC) parser.mly

lexer.ml : lexer.mll
	$(LEX) lexer.mll

%.cmi : %.mli
	$(CC) -c $<

%.cmx : %.ml
	$(CC) -c $<	 


clean : 	
	rm -f *.o *.cmx *.cmi \
	$(PROG) \
	lexer.ml \
	parser.ml \
	parser.mli

parser.cmx : dyade.cmi
parser.cmi : dyade.cmi
main.cmx : lexer.cmx
lexer.cmx : parser.cmi

install :
	true
