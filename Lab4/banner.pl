%% A factory produces banners using only a set of existing rectangular pieces.
%% Our goal is to find out how to use the minimum set of pieces that exactly match the design of the banner.
%% Note that pieces can be rotated if necessary. Also, note that each piece can be used at most once.
%% That's why there can be several identical pieces in the input.

%% Una fábrica produce pancartas utilizando solo un conjunto de piezas rectangulares existentes.
%% Nuestro objetivo es descubrir cómo usar el conjunto mínimo de piezas que coinciden exactamente
%% con el diseño del banner. Tenga en cuenta que las piezas se pueden girar si es necesario.
%% Además, tenga en cuenta que cada pieza se puede utilizar como máximo una vez.
%% Es por eso que puede haber varias piezas idénticas en la entrada.

%%%%%%%%%%%%%%%%%%%%% INPUT EXAMPLE:

%% banner( [                             the x's define the design of the banner
%% 	       [.,x,x,x,.,.,.,x,x,x,.],
%% 	       [.,x,x,x,.,.,.,x,x,x,.],
%% 	       [.,x,x,x,.,.,.,x,x,x,.],
%% 	       [.,x,x,x,x,x,x,x,x,x,.],
%% 	       [.,x,x,x,x,x,x,x,x,x,.],
%% 	       [.,x,x,x,.,.,.,x,x,x,.],
%% 	       [.,x,x,x,.,.,.,x,x,x,.],
%% 	       [.,x,x,x,.,.,.,x,x,x,.]
%% 	   ]).
%% pieces([
%% 	    [1,3,8],   % piece 1 is a 3 x 8 rectangle
%% 	    [2,3,3],   % piece 2 is a 3 x 3 rectangle
%% 	    [3,9,2],   % ...
%% 	    [4,3,3],
%% 	    [5,3,8],
%% 	    [6,3,2],
%% 	    [7,3,3],
%% 	    [8,3,3],
%% 	    [9,2,3],
%% 	    [a,1,3]	    
%% 	  ]).

%% A possible solution using 6 pieces:
%% .444...888.
%% .444...888.
%% .444...888.
%% .333333333.
%% .333333333.
%% .a99...777.
%% .a99...777.
%% .a99...777.

%% An optimal solution using 3 pieces:
%% .555...111.
%% .555...111.
%% .555...111.
%% .555666111.
%% .555666111.
%% .555...111.
%% .555...111.
%% .555...111.

:-include(input5).
symbolicOutput(0). % set to 1 to see symbolic output only; 0 otherwise.

maxPieces(MP):- widthBanner(W),heightBanner(H), MP is W*H.

%%%%%% Some helpful definitions to make the code cleaner:
piece(P):-                  pieces(L), member([P,_,_],L).
pieceSize(P,W,H):-          pieces(L), member([P,W,H],L).
widthBanner(W):-            banner(B), member(L,B), length(L,W),!.
heightBanner(H):-           banner(B), length(B,H), !.
contentsCellBanner(X,Y,C):- cell(X,Y), banner(B), heightBanner(H), Y1 is H-Y+1, nth1(Y1,B,L), nth1(X,L,C).
cell(X,Y):-                 widthBanner(W), heightBanner(H), between(1,W,X), between(1,H,Y).


iniciPecaValid(P,X,Y):-
    pieceSize(P,WP,HP),
    cell(X,Y),
    widthBanner(W),
    heightBanner(H),
    WE is X+WP-1,
    HE is Y + HP-1,
    WE =< W,
    HE =< H.
    
iniciPecaGiradaValid(P,X,Y):- 
	pieceSize(P,WP,HP),
	cell(X,Y),
	widthBanner(W),
	heightBanner(H),
	WE is X+HP-1,
	HE is Y + WP-1,
	WE =< W,
	HE =< H.
	
zonaCoverta(P,SX,SY, X,Y):- 
	cell(SX,SY),
	pieceSize(P,WP,HP),
	between(1,HP,Yr),
	between(1,WP,Xr),
	X is SX + Xr-1,
	Y is SY + Yr-1,
	cell(X,Y).
	
zonaCovertaGirada(P,SX,SY, X,Y):- 
	cell(SX,SY),
	pieceSize(P,WP,HP),
	between(1,WP,Yr),
	between(1,HP,Xr), 
	X is SX + Xr-1,
	Y is SY + Yr-1,
	cell(X,Y).

% You can use the following types of symbolic propositional variables:
%   1. pieceCell(P,X,Y) means:   "piece P fills cell [X,Y]" (note: [1,1] is the bottom-left cell of the banner (Careful: Mandatory variable. Otherwise, displaySol will not work)
satVariable( pieceCell(P,X,Y) ):- piece(P), cell(X,Y).
%   2. rotated(P) means:         "piece P is rotated"
satVariable( rotated(P) ):- piece(P).
%   3. pieceStarts(P,X,Y) means: "bottom-left cell of piece P is in cell [X,Y]"
satVariable( pieceStarts(P,X,Y) ):- piece(P), cell(X,Y).
%   4. used(P) means:            "piece P is used"
satVariable( used(P) ):- piece(P).


% ========================== writeClauses(MaxCost) ============================
writeClauses(infinite):- !, maxPieces(N), writeClauses(N), !.
writeClauses(K):-
    almenysKPeces(K),
    pecesNoComencenInvalides,
    generaCelles,
    generaNoCelles,
    generaCellesUsades,
    usadesGenerenComencament,
    noSuperposicionsDeCelles,
    totBannerCovert,
    totBannerNoCovert,
    true,!.

almenysKPeces(K):-findall(used(P),piece(P),Lits), atMost(K,Lits),fail.
almenysKPeces(_).

pecesNoComencenInvalides:-
    piece(P),
    findall(pieceStarts(P,X,Y), iniciPecaValid(P,X,Y), Possible),
    cell(X1,Y1),
    \+member(pieceStarts(P,X1,Y1),Possible),
    writeClause([ -pieceStarts(P,X1,Y1), rotated(P) ]),fail.
pecesNoComencenInvalides:-
    piece(P),
    findall(pieceStarts(P,X,Y), iniciPecaGiradaValid(P,X,Y), Possible),
    cell(X1,Y1),
    \+member(pieceStarts(P,X1,Y1),Possible),
    writeClause([-pieceStarts(P,X1,Y1), -rotated(P)]), fail.
pecesNoComencenInvalides.

generaCelles:-
    piece(P),
    contentsCellBanner(X,Y,x),
    zonaCoverta(P,X,Y, X1,Y1),
    writeClause([-pieceStarts(P,X,Y), rotated(P), pieceCell(P,X1,Y1)]), fail.
generaCelles:-
    piece(P),
    contentsCellBanner(X,Y,x),	
    zonaCovertaGirada(P,X,Y, X1,Y1),
    writeClause([-pieceStarts(P,X,Y), -rotated(P), pieceCell(P,X1,Y1)]), fail.	
generaCelles.

generaNoCelles:-
    piece(P),
    contentsCellBanner(X,Y,x),
    findall(pieceCell(P,X1,Y1), zonaCoverta(P,X,Y, X1,Y1), Covers),
    cell(X2,Y2),
    \+member(pieceCell(P,X2,Y2), Covers),
    writeClause([-pieceStarts(P,X,Y), rotated(P), -pieceCell(P,X2,Y2)]), fail.
generaNoCelles:- 
    piece(P),
    contentsCellBanner(X,Y,x),
    findall(pieceCell(P,X1,Y1), zonaCovertaGirada(P,X,Y, X1,Y1), Covers),
    cell(X2,Y2),
    \+member(pieceCell(P,X2,Y2), Covers),
    writeClause([-pieceStarts(P,X,Y), -rotated(P), -pieceCell(P,X2,Y2)]), fail.	
generaNoCelles.

generaCellesUsades:-
    piece(P), cell(X,Y), writeClause([ -pieceCell(P,X,Y), used(P)]), fail.
generaCellesUsades.

usadesGenerenComencament:-
    piece(P), findall(pieceStarts(P,X,Y), cell(X,Y), C), writeClause([-used(P)|C]), fail.
usadesGenerenComencament.

noSuperposicionsDeCelles:-
    cell(X,Y), findall(pieceCell(P,X,Y), piece(P), Lits), atMost(1, Lits),fail.
noSuperposicionsDeCelles.

totBannerCovert:- %no need for exactly since noSuperposicionsDeCelles.
    contentsCellBanner(X,Y,x), findall(pieceCell(P,X,Y), piece(P), Lits), atLeast(1,Lits),fail.
totBannerCovert.

totBannerNoCovert:-
    contentsCellBanner(X,Y,.),
    piece(P),	
    writeClause([ -pieceCell(P,X,Y) ]),
    writeClause([ -pieceStarts(P,X,Y) ]),fail. % added pieceStarts to optimize calculus
totBannerNoCovert.



%============================ Display =============================

displaySol(M):-
    widthBanner(W),
    heightBanner(H),
    between(1,H,YB),
    nl,
    Y is H-YB+1,
    between(1,W,X),
    writeCell(M,X,Y),
    fail.
displaySol(_):-nl.

writeCell(M,X,Y):- member(pieceCell(P,X,Y),M), !, write(P).
writeCell(_,_,_):- write('.').

% ====================== Calcul del cost =======================
costOfThisSolution(M,Cost):-
    findall(used(P), member(used(P),M), Lits),
	length(Lits, Cost),
    true. 


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% No need to modify anything beow this line:

main:-  symbolicOutput(1), !, writeClauses(infinite), halt.   % print the clauses in symbolic form and halt
main:-    
    told, write('Looking for initial solution with arbitrary cost...'), nl,
    initClauseGeneration,
    tell(clauses), writeClauses(infinite), told,
    tell(header),  writeHeader,  told,
    numVars(N), numClauses(C), 
    write('Generated '), write(C), write(' clauses over '), write(N), write(' variables. '),nl,
    shell('cat header clauses > infile.cnf',_),
    write('Launching picosat...'), nl,
    shell('picosat -v -o model infile.cnf', Result),  % if sat: Result=10; if unsat: Result=20.
    treatResult(Result,[]),!.

treatResult(20,[]       ):- write('No solution exists.'), nl, halt.
treatResult(20,BestModel):-
    nl,nl, costOfThisSolution(BestModel,Cost), write('Unsatisfiable. So the optimal solution was this one with cost '),
    write(Cost), write(':'), nl, displaySol(BestModel), halt.
treatResult(10,_):- %   shell('cat model',_),
    write('Solution found '), flush_output,
    see(model), symbolicModel(M), seen,
    costOfThisSolution(M,Cost),
    write('with cost '), write(Cost), nl,nl,
    displaySol(M), 
    Cost1 is Cost-1,   nl,nl,nl,nl,nl,  write('Now looking for solution with cost '), write(Cost1), write('...'), nl,
    initClauseGeneration, tell(clauses), writeClauses(Cost1), told,
    tell(header),  writeHeader,  told,
    numVars(N),numClauses(C),
    write('Generated '), write(C), write(' clauses over '), write(N), write(' variables. '),nl,
    shell('cat header clauses > infile.cnf',_),
    write('Launching picosat...'), nl,
    shell('picosat -v -o model infile.cnf', Result),  % if sat: Result=10; if unsat: Result=20.
    treatResult(Result,M),!.
treatResult(_,_):- write('cnf input error. Wrote something strange in your cnf?'), nl,nl, halt.
    

initClauseGeneration:-  %initialize all info about variables and clauses:
	retractall(numClauses(   _)),
	retractall(numVars(      _)),
	retractall(varNumber(_,_,_)),
	assert(numClauses( 0 )),
	assert(numVars(    0 )),     !.

writeClause([]):- symbolicOutput(1),!, nl.
writeClause([]):- countClause, write(0), nl.
writeClause([Lit|C]):- w(Lit), writeClause(C),!.
w(-Var):- symbolicOutput(1), satVariable(Var), write(-Var), write(' '),!. 
w( Var):- symbolicOutput(1), satVariable(Var), write( Var), write(' '),!. 
w(-Var):- satVariable(Var),  var2num(Var,N),   write(-), write(N), write(' '),!.
w( Var):- satVariable(Var),  var2num(Var,N),             write(N), write(' '),!.
w( Lit):- told, write('ERROR: generating clause with undeclared variable in literal '), write(Lit), nl,nl, halt.


% given the symbolic variable V, find its variable number N in the SAT solver:
var2num(V,N):- hash_term(V,Key), existsOrCreate(V,Key,N),!.
existsOrCreate(V,Key,N):- varNumber(Key,V,N),!.                            % V already existed with num N
existsOrCreate(V,Key,N):- newVarNumber(N), assert(varNumber(Key,V,N)), !.  % otherwise, introduce new N for V

writeHeader:- numVars(N),numClauses(C), write('p cnf '),write(N), write(' '),write(C),nl.

countClause:-     retract( numClauses(N0) ), N is N0+1, assert( numClauses(N) ),!.
newVarNumber(N):- retract( numVars(   N0) ), N is N0+1, assert(    numVars(N) ),!.

% Getting the symbolic model M from the output file:
symbolicModel(M):- get_code(Char), readWord(Char,W), symbolicModel(M1), addIfPositiveInt(W,M1,M),!.
symbolicModel([]).
addIfPositiveInt(W,L,[Var|L]):- W = [C|_], between(48,57,C), number_codes(N,W), N>0, varNumber(_,Var,N),!.
addIfPositiveInt(_,L,L).
readWord( 99,W):- repeat, get_code(Ch), member(Ch,[-1,10]), !, get_code(Ch1), readWord(Ch1,W),!. % skip line starting w/ c
readWord(115,W):- repeat, get_code(Ch), member(Ch,[-1,10]), !, get_code(Ch1), readWord(Ch1,W),!. % skip line starting w/ s
readWord(-1,_):-!, fail. %end of file
readWord(C,[]):- member(C,[10,32]), !. % newline or white space marks end of word
readWord(Char,[Char|W]):- get_code(Char1), readWord(Char1,W), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Everything below is given as a standard library, reusable for solving 
%    with SAT many different problems.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Express that Var is equivalent to the disjunction of Lits:
expressOr( Var, Lits) :- symbolicOutput(1), write( Var ), write(' <--> or('), write(Lits), write(')'), nl, !. 
expressOr( Var, Lits ):- member(Lit,Lits), negate(Lit,NLit), writeClause([ NLit, Var ]), fail.
expressOr( Var, Lits ):- negate(Var,NVar), writeClause([ NVar | Lits ]),!.

% Express that Var is equivalent to the conjunction of Lits:
expressAnd( Var, Lits) :- symbolicOutput(1), write( Var ), write(' <--> and('), write(Lits), write(')'), nl, !. 
expressAnd( Var, Lits):- member(Lit,Lits), negate(Var,NVar), writeClause([ NVar, Lit ]), fail.
expressAnd( Var, Lits):- findall(NLit, (member(Lit,Lits), negate(Lit,NLit)), NLits), writeClause([ Var | NLits]), !.


%%%%%% Cardinality constraints on arbitrary sets of literals Lits:

exactly(K,Lits):- symbolicOutput(1), write( exactly(K,Lits) ), nl, !.
exactly(K,Lits):- atLeast(K,Lits), atMost(K,Lits),!.

atMost(K,Lits):- symbolicOutput(1), write( atMost(K,Lits) ), nl, !.
atMost(K,Lits):-   % l1+...+ln <= k:  in all subsets of size k+1, at least one is false:
	negateAll(Lits,NLits),
	K1 is K+1,    subsetOfSize(K1,NLits,Clause), writeClause(Clause),fail.
atMost(_,_).

atLeast(K,Lits):- symbolicOutput(1), write( atLeast(K,Lits) ), nl, !.
atLeast(K,Lits):-  % l1+...+ln >= k: in all subsets of size n-k+1, at least one is true:
	length(Lits,N),
	K1 is N-K+1,  subsetOfSize(K1, Lits,Clause), writeClause(Clause),fail.
atLeast(_,_).

negateAll( [], [] ).
negateAll( [Lit|Lits], [NLit|NLits] ):- negate(Lit,NLit), negateAll( Lits, NLits ),!.

negate( -Var,  Var):-!.
negate(  Var, -Var):-!.

subsetOfSize(0,_,[]):-!.
subsetOfSize(N,[X|L],[X|S]):- N1 is N-1, length(L,Leng), Leng>=N1, subsetOfSize(N1,L,S).
subsetOfSize(N,[_|L],   S ):-            length(L,Leng), Leng>=N,  subsetOfSize( N,L,S).
