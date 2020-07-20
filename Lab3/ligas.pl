% Problema 1: planificación de ligas deportivas. La liga española de primera división de fútbol tiene 20 equipos, que juegan todos contra todos en 19 jornadas la primera vuelta, y otra vez en otras 19 jornadas en la segunda vuelta, en el mismo orden, pero en casa del otro. Hay que admitir los siguientes tipos de restricciones:
% –el equipo i no quiere jugar en casa la jornada j,
% –el equipo i sı́ quiere jugar en casa la jornada j,
% –en las jornadas i e i + 1 no se admiten repeticiones: dos partidos seguidos en casa, o dos partidos seguidos fuera,
% –el partido i-i0 (es decir, en casa del equipo i) no debe ser la jornada j
% –el partido i-i0 (es decir, en casa del equipo i) sı́ debe ser la jornada j.
% No se permitirán tripeticiones, es decir, ningún equipo jugará tres jornadas seguidas en casa ni tres jornadas seguidas fuera. Recomendación: primero aborda un subproblema, por ejemplo, una sola vuelta, pocos equipos, etc. Extensión: a lo largo de la temporada ningún equipo tiene más de k repeticiones (esto puede hacer que el problema SAT sea duro para ligas de mas de 16 equipos).


:-include(entradaLigas).
symbolicOutput(0).  % set to 1 to see symbolic output only; 0 otherwise.


%%%%%% Some helpful definitions to make the code cleaner:
equipo(E):-     numEquipos(NE), between(1,NE,E).
jornada(J):-    numEquipos(NE), N is (NE - 1) * 2, between(1,N,J).
jornadaV(J):-    numEquipos(NE), N is (NE - 1) * 2, between(NE,N,J).
idaVuelta(I):-  between(1,2,I).
pareja(P):-     numEquipos(NE), N is (NE - 1), between(1,N,P).

calcVuelta(J1,J2):-
    numEquipos(NE),        
    N1 is NE - 1,
    N2 is N1 * 2,    
    J2 is (((J1 - 1) + N1) mod N2) + 1.
calcVuelta.

%%%%%%  1. SAT Variables:
satVariable( ej(E,J) ):- equipo(E), jornada(J).
satVariable( pj(L,V,J) ):- equipo(L), equipo(V), jornada(J).

%%%%%%  2. Clause generation:

writeClauses:-     
    equipoJornada,
    pj2ej,
    
    noMismoEquipo,
    partidoJornada,
    vuelta,            
    unPartidoPorJornadaLocal,
       
    siPartido,
    noPartido,    
    noEnCasa,
    noFuera,
    noRepes,   
    
    true,!.                    % this way you can comment out ANY previous line of writeClauses
writeClauses:- told, nl, write('writeClauses failed!'), nl,nl, halt.


%========================== ej ==================================

equipoJornada:-
    equipo(E),
    findall(ej(E,J), jornada(J), Lits),
    numEquipos(NE),
    N is (NE - 1) * 2,
    exactly(N,Lits), fail.
equipoJornada.

pj2ej:-
    equipo(L),
    equipo(V),
    L \= V,
    jornada(J),
    writeClause([ -pj(L,V,J), ej(L,J) ]),
    writeClause([ -pj(L,V,J), ej(V,J) ]), fail.
pj2ej.

%=========================== pj ==============================

noMismoEquipo:-
    equipo(E),
    jornada(J),
    writeClause([ -pj(E,E,J) ]), fail.
noMismoEquipo.

partidoJornada:-
    equipo(L),
    equipo(V),
    L < V,
    findall(pj(L,V,J1), jornada(J1), Lits1),    
    exactly(1,Lits1),
    J1 \= J2,
    findall(pj(V,L,J2), jornada(J2), Lits2),    
    exactly(1,Lits2), fail.
partidoJornada.

vuelta:-
    equipo(L),
    equipo(V),
    L < V,
    jornada(J),    
    calcVuelta(J,J2),
    writeClause([ -pj(L,V,J), pj(V,L,J2) ]), fail.
vuelta.


unPartidoPorJornadaLocal:-
    equipo(L),    
    equipo(V1),
    equipo(V2),
    L \= V1,
    L \= V2,
    V1 \= V2,
    jornada(J),
    writeClause([ -pj(L,V1,J), -pj(L,V2,J) ]),
    writeClause([ -pj(L,V2,J), -pj(L,V1,J) ]),
    writeClause([ -pj(V1,L,J), -pj(V2,L,J) ]),
    writeClause([ -pj(V2,L,J), -pj(V1,L,J) ]),    
    writeClause([ -pj(L,V1,J), -pj(V2,L,J) ]),
    writeClause([ -pj(L,V2,J), -pj(V1,L,J) ]),
    fail.
unPartidoPorJornadaLocal.


%======================= restricciones ==========================

siPartido:-
    equipo(L),
    equipo(V),
    jornada(J),
    sipartido(L,V,J),
    writeClause([ pj(L,V,J) ]), fail.
siPartido.

noPartido:-
    equipo(L),
    equipo(V),
    jornada(J),
    nopartido(L,V,J),
    writeClause([ -pj(L,V,J) ]), fail.
noPartido.

noEnCasa:-
    equipo(L),
    equipo(V),
    jornada(J),
    nocasa(L,J),
    writeClause([ -pj(L,V,J) ]), fail.
noEnCasa.

noFuera:-
    equipo(L),
    equipo(V),
    jornada(J),
    nofuera(V,J),
    writeClause([ -pj(L,V,J) ]), fail.
noFuera.

noRepes:-
    equipo(L),
    jornada(J1),
    jornada(J2),
    norepes(J1,J2),    
    findall( pj(L,V,J1), equipo(V), Lits1),
    atMost(1, Lits1),
    findall( pj(L,V,J2), equipo(V), Lits1),
    atMost(0, Lits1),
    fail.
noRepes.





%%%%%%  3. DisplaySol: show the solution. Here M contains the literals that are true in the model:

%============================ Tabla =============================

escribeSiPartido(L,V,M):- L < V, jornada(J), member(pj(L,V,J),M), write(J),!.
escribeSiPartido(L,V,M):- L > V, jornada(J), member(pj(L,V,J),M), write(J),!.
escribeSiPartido(_,_,_):- write('--').

displayFile:- write('L'),put(92),write('V'), write('\t'), equipo(E), write(E), write('\t'),fail.
displayFile.

escribeJornadas(L,V,M):-      
    escribeSiPartido(L,V,M).
escribeJornadas.

writeNDashes(N):- between(1,N,_), write('='), fail.
writeNDashes(_).

displayCol(M):- equipo(L), nl, write(L), write('\t'), equipo(V), escribeJornadas(L,V,M), write('\t'),fail.
displayCol.

mostrarTabla(_):- nl, nl, displayFile, fail.
mostrarTabla(M):- nl, numEquipos(NE),N is NE * 8, writeNDashes(N), displayCol(M), nl, nl, fail.
mostrarTabla.

%============================ Nums ================================

mostrarNums(M):- nl, write('ej: '), equipo(E), jornada(J), member(ej(E,J), M), write(ej(E,J)), write(' '), fail.
mostrarNums(M):- nl, write('pj: '), equipo(L), equipo(V), jornada(J), member(pj(L,V,J), M), write(pj(L,V,J)), write(' '), fail.
mostrarNums.

%============================ Display =============================

displaySol(M):- nl, write('Literales de la solución:'), nl, mostrarNums(M), fail.
displaySol(M):- nl, nl, mostrarTabla(M), fail.
displaySol(_):- nl,nl.

line(I):-member(I,[4,7]), nl,!.
line(_).
space(J):-member(J,[4,7]), write(' '),!.
space(_).

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


%%%%%% main:

main:-  symbolicOutput(1), !, writeClauses, halt.   % print the clauses in symbolic form and halt
main:-  initClauseGeneration,
tell(clauses), writeClauses, told,          % generate the (numeric) SAT clauses and call the solver
tell(header),  writeHeader,  told,
numVars(N), numClauses(C),
write('Generated '), write(C), write(' clauses over '), write(N), write(' variables. '),nl,
shell('cat header clauses > infile.cnf',_),
write('Calling solver....'), nl,
shell('picosat -v -o model infile.cnf', Result),  % if sat: Result=10; if unsat: Result=20.
	treatResult(Result),!.

treatResult(20):- write('Unsatisfiable'), nl, halt.
treatResult(10):- write('Solution found: '), nl, see(model), symbolicModel(M), seen, displaySol(M), nl,nl,halt.
treatResult( _):- write('cnf input error. Wrote anything strange in your cnf?'), nl,nl, halt.
    

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
:-dynamic(varNumber / 3).
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
%========================================================================================

