% Problema 2: planificación del horario semanal de la FIB:
% - Cinco dı́as de 8 a 20h (12 horas diarias).
% - En los datos de entrada se indican las listas de aulas, profesores, y cursos que hay.
% - Todos ellos reciben un natural no nulo como identificador.
% - Por cada curso se da su lista de asignaturas, cada una con su número de horas semanales
%   de clase (máximo una al dı́a), la lista de aulas adecuadas para ella, y la lista de profesores que la podrı́an impartir.
% - Todas las sesiones de una misma asignatura deben impartirse en la misma aula por el mismo profesor.
% - Por cada profesor se indican las horas (con un entero entre 1 y 60) en que no puede dar clase.
% - Por supuesto, no puede haber más de una clase a la vez por profesor ni por aula.
% - Cada curso ha de tener un horario compacto (sin horas libres entre dos clases el mismo dı́a) y no más de seis horas de clase al dı́a.
% - Sesiones de un mismo curso no pueden solaparse en el tiempo.

% Ayuda: es mejor introducir diversos tipos de variables que relacionan dos entidades (profesor-asignatura, asignatura-hora, etc.)
% que tener variables que relacionan más de dos. Hay que mostrar la solución por horas (cada hora qué hay) y despúes de cada curso (qué clases tiene).

:-include(entradaHoraris1).
symbolicOutput(0). % set to 1 to see symbolic output only; 0 otherwise. 


%%%%%% Some helpful definitions to make the code cleaner:
assignatura(A):-  numAssignatures(NA),    between(1,NA,A).
aula(AU):-  numAules(NA),           between(1,NA,AU).
profe(P):-  numProfes(NP),          between(1,NP,P).
curs(C):-   numCursos(NC),          between(1,NC,C).
hora(H):-   between(8,19,H).
dia(D):-    between(1,5,D).
cursAssig(C,A):-    assig(C,A,_,_,_).
assigHores(A,Hs):-  assig(_,A,Hs,_,_).
assigAules(A,AU):-   assig(_,A,_,AU,_).
assigProfes(A,P):-   assig(_,A,_,_,P).

calcDiaSemana(D,H,HS):- D1 is (D-1) * 12, HS is D1 + (H - 7).

%%%%%%  1. SAT Variables:
satVariable( ap(A,P)  ):- assignatura(A), profe(P).
satVariable( aa(A,AU) ):- assignatura(A), aula(AU).
satVariable( aap(A,AU,P)    ):- assignatura(A), aula(AU), profe(P).
satVariable( ad(A,D)  ):- assignatura(A), dia(D).
satVariable( ah(A,H) ):- assignatura(A), hora(H).
satVariable( adh(A,D,H)         ):- assignatura(A), dia(D), hora(H).
satVariable( aadh(A,AU,D,H)    ):- assignatura(A), aula(AU), dia(D), hora(H).
satVariable( apdh(A,P,D,H) ):- assignatura(A), profe(P), dia(D), hora(H).

%%%%%%%%%%%%%%%% Gen Hores Setmana %%%%%%%%%%%%%%%%

writeClauses:-   
    minHoresPerAssignatures,
    maxHoresPerAssignatures,
    ad_ah2adh,
    ad_ah_ap2apdh,
    
    unProfePerAssig,
    nomesUnProfe,
    unAulaPerAssig,
    nomesUnAula,
    
    aa_ap2aap,
    aap2aa_ap,
    
    unaAssigProfeAula,
    unaAssigAulaProfe,
    
    limitClasesDies,
    ad_ah2adh,    
    
    
    prohibicioHores,
    aa_ad_ah2aadh,
    
    noSolapamentClases,
    noSolapamentClasesCurs,    
    noSolapamentProfes,
    true,!.
writeClauses:- told, nl, write('writeClauses failed!'), nl,nl, halt.

unProfePerAssig:-    
    assignatura(A),    
    findall(ap(A,P), (assigProfes(A,Ps),member(P,Ps)), Lits),
    exactly(1,Lits), fail.
unProfePerAssig.

nomesUnProfe:-
    assignatura(A),
    findall(ap(A,P), profe(P), List),
    exactly(1,List), fail.
nomesUnProfe.

unAulaPerAssig:-    
    assignatura(A),    
    findall(aa(A,AU), (assigAules(A,AUs),member(AU,AUs)), Lits),
    exactly(1,Lits), fail.
unAulaPerAssig.

nomesUnAula:-
    assignatura(A),
    findall(aa(A,AU), aula(AU), List),
    exactly(1,List), fail.
nomesUnAula.

aa_ap2aap:-
    assignatura(A),
    profe(P),
    aula(AU),
    writeClause([ -ap(A,P), -aa(A,AU), aap(A,AU,P) ]), fail.
aa_ap2aap.

aap2aa_ap:-
    assignatura(A),
    profe(P),
    aula(AU),
    writeClause([ -aap(A,AU,P), aa(A,AU) ]),
    writeClause([ -aap(A,AU,P), ap(A,P) ]), fail.
aap2aa_ap.

unaAssigProfeAula:-
    assignatura(A),
    aula(AU),
    profe(P1),
    profe(P2),
    P1 \= P2,
    writeClause([ -aap(A,AU,P1), -aap(A,AU,P2) ]), fail.
unaAssigProfeAula.

unaAssigAulaProfe:-
    assignatura(A),
    aula(AU1),
    aula(AU2),
    profe(P),
    AU1 \= AU2,
    writeClause([ -aap(A,AU1,P), -aap(A,AU2,P) ]), fail.
unaAssigAulaProfe.
   

limitClasesDies:-    
    assignatura(A),    
    assigHores(A,Hs),
    findall(ad(A,D), dia(D), Lits),
    exactly(Hs,Lits), fail.
limitClasesDies.


minHoresPerAssignatures:-
    assignatura(A),    
    findall(ah(A,H), hora(H), Lits),
    atLeast(1,Lits), fail.
minHoresPerAssignatures.

maxHoresPerAssignatures:-
    assignatura(A),
    assigHores(A,Hs),
    findall(ah(A,H), hora(H), Lits),
    atMost(Hs,Lits), fail.
maxHoresPerAssignatures.

ad_ah2adh:-
    assignatura(A),
    dia(D),
    hora(H),
    writeClause([-adh(A,D,H), ad(A,D)]),
    writeClause([-adh(A,D,H), ah(A,H)]),
    writeClause([-ad(A,D), -ah(A,H), adh(A,D,H)]), fail.
ad_ah2adh.

ad_ah_ap2apdh:-
    assignatura(A),
    profe(P),
    dia(D),
    hora(H),
    writeClause([-apdh(A,P,D,H), ap(A,P)]),
    writeClause([-apdh(A,P,D,H), ad(A,D)]),
    writeClause([-apdh(A,P,D,H), ah(A,H)]),    
    writeClause([-ad(A,D), -ah(A,H), -ap(A,P), apdh(A,P,D,H)]), fail.
ad_ah_ap2apdh.


prohibicioHores:-
    assignatura(A),
    profe(P),
    dia(D),
    hora(H),
    horesProhibides(P,Hs),
    calcDiaSemana(D,H,HS),
    member(HS,Hs),
    writeClause([-apdh(A,P,D,H)]), fail.
prohibicioHores.


aa_ad_ah2aadh:-
    assignatura(A),
    aula(AU),
    dia(D),
    hora(H),    
    writeClause([ -aadh(A,AU,D,H), aa(A,AU)]),    
    writeClause([ -aadh(A,AU,D,H), ad(A,D)]),
    writeClause([ -aadh(A,AU,D,H), ah(A,H)]),    
    writeClause([ -aa(A,AU), -ad(A,D), -ah(A,H), aadh(A,AU,D,H)]), fail.
aa_ad_ah2aadh.

noSolapamentClases:-    
    aula(AU),    
    dia(D),
    hora(H),
    findall(aadh(A,AU,D,H), assignatura(A), Lits),
    atMost(1, Lits), fail.
noSolapamentClases.

noSolapamentClasesCurs:-
    curs(C),
    assignatura(A1),
    assignatura(A2),
    A1 \= A2,
    cursAssig(C,A1),
    cursAssig(C,A2),
    dia(D),
    hora(H),
    writeClause([ -adh(A1,D,H), -adh(A2,D,H) ]), fail.
noSolapamentClasesCurs.


noSolapamentProfes:-
    assignatura(A1),
    assignatura(A2),
    A1 \= A2,
    profe(P),
    dia(D),
    hora(H),
    writeClause([ -apdh(A1,P,D,H), -apdh(A2,P,D,H) ]), fail.
noSolapamentProfes.


  
%%%%%%  3. DisplaySol: show the solution. Here M contains the literals that are true in the model:

printWithSpacesIfNeeded(A,P,AU):- A < 10, !, write(a-0), write(A-p-P-au-AU).
printWithSpacesIfNeeded(A,P,AU):-
    write(a-A-p-P-au-AU).

printAssigCursDiaHora(C,D,H,M):-
    cursAssig(C,A),
    member(ap(A,P),M),
    member(aa(A,AU),M),
    member(adh(A,D,H),M),           
    printWithSpacesIfNeeded(A,P,AU),!.
printAssigCursDiaHora(_,_,_,_):-write('.............').

writeNDashes(N):- between(1,N,_), write('='), fail.
writeNDashes(_).

writeDashes(N):- N < 10, !, writeNDashes(78).
writeDashes(_):- writeNDashes(77).

displayDays:-
    nl,write('INFORMACIO!!!!: a-AA-p-P-au-AU vol dir a (assignatura), p (professor) i au (aula)'),nl,nl,
    write('        '),
    member(X,['Dilluns  ', 'Dimarts ', ' Dimecres', ' Dijous ', '  Divendres']),
    write(X), write('       '), fail.
displayDays.

displaySchedule(M):-
    hora(H), nl, nl, write(H), write(":00    "), writeDashes(H),
    curs(C), nl, write('Curs '), write(C), write('\t'),    
    dia(D),
    printAssigCursDiaHora(C,D,H,M),
    write('\t'),
    fail.

displaySchedule2(M):-
    curs(C), nl, nl, write('Curs '), write(C), write('   '), writeDashes(C),
    hora(H), nl, write(H), write(":00"),  write('\t'),    
    dia(D),
    printAssigCursDiaHora(C,D,H,M),
    write('\t'),
    fail.


displaySol(M):- nl, nl, displayDays, displaySchedule(M), nl, nl, fail.
displaySol(M):- nl, nl, displayDays, displaySchedule2(M), nl, nl, fail.
displaySol(M):- nl,nl,
    assignatura(A), write('Assignatura '), write(A),
    write(' te el profe: '), member(ap(A,P),M), write(P),
    write(' te l`aula: '), member(aa(A,AU),M), write(AU),
    write(' i s`imparteix a les hores: \n'), member(adh(A,D,H),M), calcDiaSemana(D,H,HS), write(HS),
    nl, fail.
displaySol(_):- nl,!.

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
main:-  
write('Initializing Clause generation... '), nl,
initClauseGeneration,
write('Generating Clauses... '), nl,
tell(clauses), writeClauses, told,          % generate the (numeric) SAT clauses and call the solver
write('Generating Headers... '), nl,
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
