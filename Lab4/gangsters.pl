%% The mafia has a lot gangsters for doing different tasks.
%% These tasks are planned every 3 days (72h), according to a forecast
%% of the tasks to be done every hour.
%% No gangster can do two different tasks during the same hour or on two consecutive hours.
%% Some gangsters are not available on certain hours.
%% We want to plan all tasks (which gangster does what task when) and
%% we want to find the minimal K such that no gangster works more than
%% K consecutive hours.

%% La mafia tiene muchos gángsters para hacer diferentes tareas.
%% Estas tareas se planifican cada 3 días (72h), de acuerdo con un pronóstico de las tareas
%% que se realizarán cada hora.
%% Ningún gángster puede hacer dos tareas diferentes durante la misma hora o en dos horas
%% consecutivas.
%% Algunos gángsters no están disponibles en ciertas horas.
%% Queremos planificar todas las tareas (qué gángster hace qué tarea y cuándo) y queremos
%% encontrar la K mínima para que ningún gángster trabaje más de K horas consecutivas.




%% EXAMPLE OUTPUT:
%% 
%%                       10        20        30        40        50        60        70  
%%               123456789012345678901234567890123456789012345678901234567890123456789012
%% 
%% gangster g01: ------------------------------p-------p-----p----p----p--------------p--
%% gangster g02: ------p--p-p--------------p--ppp-----pp---pp-----p----p---p----p--------
%% gangster g03: -p----p--p-p-p--p-------p-----pp-pp-p-pp-pppp--pp--p-pp-pppp--p-------p-
%% gangster g04: -pp---p--p--pp----pp-p-pp-p-p-pppppp-cc-p--c----pppppp-p-c-p--ppp--p-p--
%% gangster g05: pppppppppppppp--p-pp-p-ppppp-c--cc-p-cc-c-c-p--ppppppp-c-c-pppppppppppp-
%% gangster g06: pp-c--c-c-cc-pp-p-pppppppppp-c--ccc-ccc-c-c-ppppp-cc-p-c-c-pppppp-cc-ppp
%% gangster g07: -c-c-cc-c-cccc--ppp-c-pp-c-cccccccc-ccccccccc--c--ccccccccc-c--cc-cccc-p
%% gangster g08: ccccccccc-cccc-p-c-cccc--c-ccccccccc-k-ccccccc-cccccccc-k-p-c-ccc-ccccc-
%% gangster g09: k--k-c-k-cc-k--cccc-k-ccccc-k-c-k-c-kk-k-c-k-cccc-kk-cc-kk--cccccccccccc
%% gangster g10: k--k-c-k--k-k-cc-kkkk-k--k-kkk-kk-k-kk-k-c-kkkk--kkk-kkkkk-c-kkkk--k--k-
%% gangster g11: k-kkk--k--kkkk-k-kkkk-k-kk-kkkkkkkk-kk-kkk-kkkkkkkkk-kkkkk--kkkkkk-k--kk
%% gangster g12: kkkkkkkkkkkkkkkkkk-kkkkkkkkkkkkkkkkkk-kkkkkkkkkkkkkkkkkk-kkkkkkkkkkkkkkk



%%%%%%%%%%%%%%%%%%%%% INPUT:

% example: 4 gangsters are needed for killing on hour 1, one gangster on hour 2, two gangsters on hour 3, etc.
% ejemplo: se necesitan 4 gángsters para matar en la hora 1, un gángster en la hora 2, dos gángsters en la hora 3, etc.

gangstersNeeded( killing,       [4,1,2,4,2,1,1,4,1,1,3,2,4,2,1,2,1,3,2,3,4,1,3,1,2,3,1,3,4,3,2,3,4,2,3,1,4,4,1,4,2,2,1,4,3,3,3,2,2,3,4,4,1,3,3,3,4,4,1,1,2,3,3,3,3,2,1,3,1,1,3,2] ).
gangstersNeeded( countingMoney, [1,2,1,3,1,4,3,1,3,1,4,3,2,2,1,2,1,2,1,1,2,1,2,1,1,3,1,2,2,4,3,2,4,4,4,1,2,4,4,2,4,4,4,3,2,2,1,3,2,1,3,3,2,3,3,3,1,4,1,1,3,1,2,3,3,1,4,4,3,3,2,1] ).
gangstersNeeded( politics,      [2,4,2,1,1,1,4,1,1,4,1,3,2,4,1,1,4,1,4,3,1,3,2,4,4,2,4,2,1,1,4,3,1,2,2,2,1,1,3,1,1,1,2,2,4,1,1,3,4,4,2,3,2,4,3,1,1,1,3,4,2,2,4,4,3,1,1,2,1,4,3,2] ).

gangsters([g01,g02,g03,g04,g05,g06,g07,g08,g09,g10,g11,g12]).

notAvailable(g01,[6,13,14,16,21,35,37,41,59]).
notAvailable(g02,[14,34,40,45,48,52,58,65,70,72]).
notAvailable(g03,[8,11,13,27,30,38,50,51,70]).
notAvailable(g04,[4,12,16,17,26,30,42,45,48,55,71]).

%%%%%%%%%%%%%%%%%%%%% END INPUT. %%%%%%%%%%%%%%%%%%%%%

symbolicOutput(0). % set to 1 to see symbolic output only; 0 otherwise.

%%%%%% Some helpful definitions to make the code cleaner:
maxHours(72).

task(T):-        gangstersNeeded(T,_).
needed(T,H,N):-  gangstersNeeded(T,L), nth1(H,L,N).
gangster(G):-    gangsters(L), member(G,L).
hour(H):-        maxHours(N), between(1,N,H).
blocked(G,H):-   notAvailable(G,L), member(H,L).
available(G,H):- hour(H), gangster(G), \+blocked(G,H).

% ========================= SAT Variables ==========================
% We use (at least) the following types of symbolic propositional variables:
%   1. does(G,T,H) means:  "gangster G does task T at hour H"     (MANDATORY)
%   2. ...
satVariable( does(G,T,H) ):- gangster(G), task(T), hour(H).


% ========================== writeClauses(MaxCost) ============================

writeClauses(infinite):- !, maxHours(N), writeClauses(N), !.
writeClauses(K):-
    cadaHoraCadaGangsterComMaximUnaVegada,  %% un gangster en una hora donada com a molt pot fer una tasca
    cadaGangsterNoPotCanviarTascaHoraConsecutiva,
    completarTasca,
    nomesHoresQueEsPuguiTreballar,
    noKHoresConsecutives(K),                   %% cap gangster treballa més de K hores consecutives
    true, !.
    

cadaHoraCadaGangsterComMaximUnaVegada:- 
    gangster(G),
    hour(H),
    findall(does(G,T,H), task(T), Lits),
    atMost(1,Lits), fail.
cadaHoraCadaGangsterComMaximUnaVegada.

cadaGangsterNoPotCanviarTascaHoraConsecutiva:-
    gangster(G),
    hour(H1),
    hour(H2),
    H2 is H1 + 1,
    task(T1),
    task(T2),
    T1 \= T2,
    writeClause([ -does(G,T1,H1), -does(G,T2,H2) ]), fail.
cadaGangsterNoPotCanviarTascaHoraConsecutiva.

completarTasca:-
    task(T),
    hour(H),    
    findall(does(G,T,H), available(G,H), Lits),
    needed(T,H,N),
    atLeast(N,Lits), fail.
completarTasca.

nomesHoresQueEsPuguiTreballar:-
    gangster(G),
    hour(H),
    task(T),
    notAvailable(G,H),
    writeClause([ -does(G,T,H) ]), fail.
nomesHoresQueEsPuguiTreballar.

noKHoresConsecutives(K):-
    gangster(G),
    hour(Hi),
    task(T),
    available(G,Hi),
    needed(T,Hi,_),
    hour(Hf),
    Hf is Hi + K,
    findall(does(G,T,H), between(Hi,Hf,H), Lits),
    atMost(K,Lits), fail.
noKHoresConsecutives(_).


%% ======================= Display ===============================

displaySol(M):- nl,nl,
    write('                      10        20        30        40        50        60        70  '), nl,
    write('              123456789012345678901234567890123456789012345678901234567890123456789012'), nl,
    gangster(G), nl, write('gangster '), write(G), write(': '), hour(H), writeIfBusy(G,H,M), fail.
displaySol(_):- nl,nl,!.

writeIfBusy(G,H,M):- member( does(G, killing,       H), M),  write('k'),!.
writeIfBusy(G,H,M):- member( does(G, countingMoney, H), M),  write('c'),!.
writeIfBusy(G,H,M):- member( does(G, politics,      H), M),  write('p'),!.
writeIfBusy(_,_,_):- write('-'),!.

% ====================== Calcul del cost =======================

% Cost es el màxim número d'hores treballades consecutivament per algun gangster
costOfThisSolution(M,K):-
    maxHours(MH),
    between(1,MH,N),
    K is MH - N,
    algunGangsterTreballaConsecutivament(K,M).
    
algunGangsterTreballaConsecutivament(K,M):-
    gangster(G),
    gangsterTreballaConsecutivament(G,K,M).

gangsterTreballaConsecutivament(G,K,M):-
    llistaHoresTreballades(G,M,L),
    hiHaSubllistaHoresConsecutives(K,L).

llistaHoresTreballades(G,M,L):-
    maxHours(MH),
    findall(does(G,_,H), (between(1,MH,H),member(does(G,_,H),M)), L).
llistaHoresTreballades.

hiHaSubllistaHoresConsecutives(K,L):- 
    append([_,LK,_], L), %% Subllistes LK en L.
    length(LK,K),
    horesConsecutives(LK,K).

horesConsecutives([_], 1).
horesConsecutives([does(_,_,X), does(_,_,Y) | L], K):-    
    Y is X + 1,
    K1 is K - 1,
    horesConsecutives([does(_,_,Y)|L], K1).




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
