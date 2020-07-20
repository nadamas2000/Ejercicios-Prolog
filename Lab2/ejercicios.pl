pert_con_resto(X,L,Resto):-
	concat(L1,[X|L2], L),
	concat(L1, L2, Resto).

permutacion([],[]).
permutacion(L,[X|P]) :- pert_con_resto(X,L,R), permutacion(R,P).

% Ejercicio 2
prod([X], X):- !.
prod([X|Xs], P):- prod(Xs,P1), P is P1 * X.


% Ejercicio 3
long([], 0).
long([_|Xs], N):- long(Xs, M), N is M + 1.

equal_long(L1, L2):-
    long(L1, S1),
    long(L2, S2),
    S1 = S2.

product([X], [Y], [Z]):-
    Z is X * Y.
product([X|L1], [Y|L2], [Z|Ps]):-
    Z is X * Y,
    product(L1, L2, Ps).

suma([X], X):- !.
suma([X|L1], Y):- suma(L1, S), Y is S + X.

pescalar(L1,L2,P):-
    equal_long(L1, L2),
    product(L1, L2, Ps),
    suma(Ps, P), !.

    

% Ejercicio 4
intersec([], _, []).
intersec([X|V1], V2, [X|V3]):-
    member(X, V2),
    intersec(V1, V2, V3), !.
intersec([_|V1], V2, V3):-    
    intersec(V1, V2, V3).
    
unio([], V, V).
unio([X|V1], V2, [X|V3]):-
    \+member(X, V2),
    unio(V1, V2, V3), !.
unio([_|V1], V2, V3):-
    unio(V1, V2, V3).    

    
% Ejercicio 5
concat([], L, L):- !.
concat([X|L1], L2, [X|L3]):- concat(L1, L2, L3).

ulti([X], X):- !.
ulti([_|Xs], Y):- ulti(Xs, Y).

inv([X], [X]):- !.
inv([X|Xs], Ys):- inv(Xs, Yr), concat(Yr, [X], Ys), !.


% Ejercicio 6
fib(1, 1).
fib(2, 1).
fib(N,F):-
    N > 1,
    N =< 30,
    N1 is N - 1,
    N2 is N - 2,
    fib(N1, F1),
    fib(N2, F2),
    F is F1+F2, !.

    
% Ejercicio 7
dados(P, 1, [P]):- member(P,[1,2,3,4,5,6]), !.
dados(P, N, [X|L]):-
    N > 0,    
    member(X, [1,2,3,4,5,6]),
    N1 is N - 1,
    P1 is P - X,
    dados(P1, N1, L),
    concat([X], L, Ls),
    suma(Ls, P).


% Ejercicio 8
n_elementos([],0).
n_elementos([_|L],N):-
	n_elementos(L,N1),
	N is N1 + 1.
	
%suma_d(X, Rs, L):-
%    member(X, L),
%    suma(Rs, S),
%    S = X.

suma_demas(L):-
	n_elementos(L,N),
	member(N,L),!.


% Ejercicio 9
suma_ants([X|L]):- suma(L,N), X = N, !.
suma_ants([_|L]):- suma_ants(L).


% Ejercicio 10
card( [X|L] , [ [X,N1] |Cr] ):-card(L,C),pert_con_resto([X,N],C,Cr),!,N1 is N+1.
card( [X|L] , [ [X,1]   |C] ):-card(L,C).
card(L):-card(L,C), write(C).


% Ejercicio 11
antMayor([],_).
antMayor([X|List],Y):-
	X >= Y,
	antMayor(List,X), !.
antMayor([X|_],Y):-
	X < Y,
	fail.

esta_ordenada([]).
esta_ordenada([_]).
esta_ordenada([X|L]):-
	antMayor(L,X),!.

	
% Ejercicio 12
ordenacion(L1,L2) :- permutacion(L1,L2), esta_ordenada(L2), !.


% Ejercicio 13
% El peor caso se da cuando la lista está ordenada inversa para lo que tiene que aplicar n! elementos.


% Ejercicio 14
ordenacion2([],[]). 
ordenacion2([X|L],L1) :- ordenacion2(L,L2), insercion(X,L2,L1), !.

insercion(X,[],[X]). 
insercion(X,[Y|L],[X,Y|L]) :- X=<Y. 
insercion(X,[Y|L],[Y|L1]) :- X>Y, insercion(X,L,L1).


% Ejercicio 15
% En el peor de los casos el coste es de n(n-1)/2.

% Ejercicio 16
split([],[],[]).
split([A],[A],[]).
split([A,B|R],[A|Ra],[B|Rb]) :-  split(R,Ra,Rb).
  
merge(L, [], L) :- !.
merge([], L, L).
merge([X|L1],[Y|L2],[X|L3]) :- X=<Y, !, merge(L1,[Y|L2],L3).
merge([X|L1],[Y|L2],[Y|L3]) :- merge([X|L1],L2,L3).

ordenacion3([],[])   :- !.
ordenacion3([X],[X]) :- !.
ordenacion3(L,L3) :- split(L,L1,L2), ordenacion3(L1,L11), ordenacion3(L2,L22), 
  merge(L11,L22,L3), !. 
