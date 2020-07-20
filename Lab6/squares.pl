:- use_module(library(clpfd)).

%ejemplo(_, Big, [S1...SN]): how to fit all squares of sizes S1...SN in a square of size Big?
% ejemplo(_, Big, [S1...SN]): ¿Cómo encajar todos los cuadrados con lados S1..SN dentro de un cuadrado de lado Size?
ejemplo(0,  3,[2,1,1,1,1,1]).
ejemplo(1,  4,[2,2,2,1,1,1,1]).
ejemplo(2,  5,[3,2,2,2,1,1,1,1]).
ejemplo(3, 19,[10,9,7,6,4,4,3,3,3,3,3,2,2,2,1,1,1,1,1,1]).
ejemplo(4,112,[50,42,37,35,33,29,27,25,24,19,18,17,16,15,11,9,8,7,6,4,2]).
ejemplo(5,175,[81,64,56,55,51,43,39,38,35,33,31,30,29,20,18,16,14,9,8,5,4,3,2,1]).

main:- 
    ejemplo(3,Big,Sides),
    nl, write('Fitting all squares of size '), write(Sides),
    write(' into big square of size '), write(Big), nl,nl,
    length(Sides,N), 
    length(RowVars,N),                          % get list of N prolog vars: Row coordinates of each small square
    length(ColVars,N),                          % añadida extracción de número de columnas
    insideBigSquare(N,Big,Sides,RowVars),
    insideBigSquare(N,Big,Sides,ColVars),
    nonoverlapping(N,Sides,RowVars,ColVars),
    
    append(RowVars,ColVars,Vars),               % Añade las coordenadas RowVars y ColVars al conjunto de variables.
    labeling([ff],Vars),                        % Genera el conjunto de variables Var a partir de las más restrictivas [ff].
    
    displaySol(N,Sides,RowVars,ColVars), halt.


displaySol(N,Sides,RowVars,ColVars):- 
    between(1,N,Row), nl, between(1,N,Col),
    nth1(K,Sides,S),    
    nth1(K,RowVars,RV),    RVS is RV+S-1,     between(RV,RVS,Row),
    nth1(K,ColVars,CV),    CVS is CV+S-1,     between(CV,CVS,Col),
    writeSide(S), fail.
displaySol(_,_,_,_):- nl,nl,!.

writeSide(S):- S<10, write('  '),write(S),!.
writeSide(S):-       write(' ' ),write(S),!.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% B1: Cuadrado de tamaño 0 es de [] por [].
% B2: Un cuadrado de N elementos, Big de lado, cuyo primer cuadrado
%     que lo compone es de X de lado y el resto en Sides, el valor 
%     de los elementos de ese cuadrado es V y el resto de valores
%     están en Vars.
% B3: Max es el lado Big menos los elementos del cuadrado X + 1.
% B4: El valor del cuadrado componente está entre los valores 1..Max.
% B5: Quedan N-1 cuadrados por introducir.
% B6: Se repite la operación para N-1 cuadrados para crear un cuadrado
%     de Big de lado con cuadrados con lados Sides y valores Vars.
insideBigSquare(0,_,[],[]).                     % <- B1                   
insideBigSquare(N, Big,[X|Sides],[V|Vars]):-    % <- B2
    Max is Big - X + 1,                         % <- B3
    V in 1..Max,                                % <- B4
    N2 is N - 1,                                % <- B5
    insideBigSquare(N2, Big, Sides, Vars).      % <- B6

% Comprobación de no-solapamiento de cuadrados.
% C1: Un cuadrado creado sin cuadrados [] resulta de una matriz [][]
%     (vacía)
% C2: Para cualquier número de cuadrados _, el primer cuadrado X de
%     la lista de cuadrados con lados Sides han de crear en una fila
%     R dentro del conjuto de filas RowVars+{R} y una columna C
%     dentro de la lista de columnas ColVars+{C}.
% C3: Verificar que el resto de elementos encajan con sus
%     filas/columnas.
% C4: Continua con el resto de elementos de las listas.
nonoverlapping(_,[],[],[]).                             % <- C1
nonoverlapping(_,[X|Sides],[R|RowVars],[C|ColVars]):-   % <- C2
    comp2b2(X, Sides,R,RowVars,C,ColVars),              % <- C3
    nonoverlapping(_,Sides,RowVars,ColVars).            % <- C4

% Comparación 2 a 2 de los cuadrados.
% D1: Cualquier comparación de un elemento cualquiera con los
%     elementos de una lista vacía es correcto.
% D2: Se comparará los elementos X1 y X2 donde éste último es de la
%     lista Sides+{X2}, con las coordenadas de fila R1 y R2 y las
%     coordenadas de columna C1 y C2.
% D3: Comprueba que los dos cuadrados con lados X1 y X2 y coordenadas
%     R1, R2, C1 y C2 no se solapan.
% D4: Continua comparando el cuadrado de lado X1 con sus coordenadas
%     R1 y C1, con el resto de cuadrados contenidos en Sides y
%     coordenadas RowVars y ColVars.
comp2b2(_,[],_,[],_,[]).                                  % <- D1
comp2b2(X1,[X2|Sides],R1,[R2|RowVars],C1,[C2|ColVars]):-  % <- D2
    nonoverlappingCoord(X1,X2,R1,C1,R2,C2),               % <- D3
    comp2b2(X1,Sides,R1,RowVars,C1,ColVars).              % <- D4


% Cuadrados no superpuestos
% E1: Para los cuadrados con lados de tamaños X1 y X2 con filas R1 y
%     R2 respectivamente y columnas C1 y C2 respectivamente.
% E2: La coordenada de fila R1 más X1 elementos ha de ser menor o
%     igual que la coordenada R2, o ...
% E3: La coordenada de columna C1 más X1 elementos ha de ser menor o
%     igual que la coordenada C2, o ...
% E4: La coordenada de fila R2 más X2 elementos ha de ser menor o
%     igual que la coordenada R1, o ...
% E5: La coordenada de columna C2 más X2 elementos ha de ser menor o
%     igual que la coordenada C1.
nonoverlappingCoord(X1,X2,R1,C1,R2,C2):-    % <- E1
    R1+X1 #=< R2 #\/                        % <- E2
    C1+X1 #=< C2 #\/                        % <- E3
    R2+X2 #=< R1 #\/                        % <- E4
    C2+X2 #=< C1.                           % <- E5
