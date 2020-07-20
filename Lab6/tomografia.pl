% A matrix which contains zeroes and ones gets "x-rayed" vertically and
% horizontally, giving the total number of ones in each row and column.
% The problem is to reconstruct the contents of the matrix from this
% information. Sample run:

% Una matriz que contiene ceros y unos obtiene "rayos x" vertical y
% horizontalmente, dando el número total de unos en cada fila y columna.
% El problema es reconstruir el contenido de la matriz a partir de esta
% información. Ejecución de muestra:

%
%	?- p.
%	    0 0 7 1 6 3 4 5 2 7 0 0
%	 0                         
%	 0                         
%	 8      * * * * * * * *    
%	 2      *             *    
%	 6      *   * * * *   *    
%	 4      *   *     *   *    
%	 5      *   *   * *   *    
%	 3      *   *         *    
%	 7      *   * * * * * *    
%	 0                         
%	 0                         
%	

:- use_module(library(clpfd)).

ejemplo1( [0,0,8,2,6,4,5,3,7,0,0], [0,0,7,1,6,3,4,5,2,7,0,0] ).
ejemplo2( [10,4,8,5,6], [5,3,4,0,5,0,5,2,2,0,1,5,1] ).
ejemplo3( [11,5,4], [3,2,3,1,1,1,1,2,3,2,1] ).


p:-	ejemplo3(RowSums,ColSums),
    length(RowSums,NumRows),
    length(ColSums,NumCols),
    NVars is NumRows*NumCols,
    listVars(NVars,L),              % generate a list of Prolog vars (their names do not matter)

    % Establece que los valores de las variables están entre 0 y 1.
    L ins 0..1,                     

    matrixByRows(L,NumCols,MatrixByRows),

    % Traspone la matriz MatrixByRows. MatrixByRows -> MatrixByCols.
    transpose(MatrixByRows, MatrixByCols),          
    
    % Declara las constricciones sobre la Matriz MatrixByRows y el vector de filas.
    declareConstraints(MatrixByRows, RowSums),      
    
    % Declara las constricciones sobre la Matriz traspuesta MatrixByCols y el vector de columnas.
    declareConstraints(MatrixByCols, ColSums),      
    
    % Asigna valores a las variables generadas L.
    labeling([ff], L),              
    
    pretty_print(RowSums,ColSums,MatrixByRows).


pretty_print(_,ColSums,_):- write('     '), member(S,ColSums), writef('%2r ',[S]), fail.
pretty_print(RowSums,_,M):- nl,nth1(N,M,Row), nth1(N,RowSums,S), nl, writef('%3r   ',[S]), member(B,Row), wbit(B), fail.
pretty_print(_,_,_).
wbit(1):- write('*  '),!.
wbit(0):- write('   '),!.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% A1: 0 elementos de L en una fila resulta un conjunto vacio [] y el
%     resto es todo L.
% A2: N elementos de una fila con un primer elemento X de una lista L+{X}
%     que ha de resultar en una lista R+{X} donde el resto es Rest.
% A3: N ha de ser mayor que 0.
% A4: Un elemento introducido implica que quedan N-1 elementos por
%     introducir.
% A5: Seguimos con el siguiente elemento de la fila donde quedan N1
%     elementos por introducir de la lista L en la fila R, con el resto
%     Rest.
elements_on_Row(0, L, [], L).               % <- A1
elements_on_Row(N, [X|L], [X|R], Rest):-    % <- A2
    N > 0,                                  % <- A3
    N1 is N-1,                              % <- A4
    elements_on_Row(N1, L, R, Rest).        % <- A5


% B1: Una conjunto de elementos vacío [] resulta una matriz vacía [].
% B2: Una lista de elementos L que ha de contener NumCols columnas y
%     donde la primera fila Row forma parte del conjunto de filas
%     RestOfRows+{Row}.
% B3: El número de elementos de una fila es NumCols que se han de extraer
%     de L y colocar en Row, el resto de elementos de L es Rest.
% B4: Continua asignando el resto de elementos Rest con NumCols elementos
%     por fila en el resto de filas que quedan.
matrixByRows([], _, []).                        % <- B1
matrixByRows(L, NumCols, [Row|RestOfRows]):-    % <- B2
    elements_on_Row(NumCols, L, Row, Rest),     % <- B3
    matrixByRows(Rest, NumCols, RestOfRows).    % <- B4
    
% C1: Una matriz vacía y un vector de vilas vacíos son correctos, caso base.
% C2: Recoge la primera fila L de la matriz Mat, y el valor de su suma ListSum del vector de sumas RS.
% C3: La suma de los elementos del vector List ha de resultar ListSum.
% C4: Continua de nuevo con el resto de filas de Mat y sumas de RS.
declareConstraints([], []).                     % <- C1
declareConstraints([List|Mat], [ListSum|RS]):-  % <- C2
    sum(List, #=, ListSum),                     % <- C3
    declareConstraints(Mat, RS).                % <- C4

% D1: Un vector de 0 elementos es una lista vacía.
% D2: Vamos a crear N elementos y se empieza por el primero. Se crea _ como primer elemento lista L1. 
% D3: Al crearse el primer elemento de N elementos queda N-1 elementos. 
% D4: Continua con el resto de elementos de la lista.
listVars(0, []):-!.     % <- D1
listVars(N, [_|L1]):-   % <- D2
    N1 is N-1,          % <- D3
    listVars(N1, L1).   % <- D4
