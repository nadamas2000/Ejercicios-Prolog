% Problema B: Un programa escrito en el lenguaje sumbol tiene la siguiente sintaxis:
% <programa> --> begin <instrucciones> end
% <instrucciones> --> <instruccion>
% <instrucciones> --> <instruccion> ; <instrucciones>
% <instruccion> --> <variable> = <variable> + <variable>
% <instruccion> --> if <variable> = <variable> then <instrucciones> else <instrucciones> endif
% <variable>--> x
% <variable>--> y
% <variable>--> z

% Tres ejemplos de programas sumbol:
%   begin x=x+z end
%   begin x=x+y; z=z+z; x=y+x end
%   begin x=y+z; if z=z then x=x+z; y=y+z else z=z+y endif; x=x+z end

% Escribe en Prolog un sencillo analizador sintáctico para el lenguaje sumbol, es decir, una
% cláusula programa( P ) que se satisface si la lista de átomos P contiene un programa sumbol
% sintácticamente correcto, y que falla en caso contrario. Para ello (es obligatorio), haz
% corresponder una cláusula a cada regla de la gramática. Ejemplos:
%       ?- programa( [begin, z, =, x, +, y, end] ).
%       yes
%       ?- programa( [begin, z, =, x, +, y, ;, x, =, z, z, end] ).   % aqui falta un "+"
%       no


programa(L):-
    append([begin],X,S),
    append(S,[end],L),
    instruccions(X), !.

instruccions(X):-
    instruccio(X).
instruccions(X):-
    append(L,M,X),
    append(S,[;],L),
    instruccio(S),
    instruccions(M).

instruccio([X,=,Y,+,Z]):-
    variable(X),
    variable(Y),
    variable(Z).
instruccio([if,X,=,Y,then|SS]):-
    append(S,L1,SS),
    append(else,L2,L1),
    append(L,endif,L2),
    varible(X),
    varible(Y),
    instruccions(S),
    instruccions(L).

variable(x).
variable(y).
variable(z).
