% A.1. “Hacer Aguas”: disponemos de un grifo de agua,
% un cubo de 5 litros y otro de 8 litros. Se puede
% verter el contenido de un cubo en otro, llenar un
% cubo, o vaciar un cubo del todo, y queremos saber la
% secuencia mı́nima de operaciones para obtener
% exactamente 4 litros de agua en el cubo de 8 litros.

camino(E,E,C,C). 
camino(EstadoActual, EstadoFinal, CaminoHastaAhora, CaminoTotal):-
    unPaso(EstadoActual, EstSiguiente),
    \+member(EstSiguiente,CaminoHastaAhora),
    camino( EstSiguiente, EstadoFinal, [EstSiguiente|CaminoHastaAhora], CaminoTotal ).
 
% De cubo8 a cubo5
unPaso([Cubo5, Cubo8], [Cubo5Next, Cubo8Next]):-
    EspacioVacio5 is (5 - Cubo5),
    AVerter is min(EspacioVacio5, Cubo8),
    Cubo5Next is (Cubo5 + AVerter),
    Cubo8Next is (Cubo8 - AVerter).
% De cubo5 a cubo8
unPaso([Cubo5, Cubo8], [Cubo5Next, Cubo8Next]):-
    EspacioVacio8 is (8 - Cubo8),
    AVerter is min(EspacioVacio8, Cubo5),
    Cubo8Next is (Cubo8 + AVerter),
    Cubo5Next is (Cubo5 - AVerter).

unPaso([Cubo5, Cubo8], [0, Cubo8]):- Cubo5 > 0.   % vaciar cubo5
unPaso([Cubo5, Cubo8], [Cubo5, 0]):- Cubo8 > 0.   % vaciar cubo8

unPaso([Cubo5, Cubo8], [5, Cubo8]):- Cubo5 < 5.   % llenar cubo5
unPaso([Cubo5, Cubo8], [Cubo5, 8]):- Cubo8 < 8.   % llenar cubo8

nat(0).
nat(N):-
    nat(N1),
    N is N1+1.
    
writeSolution(N,C1):-
    write("Solución óptima en "),
    Pasos is N-1,
    write(Pasos),
    write(" pasos."),
    nl,
    write(C1),
    nl.


    
solucionOptima:-
    nat(N),                        % Busquem solució de "cost" 0; si no, de 1, etc.
    camino([0,0],[0,4],[[0,0]],C), % A "hacer aguas": -un estado es [cubo5,cubo8], y
    length(C,N),                   % -el coste es la longitud de C.
    reverse(C,C1),
    writeSolution(N,C1).    
    
main:- solucionOptima, halt.
