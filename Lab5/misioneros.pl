% A.2. "Misioneros": buscamos la manera más rápida para tres misioneros y tres canı́bales de cruzar
% un rı́o, disponiendo de una canoa que puede ser utilizada por 1 o 2 personas (misioneros o canı́bales),
% pero siempre evitando que haya misioneros en minorı́a en cualquier orilla (por razones obvias).

isCorrect(M,C):- between(0,3,M), between(0,3,C), safe(M,C), M1 is 3-M, C1 is 3-C, safe(M1,C1).

safe(0,_).
safe(M,C):- M >= C.

unPaso([M,C,i],[M2, C,d]):- M2 is M - 2, isCorrect(M2,C).   
unPaso([M,C,i],[ M,C2,d]):- C2 is C - 2, isCorrect(M,C2).
unPaso([M,C,i],[M2, C,d]):- M2 is M - 1, isCorrect(M2,C).
unPaso([M,C,i],[ M,C2,d]):- C2 is C - 1, isCorrect(M,C2).
unPaso([M,C,i],[M2,C2,d]):- M2 is M - 1, C2 is C - 1, isCorrect(M2,C2).
   
unPaso([M,C,d],[M2, C,i]):- M2 is M + 2, isCorrect(M2,C).
unPaso([M,C,d],[ M,C2,i]):- C2 is C + 2, isCorrect(M,C2).
unPaso([M,C,d],[M2, C,i]):- M2 is M + 1, isCorrect(M2,C).
unPaso([M,C,d],[ M,C2,i]):- C2 is C + 1, isCorrect(M,C2).
unPaso([M,C,d],[M2,C2,i]):- M2 is M + 1, C2 is C + 1, isCorrect(M2,C2).
    
nat(0).
nat(N):- nat(N1), N is N1 + 1.
 
camino(E, E, C, C).
camino(EstadoActual, EstadoFinal, CaminoHastaAhora, CaminoTotal):-
    unPaso(EstadoActual, EstSiguiente),
    \+member(EstSiguiente,CaminoHastaAhora),
    camino(EstSiguiente, EstadoFinal, [EstSiguiente|CaminoHastaAhora], CaminoTotal).

solucionOptima:-
    nat(N),                             % Buscamos solución de "coste" 0; si no, de 1, etc.
    camino([3,3,i], [0,0,d], [[3,3,i]], C),   % En "hacer aguas": -un estado es [cubo5,cubo8], y
    length(C,N),                        % -el coste es la longitud de C.
    reverse(C,CR),
    write(CR), !.
    
    
main:- solucionOptima, halt.
