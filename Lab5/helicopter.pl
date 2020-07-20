%% We have a helicopter that can carry its pilot plus at most two
%% passengers at the same time.  We are given a list of passengers,
%% each with his/her origin and destination, given as coordinates in
%% the plane (a pair of integers in 0..1000).  Complete the following
%% program to find the shortest route for the helicopter to start from
%% its base, handle all passengers, and return to its base.
%% 
%% Some example inputs with 5,8,10,12 passengers:

%% Tenemos un helicóptero que puede transportar a su piloto más como máximo dos
%% pasajeros al mismo tiempo. Nos dan una lista de pasajeros,
%% cada uno con su origen y destino, dados como coordenadas en
%% el plano (un par de enteros entre 0..1000). Complete lo siguiente
%% programa para encontrar la ruta más corta para que el helicóptero comience
%% en su base, lleva a todos los pasajeros y regresa a su base.
%%
%% Algunas entradas de ejemplo con 5,8,10,12 pasajeros:

% Five passengers. The first one has origin [813,136] and destination [133,888], etc. :
example(5, [ [[813,136],[133,888]], [[942,399],[600,89]], [[532,241],[55,55]], [[498,276],[553,528]], [[531,911],[430,545]] ]). %optimal: 3981.30 km.

example(8,[[[839,731],[925,300]],[[888,309],[381,637]],[[423,608],[576,715]],[[703,709],[397,645]],[[353,442],[397,620]],[[34,945],[401,465]],[[885,319],[750,888]],[[313,357],[266,749]]]). % optimal: 3889.06 km.

example(10,[[[781,230],[204,491]],[[424,252],[634,768]],[[940,26],[487,833]],[[297,976],[478,536]],[[953,998],[224,261]],[[287,81],[189,192]],[[716,325],[236,667]],[[735,683],[876,967]],[[394,749],[533,52]],[[144,620],[558,470]]]). % al cabo de unos minutos baja a 6214.37 km pero no sabemos si es óptimo

example(12,[[[264,384],[549,238]],[[747,908],[887,67]],[[431,918],[636,13]],[[20,455],[658,892]],[[136,976],[893,570]],[[677,750],[632,434]],[[998,960],[390,169]],[[740,110],[808,811]],[[581,198],[875,245]],[[768,27],[639,556]],[[736,381],[1000,631]],[[93,222],[155,301]]]). % baja de 9200 km, pero no sabemos

helicopterBasePoint([254,372]).

distanceBetweenTwoPoints( [X1,Y1], [X2,Y2],  D ):- D is sqrt( abs(X1-X2)**2 + abs(Y1-Y2)**2 ).  % Pythagoras!

storeRouteIfBetter( Km, Route ):-  bestRouteSoFar( BestKm, _ ), Km < BestKm,
    write('Improved solution. New best distance is '), write(Km), write(' km.'),nl,
    retractall(bestRouteSoFar(_,_)), assertz(bestRouteSoFar(Km,Route)),!.

main:- N=5, retractall(bestRouteSoFar(_,_)),  assertz(bestRouteSoFar(100000,[])),  % "infinite" distance
       example( N, Passengers ),
       helicopterBasePoint( CurrentPoint ),
       heli( Passengers, 0, [CurrentPoint], [] ).
main:- bestRouteSoFar(Km,ReverseRoute), reverse( ReverseRoute, Route ), nl,
       write('Optimal route: '), write(Route), write('. '), write(Km), write(' km.'), nl, nl, halt.

% heli( PassengersToPickUp, AccumulatedDistance, RouteSoFar, DestinationsOfPassengersInHelicopter )

% backtrack if AccumulatedDistance is already larger than the distance of the best solution so far:
heli( _, AccumulatedDistance, _, _ ):-
    bestRouteSoFar(Distance,_),
    AccumulatedDistance >= Distance, !, fail.

% No passengers to pick up, no passengers left in helicopter -->  return to base
heli( [], AccumulatedDistance, [CurrentPoint|RouteSoFar], [] ):-
    helicopterBasePoint(BasePoint),
    distanceBetweenTwoPoints(CurrentPoint,BasePoint, Dist), 
    append([BasePoint], [CurrentPoint|RouteSoFar], RouteALL),
    NewDistance is AccumulatedDistance + Dist,
    storeRouteIfBetter(NewDistance, RouteALL), fail.

% Pick up another passenger:
heli( PassengersToPickUp, AccumulatedDistance, [CurrentPoint|RouteSoFar], DestinationsOfPassengersInHelicopter ):-
    select([From,Dest], PassengersToPickUp, R),    
    length(DestinationsOfPassengersInHelicopter,N),
    N < 2,
    distanceBetweenTwoPoints(CurrentPoint, From, Dist),
    NewDistance is AccumulatedDistance + Dist,
    append([From],[CurrentPoint|RouteSoFar], RouteALL),
    append([Dest],DestinationsOfPassengersInHelicopter, Dests),
    heli(R, NewDistance, RouteALL, Dests), fail.

% Drop off one of the passengers in the helicopter:
heli( PassengersToPickUp, AccumulatedDistance, [CurrentPoint|RouteSoFar], DestinationsOfPassengersInHelicopter ):- 
    select(Destination, DestinationsOfPassengersInHelicopter,R),
    distanceBetweenTwoPoints(CurrentPoint,Destination, Dist),
    NewDistance is AccumulatedDistance + Dist,
    append([Destination],[CurrentPoint|RouteSoFar], RouteALL),
    heli(PassengersToPickUp, NewDistance, RouteALL,R), fail.
