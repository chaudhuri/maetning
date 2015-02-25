% Author: Taus Brock-Nannestad <taus.brock-nannestad@inria.fr>
% Copyright (C) 2015  Inria (Institut National de Recherche
%                     en Informatique et en Automatique)
% See LICENSE for licensing details.


%negative sum.

%assume sum_z : \A x. sum(z,x,x).
%assume sum_s : \A x,y,w. sum(x,y,w) => sum(s(x),y,s(w)).


%pseudo s0 : (\E x,y,w. sum(x,y,w)) => (\A x,y,w. sum(x,y,w)).
% pseudo s01 : (\E x,y,w. sum(s(s(s(x))),y,w)) => \A x,y,w. sum(s(s(s(x))),y,w).
% pseudo s02 : (\E x,y,w. sum(x,s(s(s(y))),w)) => \A x,y,w. sum(x,s(s(s(y))),w).
% pseudo s03 : (\E x,y,w. sum(x,y,s(s(s(s(s(s(w)))))))) => \A x,y,w. sum(x,y,s(s(s(s(s(s(w))))))).

% refute sum(s(s(z)),s(s(z)),s(s(s(s(s(z)))))).

%refute \A x,y,w. sum(x,y,w) => sum(y,x,w).
% refute \A x,y. \E w. sum(x,y,w).
