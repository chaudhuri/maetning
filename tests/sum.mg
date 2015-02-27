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

%refute sum(s(s(z)),s(s(z)),s(s(s(s(s(z)))))).


%refute \A x,y,w. sum(x,y,w) => sum(y,x,w).
%refute \A x,y. \E w. sum(x,y,w).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Finally, is x+x=3 solvable?

%refute \E x. sum(x,x,s(s(s(z)))).

%% Naturally, this succeeds with pseudo s0, yielding a proof of the form
%%
%% @3(?32,?32,s(s(s(z)))) --> %4
%%
%% where %4 is the goal. Notice that we do not necessarily get
%% ground terms in our pseudo.
%%
%% If we now refine s0 into

% pseudo s1 : \A x,y,w. sum(x,y,s(s(s(s(w))))).
%pseudo s1 : (\E x,y,w. sum(x,y,s(s(s(s(w)))))) => \A x,y,w. sum(x,y,s(s(s(s(w))))).
% retract s0.

% pseudo s2 : \A x, y, z. sum(s(s(s(x))),y,z).
% pseudo s3 : \A x, y, z. sum(x,s(s(s(y))),z).

%% something interesting happens -- mætning successfully refutes the
%% goal. Note that by just adding this one pseudo, we are not
%% guaranteed to terminate. In fact, if we add additional goals to
%% ensure a cofinite cover, it seems we are doomed to always find an
%% unsound proof.

%refute \E x. sum(x,x,s(s(s(z)))).
