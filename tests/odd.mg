% Copyright (C) 2015  Inria (Institut National de Recherche
%                     en Informatique et en Automatique)
% See LICENSE for licensing details.

%negative odd.

%assume odd_sz : odd(s(z)).
%assume odd_s  : \A x. odd(s(s(x))) => odd(x).

%refute odd(s(s(z))).

%pseudo p : \A x. odd(s(s(s(s(s(s(x))))))).

%refute odd(s(s(z))).

%retract p.
%pseudo p : (\E x. odd(s(s(s(s(s(s(x)))))))) => (\A x. odd(s(s(s(s(s(s(x)))))))).

%refute odd(s(s(z))).
