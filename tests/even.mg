% Copyright (C) 2015  Inria (Institut National de Recherche
%                     en Informatique et en Automatique)
% See LICENSE for licensing details.


%negative even.

%assume even_z : even(z).
%assume even_s : \A x. even(x) => even(s(s(x))).

%pseudo p0 : \A x. even(x).
% pseudo p1 : (\E x. even(s(x))) => (\A x. even(s(x))).
% pseudo p2 : \A x. even(s(s(x))).
% pseudo p3 : \A x. even(s(s(s(x)))).
% pseudo p4 : \A x. even(s(s(s(s(x))))).

% prove  even(s(s(s(s(z))))).

% refute even(s(z)).
% refute even(s(s(s(z)))).
%refute \A x. even(s(s(s(x)))).
% refute even(s(s(s(s(z))))).