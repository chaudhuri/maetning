% negative even.

% assume even_z  : even(zero).
% assume even_ss : \A x. even(x) => even(s(s(x))).


% prove even(s(s(s(s(zero))))).

% pseudo e0 : \A x. even(x).
% pseudo e4 : \A x. even(s(s(s(s(x))))).
% refute even(s(s(s(zero)))).


%negative sum.
%assume sum_z : \A x. sum(zero,x,x).
%assume sum_s : \A x, y, z. sum(x,y,z) => sum(s(x),y,s(z)).

% prove \E x. sum(s(s(zero)),s(s(zero)),x).

%positive fib.
%assume fib_z  : fib(zero,zero).
%assume fib_s  : fib(s(zero),s(zero)).
%assume fib_ss : \A x,y,z,v. fib(v,x) =>
                             fib(s(v),y) =>
                             sum(x,y,z) => fib(s(s(v)),z).

%prove \E x. fib(s(s(s(s(s(s(zero)))))),x).