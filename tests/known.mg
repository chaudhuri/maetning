%positive A.
%positive B.

%prove A => A.
%refute A.

%positive p.

%refute (\A x. \E y. p(x, y)) => \E y. \A x. p(x, y).
%prove (\A x. \E y. p(x, y)) <= \E y. \A x. p(x, y).

%refute A + ~A.
%refute ((A => C) => A) => A.
%refute (\E x. p(x)) <= ~~\E x. p(x).

%prove ~(A + B) <=> ~A & ~B.

%prove ~(A * B) <= ~A + ~B.
%prove ~(A & B) <= ~A + ~B.
%refute  ~(A & B) => ~A + ~B.

% drinker's formula and its Goedel-Gentzen translation

%refute \E x. \A y. p(x) => p(y).

%prove ~ (\A x. \E y. p(x) & ~ p(y)).