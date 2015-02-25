%%% Quiescence should be on new percolation of rules, not all rules
%%% 2015-02-25 23:11:08+0100

%negative nat.
%assume nz : nat(z).

% assume ns : \A x. nat(x) => nat(s(x)).
%assume nns : \A x. nat(x) & nat(x) => nat(s(x)).

%pseudo p : \A x. nat(s(s(s(x)))).

%refute \A x. nat(x) + (nat(x) => 0).
