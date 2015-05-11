%assume as1 : \E x. f(x) & ng(x).
%assume as2 : \A x. f(x) => h(x).
%assume as3 : \A x. j(x) & i(x) => f(x).
%assume as4 : (\E x. h(x) & ng(x)) => \A y. i(y) => ~ h(y).
%prove \A x. j(x) => ~ i(x).
