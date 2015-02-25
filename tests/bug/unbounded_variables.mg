%positive p.
%positive q.

%assume r : (\A y,a,b,w. q(y,a) * q(a,b) * p(b,w)) => (\A z. q(y,z) * p(z,w)).

%refute \E x,y,z. p(x,y) * q(y,z) * p(z,x).