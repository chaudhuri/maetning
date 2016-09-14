% assume end : a3.
%assume O0 : ((b0 + a0) + b0).
%assume O1 : (b0 => ((b1 + a1) + b1)).
%assume O2 : (b1 => ((b2 + a2) + b2)).

%refute a0 + ((b0 & a1) + (((b1 & a2) + ((b2 & a3))))).
